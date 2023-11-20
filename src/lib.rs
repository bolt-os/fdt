/*
 * Copyright (c) 2023 xvanc and contributors
 * SPDX-License-Identifier: BSD-3-Clause
 */

#![no_std]

#[cfg(feature = "alloc")]
extern crate alloc;

pub mod node;
pub mod parser;
pub mod prop;

pub use node::Node;
pub use prop::Prop;
pub use parser::{Parse, PropParser};

use core::mem::size_of;
use libsa::endian::u32_be;
use parser::{Parser, FDT_BEGIN_NODE};

pub type Result<T, E = Error> = core::result::Result<T, E>;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Error {
    InvalidData(bytemuck::PodCastError),
    InvalidHeader,
    InvalidSlice,
    InvalidPropType,
    InvalidUtf8,
    MalformedDtb,
    NoData,
    /// A requested node or property was not found
    NotFound,
    /// The parser unexpectedly encountered the end of a stream
    UnexpectedEndOfStream,
    UnexpectedCell {
        expected: Cell,
        found: Cell,
    },
    UnsupportedVersion,
}

impl From<bytemuck::PodCastError> for Error {
    fn from(error: bytemuck::PodCastError) -> Error {
        Error::InvalidData(error)
    }
}

#[cfg(feature = "anyhow")]
impl From<Error> for anyhow::Error {
    fn from(error: Error) -> Self {
        anyhow::anyhow!("{error:?}")
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, bytemuck::Pod, bytemuck::Zeroable)]
pub struct FdtHeader {
    pub magic: u32_be,
    pub total_size: u32_be,
    pub struct_offset: u32_be,
    pub string_offset: u32_be,
    pub rsvmap_offset: u32_be,
    pub version: u32_be,
    pub last_compatible_version: u32_be,
    pub boot_cpuid: u32_be,
    pub string_size: u32_be,
    pub struct_size: u32_be,
}

impl FdtHeader {
    pub fn new(bytes: &[u8]) -> Result<&FdtHeader, Error> {
        let header = bytemuck::try_from_bytes::<FdtHeader>(&bytes[..size_of::<FdtHeader>()])?;
        if header.magic.get() != 0xd00dfeed {
            return Err(Error::InvalidHeader);
        }
        Ok(header)
    }
}

pub type Cell = u32_be;

/// Flattened Device Tree
#[derive(Clone, Copy, Debug)]
pub struct Fdt<'dtb> {
    dtb: &'dtb [u8],
    header: &'dtb FdtHeader,
    tree: &'dtb [Cell],
    strs: &'dtb str,
}

impl<'dtb> Fdt<'dtb> {
    /// Create an `Fdt` from a buffer
    ///
    /// # Errors
    ///
    /// This function
    pub fn new(dtb: &'dtb [u8]) -> Result<Fdt<'dtb>, Error> {
        let header = FdtHeader::new(dtb)?;
        if header.total_size.get() as usize != dtb.len() {
            return Err(Error::InvalidSlice);
        }
        Self::new_(header, dtb)
    }

    /// Create an `Fdt` from a raw pointer
    ///
    /// # Safety
    ///
    /// The pointer must point to a valid device tree blob. Specifically, it must be at least
    /// 8-byte aligned and valid for reads up to the number of bytes specified in the header.
    ///
    /// # Errors
    ///
    /// This function errors for the same reasons as [`Fdt::new()`].
    pub unsafe fn from_ptr(ptr: *const u8) -> Result<Fdt<'dtb>, Error> {
        let header_bytes = core::slice::from_raw_parts(ptr, size_of::<FdtHeader>());
        let header = FdtHeader::new(header_bytes)?;
        let dtb = core::slice::from_raw_parts(ptr, header.total_size.get() as usize);
        Self::new_(header, dtb)
    }

    fn new_(header: &'dtb FdtHeader, dtb: &'dtb [u8]) -> Result<Fdt<'dtb>> {
        let tree = bytemuck::try_cast_slice::<_, Cell>(
            &dtb[header.struct_offset.get() as usize..][..header.struct_size.get() as usize],
        )?;
        let strs = core::str::from_utf8(
            &dtb[header.string_offset.get() as usize..][..header.string_size.get() as usize],
        )
        .map_err(|_| Error::InvalidUtf8)?;
        Ok(Fdt {
            dtb,
            header,
            tree,
            strs,
        })
    }

    /// Returns a pointer to the underlying device tree blob
    pub const fn as_ptr(&self) -> *const u8 {
        self.dtb.as_ptr()
    }

    /// Returns the total size of the device tree blob, in bytes
    pub fn total_size(&self) -> usize {
        self.header.total_size.get() as usize
    }

    /// Returns the string at the specified `offset` in the string table
    pub fn get_string(&self, offset: u32) -> Option<&'dtb str> {
        let s = self.strs.get(offset as usize..)?;
        let len = s.bytes().position(|x| x == 0)?;
        Some(&s[..len])
    }

    pub fn root(&self) -> Node<'_, 'dtb> {
        let mut parser = Parser::new(self.tree);
        assert!(parser.bump() == Ok(FDT_BEGIN_NODE));
        parser.parse_node(self).unwrap()
    }

    pub fn try_find_node(&self, path: &str) -> Result<Option<Node<'_, 'dtb>>> {
        self.root().try_find_node(path)
    }

    pub fn find_node(&self, path: &str) -> Option<Node<'_, 'dtb>> {
        self.root().find_node(path)
    }

    pub fn cpus(&self) -> impl Iterator<Item = Node<'_, 'dtb>> {
        self.find_node("/cpus")
            .into_iter()
            .flat_map(|node| node.children())
    }

    pub fn try_property_as<'f, T: Parse<'f, 'dtb>>(&'f self, path: &str) -> Result<Option<T>>
    where
        'dtb: 'f,
    {
        let prop_name = path.split('/').last().ok_or(Error::NotFound)?;
        let path_len = prop_name.as_ptr() as usize - path.as_ptr() as usize;
        let path = &path[..path_len];

        self.try_find_node(path)?
            .and_then(|node| node.try_property_as::<T>(prop_name).transpose())
            .transpose()
    }

    pub fn property_as<'f, T: Parse<'f, 'dtb>>(&'f self, path: &str) -> Option<T>
    where
        'dtb: 'f,
    {
        let prop_name = path.split('/').last()?;
        let path_len = prop_name.as_ptr() as usize - path.as_ptr() as usize;
        let path = &path[..path_len];

        let node = self.find_node(path)?;
        node.property_as::<T>(prop_name)
    }
}
