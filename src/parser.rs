/*
 * Copyright (c) 2023 xvanc and contributors
 * SPDX-License-Identifier: BSD-3-Clause
 */

use crate::{node::NodeOrProp, Cell, Error, Fdt, Node, Prop, Result};
#[cfg(feature = "alloc")]
use alloc::vec::Vec;
use core::{
    mem::size_of,
    ops::{Deref, DerefMut},
    ptr::NonNull,
};

pub const FDT_BEGIN_NODE: Cell = Cell::new(0x1);
pub const FDT_END_NODE: Cell = Cell::new(0x2);
pub const FDT_PROP: Cell = Cell::new(0x3);
pub const FDT_NOP: Cell = Cell::new(0x4);
pub const FDT_END: Cell = Cell::new(0x9);

pub struct Parser<'dtb> {
    pub(crate) data: &'dtb [Cell],
    pub(crate) position: usize,
}

impl<'dtb> Parser<'dtb> {
    pub fn new(data: &'dtb [Cell]) -> Parser<'dtb> {
        Self { data, position: 0 }
    }

    /// Returns `true` if the stream is empty
    pub fn is_empty(&self) -> bool {
        self.position >= self.data.len()
    }

    pub fn peek(&self) -> Result<Cell> {
        self.data.get(self.position).copied().ok_or(Error::NoData)
    }

    pub fn bump(&mut self) -> Result<Cell> {
        let cell = self.peek()?;
        self.position += 1;
        Ok(cell)
    }

    pub fn take_until(&mut self, mut pred: impl FnMut(Cell) -> bool) -> Result<&'dtb [Cell]> {
        let start = self.position;
        while !pred(self.bump()?) {}
        Ok(&self.data[start..self.position])
    }

    /// Parse a slice of cells
    pub fn parse_cells(&mut self, len: usize) -> Result<&'dtb [Cell]> {
        if self.is_empty() {
            return Err(Error::NoData);
        }
        let cells = self.data[self.position..]
            .get(..len)
            .ok_or(Error::UnexpectedEndOfStream)?;
        self.position += len;
        Ok(cells)
    }

    /// Parse a slice of bytes, returning a raw pointer
    ///
    /// Any padding bytes required to make `len` a multiple of 4 are pulled from the stream
    /// but not returned in the result.
    ///
    /// The returned pointer retains provenance over the padding bytes, if any, so that it
    /// may safely be cast back to a `[Cell]` for parsing.
    pub(crate) fn parse_bytes_raw(&mut self, len: usize) -> Result<NonNull<[u8]>> {
        let cells = self.parse_cells((len + 3) / 4)?;
        // Create a pointer with provenance for all bytes of `cells`.
        let ptr = NonNull::from(bytemuck::cast_slice::<_, u8>(cells));
        // Truncate the length to the requested number of bytes, but retain the provenance.
        let ptr = NonNull::slice_from_raw_parts(ptr.cast::<u8>(), len);
        Ok(ptr)
    }

    /// Parse a slice of bytes
    ///
    /// Any padding bytes required to make `len` a multiple of 4 are pulled from the stream
    /// but not returned in the result.
    pub fn parse_bytes(&mut self, len: usize) -> Result<&'dtb [u8]> {
        let cells = self.parse_bytes_raw(len)?;
        Ok(unsafe { cells.as_ref() })
    }

    pub fn parse_str(&mut self) -> Result<&'dtb str> {
        let buf = self.take_until(cell_has_nul)?;
        let len = buf.len().saturating_sub(1) * 4;
        let len = len
            + bytemuck::bytes_of(buf.last().unwrap())
                .iter()
                .position(|x| *x == 0)
                .unwrap();
        let buf = &bytemuck::cast_slice::<_, u8>(buf)[..len];
        core::str::from_utf8(buf).map_err(|_| Error::InvalidUtf8)
    }
}

impl<'f, 'dtb: 'f> Parser<'dtb> {
    pub(crate) fn parse_node(&mut self, fdt: &'f Fdt<'dtb>) -> Result<Node<'f, 'dtb>> {
        let name = self.parse_str()?;
        let start = self.position;
        let data = loop {
            match self.bump()? {
                FDT_BEGIN_NODE => {
                    let _ = self.parse_node(fdt)?;
                }
                FDT_PROP => {
                    let len = self.bump()?.get();
                    self.parse_bytes(len as usize + 4)?;
                }
                FDT_NOP => {}
                FDT_END_NODE => break &self.data[start..self.position - 1],
                FDT_END => return Err(Error::UnexpectedEndOfStream),
                _ => return Err(Error::MalformedDtb),
            }
        };
        Ok(Node { name, data, fdt })
    }

    pub(crate) fn parse_prop(&mut self, fdt: &'f Fdt<'dtb>) -> Result<Prop<'dtb>> {
        let len = self.bump()?.get() as usize;
        let name = fdt.get_string(self.bump()?.get()).unwrap();
        let data = self.parse_bytes_raw(len)?;
        Ok(Prop { name, data })
    }

    pub(crate) fn parse_item(&mut self, fdt: &'f Fdt<'dtb>) -> Result<NodeOrProp<'f, 'dtb>> {
        loop {
            match self.bump()? {
                FDT_BEGIN_NODE => break Ok(NodeOrProp::Node(self.parse_node(fdt)?)),
                FDT_PROP => break Ok(NodeOrProp::Prop(self.parse_prop(fdt)?)),
                FDT_NOP => (),
                FDT_END => break Err(Error::NoData),
                _ => return Err(Error::MalformedDtb),
            }
        }
    }
}

fn cell_has_nul(cell: Cell) -> bool {
    let x = cell.get();
    x.wrapping_sub(0x01010101) & !x & 0x80808080 != 0
}

pub trait Parse<'f, 'dtb: 'f>: Sized {
    fn parse(parser: &mut PropParser<'f, 'dtb>) -> Result<Self>;
}

pub struct PropParser<'f, 'dtb: 'f> {
    node: Node<'f, 'dtb>,
    parser: Parser<'dtb>,
}

impl<'f, 'dtb: 'f> Deref for PropParser<'f, 'dtb> {
    type Target = Parser<'dtb>;

    fn deref(&self) -> &Self::Target {
        &self.parser
    }
}

impl<'f, 'dtb: 'f> DerefMut for PropParser<'f, 'dtb> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.parser
    }
}

impl<'f, 'dtb: 'f> PropParser<'f, 'dtb> {
    pub(crate) fn new(node: &Node<'f, 'dtb>, data: &'dtb [Cell]) -> PropParser<'f, 'dtb> {
        Self {
            node: *node,
            parser: Parser::new(data),
        }
    }

    pub fn node(&self) -> &Node<'f, 'dtb> {
        &self.node
    }

    pub fn fdt(&self) -> &'f Fdt<'dtb> {
        self.node.fdt()
    }

    pub fn parse<T: Parse<'f, 'dtb>>(&mut self) -> Result<T> {
        T::parse(self)
    }

    #[cfg(feature = "alloc")]
    pub fn parse_to_end<T: Parse<'f, 'dtb>>(&mut self) -> Result<Vec<T>> {
        let mut v = Vec::new();

        while !self.is_empty() {
            v.push(self.parse()?);
        }

        Ok(v)
    }
}

impl<'f, 'dtb: 'f> Parse<'f, 'dtb> for Cell {
    fn parse(parser: &mut PropParser<'f, 'dtb>) -> Result<Self> {
        parser.bump()
    }
}

impl<'f, 'dtb: 'f> Parse<'f, 'dtb> for u32 {
    fn parse(parser: &mut PropParser<'f, 'dtb>) -> Result<Self> {
        Ok(parser.bump()?.get())
    }
}

impl<'f, 'dtb: 'f> Parse<'f, 'dtb> for u64 {
    fn parse(parser: &mut PropParser<'f, 'dtb>) -> Result<Self> {
        let hi = parser.parse::<u32>()? as u64;
        let lo = parser.parse::<u32>()? as u64;
        Ok((hi << 32) | lo)
    }
}

impl<'f, 'dtb: 'f> Parse<'f, 'dtb> for usize {
    fn parse(parser: &mut PropParser<'f, 'dtb>) -> Result<Self> {
        Ok(match size_of::<usize>() {
            4 => parser.parse::<u32>()? as usize,
            8 => {
                let hi = parser.parse::<u32>()? as usize;
                let lo = parser.parse::<u32>()? as usize;
                (hi << 32) | lo
            }
            _ => unimplemented!("unsupported size for `usize`"),
        })
    }
}

impl<'f, 'dtb: 'f> Parse<'f, 'dtb> for &'dtb str {
    fn parse(parser: &mut PropParser<'f, 'dtb>) -> Result<Self> {
        parser.parse_str()
    }
}

impl<'f, 'dtb: 'f, T: Parse<'f, 'dtb>> Parse<'f, 'dtb> for Vec<T> {
    fn parse(parser: &mut PropParser<'f, 'dtb>) -> Result<Self> {
        parser.parse_to_end()
    }
}
