/*
 * Copyright (c) 2023 xvanc and contributors
 * SPDX-License-Identifier: BSD-3-Clause
 */

use crate::{Cell, Error, Node, PropParser, Result, Parse};
use core::{fmt, mem::size_of, ptr::NonNull};
use libsa::endian::u64_be;

/// Node Property
#[derive(Clone, Copy)]
pub struct Prop<'dtb> {
    pub name: &'dtb str,
    pub(crate) data: NonNull<[u8]>,
}

unsafe impl Send for Prop<'_> {}
unsafe impl Sync for Prop<'_> {}

impl fmt::Debug for Prop<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Prop({}, {} bytes)", self.name, self.len())
    }
}

impl<'f, 'dtb: 'f> Prop<'dtb> {
    pub(crate) fn parser(self, node: &Node<'f, 'dtb>) -> PropParser<'f, 'dtb> {
        PropParser::new(node, self.as_cell_slice())
    }

    pub fn parse<T>(
        self,
        node: &Node<'f, 'dtb>,
        mut parse: impl FnMut(&mut PropParser<'f, 'dtb>) -> Result<T>,
    ) -> Result<T> {
        let mut parser = PropParser::new(node, self.as_cell_slice());
        parse(&mut parser)
    }
}

impl<'dtb> Prop<'dtb> {
    pub fn len(self) -> usize {
        self.data.len()
    }

    pub fn is_empty(self) -> bool {
        self.len() == 0
    }

    pub fn as_slice(self) -> &'dtb [u8] {
        unsafe { self.data.as_ref() }
    }

    pub fn as_cell_slice(self) -> &'dtb [Cell] {
        let ptr = NonNull::slice_from_raw_parts(self.data.cast::<Cell>(), (self.len() + 3) / 4);
        unsafe { ptr.as_ref() }
    }

    pub fn cell(self) -> Result<Cell> {
        if self.data.len() == 4 {
            Ok(*bytemuck::try_from_bytes::<Cell>(self.as_slice())?)
        } else {
            Err(Error::InvalidPropType)
        }
    }

    pub fn cells(self) -> Result<impl Iterator<Item = Cell> + 'dtb> {
        if self.data.len() % 4 == 0 {
            let cells = bytemuck::cast_slice::<_, Cell>(self.as_slice())
                .iter()
                .copied();
            Ok(cells)
        } else {
            Err(Error::InvalidPropType)
        }
    }

    pub fn u32(self) -> Result<u32> {
        self.cell().map(Cell::get)
    }

    pub fn u64(self) -> Result<u64> {
        if self.data.len() == 8 {
            Ok(bytemuck::try_from_bytes::<u64_be>(self.as_slice())?.get())
        } else {
            Err(Error::InvalidPropType)
        }
    }

    pub fn usize(self) -> Result<usize> {
        match size_of::<usize>() {
            4 => self.u32().map(|x| x as usize),
            8 => self.u64().map(|x| x as usize),
            _ => Err(Error::InvalidPropType),
        }
    }

    pub fn string(self) -> Result<&'dtb str> {
        Ok(core::str::from_utf8(self.as_slice())
            .map_err(|_| Error::InvalidPropType)?
            .trim_end_matches('\0'))
    }

    pub fn string_list(self) -> Result<impl Iterator<Item = &'dtb str>> {
        self.string().map(|s| s.split('\0'))
    }

    pub fn name_index(self, name: &str) -> Result<usize> {
        self.string_list()?
            .position(|n| n == name)
            .ok_or(Error::NotFound)
    }
}

/// `reg` Property
#[derive(Debug)]
pub struct Reg {
    pub addr: *mut u8,
    pub size: usize,
}

impl<'f, 'dtb: 'f> Parse<'f, 'dtb> for Reg {
    fn parse(parser: &mut PropParser<'f, 'dtb>) -> Result<Self> {
        Ok(Reg {
            addr: parser.parse::<usize>()? as *mut u8,
            size: parser.parse()?,
        })
    }
}
