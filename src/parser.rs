/*
 * Copyright (c) 2023 xvanc and contributors
 * SPDX-License-Identifier: BSD-3-Clause
 */

use crate::{Cell, Error, Fdt, Result};
use core::{mem::size_of, ptr::NonNull};

pub const FDT_BEGIN_NODE: Cell = Cell::new(0x1);
pub const FDT_END_NODE: Cell = Cell::new(0x2);
pub const FDT_PROP: Cell = Cell::new(0x3);
pub const FDT_NOP: Cell = Cell::new(0x4);
pub const FDT_END: Cell = Cell::new(0x9);

pub trait Parse<'f, 'dtb: 'f>: Sized {
    fn parse(parser: &mut Parser<'f, 'dtb>) -> Result<Self>;
}

pub struct Parser<'f, 'a: 'f> {
    pub fdt: &'f Fdt<'a>,
    pub(crate) data: &'a [Cell],
    pub(crate) position: usize,
}

impl<'f, 'a: 'f> Parser<'f, 'a> {
    pub fn new(fdt: &'f Fdt<'a>, data: &'a [Cell]) -> Parser<'f, 'a> {
        Self {
            fdt,
            data,
            position: 0,
        }
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

    pub fn take_until(&mut self, mut pred: impl FnMut(Cell) -> bool) -> Result<&'a [Cell]> {
        let start = self.position;
        while !pred(self.bump()?) {}
        Ok(&self.data[start..self.position])
    }

    /// Parse a slice of cells
    pub fn parse_cells(&mut self, len: usize) -> Result<&'a [Cell]> {
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
    pub fn parse_bytes(&mut self, len: usize) -> Result<&'a [u8]> {
        let cells = self.parse_bytes_raw(len)?;
        Ok(unsafe { cells.as_ref() })
    }

    pub fn parse<T: Parse<'f, 'a>>(&mut self) -> Result<T> {
        T::parse(self)
    }
}

fn cell_has_nul(cell: Cell) -> bool {
    let x = cell.get();
    x.wrapping_sub(0x01010101) & !x & 0x80808080 != 0
}

impl<'f, 'dtb: 'f> Parse<'f, 'dtb> for Cell {
    fn parse(parser: &mut Parser<'_, 'dtb>) -> Result<Self> {
        parser.bump()
    }
}

impl<'f, 'dtb: 'f> Parse<'f, 'dtb> for u32 {
    fn parse(parser: &mut Parser<'_, 'dtb>) -> Result<Self> {
        Ok(parser.bump()?.get())
    }
}

impl<'f, 'dtb: 'f> Parse<'f, 'dtb> for usize {
    fn parse(parser: &mut Parser<'_, 'dtb>) -> Result<Self> {
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
    fn parse(parser: &mut Parser<'_, 'dtb>) -> Result<Self> {
        let buf = parser.take_until(cell_has_nul)?;
        let len = buf.len().saturating_sub(1) * 4;
        let len = len + bytemuck::bytes_of(buf.last().unwrap()).partition_point(|x| *x != 0);
        let buf = &bytemuck::cast_slice::<_, u8>(buf)[..len];
        let s = core::str::from_utf8(buf).unwrap();
        Ok(s)
    }
}
