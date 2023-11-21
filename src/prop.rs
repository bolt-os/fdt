/*
 * Copyright (c) 2023 xvanc and contributors
 * SPDX-License-Identifier: BSD-3-Clause
 */

use crate::{Cell, Error, Node, Parse, PropParser, Result};
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

/// `ranges` Property
///
/// The `ranges` property defines a mapping between the address space of a node and
/// the address space of the node's parent.
///
/// A node may contain multiple ranges, so this property should be parsed as `Vec<Range>`.
/// An empty property indicates a one-to-one mapping between parent and child addresses.
pub struct Range {
    /// Child Bus Address
    ///
    /// Physical address within the parent address space.
    ///
    /// The number of cells making up this value is determined by the `#address-cells`
    /// property of this node.
    pub child_addr: u64,
    /// Child Bus Address High Bits
    ///
    /// Certain nodes (PCI(e)) have an `#address-cells` value of 3. The high 32 bits of these
    /// addresses are stored here.
    pub child_addr_hi: u64,
    /// Parent Bus Address
    ///
    /// Physical address within the parent address space.
    ///
    /// The number of cells making up this value is determined by the `#address-cells`
    /// property of the node which defines the parent address space.
    pub parent_addr: u64,
    /// Range Size
    ///
    /// The size of of the range within the child address space.
    ///
    /// The number of cells making up this value is determined by the `#address-cells`
    /// property of this node.
    pub size: u64,
}

impl<'f, 'dtb: 'f> Parse<'f, 'dtb> for Range {
    fn parse(parser: &mut PropParser<'f, 'dtb>) -> Result<Self> {
        let child_addr_cells = parser
            .node()
            .try_property_as::<u32>("#address-cells")?
            .ok_or(Error::NotFound)?;
        let parent_addr_cells = parser
            .node()
            .try_parent_property_as::<u32>("#address-cells")?
            .ok_or(Error::NotFound)?;
        let size_cells = parser
            .node()
            .try_property_as::<u32>("#size-cells")?
            .ok_or(Error::NotFound)?;

        if child_addr_cells > 3 || parent_addr_cells > 2 || size_cells > 2 {
            return Err(Error::InvalidPropType);
        }

        let child_addr_hi = match child_addr_cells {
            3 => parser.parse::<u32>()? as u64,
            _ => 0,
        };
        let child_addr = match child_addr_cells {
            3 | 2 => parser.parse::<u64>()?,
            1 => parser.parse::<u32>()? as u64,
            _ => unreachable!(),
        };
        let parent_addr = match parent_addr_cells {
            2 => parser.parse::<u64>()?,
            1 => parser.parse::<u32>()? as u64,
            _ => unreachable!(),
        };
        let size = match size_cells {
            2 => parser.parse::<u64>()?,
            1 => parser.parse::<u32>()? as u64,
            _ => unreachable!(),
        };

        Ok(Self {
            child_addr,
            child_addr_hi,
            parent_addr,
            size,
        })
    }
}

/// `reg` Property
#[derive(Debug)]
pub struct Reg {
    pub addr: u64,
    pub size: u64,
}

impl<'f, 'dtb: 'f> Parse<'f, 'dtb> for Reg {
    fn parse(parser: &mut PropParser<'f, 'dtb>) -> Result<Self> {
        let addr_cells = parser
            .node()
            .try_parent_property_as::<u32>("#address-cells")?
            .unwrap_or(2);
        let size_cells = parser
            .node()
            .try_parent_property_as::<u32>("#size-cells")?
            .unwrap_or(1);

        if addr_cells > 2 || size_cells > 2 {
            return Err(Error::InvalidPropType);
        }

        let addr = match addr_cells {
            2 => parser.parse::<u64>()?,
            1 => parser.parse::<u32>()? as u64,
            _ => return Err(Error::InvalidPropType),
        };
        let size = match size_cells {
            2 => parser.parse::<u64>()?,
            1 => parser.parse::<u32>()? as u64,
            0 => 0,
            _ => unreachable!(),
        };

        Ok(Reg { addr, size })
    }
}
