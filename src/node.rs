/*
 * Copyright (c) 2023 xvanc and contributors
 * SPDX-License-Identifier: BSD-3-Clause
 */

use crate::{
    parser::{Parse, Parser, FDT_BEGIN_NODE, FDT_END, FDT_END_NODE, FDT_NOP, FDT_PROP},
    Cell, Error, Fdt, Result,
};
use core::mem::size_of;
use core::{fmt, ptr::NonNull};
use libsa::endian::u64_be;

#[derive(Clone, Copy)]
pub struct Node<'f, 'dtb: 'f> {
    pub(crate) fdt: &'f Fdt<'dtb>,
    pub name: &'dtb str,
    pub(crate) data: &'dtb [Cell],
}

impl<'f, 'dtb: 'f> Node<'f, 'dtb> {
    pub fn fdt(&self) -> &'f Fdt<'dtb> {
        self.fdt
    }

    pub fn is_(&self, other: &'dtb str) -> bool {
        self.name.as_ptr() == other.as_ptr()
    }

    pub fn is(&self, other: &Self) -> bool {
        self.is_(other.name)
    }

    fn parse_error(&self, error: Error, args: fmt::Arguments) -> ! {
        panic!("parse error in `{}`: {args}: {error:?}", self.name);
    }

    pub fn items(&self) -> impl Iterator<Item = NodeOrProp<'f, 'dtb>> {
        let mut parser = Parser::new(self.fdt, self.data);
        core::iter::from_fn(move || match parser.parse::<NodeOrProp<'f, 'dtb>>() {
            Ok(item) => Some(item),
            Err(Error::NoData) => None,
            Err(error) => unreachable!("{error:?}"),
        })
    }
}

impl<'f, 'dtb: 'f> Node<'f, 'dtb> {
    /// Returns an iterator over all children of this node
    pub fn children(&self) -> impl Iterator<Item = Node<'f, 'dtb>> + 'f {
        self.items().filter_map(|item| match item {
            NodeOrProp::Node(node) => Some(node),
            _ => None,
        })
    }

    /// Search for a specific child of this node by name
    pub fn child(&self, name: &str) -> Option<Node<'f, 'dtb>> {
        self.children().find(|&node| node.name == name)
    }

    /// Returns the parent of this node, if any
    pub fn parent(&self) -> Option<Node<'f, 'dtb>> {
        self.fdt.root().parent_(self)
    }

    fn parent_(&self, find: &Node<'f, 'dtb>) -> Option<Node<'f, 'dtb>> {
        for node in self.children() {
            if node.is(find) {
                return Some(*self);
            }
            if let Some(node) = node.parent_(find) {
                return Some(node);
            }
        }
        None
    }

    /// Returns the next node in the path between this node and `end`
    pub fn next_node_to(&self, end: &Node<'f, 'dtb>) -> Option<Node<'f, 'dtb>> {
        self.next_node_to_(end.name)
    }

    fn next_node_to_(&self, name: &'dtb str) -> Option<Node<'f, 'dtb>> {
        self.children().find(|node| node.next_node_to__(name))
    }

    fn next_node_to__(&self, find: &'dtb str) -> bool {
        self.is_(find) || self.children().any(|node| node.next_node_to__(find))
    }

    pub fn path(&self) -> NodePath<'f, 'dtb> {
        NodePath {
            end: self.name,
            current: self.fdt().root(),
            finished: false,
        }
    }

    pub fn find_node_(&self, iter: &mut PathIter) -> Result<Option<Node<'f, 'dtb>>> {
        let Some(path) = iter.next_component() else {
            return Ok(Some(*self));
        };
        if let Some(node) = self.child(path) {
            return node.find_node_(iter);
        }
        Ok(None)
    }

    pub fn try_find_node(&self, path: &str) -> Result<Option<Node<'f, 'dtb>>> {
        let (absolute, mut iter) = PathIter::new(path);
        if absolute && !self.name.is_empty() {
            return Ok(None);
        }
        self.find_node_(&mut iter)
    }

    pub fn find_node(&self, path: &str) -> Option<Node<'f, 'dtb>> {
        self.try_find_node(path)
            .unwrap_or_else(|error| self.parse_error(error, format_args!("find node `{path}`")))
    }
}

impl<'f, 'dtb: 'f> Node<'f, 'dtb> {
    fn parse_property<T: Parse<'f, 'dtb>>(&self, prop: Prop<'dtb>) -> Result<T> {
        Parser::new(self.fdt(), prop.as_cell_slice()).parse()
    }

    pub fn properties(&self) -> impl Iterator<Item = Prop<'dtb>> + 'f {
        self.items().filter_map(|item| match item {
            NodeOrProp::Prop(prop) => Some(prop),
            _ => None,
        })
    }

    pub fn property(&self, name: &str) -> Option<Prop<'dtb>> {
        self.properties().find(|&prop| prop.name == name)
    }

    pub fn try_property_as<T: Parse<'f, 'dtb>>(&self, name: &str) -> Result<Option<T>> {
        self.property(name)
            .map(|prop| self.parse_property::<T>(prop))
            .transpose()
    }

    pub fn property_as<T: Parse<'f, 'dtb>>(&self, name: &str) -> Option<T> {
        self.try_property_as(name)
            .unwrap_or_else(|error| self.parse_error(error, format_args!("property `{name}`")))
    }

    /// Searches all parent nodes for a property
    pub fn parent_property(&self, name: &str) -> Option<Prop<'dtb>> {
        let mut parent = self.parent()?;
        loop {
            if let Some(prop) = parent.property(name) {
                return Some(prop);
            }
            parent = parent.parent()?;
        }
    }

    /// Searches all parent nodes for a property and attempts to parse it
    pub fn try_parent_property_as<T: Parse<'f, 'dtb>>(&self, name: &str) -> Result<Option<T>> {
        self.parent_property(name)
            .map(|prop| self.parse_property::<T>(prop))
            .transpose()
    }

    /// Searches all parent nodes for a property and parses it
    pub fn parent_property_as<T: Parse<'f, 'dtb>>(&self, name: &str) -> Option<T> {
        self.try_parent_property_as(name).unwrap_or_else(|error| {
            self.parse_error(error, format_args!("parent property `{name}`"))
        })
    }

    pub fn inherited_property(&self, name: &str) -> Option<Prop<'dtb>> {
        self.property(name).or_else(|| self.parent_property(name))
    }

    pub fn try_inherited_property_as<T: Parse<'f, 'dtb>>(&self, name: &str) -> Result<Option<T>> {
        self.inherited_property(name)
            .map(|prop| self.parse_property::<T>(prop))
            .transpose()
    }

    pub fn inherited_property_as<T: Parse<'f, 'dtb>>(&self, name: &str) -> Option<T> {
        self.try_inherited_property_as(name)
            .unwrap_or_else(|error| {
                self.parse_error(error, format_args!("inherited property `{name}`"))
            })
    }
}

/// Convience methods
impl<'f, 'dtb: 'f> Node<'f, 'dtb> {
    pub fn is_enabled(&self) -> bool {
        self.property_as::<&str>("status")
            .map_or(true, |s| matches!(s, "ok" | "okay"))
    }

    pub fn is_compatible(&self, matches: &str) -> bool {
        self.is_compatible_any(&[matches])
    }

    pub fn is_compatible_any(&self, matches: &[&str]) -> bool {
        self.property("compatible")
            .and_then(|prop| prop.string_list().ok())
            .map(|mut compat| compat.any(|s| matches.contains(&s)))
            .unwrap_or_default()
    }

    pub fn address_cells(&self) -> Option<usize> {
        self.inherited_property("#address-cells")
            .and_then(|prop| prop.u32().ok().map(|x| x as usize))
    }

    pub fn size_cells(&self) -> Option<usize> {
        self.inherited_property("#size-cells")
            .and_then(|prop| prop.u32().ok().map(|x| x as usize))
    }

    pub fn reg(&self) -> Result<impl Iterator<Item = Result<Reg>> + '_> {
        let addr_cells = self
            .try_inherited_property_as::<u32>("#address-cells")?
            .ok_or(Error::NotFound)? as usize;
        let size_cells = self
            .try_inherited_property_as::<u32>("#size-cells")?
            .ok_or(Error::NotFound)? as usize;

        if addr_cells != size_of::<usize>() / 4 || size_cells != size_of::<usize>() / 4 {
            // XXX: should have a better error.
            return Err(Error::InvalidPropType);
        }

        Ok(self.property("reg").into_iter().flat_map(|prop| {
            let mut parser = prop.parser(self.fdt());
            core::iter::from_fn(move || {
                if parser.is_empty() {
                    return None;
                }
                Some(parser.parse())
            })
        }))
    }

    pub fn reg_by_index(&self, index: usize) -> Result<Reg> {
        self.reg()?.nth(index).ok_or(Error::NotFound)?
    }

    pub fn reg_by_name(&self, name: &str) -> Result<Reg> {
        let index = self
            .property("reg-names")
            .ok_or(Error::NotFound)?
            .name_index(name)?;
        self.reg()?.nth(index).ok_or(Error::NotFound)?
    }
}

#[derive(Debug)]
pub struct Reg {
    pub addr: *mut u8,
    pub size: usize,
}

impl<'f, 'dtb: 'f> Parse<'f, 'dtb> for Reg {
    fn parse(parser: &mut Parser<'f, 'dtb>) -> Result<Self> {
        Ok(Reg {
            addr: parser.parse::<usize>()? as *mut u8,
            size: parser.parse()?,
        })
    }
}

impl fmt::Debug for Node<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Node({:?}, {} bytes)", self.name, self.data.len())
    }
}

impl<'f, 'dtb: 'f> Parse<'f, 'dtb> for Node<'f, 'dtb> {
    fn parse(parser: &mut Parser<'f, 'dtb>) -> Result<Self> {
        let name = parser.parse::<&'dtb str>()?;
        let start = parser.position;
        let data = loop {
            let cell = parser.bump()?;
            match cell {
                FDT_BEGIN_NODE => {
                    let _ = parser.parse::<Self>()?;
                }
                FDT_PROP => {
                    let header = parser.parse::<PropHeader>()?;
                    parser.parse_bytes(header.size.get() as usize)?;
                }
                FDT_NOP => {}
                FDT_END_NODE => break &parser.data[start..parser.position - 1],
                FDT_END => return Err(Error::UnexpectedEndOfStream),
                cell => unreachable!("{cell:x?}, {start}, {}", parser.position),
            }
        };
        Ok(Self {
            name,
            data,
            fdt: parser.fdt,
        })
    }
}

pub struct PathIter<'a> {
    next: &'a str,
}

impl<'a> PathIter<'a> {
    pub fn new(path: &'a str) -> (bool, PathIter<'a>) {
        (
            path.starts_with('/'),
            Self {
                next: path.trim_start_matches('/'),
            },
        )
    }

    pub fn next_component(&mut self) -> Option<&'a str> {
        if self.next.is_empty() {
            return None;
        }
        let component = self.next;
        let len = component.find('/').unwrap_or(component.len());
        self.next = self.next[len..].trim_start_matches('/');
        Some(&component[..len])
    }
}

#[derive(Clone)]
pub struct NodePath<'f, 'dtb: 'f> {
    end: &'dtb str,
    current: Node<'f, 'dtb>,
    finished: bool,
}

impl<'f, 'dtb: 'f> Iterator for NodePath<'f, 'dtb> {
    type Item = &'dtb str;

    fn next(&mut self) -> Option<Self::Item> {
        if self.finished {
            return None;
        }
        let s = self.current.name;
        if self.current.is_(self.end) {
            self.finished = true;
            return Some(s);
        } else {
            self.current = self.current.next_node_to_(self.end).unwrap();
        }
        Some(s)
    }
}

impl fmt::Display for NodePath<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for component in self.clone().filter(|s| !s.is_empty()) {
            write!(f, "/{component}")?;
        }
        Ok(())
    }
}

#[repr(C)]
#[derive(Debug)]
pub struct PropHeader {
    /// Total size of the property, in bytes, including the header.
    size: Cell,
    /// Offset of the property's name in the string table
    name: Cell,
}

impl<'f, 'dtb: 'f> Parse<'f, 'dtb> for PropHeader {
    fn parse(parser: &mut Parser<'_, 'dtb>) -> Result<Self> {
        let header = Self {
            size: parser.parse()?,
            name: parser.parse()?,
        };
        Ok(header)
    }
}

#[derive(Clone, Copy)]
pub struct Prop<'dtb> {
    pub name: &'dtb str,
    data: NonNull<[u8]>,
}

unsafe impl Send for Prop<'_> {}
unsafe impl Sync for Prop<'_> {}

impl<'f, 'dtb: 'f> Parse<'f, 'dtb> for Prop<'dtb> {
    fn parse(parser: &mut Parser<'_, 'dtb>) -> Result<Self> {
        let header = parser.parse::<PropHeader>()?;
        let name = parser.fdt.get_string(header.name.get()).unwrap();
        let data = parser.parse_bytes_raw(header.size.get() as usize)?;
        Ok(Self { name, data })
    }
}

impl fmt::Debug for Prop<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Prop({}, {} bytes)", self.name, self.len())
    }
}

impl<'dtb> Prop<'dtb> {
    pub(crate) fn parser<'f>(self, fdt: &'f Fdt<'dtb>) -> Parser<'f, 'dtb>
    where
        'dtb: 'f,
    {
        Parser::new(fdt, self.as_cell_slice())
    }

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

    pub fn parse<T>(
        self,
        fdt: &Fdt<'dtb>,
        mut parse: impl FnMut(&mut Parser<'_, 'dtb>) -> Result<T>,
    ) -> Result<T> {
        let mut parser = Parser::new(fdt, self.as_cell_slice());
        parse(&mut parser)
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

pub enum NodeOrProp<'f, 'dtb: 'f> {
    Node(Node<'f, 'dtb>),
    Prop(Prop<'dtb>),
}

impl<'f, 'dtb: 'f> Parse<'f, 'dtb> for NodeOrProp<'f, 'dtb> {
    fn parse(parser: &mut Parser<'f, 'dtb>) -> Result<Self> {
        loop {
            match parser.bump()? {
                FDT_BEGIN_NODE => break Ok(Self::Node(parser.parse()?)),
                FDT_PROP => break Ok(Self::Prop(parser.parse()?)),
                FDT_NOP => (),
                FDT_END => break Err(Error::NoData),
                cell => unreachable!("{cell:x?}, {}", parser.position),
            }
        }
    }
}
