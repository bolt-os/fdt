/*
 * Copyright (c) 2023 xvanc and contributors
 * SPDX-License-Identifier: BSD-3-Clause
 */

use crate::{
    parser::{Parse, Parser, PropParser},
    prop::Reg,
    Cell, Error, Fdt, Prop, Result,
};
use core::fmt;

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
        let mut parser = Parser::new(self.data);
        let fdt = self.fdt;
        core::iter::from_fn(move || match parser.parse_item(fdt) {
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
        self.children().find(|node| node.name == name)
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
        PropParser::new(self, prop.as_cell_slice()).parse()
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

    pub fn reg(&self) -> Result<impl Iterator<Item = Result<Reg>> + '_> {
        Ok(self.property("reg").into_iter().flat_map(|prop| {
            let mut parser = prop.parser(self);
            core::iter::from_fn(move || match parser.parse() {
                Ok(reg) => Some(Ok(reg)),
                Err(Error::NoData) => None,
                Err(error) => Some(Err(error)),
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

impl fmt::Debug for Node<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Node({:?}, {} bytes)", self.name, self.data.len())
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

pub enum NodeOrProp<'f, 'dtb: 'f> {
    Node(Node<'f, 'dtb>),
    Prop(Prop<'dtb>),
}
