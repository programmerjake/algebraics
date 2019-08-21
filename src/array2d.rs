// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information

use std::borrow::Borrow;
use std::borrow::BorrowMut;
use std::fmt;
use std::ops::Bound;
use std::ops::Index;
use std::ops::IndexMut;
use std::ops::RangeBounds;

mod private {
    pub trait Sealed {}

    impl<T> Sealed for Vec<T> {}
    impl<'a, T> Sealed for &'a [T] {}
    impl<'a, T> Sealed for &'a mut [T] {}
}

pub trait Array2DData: private::Sealed + Borrow<[<Self as Array2DData>::Element]> {
    type Element: Clone;
}

impl<T: Clone> Array2DData for Vec<T> {
    type Element = T;
}

impl<'a, T: Clone> Array2DData for &'a [T] {
    type Element = T;
}

impl<'a, T: Clone> Array2DData for &'a mut [T] {
    type Element = T;
}

/// column-major 2D array
///
/// The alternate display format (using `"{:#}"`) is a reStructuredText table
///
/// Examples:
/// ```
/// # use algebraics::array2d::Array2DOwned;
/// // Note: using strings to demonstrate `Display`, numbers are normally used
/// let mut array = Array2DOwned::from_array(
///     3,
///     3,
///     vec!["0", "1", "2", "10", "11", "12", "20", "21", "22"],
/// );
/// assert_eq!(
///     format!("{}", array),
///     "[ 0  10  20 ]\n\
///      [ 1  11  21 ]\n\
///      [ 2  12  22 ]"
/// );
/// assert_eq!(
///     format!("{:#}", array),
///     "+---+----+----+\n\
///      | 0 | 10 | 20 |\n\
///      +---+----+----+\n\
///      | 1 | 11 | 21 |\n\
///      +---+----+----+\n\
///      | 2 | 12 | 22 |\n\
///      +---+----+----+"
/// );
/// // change the value at x=0, y=2 to a multi-line str
/// array[(0, 2)] = "line 1\nline 2";
///
/// assert_eq!(
///     format!("{}", array),
///     "[ 0       10  20 ]\n\
///      [                ]\n\
///      [ 1       11  21 ]\n\
///      [                ]\n\
///      [ line 1  12  22 ]\n\
///      [ line 2         ]"
/// );
/// assert_eq!(
///     format!("{:#}", array),
///     "+--------+----+----+\n\
///      | 0      | 10 | 20 |\n\
///      +--------+----+----+\n\
///      | 1      | 11 | 21 |\n\
///      +--------+----+----+\n\
///      | line 1 | 12 | 22 |\n\
///      | line 2 |    |    |\n\
///      +--------+----+----+"
/// );
/// ```
#[derive(Copy, Clone, Hash, Eq, PartialEq, Debug)]
pub struct Array2DBase<Data: Array2DData> {
    x_size: usize,
    y_size: usize,
    stride: usize,
    data: Data,
}

struct Array2DSliceData {
    x_size: usize,
    y_size: usize,
    data_offset: usize,
}

impl<Data: Array2DData> Array2DBase<Data> {
    /// data is a column-major 2D array
    pub fn from_array<T: Into<Data>>(x_size: usize, y_size: usize, data: T) -> Self {
        let data = data.into();
        assert_eq!(x_size * y_size, data.borrow().len());
        Self {
            x_size,
            y_size,
            stride: x_size,
            data,
        }
    }
    pub fn x_size(&self) -> usize {
        self.x_size
    }
    pub fn y_size(&self) -> usize {
        self.y_size
    }
    fn get_index_unchecked(&self, x: usize, y: usize) -> usize {
        x * self.stride + y
    }
    fn get_index(&self, x: usize, y: usize) -> usize {
        assert!(x < self.x_size);
        assert!(y < self.y_size);
        self.get_index_unchecked(x, y)
    }
    fn do_slice(
        &self,
        x_start_bound: Bound<&usize>,
        x_end_bound: Bound<&usize>,
        y_start_bound: Bound<&usize>,
        y_end_bound: Bound<&usize>,
    ) -> Array2DSliceData {
        fn start(bound: Bound<&usize>) -> usize {
            match bound {
                Bound::Unbounded => 0,
                Bound::Excluded(&v) => v + 1,
                Bound::Included(&v) => v,
            }
        }
        fn end(bound: Bound<&usize>, size: usize) -> usize {
            match bound {
                Bound::Unbounded => size,
                Bound::Excluded(&v) => v,
                Bound::Included(&v) => v - 1,
            }
        }
        let x_start = start(x_start_bound);
        let x_end = end(x_end_bound, self.x_size);
        let y_start = start(y_start_bound);
        let y_end = end(y_end_bound, self.y_size);
        assert!(x_start <= x_end);
        assert!(x_end <= self.x_size);
        assert!(y_start <= y_end);
        assert!(y_end <= self.y_size);
        Array2DSliceData {
            x_size: x_end - x_start,
            y_size: y_end - y_start,
            data_offset: self.get_index_unchecked(x_start, y_start),
        }
    }
    pub fn slice<XR: RangeBounds<usize>, YR: RangeBounds<usize>>(
        &self,
        x: XR,
        y: YR,
    ) -> Array2DSlice<Data::Element> {
        let Array2DSliceData {
            x_size,
            y_size,
            data_offset,
        } = self.do_slice(
            x.start_bound(),
            x.end_bound(),
            y.start_bound(),
            y.end_bound(),
        );
        Array2DBase {
            x_size,
            y_size,
            stride: self.stride,
            data: &self.data.borrow()[data_offset..],
        }
    }
    pub fn slice_mut<XR: RangeBounds<usize>, YR: RangeBounds<usize>>(
        &mut self,
        x: XR,
        y: YR,
    ) -> Array2DMutSlice<Data::Element>
    where
        Data: BorrowMut<[<Data as Array2DData>::Element]>,
    {
        let Array2DSliceData {
            x_size,
            y_size,
            data_offset,
        } = self.do_slice(
            x.start_bound(),
            x.end_bound(),
            y.start_bound(),
            y.end_bound(),
        );
        Array2DBase {
            x_size,
            y_size,
            stride: self.stride,
            data: &mut self.data.borrow_mut()[data_offset..],
        }
    }
}

impl<Data: Array2DData> Index<(usize, usize)> for Array2DBase<Data> {
    type Output = Data::Element;
    fn index(&self, (vector_index, element_index): (usize, usize)) -> &Self::Output {
        let index = self.get_index(vector_index, element_index);
        &self.data.borrow()[index]
    }
}

impl<Data: Array2DData + BorrowMut<[<Data as Array2DData>::Element]>> IndexMut<(usize, usize)>
    for Array2DBase<Data>
{
    fn index_mut(&mut self, (vector_index, element_index): (usize, usize)) -> &mut Self::Output {
        let index = self.get_index(vector_index, element_index);
        &mut self.data.borrow_mut()[index]
    }
}

impl<T: fmt::Display + Clone, Data: Array2DData<Element = T>> fmt::Display for Array2DBase<Data> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.x_size() == 0 || self.y_size() == 0 {
            return writeln!(f, "[x_size={}, y_size={}]", self.x_size(), self.y_size());
        }
        let mut cells: Vec<Vec<String>> = Vec::new();
        let mut row_heights = vec![0usize; self.y_size()];
        let mut col_widths = vec![0usize; self.x_size()];
        cells.resize(self.y_size(), Vec::with_capacity(self.x_size()));
        let mut any_multiline_cells = false;
        for y in 0..self.y_size() {
            for x in 0..self.x_size() {
                let cell_str = format!("{}", self[(x, y)]);
                let mut width = 1;
                let mut height = 0;
                for line in cell_str.lines() {
                    height += 1;
                    width = width.max(line.len());
                }
                height = height.max(1);
                if height > 1 {
                    any_multiline_cells = true;
                }
                row_heights[y] = row_heights[y].max(height);
                col_widths[x] = col_widths[x].max(width);
                cells[y].push(cell_str);
            }
        }
        let write_separator_line = |f: &mut fmt::Formatter| {
            for &col_width in &col_widths {
                write!(f, "+-")?;
                for _ in 0..col_width {
                    write!(f, "-")?;
                }
                write!(f, "-")?;
            }
            write!(f, "+")
        };
        if f.alternate() {
            write_separator_line(f)?;
            writeln!(f)?;
        }
        for y in 0..self.y_size() {
            let is_last_row = y == self.y_size() - 1;
            let mut line_iters: Vec<_> = cells[y].iter().map(|cell| cell.lines()).collect();
            let mut height = row_heights[y];
            if !f.alternate() && any_multiline_cells && !is_last_row {
                height += 1;
            }
            for cell_row in 0..height {
                if !f.alternate() {
                    write!(f, "[")?;
                }
                for x in 0..self.x_size() {
                    let cell_line = line_iters[x].next().unwrap_or("");
                    if f.alternate() {
                        write!(f, "|")?;
                    }
                    write!(
                        f,
                        " {cell_line:width$} ",
                        cell_line = cell_line,
                        width = col_widths[x]
                    )?;
                }
                if f.alternate() {
                    write!(f, "|")?;
                } else {
                    write!(f, "]")?;
                }
                if cell_row != height - 1 {
                    writeln!(f)?;
                }
            }
            if f.alternate() {
                writeln!(f)?;
                write_separator_line(f)?;
            }
            if !is_last_row {
                writeln!(f)?;
            }
        }
        Ok(())
    }
}

pub type Array2DOwned<T> = Array2DBase<Vec<T>>;
pub type Array2DSlice<'a, T> = Array2DBase<&'a [T]>;
pub type Array2DMutSlice<'a, T> = Array2DBase<&'a mut [T]>;
