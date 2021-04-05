// Copyright 2020 METAFONT-rs Author(s)
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
// ------------------------OR----------------------------
// Copyright 2020 METAFONT-rs Author(s)
//
// Permission is hereby granted, free of charge, to any
// person obtaining a copy of this software and associated
// documentation files (the "Software"), to deal in the
// Software without restriction, including without
// limitation the rights to use, copy, modify, merge,
// publish, distribute, sublicense, and/or sell copies of
// the Software, and to permit persons to whom the Software
// is furnished to do so, subject to the following
// conditions:
//
// The above copyright notice and this permission notice
// shall be included in all copies or substantial portions
// of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF
// ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED
// TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A
// PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT
// SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
// CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
// OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR
// IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
// DEALINGS IN THE SOFTWARE.

// -------------------------------------------------------
// `METAFONT-rs` originates from the `METAFONT` program, which was
// created by Donald Knuth and released under his usual license:
// http://www.ctan.org/license/knuth.

// TeX is a trademark of the American Mathematical Society.
// METAFONT is a trademark of Addison-Wesley Publishing Company.
#![feature(pub_macro_rules, const_panic)]
#![deny(warnings, missing_docs, missing_debug_implementations)]
#![allow(
    dead_code,
    non_upper_case_globals,
    non_camel_case_types,
    unused_imports,
    unused_doc_comments
)]
#![allow(unreachable_code, unused_macros)]
//! This is METAFONT, a font compiler intended to produce typefaces of high quality.

mod info;
mod pascal;

mod section_0001;
mod section_0002;
mod section_0003;
mod section_0004;
mod section_0005_to_0015;
mod section_0016;
mod section_0017_to_0023;
mod section_0024;
mod section_0025_to_0030;
mod section_0031;
mod section_0032;
mod section_0033;
mod section_0034_to_0053;
mod section_0054;
mod section_0055;
mod section_0056;
mod section_0057_to_0070;
mod section_0071;
mod section_0072_to_0075;
mod section_0076;
mod section_0077_to_0154;
mod section_0155;
mod section_0156;
mod section_0157_to_0199;
mod section_0200;
mod section_0201_to_0623;
mod section_0624;
mod section_0625_to_0651;
mod section_0652;
mod section_0653_to_1016;
mod section_1017;
mod section_1018_to_1076;
mod section_1077;
mod section_1078;
mod section_1079_to_1202;
mod section_1203;
mod section_1204;
mod section_1205;
mod section_1206_to_1208;
mod section_1209;
mod section_1210;
mod section_1211;
mod section_1212;
mod section_1213;
mod section_1214;
mod section_1215;

pub use section_0004::MetafontSystem;
