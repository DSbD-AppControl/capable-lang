/* A Rust Runtime for Capable Lang.

Here we provide an implementation of various primitives and builtins required by all capable programs.

This is a temporay quick support module for experimenting.
We will turn it into a proper Rust crate/module whatever later.

Still TODO

1. Sort out the file API.
2. Sort out managed session runtime...
3. Sort out bespoke elaboration for structs and enums...
4. Work out naming schemes and how functions are to be named.

 */

// Imports

use std::fs::File;
use std::process::Child;
use std::cell::Cell;
use std::env;
use std::io::{self, Write};

/* # Primitives i.e. Builtins

## Definitions

Primitives are custom types

Tuples are translated directly into rust tuples.

Compound types are translated to rust types

We provide a few bespoke instances for Either and POpen2 that are used internally.

*/

enum CapableUnit { Unit }

#[derive(Clone,Default)]
struct CapableChar { value : char }

#[derive(Clone,Default)]
struct CapableInt { value : u32 }

#[derive(Clone,Default)]
struct CapableString { value : String}

#[derive(Clone,Default)]
struct CapableBool { value : bool}

// Not sure if File and Child are the correct types...
enum CapableHandle
{
    CapableFile(File), CapableProc(Child)
}

// Lists are just vects (n.b. vectors are [type;size])
type CapableList<T> = Vec<T>;

type CapableRef<T> = Cell<T>;

/// Used internally
enum CapableEither<L,R>
{
    Left(L),
    Right(R),
}

/// Used internally probably good to transform this to SubProcess
struct CapablePOpen2
{
    writeTo : Child,
    readFrom : Child,
}

// ## Constructors for Primitives

fn capable_char ( c : char ) -> CapableChar
{
    CapableChar { value : c }
}

fn capable_unit() -> CapableUnit
{
    CapableUnit::Unit
}

fn capable_string(s : &str) -> CapableString
{
    CapableString { value : String::from(s) }
}

fn capable_int(i : u32) -> CapableInt
{
    CapableInt { value : i }
}

fn capable_bool(b : bool) -> CapableBool
{
    CapableBool { value : b}
}

// # Char operations

fn capable_ord (c : CapableChar) -> CapableInt
{
    capable_int( c.value.into())
}

fn capable_chr (c : CapableInt) -> CapableChar
{
    unsafe {
        capable_char(char::from_u32_unchecked(c.value))
    }
}

fn capable_singleton (c : CapableChar) -> CapableString
{
    CapableString { value : c.value.to_string()}
}

// ## Math
fn capable_int_add(x : CapableInt, y : CapableInt) -> CapableInt
{
    CapableInt { value : x.value + y.value }
}

fn capable_int_sub(x : CapableInt, y : CapableInt) -> CapableInt
{
    CapableInt { value : x.value - y.value }
}

fn capable_int_div(x : CapableInt, y : CapableInt) -> CapableInt
{
    CapableInt { value : x.value / y.value }
}

fn capable_int_mul(x : CapableInt, y : CapableInt) -> CapableInt
{
    CapableInt { value : x.value * y.value }
}

// # Boolean
fn capable_bool_and(x : CapableBool, y : CapableBool) -> CapableBool
{
    CapableBool { value : x.value && y.value }
}

fn capable_bool_ior(x : CapableBool, y : CapableBool) -> CapableBool
{
    CapableBool { value : x.value || y.value }
}

fn capable_bool_not(x : CapableBool) -> CapableBool
{
    CapableBool { value : !x.value }
}

// # Comparable Things
trait CapableComparable
{
    fn capable_lt(&self, y : Self) -> CapableBool;
    fn capable_lte(&self, y : Self) -> CapableBool;
    fn capable_eq(&self, y : Self) -> CapableBool;
    fn capable_gte(&self, y : Self) -> CapableBool;
    fn capable_gt(&self, y : Self) -> CapableBool;
    fn capable_to_string(&self) -> CapableString;
}

impl CapableComparable for CapableBool
{
    fn capable_lt(&self, y : CapableBool) -> CapableBool
    {
        CapableBool { value : self.value < y.value }
    }

    fn capable_lte(&self, y : CapableBool) -> CapableBool
    {
        CapableBool { value : self.value <= y.value }
    }
    fn capable_eq(&self, y : CapableBool) -> CapableBool
    {
        CapableBool { value : self.value == y.value }
    }
    fn capable_gte(&self, y : CapableBool) -> CapableBool
    {
        CapableBool { value : self.value >= y.value }
    }
    fn capable_gt(&self, y : CapableBool) -> CapableBool
    {
        CapableBool { value : self.value > y.value }
    }
    fn capable_to_string(&self) -> CapableString
    {
        CapableString { value : self.value.to_string()}
    }
}
impl CapableComparable for CapableInt
{
    fn capable_lt(&self, y : CapableInt) -> CapableBool
    {
        CapableBool { value : self.value < y.value }
    }

    fn capable_lte(&self, y : CapableInt) -> CapableBool
    {
        CapableBool { value : self.value <= y.value }
    }
    fn capable_eq(&self, y : CapableInt) -> CapableBool
    {
        CapableBool { value : self.value == y.value }
    }
    fn capable_gte(&self, y : CapableInt) -> CapableBool
    {
        CapableBool { value : self.value >= y.value }
    }
    fn capable_gt(&self, y : CapableInt) -> CapableBool
    {
        CapableBool { value : self.value > y.value }
    }
    fn capable_to_string(&self) -> CapableString
    {
        CapableString { value : self.value.to_string()}
    }
}

impl CapableComparable for CapableChar
{
    fn capable_lt(&self, y : CapableChar) -> CapableBool
    {
        CapableBool { value : self.value < y.value }
    }

    fn capable_lte(&self, y : CapableChar) -> CapableBool
    {
        CapableBool { value : self.value <= y.value }
    }
    fn capable_eq(&self, y : CapableChar) -> CapableBool
    {
        CapableBool { value : self.value == y.value }
    }
    fn capable_gte(&self, y : CapableChar) -> CapableBool
    {
        CapableBool { value : self.value >= y.value }
    }
    fn capable_gt(&self, y : CapableChar) -> CapableBool
    {
        CapableBool { value : self.value > y.value }
    }
    fn capable_to_string(&self) -> CapableString
    {
        CapableString { value : self.value.to_string()}
    }

}

impl CapableComparable for CapableString
{
    fn capable_lt(&self, y : CapableString) -> CapableBool
    {
        CapableBool { value : self.value < y.value }
    }

    fn capable_lte(&self, y : CapableString) -> CapableBool
    {
        CapableBool { value : self.value <= y.value }
    }
    fn capable_eq(&self, y : CapableString) -> CapableBool
    {
        CapableBool { value : self.value == y.value }
    }
    fn capable_gte(&self, y : CapableString) -> CapableBool
    {
        CapableBool { value : self.value >= y.value }
    }
    fn capable_gt(&self, y : CapableString) -> CapableBool
    {
        CapableBool { value : self.value > y.value }
    }
    fn capable_to_string(&self) -> CapableString
    {
        let x = self ;
        capable_string(&x.value)
    }

}

// ## String Operations

fn capable_string_length(x : CapableString) -> CapableInt
{
    let l = x.value.len() as u32;
    CapableInt { value : l }
}

fn capable_string_cons(x : CapableChar, y : CapableString) -> CapableString
{
    CapableString { value : format!("{}{}", x.value.to_string(), y.value) }
}


fn capable_string_slice( x : CapableInt
                       , y : CapableInt
                       , z : CapableString
                       )  -> CapableString
{
    let start = x.value as usize;
    let end = y.value as usize;
    let st = &z.value[start..end];
    CapableString { value : String::from(st)}
}


// ## Memories

fn capable_ref_alloc<T>(v : T) -> CapableRef<T>
{
    Cell::new(v)
}

fn capable_ref_fetch<T>(r : &CapableRef<T>)
                         ->             T where T : Clone + Default

{
    let v = r.take();
    let vc = v.clone();
    r.set(v);
    vc
}

fn capable_ref_mutate<T>(r : &CapableRef<T>, v : T)
                          -> CapableUnit
{
    r.set(v);
    capable_unit()
}

// # File and Process Effects
// @TODO POpen2 STR -> Either Int Popen2
// @TODO Open (kind) mode... STR -> Either Int HANDLE
// @TODO ReadLn  Handle -> Either INT String
// @TODO WriteLn Handle String -> Int UNIT
// @TODO Close Handle -> Unit

// # Misc Effects

fn capable_print(s : CapableString) -> CapableUnit
{
    print!("{}",s.value);
    io::stdout().flush().unwrap();
    CapableUnit::Unit
}

// # An example of what a generated Program coudl look like.

fn capable_main( args : CapableList<CapableString>) -> CapableUnit
{
    let i = capable_int(1);
    let a = capable_ref_alloc(i);
    capable_print(capable_ref_fetch(&a)
                  .capable_lt(capable_int(4))
                  .capable_to_string()
                 );
    capable_ref_mutate(&a,capable_int(4));
    capable_print(capable_ref_fetch(&a).capable_to_string());

    let i = capable_string("123");
    let a = capable_ref_alloc(i);
    capable_print(capable_ref_fetch(&a).capable_to_string());

    capable_unit()
}

// # Boiler plate to execute generated programs.

fn capable_args() -> CapableList<CapableString>
{
  let args : Vec<String> = env::args().collect()
; args.iter().map(|a| capable_string(a)).collect()
}

fn capable_run( u : CapableUnit)
{
  match u { CapableUnit::Unit => () }
}

fn main ()
{
  capable_run(capable_main(capable_args()))
}

// [ EOF ]
