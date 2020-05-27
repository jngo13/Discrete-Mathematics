-- Justin Ngo
-- jmn4fms
-- 2/3/20
-- Sullivan 2102-001
/-
3. [30 points]

Define a polymorphic ADT called dm_box. This type
builder takes one type argument. The intuitive 
idea is that a dm_box contains one value of the
type specified by the type argument. Define dm_box 
to have one constructor, mk, that takes one value 
of the specified type and that produces a dm_box
with that value stored "in" the box. Note: a box
is very much like an ordered pair but it contains
only one value, not two.  Define one "inspector"
function, unbox, that takes a dm_box and returns
the value "inside" the box. Write unbox, unbox',
and unbox'', using respectively lambda, C-style,
and cases syntax. Put your definitions in a file,
dm_box.lean, and write a few test cases, using
values of different types, in dm_box_test.lean.
-/

inductive dm_box (value:Type): Type
| mk: value → dm_box --first type of dm_box

open dm_box --data type has its own namespace

--Lamda style
def unbox {value: Type}: dm_box value → value :=
    λ (b: dm_box value),
        match b with
        |  dm_box.mk x := x
end

-- C style
def unbox' {value: Type} (b: dm_box value):=
    match b with
    |(dm_box.mk x) := x
end

-- By case
def unbox'' {value: Type}: (dm_box value) → value
    |(dm_box.mk x) := x