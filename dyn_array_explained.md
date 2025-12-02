# dyn_array.vpr - Line-by-Line Explanation

This document provides a detailed line-by-line explanation of `dyn_array.vpr`, covering dynamic arrays with amortized analysis in Viper.

---

## File Overview

This file implements a dynamic array (like Java's ArrayList or Python's list) with:
1. **Automatic resizing**: Array doubles when full
2. **Amortized O(1) append**: Uses time credit accounting to prove constant amortized time
3. **Predicate-based abstraction**: Encapsulates array state and permissions

---

## Lines 1-12: Runtime Model

```viper
// -----------------------------------------
// Runtime model
// Notice that we can hold at most one permission
// to *fields*, but this does not apply to *predicates*
predicate time_credit() // represents one abstract unit of time

// models spending an abstract unit of time 
// needs to be called at the beginning of every method
// and loop iteration
method consume_time_credit() // 
    requires acc(time_credit(), 1/1)
// -----------------------------------------
```

**Key Comment**: "we can hold at most one permission to *fields*, but this does not apply to *predicates*"

This is crucial:
- **Fields**: Can only have permission 0 to 1 (fractional)
- **Predicates**: Can have multiple instances (like holding 10 time_credit predicates)

---

## Lines 14-29: Object Model (Fields)

```viper
// -----------------------------------------
// Object model
// You can add ghost fields if you want.

// Fields of dynamic array objects
field length: Int // how many elements are currently stored in the array
field capacity: Int // how many elements can be stored in the array
field array: StaticArray // the static array storing the actual elements, see below
field credits: Int // ghost field: saved time credits for amortized analysis


// Fields of individual array elements
field entry: Int // the value of the array element
// -----------------------------------------
```

### Line 19: `field length: Int`

**Viper Syntax**:
- `field name: Type` declares a field that objects can have
- Fields are accessed via references (Ref type)

**Purpose**: Number of elements currently stored.

### Line 20: `field capacity: Int`

**Purpose**: Total slots available in the underlying array.

### Line 21: `field array: StaticArray`

**Viper Syntax**:
- Fields can have domain types (user-defined types)
- `StaticArray` is defined below as a domain

**Purpose**: Pointer to the actual storage.

### Line 22: `field credits: Int`

**Purpose**: 
- **Ghost field** - only for verification, not runtime
- Tracks saved time credits for amortized analysis
- Each append saves credits for future grow operations

### Line 26: `field entry: Int`

**Purpose**: The value stored at each array position.

---

## Lines 31-48: StaticArray Domain

```viper
// -----------------------------------------
// Static arrays with field entry as in module 11
domain StaticArray {
    function loc(a: StaticArray, i: Int): Ref
    function len(a: StaticArray): Int
    function first(r: Ref): StaticArray
    function second(r: Ref): Int

    axiom injectivity {
        forall a: StaticArray, i: Int :: {loc(a, i)}
        first(loc(a, i)) == a && second(loc(a, i)) == i
    }

    axiom length_nonneg {
        forall a: StaticArray :: len(a) >= 0
    }
}
// -----------------------------------------
```

### Line 33: `domain StaticArray { ... }`

**Viper Syntax**:
- `domain Name { ... }` defines an abstract data type
- Contains function declarations and axioms
- Functions are uninterpreted (defined only by axioms)

**Purpose**: Models fixed-size arrays (like C arrays).

### Line 34: `function loc(a: StaticArray, i: Int): Ref`

**Purpose**: 
- Returns a reference to position i in array a
- `loc(a, 5)` is like `&a[5]` in C

### Line 35: `function len(a: StaticArray): Int`

**Purpose**: Returns the length of the array.

### Lines 36-37: Inverse Functions

```viper
    function first(r: Ref): StaticArray
    function second(r: Ref): Int
```

**Purpose**: Given a reference from `loc`, recover the array and index.

### Lines 39-42: Injectivity Axiom

```viper
    axiom injectivity {
        forall a: StaticArray, i: Int :: {loc(a, i)}
        first(loc(a, i)) == a && second(loc(a, i)) == i
    }
```

**Viper Syntax**:
- `axiom name { formula }` declares an axiom (assumed true)
- `forall x: Type :: formula` is universal quantification
- `{loc(a, i)}` is a **trigger** - tells when to instantiate the axiom

**Purpose**: 
- States that loc is injective (different positions give different refs)
- first(loc(a,i)) = a and second(loc(a,i)) = i

### Lines 44-46: Length Non-negative

```viper
    axiom length_nonneg {
        forall a: StaticArray :: len(a) >= 0
    }
```

**Purpose**: Array lengths are never negative.

---

## Lines 50-71: Shortcuts for Static Arrays

```viper
// -----------------------------------------
// Shortcuts for using static arrays

// a[i] for static array a
define lookup(a, i)
    loc(a, i).entry

// a[i] := e for static array a
define update(a, i, e) { 
    loc(a, i).entry := e
}

// Permissions to elements of static array a
define staticArray(a)
    (forall i: Int :: {loc(a, i)}  0 <= i && i < len(a) ==> acc(loc(a, i).entry)) 

// Allocate a new static array a of length l
// You can (reasonably) use this to create a new array
// Warning: do not use twice with the same arguments.
define alloc(a, l) {
    inhale staticArray(a) && len(a) == l
}
// -----------------------------------------
```

### Line 54: `define lookup(a, i)`

**Viper Syntax**:
- `define name(params) expression` creates a macro
- Macros are textually substituted (like C #define)

**Purpose**: `lookup(a, i)` expands to `loc(a, i).entry` (reading a[i]).

### Lines 57-59: Update Macro

```viper
define update(a, i, e) { 
    loc(a, i).entry := e
}
```

**Purpose**: `update(a, i, e)` expands to assignment a[i] := e.

### Lines 62-63: staticArray Macro

```viper
define staticArray(a)
    (forall i: Int :: {loc(a, i)}  0 <= i && i < len(a) ==> acc(loc(a, i).entry)) 
```

**Viper Syntax**:
- `acc(field)` is shorthand for `acc(field, write)` (full permission)
- `forall ... ==> acc(...)` means "permission to all elements"

**Purpose**: 
- Represents permission to all elements of array a
- "For all i from 0 to len(a)-1, we have write permission to a[i]"

### Lines 67-70: Alloc Macro

```viper
define alloc(a, l) {
    inhale staticArray(a) && len(a) == l
}
```

**Viper Syntax**:
- `inhale formula` adds permissions/facts to the current state
- Opposite of `exhale` which removes them

**Purpose**:
- Models memory allocation
- Creates a new array with permissions to all elements
- `inhale` is an assumption - we trust this models allocation correctly

---

## Lines 73-93: Dynamic Array Predicate

```viper
// -----------------------------------------
// TASK 3.1: Give a predicate modelling the data structure invariants and permissions
//         of dynamic arrays. You may also store other (ghost) information
//         such as time credits needed for amortized analysis.
//         Feel free to add acessor functions to simplify fold-unfold reasoning.
predicate dyn_array(self: Ref) {
    // Permissions to fields
    acc(self.length) && acc(self.capacity) && acc(self.array) && acc(self.credits) &&
    // Permissions to all array elements
    staticArray(self.array) &&
    // Data structure invariants
    0 <= self.length &&
    self.length <= self.capacity &&
    0 < self.capacity &&
    len(self.array) == self.capacity &&
    // Time credit invariants for amortized analysis
    // We track credits >= 0. The actual amount depends on usage pattern.
    // The grow method requires sufficient credits to copy all elements.
    self.credits >= 0 &&
    acc(time_credit(), self.credits/1)
}
```

### Line 78: `predicate dyn_array(self: Ref) { ... }`

**Viper Syntax**:
- `predicate name(params) { body }` defines a predicate with a body
- Unlike abstract predicates, this has content
- Must be **folded** (hidden) or **unfolded** (exposed) to access

**Purpose**: Encapsulates all state and invariants of a dynamic array.

### Line 80: `acc(self.length) && acc(self.capacity) && ...`

**Purpose**: Permission to all four fields of the dynamic array object.

### Line 82: `staticArray(self.array)`

**Purpose**: Permission to all elements in the underlying static array.

### Lines 84-87: Data Structure Invariants

```viper
    0 <= self.length &&
    self.length <= self.capacity &&
    0 < self.capacity &&
    len(self.array) == self.capacity &&
```

**Purpose**:
- length is non-negative
- length never exceeds capacity
- capacity is positive
- underlying array has size = capacity

### Lines 90-91: Time Credit Invariants

```viper
    self.credits >= 0 &&
    acc(time_credit(), self.credits/1)
```

**Purpose**:
- credits field tracks how many time credits are "saved"
- Actually store that many time_credit permissions inside the predicate
- `self.credits/1` means `self.credits` full time credits

---

## Lines 96-107: Accessor Functions

```viper
// Accessor functions for commonly needed fields
function arr_length(base: Ref): Int 
    requires acc(dyn_array(base))
{ unfolding acc(dyn_array(base)) in base.length }

function arr_capacity(base: Ref): Int
    requires acc(dyn_array(base))
{ unfolding acc(dyn_array(base)) in base.capacity }

function arr_credits(base: Ref): Int
    requires acc(dyn_array(base))
{ unfolding acc(dyn_array(base)) in base.credits }
```

### Line 97: `function arr_length(base: Ref): Int`

**Purpose**: Get length without permanently unfolding the predicate.

### Line 98: `requires acc(dyn_array(base))`

**Purpose**: Need permission to the predicate to read from it.

### Line 99: `{ unfolding acc(dyn_array(base)) in base.length }`

**Viper Syntax**:
- `unfolding acc(predicate) in expression` temporarily unfolds a predicate
- During evaluation of `expression`, the predicate body is accessible
- Predicate is automatically re-folded after

**Purpose**: Access `base.length` without permanently changing state.

---

## Lines 116-143: Constructor Method

```viper
method cons(_capacity: Int) returns (arr: Ref)
    requires 0 < _capacity
    requires acc(time_credit(), 1/1)
    ensures acc(dyn_array(arr))
    ensures unfolding acc(dyn_array(arr)) in arr.length == 0
    ensures unfolding acc(dyn_array(arr)) in arr.capacity == _capacity
{
    consume_time_credit() // every method call must consume a time credit
    
    // Allocate new object
    arr := new(length, capacity, array, credits)
    arr.length := 0
    arr.capacity := _capacity
    arr.credits := 0
    
    // Allocate the static array
    alloc(arr.array, _capacity)
    
    // Fold the predicate
    fold acc(dyn_array(arr))
}
```

### Line 117: `method cons(_capacity: Int) returns (arr: Ref)`

**Viper Syntax**:
- Parameters starting with `_` is just naming convention
- Return type `Ref` is a reference to a heap object

### Line 120: `ensures acc(dyn_array(arr))`

**Purpose**: 
- Postcondition: caller receives permission to a dyn_array predicate
- The newly created array is encapsulated in the predicate

### Lines 121-122: Postconditions with Unfolding

```viper
    ensures unfolding acc(dyn_array(arr)) in arr.length == 0
    ensures unfolding acc(dyn_array(arr)) in arr.capacity == _capacity
```

**Purpose**: 
- Specify properties about the array's internal state
- Must use `unfolding` because the predicate is folded

### Line 127: `arr := new(length, capacity, array, credits)`

**Viper Syntax**:
- `new(field1, field2, ...)` allocates a new object with given fields
- Returns a fresh reference
- Gives write permission to all listed fields

### Line 134: `alloc(arr.array, _capacity)`

**Purpose**: Create the underlying static array.

### Line 137: `fold acc(dyn_array(arr))`

**Viper Syntax**:
- `fold acc(predicate)` packages state into a predicate
- Before fold: must have all permissions and satisfy all invariants
- After fold: have permission to predicate, lose direct field access

---

## Lines 148-166: Abstraction Function

```viper
function arr_contents(base: Ref): Seq[Int]
    requires acc(dyn_array(base))
{
    unfolding acc(dyn_array(base)) in 
        (base.length == 0 ? Seq[Int]() : arr_contents_helper(base.array, 0, base.length))
}

// Helper function to build sequence from static array
function arr_contents_helper(a: StaticArray, from: Int, to: Int): Seq[Int]
    requires 0 <= from && from <= to && to <= len(a)
    requires forall i: Int :: {loc(a, i)} from <= i && i < to ==> acc(loc(a, i).entry)
{
    from == to ? Seq[Int]() : 
        arr_contents_helper(a, from, to - 1) ++ Seq(lookup(a, to - 1))
}
```

### Line 148: `function arr_contents(base: Ref): Seq[Int]`

**Viper Syntax**:
- `Seq[Int]` is a mathematical sequence type (immutable list)
- Built-in type in Viper for specification

**Purpose**: Maps concrete array to abstract sequence of values.

### Line 152: `Seq[Int]()`

**Viper Syntax**:
- `Seq[T]()` creates an empty sequence

### Line 161: `arr_contents_helper(a, from, to - 1) ++ Seq(lookup(a, to - 1))`

**Viper Syntax**:
- `++` is sequence concatenation
- `Seq(value)` creates a singleton sequence

**Purpose**: Recursively builds sequence from right to left.

---

## Lines 177-208: append_nogrow Method

```viper
method append_nogrow(arr: Ref, val: Int)
    requires acc(dyn_array(arr))
    requires arr_length(arr) < arr_capacity(arr)
    requires acc(time_credit(), 4/1) // Need 4 credits: 1 for execution, 3 to save
    ensures acc(dyn_array(arr))
    ensures arr_length(arr) == old(arr_length(arr)) + 1
    ensures arr_capacity(arr) == old(arr_capacity(arr))
    ensures arr_credits(arr) == old(arr_credits(arr)) + 3 // We save 3 credits
{
    consume_time_credit() 
    
    var old_len: Int := arr_length(arr)
    var old_credits: Int := arr_credits(arr)
    
    unfold acc(dyn_array(arr))
    var arr_array: StaticArray := arr.array
    
    update(arr_array, arr.length, val) // append value
    arr.length := arr.length + 1 // we appended an element
    
    // Save THREE time credits for future grow operation
    arr.credits := arr.credits + 3
    
    fold acc(dyn_array(arr))
}
```

### Line 179: `requires arr_length(arr) < arr_capacity(arr)`

**Purpose**: Can only call this when there's room (no need to grow).

### Line 180: `requires acc(time_credit(), 4/1)`

**Purpose**: 
- Need 4 credits: 1 for method, 3 to save
- The saved credits pay for future grow operations

### Line 183: `ensures arr_length(arr) == old(arr_length(arr)) + 1`

**Viper Syntax**:
- `old(expression)` refers to value at method entry
- Evaluated in pre-state, usable in postcondition

**Purpose**: Length increases by 1.

### Line 185: `ensures arr_credits(arr) == old(arr_credits(arr)) + 3`

**Purpose**: We save 3 credits for amortized analysis.

### Line 192: `unfold acc(dyn_array(arr))`

**Viper Syntax**:
- `unfold acc(predicate)` opens a predicate
- After unfold: have access to fields and array elements
- Predicate permission is "spent" - must fold again later

### Line 200: `arr.credits := arr.credits + 3`

**Purpose**: 
- Save 3 time credits inside the data structure
- This is the key to amortized analysis!
- When we grow later, we'll use these saved credits

---

## Lines 222-302: grow Method

```viper
method grow(arr: Ref) returns (new_arr: Ref)
    requires acc(dyn_array(arr))
    requires unfolding acc(dyn_array(arr)) in arr.credits >= arr.length
    requires acc(time_credit(), 1/1) // Only constant time credits from caller
    ensures acc(dyn_array(new_arr))
    ensures arr_length(new_arr) == old(arr_length(arr))
    ensures arr_capacity(new_arr) == 2 * old(arr_capacity(arr))
{
    consume_time_credit()
    
    // ... setup code ...
    
    unfold acc(dyn_array(arr))
    
    // create a new dynamic array with twice the capacity
    new_arr := new(length, capacity, array, credits)
    new_arr.capacity := 2 * arr.capacity
    new_arr.length := arr.length
    new_arr.credits := 0
    alloc(new_arr.array, new_arr.capacity)
    
    // ... ghost variable setup ...
    
    var pos: Int := 0
    while (pos < old_len)
        invariant 0 <= pos && pos <= old_len
        invariant new_len == old_len
        invariant new_cap == 2 * old_cap
        invariant len(new_static_arr) == new_cap
        invariant staticArray(new_static_arr)
        invariant staticArray(old_static_arr)
        invariant len(old_static_arr) == old_cap
        invariant old_arr_credits >= old_len - pos
        invariant acc(time_credit(), old_arr_credits/1)
        invariant acc(arr.length) && acc(arr.capacity) && acc(arr.array) && acc(arr.credits)
        invariant arr.array == old_static_arr
        invariant forall i: Int :: {loc(new_static_arr, i)} 0 <= i && i < pos ==> 
            lookup(new_static_arr, i) == lookup(old_static_arr, i)
    {
        consume_time_credit()
        old_arr_credits := old_arr_credits - 1
        update(new_static_arr, pos, lookup(old_static_arr, pos))
        pos := pos + 1
    }
    
    new_arr.credits := old_arr_credits
    
    fold acc(dyn_array(new_arr))
}
```

### Line 224: `requires unfolding acc(dyn_array(arr)) in arr.credits >= arr.length`

**Purpose**:
- Need enough saved credits to pay for copying
- Each iteration costs 1 credit, we copy `length` elements
- This is where amortized analysis pays off!

### Line 225: `requires acc(time_credit(), 1/1)`

**Purpose**: 
- Only need 1 credit from caller (constant!)
- Remaining credits come from the data structure itself

### Lines 260-276: Loop Invariants

```viper
    while (pos < old_len)
        invariant 0 <= pos && pos <= old_len
        invariant old_arr_credits >= old_len - pos
        invariant acc(time_credit(), old_arr_credits/1)
        invariant forall i: Int :: {loc(new_static_arr, i)} 0 <= i && i < pos ==> 
            lookup(new_static_arr, i) == lookup(old_static_arr, i)
```

**Key Invariants**:
- `old_arr_credits >= old_len - pos`: Have enough credits for remaining iterations
- `acc(time_credit(), old_arr_credits/1)`: Actually hold those credits
- Last invariant: Elements 0..pos-1 have been copied correctly

### Lines 278-285: Loop Body

```viper
    {
        consume_time_credit()
        old_arr_credits := old_arr_credits - 1
        update(new_static_arr, pos, lookup(old_static_arr, pos))
        pos := pos + 1
    }
```

**Logic**:
1. Consume one credit from saved credits
2. Decrement our counter
3. Copy element at position pos
4. Move to next position

### Line 289: `new_arr.credits := old_arr_credits`

**Purpose**: Transfer any remaining credits to the new array.

---

## Lines 313-347: append Method

```viper
method append(arr: Ref, val: Int) returns (new_arr: Ref)
    requires acc(dyn_array(arr))
    requires unfolding acc(dyn_array(arr)) in arr.credits >= arr.length
    requires acc(time_credit(), 5/1) // Constant time credits
    ensures acc(dyn_array(new_arr))
    ensures arr_length(new_arr) == old(arr_length(arr)) + 1
{
    consume_time_credit()
    
    var old_len: Int := arr_length(arr)
    var old_cap: Int := arr_capacity(arr)

    if (old_len + 1 >= old_cap) {
        // Need to grow first
        new_arr := grow(arr)
        
        unfold acc(dyn_array(new_arr))
        update(new_arr.array, new_arr.length, val)
        new_arr.length := new_arr.length + 1
        new_arr.credits := new_arr.credits + 3
        fold acc(dyn_array(new_arr))
    } else {
        // Can append directly
        new_arr := arr
        append_nogrow(new_arr, val)
    }   
}
```

### Line 315: `requires unfolding acc(dyn_array(arr)) in arr.credits >= arr.length`

**Purpose**: Need enough saved credits in case we need to grow.

### Line 316: `requires acc(time_credit(), 5/1)`

**Purpose**: 
- Constant 5 credits regardless of array size
- 1 for this method + 4 for append_nogrow, or 1 + 1 for grow + inline work
- This proves **amortized O(1)** append!

### Lines 325-332: Grow Branch

**Logic**:
- Call grow to double capacity
- Manually append (don't call append_nogrow again)
- Save 3 credits for consistency

### Lines 333-336: No-grow Branch

**Logic**:
- Array has room, use append_nogrow directly

---

## Summary: Amortized Analysis

The key insight is **credit accounting**:

| Operation | Credits In | Credits Out | Net |
|-----------|------------|-------------|-----|
| cons | 1 | 0 saved | -1 |
| append_nogrow | 4 | 3 saved | +2 net saved |
| grow | 1 + saved | remaining saved | uses saved |
| append | 5 | 3 saved | amortized O(1) |

When we grow at capacity C with C elements:
- We've done C appends since last grow
- Each saved 3 credits → C×3 credits saved  
- We need C credits to copy → plenty remaining!

This proves append is **amortized O(1)** even though grow is O(n).
