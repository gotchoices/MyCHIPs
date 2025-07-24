# Standard Modules

**Reference Chapter**: Built-in TLA+ modules containing essential operators and functions that form the core language library.

## Naturals Module
Basic arithmetic and comparison for natural numbers (non-negative integers).

**Operators:**
- `+ - * ^ % < > <= >=` - Standard arithmetic and comparison
- `Nat` - The set `{0, 1, 2, ...}` (infinite, membership testing only)
- `a..b` - Range set `{a, a+1, ..., b}`
- `a \div b` - Floor division (e.g., `10 \div 3 = 3`)

## Integers Module
Extends Naturals with negative numbers and full integer support.

**Additional operators:**
- `Int` - Set of all integers (infinite, membership testing only)
- `-a` - Unary negation for negative numbers
- All Naturals operators work with negative integers

## Sequences Module
List-like data structures with 1-indexed access. Essential for algorithms and data manipulation.

**Core operators:**
- `Seq(set)` - Set of all sequences with elements from `set`
- `Len(seq)` - Length of sequence
- `Head(seq)` - First element
- `Tail(seq)` - All elements except first
- `seq1 \o seq2` - Concatenation
- `Append(seq, e)` - Add element to end
- `SubSeq(seq, m, n)` - Subsequence from index m to n (inclusive)
- `SelectSeq(seq, Op(_))` - Filter sequence using predicate

**Critical notes:**
- Sequences use 1-indexed access: `seq[1]` is first element
- Written as `<<a, b, c>>` in TLA+ syntax
- Required for PlusCal procedures

## FiniteSets Module
Utilities for finite set operations and cardinality.

**Operators:**
- `IsFiniteSet(set)` - Tests if set is finite (not infinite like `Nat`)
- `Cardinality(set)` - Number of elements in finite set

**Usage patterns:**
```tla+
Cardinality({1, 2, 3}) = 3
IsFiniteSet(Nat) = FALSE
IsFiniteSet({1, 2, 3}) = TRUE
```

## Bags Module
Multisets - functions mapping elements to positive integer counts.

**Structure:** `[element |-> count, ...]` where counts are positive integers.

**Core operations:**
- `bag1 (+) bag2` - Bag addition (sum counts)
- `bag1 (-) bag2` - Bag subtraction (subtract counts, remove if <= 0)
- `BagCardinality(bag)` - Sum of all counts
- `bag1 \sqsubseteq bag2` - Subbag relation

**Conversion:**
- `BagToSet(bag)` - Get domain (set of elements)
- `SetToBag(set)` - Convert set to bag with count 1
- `EmptyBag` - Empty multiset `<<>>`

**Utility:**
- `BagIn(e, bag)` - Element membership test
- `CopiesIn(e, bag)` - Get count of element (0 if not present)
- `SubBag(bag)` - Set of all subbags

## TLC Module
Model checker utilities and debugging operators. **Use with caution** - breaks referential transparency.

**Essential operators:**
- `Assert(bool, errmsg)` - Terminate with error if condition false
- `Print(val, out)` - Print value and return `out`
- `PrintT(val)` - Print value and return TRUE
- `ToString(val)` - Convert value to string

**Function utilities:**
- `a :> b` - Single-element function `[x \in {a} |-> b]`
- `func1 @@ func2` - Function merge (func1 takes precedence)
- `Permutations(set)` - All permutation functions of set

**Advanced:**
- `RandomElement(set)` - Random element (non-deterministic)
- `SortSeq(seq, Op(_, _))` - Sort sequence with comparator
- `Any` - Universal set (any value is member)

## Specialized Modules

### Json Module
- `ToJson(val)` - Convert TLA+ value to JSON string
- `JsonSerialize(file, val)` / `JsonDeserialize(file)` - File I/O

### Randomization Module
**Warning**: Breaks exhaustive model checking - use for optimization only.
- `RandomSubset(k, S)` - Random k-element subset
- `RandomSetOfSubsets(k, n, S)` - Multiple random subsets

## Usage Patterns

### Module Import
```tla+
EXTENDS Integers, Sequences, FiniteSets, TLC
```

### Common Combinations
- **Basic specs**: `Integers, TLC` (arithmetic + debugging)
- **Algorithm specs**: `+ Sequences` (for data structures)
- **Complex specs**: `+ FiniteSets, Bags` (for advanced data manipulation)

### Performance Notes
- Infinite sets (`Nat`, `Int`, `Seq(S)`) support membership but not enumeration
- `Cardinality` and set operations can be expensive on large finite sets
- TLC operators may impact model checking performance 