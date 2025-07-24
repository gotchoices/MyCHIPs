# Operators and Values

**Core Chapter**: Fundamental TLA+ syntax for operators, values, and basic data types.

## Operators
Functions that take arguments and evaluate to expressions. Defined with double equals:
```tla+
MinutesToSeconds(m) == m * 60
SecondsPerMinute == 60  // No arguments - effectively a constant
Abs(x) == IF x < 0 THEN -x ELSE x
```

**Key Rules:**
- Use `==` for operator definition (NOT single `=`)
- No default values, overloading, or optional arguments
- Must always take exact number of parameters defined
- IF-THEN-ELSE expressions must have ELSE branch (expressions always equal something)

## Data Types

### Primitive Types
- **Integers**: Require `EXTENDS Integers` for operators (`+`, `-`, `*`, `\div`, `%`)
- **Strings**: Double quotes only (`"hello"`), no operators except `=` and `#`
- **Booleans**: `TRUE`, `FALSE`
- **Model values**: Abstract identifiers

### Boolean Operators
```tla+
/\  (and)     // looks like "A"
\/  (or)      // the other one  
~   (not)     // flippy thing
=>  (implies) // A => B means "A is at least as true as B"
```

**Bullet-point notation** for complex expressions (whitespace matters):
```tla+
/\ A
/\ \/ B
   \/ C
/\ D
```

### Sequences (1-indexed!)
```tla+
<<a, b, c>>           // sequence literal
seq[1]                // first element  
Len(seq)              // length
Head(seq), Tail(seq)  // first element, rest
Append(seq, elem)     // add to end
seq1 \o seq2          // concatenation
```

### Sets
```tla+
{1, 2, 3}             // set literal
x \in set             // membership
set1 \subseteq set2   // subset
set1 \union set2      // union
set1 \intersect set2  // intersection  
set1 \ set2           // difference
Cardinality(set)      // size (needs EXTENDS FiniteSets)
```

**Set construction:**
```tla+
BOOLEAN              // {TRUE, FALSE}
1..5                 // {1, 2, 3, 4, 5}
S1 \X S2            // Cartesian product
SUBSET S            // All subsets (careful - exponential!)
{x*x: x \in 1..4}   // Map: {1, 4, 9, 16}
{x \in 1..4: x % 2 = 0}  // Filter: {2, 4}
```

### CHOOSE Operator
Deterministic selection from sets:
```tla+
CHOOSE x \in set: P(x)  // Picks element satisfying P
// Error if no element satisfies P
// Always same result if multiple satisfy P
```

## LET Expressions
Local operator definitions for complex expressions:
```tla+
ToClock(seconds) ==
  LET seconds_per_day == 86400
      Max(x, y) == IF x > y THEN x ELSE y
  IN CHOOSE x \in ClockType: ToSeconds(x) = seconds % seconds_per_day
```

## Common Patterns
- **Empty tests**: `set = {}`, `seq = <<>>`
- **Type definitions**: `ClockType == (0..23) \X (0..59) \X (0..59)`
- **Range of sequence**: `Range(seq) == {seq[i]: i \in 1..Len(seq)}`
- **Multiple modules**: `EXTENDS Integers, Sequences` (one line only)

## Critical Gotchas
- Sequences are 1-indexed
- Use `==` for operators, `=` for equality tests  
- One `EXTENDS` line per spec (comma-separated modules)
- `CHOOSE` errors if no element satisfies predicate
- Sets cannot mix types: `{1, "a"}` is invalid 