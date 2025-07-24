# More Operators

**Core Chapter**: Advanced operator features - recursion, higher-order operators, and syntactic conveniences for complex data manipulation.

## Recursive Operators
Enable operations like summing sequences that were previously impossible with basic TLA+ constructs.

**Declaration Required:**
```tla+
RECURSIVE SumSeq(_)  // Specify arity in advance

SumSeq(s) == IF s = <<>> THEN 0 ELSE
  Head(s) + SumSeq(Tail(s))
```

**Local Recursion:**
```tla+
SumSeq(s) == LET
  RECURSIVE Helper(_)
  Helper(s_) == IF s_ = <<>> THEN 0 ELSE
    Head(s_) + Helper(Tail(s_))
IN Helper(s)
```

**Critical Limitation:** No syntactic check for termination - infinite recursion causes stack overflow.

### Set Recursion and Determinism
```tla+
RECURSIVE SetSum(_)
SetSum(set) == IF set = {} THEN 0 ELSE
  LET x == CHOOSE x \in set: TRUE
  IN x + SetSum(set \ {x})
```

**Warning:** `CHOOSE x \in set: TRUE` is non-deterministic but TLC picks lowest value. For deterministic behavior, use explicit selection:
```tla+
LET x == CHOOSE x \in set: \A y \in set: x <= y  // Explicitly choose minimum
```

## Higher-Order Operators
Operators that take other operators as parameters, enabling functional programming patterns.

**Basic Syntax:**
```tla+
SeqMap(Op(_), seq) == [i \in DOMAIN seq |-> Op(seq[i])]

// Usage with named operator
Double(x) == x * 2
SeqMap(Double, <<1, 2, 3>>)  // <<2, 4, 6>>
```

**Anonymous Functions with LAMBDA:**
```tla+
SeqMap(LAMBDA x: x + 1, <<1, 2, 3>>)  // <<2, 3, 4>>
```

**Critical Limitation:** Cannot combine recursive and higher-order operators.

## Binary Operators
Custom infix operators for frequently used operations.

**Definition Pattern:**
```tla+
s \o t == [i \in 1..(Len(s) + Len(t)) |-> 
  IF i \leq Len(s) THEN s[i] ELSE t[i-Len(s)]]

// Custom examples
set ++ x == set \union {x}  // Add element
set -- x == set \ {x}       // Remove element
```

**Note:** Fixed set of allowed binary operator symbols. Use sparingly as they can make specs confusing.

## Function Operators
Syntactic sugar for top-level function definitions.

**Standard vs Function Operator Syntax:**
```tla+
// Standard function definition
Double == [x \in 1..10 |-> x * 2]

// Function operator syntax (equivalent)
Double[x \in 1..10] == x * 2
```

**Primary Use - Recursive Functions:**
```tla+
Factorial[x \in 0..10] == IF x = 0 THEN 1 ELSE x * Factorial[x - 1]
```

## CASE Statements
Multi-way conditionals for complex branching logic.

```tla+
Fizzbuzz(x) ==
  CASE (x % 3 = 0) /\ (x % 5 = 0) -> "Fizzbuzz"
    [] (x % 3 = 0)                -> "Fizz"
    [] (x % 5 = 0)                -> "Buzz"
    [] OTHER                      -> x
```

**Behavior:**
- No match + no `OTHER` → TLC error
- Multiple matches → TLC picks first match (implementation-defined)
- `[]` separates cases

## Practical Applications
- **Sequence/Set Operations**: Sum, map, filter, reduce operations
- **Recursive Data Structures**: Tree traversal, graph algorithms
- **Functional Programming**: Higher-order transformations
- **Complex Logic**: Multi-condition branching with CASE

## Key Limitations
- Recursive operators require pre-declaration with arity
- No termination checking (runtime stack overflow possible)
- Cannot mix recursion with higher-order operators
- Binary operators limited to predefined symbols
- CHOOSE in set recursion can be non-deterministic

## Best Practices
- Use explicit selection predicates with CHOOSE for deterministic recursion
- Prefer named operators over LAMBDA for reusability
- Use binary operators sparingly to maintain readability
- Test recursive operators with small inputs first 