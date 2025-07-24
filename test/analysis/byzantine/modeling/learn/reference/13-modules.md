# Modules

**Core Chapter**: Code organization through imports and modular design - less critical than other features but useful for larger specifications and reusable libraries.

## When to Use Modules
Most TLA+ specs are under 300 lines and work fine in single files. Use modules for:
- Creating abstract libraries (e.g., `LinkedLists`)
- Separating invariants into dedicated files
- Building reusable components

## EXTENDS - Simple Imports
Dumps everything from the imported module into current namespace:
```tla+
EXTENDS Sequences, Integers
\* Now can use Append, Head, +, -, etc. directly
```

**LOCAL exclusion**: `LOCAL Op == "definition"` prevents import during EXTENDS.

**Requirements**: All EXTENDS must be on same line, at module start.

## INSTANCE - Advanced Imports
More flexible than EXTENDS with additional capabilities:

### Basic Usage
```tla+
INSTANCE Sequences  \* Same as EXTENDS
LOCAL INSTANCE Naturals  \* Available but not transitive
```

### Namespacing
Prevents namespace pollution:
```tla+
Foo == INSTANCE Sequences
\* Use with: Foo!Append(seq, 1) instead of Append(seq, 1)
```

Can import same module multiple times:
```tla+
Foo == INSTANCE Sequences
Bar == INSTANCE Sequences
```

### Parameterized Modules
Pass constants to modules during instantiation:
```tla+
---- MODULE Point ----
CONSTANTS X, Y
Repr == <<X, Y>>
Add(x, y) == <<X + x, Y + y>>
====

\* Usage:
Origin == INSTANCE Point WITH X <- 0, Y <- 0
\* Now Origin!Add(1, 2) == <<1, 2>>
```

**Auto-import**: Constants with same name import automatically (can override with WITH).

### Partial Parameterization
Defer some constants to call-time:
```tla+
XAxis(X) == INSTANCE Point WITH Y <- 0
\* Use: XAxis(2)!Add(1, 3) == <<3, 3>>
```

## Key Differences: EXTENDS vs INSTANCE

| Feature | EXTENDS | INSTANCE |
|---------|---------|----------|
| Multiple imports | Single line only | Multiple lines OK |
| Namespace control | Dumps all | Can namespace with ! |
| Parameterization | None | Full WITH support |
| Local importing | No | Yes (LOCAL INSTANCE) |
| Use case | Simple imports | Complex/reusable modules |

## Practical Patterns
- **Libraries**: Use INSTANCE with namespacing
- **Standard modules**: Use EXTENDS for simplicity  
- **Reusable components**: Parameterized INSTANCE
- **Private imports**: LOCAL INSTANCE to prevent transitive exposure 