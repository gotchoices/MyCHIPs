# Parameterizing Specs

**Core Chapter**: Using constants to make specs configurable per model run, enabling iterative development and comprehensive testing.

## Model Constants
Constants allow dynamic configuration of spec parameters per model run, like command-line flags in programming.

**Declaration:**
```tla+
---- MODULE example ----
EXTENDS Integers, Sequences, TLC
CONSTANT S

(*--algorithm spec
  variable seq \in S \X S \X S \X S;
  // ... rest of spec
```

**Configuration:** In TLC model, assign values like `S <- 1..10` (ordinary assignment).

## Three Types of Constants

### 1. Ordinary Assignments
Standard TLA+ expressions assigned to constants:
```tla+
S <- 1..10
MaxSize <- 100
Workers <- {"w1", "w2", "w3"}
```

### 2. Model Values
Special values that only support equality comparison:
```tla+
NULL <- [model value]
```

**Properties:**
- `X = X` (always true)
- `X # Y` (for different model values)
- `X # 1` (incompatible with other types)
- Useful as sentinel values and placeholders
- Prevents type comparison errors

### 3. Sets of Model Values
Create sets of abstract values:
```tla+
S <- [model value] {s1, s2, s3, s4}
```

**Symmetry sets:** Special optimization making `S` a symmetry set can dramatically reduce state space (often by factor of n!). Treats "symmetric" states as identical:
- `<<s1, s2, s3>>` vs `<<s2, s1, s3>>` are considered equivalent
- Only works with model values (no meaningful operations besides equality)

## Constraining Constants

### ASSUME Statements
Validate constants before model execution:
```tla+
CONSTANT S
ASSUME Cardinality(S) >= 4

CONSTANT NULL, Threads  
ASSUME NULL \notin Threads
ASSUME Threads # {}
```

**Benefits:**
- Prevents nonsense configurations (e.g., empty sets)
- Documents expected constant properties
- Fails fast before expensive model checking

## Development Patterns

### Iterative Development
- **Small constants** for fast feedback during development
- **Large constants** for comprehensive final testing
- Use separate model configurations

### Debug Control
```tla+
CONSTANT DEBUG
ASSUME DEBUG \in BOOLEAN

macro print_if_debug(str) begin
  if DEBUG then
    print str;
  end if;
end macro;

Inputs ==
  IF DEBUG
  THEN {<<1, 2, 3, 4>>}  // Single test case
  ELSE S \X S \X S \X S   // Full state space
```

## Performance Considerations

### Symmetry Set Optimization
- Can reduce states by factorial amounts
- Has overhead - may slow down very large sets
- Only works with model values
- Cannot be used with liveness properties

### Model Value Usage
- Perfect for abstract entities (workers, servers, processes)
- Safer than strings/integers for identifiers
- Enables symmetry optimizations
- Use when only identity matters, not operations

## Common Patterns
- **Type constraints**: `ASSUME S \subseteq SomeType`
- **Size bounds**: `ASSUME Cardinality(S) >= MinSize`
- **Exclusions**: `ASSUME NULL \notin ValidValues`
- **Debug flags**: `ASSUME DEBUG \in BOOLEAN`
- **Multi-model configs**: Small constants for iteration, large for validation

## Critical Rules
- All constants must be assigned values in model configuration
- ASSUME expressions checked before model execution starts
- Symmetry sets require model values (not regular values)
- One `CONSTANT` declaration per constant (or comma-separated list)
- Good practice: Every constant should have an ASSUME constraint 