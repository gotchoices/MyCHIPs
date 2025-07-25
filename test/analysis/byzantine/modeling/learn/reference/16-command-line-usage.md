# Command-Line Usage

**Reference Chapter**: Essential CLI information for TLA+ toolchain usage outside the Toolbox IDE.

## Core Tools

**Main file**: `tla2tools.jar` - Contains all TLA+ command-line tools

**Four subtools**:
- **TLC**: Model checker
- **pcal.trans**: PlusCal translator  
- **SANY**: Parser/syntax checker
- **Tla2Tex**: LaTeX PDF generator

## PlusCal Translation

```bash
java -cp tla2tools.jar pcal.trans file.tla
```

**Actions**:
1. Translates PlusCal in `file.tla` to TLA+
2. Creates `file.old` as backup
3. Generates `file.cfg` config file (overwrites existing)

**Prevent config overwrite**: Add `-nocfg` flag
**No way to prevent**: `file.old` backup creation

## TLC Model Checking

```bash
java -jar tla2tools.jar -config configfile.cfg specfile.tla
```

**Default behavior**: If `-config` omitted, looks for `specfile.cfg`

## Config File Format

**Complete DSL** for command-line TLC configuration:

### Required Specification
```
SPECIFICATION Spec
```
**Note**: Must use `SPECIFICATION`, not separate `INIT/NEXT`

### Constants
```
CONSTANT
  Const1 = {"a", "b", "c"}        // Ordinary assignment
  Const2 = Const2                 // Model value (same name)  
  Const3 = {c1, c2, c3}          // Set of model values (identifiers, not strings)
```

**Limitations**:
- No functions or expressions as values
- No negative numbers (technically requires Integers import)
- No imports available in config files

### Properties and Invariants
```
INVARIANT Inv1, Inv2              // Multiple allowed, comma-separated
PROPERTY Prop1                    // Temporal properties
```

**Restriction**: Must be **named operators**, not expressions (unlike Toolbox)

### Optional Features
```
CONSTRAINT SomeConstraint         // State constraint
ACTION-CONSTRAINT ActionConstraint // Action constraint  
VIEW ViewOperator                 // State view for symmetry
CHECK_DEADLOCK FALSE              // Disable deadlock checking
ALIAS AliasOperator               // Custom error trace output
```

## Key TLC Options

### Performance
```bash
-workers auto                     // Use all CPU cores (default: single thread!)
-fpmem 0.5                       // Use 50% of system memory (default: 25%)
-metadir /tmp/states             // Store state space in specific directory
```

### Debugging
```bash
-continue                        // Continue after violations (show all errors)
-dump states.txt                 // Write all reached states to file
-dump dot graph.dot              // Output Graphviz graph of state space
-dump dot,colorize,actionlabels graph.dot  // Enhanced graph with colors/labels
```

### Error Handling
```bash
-noGenerateSpecTE                // Don't write error files on property violations
```

## ALIAS Feature

**Custom error trace output**:
```tla+
Alias == 
  [x |-> x,
   nextx |-> x',
   computed |-> x + 1]
```

**Config**: `ALIAS Alias`

**Effect**: Error traces show only aliased values, replacing standard output

## Example Complete Config

```
SPECIFICATION Spec

CONSTANT
  RM = {rm1, rm2, rm3}
  MaxSize = 10
  Workers = {w1, w2}

INVARIANT TypeInvariant, SafetyProperty
PROPERTY LivenessProperty

CONSTRAINT StateBound
CHECK_DEADLOCK FALSE
```

## Best Practices

1. **Always use** `-workers auto` for performance
2. **Use** `SPECIFICATION` format (not `INIT/NEXT`)
3. **Test with small constants** first, then scale up
4. **Use** `-metadir` for scripted runs to simplify cleanup
5. **Add** `ALIAS` for readable error traces in complex models 