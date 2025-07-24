# MyCHIPs Formal Verification

## Purpose

This folder contains formal specifications and verification models for MyCHIPs protocol components, with particular focus on validating Byzantine fault tolerance and security properties of the ChipNet consensus protocol.

**Primary Goals**:
- Validate security assertions made in the broader [Byzantine analysis](../README.md)
- Verify correctness of critical protocol components (lifts, consensus, recovery)
- Quantify Byzantine fault tolerance with mathematical precision
- Provide formal specifications for implementation guidance

## Command-Line Setup

This folder is designed for **command-line TLA+ usage** rather than the TLA+ IDE.

### 1. Install TLA+ Tools
```bash
# Download latest tla2tools.jar
wget https://github.com/tlaplus/tlaplus/releases/latest/download/tla2tools.jar

# Place in your preferred location (e.g., ~/bin/)
mkdir -p ~/bin
mv tla2tools.jar ~/bin/
```

### 2. Install Wrapper Scripts
```bash
# Copy the wrapper scripts to your PATH
cp bin/tlc ~/bin/
cp bin/sany ~/bin/
chmod +x ~/bin/tlc ~/bin/sany

# Or add this bin/ directory to your PATH
export PATH="$PATH:$(pwd)/bin"
```

### 3. Verify Installation
```bash
sany learn/DieHard/DieHard.tla    # Parse a simple model
tlc learn/DieHard/DieHard.tla     # Run model checker
```

## Folder Structure

```
modeling/
├── README.md           # This file - project overview
├── STATUS.md           # Progress tracking checklist
├── HISTORY.md          # Historical context from DSR/BYU analyses
├── bin/                # Command-line TLA+ tool wrappers
│   ├── tlc             # TLC model checker wrapper
│   └── sany            # SANY parser wrapper
├── learn/              # Simple TLA+ learning examples
│   ├── DieHard/        # Water jug puzzle (basic TLA+ syntax)
│   └── TCommit/        # Two-phase commit (distributed systems)
├── ChipNetBasic/       # Advanced integrated model (currently has syntax errors)
│   ├── ChipNetBasic.tla
│   ├── ChipNetBasic.cfg
│   └── ChipNetBasic.md
└── [future: organized models by complexity]
```

## Quick Start

### For Learning TLA+
```bash
cd learn/DieHard/
sany DieHard.tla        # Check syntax
tlc DieHard.tla         # Run model checker
```

### For MyCHIPs Development
1. **Check current progress**: Review `STATUS.md` 
2. **Read historical context**: See `HISTORY.md` for DSR/BYU background
3. **Start with simple models**: Work through the checklist in `STATUS.md`
4. **Build toward ChipNetBasic**: Eventually fix and complete the comprehensive model

## Key Concepts

- **ChipNet Protocol**: Flexible consensus mechanisms for credit clearing
- **Byzantine Fault Tolerance**: Handling malicious participants
- **Circuit Starvation Attack**: Specific attack requiring insurance chit recovery
- **Insurance Chits**: Minority recovery mechanism for abandoned promises

## Contributing

This is **not a TLA+ tutorial** - contributors should learn TLA+ independently. The `learn/` folder provides simple examples, but the assumption is that users will figure out TLA+ on their own.

Focus areas:
1. Work through the `STATUS.md` checklist systematically
2. Build simple models before attempting complex ones
3. Validate against historical DSR/BYU findings
4. Eventually fix and complete `ChipNetBasic.tla`

See `HISTORY.md` for detailed background on protocol evolution and prior formal verification efforts. 