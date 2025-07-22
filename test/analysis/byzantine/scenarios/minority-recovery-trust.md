# Minority Recovery: Trust Requirements Analysis

## Trust Problem

### Original Assumption (Flawed)
```mermaid
graph LR
    subgraph "Assumed Settlement"
        A[Node A] -->|"New Tally"| B[Node B]
        B -->|"New Tally"| C[Node C]
        C -->|"New Tally"| A
    end
    
    style A fill:#ffd,stroke:#666
    style C fill:#ffd,stroke:#666
```

**Issues**:
- Requires new trust relationships
- No basis for A-C trust
- Forces unnatural connections
- Increases risk exposure

### Actual Trust Network
```mermaid
graph LR
    subgraph "Real Relationships"
        A[Node A] -->|"Existing Trust"| B[Node B]
        B -->|"Existing Trust"| C[Node C]
        
        A -->|"No Trust"| C
    end
    
    style A fill:#ffd,stroke:#666
    style C fill:#ffd,stroke:#666
```

## Alternative Solutions

### 1. Chain-Based Settlement
```mermaid
graph TD
    subgraph "Before"
        A1[A] -->|"Promise"| B1[B]
        B1 -->|"Promise"| C1[C]
    end
    
    subgraph "After"
        A2[A] -->|"Adjusted Tally"| B2[B]
        B2 -->|"Adjusted Tally"| C2[C]
    end
```

**Process**:
1. Keep existing trust lines
2. Adjust balances sequentially
3. B acts as intermediary
4. Preserve original claims

**Advantages**:
- Uses existing relationships
- No new trust required
- Clear responsibility chain
- Natural settlement path

**Disadvantages**:
- More risk for B
- Complex accounting
- Requires B's cooperation
- May need incentives

### 2. Independent Resolution
```mermaid
graph TD
    subgraph "Separate Settlements"
        A1[A] -->|"Resolve"| B1[B]
        B2[B] -->|"Resolve"| C1[C]
    end
    
    subgraph "Claims Preserved"
        A2[A] -->|"Claim"| M[Majority]
        C2[C] -->|"Claim"| M
    end
```

**Process**:
1. Each pair settles independently
2. Keep original claims separate
3. No cross-node obligations
4. Individual timeout handling

**Advantages**:
- No new trust needed
- Simple bilateral resolution
- Clear responsibilities
- Independent decisions

**Disadvantages**:
- Less efficient
- Might be unbalanced
- Harder to coordinate
- Potential inequities

### 3. Mediated Settlement
```mermaid
graph TD
    subgraph "Mediation Structure"
        A[A] -->|"1. Propose"| M[Mediator]
        B[B] -->|"2. Verify"| M
        C[C] -->|"3. Agree"| M
        M -->|"4. Terms"| All
    end
    
    subgraph "Resolution"
        A1[A] -->|"Original Tally"| B1[B]
        B1 -->|"Original Tally"| C1[C]
    end
```

**Process**:
1. Use trusted third party
2. Keep existing tallies
3. Adjust terms bilaterally
4. Document resolution

**Advantages**:
- No new trust lines
- Professional oversight
- Clear process
- Legal framework

**Disadvantages**:
- External dependency
- Additional cost
- More complex
- Slower resolution

## Recommended Approach: Hybrid Resolution

### Process Flow
```mermaid
sequenceDiagram
    participant A as Node A
    participant B as Node B
    participant C as Node C
    
    Note over A,C: Phase 1: Documentation
    A->>B: Document state
    B->>C: Document state
    
    Note over A,C: Phase 2: Individual Resolution
    A->>B: Propose adjustment
    B->>C: Propose adjustment
    
    Note over A,C: Phase 3: Coordination
    B->>A: Confirm terms
    B->>C: Confirm terms
    
    Note over A,C: Phase 4: Settlement
    A->>B: Execute settlement
    B->>C: Execute settlement
```

### Implementation

1. **Documentation Phase**:
   ```json
   {
     "stuck_lift": {
       "id": "lift_uuid",
       "original_promises": ["details"],
       "timeout_evidence": ["logs"]
     },
     "bilateral_settlements": [
       {
         "nodes": ["A", "B"],
         "adjustment": "amount",
         "terms": ["details"]
       },
       {
         "nodes": ["B", "C"],
         "adjustment": "amount",
         "terms": ["details"]
       }
     ],
     "preserved_claims": {
       "against_majority": ["claim_details"],
       "recovery_rights": ["terms"]
     }
   }
   ```

2. **Resolution Steps**:
   - Keep existing tally relationships
   - Adjust bilateral balances fairly
   - Document all decisions
   - Preserve external claims

3. **Risk Management**:
   - No new trust requirements
   - Limited exposure changes
   - Clear responsibility chain
   - Documented process

### Legal Framework

1. **Settlement Agreement**:
   - Uses existing contracts
   - Documents timeout/default
   - Preserves claims
   - Bilateral adjustments

2. **Claim Preservation**:
   - Individual rights maintained
   - Coordinated documentation
   - Future recovery path
   - Legal standing preserved

## Conclusions

### Key Principles
1. **Trust Preservation**:
   - No new trust relationships required
   - Use existing tally structure
   - Respect trust boundaries
   - Maintain natural relationships

2. **Fair Resolution**:
   - Bilateral settlements
   - Proportional adjustments
   - Coordinated timing
   - Preserved rights

3. **Practical Implementation**:
   - Simple process
   - Clear documentation
   - Manageable risk
   - Natural recovery

The revised approach acknowledges and respects existing trust relationships while providing a practical path to resource recovery. It's more limited than the original proposal but more realistic and implementable. 