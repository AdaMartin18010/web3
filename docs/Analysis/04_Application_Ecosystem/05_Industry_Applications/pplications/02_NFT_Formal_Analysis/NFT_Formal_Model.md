# Non-Fungible Tokens Formal Model

## 1. Mathematical Foundations

### 1.1 Definitions

**Definition 1.1.1** (Non-Fungible Token) A non-fungible token (NFT) system is a tuple $(G, M, O, T)$ where:

1. $G$ is a set of globally unique identifiers.
2. $M$ is a set of metadata associated with each token.
3. $O$ is a set of ownership records.
4. $T$ is a set of transfer functions.

**Definition 1.1.2** (Digital Asset) A digital asset in an NFT context is defined as a tuple $(g, m, o)$ where:

- $g \in G$ is a unique identifier
- $m \in M$ is the associated metadata
- $o \in O$ is the current owner

**Definition 1.1.3** (Ownership Relation) An ownership relation $R \subseteq O \times G$ represents the mapping between owners and token identifiers, with the constraint that for any $g \in G$, there exists at most one $o \in O$ such that $(o, g) \in R$.

### 1.2 Formal Properties

**Property 1.2.1** (Uniqueness) For all $g_1, g_2 \in G$, if $g_1 \neq g_2$, then the corresponding assets $(g_1, m_1, o_1) \neq (g_2, m_2, o_2)$.

**Property 1.2.2** (Non-Fungibility) For any two distinct digital assets $(g_1, m_1, o_1)$ and $(g_2, m_2, o_2)$, there does not exist a substitution function $f$ such that $f(g_1, m_1, o_1) = (g_2, m_2, o_2)$.

**Property 1.2.3** (Provenance) For any token $g \in G$, there exists a sequence of ownership transfers $(o_1, o_2, \ldots, o_n)$ such that $o_1$ is the minter and $o_n$ is the current owner.

## 2. Token Standard Formal Model

### 2.1 ERC-721 Formalization

**Definition 2.1.1** (ERC-721 Contract) An ERC-721 contract is defined as a tuple $(T, B, A, M, E)$ where:

1. $T$ is a set of token IDs.
2. $B : T \rightarrow A$ is a balancing function mapping tokens to owners.
3. $A$ is a set of addresses (owners).
4. $M : T \rightarrow \{0,1\}^*$ is a metadata function mapping tokens to their metadata.
5. $E$ is a set of events triggered by contract operations.

**Theorem 2.1.2** (ERC-721 Ownership Invariant) For any valid ERC-721 contract, at any point in time, for every token ID $t \in T$, there exists at most one address $a \in A$ such that $B(t) = a$.

*Proof:* By the definition of the `transferFrom` function, whenever a token changes ownership, the previous owner's balance for that token is decremented before the new owner's balance is incremented, ensuring the invariant holds.

### 2.2 ERC-1155 Formalization

**Definition 2.2.1** (ERC-1155 Contract) An ERC-1155 contract is defined as a tuple $(T, F, NF, B, A, E)$ where:

1. $T$ is a set of token IDs.
2. $F \subset T$ is the subset of fungible token IDs.
3. $NF \subset T$ is the subset of non-fungible token IDs, with $F \cap NF = \emptyset$ and $F \cup NF = T$.
4. $B : A \times T \rightarrow \mathbb{N}$ is a balance function mapping (address, token ID) pairs to balances.
5. $A$ is a set of addresses (owners).
6. $E$ is a set of events triggered by contract operations.

**Theorem 2.2.2** (ERC-1155 Batch Transfer Conservation) For any batch transfer of tokens from address $a_1$ to address $a_2$, the sum of tokens before and after transfer remains constant.

*Proof:* For each token ID $t_i$ and amount $v_i$ in a batch transfer, the operation ensures that $B'(a_1, t_i) = B(a_1, t_i) - v_i$ and $B'(a_2, t_i) = B(a_2, t_i) + v_i$, where $B'$ is the balance function after transfer. Therefore, $\sum_{a \in A}\sum_{t \in T} B(a, t) = \sum_{a \in A}\sum_{t \in T} B'(a, t)$.

## 3. Smart Contract Implementation

### 3.1 Formal Verification

**Theorem 3.1.1** (Safety of NFT Transfer) For a correctly implemented ERC-721 contract, the transfer operation satisfies the following properties:

1. Only the owner or approved operator can transfer a token.
2. After a successful transfer, the receiver becomes the new owner.
3. The sender is no longer the owner after transfer.

*Proof sketch:* The transfer function contains preconditions that verify the sender is either the owner or approved to transfer. The function then updates the ownership mapping, ensuring the properties hold.

### 3.2 Implementation in Solidity

```solidity
// Formal model implementation of ERC-721
contract ERC721FormalModel {
    // Ownership mapping: token ID => owner address
    mapping(uint256 => address) private _owners;
    
    // Approval mapping: token ID => approved address
    mapping(uint256 => address) private _tokenApprovals;
    
    // Operator approval: owner => operator => approved
    mapping(address => mapping(address => bool)) private _operatorApprovals;
    
    // Transfer function with formal properties
    function transferFrom(address from, address to, uint256 tokenId) public {
        // Preconditions
        require(_isApprovedOrOwner(msg.sender, tokenId), "Not authorized");
        require(ownerOf(tokenId) == from, "From address is not owner");
        require(to != address(0), "Transfer to zero address");
        
        // Clear approvals
        _approve(address(0), tokenId);
        
        // Update ownership - ensures Safety Property 2 and 3
        _owners[tokenId] = to;
        
        // Emit event for provenance tracking
        emit Transfer(from, to, tokenId);
    }
    
    // Helper function that implements authorization check - Safety Property 1
    function _isApprovedOrOwner(address operator, uint256 tokenId) internal view returns (bool) {
        address owner = ownerOf(tokenId);
        return (operator == owner || 
                isApprovedForAll(owner, operator) || 
                getApproved(tokenId) == operator);
    }
    
    // Other required functions omitted for brevity
}
```

## 4. NFT Marketplace Formal Model

### 4.1 Definitions

**Definition 4.1.1** (NFT Marketplace) An NFT marketplace is a tuple $(L, B, S, A, F)$ where:

1. $L$ is a set of listing records, each containing a token ID, seller, price, and status.
2. $B$ is a set of bid records, each containing a token ID, bidder, bid amount, and status.
3. $S$ is a set of sale records, each containing a token ID, seller, buyer, price, and timestamp.
4. $A$ is a set of asset provenance records.
5. $F$ is a set of fee calculation functions.

**Definition 4.1.2** (Marketplace Equilibrium) A marketplace is in equilibrium when for every active listing $l \in L$ with price $p$, either:

1. There is no bid $b \in B$ with amount greater than $p$, or
2. The highest bid $b_{max} \in B$ has just been accepted, creating a new sale record $s \in S$.

### 4.2 Economic Model

**Theorem 4.2.1** (NFT Price Discovery) In an efficient NFT marketplace with perfect information, the price of an NFT converges to its perceived value among the set of potential buyers.

*Proof sketch:* For any NFT with true perceived value $v$ among buyers, sellers with reservation prices below $v$ will sell, and buyers with valuations above the asking price will buy, leading to price convergence.

**Theorem 4.2.2** (Royalty Distribution) For an NFT with royalty rate $r$, the creator receives $r \cdot p$ for each secondary sale at price $p$.

## 5. Advanced NFT Systems

### 5.1 Fractionalized NFTs

**Definition 5.1.1** (Fractionalized NFT) A fractionalized NFT system is a tuple $(N, F, O, S, G)$ where:

1. $N$ is an NFT with unique identifier $g \in G$.
2. $F$ is a set of fungible tokens representing fractions of ownership.
3. $O : F \rightarrow \mathcal{P}(A)$ is an ownership function mapping fractions to sets of addresses.
4. $S : F \rightarrow [0, 1]$ is a share function mapping fractions to proportions such that $\sum_{f \in F} S(f) = 1$.
5. $G$ is a governance mechanism for collective decisions.

**Theorem 5.1.2** (Fractionalized NFT Value Conservation) The sum of the market values of all fractions equals the market value of the underlying NFT in a perfect market.

*Proof sketch:* In the absence of market inefficiencies and with perfect information, arbitrage opportunities would exist if the sum of fraction values diverged from the whole NFT value, driving them back to equality.

### 5.2 Dynamic NFTs

**Definition 5.2.1** (Dynamic NFT) A dynamic NFT is a tuple $(g, m(t), s(t), r)$ where:

1. $g \in G$ is a unique identifier.
2. $m(t)$ is a time-dependent metadata function.
3. $s(t)$ is a state transition function.
4. $r$ is a set of rules governing state transitions.

**Theorem 5.2.2** (Dynamic NFT State Transition Safety) For any dynamic NFT, all state transitions preserving the rules $r$ maintain the uniqueness property of the NFT.

*Proof sketch:* Since the unique identifier $g$ remains constant across state transitions, and state transitions only modify metadata according to rules $r$, the uniqueness property is preserved.

## 6. Applications in Web3

### 6.1 Digital Collectibles

**Theorem 6.1.1** (Collection Value) For a collection of related NFTs $\{a_1, a_2, \ldots, a_n\}$, the market value of the complete collection is often greater than the sum of individual values, expressed as $V(\{a_1, a_2, \ldots, a_n\}) \geq \sum_{i=1}^{n} V(a_i)$.

*Proof sketch:* Collectors value completeness, creating additional utility for complete sets beyond the sum of individual items.

### 6.2 NFT-Based Access Control

**Definition 6.2.1** (Access Control System) An NFT-based access control system is a tuple $(T, A, P, R)$ where:

1. $T$ is a set of token IDs representing access rights.
2. $A$ is a set of addresses (users).
3. $P$ is a set of permissions.
4. $R : T \rightarrow \mathcal{P}(P)$ is a function mapping tokens to sets of permissions.

**Theorem 6.2.2** (Access Control Correctness) A user with address $a$ has permission $p$ if and only if they own a token $t$ such that $p \in R(t)$.

*Proof:* By the definition of the access control system, a permission check evaluates ownership of tokens mapped to the required permission, ensuring the correctness property.

### 6.3 Formal Model for NFT Gaming

**Definition 6.3.1** (NFT Game System) An NFT game system is a tuple $(G, P, A, S, I)$ where:

1. $G$ is a set of game assets represented as NFTs.
2. $P$ is a set of players (addresses).
3. $A : G \times P \rightarrow \mathbb{R}$ is an attribute function mapping (asset, player) pairs to attribute values.
4. $S$ is the game state.
5. $I$ is a set of interactions between assets and the game state.

**Theorem 6.3.2** (NFT Game Asset Persistence) Game assets represented as NFTs persist beyond the lifecycle of any specific game instance.

*Proof:* Since NFTs exist on the blockchain independently of the game logic, their existence is not bound to the game's operational status.

## 7. Future Research Directions

The formal modeling of NFTs in Web3 provides a rigorous foundation for developing applications and standards. Future research should focus on:

1. Developing formal verification tools specific to NFT contracts
2. Creating mathematical models for NFT composability
3. Formalizing cross-chain NFT interoperability
4. Developing privacy-preserving NFT models
5. Extending formal models to account for social and cultural value factors
