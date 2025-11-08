# Substrate Theory

> This repository contains the canonical specification, the verbatim Lean 4 formalization, and the verified Ethereum on-chain record of *Substrate Theory – Canonical Edition*.

---

## Abstract

We present a complete formal system establishing quantum mechanics and general relativity
as computational regimes of a single substrate governed by algorithmic complexity thresholds.
The theory is grounded in Kolmogorov complexity, formalized in Lean 4 across 21 modules total-
ing 5 300 + lines, and demonstrates convergence between ideal (noncomputable) and operational (computable)
layers through eight bridge theorems. A critical complexity threshold at 50 bits determines the quantum-classical transition,
with gravity and quantum collapse emerging as the same mechanism. The formalization establishes universal grounding through a rank system and
proposes information-theoretic interpretations of fundamental physical constants.

---

## Build & Verify (Lean 4)

1. **Install Lean toolchain (elan):**
```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
# restart your shell then:
lean --version
lake --version
````

2. **Build the project**

```bash
lake update
lake build
```

If the formalization declares external dependencies, they will be fetched by `lake update`.

---

## On-Chain Canonical Record (Ethereum Mainnet)

### Smart Contracts

| Contract                                                                                         | Type                 | Address                                      | Verified | Description                                                            |
| ------------------------------------------------------------------------------------------------ | -------------------- | -------------------------------------------- | -------- | ---------------------------------------------------------------------- |
| [`OnchainText`](https://etherscan.io/address/0x31218c4d139e373c185732655658315f1892e1ae#code)    | Immutable data store | `0x31218c4d139e373c185732655658315f1892e1ae` | ✅ Yes    | Contains the canonical *Substrate Theory* text, encoded as UTF-8 bytes |
| [`OnchainTextNFT`](https://etherscan.io/address/0xb58fe65017941F8fb8eE173Bc7a9160dA136151F#code) | ERC-721 NFT wrapper  | `0xb58fe65017941F8fb8eE173Bc7a9160dA136151F` | ✅ Yes    | Mints and manages NFTs that reference the canonical text               |

---

### NFT Details

| Field                | Value                                                                                                                                                              |
| -------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| **Collection Name**  | SUBSTRATE THEORY CANONICAL (Updated)                                                                                                                               |
| **Token ID**         | #1                                                                                                                                                                 |
| **Owner**            | [`0x367E6B384b6Ec96Ccec478F7B314d3deB2F01195`](https://etherscan.io/address/0x367E6B384b6Ec96Ccec478F7B314d3deB2F01195)                                            |
| **Minted From**      | [`0x7c8a138f581A0a87C1BF63BF697A9BC729ac2dE1`](https://etherscan.io/address/0x7c8a138f581A0a87C1BF63BF697A9BC729ac2dE1)                                            |
| **Transaction Hash** | [`0x8640dfaab67c13e031d794f35c3a678b74d2ec19ae9014f6bdca43879c33421c`](https://etherscan.io/tx/0x8640dfaab67c13e031d794f35c3a678b74d2ec19ae9014f6bdca43879c33421c) |
| **Timestamp**        | Nov-08-2025, 11:30 UTC                                                                                                                                             |
| **Gas Fee**          | 0.000006637 ETH ($0.02)                                                                                                                                            |
| **Function Called**  | `mint(address _to)`                                                                                                                                                |

---

### Canonical Content Verification

| Field                             | Value                                                                |
| --------------------------------- | -------------------------------------------------------------------- |
| **Canonical Text (UTF-8)**        | `SUBSTRATE_THEORY_CANONICAL_REFERENCE.txt`                           |
| **Size**                          | 11 290 bytes                                                         |
| **Keccak-256 (text)**             | `0x552901c27d17488e6edea08f34db085f2959bcc8eb3f7f0c8869560c4f89ec09` |
| **Keccak-256 (runtime bytecode)** | `0x7dd220053f5ec52419e2a2de159f7b32946f3d41a342dbf77e15c5ca65d8a0a2` |

#### Verify the on-chain text locally

```bash
# 1. Retrieve and decode the bytecode
cast code 0x31218c4d139e373c185732655658315f1892e1ae --rpc-url https://ethereum.publicnode.com > code.hex
sed 's/^0x//' code.hex | xxd -r -p > substrate.txt

# 2. Confirm hash match
xxd -p -c 999999 substrate.txt | cast keccak
# → 0x552901c27d17488e6edea08f34db085f2959bcc8eb3f7f0c8869560c4f89ec09
```

---

### Key Transactions

| Action                  | Tx Hash                                                                                                                                                            | Block                | Notes                     |
| ----------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------ | -------------------- | ------------------------- |
| Deploy `OnchainText`    | [`0xaf60585cb51e4eb289a0babf1fc3c66a17e3244ed26874fbfe505f8b433e916f`](https://etherscan.io/tx/0xaf60585cb51e4eb289a0babf1fc3c66a17e3244ed26874fbfe505f8b433e916f) | Mainnet (Nov 7 2025) | Canonical content storage |
| Deploy `OnchainTextNFT` | [`0xe820a42226839735519c3eb12d46ae8d73d06c203c13b6caf38c065d6e2bc7b0`](https://etherscan.io/tx/0xe820a42226839735519c3eb12d46ae8d73d06c203c13b6caf38c065d6e2bc7b0) | Mainnet (Nov 7 2025) | ERC-721 wrapper           |
| Mint Token #1           | [`0x8640dfaab67c13e031d794f35c3a678b74d2ec19ae9014f6bdca43879c33421c`](https://etherscan.io/tx/0x8640dfaab67c13e031d794f35c3a678b74d2ec19ae9014f6bdca43879c33421c) | Mainnet (Nov 8 2025) | Successful mint to owner  |

---

## Academic Citation

> **Scherf, M. (2025).**
> *Substrate Theory — Canonical Logical Specification (Ethereum On-Chain Reference).*
> Ethereum Mainnet Contracts `0x31218c4d139e373c185732655658315f1892e1ae` and `0xb58fe65017941F8fb8eE173Bc7a9160dA136151F`.
> Keccak-256 (text) `0x552901c27d17488e6edea08f34db085f2959bcc8eb3f7f0c8869560c4f89ec09`.
> DOI pending via Zenodo.

---

## External Links

* [View `OnchainText` contract on Etherscan](https://etherscan.io/address/0x31218c4d139e373c185732655658315f1892e1ae#code)
* [View `OnchainTextNFT` contract on Etherscan](https://etherscan.io/address/0xb58fe65017941F8fb8eE173Bc7a9160dA136151F#code)
* [Mint Transaction #1](https://etherscan.io/tx/0x8640dfaab67c13e031d794f35c3a678b74d2ec19ae9014f6bdca43879c33421c)

---
