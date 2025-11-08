Got it — let’s fix and modernize your **README** with all the new on-chain values **and a working way to read the text** (not bytecode).

Here’s the updated section ready to replace your current on-chain record block:

---

## On-Chain Canonical Record (Ethereum Mainnet)

### Smart Contracts

| Contract                                                                                         | Type                   | Address                                      | Verified | Description                                                             |
| ------------------------------------------------------------------------------------------------ | ---------------------- | -------------------------------------------- | -------- | ----------------------------------------------------------------------- |
| [`OnchainText`](https://etherscan.io/address/0x31218c4d139e373c185732655658315f1892e1ae#code)    | Immutable data pointer | `0x31218c4d139e373c185732655658315f1892e1ae` | ✅ Yes    | Contains the compiled helper contract for text retrieval                |
| [`OnchainTextNFT`](https://etherscan.io/address/0xb58fe65017941F8fb8eE173Bc7a9160dA136151F#code) | ERC-721 NFT wrapper    | `0xb58fe65017941F8fb8eE173Bc7a9160dA136151F` | ✅ Yes    | Mints and references the canonical text through Base64-encoded metadata |

---

### NFT Details

| Field                | Value                                                                                                                                                              |
| -------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| **Collection Name**  | SUBSTRATE THEORY CANONICAL (Updated)                                                                                                                               |
| **Token ID**         | #1                                                                                                                                                                 |
| **Owner**            | [`0x367E6B384b6Ec96Ccec478F7B314d3deB2F01195`](https://etherscan.io/address/0x367E6B384b6Ec96Ccec478F7B314d3deB2F01195)                                            |
| **Minted From**      | [`0x7c8a138f581A0a87C1BF63BF697A9BC729ac2dE1`](https://etherscan.io/address/0x7c8a138f581A0a87C1BF63BF697A9BC729ac2dE1)                                            |
| **Transaction Hash** | [`0x8640dfaab67c13e031d794f35c3a678b74d2ec19ae9014f6bdca43879c33421c`](https://etherscan.io/tx/0x8640dfaab67c13e031d794f35c3a678b74d2ec19ae9014f6bdca43879c33421c) |
| **Timestamp**        | Nov-08-2025 11:30 UTC                                                                                                                                              |
| **Gas Fee**          | 0.000006637 ETH ($0.02)                                                                                                                                            |
| **Function**         | `mint(address _to)`                                                                                                                                                |

---

### Canonical Content Verification

| Field                      | Value                                                                |
| -------------------------- | -------------------------------------------------------------------- |
| **Canonical text (bytes)** | `18043`                                                              |
| **Keccak-256 (text)**      | `0x90147f16c543fe45a92a252340f20d055535a10f12eb43aab87eaa2a4879fbc0` |
| **Keccak-256 (bytecode)**  | `0x7dd220053f5ec52419e2a2de159f7b32946f3d41a342dbf77e15c5ca65d8a0a2` |

#### 🔍 To Read the Text (it’s Base64-encoded in the metadata)

```bash
# Define NFT contract + tokenId
COLL=0xb58fe65017941F8fb8eE173Bc7a9160dA136151F
ID=1
RPC=https://ethereum.publicnode.com

# 1. Fetch and decode metadata JSON
URI=$(cast call "$COLL" --rpc-url "$RPC" "tokenURI(uint256)(string)" $ID | tr -d '"')
echo "$URI" | sed 's|^data:application/json;base64,||' | base64 -d > meta.json

# 2. Extract canonical text
jq -r '.external_url' meta.json | sed 's|^data:text/plain;base64,||' | base64 -d > substrate.txt

# 3. Verify
xxd -p -c 999999 substrate.txt | cast keccak
# expected → 0x90147f16c543fe45a92a252340f20d055535a10f12eb43aab87eaa2a4879fbc0
wc -c < substrate.txt   # expected → 18043

# 4. (Optional) Preview SVG
jq -r '.image' meta.json | sed 's|^data:image/svg+xml;base64,||' | base64 -d > image.svg
open image.svg  # or xdg-open on Linux
```

---

### Provenance Transactions

| Action                  | Tx Hash (link)                                                                                                                                                     | Notes              |
| ----------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------ | ------------------ |
| Deploy `OnchainText`    | [`0xaf60585cb51e4eb289a0babf1fc3c66a17e3244ed26874fbfe505f8b433e916f`](https://etherscan.io/tx/0xaf60585cb51e4eb289a0babf1fc3c66a17e3244ed26874fbfe505f8b433e916f) | Pointer contract   |
| Deploy `OnchainTextNFT` | [`0xf85eed429b328287e0986092f2b27211ec2d1c3743cf8f48f92bcb3a59d545a2`](https://etherscan.io/tx/0xf85eed429b328287e0986092f2b27211ec2d1c3743cf8f48f92bcb3a59d545a2) | ERC-721 collection |
| Mint Token #1           | [`0x8640dfaab67c13e031d794f35c3a678b74d2ec19ae9014f6bdca43879c33421c`](https://etherscan.io/tx/0x8640dfaab67c13e031d794f35c3a678b74d2ec19ae9014f6bdca43879c33421c) | Successful mint    |

---

### In Short

Use the commands above → they download the real `substrate.txt` from on-chain Base64 data, verify its hash ( `0x9014…fbc0` ), and open it for you.
No EVM bytecode decoding needed anymore — this gives you the full human-readable canonical text.
