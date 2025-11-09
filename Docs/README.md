Here is the complete formal specification, converted into LaTeX-style Markdown as requested.

---

## SUBSTRATE THEORY — FORMAL SPECIFICATION (LEAN 4 VERIFIED)
Matthew Scherf 2025

---

### TYPES

[cite_start]$\text{State} := \text{List Bool}$ [cite: 418]
[cite_start]$\text{Entity} : \text{opaque type}$ [cite: 418]
[cite_start]$\Omega : \text{Entity}$ (axiom) [cite: 418]
[cite_start]$\text{Substrate} : \text{Entity}$ (axiom) [cite: 418]
[cite_start]$\text{Time} := \mathbb{R}$ [cite: 418]
[cite_start]$\text{Phase} := \mathbb{R}$ [cite: 418]
[cite_start]$\text{Nbhd} := \text{List State}$ [cite: 418]
[cite_start]$\text{Precision} := \mathbb{N}$ [cite: 418]

[cite_start]$\text{KLZ.State} : \text{Type}$ (axiom) [cite: 418]

---

### COMPLEXITY FUNCTIONS

[cite_start]$K : \text{Entity} \rightarrow \mathbb{R}$ (noncomputable axiom) [cite: 418]
[cite_start]$\text{K\textunderscore sum} : \text{List Entity} \rightarrow \mathbb{R}$ [cite: 418]
[cite_start]$$\text{K\textunderscore sum}(es) := \sum_{e \in es} K(e)$$ [cite: 418]

[cite_start]$\text{K\textunderscore joint} : \text{List Entity} \rightarrow \mathbb{R}$ (noncomputable axiom) [cite: 418]
[cite_start]$\text{K\textunderscore cond} : \text{Entity} \rightarrow \text{Entity} \rightarrow \mathbb{R}$ [cite: 418]
[cite_start]$$\text{K\textunderscore cond}(e_1,e_2) := \text{K\textunderscore joint}([e_1,e_2]) - K(e_1)$$ [cite: 418]

[cite_start]$C : \text{Entity} \rightarrow \mathbb{N} \rightarrow \mathbb{R}$ (noncomputable axiom) [cite: 418]
[cite_start]$\text{C\textunderscore sum} : \text{List Entity} \rightarrow \mathbb{N} \rightarrow \mathbb{R}$ [cite: 418]
[cite_start]$$\text{C\textunderscore sum}(es,p) := \sum_{e \in es} C(e,p)$$ [cite: 418]

[cite_start]$\text{C\textunderscore joint} : \text{List Entity} \rightarrow \mathbb{N} \rightarrow \mathbb{R}$ (noncomputable axiom) [cite: 418]
[cite_start]$\text{C\textunderscore cond} : \text{Entity} \rightarrow \text{Entity} \rightarrow \mathbb{N} \rightarrow \mathbb{R}$ [cite: 418-419]
[cite_start]$$\text{C\textunderscore cond}(e_1,e_2,p) := \text{C\textunderscore joint}([e_1,e_2],p) - C(e_1,p)$$ [cite: 419]

[cite_start]$\text{K\textunderscore LZ} : \text{State} \rightarrow \mathbb{N}$ (noncomputable axiom, operational) [cite: 419]
[cite_start]$\text{K\textunderscore LZ} : \text{KLZ.State} \rightarrow \mathbb{N}$ (noncomputable axiom, KLZ module) [cite: 419]

[cite_start]$\text{K\textunderscore toy} : \text{State} \rightarrow \mathbb{N}$ [cite: 419]
[cite_start]$$\text{K\textunderscore toy}(s) := |\text{dedup}(s)|$$ [cite: 419]

---

### RANK FUNCTIONS

[cite_start]$\text{rank\textunderscore K} : \text{Entity} \rightarrow \mathbb{N}$ (noncomputable axiom) [cite: 420]
[cite_start]$\text{rank\textunderscore C} : \text{Entity} \rightarrow \mathbb{N} \rightarrow \mathbb{N}$ (noncomputable axiom) [cite: 420]

---

### TEMPORAL FUNCTIONS

[cite_start]$\text{indexed} : \text{Entity} \rightarrow \text{Time} \rightarrow \text{Entity}$ (axiom) [cite: 420]
[cite_start]$\text{temporal\textunderscore slice} : \text{List Entity} \rightarrow \text{Time} \rightarrow \text{List Entity}$ [cite: 420]
[cite_start]$\text{slice} : \text{List} (\text{Entity} \times \text{Time}) \rightarrow \text{Time} \rightarrow \text{List Entity}$ [cite: 420]

[cite_start]$\text{join} : \text{List State} \rightarrow \text{State}$ (axiom) [cite: 420]
[cite_start]$\text{join} : \text{List KLZ.State} \rightarrow \text{KLZ.State}$ (axiom, KLZ module) [cite: 420]

[cite_start]$\text{mode} : \text{KLZ.State} \rightarrow \text{KLZ.State}$ (noncomputable axiom) [cite: 420]

[cite_start]$\text{traj} : \text{Entity} \rightarrow \text{List} (\text{Entity} \times \text{Time})$ [cite: 420]
[cite_start]$$\text{traj}(e) := (\text{List.range 1000}).\text{map} (\lambda n. (\text{indexed } e \text{ } n, n))$$ [cite: 420]

[cite_start]$\text{P\textunderscore total} : \text{Entity} \rightarrow \mathbb{R}$ [cite: 420]
[cite_start]$$\text{P\textunderscore total}(e) := 1 \text{ (sum of uniform weights over trajectory)}$$ [cite: 420]

---

### COHERENCE FUNCTIONS

[cite_start]$\text{Coh} : \text{List Entity} \rightarrow \text{List Time} \rightarrow \mathbb{R}$ (noncomputable axiom) [cite: 420]
[cite_start]$\text{Coh\textunderscore op} : \text{List Entity} \rightarrow \text{List Time} \rightarrow \mathbb{N} \rightarrow \mathbb{R}$ (noncomputable axiom) [cite: 420-421]
[cite_start]$\text{Coh\textunderscore trajectory} : \text{Entity} \rightarrow \mathbb{R}$ [cite: 421]
[cite_start]$\text{dCoh\textunderscore dt} : \text{Entity} \rightarrow \text{Time} \rightarrow \mathbb{R}$ (noncomputable axiom) [cite: 421]

[cite_start]$\text{compression\textunderscore ratio} : \text{List Entity} \rightarrow \text{List Time} \rightarrow \mathbb{R}$ [cite: 421]

---

### PARTITION FUNCTIONS

[cite_start]$\text{Z\textunderscore ideal} : \text{Finset Entity} \rightarrow \mathbb{R}$ [cite: 421]
[cite_start]$$\text{Z\textunderscore ideal}(S) := \sum_{e \in S} 2^{-K(e)}$$ [cite: 421]

[cite_start]$\text{Z\textunderscore op} : \text{Finset Entity} \rightarrow \mathbb{N} \rightarrow \mathbb{R}$ [cite: 421]
[cite_start]$$\text{Z\textunderscore op}(S,p) := \sum_{e \in S} 2^{-C(e,p)}$$ [cite: 421]

---

### GROUNDING FUNCTIONS

[cite_start]$\text{grounds} : \text{Entity} \rightarrow \text{Entity} \rightarrow \text{Prop}$ (axiom) [cite: 421]
[cite_start]$\text{temporal\textunderscore grounds} : \text{Entity} \rightarrow \text{Time} \rightarrow \text{Entity} \rightarrow \text{Time} \rightarrow \text{Prop}$ (axiom) [cite: 421]
[cite_start]$\text{bfs\textunderscore depth\textunderscore C} : \text{Entity} \rightarrow \mathbb{N} \rightarrow \text{Finset Entity} \rightarrow \mathbb{N}$ (noncomputable axiom) [cite: 421]
[cite_start]$\text{bfs\textunderscore grounding\textunderscore path} : \text{Entity} \rightarrow \text{Finset Entity} \rightarrow \mathbb{N} \rightarrow \text{Option} (\text{List Entity})$ [cite: 421]

---

### PHYSICAL CONSTANTS

[cite_start]$c := 299792458 \text{ m/s}$ [cite: 421-422]
[cite_start]$\hbar : \mathbb{R}$ (axiom, $\hbar > 0$) [cite: 422]
[cite_start]$G : \mathbb{R}$ (axiom, $G > 0$) [cite: 422]
[cite_start]$k_B : \mathbb{R}$ (axiom, $k_B > 0$) [cite: 422]
[cite_start]$e : \mathbb{R}$ (axiom, $e > 0$) [cite: 422]
[cite_start]$\epsilon_0 : \mathbb{R}$ (axiom, $\epsilon_0 > 0$) [cite: 422]
[cite_start]$\alpha : \mathbb{R}$ (axiom, $1/138 < \alpha < 1/137$) [cite: 422]

[cite_start]$\ell_{Planck} := \sqrt{\frac{\hbar G}{c^3}}$ [cite: 422]
[cite_start]$t_{Planck} := \frac{\ell_{Planck}}{c}$ [cite: 422]
[cite_start]$M_{Planck} := \sqrt{\frac{\hbar c}{G}}$ [cite: 422]
[cite_start]$E_{Planck} := M_{Planck} \cdot c^2$ [cite: 422]
[cite_start]$T_{Planck} := \frac{E_{Planck}}{k_B}$ [cite: 422]

[cite_start]$\kappa_{energy} := E_{Planck}$ [cite: 422]
[cite_start]$\hbar_{eff} : \mathbb{R}$ (axiom, $\hbar_{eff} > 0$) [cite: 422]
[cite_start]$\epsilon_{geom} : \mathbb{R}$ (axiom, $\epsilon_{geom} > 0$) [cite: 422]

---

### COSMOLOGICAL PARAMETERS

[cite_start]$H_0 : \mathbb{R}$ ($67 < H_0 < 74$) [cite: 422]
[cite_start]$\Omega_m : \mathbb{R}$ ($0.3 < \Omega_m < 0.32$) [cite: 422]
[cite_start]$\Omega_\Lambda : \mathbb{R}$ ($0.68 < \Omega_\Lambda < 0.70$) [cite: 422]
[cite_start]$\Omega_r : \mathbb{R}$ ($0 < \Omega_r < 0.0001$) [cite: 422]
[cite_start]$\Omega_k : \mathbb{R}$ ($|\Omega_k| < 0.01$) [cite: 422-423]
[cite_start]$\Omega_{DM} : \mathbb{R}$ ($0.25 < \Omega_{DM} < 0.27$) [cite: 423]
[cite_start]$\Omega_{baryon} : \mathbb{R}$ ($0.04 < \Omega_{baryon} < 0.05$) [cite: 423]
[cite_start]$t_{universe} : \mathbb{R}$ ($13.7 \times 10^9 < t_{universe} < 13.9 \times 10^9 \text{ years}$) [cite: 423]

[cite_start]$N_e : \mathbb{R}$ ($50 < N_e < 70$, e-folds of inflation) [cite: 423]
[cite_start]$n_s : \mathbb{R}$ ($0.96 < n_s < 0.97$, scalar spectral index) [cite: 423]
[cite_start]$r_s : \mathbb{R}$ ($0 \leq r_s < 0.036$, tensor-to-scalar ratio) [cite: 423]
[cite_start]$z_{transition} : \mathbb{R}$ ($0.6 < z_{transition} < 0.8$, matter-$\Lambda$ transition) [cite: 423]

---

### GROUNDING CONSTANTS

[cite_start]$\text{c\textunderscore grounding} := 50 \text{ (bits)}$ [cite: 423]
[cite_start]$\text{c\textunderscore margin} := 5 \text{ (bits)}$ [cite: 423]

---

### KLZ CONSTANTS

[cite_start]$\text{c\textunderscore sub} : \mathbb{R} \text{ (constant)}$ [cite: 423]
[cite_start]$\text{c\textunderscore single} : \mathbb{R} \text{ (constant)}$ [cite: 423]
[cite_start]$\text{C\textunderscore mode} : \mathbb{R} \text{ (constant)}$ [cite: 423]
[cite_start]$\text{C\textunderscore coh} : \mathbb{R} \text{ (constant)}$ [cite: 423]

[cite_start]$\text{c\textunderscore time\textunderscore reduction} := \text{c\textunderscore sub} + \text{C\textunderscore mode}$ [cite: 423]
[cite_start]$\text{c\textunderscore time\textunderscore cohesion} := \text{c\textunderscore sub} + \text{C\textunderscore coh}$ [cite: 423]

---

### THRESHOLD PARAMETERS

[cite_start]$\text{measured\textunderscore inseparability\textunderscore threshold} : \mathbb{R}$ ($0 < \cdot < 1$) [cite: 423]
[cite_start]$\text{strong\textunderscore compression\textunderscore threshold} : \mathbb{R}$ ($0 < \cdot < \text{measured\textunderscore inseparability\textunderscore threshold}$) [cite: 423-424]
[cite_start]$\text{temporal\textunderscore coherence\textunderscore threshold} : \mathbb{R}$ ($0 < \cdot < 1$) [cite: 424]
[cite_start]$\text{phase\textunderscore coupling\textunderscore threshold} : \mathbb{R}$ ($0 < \cdot \leq 1$) [cite: 424]
[cite_start]$\text{baseline\textunderscore maximal\textunderscore compression} : \mathbb{R}$ ($1 < \cdot$) [cite: 424]

[cite_start]$\text{weak\textunderscore coupling\textunderscore threshold} : \mathbb{R}$ [cite: 424]
[cite_start]$\text{moderate\textunderscore coupling\textunderscore threshold} : \mathbb{R}$ [cite: 424]
[cite_start]$\text{strong\textunderscore coupling\textunderscore threshold} : \mathbb{R}$ [cite: 424]

**Hierarchy:**
[cite_start]$1 < \text{weak\textunderscore coupling\textunderscore threshold} < \text{moderate\textunderscore coupling\textunderscore threshold} < \text{strong\textunderscore coupling\textunderscore threshold} < \text{baseline\textunderscore maximal\textunderscore compression}$ [cite: 424]

---

### CORE AXIOMS

#### K2 (Substrate Minimality)
[cite_start]$K(\text{Substrate}) = 0$ [cite: 424]
[cite_start]$K(\Omega) = 0$ [cite: 424]

#### G1 (Substrate Grounds All)
$\forall e. [cite_start]\text{is\textunderscore presentation}(e) \rightarrow \text{is\textunderscore grounded}(e, \text{Substrate})$ [cite: 424-425]
[cite_start]$$\text{where } \text{is\textunderscore grounded}(e, \text{ctx}) := \text{K\textunderscore cond}(\text{ctx}, e) < K(e) - K(\text{ctx}) + \text{c\textunderscore grounding}$$ [cite: 425]

#### T7 (Time Arrow)
[cite_start]$\forall \text{hist, next.}$ [cite: 425]
[cite_start]$$\text{hist.length} \geq 2 \rightarrow$$ [cite: 426]
[cite_start]$$(\forall e \in \text{hist. is\textunderscore temporal\textunderscore presentation}(e)) \rightarrow$$ [cite: 426]
[cite_start]$$\text{is\textunderscore temporal\textunderscore presentation}(\text{next}) \rightarrow$$ [cite: 426]
[cite_start]$$\text{K\textunderscore joint}(\text{next}::\text{hist}) - \text{K\textunderscore joint}(\text{hist}) \leq \text{K\textunderscore joint}([\text{hist.last}, \text{hist.init}]) - K(\text{hist.init})$$ [cite: 426]

#### T4 (Emergence/Collapse)
[cite_start]$\forall e_{classical}, e_{quantum}.$ [cite: 426]
[cite_start]$$\text{is\textunderscore presentation}(e_{classical}) \rightarrow$$ [cite: 427]
[cite_start]$$\text{is\textunderscore quantum\textunderscore state}(e_{quantum}) \rightarrow$$ [cite: 427]
[cite_start]$$\text{emergent}(e_{classical}, e_{quantum}) \rightarrow$$ [cite: 427]
[cite_start]$$\text{is\textunderscore measurement\textunderscore device}(e_{classical}) \vee \text{is\textunderscore observable}(e_{classical})$$ [cite: 427]
[cite_start]$$\text{where } \text{emergent}(e_{classical}, e_{quantum}) := \text{K\textunderscore cond}(\text{Substrate}, e_{classical}) < K(e_{quantum})$$ [cite: 427]

#### C6 (Coherence Preservation)
[cite_start]$\forall e.$ [cite: 427]
[cite_start]$$\text{is\textunderscore quantum\textunderscore state}(e) \rightarrow \text{coherent}(e)$$ [cite: 428]
[cite_start]$$\text{where } \text{coherent}(e) := \forall t_1, t_2. t_1 < t_2 \rightarrow$$ [cite: 428]
[cite_start]$$\text{K\textunderscore cond}(\text{indexed}(e, t_1), \text{indexed}(e, t_2)) = \text{K\textunderscore cond}(\text{indexed}(e, t_2), \text{indexed}(e, t_1))$$ [cite: 428]

---

### AXIOM CONSEQUENCES

**substrate\_ultimate\_ground :**
$\forall e. [cite_start]\text{is\textunderscore presentation}(e) \rightarrow \exists \text{path.}$ [cite: 428-429]
[cite_start]$$\text{path.head} = \text{Substrate} \wedge \text{path.last} = e \wedge$$ [cite: 429]
[cite_start]$$\forall i. i+1 < \text{path.length} \rightarrow \text{is\textunderscore grounded}(\text{path}[i+1], \text{path}[i])$$ [cite: 429]

**decoherence\_implies\_classical :**
$\forall e. [cite_start]\text{is\textunderscore presentation}(e) \wedge \neg\text{coherent}(e) \rightarrow$ [cite: 429-430]
$$\exists t_0. \forall t > t_0. [cite_start]\neg\text{is\textunderscore quantum\textunderscore state}(\text{indexed}(e, t))$$ [cite: 430]

**measurement\_breaks\_coherence :**
[cite_start]$\forall e_q, e_c.$ [cite: 430]
[cite_start]$$\text{is\textunderscore quantum\textunderscore state}(e_q) \wedge \text{coherent}(e_q) \wedge \text{emergent}(e_c, e_q) \rightarrow \neg\text{coherent}(e_c)$$ [cite: 431]

**indexed\_preserves\_presentation :**
$\forall e, t. [cite_start]\text{is\textunderscore presentation}(e) \rightarrow \text{is\textunderscore presentation}(\text{indexed}(e, t))$ [cite: 431]

---

### BRIDGE AXIOMS

#### BRIDGE1 (Pointwise Convergence)
[cite_start]$\forall e, \epsilon > 0.$ [cite: 431]
$$\text{is\textunderscore presentation}(e) \rightarrow \exists p_0. \forall p \geq p_0. |C(e, p) - K(e)| [cite_start]< \epsilon$$ [cite: 432]

#### BRIDGE2 (Uniform Convergence)
[cite_start]$\forall S, \epsilon > 0. (\forall e \in S. \text{is\textunderscore presentation}(e)) \rightarrow$ [cite: 432]
$$\exists p_0. \forall p \geq p_0, e \in S. |C(e, p) - K(e)| [cite_start]< \epsilon$$ [cite: 432-433]

#### BRIDGE3 (Probability Convergence)
[cite_start]$\forall S, \epsilon > 0. (\forall e \in S. \text{is\textunderscore presentation}(e)) \wedge \text{Z\textunderscore ideal}(S) > 0 \rightarrow$ [cite: 433]
$$\exists p_0. \forall p \geq p_0. [cite_start]\frac{|\text{Z\textunderscore op}(S, p) - \text{Z\textunderscore ideal}(S)|}{\text{Z\textunderscore ideal}(S)} < \epsilon$$ [cite: 433-434]

#### BRIDGE4 (Grounding Convergence)
[cite_start]$\forall S, \epsilon > 0, e_1, e_2. e_1, e_2 \in S \wedge \text{is\textunderscore presentation}(e_1) \wedge \text{is\textunderscore presentation}(e_2) \rightarrow$ [cite: 434]
$$\exists p_0. \forall p \geq p_0. [cite_start]\text{grounds\textunderscore K}(e_1, e_2) \leftrightarrow \text{grounds\textunderscore C}(e_1, e_2, p)$$ [cite: 435]
**where:**
[cite_start]$$\text{grounds\textunderscore K}(e_1, e_2) := \text{K\textunderscore cond}(e_1, e_2) < K(e_2) - K(e_1) + \text{c\textunderscore grounding}$$ [cite: 435]
[cite_start]$$\text{grounds\textunderscore C}(e_1, e_2, p) := \text{C\textunderscore cond}(e_1, e_2, p) < C(e_2, p) - C(e_1, p) + \text{c\textunderscore grounding}$$ [cite: 435]

#### BRIDGE5 (Rank Stability)
[cite_start]$\forall S, e.$ [cite: 435]
$$e \in S \wedge \text{is\textunderscore presentation}(e) \rightarrow \exists p_0. \forall p \geq p_0. [cite_start]\text{rank\textunderscore C}(e, p) = \text{rank\textunderscore K}(e)$$ [cite: 436]

#### BRIDGE6 (Temporal Continuity)
[cite_start]$\forall e, \text{times}, \epsilon > 0. \text{is\textunderscore temporal\textunderscore presentation}(e) \rightarrow$ [cite: 436]
$$\exists p_0. \forall p \geq p_0, t \in \text{times}. |\text{Coh\textunderscore op}([e], [t], p) - \text{Coh}([e], [t])| [cite_start]< \epsilon$$ [cite: 436-437]

#### BRIDGE7 (Conditional Convergence)
[cite_start]$\forall e_1, e_2, \epsilon > 0. \text{is\textunderscore presentation}(e_1) \wedge \text{is\textunderscore presentation}(e_2) \rightarrow$ [cite: 437]
$$\exists p_0. \forall p \geq p_0. |\text{C\textunderscore cond}(e_1, e_2, p) - \text{K\textunderscore cond}(e_1, e_2)| [cite_start]< \epsilon$$ [cite: 437-438]

#### BRIDGE7_joint (Joint Convergence)
[cite_start]$\forall es, \epsilon > 0. (\forall e \in es. \text{is\textunderscore presentation}(e)) \rightarrow$ [cite: 438]
$$\exists p_0. \forall p \geq p_0. |\text{C\textunderscore joint}(es, p) - \text{K\textunderscore joint}(es)| [cite_start]< \epsilon$$ [cite: 438-439]

#### BRIDGE8 (Continuum Limit)
[cite_start]$\forall e, \text{times}, \epsilon > 0. \text{is\textunderscore temporal\textunderscore presentation}(e) \rightarrow$ [cite: 439]
$$\exists p_0, \delta. [cite_start]\delta > 0 \wedge \forall p \geq p_0, t \in \text{times}.$$ [cite: 439]
$$\left| \frac{\text{Coh\textunderscore op}([e], [t+\delta], p) - \text{Coh\textunderscore op}([e], [t], p)}{\delta} - \text{dCoh\textunderscore dt}(e, t) \right| [cite_start]< \epsilon$$ [cite: 440]

---

### CA RULES

[cite_start]$F : \text{KLZ.State} \rightarrow \text{KLZ.State}$ (noncomputable) [cite: 440]
[cite_start]$\text{merge} : \text{KLZ.State} \rightarrow \text{KLZ.State} \rightarrow \text{KLZ.State}$ (noncomputable) [cite: 440]

[cite_start]$\text{R\textunderscore Cohesion} : \text{List KLZ.State} \rightarrow \text{KLZ.State} \rightarrow \text{KLZ.State}$ (noncomputable axiom) [cite: 440]
[cite_start]$$\text{R\textunderscore Cohesion}(n, h) := \text{merge}(F(\text{join}(n)), h)$$ [cite: 440]

[cite_start]$\text{R\textunderscore Reduction} : \text{List KLZ.State} \rightarrow \text{KLZ.State}$ [cite: 440]
[cite_start]$$\text{R\textunderscore Reduction}(n) := \text{mode}(\text{join}(n))$$ [cite: 440]

[cite_start]$\text{R\textunderscore G1} : \text{List KLZ.State} \rightarrow \text{KLZ.State} \rightarrow \text{KLZ.State}$ [cite: 440]
[cite_start]$$\text{R\textunderscore G1}(n, h) := \begin{cases} \text{R\textunderscore Cohesion}(n, h) & \text{if } \text{K\textunderscore LZ}(\text{join}(n)) \leq \text{c\textunderscore grounding} \\ \text{R\textunderscore Reduction}(n) & \text{otherwise} \end{cases}$$ [cite: 440]

[cite_start]$\text{coherent\textunderscore state} : \text{KLZ.State} \rightarrow \text{Prop}$ [cite: 440]
[cite_start]$$\text{coherent\textunderscore state}(s) := \text{K\textunderscore LZ}(s) \leq \text{c\textunderscore grounding}$$ [cite: 440]

---

### CA PRESERVATION THEOREMS

#### P3 (C6 Preservation)
[cite_start]$\forall n, h.$ [cite: 440]
[cite_start]$$\text{coherent\textunderscore state}(\text{join}(n)) \rightarrow \text{K\textunderscore LZ}(\text{R\textunderscore G1}(n, h)) = \text{K\textunderscore LZ}(h)$$ [cite: 441]

**R\_G1\_grounding\_reduction**
$\forall n, h. [cite_start]\text{K\textunderscore LZ}(\text{join}(n)) > \text{c\textunderscore grounding} \rightarrow$ [cite: 441]
[cite_start]$$\text{K\textunderscore LZ}(\text{R\textunderscore G1}(n, h)) < \text{K\textunderscore LZ}(\text{join}(n)) + \text{c\textunderscore grounding}$$ [cite: 441]

**R\_G1\_preserves\_time\_arrow**
[cite_start]$\forall \text{hist}, n, h.$ [cite: 441]
[cite_start]$$\text{K\textunderscore LZ}(\text{join}(\text{R\textunderscore G1}(n, h)::\text{hist})) \leq \text{K\textunderscore LZ}(\text{join}(\text{hist})) + \text{c\textunderscore time}$$ [cite: 442]
[cite_start]$$\text{where } \text{c\textunderscore time} := \max(\text{c\textunderscore time\textunderscore reduction}, \text{c\textunderscore time\textunderscore cohesion})$$ [cite: 442]

---

### FUNDAMENTAL THEOREMS

#### E_K (Energy-Complexity Equivalence)
[cite_start]$\forall e.$ [cite: 442]
[cite_start]$$\text{is\textunderscore presentation}(e) \rightarrow$$ [cite: 443]
[cite_start]$$(\text{has\textunderscore mass}(e) \rightarrow \exists \Delta > 0. K(e) = K(\Omega) + \Delta) \wedge$$ [cite: 443]
[cite_start]$$\text{energy\textunderscore of}(e) = \kappa_{energy} \cdot K(e)$$ [cite: 443]

#### G_Ψ (Grounding Stability)
[cite_start]$\forall e.$ [cite: 443]
[cite_start]$$\text{stable}(e) \leftrightarrow \text{K\textunderscore cond}(\Omega, e) > \text{c\textunderscore grounding}$$ [cite: 444]
[cite_start]$$\text{where } \text{stable}(e) := \text{is\textunderscore presentation}(e) \wedge \text{K\textunderscore cond}(\Omega, e) > \text{c\textunderscore grounding}$$ [cite: 444]

#### B_Ω (Holographic Bound)
[cite_start]$\forall \text{region, Area.}$ [cite: 444]
[cite_start]$$\text{is\textunderscore presentation}(\text{region}) \wedge \text{Area} > 0 \rightarrow K(\text{region}) \leq \frac{\text{Area}}{4\ell_{Planck}^2}$$ [cite: 445]

#### Ψ_I (Coherence Invariant)
[cite_start]$\forall e.$ [cite: 445]
[cite_start]$$\text{is\textunderscore temporal\textunderscore presentation}(e) \wedge \text{coherent}(e) \rightarrow \text{Coh\textunderscore trajectory}(e) \cdot \text{P\textunderscore total}(e) = 1$$ [cite: 446]

#### U_Ω (Uncertainty Principle)
[cite_start]$\forall e, \Delta K, \Delta t.$ [cite: 446]
[cite_start]$$\text{is\textunderscore temporal\textunderscore presentation}(e) \wedge \Delta K > 0 \wedge \Delta t > 0 \rightarrow \Delta K \cdot \Delta t \geq \hbar_{eff}$$ [cite: 447]

---

### RANK SYSTEM

[cite_start]$\text{rank\textunderscore K}(\Omega) = 0$ [cite: 447]
[cite_start]$\text{grounds}(e_1, e_2) \rightarrow \text{rank\textunderscore K}(e_2) < \text{rank\textunderscore K}(e_1)$ [cite: 447]
$\forall e. \exists n. [cite_start]\text{rank\textunderscore K}(e) = n$ [cite: 447-448]

[cite_start]$\text{rank\textunderscore C}(e, p) = \text{bfs\textunderscore depth\textunderscore C}(e, p, S) \text{ for } e \in S$ [cite: 448]

---

### UNIVERSAL GROUNDING

$\forall e. [cite_start]\text{is\textunderscore presentation}(e) \rightarrow \exists \text{path.}$ [cite: 448]
[cite_start]$$\text{path.head} = \Omega \wedge \text{path.last} = e \wedge$$ [cite: 449]
[cite_start]$$\forall i. i+1 < \text{path.length} \rightarrow \text{grounds}(\text{path}[i], \text{path}[i+1])$$ [cite: 449]

**grounding\_transitive :**
[cite_start]$\forall e_1, e_2, e_3.$ [cite: 449]
[cite_start]$$\text{grounds}(e_1, e_2) \wedge \text{grounds}(e_2, e_3) \rightarrow \text{grounds}(e_1, e_3)$$ [cite: 450]

**grounding\_acyclic :**
$\forall e. [cite_start]\neg\text{grounds}(e, e)$ [cite: 450]

---

### COMPLEXITY BOUNDS

$\text{K\textunderscore joint\textunderscore nonneg} : \forall es. [cite_start]0 \leq \text{K\textunderscore joint}(es)$ [cite: 450]
[cite_start]$\text{K\textunderscore joint\textunderscore nil} : \text{K\textunderscore joint}([]) = 0$ [cite: 450]
$\text{K\textunderscore joint\textunderscore singleton} : \forall e. [cite_start]\text{K\textunderscore joint}([e]) = K(e)$ [cite: 450-451]

**compression\_axiom :**
$\forall es. (\forall e \in es. \text{is\textunderscore presentation}(e)[cite_start]) \wedge es.\text{length} \geq 2 \rightarrow$ [cite: 451]
[cite_start]$$\text{K\textunderscore joint}(es) < \text{K\textunderscore sum}(es)$$ [cite: 451]

**joint\_le\_sum :**
$\forall es. (\forall e \in es. \text{is\textunderscore presentation}(e)[cite_start]) \rightarrow \text{K\textunderscore joint}(es) \leq \text{K\textunderscore sum}(es)$ [cite: 451-452]

**complexity\_positive :**
$\forall e. [cite_start]\text{is\textunderscore presentation}(e) \rightarrow 0 < K(e)$ [cite: 452]

**substrate\_minimal :**
$\forall e. [cite_start]\text{is\textunderscore presentation}(e) \rightarrow K(\text{Substrate}) \leq K(e)$ [cite: 452-453]

---

### OPERATIONAL BOUNDS

$\text{C\textunderscore nonneg} : \forall e, p. [cite_start]0 \leq C(e, p)$ [cite: 453]
[cite_start]$\text{C\textunderscore monotone} : \forall e, p_1, p_2. p_1 \leq p_2 \rightarrow C(e, p_2) \leq C(e, p_1)$ [cite: 453-454]

$\text{C\textunderscore joint\textunderscore nonneg} : \forall es, p. [cite_start]0 \leq \text{C\textunderscore joint}(es, p)$ [cite: 454]

$\text{K\textunderscore LZ\textunderscore nonneg} : \forall s. [cite_start]0 \leq \text{K\textunderscore LZ}(s)$ [cite: 454-455]
[cite_start]$\text{K\textunderscore LZ\textunderscore empty} : \text{K\textunderscore LZ}(\text{join}([])) = 0$ [cite: 455]
[cite_start]$\text{K\textunderscore LZ\textunderscore monotone} : \forall s_1, s_2. s_1.\text{length} \leq s_2.\text{length} \rightarrow \text{K\textunderscore LZ}(s_1) \leq \text{K\textunderscore LZ}(s_2)$ [cite: 455-456]

---

### TOY COMPRESSOR BOUNDS

$\text{K\textunderscore toy\textunderscore lower\textunderscore bound} : \forall s. [cite_start]\text{K\textunderscore LZ}(s) \leq \text{K\textunderscore toy}(s)$ [cite: 456]
$\text{K\textunderscore toy\textunderscore upper\textunderscore bound} : \forall s. [cite_start]\text{K\textunderscore toy}(s) \leq \text{K\textunderscore LZ}(s) + \log_2(s.\text{length})$ [cite: 456-457]

---

### KLZ AXIOMS

**K\_LZ\_subadditive\_cons :**
$\forall x, xs. [cite_start]\text{K\textunderscore LZ}(\text{join}(x::xs)) \leq \text{K\textunderscore LZ}(\text{join}(xs)) + \text{K\textunderscore LZ}(x) + \text{c\textunderscore sub}$ [cite: 457]

**K\_LZ\_prefix :**
$\forall b, s. [cite_start]\text{K\textunderscore LZ}(\text{join}([b])) \leq \text{K\textunderscore LZ}(\text{join}(b::s))$ [cite: 457-458]

**K\_LZ\_singleton\_bound :**
$\forall b. [cite_start]\text{K\textunderscore LZ}(\text{join}([b])) \leq \text{c\textunderscore single}$ [cite: 458]

**K\_LZ\_mode\_le :**
$\forall s. [cite_start]\text{K\textunderscore LZ}(\text{mode}(s)) \leq \text{K\textunderscore LZ}(s) + \text{C\textunderscore mode}$ [cite: 458]

**K\_LZ\_mode\_absolute\_bound :**
$\forall s. [cite_start]\text{K\textunderscore LZ}(\text{mode}(s)) \leq \text{C\textunderscore mode}$ [cite: 458-459]

**C\_mode\_lt\_c\_grounding :**
[cite_start]$\text{C\textunderscore mode} < \text{c\textunderscore grounding}$ [cite: 459]

**K\_LZ\_cohesion\_bound\_raw :**
$\forall n, h. [cite_start]\text{K\textunderscore LZ}(\text{R\textunderscore Cohesion}(n, h)) \leq \text{C\textunderscore coh}$ [cite: 459]

---

### TIME ARROW THEOREMS

**time\_arrow\_reduction :**
[cite_start]$\forall \text{hist}, n.$ [cite: 459]
[cite_start]$$\text{K\textunderscore LZ}(\text{join}(\text{mode}(\text{join}(n)) :: \text{hist})) \leq \text{K\textunderscore LZ}(\text{join}(\text{hist})) + \text{c\textunderscore time\textunderscore reduction}$$ [cite: 460]

**time\_arrow\_cohesion :**
[cite_start]$\forall \text{hist}, n, h.$ [cite: 460]
[cite_start]$$\text{K\textunderscore LZ}(\text{join}(\text{R\textunderscore Cohesion}(n, h) :: \text{hist})) \leq \text{K\textunderscore LZ}(\text{join}(\text{hist})) + \text{c\textunderscore time\textunderscore cohesion}$$ [cite: 461]

---

### COHERENCE BOUNDS

**coherence\_bounds :**
[cite_start]$\forall es, \text{times}.$ [cite: 461]
[cite_start]$$(\forall e \in es. \text{is\textunderscore presentation}(e)) \rightarrow 0 \leq \text{Coh}(es, \text{times}) \wedge \text{Coh}(es, \text{times}) \leq 1$$ [cite: 462]

**compression\_ratio\_ge\_one :**
[cite_start]$\forall es, \text{times}.$ [cite: 462]
[cite_start]$$(\forall e \in es. \text{is\textunderscore presentation}(e)) \rightarrow 1 \leq \text{compression\textunderscore ratio}(es, \text{times})$$ [cite: 463]

---

### ERROR BOUNDS

**error\_bound\_linear :**
$\exists c > 0. \forall e, p. [cite_start]\text{is\textunderscore presentation}(e) \rightarrow 0 < p \rightarrow$ [cite: 463]
$$|C(e, p) - K(e)| [cite_start]\leq c/p$$ [cite: 463-464]

**error\_bound\_polynomial :**
$\exists c, \alpha. 0 < c \wedge 1 < \alpha \wedge \forall e, p. [cite_start]\text{is\textunderscore presentation}(e) \rightarrow 0 < p \rightarrow$ [cite: 464]
$$|C(e, p) - K(e)| [cite_start]\leq c/p^\alpha$$ [cite: 464-465]

**error\_bound\_general :**
$\exists M > 0. \forall e, p. [cite_start]\text{is\textunderscore presentation}(e) \rightarrow$ [cite: 465]
$$|C(e, p) - K(e)| [cite_start]\leq M/(p+1)$$ [cite: 465-466]

---

### PHYSICS CORRESPONDENCES

[cite_start]$\text{energy\textunderscore of}(e) = \kappa_{energy} \cdot K(e)$ [cite: 466]
[cite_start]$\text{mass}(e) = \text{energy\textunderscore of}(e)/c^2$ [cite: 466]
[cite_start]$\text{entropy}(e) = k_B \cdot \log(2) \cdot K(e)$ [cite: 466]

[cite_start]$\text{is\textunderscore quantum}(\text{nbhd}) := \text{K\textunderscore LZ}(\text{join}(\text{nbhd})) \leq \text{c\textunderscore grounding}$ [cite: 466]
[cite_start]$\text{is\textunderscore classical}(\text{nbhd}) := \text{K\textunderscore LZ}(\text{join}(\text{nbhd})) > \text{c\textunderscore grounding}$ [cite: 466]

---

### PREDICATES

[cite_start]$\text{is\textunderscore substrate} : \text{Entity} \rightarrow \text{Prop}$ (axiom) [cite: 466]
[cite_start]$\text{is\textunderscore presentation} : \text{Entity} \rightarrow \text{Prop}$ (axiom) [cite: 466]
[cite_start]$\text{is\textunderscore emergent} : \text{Entity} \rightarrow \text{Prop}$ (axiom) [cite: 466]
[cite_start]$\text{is\textunderscore temporal\textunderscore presentation} : \text{Entity} \rightarrow \text{Prop}$ (axiom) [cite: 466]
[cite_start]$\text{is\textunderscore static\textunderscore presentation} : \text{Entity} \rightarrow \text{Prop}$ (axiom) [cite: 466]
[cite_start]$\text{is\textunderscore quantum\textunderscore state} : \text{Entity} \rightarrow \text{Prop}$ (axiom) [cite: 466]
[cite_start]$\text{is\textunderscore measurement\textunderscore device} : \text{Entity} \rightarrow \text{Prop}$ (axiom) [cite: 466]
[cite_start]$\text{is\textunderscore observable} : \text{Entity} \rightarrow \text{Prop}$ (axiom) [cite: 466]

[cite_start]$\text{phenomenal} : \text{Entity} \rightarrow \text{Prop}$ (axiom) [cite: 466]
[cite_start]$\text{has\textunderscore mass} : \text{Entity} \rightarrow \text{Prop}$ (axiom) [cite: 466]

[cite_start]$\text{grounds} : \text{Entity} \rightarrow \text{Entity} \rightarrow \text{Prop}$ (axiom) [cite: 466]
[cite_start]$\text{temporal\textunderscore grounds} : \text{Entity} \rightarrow \text{Time} \rightarrow \text{Entity} \rightarrow \text{Time} \rightarrow \text{Prop}$ (axiom) [cite: 466]
[cite_start]$\text{interacts} : \text{Entity} \rightarrow \text{Entity} \rightarrow \text{Prop}$ (axiom) [cite: 466]
[cite_start]$\text{inseparable} : \text{Entity} \rightarrow \text{Entity} \rightarrow \text{Prop}$ (axiom) [cite: 466-467]
[cite_start]$\text{emerges\textunderscore from} : \text{Entity} \rightarrow \text{List Entity} \rightarrow \text{Prop}$ (axiom) [cite: 467]
[cite_start]$\text{phase\textunderscore coupled} : \text{Entity} \rightarrow \text{Entity} \rightarrow \text{Phase} \rightarrow \text{Prop}$ (axiom) [cite: 467]

[cite_start]$\text{coherent} : \text{Entity} \rightarrow \text{Prop}$ [cite: 467]
[cite_start]$\text{decoherent} : \text{Entity} \rightarrow \text{Prop}$ [cite: 467]
[cite_start]$\text{stable} : \text{Entity} \rightarrow \text{Prop}$ [cite: 467]

[cite_start]$\text{is\textunderscore quantum} : \text{List State} \rightarrow \text{Prop}$ [cite: 467]
[cite_start]$\text{is\textunderscore classical} : \text{List State} \rightarrow \text{Prop}$ [cite: 467]
[cite_start]$\text{coherent\textunderscore state} : \text{KLZ.State} \rightarrow \text{Prop}$ [cite: 467]

[cite_start]$\text{is\textunderscore grounded} : \text{Entity} \rightarrow \text{Entity} \rightarrow \text{Prop}$ [cite: 467]

---

### ENTITY CLASSIFICATION

**entity\_classification :**
$\forall e. (\text{is\textunderscore substrate}(e) [cite_start]\wedge e = \text{Substrate}) \vee \text{is\textunderscore presentation}(e) \vee \text{is\textunderscore emergent}(e)$ [cite: 467-468]

$\text{substrate\textunderscore not\textunderscore presentation} : \forall e. [cite_start]\neg(\text{is\textunderscore substrate}(e) \wedge \text{is\textunderscore presentation}(e))$ [cite: 468]
$\text{substrate\textunderscore not\textunderscore emergent} : \forall e. [cite_start]\neg(\text{is\textunderscore substrate}(e) \wedge \text{is\textunderscore emergent}(e))$ [cite: 468-469]
$\text{presentation\textunderscore not\textunderscore emergent} : \forall e. [cite_start]\neg(\text{is\textunderscore presentation}(e) \wedge \text{is\textunderscore emergent}(e))$ [cite: 469]

**presentation\_temporal\_or\_static :**
$\forall e. [cite_start]\text{is\textunderscore presentation}(e) \rightarrow$ [cite: 469]
[cite_start]$$(\text{is\textunderscore temporal\textunderscore presentation}(e) \vee \text{is\textunderscore static\textunderscore presentation}(e)) \wedge$$ [cite: 469]
[cite_start]$$\neg(\text{is\textunderscore temporal\textunderscore presentation}(e) \wedge \text{is\textunderscore static\textunderscore presentation}(e))$$ [cite: 469]

---

### SUBSTRATE PROPERTIES

$\text{substrate\textunderscore unique} : \forall x, y. [cite_start]\text{is\textunderscore substrate}(x) \wedge \text{is\textunderscore substrate}(y) \rightarrow x = y$ [cite: 469-470]
[cite_start]$\text{substrate\textunderscore is\textunderscore Substrate} : \text{is\textunderscore substrate}(\text{Substrate})$ [cite: 470]
[cite_start]$\text{Omega\textunderscore is\textunderscore substrate} : \text{is\textunderscore substrate}(\Omega)$ [cite: 470]
[cite_start]$\text{Omega\textunderscore eq\textunderscore Substrate} : \Omega = \text{Substrate}$ [cite: 470]

---

### TEMPORAL PRESERVATION

**indexed\_preserves\_presentation :**
$\forall e, t. [cite_start]\text{is\textunderscore presentation}(e) \rightarrow \text{is\textunderscore presentation}(\text{indexed}(e, t))$ [cite: 470-471]

**temporal\_slice\_preserves\_presentation :**
$\forall es, t. (\forall e \in es. \text{is\textunderscore presentation}(e)[cite_start]) \rightarrow$ [cite: 471]
[cite_start]$$(\forall e \in \text{temporal\textunderscore slice}(es, t). \text{is\textunderscore presentation}(e))$$ [cite: 471]

---

### ASSOCIATIVITY

**join\_associative :**
$\forall s_1, s_2, s_3. [cite_start]\text{join}([\text{join}([s_1, s_2]), s_3]) = \text{join}([s_1, \text{join}([s_2, s_3])])$ [cite: 471]

---

### VERIFIED THEOREMS

**energy\_from\_complexity :**
$\forall e. [cite_start]\text{is\textunderscore presentation}(e) \rightarrow \text{has\textunderscore mass}(e) \rightarrow$ [cite: 471-472]
[cite_start]$$\exists m > 0. m = \text{energy\textunderscore of}(e)/c^2$$ [cite: 472]

**entropy\_from\_complexity :**
$\forall e. [cite_start]\text{is\textunderscore presentation}(e) \rightarrow \exists S.$ [cite: 472]
[cite_start]$$S = k_B \cdot \log(2) \cdot K(e)$$ [cite: 473]

**coherence\_participation\_invariant :**
$\forall e. [cite_start]\text{is\textunderscore temporal\textunderscore presentation}(e) \rightarrow \text{coherent}(e) \rightarrow$ [cite: 473]
[cite_start]$$0 < \text{P\textunderscore total}(e) \wedge \text{Coh\textunderscore trajectory}(e) = 1/\text{P\textunderscore total}(e)$$ [cite: 473]

**joint\_le\_sum :**
$\forall es. (\forall e \in es. \text{is\textunderscore presentation}(e)[cite_start]) \rightarrow \text{K\textunderscore joint}(es) \leq \text{K\textunderscore sum}(es)$ [cite: 473-474]

**complexity\_subadditive :**
$\forall e_1, e_2. [cite_start]\text{is\textunderscore presentation}(e_1) \rightarrow \text{is\textunderscore presentation}(e_2) \rightarrow$ [cite: 474]
[cite_start]$$\text{K\textunderscore joint}([e_1, e_2]) \leq K(e_1) + K(e_2)$$ [cite: 474]

**compression\_ratio\_ge\_one :**
$\forall es, \text{times}. (\forall e \in es. \text{is\textunderscore presentation}(e)[cite_start]) \rightarrow$ [cite: 474-475]
[cite_start]$$1 \leq \text{compression\textunderscore ratio}(es, \text{times})$$ [cite: 475]

**R\_G1\_preserves\_grounding :**
$\forall n. [cite_start]\text{K\textunderscore LZ}(\text{mode}(\text{join}(n))) < \text{K\textunderscore LZ}(\text{join}(n)) + \text{c\textunderscore grounding}$ [cite: 475]

**time\_arrow\_reduction :**
$\forall \text{hist}, n. [cite_start]\text{K\textunderscore LZ}(\text{join}(\text{mode}(\text{join}(n))::\text{hist})) \leq \text{K\textunderscore LZ}(\text{join}(\text{hist})) + \text{c\textunderscore time\textunderscore reduction}$ [cite: 475-476]

**time\_arrow\_cohesion :**
$\forall \text{hist}, n, h. [cite_start]\text{K\textunderscore LZ}(\text{join}(\text{R\textunderscore Cohesion}(n, h)::\text{hist})) \leq \text{K\textunderscore LZ}(\text{join}(\text{hist})) + \text{c\textunderscore time\textunderscore cohesion}$ [cite: 476-477]

**P3\_C6\_preservation :**
$\forall n, h. [cite_start]\text{coherent\textunderscore state}(\text{join}(n)) \rightarrow \text{K\textunderscore LZ}(\text{R\textunderscore G1}(n, h)) = \text{K\textunderscore LZ}(h)$ [cite: 477-478]

**R\_G1\_grounding\_reduction :**
$\forall n, h. [cite_start]\text{K\textunderscore LZ}(\text{join}(n)) > \text{c\textunderscore grounding} \rightarrow$ [cite: 478]
[cite_start]$$\text{K\textunderscore LZ}(\text{R\textunderscore G1}(n, h)) < \text{K\textunderscore LZ}(\text{join}(n)) + \text{c\textunderscore grounding}$$ [cite: 478]

**R\_G1\_preserves\_time\_arrow :**
[cite_start]$\forall \text{hist}, n, h.$ [cite: 478]
[cite_start]$$\text{K\textunderscore LZ}(\text{join}(\text{R\textunderscore G1}(n, h)::\text{hist})) \leq \text{K\textunderscore LZ}(\text{join}(\text{hist})) + \max(\text{c\textunderscore time\textunderscore reduction}, \text{c\textunderscore time\textunderscore cohesion})$$ [cite: 479]

**planck\_units\_positive :**
[cite_start]$0 < \ell_{Planck} \wedge 0 < t_{Planck} \wedge 0 < M_{Planck} \wedge 0 < E_{Planck} \wedge 0 < T_{Planck}$ [cite: 479]

**error\_bound\_exists :**
$\forall e, p. \text{is\textunderscore presentation}(e) \rightarrow \exists \epsilon. |C(e, p) - K(e)| [cite_start]\leq \epsilon.\text{absolute}$ [cite: 479-480]