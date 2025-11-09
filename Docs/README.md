## SUBSTRATE THEORY — FORMAL SPECIFICATION (LEAN 4 VERIFIED)
Matthew Scherf 2025

---

### TYPES

$\text{State} := \text{List Bool}$
$\text{Entity} : \text{opaque type}$
$\Omega : \text{Entity}$ (axiom)
$\text{Substrate} : \text{Entity}$ (axiom)
$\text{Time} := \mathbb{R}$
$\text{Phase} := \mathbb{R}$
$\text{Nbhd} := \text{List State}$
$\text{Precision} := \mathbb{N}$

$\text{KLZ.State} : \text{Type}$ (axiom)

---

### COMPLEXITY FUNCTIONS

$K : \text{Entity} \rightarrow \mathbb{R}$ (noncomputable axiom)
$\text{K\_ sum} : \text{List Entity} \rightarrow \mathbb{R}$
$$\text{K\_ sum}(es) := \sum_{e \in es} K(e)$$

$\text{K\_ joint} : \text{List Entity} \rightarrow \mathbb{R}$ (noncomputable axiom)
$\text{K\_ cond} : \text{Entity} \rightarrow \text{Entity} \rightarrow \mathbb{R}$
$$\text{K\_ cond}(e_1,e_2) := \text{K\_ joint}([e_1,e_2]) - K(e_1)$$

$C : \text{Entity} \rightarrow \mathbb{N} \rightarrow \mathbb{R}$ (noncomputable axiom)
$\text{C\_ sum} : \text{List Entity} \rightarrow \mathbb{N} \rightarrow \mathbb{R}$
$$\text{C\_ sum}(es,p) := \sum_{e \in es} C(e,p)$$

$\text{C\_ joint} : \text{List Entity} \rightarrow \mathbb{N} \rightarrow \mathbb{R}$ (noncomputable axiom)
$\text{C\_ cond} : \text{Entity} \rightarrow \text{Entity} \rightarrow \mathbb{N} \rightarrow \mathbb{R}$
$$\text{C\_ cond}(e_1,e_2,p) := \text{C\_ joint}([e_1,e_2],p) - C(e_1,p)$$

$\text{K\_ LZ} : \text{State} \rightarrow \mathbb{N}$ (noncomputable axiom, operational)
$\text{K\_ LZ} : \text{KLZ.State} \rightarrow \mathbb{N}$ (noncomputable axiom, KLZ module)

$\text{K\_ toy} : \text{State} \rightarrow \mathbb{N}$
$$\text{K\_ toy}(s) := |\text{dedup}(s)|$$

---

### RANK FUNCTIONS

$\text{rank\_ K} : \text{Entity} \rightarrow \mathbb{N}$ (noncomputable axiom)
$\text{rank\_ C} : \text{Entity} \rightarrow \mathbb{N} \rightarrow \mathbb{N}$ (noncomputable axiom)

---

### TEMPORAL FUNCTIONS

$\text{indexed} : \text{Entity} \rightarrow \text{Time} \rightarrow \text{Entity}$ (axiom)
$\text{temporal\_ slice} : \text{List Entity} \rightarrow \text{Time} \rightarrow \text{List Entity}$
$\text{slice} : \text{List} (\text{Entity} \times \text{Time}) \rightarrow \text{Time} \rightarrow \text{List Entity}$

$\text{join} : \text{List State} \rightarrow \text{State}$ (axiom)
$\text{join} : \text{List KLZ.State} \rightarrow \text{KLZ.State}$ (axiom, KLZ module)

$\text{mode} : \text{KLZ.State} \rightarrow \text{KLZ.State}$ (noncomputable axiom)

$\text{traj} : \text{Entity} \rightarrow \text{List} (\text{Entity} \times \text{Time})$
$$\text{traj}(e) := (\text{List.range 1000}).\text{map} (\lambda n. (\text{indexed } e \text{ } n, n))$$

$\text{P\_ total} : \text{Entity} \rightarrow \mathbb{R}$
$$\text{P\_ total}(e) := 1 \text{ (sum of uniform weights over trajectory)}$$

---

### COHERENCE FUNCTIONS

$\text{Coh} : \text{List Entity} \rightarrow \text{List Time} \rightarrow \mathbb{R}$ (noncomputable axiom)
$\text{Coh\_ op} : \text{List Entity} \rightarrow \text{List Time} \rightarrow \mathbb{N} \rightarrow \mathbb{R}$ (noncomputable axiom)
$\text{Coh\_ trajectory} : \text{Entity} \rightarrow \mathbb{R}$
$\text{dCoh\_ dt} : \text{Entity} \rightarrow \text{Time} \rightarrow \mathbb{R}$ (noncomputable axiom)

$\text{compression\_ ratio} : \text{List Entity} \rightarrow \text{List Time} \rightarrow \mathbb{R}$

---

### PARTITION FUNCTIONS

$\text{Z\_ ideal} : \text{Finset Entity} \rightarrow \mathbb{R}$
$$\text{Z\_ ideal}(S) := \sum_{e \in S} 2^{-K(e)}$$

$\text{Z\_ op} : \text{Finset Entity} \rightarrow \mathbb{N} \rightarrow \mathbb{R}$
$$\text{Z\_ op}(S,p) := \sum_{e \in S} 2^{-C(e,p)}$$

---

### GROUNDING FUNCTIONS

$\text{grounds} : \text{Entity} \rightarrow \text{Entity} \rightarrow \text{Prop}$ (axiom)
$\text{temporal\_ grounds} : \text{Entity} \rightarrow \text{Time} \rightarrow \text{Entity} \rightarrow \text{Time} \rightarrow \text{Prop}$ (axiom)
$\text{bfs\_ depth\_ C} : \text{Entity} \rightarrow \mathbb{N} \rightarrow \text{Finset Entity} \rightarrow \mathbb{N}$ (noncomputable axiom)
$\text{bfs\_ grounding\_ path} : \text{Entity} \rightarrow \text{Finset Entity} \rightarrow \mathbb{N} \rightarrow \text{Option} (\text{List Entity})$

---

### PHYSICAL CONSTANTS

$c := 299792458 \text{ m/s}$
$\hbar : \mathbb{R}$ (axiom, $\hbar > 0$)
$G : \mathbb{R}$ (axiom, $G > 0$)
$k_B : \mathbb{R}$ (axiom, $k_B > 0$)
$e : \mathbb{R}$ (axiom, $e > 0$)
$\epsilon_0 : \mathbb{R}$ (axiom, $\epsilon_0 > 0$)
$\alpha : \mathbb{R}$ (axiom, $1/138 < \alpha < 1/137$)

$\ell_{Planck} := \sqrt{\frac{\hbar G}{c^3}}$
$t_{Planck} := \frac{\ell_{Planck}}{c}$
$M_{Planck} := \sqrt{\frac{\hbar c}{G}}$
$E_{Planck} := M_{Planck} \cdot c^2$
$T_{Planck} := \frac{E_{Planck}}{k_B}$

$\kappa_{energy} := E_{Planck}$
$\hbar_{eff} : \mathbb{R}$ (axiom, $\hbar_{eff} > 0$)
$\epsilon_{geom} : \mathbb{R}$ (axiom, $\epsilon_{geom} > 0$)

---

### COSMOLOGICAL PARAMETERS

$H_0 : \mathbb{R}$ ($67 < H_0 < 74$)
$\Omega_m : \mathbb{R}$ ($0.3 < \Omega_m < 0.32$)
$\Omega_\Lambda : \mathbb{R}$ ($0.68 < \Omega_\Lambda < 0.70$)
$\Omega_r : \mathbb{R}$ ($0 < \Omega_r < 0.0001$)
$\Omega_k : \mathbb{R}$ ($|\Omega_k| < 0.01$)
$\Omega_{DM} : \mathbb{R}$ ($0.25 < \Omega_{DM} < 0.27$)
$\Omega_{baryon} : \mathbb{R}$ ($0.04 < \Omega_{baryon} < 0.05$)
$t_{universe} : \mathbb{R}$ ($13.7 \times 10^9 < t_{universe} < 13.9 \times 10^9 \text{ years}$)

$N_e : \mathbb{R}$ ($50 < N_e < 70$, e-folds of inflation)
$n_s : \mathbb{R}$ ($0.96 < n_s < 0.97$, scalar spectral index)
$r_s : \mathbb{R}$ ($0 \leq r_s < 0.036$, tensor-to-scalar ratio)
$z_{transition} : \mathbb{R}$ ($0.6 < z_{transition} < 0.8$, matter-$\Lambda$ transition)

---

### GROUNDING CONSTANTS

$\text{c\_ grounding} := 50 \text{ (bits)}$
$\text{c\_ margin} := 5 \text{ (bits)}$

---

### KLZ CONSTANTS

$\text{c\_ sub} : \mathbb{R} \text{ (constant)}$
$\text{c\_ single} : \mathbb{R} \text{ (constant)}$
$\text{C\_ mode} : \mathbb{R} \text{ (constant)}$
$\text{C\_ coh} : \mathbb{R} \text{ (constant)}$

$\text{c\_ time\_ reduction} := \text{c\_ sub} + \text{C\_ mode}$
$\text{c\_ time\_ cohesion} := \text{c\_ sub} + \text{C\_ coh}$

---

### THRESHOLD PARAMETERS

$\text{measured\_ inseparability\_ threshold} : \mathbb{R}$ ($0 < \cdot < 1$)
$\text{strong\_ compression\_ threshold} : \mathbb{R}$ ($0 < \cdot < \text{measured\_ inseparability\_ threshold}$)
$\text{temporal\_ coherence\_ threshold} : \mathbb{R}$ ($0 < \cdot < 1$)
$\text{phase\_ coupling\_ threshold} : \mathbb{R}$ ($0 < \cdot \leq 1$)
$\text{baseline\_ maximal\_ compression} : \mathbb{R}$ ($1 < \cdot$)

$\text{weak\_ coupling\_ threshold} : \mathbb{R}$
$\text{moderate\_ coupling\_ threshold} : \mathbb{R}$
$\text{strong\_ coupling\_ threshold} : \mathbb{R}$

**Hierarchy:**
$1 < \text{weak\_ coupling\_ threshold} < \text{moderate\_ coupling\_ threshold} < \text{strong\_ coupling\_ threshold} < \text{baseline\_ maximal\_ compression}$

---

### CORE AXIOMS

#### K2 (Substrate Minimality)
$K(\text{Substrate}) = 0$
$K(\Omega) = 0$

#### G1 (Substrate Grounds All)
$\forall e. \text{is\_ presentation}(e) \rightarrow \text{is\_ grounded}(e, \text{Substrate})$
$$\text{where } \text{is\_ grounded}(e, \text{ctx}) := \text{K\_ cond}(\text{ctx}, e) < K(e) - K(\text{ctx}) + \text{c\_ grounding}$$

#### T7 (Time Arrow)
$\forall \text{hist, next.}$
$$\text{hist.length} \geq 2 \rightarrow$$
$$(\forall e \in \text{hist. is\_ temporal\_ presentation}(e)) \rightarrow$$
$$\text{is\_ temporal\_ presentation}(\text{next}) \rightarrow$$
$$\text{K\_ joint}(\text{next}::\text{hist}) - \text{K\_ joint}(\text{hist}) \leq \text{K\_ joint}([\text{hist.last}, \text{hist.init}]) - K(\text{hist.init})$$

#### T4 (Emergence/Collapse)
$\forall e_{classical}, e_{quantum}.$
$$\text{is\_ presentation}(e_{classical}) \rightarrow$$
$$\text{is\_ quantum\_ state}(e_{quantum}) \rightarrow$$
$$\text{emergent}(e_{classical}, e_{quantum}) \rightarrow$$
$$\text{is\_ measurement\_ device}(e_{classical}) \vee \text{is\_ observable}(e_{classical})$$
$$\text{where } \text{emergent}(e_{classical}, e_{quantum}) := \text{K\_ cond}(\text{Substrate}, e_{classical}) < K(e_{quantum})$$

#### C6 (Coherence Preservation)
$\forall e.$
$$\text{is\_ quantum\_ state}(e) \rightarrow \text{coherent}(e)$$
$$\text{where } \text{coherent}(e) := \forall t_1, t_2. t_1 < t_2 \rightarrow$$
$$\text{K\_ cond}(\text{indexed}(e, t_1), \text{indexed}(e, t_2)) = \text{K\_ cond}(\text{indexed}(e, t_2), \text{indexed}(e, t_1))$$

---

### AXIOM CONSEQUENCES

**substrate\_ultimate\_ground :**
$\forall e. \text{is\_ presentation}(e) \rightarrow \exists \text{path.}$
$$\text{path.head} = \text{Substrate} \wedge \text{path.last} = e \wedge$$
$$\forall i. i+1 < \text{path.length} \rightarrow \text{is\_ grounded}(\text{path}[i+1], \text{path}[i])$$

**decoherence\_implies\_classical :**
$\forall e. \text{is\_ presentation}(e) \wedge \neg\text{coherent}(e) \rightarrow$
$$\exists t_0. \forall t > t_0. \neg\text{is\_ quantum\_ state}(\text{indexed}(e, t))$$

**measurement\_breaks\_coherence :**
$\forall e_q, e_c.$
$$\text{is\_ quantum\_ state}(e_q) \wedge \text{coherent}(e_q) \wedge \text{emergent}(e_c, e_q) \rightarrow \neg\text{coherent}(e_c)$$

**indexed\_preserves\_presentation :**
$\forall e, t. \text{is\_ presentation}(e) \rightarrow \text{is\_ presentation}(\text{indexed}(e, t))$

---

### BRIDGE AXIOMS

#### BRIDGE1 (Pointwise Convergence)
$\forall e, \epsilon > 0.$
$$\text{is\_ presentation}(e) \rightarrow \exists p_0. \forall p \geq p_0. |C(e, p) - K(e)| < \epsilon$$

#### BRIDGE2 (Uniform Convergence)
$\forall S, \epsilon > 0. (\forall e \in S. \text{is\_ presentation}(e)) \rightarrow$
$$\exists p_0. \forall p \geq p_0, e \in S. |C(e, p) - K(e)| < \epsilon$$

#### BRIDGE3 (Probability Convergence)
$\forall S, \epsilon > 0. (\forall e \in S. \text{is\_ presentation}(e)) \wedge \text{Z\_ ideal}(S) > 0 \rightarrow$
$$\exists p_0. \forall p \geq p_0. \frac{|\text{Z\_ op}(S, p) - \text{Z\_ ideal}(S)|}{\text{Z\_ ideal}(S)} < \epsilon$$

#### BRIDGE4 (Grounding Convergence)
$\forall S, \epsilon > 0, e_1, e_2. e_1, e_2 \in S \wedge \text{is\_ presentation}(e_1) \wedge \text{is\_ presentation}(e_2) \rightarrow$
$$\exists p_0. \forall p \geq p_0. \text{grounds\_ K}(e_1, e_2) \leftrightarrow \text{grounds\_ C}(e_1, e_2, p)$$
**where:**
$$\text{grounds\_ K}(e_1, e_2) := \text{K\_ cond}(e_1, e_2) < K(e_2) - K(e_1) + \text{c\_ grounding}$$
$$\text{grounds\_ C}(e_1, e_2, p) := \text{C\_ cond}(e_1, e_2, p) < C(e_2, p) - C(e_1, p) + \text{c\_ grounding}$$

#### BRIDGE5 (Rank Stability)
$\forall S, e.$
$$e \in S \wedge \text{is\_ presentation}(e) \rightarrow \exists p_0. \forall p \geq p_0. \text{rank\_ C}(e, p) = \text{rank\_ K}(e)$$

#### BRIDGE6 (Temporal Continuity)
$\forall e, \text{times}, \epsilon > 0. \text{is\_ temporal\_ presentation}(e) \rightarrow$
$$\exists p_0. \forall p \geq p_0, t \in \text{times}. |\text{Coh\_ op}([e], [t], p) - \text{Coh}([e], [t])| < \epsilon$$

#### BRIDGE7 (Conditional Convergence)
$\forall e_1, e_2, \epsilon > 0. \text{is\_ presentation}(e_1) \wedge \text{is\_ presentation}(e_2) \rightarrow$
$$\exists p_0. \forall p \geq p_0. |\text{C\_ cond}(e_1, e_2, p) - \text{K\_ cond}(e_1, e_2)| < \epsilon$$

#### BRIDGE7_joint (Joint Convergence)
$\forall es, \epsilon > 0. (\forall e \in es. \text{is\_ presentation}(e)) \rightarrow$
$$\exists p_0. \forall p \geq p_0. |\text{C\_ joint}(es, p) - \text{K\_ joint}(es)| < \epsilon$$

#### BRIDGE8 (Continuum Limit)
$\forall e, \text{times}, \epsilon > 0. \text{is\_ temporal\_ presentation}(e) \rightarrow$
$$\exists p_0, \delta. \delta > 0 \wedge \forall p \geq p_0, t \in \text{times}.$$
$$\left| \frac{\text{Coh\_ op}([e], [t+\delta], p) - \text{Coh\_ op}([e], [t], p)}{\delta} - \text{dCoh\_ dt}(e, t) \right| < \epsilon$$

---

### CA RULES

$F : \text{KLZ.State} \rightarrow \text{KLZ.State}$ (noncomputable)
$\text{merge} : \text{KLZ.State} \rightarrow \text{KLZ.State} \rightarrow \text{KLZ.State}$ (noncomputable)

$\text{R\_ Cohesion} : \text{List KLZ.State} \rightarrow \text{KLZ.State} \rightarrow \text{KLZ.State}$ (noncomputable axiom)
$$\text{R\_ Cohesion}(n, h) := \text{merge}(F(\text{join}(n)), h)$$

$\text{R\_ Reduction} : \text{List KLZ.State} \rightarrow \text{KLZ.State}$
$$\text{R\_ Reduction}(n) := \text{mode}(\text{join}(n))$$

$\text{R\_ G1} : \text{List KLZ.State} \rightarrow \text{KLZ.State} \rightarrow \text{KLZ.State}$
$$\text{R\_ G1}(n, h) := \begin{cases} \text{R\_ Cohesion}(n, h) & \text{if } \text{K\_ LZ}(\text{join}(n)) \leq \text{c\_ grounding} \\ \text{R\_ Reduction}(n) & \text{otherwise} \end{cases}$$

$\text{coherent\_ state} : \text{KLZ.State} \rightarrow \text{Prop}$
$$\text{coherent\_ state}(s) := \text{K\_ LZ}(s) \leq \text{c\_ grounding}$$

---

### CA PRESERVATION THEOREMS

#### P3 (C6 Preservation)
$\forall n, h.$
$$\text{coherent\_ state}(\text{join}(n)) \rightarrow \text{K\_ LZ}(\text{R\_ G1}(n, h)) = \text{K\_ LZ}(h)$$

**R\_G1\_grounding\_reduction**
$\forall n, h. \text{K\_ LZ}(\text{join}(n)) > \text{c\_ grounding} \rightarrow$
$$\text{K\_ LZ}(\text{R\_ G1}(n, h)) < \text{K\_ LZ}(\text{join}(n)) + \text{c\_ grounding}$$

**R\_G1\_preserves\_time\_arrow**
$\forall \text{hist}, n, h.$
$$\text{K\_ LZ}(\text{join}(\text{R\_ G1}(n, h)::\text{hist})) \leq \text{K\_ LZ}(\text{join}(\text{hist})) + \text{c\_ time}$$
$$\text{where } \text{c\_ time} := \max(\text{c\_ time\_ reduction}, \text{c\_ time\_ cohesion})$$

---

### FUNDAMENTAL THEOREMS

#### E_K (Energy-Complexity Equivalence)
$\forall e.$
$$\text{is\_ presentation}(e) \rightarrow$$
$$(\text{has\_ mass}(e) \rightarrow \exists \Delta > 0. K(e) = K(\Omega) + \Delta) \wedge$$
$$\text{energy\_ of}(e) = \kappa_{energy} \cdot K(e)$$

#### G_Ψ (Grounding Stability)
$\forall e.$
$$\text{stable}(e) \leftrightarrow \text{K\_ cond}(\Omega, e) > \text{c\_ grounding}$$
$$\text{where } \text{stable}(e) := \text{is\_ presentation}(e) \wedge \text{K\_ cond}(\Omega, e) > \text{c\_ grounding}$$

#### B_Ω (Holographic Bound)
$\forall \text{region, Area.}$
$$\text{is\_ presentation}(\text{region}) \wedge \text{Area} > 0 \rightarrow K(\text{region}) \leq \frac{\text{Area}}{4\ell_{Planck}^2}$$

#### Ψ_I (Coherence Invariant)
$\forall e.$
$$\text{is\_ temporal\_ presentation}(e) \wedge \text{coherent}(e) \rightarrow \text{Coh\_ trajectory}(e) \cdot \text{P\_ total}(e) = 1$$

#### U_Ω (Uncertainty Principle)
$\forall e, \Delta K, \Delta t.$
$$\text{is\_ temporal\_ presentation}(e) \wedge \Delta K > 0 \wedge \Delta t > 0 \rightarrow \Delta K \cdot \Delta t \geq \hbar_{eff}$$

---

### RANK SYSTEM

$\text{rank\_ K}(\Omega) = 0$
$\text{grounds}(e_1, e_2) \rightarrow \text{rank\_ K}(e_2) < \text{rank\_ K}(e_1)$
$\forall e. \exists n. \text{rank\_ K}(e) = n$

$\text{rank\_ C}(e, p) = \text{bfs\_ depth\_ C}(e, p, S) \text{ for } e \in S$

---

### UNIVERSAL GROUNDING

$\forall e. \text{is\_ presentation}(e) \rightarrow \exists \text{path.}$
$$\text{path.head} = \Omega \wedge \text{path.last} = e \wedge$$
$$\forall i. i+1 < \text{path.length} \rightarrow \text{grounds}(\text{path}[i], \text{path}[i+1])$$

**grounding\_transitive :**
$\forall e_1, e_2, e_3.$
$$\text{grounds}(e_1, e_2) \wedge \text{grounds}(e_2, e_3) \rightarrow \text{grounds}(e_1, e_3)$$

**grounding\_acyclic :**
$\forall e. \neg\text{grounds}(e, e)$

---

### COMPLEXITY BOUNDS

$\text{K\_ joint\_ nonneg} : \forall es. 0 \leq \text{K\_ joint}(es)$
$\text{K\_ joint\_ nil} : \text{K\_ joint}([]) = 0$
$\text{K\_ joint\_ singleton} : \forall e. \text{K\_ joint}([e]) = K(e)$

**compression\_axiom :**
$\forall es. (\forall e \in es. \text{is\_ presentation}(e)) \wedge es.\text{length} \geq 2 \rightarrow$
$$\text{K\_ joint}(es) < \text{K\_ sum}(es)$$

**joint\_le\_sum :**
$\forall es. (\forall e \in es. \text{is\_ presentation}(e)) \rightarrow \text{K\_ joint}(es) \leq \text{K\_ sum}(es)$

**complexity\_positive :**
$\forall e. \text{is\_ presentation}(e) \rightarrow 0 < K(e)$

**substrate\_minimal :**
$\forall e. \text{is\_ presentation}(e) \rightarrow K(\text{Substrate}) \leq K(e)$

---

### OPERATIONAL BOUNDS

$\text{C\_ nonneg} : \forall e, p. 0 \leq C(e, p)$
$\text{C\_ monotone} : \forall e, p_1, p_2. p_1 \leq p_2 \rightarrow C(e, p_2) \leq C(e, p_1)$

$\text{C\_ joint\_ nonneg} : \forall es, p. 0 \leq \text{C\_ joint}(es, p)$

$\text{K\_ LZ\_ nonneg} : \forall s. 0 \leq \text{K\_ LZ}(s)$
$\text{K\_ LZ\_ empty} : \text{K\_ LZ}(\text{join}([])) = 0$
$\text{K\_ LZ\_ monotone} : \forall s_1, s_2. s_1.\text{length} \leq s_2.\text{length} \rightarrow \text{K\_ LZ}(s_1) \leq \text{K\_ LZ}(s_2)$

---

### TOY COMPRESSOR BOUNDS

$\text{K\_ toy\_ lower\_ bound} : \forall s. \text{K\_ LZ}(s) \leq \text{K\_ toy}(s)$
$\text{K\_ toy\_ upper\_ bound} : \forall s. \text{K\_ toy}(s) \leq \text{K\_ LZ}(s) + \log_2(s.\text{length})$

---

### KLZ AXIOMS

**K\_LZ\_subadditive\_cons :**
$\forall x, xs. \text{K\_ LZ}(\text{join}(x::xs)) \leq \text{K\_ LZ}(\text{join}(xs)) + \text{K\_ LZ}(x) + \text{c\_ sub}$

**K\_LZ\_prefix :**
$\forall b, s. \text{K\_ LZ}(\text{join}([b])) \leq \text{K\_ LZ}(\text{join}(b::s))$

**K\_LZ\_singleton\_bound :**
$\forall b. \text{K\_ LZ}(\text{join}([b])) \leq \text{c\_ single}$

**K\_LZ\_mode\_le :**
$\forall s. \text{K\_ LZ}(\text{mode}(s)) \leq \text{K\_ LZ}(s) + \text{C\_ mode}$

**K\_LZ\_mode\_absolute\_bound :**
$\forall s. \text{K\_ LZ}(\text{mode}(s)) \leq \text{C\_ mode}$

**C\_mode\_lt\_c\_grounding :**
$\text{C\_ mode} < \text{c\_ grounding}$

**K\_LZ\_cohesion\_bound\_raw :**
$\forall n, h. \text{K\_ LZ}(\text{R\_ Cohesion}(n, h)) \leq \text{C\_ coh}$

---

### TIME ARROW THEOREMS

**time\_arrow\_reduction :**
$\forall \text{hist}, n.$
$$\text{K\_ LZ}(\text{join}(\text{mode}(\text{join}(n)) :: \text{hist})) \leq \text{K\_ LZ}(\text{join}(\text{hist})) + \text{c\_ time\_ reduction}$$

**time\_arrow\_cohesion :**
$\forall \text{hist}, n, h.$
$$\text{K\_ LZ}(\text{join}(\text{R\_ Cohesion}(n, h) :: \text{hist})) \leq \text{K\_ LZ}(\text{join}(\text{hist})) + \text{c\_ time\_ cohesion}$$

---

### COHERENCE BOUNDS

**coherence\_bounds :**
$\forall es, \text{times}.$
$$(\forall e \in es. \text{is\_ presentation}(e)) \rightarrow 0 \leq \text{Coh}(es, \text{times}) \wedge \text{Coh}(es, \text{times}) \leq 1$$

**compression\_ratio\_ge\_one :**
$\forall es, \text{times}.$
$$(\forall e \in es. \text{is\_ presentation}(e)) \rightarrow 1 \leq \text{compression\_ ratio}(es, \text{times})$$

---

### ERROR BOUNDS

**error\_bound\_linear :**
$\exists c > 0. \forall e, p. \text{is\_ presentation}(e) \rightarrow 0 < p \rightarrow$
$$|C(e, p) - K(e)| \leq c/p$$

**error\_bound\_polynomial :**
$\exists c, \alpha. 0 < c \wedge 1 < \alpha \wedge \forall e, p. \text{is\_ presentation}(e) \rightarrow 0 < p \rightarrow$
$$|C(e, p) - K(e)| \leq c/p^\alpha$$

**error\_bound\_general :**
$\exists M > 0. \forall e, p. \text{is\_ presentation}(e) \rightarrow$
$$|C(e, p) - K(e)| \leq M/(p+1)$$

---

### PHYSICS CORRESPONDENCES

$\text{energy\_ of}(e) = \kappa_{energy} \cdot K(e)$
$\text{mass}(e) = \text{energy\_ of}(e)/c^2$
$\text{entropy}(e) = k_B \cdot \log(2) \cdot K(e)$

$\text{is\_ quantum}(\text{nbhd}) := \text{K\_ LZ}(\text{join}(\text{nbhd})) \leq \text{c\_ grounding}$
$\text{is\_ classical}(\text{nbhd}) := \text{K\_ LZ}(\text{join}(\text{nbhd})) > \text{c\_ grounding}$

---

### PREDICATES

$\text{is\_ substrate} : \text{Entity} \rightarrow \text{Prop}$ (axiom)
$\text{is\_ presentation} : \text{Entity} \rightarrow \text{Prop}$ (axiom)
$\text{is\_ emergent} : \text{Entity} \rightarrow \text{Prop}$ (axiom)
$\text{is\_ temporal\_ presentation} : \text{Entity} \rightarrow \text{Prop}$ (axiom)
$\text{is\_ static\_ presentation} : \text{Entity} \rightarrow \text{Prop}$ (axiom)
$\text{is\_ quantum\_ state} : \text{Entity} \rightarrow \text{Prop}$ (axiom)
$\text{is\_ measurement\_ device} : \text{Entity} \rightarrow \text{Prop}$ (axiom)
$\text{is\_ observable} : \text{Entity} \rightarrow \text{Prop}$ (axiom)

$\text{phenomenal} : \text{Entity} \rightarrow \text{Prop}$ (axiom)
$\text{has\_ mass} : \text{Entity} \rightarrow \text{Prop}$ (axiom)

$\text{grounds} : \text{Entity} \rightarrow \text{Entity} \rightarrow \text{Prop}$ (axiom)
$\text{temporal\_ grounds} : \text{Entity} \rightarrow \text{Time} \rightarrow \text{Entity} \rightarrow \text{Time} \rightarrow \text{Prop}$ (axiom)
$\text{interacts} : \text{Entity} \rightarrow \text{Entity} \rightarrow \text{Prop}$ (axiom)
$\text{inseparable} : \text{Entity} \rightarrow \text{Entity} \rightarrow \text{Prop}$ (axiom)
$\text{emerges\_ from} : \text{Entity} \rightarrow \text{List Entity} \rightarrow \text{Prop}$ (axiom)
$\text{phase\_ coupled} : \text{Entity} \rightarrow \text{Entity} \rightarrow \text{Phase} \rightarrow \text{Prop}$ (axiom)

$\text{coherent} : \text{Entity} \rightarrow \text{Prop}$
$\text{decoherent} : \text{Entity} \rightarrow \text{Prop}$
$\text{stable} : \text{Entity} \rightarrow \text{Prop}$

$\text{is\_ quantum} : \text{List State} \rightarrow \text{Prop}$
$\text{is\_ classical} : \text{List State} \rightarrow \text{Prop}$
$\text{coherent\_ state} : \text{KLZ.State} \rightarrow \text{Prop}$

$\text{is\_ grounded} : \text{Entity} \rightarrow \text{Entity} \rightarrow \text{Prop}$

---

### ENTITY CLASSIFICATION

**entity\_classification :**
$\forall e. (\text{is\_ substrate}(e) \wedge e = \text{Substrate}) \vee \text{is\_ presentation}(e) \vee \text{is\_ emergent}(e)$

$\text{substrate\_ not\_ presentation} : \forall e. \neg(\text{is\_ substrate}(e) \wedge \text{is\_ presentation}(e))$
$\text{substrate\_ not\_ emergent} : \forall e. \neg(\text{is\_ substrate}(e) \wedge \text{is\_ emergent}(e))$
$\text{presentation\_ not\_ emergent} : \forall e. \neg(\text{is\_ presentation}(e) \wedge \text{is\_ emergent}(e))$

**presentation\_temporal\_or\_static :**
$\forall e. \text{is\_ presentation}(e) \rightarrow$
$$(\text{is\_ temporal\_ presentation}(e) \vee \text{is\_ static\_ presentation}(e)) \wedge$$
$$\neg(\text{is\_ temporal\_ presentation}(e) \wedge \text{is\_ static\_ presentation}(e))$$

---

### SUBSTRATE PROPERTIES

$\text{substrate\_ unique} : \forall x, y. \text{is\_ substrate}(x) \wedge \text{is\_ substrate}(y) \rightarrow x = y$
$\text{substrate\_ is\_ Substrate} : \text{is\_ substrate}(\text{Substrate})$
$\text{Omega\_ is\_ substrate} : \text{is\_ substrate}(\Omega)$
$\text{Omega\_ eq\_ Substrate} : \Omega = \text{Substrate}$

---

### TEMPORAL PRESERVATION

**indexed\_preserves\_presentation :**
$\forall e, t. \text{is\_ presentation}(e) \rightarrow \text{is\_ presentation}(\text{indexed}(e, t))$

**temporal\_slice\_preserves\_presentation :**
$\forall es, t. (\forall e \in es. \text{is\_ presentation}(e)) \rightarrow$
$$(\forall e \in \text{temporal\_ slice}(es, t). \text{is\_ presentation}(e))$$

---

### ASSOCIATIVITY

**join\_associative :**
$\forall s_1, s_2, s_3. \text{join}([\text{join}([s_1, s_2]), s_3]) = \text{join}([s_1, \text{join}([s_2, s_3])])$

---

### VERIFIED THEOREMS

**energy\_from\_complexity :**
$\forall e. \text{is\_ presentation}(e) \rightarrow \text{has\_ mass}(e) \rightarrow$
$$\exists m > 0. m = \text{energy\_ of}(e)/c^2$$

**entropy\_from\_complexity :**
$\forall e. \text{is\_ presentation}(e) \rightarrow \exists S.$
$$S = k_B \cdot \log(2) \cdot K(e)$$

**coherence\_participation\_invariant :**
$\forall e. \text{is\_ temporal\_ presentation}(e) \rightarrow \text{coherent}(e) \rightarrow$
$$0 < \text{P\_ total}(e) \wedge \text{Coh\_ trajectory}(e) = 1/\text{P\_ total}(e)$$

**joint\_le\_sum :**
$\forall es. (\forall e \in es. \text{is\_ presentation}(e)) \rightarrow \text{K\_ joint}(es) \leq \text{K\_ sum}(es)$

**complexity\_subadditive :**
$\forall e_1, e_2. \text{is\_ presentation}(e_1) \rightarrow \text{is\_ presentation}(e_2) \rightarrow$
$$\text{K\_ joint}([e_1, e_2]) \leq K(e_1) + K(e_2)$$

**compression\_ratio\_ge\_one :**
$\forall es, \text{times}. (\forall e \in es. \text{is\_ presentation}(e)) \rightarrow$
$$1 \leq \text{Compression\_ ratio}(es, \text{times})$$

**R\_G1\_preserves\_grounding :**
$\forall n. \text{K\_ LZ}(\text{mode}(\text{join}(n))) < \text{K\_ LZ}(\text{join}(n)) + \text{c\_ grounding}$

**time\_arrow\_reduction :**
$\forall \text{hist}, n. \text{K\_ LZ}(\text{join}(\text{mode}(\text{join}(n))::\text{hist})) \leq \text{K\_ LZ}(\text{join}(\text{hist})) + \text{c\_ time\_ reduction}$

**time\_arrow\_cohesion :**
$\forall \text{hist}, n, h. \text{K\_ LZ}(\text{join}(\text{R\_ Cohesion}(n, h)::\text{hist})) \leq \text{K\_ LZ}(\text{join}(\text{hist})) + \text{c\_ time\_ cohesion}$

**P3\_C6\_preservation :**
$\forall n, h. \text{coherent\_ state}(\text{join}(n)) \rightarrow \text{K\_ LZ}(\text{R\_ G1}(n, h)) = \text{K\_ LZ}(h)$

**R\_G1\_grounding\_reduction :**
$\forall n, h. \text{K\_ LZ}(\text{join}(n)) > \text{c\_ grounding} \rightarrow$
$$\text{K\_ LZ}(\text{R\_ G1}(n, h)) < \text{K\_ LZ}(\text{join}(n)) + \text{c\_ grounding}$$

**R\_G1\_preserves\_time\_arrow :**
$\forall \text{hist}, n, h.$
$$\text{K\_ LZ}(\text{join}(\text{R\_ G1}(n, h)::\text{hist})) \leq \text{K\_ LZ}(\text{join}(\text{Lz}(\text{hist})) + \max(\text{c\_ time\_ reduction}, \text{c\_ time\_ cohesion})$$

**planck\_units\_positive :**
$0 < \ell_{Planck} \wedge 0 < t_{Planck} \wedge 0 < M_{Planck} \wedge 0 < E_{Planck} \wedge 0 < T_{Planck}$

**error\_bound\_exists :**
$\forall e, p. \text{is\_ presentation}(e) \rightarrow \exists \epsilon. |C(e, p) - K(e)| \leq \epsilon.\text{absolute}$