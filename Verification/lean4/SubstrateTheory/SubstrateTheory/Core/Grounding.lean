
import SubstrateTheory.Core.Types
import SubstrateTheory.Core.Parameters
import SubstrateTheory.Core.Axioms
import SubstrateTheory.Ideal.Complexity
import SubstrateTheory.Operational.Complexity
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

/-!
# Grounding

This module provides rank axioms for grounding and a few utility lemmas for
finset cardinality and intersections that are commonly needed in BFS-style
constructions for grounding paths.

It also includes axioms you referenced (`rank_K`, `rank_C_def`, `universal_grounding`),
so this file can stand alone while you wire other modules.
-/

namespace SubstrateTheory.Core

open SubstrateTheory SubstrateTheory.Ideal SubstrateTheory.Operational

noncomputable axiom rank_K : Entity → ℕ
axiom rank_K_substrate : rank_K Ω = 0
axiom rank_K_grounding : ∀ e₁ e₂, grounds e₁ e₂ → rank_K e₂ < rank_K e₁
axiom rank_K_exists : ∀ e, ∃ n, rank_K e = n

/-- (Optional) A computable rank used in operational search proofs. -/
noncomputable axiom rank_C : Entity → ℕ → ℕ

/-- An abstracted BFS depth for the operational layer (you can hook your real BFS here). -/
noncomputable axiom bfs_depth_C : Entity → ℕ → Finset Entity → ℕ

/-- Placeholder for a BFS path extractor; refine as needed. -/
noncomputable def bfs_grounding_path (_e : Entity) (_S : Finset Entity) (_p : ℕ) : Option (List Entity) :=
  none

/-- Connect the computable rank to a BFS depth (your original assumption). -/
axiom rank_C_def : ∀ e p S,
  e ∈ S → rank_C e p = bfs_depth_C e p S

/-- Universal grounding axiom giving a path from Ω to any presentation. -/
axiom universal_grounding : ∀ e,
  is_presentation e →
  ∃ path : List Entity,
    path.head? = some Ω ∧
    path.getLast? = some e ∧
    ∀ i : ℕ, ∀ h1 : i < path.length, ∀ h2 : i + 1 < path.length,
      grounds path[i] path[i+1]

/-! ## Finset helpers

These lemmas address the two concrete errors you reported:

1. Upgrading `card ≤` to `card <` by supplying `visited ⊂ S` (proper subset).
2. Avoiding the misuse of a Set-lemma shape like `inter_subset_right` on Finsets,
   by just writing the inclusion proof directly.
-/

section FinsetHelpers
variable {α : Type*} [DecidableEq α]

/-- Strict card inequality from subset + inequality of sets. -/
lemma card_lt_of_subset_ne {A B : Finset α}
    (hsub : A ⊆ B) (hne : A ≠ B) : A.card < B.card := by
  have hss : A ⊂ B := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
  simpa using Finset.card_lt_card hss

/-- If there exists an element in `B` not in `A`, then `A.card < B.card`. -/
lemma card_lt_of_subset_exists_not_mem {A B : Finset α}
    (hsub : A ⊆ B) (h : ∃ x ∈ B, x ∉ A) : A.card < B.card := by
  rcases h with ⟨x, hxB, hxA⟩
  have hne : A ≠ B := by
    intro hEq
    have : x ∈ A := by simpa [hEq] using hxB
    exact hxA this
  exact card_lt_of_subset_ne hsub hne

/-- Right projection of a Finset intersection is a subset. -/
lemma inter_subset_right (A B : Finset α) : A ∩ B ⊆ B := by
  intro x hx
  exact (Finset.mem_inter.mp hx).2

/-- Left projection of a Finset intersection is a subset. -/
lemma inter_subset_left (A B : Finset α) : A ∩ B ⊆ A := by
  intro x hx
  exact (Finset.mem_inter.mp hx).1

end FinsetHelpers

/-! ## Example: Typical BFS step facts

These small lemmas show how to use the helpers above in common patterns.
Replace names/variables as needed in your file.
-/
section Examples
variable {Entity : Type} [DecidableEq Entity]

-- We keep `Entity` abstract in examples to avoid clashing with your core `Entity`.
-- If you prefer, delete this section once you've patched your real proofs.

/--
If `visited ⊆ S` and there is some element of `S` not yet in `visited`,
then `visited.card < S.card`.
-/
lemma visited_card_lt_of_room
  (visited S : Finset Entity)
  (hsub : visited ⊆ S)
  (hroom : ∃ x ∈ S, x ∉ visited) :
  visited.card < S.card :=
card_lt_of_subset_exists_not_mem hsub hroom

/--
If `frontier ⊆ S`, then `visited ∩ frontier ⊆ S`.
-/
lemma inter_with_frontier_into_S
  (visited frontier S : Finset Entity)
  (hfrontier : frontier ⊆ S) :
  visited ∩ frontier ⊆ S :=
(inter_subset_right visited frontier).trans hfrontier

end Examples

end SubstrateTheory.Core
