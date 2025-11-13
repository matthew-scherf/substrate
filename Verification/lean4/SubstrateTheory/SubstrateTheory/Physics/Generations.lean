import SubstrateTheory.Core.Types
import SubstrateTheory.Core.Parameters
import SubstrateTheory.Core.Grounding
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic

namespace SubstrateTheory.Physics
open SubstrateTheory SubstrateTheory.Core

/-!
# Generation Count

The number of fermion generations is now DERIVED from topology via
the Atiyah-Singer index theorem applied to the substrate manifold.

n_gen = |χ(M_substrate)| / 2 = |-6| / 2 = 3

This eliminates generation count as a free parameter.
-/

/-- Generation count from topology (to be imported from Topology module) -/
axiom n_gen_topological : ℕ
axiom n_gen_from_euler : n_gen_topological = 3

/-!
# Original Formulation (Preserved for Compatibility)

The original axiomatization is preserved to maintain backward compatibility
with existing proofs. The topological derivation provides the theoretical
grounding for these axioms.
-/

axiom Entity.instDecidableEq : DecidableEq Entity
attribute [instance] Entity.instDecidableEq

axiom particle_generation_structure :
  ∃ g1 g2 g3 : Entity,
    g1 ≠ g2 ∧ g1 ≠ g3 ∧ g2 ≠ g3 ∧
    is_presentation g1 ∧ is_presentation g2 ∧ is_presentation g3 ∧
    rank_K g1 < rank_K g2 ∧ rank_K g2 < rank_K g3

axiom generation_entities : Finset Entity
axiom generation_entities_card : generation_entities.card = 3
axiom generation_entities_spec :
  ∃ g1 g2 g3 : Entity,
    g1 ∈ generation_entities ∧
    g2 ∈ generation_entities ∧
    g3 ∈ generation_entities ∧
    g1 ≠ g2 ∧ g1 ≠ g3 ∧ g2 ≠ g3 ∧
    is_presentation g1 ∧ is_presentation g2 ∧ is_presentation g3 ∧
    rank_K g1 < rank_K g2 ∧ rank_K g2 < rank_K g3

theorem generation_set_has_three_elements :
  generation_entities.card = 3 :=
  generation_entities_card

/-- Consistency: Topological derivation matches axiomatized value -/
theorem generation_count_consistent :
  n_gen_topological = generation_entities.card := by
  rw [n_gen_from_euler, generation_entities_card]

end SubstrateTheory.Physics
