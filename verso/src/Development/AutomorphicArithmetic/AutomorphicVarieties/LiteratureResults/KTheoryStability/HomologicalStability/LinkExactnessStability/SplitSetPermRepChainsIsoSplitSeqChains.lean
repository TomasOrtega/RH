import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.MemSplitSeqIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KAcyclicHomology

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL

namespace GlobalTheory.HomStab

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
private theorem split_set_boundary_comp_face_sum (R : Type) [CommRing R] (n p : ℕ) :
    (Finsupp.lmapDomain ℤ ℤ (fun x : SplitSet R n p => (x.1 : List ((Fin n → R) × (Fin n → R))))) ∘ₗ
      (∑ i : Fin (p + 1), (-1 : ℤ) ^ (i : ℕ) • Finsupp.lmapDomain ℤ ℤ (face R n p i)) =
    bd _ ∘ₗ Finsupp.lmapDomain ℤ ℤ
      (fun x : SplitSet R n (p + 1) => (x.1 : List ((Fin n → R) × (Fin n → R)))) := by
  apply Finsupp.lhom_ext
  intro l a
  have hlen : l.1.length = p + 1 := l.2.2
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  unfold bd
  rw [Finsupp.linearCombination_single, hlen, Finset.smul_sum]
  rw [← Fin.sum_univ_eq_sum_range (fun i => a • ((-1 : ℤ) ^ i • Finsupp.single (l.1.eraseIdx i) (1 : ℤ)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  show (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (l.1.eraseIdx i) a =
    a • ((-1 : ℤ) ^ (i : ℕ) • Finsupp.single (l.1.eraseIdx i) (1 : ℤ))
  simp [Finsupp.smul_single, mul_comm]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem splitSet_chains_incl : ∀ (R : Type) [CommRing R] (n p : ℕ), Function.Injective (Finsupp.lmapDomain ℤ ℤ (Subtype.val : SplitSet R n p → _)) ∧ LinearMap.range (Finsupp.lmapDomain ℤ ℤ (Subtype.val : SplitSet R n p → _)) = chains (splitSeq R n) p ∧ ∀ c : SplitSet R n (p + 1) →₀ ℤ, Finsupp.mapDomain (Subtype.val : SplitSet R n p → _) ((splitD R n p).hom c) = bd _ (Finsupp.mapDomain (Subtype.val : SplitSet R n (p + 1) → _) c) := by
  intro R _ n p
  have hD : ∀ c : SplitSet R n (p + 1) →₀ ℤ, (splitD R n p).hom c =
      (∑ i : Fin (p + 1), (-1 : ℤ) ^ (i : ℕ) • Finsupp.mapDomain (face R n p i) c : SplitSet R n p →₀ ℤ) := by
    intro c
    simp [splitD, permMap, Rep.sum_hom, Rep.hom_ofHom, Rep.zsmul_hom, Rep.smul_hom,
      Representation.IntertwiningMap.sum_apply, Representation.IntertwiningMap.smul_apply]
  refine ⟨?_, ?_, ?_⟩
  · exact Finsupp.mapDomain_injective Subtype.val_injective
  · rw [LinearMap.range_eq_map, ← Finsupp.supported_univ, Finsupp.lmapDomain_supported, Set.image_univ]
    unfold chains
    congr 1
    ext l
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro hl
      exact ⟨⟨l, hl⟩, rfl⟩
  · intro c
    rw [hD]
    have key := LinearMap.congr_fun (split_set_boundary_comp_face_sum R n p) c
    simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      Finsupp.lmapDomain_apply] at key
    exact key

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL
/- English proof (translation)
Treat this case separately. A detailed English derivation is pending.
-/
theorem _root_.GlobalTheory.T.splitSet_permRep_chains_iso_splitSeq_chains : ∀ (R : Type) [CommRing R] (n p : ℕ), Function.Injective (Finsupp.lmapDomain ℤ ℤ (Subtype.val : SplitSet R n p → _)) ∧ LinearMap.range (Finsupp.lmapDomain ℤ ℤ (Subtype.val : SplitSet R n p → _)) = chains (splitSeq R n) p ∧ ∀ c : SplitSet R n (p + 1) →₀ ℤ, Finsupp.mapDomain (Subtype.val : SplitSet R n p → _) ((splitD R n p).hom c) = bd _ (Finsupp.mapDomain (Subtype.val : SplitSet R n (p + 1) → _) c) := by
  first
  | exact @GlobalTheory.HomStab.splitSet_chains_incl
end
