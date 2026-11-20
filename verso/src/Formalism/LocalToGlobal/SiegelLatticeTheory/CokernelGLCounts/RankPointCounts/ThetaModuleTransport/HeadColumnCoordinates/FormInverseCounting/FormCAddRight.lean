import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.LamSMulVec

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.LocCnt0LAlg

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

/- English proof (translation)
Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Normalize the expressions using the abelian group laws. A detailed English derivation is pending.
-/
theorem mem_relC_of_mk (hO : ∀ x ∈ O, cj x ∈ O) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O)
    (t t' : O) (u u' : Fin (r + 1) → O) (α β : O)
    (h : (Submodule.Quotient.mk u : MbMod Z) = α • bCls Z - (t * β) • eCl Z)
    (h' : (Submodule.Quotient.mk u' : MbMod (cjT O cj hO Z)) =
      β • bCls (cjT O cj hO Z) - (t' * α) • eCl (cjT O cj hO Z)) :
    (Sum.elim u u' : Ix r → O) ∈ relC O cj (Z.map O.subtype) t t' := by
  rw [bCls, eCl, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
    ← Submodule.Quotient.mk_sub, Submodule.Quotient.eq] at h h'
  obtain ⟨w, hw, hwe⟩ := (mem_headCols_iff _ _).1 h
  obtain ⟨v, hv, hve⟩ := (mem_headCols_iff _ _).1 h'
  rw [mem_relC_iff O cj hO Z t t']
  refine ⟨v + β • Pi.single (Fin.last r) 1, w + α • Pi.single (Fin.last r) 1, ?_, ?_⟩
  · have hl : ((v + β • Pi.single (Fin.last r) 1 : Fin (r + 1) → O)) (Fin.last r) = β := by simp [hv]
    rw [hl, Matrix.mulVec_add, Matrix.mulVec_smul, ← bvec_eq, ← hwe]
    show u = _
    abel
  · have hl : ((w + α • Pi.single (Fin.last r) 1 : Fin (r + 1) → O)) (Fin.last r) = α := by simp [hw]
    rw [hl, Matrix.mulVec_add, Matrix.mulVec_smul, ← bvec_eq, ← hve]
    show u' = _
    abel

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem mem_relC_of_K (hO : ∀ x ∈ O, cj x ∈ O) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O)
    (t t' : O) (u u' : Fin (r + 1) → O) (hu : u ∈ headCols Z) (hu' : u' ∈ headCols (cjT O cj hO Z)) :
    (Sum.elim u u' : Ix r → O) ∈ relC O cj (Z.map O.subtype) t t' := by
  apply mem_relC_of_mk O cj hO Z t t' u u' 0 0
  · rw [(Submodule.Quotient.mk_eq_zero _).2 hu]; simp
  · rw [(Submodule.Quotient.mk_eq_zero _).2 hu']; simp

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules.
-/
theorem gramC_herm (hcj : ∀ x, cj (cj x) = x) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E)
    (hT : cj T = T) (hT' : cj T' = T') (k j : Ix r) :
    cj (gramC cj Z T T' k j) = gramC cj Z T T' j k := by
  rcases k with a | a <;> rcases j with b | b <;>
    simp [gramC, hcj, apply_ite cj, hT, hT', and_comm]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem formC_add_left (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) (Y Y' W : Ix r → O) :
    formC O cj Z T T' (Y + Y') W = formC O cj Z T T' Y W + formC O cj Z T T' Y' W := by
  simp [formC, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem formC_add_right (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) (Y W W' : Ix r → O) :
    formC O cj Z T T' Y (W + W') = formC O cj Z T T' Y W + formC O cj Z T T' Y W' := by
  simp [formC, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem formC_sub_left (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) (Y Y' W : Ix r → O) :
    formC O cj Z T T' (Y - Y') W = formC O cj Z T T' Y W - formC O cj Z T T' Y' W := by
  have := formC_add_left O cj Z T T' (Y - Y') Y' W
  rw [sub_add_cancel] at this
  rw [this]; ring

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem formC_sub_right (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) (Y W W' : Ix r → O) :
    formC O cj Z T T' Y (W - W') = formC O cj Z T T' Y W - formC O cj Z T T' Y W' := by
  have := formC_add_right O cj Z T T' Y (W - W') W'
  rw [sub_add_cancel] at this
  rw [this]; ring

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem formC_rel_left (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E)
    (hG : IsUnit (gramC cj Z T T').det) (hO : ∀ x ∈ O, cj x ∈ O) (Y W : Ix r → O)
    (hY : Y ∈ relC O cj Z T T') : formC O cj Z T T' Y W ∈ O := by
  obtain ⟨c, hc⟩ := hY
  rw [formC_of_rel O cj Z T T' hG Y W (fun i => (c i : E)) hc]
  exact O.sum_mem fun j _ => O.mul_mem (c j).2 (hO _ (W j).2)

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem formC_rel_right (hcj : ∀ x, cj (cj x) = x) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E)
    (hT : cj T = T) (hT' : cj T' = T')
    (hG : IsUnit (gramC cj Z T T').det) (hO : ∀ x ∈ O, cj x ∈ O) (Y W : Ix r → O)
    (hW : W ∈ relC O cj Z T T') : formC O cj Z T T' Y W ∈ O := by
  obtain ⟨d, hd⟩ := hW
  have hinv := Matrix.nonsing_inv_mul (gramC cj Z T T') hG
  have key : ∀ i, ∑ j, (gramC cj Z T T')⁻¹ i j * cj (W j : E) = cj (d i : E) := by
    intro i
    have h1 : ∀ j, cj (W j : E) = ∑ k, cj (d k : E) * gramC cj Z T T' j k := by
      intro j
      rw [hd j, map_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [map_mul, gramC_herm cj hcj Z T T' hT hT']
    simp only [h1, Finset.mul_sum]
    rw [Finset.sum_comm]
    have h2 : ∀ k, ∑ j, (gramC cj Z T T')⁻¹ i j * (cj (d k : E) * gramC cj Z T T' j k) =
        cj (d k : E) * ((gramC cj Z T T')⁻¹ * gramC cj Z T T') i k := by
      intro k
      rw [Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [h2, hinv, Matrix.one_apply]
    simp
  unfold formC
  have h3 : ∀ i, ∑ j, (Y i : E) * (gramC cj Z T T')⁻¹ i j * cj (W j : E) = (Y i : E) * cj (d i : E) := by
    intro i
    rw [← key i, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [h3]
  exact O.sum_mem fun i _ => O.mul_mem (Y i).2 (hO _ (d i).2)

end Formalism.L2.SG.LocalCountModules.LocCnt0LAlg
