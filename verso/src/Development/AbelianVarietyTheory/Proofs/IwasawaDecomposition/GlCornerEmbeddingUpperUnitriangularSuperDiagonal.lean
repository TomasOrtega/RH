import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CornerUnip

/- English proof (translation)
Rewrite using `[Equiv.symm_apply_eq]`. Use `ext`. Simplify using `[stdSum_inl]`.
-/
theorem corner_symm_castSucc {m : ℕ} (i : Fin m) :
    (stdSum (rfl : m + 1 = m + 1)).symm (Fin.castSucc i) = Sum.inl i := by
  rw [Equiv.symm_apply_eq]; ext; simp [stdSum_inl]

/- English proof (translation)
Rewrite using `[Equiv.symm_apply_eq]`. Use `ext`. Simplify using `[stdSum_inr]`.
-/
theorem corner_symm_last (m : ℕ) :
    (stdSum (rfl : m + 1 = m + 1)).symm (Fin.last m) = Sum.inr 0 := by
  rw [Equiv.symm_apply_eq]; ext; simp [stdSum_inr]

variable {R : Type} [CommRing R] {m : ℕ}

/- English proof (translation)
Simplify using `[corner, val_emb₂, corner_symm_castSucc]`.
-/
theorem corner_cc (u : GL (Fin m) R) (i j : Fin m) :
    (corner u : Matrix (Fin (m+1)) (Fin (m+1)) R) (Fin.castSucc i) (Fin.castSucc j) = (u : Matrix _ _ R) i j := by
  simp [corner, val_emb₂, corner_symm_castSucc]

/- English proof (translation)
Simplify using `[corner, val_emb₂, corner_symm_castSucc, corner_symm_last]`.
-/
theorem corner_cl (u : GL (Fin m) R) (i : Fin m) :
    (corner u : Matrix (Fin (m+1)) (Fin (m+1)) R) (Fin.castSucc i) (Fin.last m) = 0 := by
  simp [corner, val_emb₂, corner_symm_castSucc, corner_symm_last]

/- English proof (translation)
Simplify using `[corner, val_emb₂, corner_symm_castSucc, corner_symm_last]`.
-/
theorem corner_lc (u : GL (Fin m) R) (j : Fin m) :
    (corner u : Matrix (Fin (m+1)) (Fin (m+1)) R) (Fin.last m) (Fin.castSucc j) = 0 := by
  simp [corner, val_emb₂, corner_symm_castSucc, corner_symm_last]

/- English proof (translation)
Simplify using `[corner, val_emb₂, corner_symm_last]`.
-/
theorem corner_ll (u : GL (Fin m) R) :
    (corner u : Matrix (Fin (m+1)) (Fin (m+1)) R) (Fin.last m) (Fin.last m) = 1 := by
  simp [corner, val_emb₂, corner_symm_last]

end GlobalTheory.CornerUnip

open GlobalTheory.CornerUnip in
/- English proof (translation)
Introduce `R _ m u hu`. Rewrite `hu` using `[mem_unipB]`. Take `⟨hl, hd⟩` from `hu`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_unipB]`.

Use `⟨fun i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last`. Proceed by induction on `j using Fin.lastCases with`. Consider the case `last => exact absurd hij (lt_irrefl _)`.

Consider the case `cast j => exact corner_lc u j`. Consider the case `cast i`. Proceed by induction on `j using Fin.lastCases with`. Consider the case `last => exact absurd hij (not_lt.2 (Fin.le_last _))`. Consider the case `cast j`.

Rewrite using `[corner_cc]`. Conclude with `hl i j (Fin.castSucc_lt_castSucc_iff.1 hij)`. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last => exact corner_ll u`. Consider the case `cast i => rw [corner_cc]`.

Conclude with `hd i`. Unfold `superDiag`. Simplify using `only [Finset.sum_filter]`. Simplify using `[Fin.sum_univ_castSucc, corner_cc, corner_cl, corner_lc, corner_ll]`.
-/
theorem GlobalTheory.CornerUnip.corner_unipB_superDiag : ∀ (R : Type) [CommRing R] (m : ℕ) (u : GL (Fin m) R), u ∈ unipB R (Fin m) → corner u ∈ unipB R (Fin (m + 1)) ∧ superDiag (corner u) = superDiag u := by
  intro R _ m u hu
  rw [mem_unipB] at hu
  obtain ⟨hl, hd⟩ := hu
  refine ⟨?_, ?_⟩
  · rw [mem_unipB]
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (lt_irrefl _)
        | cast j => exact corner_lc u j
      | cast i =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (not_lt.2 (Fin.le_last _))
        | cast j =>
          rw [corner_cc]
          exact hl i j (Fin.castSucc_lt_castSucc_iff.1 hij)
    · induction i using Fin.lastCases with
      | last => exact corner_ll u
      | cast i => rw [corner_cc]; exact hd i
  · unfold superDiag
    simp only [Finset.sum_filter]
    simp [Fin.sum_univ_castSucc, corner_cc, corner_cl, corner_lc, corner_ll]
