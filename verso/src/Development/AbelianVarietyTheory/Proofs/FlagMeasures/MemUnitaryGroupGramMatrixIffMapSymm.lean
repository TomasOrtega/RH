import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnWittFrameBasisBlockGramStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryStabiliserOrthogonalSummand
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.InclusionInjective
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.Transfer

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St

/- English proof (translation)
Use `haveI := D.host.isCMField_hostE`. Apply `D.host.φ₀.injective` to reduce the goal to its premises. Establish `h1 : D.host.φ₀ (star x) = starRingEnd ℂ (D.host.φ₀ x)` using `NumberField.IsCMField.complexEmbedding_complexConj (K := D.host.E) (φ := D.host.φ₀) (x := x)`. Establish `h2 : D.host.φ₀ (D.host.conj x) = starRingEnd ℂ (D.host.φ₀ x)`. Rewrite using `[← D.embE_φ₀, RingHom.comp_apply, RingHom.comp_apply, D.embE_conj, D.starLL_cx]`.

Rewrite using `[h1, h2]`.
-/
private theorem host_star_eq_conj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  haveI := D.host.isCMField_hostE
  apply D.host.φ₀.injective
  have h1 : D.host.φ₀ (star x) = starRingEnd ℂ (D.host.φ₀ x) :=
    NumberField.IsCMField.complexEmbedding_complexConj (K := D.host.E) (φ := D.host.φ₀) (x := x)
  have h2 : D.host.φ₀ (D.host.conj x) = starRingEnd ℂ (D.host.φ₀ x) := by
    rw [← D.embE_φ₀, RingHom.comp_apply, RingHom.comp_apply, D.embE_conj, D.starLL_cx]
  rw [h1, h2]

/- English proof (translation)
Introduce `D X g`. Establish `hc : ∀ y : D.host.E, X.ιE.symm ((Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) y) = starRingEnd X.B.I.E (X.ιE.symm y)`. Introduce `y`. Apply `X.ιE.injective` to reduce the goal to its premises. Rewrite using `[starRingEnd_apply, X.ιE_conj, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]`.

Conclude with `host_star_eq_conj D y`. Establish `hm : ∀ A B : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E, (A * B).map X.ιE.symm = A.map X.ιE.symm * B.map X.ιE.symm`. Introduce `A B`. Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, map_sum]`.

Establish `hb : ∀ A : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E, (A.map X.ιE.symm).map (starRingEnd X.B.I.E) = (A.map (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E)).map X.ιE.symm`. Introduce `A`. Use extensionality with `i j`. Conclude with `(hc (A i j)).symm`. Establish `hT : ∀ A : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E, Formalism.UG.cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) A = (A.map (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E))ᵀ`.

Introduce `A`. Unfold `Formalism.UG.cT`. Use `first`. Consider the case `rfl`. Consider the case `(ext i j; rfl)`.

Establish `hinj : Function.Injective (fun A : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E => A.map X.ιE.symm)` using `Matrix.map_injective X.ιE.symm.injective`. Use `Iff.trans (Iff.rfl : _ ↔ Formalism.UG.cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) * Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) * (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) = Formalism.L2.Forms.gramN D 0 …` and prove the remaining obligations. Rewrite using `[hT, hb, ← Matrix.transpose_map (f := ⇑X.ιE.symm), ← hm, ← hm]`. Conclude with `hinj.eq_iff.symm`.
-/
theorem mem_UJ_gramN_iff_map_symm : ∀ (D : D7) (X : HidaSetting D) (g : GL (Fin (D.R.N 0)) D.host.E), g ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) ↔ (((g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map X.ιE.symm).map (starRingEnd X.B.I.E))ᵀ * (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm * (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map X.ιE.symm = (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm := by
  intro D X g

  have hc : ∀ y : D.host.E, X.ιE.symm ((Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) y) =
      starRingEnd X.B.I.E (X.ιE.symm y) := by
    intro y
    apply X.ιE.injective
    rw [starRingEnd_apply, X.ιE_conj, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    exact host_star_eq_conj D y
  have hm : ∀ A B : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E,
      (A * B).map X.ιE.symm = A.map X.ιE.symm * B.map X.ιE.symm := by
    intro A B
    ext i j
    simp [Matrix.mul_apply, map_sum]
  have hb : ∀ A : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E,
      (A.map X.ιE.symm).map (starRingEnd X.B.I.E) =
        (A.map (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E)).map X.ιE.symm := by
    intro A
    ext i j
    exact (hc (A i j)).symm
  have hT : ∀ A : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E,
      Formalism.UG.cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) A =
        (A.map (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E))ᵀ := by
    intro A
    unfold Formalism.UG.cT
    first
      | rfl
      | (ext i j; rfl)
  have hinj : Function.Injective
      (fun A : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E => A.map X.ιE.symm) :=
    Matrix.map_injective X.ιE.symm.injective
  refine Iff.trans (Iff.rfl : _ ↔ Formalism.UG.cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E)
      (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) * Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) *
      (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) = Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) ?_
  rw [hT, hb, ← Matrix.transpose_map (f := ⇑X.ιE.symm), ← hm, ← hm]
  exact hinj.eq_iff.symm

end GlobalTheory.St
