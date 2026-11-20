import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapMulRightUnitaryGramAdelicMatrixHaarEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsHermNDInvTranspose
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Twist.LeftHaar

def transposeCAE (D : D7) (m n : ℕ) : Mx D m n ≃ₜ+ Mx D n m where
  toAddEquiv := Matrix.transposeAddEquiv (Fin m) (Fin n) (AE D)
  continuous_toFun := continuous_id.matrix_transpose
  continuous_invFun := continuous_id.matrix_transpose

/- English proof (translation)
Take `⟨h1, h2, h3, h4, h5⟩` from `Formalism.IndefR.Eqv.ae_facts D`. Establish `hJ : IsHermND D.sp.cm.sig W.gram` using `GlobalTheory.Mem.VolExists.isHermND D.sp.cm W`. Take `⟨g', hg'⟩` from `GlobalTheory.AdelicModulus.Row.exists_transpose (AF D.host.F) hJ h`. Establish `hK` using `GlobalTheory.AdelicModulus.Row.isHermND_inv_transpose hJ`. Use `haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩`.

Use `haveI : BorelSpace (Mx D r W.rank) := ⟨rfl⟩`. Set `T` to `transposeCAE D W.rank r`. Establish `hT : Measurable T` using `T.continuous.measurable`. Establish `hTs : Measurable T.symm` using `T.symm.continuous.measurable`. Use `haveI hμ' : (ν.map T).IsAddHaarMeasure := T.isAddHaarMeasure_map ν`.

Establish `hm` using `GlobalTheory.mul_unitary_map_haar D W.rank r (W.gram⁻¹)ᵀ hK.1 hK.2 g' (ν.map T) hμ'`. Use `set A : Matrix (Fin W.rank) (Fin W.rank) (AE D) := (HA.mat (AF D.host.F) D.sp.cm.sig (W.gram⁻¹)ᵀ g').1`. Establish `hR : Measurable (fun x : Mx D r W.rank => (HMul.hMul (x : Matrix (Fin r) (Fin W.rank) (AE D)) A : Mx D r W.rank))` using `(continuous_id.matrix_mul continuous_const).measurable`. Establish `hmt : mt W h = (HA.mat (AF D.host.F) D.sp.cm.sig W.gram h).1` using `rfl`. Establish `hf : (fun y : Mx D W.rank r => (HMul.hMul (mt W h) (y : Matrix (Fin W.rank) (Fin r) (AE D)) : Mx D W.rank r)) = T.symm ∘ (fun x : Mx D r W.rank => (HMul.hMul (x : Matrix (Fin r) (Fin W.rank) (AE D)) A : Mx D r W.rank)) ∘ T`.

Use function extensionality and compare the values at `y`. Simplify using `only [Function.comp_apply, A, hg', hmt]`. Use `show _ = ((y : Matrix (Fin W.rank) (Fin r) (AE D))ᵀ * ((HA.mat (AF D.host.F) D.sp.cm.sig W.gram h).1)ᵀ)ᵀ`. Rewrite using `[← Matrix.transpose_mul, Matrix.transpose_transpose]`. Rewrite using `[hf, ← Measure.map_map hTs (hR.comp hT), ← Measure.map_map hR hT, hm, Measure.map_map hTs hT]`.

Establish `: (T.symm ∘ T : Mx D W.rank r → Mx D W.rank r) = id`. Use function extensionality and compare the values at `y`. Simplify using the standard rewrite rules. Rewrite using `[this, Measure.map_id]`.
-/
theorem map_left_unitary (D : D7) (W : HSp D) (r : ℕ) (h : GA D W) (ν : Measure (Mx D W.rank r))
    (hν : ν.IsAddHaarMeasure) :
    ν.map (fun y : Mx D W.rank r =>
      (HMul.hMul (mt W h) (y : Matrix (Fin W.rank) (Fin r) (AE D)) : Mx D W.rank r)) = ν := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := Formalism.IndefR.Eqv.ae_facts D
  have hJ : IsHermND D.sp.cm.sig W.gram := GlobalTheory.Mem.VolExists.isHermND D.sp.cm W
  obtain ⟨g', hg'⟩ := GlobalTheory.AdelicModulus.Row.exists_transpose (AF D.host.F) hJ h
  have hK := GlobalTheory.AdelicModulus.Row.isHermND_inv_transpose hJ
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI : BorelSpace (Mx D r W.rank) := ⟨rfl⟩
  let T := transposeCAE D W.rank r
  have hT : Measurable T := T.continuous.measurable
  have hTs : Measurable T.symm := T.symm.continuous.measurable
  haveI hμ' : (ν.map T).IsAddHaarMeasure := T.isAddHaarMeasure_map ν
  have hm := GlobalTheory.mul_unitary_map_haar D W.rank r (W.gram⁻¹)ᵀ hK.1 hK.2 g' (ν.map T) hμ'
  set A : Matrix (Fin W.rank) (Fin W.rank) (AE D) := (HA.mat (AF D.host.F) D.sp.cm.sig (W.gram⁻¹)ᵀ g').1
  have hR : Measurable (fun x : Mx D r W.rank =>
      (HMul.hMul (x : Matrix (Fin r) (Fin W.rank) (AE D)) A : Mx D r W.rank)) :=
    (continuous_id.matrix_mul continuous_const).measurable
  have hmt : mt W h = (HA.mat (AF D.host.F) D.sp.cm.sig W.gram h).1 := rfl
  have hf : (fun y : Mx D W.rank r =>
      (HMul.hMul (mt W h) (y : Matrix (Fin W.rank) (Fin r) (AE D)) : Mx D W.rank r)) =
      T.symm ∘ (fun x : Mx D r W.rank => (HMul.hMul (x : Matrix (Fin r) (Fin W.rank) (AE D)) A : Mx D r W.rank)) ∘ T := by
    funext y
    simp only [Function.comp_apply, A, hg', hmt]
    show _ = ((y : Matrix (Fin W.rank) (Fin r) (AE D))ᵀ * ((HA.mat (AF D.host.F) D.sp.cm.sig W.gram h).1)ᵀ)ᵀ
    rw [← Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [hf, ← Measure.map_map hTs (hR.comp hT), ← Measure.map_map hR hT, hm, Measure.map_map hTs hT]
  have : (T.symm ∘ T : Mx D W.rank r → Mx D W.rank r) = id := by
    funext y; simp
  rw [this, Measure.map_id]

/- English proof (translation)
Introduce `D W r h ν hν Φ`. Take `⟨h1, h2, h3, h4, h5⟩` from `Formalism.IndefR.Eqv.ae_facts D`. Set `u` to `HA.mat (AF D.host.F) D.sp.cm.sig W.gram h`. Establish `hmt : mt W h = u.1` using `rfl`. Use `haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩`.

Set `e : Mx D W.rank r ≃ᵐ Mx D W.rank r` to `{ toFun := fun y => (HMul.hMul u.1 (y : Matrix (Fin W.rank) (Fin r) (AE D)) : Mx D W.rank r) invFun := fun y => (HMul.hMul (u⁻¹).1 (y : Matrix (Fin W.rank) (Fin r) (AE D)) : Mx D W.rank r) left_inv := fun y => by show (u⁻¹).1 * (u.1 * y) = y`. Rewrite using `[← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]`. Use `right_inv := fun y => by show u.1 * ((u⁻¹).1 * y) = y`. Rewrite using `[← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]`. Use `measurable_toFun := (continuous_const.matrix_mul continuous_id).measurable`.

Use `measurable_invFun := (continuous_const.matrix_mul continuous_id).measurable }`. Establish `hmap` using `map_left_unitary D W r h ν hν`. Rewrite `hmap` using `[hmt]`. Establish `he : Measure.map (⇑e) ν = ν` using `hmap`. Use `integral_map_equiv (μ := ν) e Φ` as an intermediate fact.

Rewrite `this` using `[he]`. Rewrite using `[hmt]`. Conclude with `this.symm`.
-/
theorem integral_left_unitary : ∀ (D : D7) (W : HSp D) (r : ℕ) (h : GA D W) (ν : Measure (Mx D W.rank r)),
    ν.IsAddHaarMeasure → ∀ Φ : Mx D W.rank r → ℂ,
    ∫ y, Φ (HMul.hMul (Formalism.L2.Theta.mt W h) (y : Matrix (Fin W.rank) (Fin r) (AE D)) : Mx D W.rank r) ∂ν =
      ∫ y, Φ y ∂ν := by
  intro D W r h ν hν Φ
  obtain ⟨h1, h2, h3, h4, h5⟩ := Formalism.IndefR.Eqv.ae_facts D
  let u := HA.mat (AF D.host.F) D.sp.cm.sig W.gram h
  have hmt : mt W h = u.1 := rfl
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  let e : Mx D W.rank r ≃ᵐ Mx D W.rank r :=
    { toFun := fun y => (HMul.hMul u.1 (y : Matrix (Fin W.rank) (Fin r) (AE D)) : Mx D W.rank r)
      invFun := fun y => (HMul.hMul (u⁻¹).1 (y : Matrix (Fin W.rank) (Fin r) (AE D)) : Mx D W.rank r)
      left_inv := fun y => by
        show (u⁻¹).1 * (u.1 * y) = y
        rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      right_inv := fun y => by
        show u.1 * ((u⁻¹).1 * y) = y
        rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      measurable_toFun := (continuous_const.matrix_mul continuous_id).measurable
      measurable_invFun := (continuous_const.matrix_mul continuous_id).measurable }
  have hmap := map_left_unitary D W r h ν hν
  rw [hmt] at hmap
  have he : Measure.map (⇑e) ν = ν := hmap
  have := integral_map_equiv (μ := ν) e Φ
  rw [he] at this
  rw [hmt]
  exact this.symm

end GlobalTheory.Twist.LeftHaar

end
