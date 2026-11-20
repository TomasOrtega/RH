import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped ComplexOrder

namespace GlobalTheory.FockPos

variable {D : D7}

def frAt {n : ℕ} (fr : GL (Fin n) D.host.E) (τ : D.what₂.Tau) : Matrix (Fin n) (Fin n) ℂ :=
  fr.1.map (tauE D τ)

def zCo (θ : InfFam D) {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E) (w : WO S T) :
    Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank :=
  fun τ => (frAt frT τ)⁻¹ * compAt θ τ w * frAt frS τ

def gaussO (θ : InfFam D) {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E) (w : WO S T) : ℂ :=
  Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖zCo θ frS frT w τ a b‖ ^ 2 : ℝ) : ℂ))

/- English proof (translation)
Take `⟨hss, -, hP⟩` from `h`. Establish `key : ∀ v : Fin k → ℂ, (s - 1) *ᵥ v = 0`. Introduce `v`. Assume the negation of the conclusion as `hx`. Use `set x := (s - 1) *ᵥ v with hxdef`.

Establish `hsx : s *ᵥ x = -x`. Rewrite using `[hxdef, Matrix.mulVec_mulVec, Matrix.mul_sub, hss, Matrix.mul_one, ← neg_sub, Matrix.neg_mulVec]`. Establish `h1` using `hP.dotProduct_mulVec_pos hx`. Establish `h2` using `hG.dotProduct_mulVec_pos hx`. Rewrite `h1` using `[← Matrix.mulVec_mulVec, hsx, Matrix.mulVec_neg, dotProduct_neg]`.

Use `add_pos h1 h2` as an intermediate fact. Simplify using `at this`. Establish `: s - 1 = 0`. Use extensionality with `i j`. Use `congrFun (key (Pi.single j 1)) i` as an intermediate fact.

Simplify `this` using `[Matrix.mulVec_single]`. Conclude with `sub_eq_zero.1 this`.
-/
theorem cartan_eq_one {k : ℕ} {G s : Matrix (Fin k) (Fin k) ℂ} (h : IsCartanInv G s) (hG : G.PosDef) : s = 1 := by
  obtain ⟨hss, -, hP⟩ := h
  have key : ∀ v : Fin k → ℂ, (s - 1) *ᵥ v = 0 := by
    intro v
    by_contra hx
    set x := (s - 1) *ᵥ v with hxdef
    have hsx : s *ᵥ x = -x := by
      rw [hxdef, Matrix.mulVec_mulVec, Matrix.mul_sub, hss, Matrix.mul_one, ← neg_sub, Matrix.neg_mulVec]
    have h1 := hP.dotProduct_mulVec_pos hx
    have h2 := hG.dotProduct_mulVec_pos hx
    rw [← Matrix.mulVec_mulVec, hsx, Matrix.mulVec_neg, dotProduct_neg] at h1
    have := add_pos h1 h2
    simp at this
  have : s - 1 = 0 := by
    ext i j
    have := congrFun (key (Pi.single j 1)) i
    simpa [Matrix.mulVec_single] using this
  exact sub_eq_zero.1 this

/- English proof (translation)
Establish `e : (frAt fr τ).det = tauE D τ fr.1.det` using `(RingHom.map_det (tauE D τ) fr.1).symm`. Rewrite using `[e, map_ne_zero]`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).1 fr.isUnit).ne_zero`.
-/
theorem frAt_det_ne {n : ℕ} (fr : GL (Fin n) D.host.E) (τ : D.what₂.Tau) : (frAt fr τ).det ≠ 0 := by
  have e : (frAt fr τ).det = tauE D τ fr.1.det := (RingHom.map_det (tauE D τ) fr.1).symm
  rw [e, map_ne_zero]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 fr.isUnit).ne_zero

/- English proof (translation)
Establish `hs : ∀ x : D.host.E, tauE D τ ((D.sp.cm.sig : D.host.E →+* D.host.E) x) = star (tauE D τ x)` using `fun x => by`. Use `D.host.isCMField_hostE` as an intermediate fact. Conclude with `NumberField.IsCMField.complexEmbedding_complexConj D.host.E _ x`. Establish `h2` using `congrArg (fun M => M.map (tauE D τ)) h`. Simplify using `only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h2`.

Rewrite using `[← h2, frAt, gramAt]`. Use `congr 2`. Use extensionality with `i j`. Simplify using `[Formalism.UG.cT, Matrix.conjTranspose_apply, hs]`. Conclude with `(hs _).symm`.
-/
theorem frAt_on {S : HSp D} (fr : GL (Fin S.rank) D.host.E)
    (h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * S.gram * fr.1 = 1) (τ : D.what₂.Tau) :
    (frAt fr τ)ᴴ * gramAt D S τ * frAt fr τ = 1 := by
  have hs : ∀ x : D.host.E, tauE D τ ((D.sp.cm.sig : D.host.E →+* D.host.E) x) = star (tauE D τ x) := fun x => by
    have := D.host.isCMField_hostE
    exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E _ x
  have h2 := congrArg (fun M => M.map (tauE D τ)) h
  simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h2
  rw [← h2, frAt, gramAt]
  congr 2
  ext i j
  simp [Formalism.UG.cT, Matrix.conjTranspose_apply, hs]
  exact (hs _).symm

/- English proof (translation)
Establish `hMd : IsUnit (frAt fr τ).det` using `isUnit_iff_ne_zero.2 (frAt_det_ne fr τ)`. Establish `hM : IsUnit (frAt fr τ)` using `(Matrix.isUnit_iff_isUnit_det _).2 hMd`. Establish `hMHd : IsUnit (frAt fr τ)ᴴ.det` using `by rw [Matrix.det_conjTranspose]; exact hMd.star`. Establish `h1` using `frAt_on fr h τ`. Establish `e : ((frAt fr τ)⁻¹)ᴴ * 1 * (frAt fr τ)⁻¹ = gramAt D S τ`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h1, Matrix.conjTranspose_nonsing_inv]`. Use `_ = (((frAt fr τ)ᴴ)⁻¹ * (frAt fr τ)ᴴ) * gramAt D S τ * (frAt fr τ * (frAt fr τ)⁻¹) := by`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = gramAt D S τ := by`.

Rewrite using `[Matrix.nonsing_inv_mul _ hMHd, Matrix.mul_nonsing_inv _ hMd, Matrix.one_mul, Matrix.mul_one]`. Rewrite using `[← e]`. Use `Matrix.PosDef.one.conjTranspose_mul_mul_same ?_` and prove the remaining obligations. Conclude with `Matrix.mulVec_injective_of_isUnit (Matrix.isUnit_nonsing_inv_iff.2 hM)`.
-/
theorem gramAt_posDef {S : HSp D} (fr : GL (Fin S.rank) D.host.E)
    (h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * S.gram * fr.1 = 1) (τ : D.what₂.Tau) :
    (gramAt D S τ).PosDef := by
  have hMd : IsUnit (frAt fr τ).det := isUnit_iff_ne_zero.2 (frAt_det_ne fr τ)
  have hM : IsUnit (frAt fr τ) := (Matrix.isUnit_iff_isUnit_det _).2 hMd
  have hMHd : IsUnit (frAt fr τ)ᴴ.det := by rw [Matrix.det_conjTranspose]; exact hMd.star
  have h1 := frAt_on fr h τ
  have e : ((frAt fr τ)⁻¹)ᴴ * 1 * (frAt fr τ)⁻¹ = gramAt D S τ := by
    calc ((frAt fr τ)⁻¹)ᴴ * 1 * (frAt fr τ)⁻¹
        = ((frAt fr τ)ᴴ)⁻¹ * ((frAt fr τ)ᴴ * gramAt D S τ * frAt fr τ) * (frAt fr τ)⁻¹ := by
          rw [h1, Matrix.conjTranspose_nonsing_inv]
      _ = (((frAt fr τ)ᴴ)⁻¹ * (frAt fr τ)ᴴ) * gramAt D S τ * (frAt fr τ * (frAt fr τ)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = gramAt D S τ := by
          rw [Matrix.nonsing_inv_mul _ hMHd, Matrix.mul_nonsing_inv _ hMd, Matrix.one_mul, Matrix.mul_one]
  rw [← e]
  refine Matrix.PosDef.one.conjTranspose_mul_mul_same ?_
  exact Matrix.mulVec_injective_of_isUnit (Matrix.isUnit_nonsing_inv_iff.2 hM)

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Establish `h1 : (gramAt D S τ).PosDef` using `gramAt_posDef fr h τ`. Conclude with `cartan_eq_one (hs τ) h1`.
-/
theorem cart_one {S : HSp D} (fr : GL (Fin S.rank) D.host.E)
    (h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * S.gram * fr.1 = 1)
    {s : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} (hs : ∀ τ, IsCartanInv (gramAt D S τ) (s τ)) : s = fun _ => 1 :=
by
  funext τ
  have h1 : (gramAt D S τ).PosDef := gramAt_posDef fr h τ
  exact cartan_eq_one (hs τ) h1

end GlobalTheory.FockPos
