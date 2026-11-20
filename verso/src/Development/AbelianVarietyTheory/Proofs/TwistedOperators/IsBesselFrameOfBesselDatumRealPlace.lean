import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GramAtConjTranspose
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BesselFormsTrivialNeBot
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.BesselFrameReal

variable {D : D7}

/- English proof (translation)
Rewrite using `[Matrix.map_mul, Matrix.map_mul, Matrix.conjTranspose_map _ (GlobalTheory.FockCompare.tauE_star τ)]`. Both sides reduce to the same expression.
-/
theorem map_cT_gram_mul (V : HSp D) (τ : D.what₂.Tau) {a b : ℕ} (X : Matrix (Fin V.rank) (Fin a) D.host.E)
    (Z : Matrix (Fin V.rank) (Fin b) D.host.E) :
    (X.map (tauE D τ))ᴴ * gramAt D V τ * Z.map (tauE D τ) = (Xᴴ * V.gram * Z).map (tauE D τ) := by
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.conjTranspose_map _ (GlobalTheory.FockCompare.tauE_star τ)]; rfl

/- English proof (translation)
Rewrite using `[Matrix.map_mul, Matrix.conjTranspose_map _ (GlobalTheory.FockCompare.tauE_star τ)]`. Both sides reduce to the same expression.
-/
theorem map_cT_gram (V : HSp D) (τ : D.what₂.Tau) {a : ℕ} (X : Matrix (Fin V.rank) (Fin a) D.host.E) :
    (X.map (tauE D τ))ᴴ * gramAt D V τ = (Xᴴ * V.gram).map (tauE D τ) := by
  rw [Matrix.map_mul, Matrix.conjTranspose_map _ (GlobalTheory.FockCompare.tauE_star τ)]; rfl

/- English proof (translation)
Use function extensionality and compare the values at `i`. Rewrite using `[map_cT_gram, RingHom.map_mulVec]`. Both sides reduce to the same expression.
-/
theorem map_cT_gram_mulVec (V : HSp D) (τ : D.what₂.Tau) {a : ℕ} (X : Matrix (Fin V.rank) (Fin a) D.host.E)
    (z : Fin V.rank → D.host.E) :
    ((X.map (tauE D τ))ᴴ * gramAt D V τ) *ᵥ (fun k => tauE D τ (z k)) =
      fun i => tauE D τ (((Xᴴ * V.gram) *ᵥ z) i) := by
  funext i
  rw [map_cT_gram, RingHom.map_mulVec]
  rfl

/- English proof (translation)
Establish `hσ : ∀ x : D.host.E, tauE D τ ((D.sp.cm.sig : D.host.E →+* D.host.E) x) = star (tauE D τ x)` using `fun x => GlobalTheory.FockCompare.tauE_star τ x`. Simplify using `only [Formalism.QuantumDeterminants.herm, Formalism.UG.hform, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, gramAt, Matrix.map_apply, Finset.mul_sum, Pi.star_apply, mul_assoc]`.
-/
theorem herm_gramAt (V : HSp D) (τ : D.what₂.Tau) (z : Fin V.rank → D.host.E) :
    Formalism.QuantumDeterminants.herm (gramAt D V τ) (fun k => tauE D τ (z k)) (fun k => tauE D τ (z k)) =
      tauE D τ (Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram z z) := by
  have hσ : ∀ x : D.host.E, tauE D τ ((D.sp.cm.sig : D.host.E →+* D.host.E) x) = star (tauE D τ x) :=
    fun x => GlobalTheory.FockCompare.tauE_star τ x
  simp only [Formalism.QuantumDeterminants.herm, Formalism.UG.hform, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, gramAt,
    Matrix.map_apply, Finset.mul_sum, Pi.star_apply, mul_assoc]

end GlobalTheory.BesselFrameReal

namespace GlobalTheory.BesselFrameReal

/- English proof (translation)
Use `Fintype.linearIndependent_iff.mpr fun g hg => ?_` and prove the remaining obligations. Establish `h1 : e *ᵥ g = 0`. Use function extensionality and compare the values at `k`. Use `congrFun hg k` as an intermediate fact. Simplify `this` using `[Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]`.

Establish `h2` using `congrArg (fun v => L *ᵥ v) h1`. Simplify using `only [Matrix.mulVec_mulVec, hL, Matrix.one_mulVec, Matrix.mulVec_zero] at h2`. Conclude with `congrFun h2`.
-/
theorem linearIndependent_of_mul_eq_one {n r : ℕ} (e : Matrix (Fin n) (Fin r) ℂ) (L : Matrix (Fin r) (Fin n) ℂ)
    (hL : L * e = 1) : LinearIndependent ℂ eᵀ := by
  refine Fintype.linearIndependent_iff.mpr fun g hg => ?_
  have h1 : e *ᵥ g = 0 := by
    funext k
    have := congrFun hg k
    simpa [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm] using this
  have h2 := congrArg (fun v => L *ᵥ v) h1
  simp only [Matrix.mulVec_mulVec, hL, Matrix.one_mulVec, Matrix.mulVec_zero] at h2
  exact congrFun h2

/- English proof (translation)
Introduce `D A B ι hι d τ`. Establish `hinj : Function.Injective (tauE D τ)` using `(tauE D τ).injective`. Establish `hunit : ∀ V : HSp D, IsUnit (gramAt D V τ)` using `fun V => by`. Rewrite using `[Matrix.isUnit_iff_isUnit_det]`. Use `show IsUnit ((tauE D τ).mapMatrix (HSpace.gram V)).det`.

Rewrite using `[← RingHom.map_det]`. Conclude with `isUnit_iff_ne_zero.2 ((map_ne_zero _).2 (Formalism.L2.Theta.gram_det_ne V))`. Take `⟨L, hL⟩` from `GlobalTheory.BesselChar.exists_leftInv d.e d.e_iso.1`. Use `{ herm := GlobalTheory.SepPer.gramAt_conjTranspose B τ unit := hunit B unit₀ := hunit A codim := d.codim gram := ?_ e_indep := ?_ e_iso := ?_ e_perp := ?_ z_perpF := ?_ z_perpE := ?_ z_ne := ?_ }` and prove the remaining obligations. Rewrite using `[map_cT_gram_mul]`.

Establish `h : (frameMat B A ι)ᴴ * B.gram * frameMat B A ι = A.gram` using `GlobalTheory.AutFunCounterexample.gram_pull B A ι hι`. Rewrite using `[h]`. Both sides reduce to the same expression. Use `linearIndependent_of_mul_eq_one _ (L.map (tauE D τ)) ?_` and prove the remaining obligations. Rewrite using `[← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]`.

Rewrite using `[map_cT_gram_mul]`. Establish `h : d.eᴴ * B.gram * d.e = 0` using `d.e_iso.2`. Rewrite using `[h, Matrix.map_zero _ (map_zero _)]`. Rewrite using `[map_cT_gram_mul]`. Establish `h : (frameMat B A ι)ᴴ * B.gram * d.e = 0` using `d.e_perp`.

Rewrite using `[h, Matrix.map_zero _ (map_zero _)]`. Rewrite using `[map_cT_gram_mulVec]`. Establish `h : ((frameMat B A ι)ᴴ * B.gram) *ᵥ d.z = 0` using `d.z_perpA`. Rewrite using `[h]`. Use function extensionality and compare the values at `i`.

Simplify using the standard rewrite rules. Rewrite using `[map_cT_gram_mulVec]`. Establish `h : (d.eᴴ * B.gram) *ᵥ d.z = 0` using `d.z_perpE`. Rewrite using `[h]`. Use function extensionality and compare the values at `i`.

Simplify using the standard rewrite rules. Rewrite using `[herm_gramAt]`. Conclude with `(map_ne_zero _).2 d.z_ne`.
-/
theorem isFrame_of_besDat : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V), HSpace.IsIsomEmb A B ι → ∀ (d : BesDat A B ι) (τ : D.what₂.Tau),
  GlobalTheory.RealBessel.IsFrame (gramAt D B τ) (gramAt D A τ) ((frameMat B A ι).map (tauE D τ)) (d.e.map (tauE D τ)) (fun k => tauE D τ (d.z k)) := by
  intro D A B ι hι d τ
  have hinj : Function.Injective (tauE D τ) := (tauE D τ).injective
  have hunit : ∀ V : HSp D, IsUnit (gramAt D V τ) := fun V => by
    rw [Matrix.isUnit_iff_isUnit_det]
    show IsUnit ((tauE D τ).mapMatrix (HSpace.gram V)).det
    rw [← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 (Formalism.L2.Theta.gram_det_ne V))
  obtain ⟨L, hL⟩ := GlobalTheory.BesselChar.exists_leftInv d.e d.e_iso.1
  refine
    { herm := GlobalTheory.SepPer.gramAt_conjTranspose B τ
      unit := hunit B
      unit₀ := hunit A
      codim := d.codim
      gram := ?_
      e_indep := ?_
      e_iso := ?_
      e_perp := ?_
      z_perpF := ?_
      z_perpE := ?_
      z_ne := ?_ }
  · rw [map_cT_gram_mul]
    have h : (frameMat B A ι)ᴴ * B.gram * frameMat B A ι = A.gram := GlobalTheory.AutFunCounterexample.gram_pull B A ι hι
    rw [h]; rfl
  · refine linearIndependent_of_mul_eq_one _ (L.map (tauE D τ)) ?_
    rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [map_cT_gram_mul]
    have h : d.eᴴ * B.gram * d.e = 0 := d.e_iso.2
    rw [h, Matrix.map_zero _ (map_zero _)]
  · rw [map_cT_gram_mul]
    have h : (frameMat B A ι)ᴴ * B.gram * d.e = 0 := d.e_perp
    rw [h, Matrix.map_zero _ (map_zero _)]
  · rw [map_cT_gram_mulVec]
    have h : ((frameMat B A ι)ᴴ * B.gram) *ᵥ d.z = 0 := d.z_perpA
    rw [h]; funext i; simp
  · rw [map_cT_gram_mulVec]
    have h : (d.eᴴ * B.gram) *ᵥ d.z = 0 := d.z_perpE
    rw [h]; funext i; simp
  · rw [herm_gramAt]
    exact (map_ne_zero _).2 d.z_ne

end GlobalTheory.BesselFrameReal
