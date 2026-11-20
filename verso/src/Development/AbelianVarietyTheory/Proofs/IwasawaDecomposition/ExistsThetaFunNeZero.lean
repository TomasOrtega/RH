import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsWeilOnOfCoord
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MapFinNeg
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.WeilTransport
open scoped TensorProduct ComplexOrder

namespace GlobalTheory.Mem.ThetaNonzero

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

/- English proof (translation)
Set `U : Matrix (Fin k) (Fin k) ℂ` to `hG.eigenvectorUnitary.1`. Establish `h1 : U * star U = 1` using `hG.eigenvectorUnitary.2.2`. Establish `h2 : star U * U = 1` using `hG.eigenvectorUnitary.2.1`. Establish `hs : G = U * diagonal (fun i => (hG.eigenvalues i : ℂ)) * star U`. Use `hG.spectral_theorem` as an intermediate fact.

Rewrite `this` using `[Unitary.conjStarAlgAut_apply]`. Conclude with `this`. Establish `hne : ∀ i, hG.eigenvalues i ≠ 0` using `fun i hi => by`. Rewrite `hd` using `[hG.det_eq_prod_eigenvalues]`. Conclude with `hd.ne_zero (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]))`.

Establish `mul : ∀ a b : Fin k → ℂ, (U * diagonal a * star U) * (U * diagonal b * star U) = U * diagonal (fun i => a i * b i) * star U` using `fun a b => by`. Combine the equalities or inequalities in the displayed calculation. Set `e : Fin k → ℝ` to `fun i => if 0 < hG.eigenvalues i then 1 else -1`. Establish `he : ∀ i, (e i : ℂ) * e i = 1` using `fun i => by`. Apply the tactic sequence `simp only [e]; split_ifs <;> simp`.

Establish `hh : (U * diagonal (fun i => (e i : ℂ)) * star U)ᴴ = U * diagonal (fun i => (e i : ℂ)) * star U`. Simplify using `[Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.mul_assoc, Pi.star_def]`. Use `⟨U * diagonal (fun i => (e i : ℂ)) * star U, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mul]`. Simplify using `only [he, diagonal_one, Matrix.mul_one, h1]`.

Rewrite using `[hh] conv_lhs => rw [hs] conv_rhs => rw [hs]`. Rewrite using `[mul, mul]`. Use `congr 3`. Use function extensionality and compare the values at `i`. Rewrite using `[mul_right_comm, he, one_mul]`.

Use `conv => arg 1`. Use `arg 1`. Rewrite using `[hs]`. Rewrite using `[mul]`. Establish `hp : (diagonal fun i => (hG.eigenvalues i : ℂ) * e i).PosDef`.

Rewrite using `[Matrix.posDef_diagonal_iff]`. Introduce `i`. Rewrite using `[← Complex.ofReal_mul, Complex.zero_lt_real]`. Simplify using `only [e]`. Use `split_ifs with h`.

Simplify using `using h`. Use `lt_of_le_of_ne (not_lt.1 h) (hne i)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hu : IsUnit (star U)` using `⟨⟨star U, U, h2, h1⟩, rfl⟩`. Use `hp.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hu)` as an intermediate fact.

Rewrite `this` using `[Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose, ← Matrix.star_eq_conjTranspose]`. Then use the resulting hypothesis.
-/
theorem exists_isCartanInv {k : ℕ} {G : Matrix (Fin k) (Fin k) ℂ} (hG : G.IsHermitian) (hd : IsUnit G.det) :
    ∃ s, IsCartanInv G s := by
  classical
  let U : Matrix (Fin k) (Fin k) ℂ := hG.eigenvectorUnitary.1
  have h1 : U * star U = 1 := hG.eigenvectorUnitary.2.2
  have h2 : star U * U = 1 := hG.eigenvectorUnitary.2.1
  have hs : G = U * diagonal (fun i => (hG.eigenvalues i : ℂ)) * star U := by
    have := hG.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hne : ∀ i, hG.eigenvalues i ≠ 0 := fun i hi => by
    rw [hG.det_eq_prod_eigenvalues] at hd
    exact hd.ne_zero (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]))
  have mul : ∀ a b : Fin k → ℂ, (U * diagonal a * star U) * (U * diagonal b * star U) =
      U * diagonal (fun i => a i * b i) * star U := fun a b => by
    calc _ = U * (diagonal a * (star U * U) * diagonal b) * star U := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h2, Matrix.mul_one, diagonal_mul_diagonal]
  let e : Fin k → ℝ := fun i => if 0 < hG.eigenvalues i then 1 else -1
  have he : ∀ i, (e i : ℂ) * e i = 1 := fun i => by
    simp only [e]; split_ifs <;> simp
  have hh : (U * diagonal (fun i => (e i : ℂ)) * star U)ᴴ = U * diagonal (fun i => (e i : ℂ)) * star U := by
    simp [Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.mul_assoc,
      Pi.star_def]
  refine ⟨U * diagonal (fun i => (e i : ℂ)) * star U, ?_, ?_, ?_⟩
  · rw [mul]
    simp only [he, diagonal_one, Matrix.mul_one, h1]
  · rw [hh]
    conv_lhs => rw [hs]
    conv_rhs => rw [hs]
    rw [mul, mul]
    congr 3
    funext i
    rw [mul_right_comm, he, one_mul]
  · conv => arg 1; arg 1; rw [hs]
    rw [mul]
    have hp : (diagonal fun i => (hG.eigenvalues i : ℂ) * e i).PosDef := by
      rw [Matrix.posDef_diagonal_iff]
      intro i
      rw [← Complex.ofReal_mul, Complex.zero_lt_real]
      simp only [e]
      split_ifs with h
      · simpa using h
      · have := lt_of_le_of_ne (not_lt.1 h) (hne i)
        linarith
    have hu : IsUnit (star U) := ⟨⟨star U, U, h2, h1⟩, rfl⟩
    have := hp.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hu)
    rwa [Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose, ← Matrix.star_eq_conjTranspose] at this

/- English proof (translation)
Take `⟨θ, hθ⟩` from `GlobalTheory.Member.exists_isInfFam_family D`. Establish `hc : ∀ (V : HSp D) τ, ∃ s, IsCartanInv (gramAt D V τ) s` using `fun V τ => exists_isCartanInv (GlobalTheory.SmoothForms.RealPts.gramAt_herm V τ) (GlobalTheory.SmoothForms.RealPts.gramAt_unit V τ)`. Use `choose s hs using hc`. Take `⟨f, f0, hf⟩` from `GlobalTheory.VacuumO.exists_ne_zero ψ θ hψ hθ S T (s S) (s T) (hs S) (hs T) _ _ (GlobalTheory.PlaceModel.isSelfDualC_latFrame S) (GlobalTheory.PlaceModel.isSelfDualC_latFrame T)`. Use `⟨f, ?_, f0⟩` and prove the remaining obligations.

Simplify `(hf 1).1` using `only [one_mul]`.
-/
theorem exists_thetaO_ne_zero {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) :
    ∃ f, IsThetaFunO ψ S T f ∧ f ≠ 0 := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  have hc : ∀ (V : HSp D) τ, ∃ s, IsCartanInv (gramAt D V τ) s := fun V τ =>
    exists_isCartanInv (GlobalTheory.SmoothForms.RealPts.gramAt_herm V τ) (GlobalTheory.SmoothForms.RealPts.gramAt_unit V τ)
  choose s hs using hc
  obtain ⟨f, f0, hf⟩ := GlobalTheory.VacuumO.exists_ne_zero ψ θ hψ hθ S T (s S) (s T) (hs S) (hs T) _ _
    (GlobalTheory.PlaceModel.isSelfDualC_latFrame S) (GlobalTheory.PlaceModel.isSelfDualC_latFrame T)
  refine ⟨f, ?_, f0⟩
  simpa only [one_mul] using (hf 1).1

/- English proof (translation)
Take `⟨f, hf, f0⟩` from `exists_thetaO_ne_zero hψ S T`. Establish `e : (f ∘ E.symm) ∘ E = f`. Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules. Use `⟨f ∘ E.symm, (hE.theta_iff ψ _).1 (by rwa [e]), fun h => f0 ?_⟩` and prove the remaining obligations.

Rewrite using `[← e, h]`. Both sides reduce to the same expression.
-/
theorem exists_of_isCoord {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T V W : HSp D}
    {E : WO S T ≃+ WA V W} (hE : IsCoord S T V W E) : ∃ f, IsThetaFun ψ V W f ∧ f ≠ 0 := by
  obtain ⟨f, hf, f0⟩ := exists_thetaO_ne_zero hψ S T
  have e : (f ∘ E.symm) ∘ E = f := by
    funext x
    simp
  refine ⟨f ∘ E.symm, (hE.theta_iff ψ _).1 (by rwa [e]), fun h => f0 ?_⟩
  rw [← e, h]
  rfl

/- English proof (translation)
The claim follows from `(continuous_id.matrix_mul continuous_const).matrix_transpose cont' := continuous_id.matrix_transpose.matrix_mul continuous_const sympl x y := by unfold symplOH symplH rw [(GlobalTheory.OrientedSmall.bridgeSmall D S T hr).1] rfl rat x := by constructor · rintro ⟨γ, rfl⟩ have h : ( …`.
-/
theorem isCoord_of_le (S T : HSp D) (hr : S.rank ≤ T.rank) :
    IsCoord S T S T ((mulGramInv S T).trans (Matrix.transposeAddEquiv _ _ _)) where
  cont := (continuous_id.matrix_mul continuous_const).matrix_transpose
  cont' := continuous_id.matrix_transpose.matrix_mul continuous_const
  sympl x y := by
    unfold symplOH symplH
    rw [(GlobalTheory.OrientedSmall.bridgeSmall D S T hr).1]
    rfl
  rat x := by
    constructor
    · rintro ⟨γ, rfl⟩
      have h : (γ * S.gram⁻¹).map (incA D) = mulGramInv S T (γ.map (incA D)) := Matrix.map_mul (f := incA D)
      exact ⟨(γ * S.gram⁻¹).transpose, congrArg Matrix.transpose h⟩
    · rintro ⟨γ, hγ⟩
      have hγ' : γ.transpose.map (incA D) = mulGramInv S T x := congrArg Matrix.transpose hγ
      refine ⟨γ.transpose * S.gram, (Matrix.map_mul (f := incA D)).trans ?_⟩
      rw [← (mulGramInv S T).symm_apply_apply x, ← hγ']
      rfl
  inf x := (map_mulGramInv _ S T x).trans
    ⟨fun h => congrArg Matrix.transpose h, fun h => congrArg Matrix.transpose h⟩
  fin x := (map_mulGramInv _ S T x).trans
    ⟨fun h => congrArg Matrix.transpose h, fun h => congrArg Matrix.transpose h⟩
  part a x h i j := by
    show a * ∑ k, x j k * incA D (S.gram⁻¹ k i) = ∑ k, x j k * incA D (S.gram⁻¹ k i)
    simp only [Finset.mul_sum, ← mul_assoc, h]

/- English proof (translation)
Introduce `D ψ hψ V W`. Break down `le_or_gt V.rank W.rank with hr | hr` into its components or cases. Conclude with `exists_of_isCoord hψ (isCoord_of_le V W hr)`. Conclude with `exists_of_isCoord hψ (isCoord_large W V hr)`.
-/
theorem exists_thetaFun_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V W : HSp D), ∃ f, IsThetaFun ψ V W f ∧ f ≠ 0 := by
  intro D ψ hψ V W
  rcases le_or_gt V.rank W.rank with hr | hr
  · exact exists_of_isCoord hψ (isCoord_of_le V W hr)
  · exact exists_of_isCoord hψ (isCoord_large W V hr)

end GlobalTheory.Mem.ThetaNonzero

end
