import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.CayleyPhaseQuadratic
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.GaussSumEighthPower
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.UnitaryEighthOf
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.RelIndexEqAbsDetReal
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.ExtensionActionPermutesPlaces
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.GaloisDescentSubspaces
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.ExtensionInterSubspace
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.ExtensionFiltrationStable
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.CayleyGaussianIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.DiagonalIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.UnfoldingIntegral

noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace Formalism.L2.Th1.H

namespace UC

/- English proof (translation)
The claim follows from `KerPTh_of exp_series_entire latticeGaussSummable formNormEquiv`.
-/
theorem kerPTh : KerPTh := KerPTh_of exp_series_entire latticeGaussSummable formNormEquiv
/- English proof (translation)
The claim follows from `KerPNonzero_of diagonalIntegral`.
-/
theorem kerPNonzero : KerPNonzero := KerPNonzero_of diagonalIntegral
/- English proof (translation)
The claim follows from `GaussIntegrable_of formNormEquiv`.
-/
theorem gaussIntegrable : GaussIntegrable := GaussIntegrable_of formNormEquiv
/- English proof (translation)
The claim follows from `UnitaryGauss_of gaussSumEighthPower`.
-/
theorem unitaryGauss : UnitaryGauss := UnitaryGauss_of gaussSumEighthPower

section Line

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] {H : Sesq V}
  {Λ : AddSubgroup V} {α : V → ℂ} {δ Ae : V ≃ₗ[ℂ] V}

/- English proof (translation)
Assemble the required witnesses or components as `⟨hF.1, fun x hx z => by rw [h x hx]; exact hF.2 x hx z⟩`.
-/
theorem th_congr (α' : V → ℂ) (h : ∀ x ∈ Λ, α' x = α x) {F : V → ℂ} (hF : F ∈ Th H α Λ) :
    F ∈ Th H α' Λ :=
  ⟨hF.1, fun x hx z => by rw [h x hx]; exact hF.2 x hx z⟩

/- English proof (translation)
Rewrite using `[thIsom V V H H δ hU.isom Λ α (pullInv δ θ)]`. Establish `e : (fun v => pullInv δ θ (δ v)) = θ`. Use function extensionality and compare the values at `v`. Simplify using `[pullInv]`. Rewrite using `[e]`.

Conclude with `th_congr _ hU.inv hθ`.
-/
theorem pull_mem (hU : UnitaryData H Λ α δ Ae) {θ : V → ℂ} (hθ : θ ∈ Th H α Λ) :
    pullInv δ θ ∈ Th H α (imgLat (δ : V →ₗ[ℂ] V) Λ) := by
  rw [thIsom V V H H δ hU.isom Λ α (pullInv δ θ)]
  have e : (fun v => pullInv δ θ (δ v)) = θ := by
    funext v
    simp [pullInv]
  rw [e]
  exact th_congr _ hU.inv hθ

/- English proof (translation)
Take `⟨w, z, hwz⟩` from `kerPNonzero V H Λ α hU.herm hU.pos hL hU.selfDual hU.semi`. Take `⟨θ₀, hdef⟩ : ∃ θ₀ : V → ℂ, θ₀ = fun z => kerP H α Λ z w` from `⟨_, rfl⟩`. Establish `hθ₀ : θ₀ ∈ Th H α Λ`. Rewrite using `[hdef]`. Conclude with `(kerPTh V H Λ α hU.herm hU.pos hL hU.semi w).2`.

Establish `hne : θ₀ ≠ 0`. Introduce `h`. Apply `hwz` to reduce the goal to its premises. Use `congrFun h z` as an intermediate fact. Rewrite `this` using `[hdef]`.

Conclude with `this`. Take `⟨-, hline2⟩` from `lineTransport V H hU.herm Λ (imgLat (δ : V →ₗ[ℂ] V) Λ) α hU.selfDual (Cay.selfDual_img H Λ δ hU.isom hU.selfDual) hU.semi hU.semi' hU.idx₂ hU.idx₁ θ₀ hθ₀ hne (hLine θ₀ hθ₀ hne)`. Take `⟨c, hc⟩` from `hline2 _ (pull_mem hU hθ₀)`. Use `⟨c, fun θ hθ => ?_⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `hLine θ₀ hθ₀ hne θ hθ`.

Rewrite using `[Inv.inter_smul, smul_comm, ← hc]`. Both sides reduce to the same expression.
-/
theorem exists_const (hL : IsLat Λ) (hU : UnitaryData H Λ α δ Ae) (hLine : AtMostLine H α Λ) :
    ∃ c : ℂ, ∀ θ ∈ Th H α Λ, pullInv δ θ = c • inter H α Λ (imgLat (δ : V →ₗ[ℂ] V) Λ) θ := by
  obtain ⟨w, z, hwz⟩ := kerPNonzero V H Λ α hU.herm hU.pos hL hU.selfDual hU.semi
  obtain ⟨θ₀, hdef⟩ : ∃ θ₀ : V → ℂ, θ₀ = fun z => kerP H α Λ z w := ⟨_, rfl⟩
  have hθ₀ : θ₀ ∈ Th H α Λ := by
    rw [hdef]
    exact (kerPTh V H Λ α hU.herm hU.pos hL hU.semi w).2
  have hne : θ₀ ≠ 0 := by
    intro h
    apply hwz
    have := congrFun h z
    rw [hdef] at this
    exact this
  obtain ⟨-, hline2⟩ := lineTransport V H hU.herm Λ (imgLat (δ : V →ₗ[ℂ] V) Λ) α hU.selfDual
    (Cay.selfDual_img H Λ δ hU.isom hU.selfDual) hU.semi hU.semi' hU.idx₂ hU.idx₁ θ₀ hθ₀ hne
    (hLine θ₀ hθ₀ hne)
  obtain ⟨c, hc⟩ := hline2 _ (pull_mem hU hθ₀)
  refine ⟨c, fun θ hθ => ?_⟩
  obtain ⟨a, rfl⟩ := hLine θ₀ hθ₀ hne θ hθ
  rw [Inv.inter_smul, smul_comm, ← hc]
  rfl

/- English proof (translation)
Take `⟨-, hidx⟩` from `unitary_index V H Λ α δ Ae hL hU`. Introduce `h0`. Rewrite `hidx` using `[h0]`. Establish `hdt0 : LinearMap.det (Ae : V →ₗ[ℂ] V) ≠ 0` using `(LinearEquiv.isUnit_det' Ae).ne_zero`. Establish `h1 : (relIdx (imgLat (δ : V →ₗ[ℂ] V) Λ) Λ : ℝ) ≠ 0` using `by exact_mod_cast hU.idx₁`.

Establish `h2 : ‖LinearMap.det (Ae : V →ₗ[ℂ] V)‖ ^ 2 ≠ 0` using `pow_ne_zero _ (norm_ne_zero_iff.mpr hdt0)`. Conclude with `mul_ne_zero h1 h2 (by simpa using hidx.symm)`.
-/
theorem latA_idx_ne (hL : IsLat Λ) (hU : UnitaryData H Λ α δ Ae) : relIdx (latA Λ δ Ae) Λ ≠ 0 := by
  obtain ⟨-, hidx⟩ := unitary_index V H Λ α δ Ae hL hU
  intro h0
  rw [h0] at hidx
  have hdt0 : LinearMap.det (Ae : V →ₗ[ℂ] V) ≠ 0 := (LinearEquiv.isUnit_det' Ae).ne_zero
  have h1 : (relIdx (imgLat (δ : V →ₗ[ℂ] V) Λ) Λ : ℝ) ≠ 0 := by exact_mod_cast hU.idx₁
  have h2 : ‖LinearMap.det (Ae : V →ₗ[ℂ] V)‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hdt0)
  exact mul_ne_zero h1 h2 (by simpa using hidx.symm)

/- English proof (translation)
Take `⟨-, hidx⟩` from `unitary_index V H Λ α δ Ae hL hU`. Rewrite using `[(repsExist V _ _ (latA_idx_ne hL hU)).2 S hS, hidx, Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]`.
-/
theorem sqrt_card (hL : IsLat Λ) (hU : UnitaryData H Λ α δ Ae) {S : Finset V}
    (hS : IsReps (latA Λ δ Ae) Λ S) :
    Real.sqrt S.card
      = Real.sqrt (relIdx (imgLat (δ : V →ₗ[ℂ] V) Λ) Λ) * ‖LinearMap.det (Ae : V →ₗ[ℂ] V)‖ := by
  obtain ⟨-, hidx⟩ := unitary_index V H Λ α δ Ae hL hU
  rw [(repsExist V _ _ (latA_idx_ne hL hU)).2 S hS, hidx, Real.sqrt_mul (Nat.cast_nonneg _),
    Real.sqrt_sq (norm_nonneg _)]

end Line

/- English proof (translation)
Establish `h8` using `unitaryGauss V H Λ α δ Ae hU S hS`. Establish `h1 : ‖gaussC H α Ae S‖ = 1`. Use `congrArg norm h8` as an intermediate fact. Rewrite `this` using `[norm_pow, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp this`.

Establish `hs : Real.sqrt S.card ≠ 0`. Introduce `h0`. Rewrite `h1` using `[gaussC, h0]`. Simplify using `at h1`. Rewrite `h1` using `[gaussC, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]`.

Clear denominators, using `at h1` for the nonvanishing conditions. Conclude with `h1`.
-/
theorem norm_sum_phi {V : Type} [AddCommGroup V] [Module ℂ V] {H : Sesq V} {Λ : AddSubgroup V} {α : V → ℂ}
    {δ Ae : V ≃ₗ[ℂ] V} (hU : UnitaryData H Λ α δ Ae) {S : Finset V} (hS : IsReps (latA Λ δ Ae) Λ S) :
    ‖∑ x ∈ S, phiC H α Ae x‖ = Real.sqrt S.card := by
  have h8 := unitaryGauss V H Λ α δ Ae hU S hS
  have h1 : ‖gaussC H α Ae S‖ = 1 := by
    have := congrArg norm h8
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp this
  have hs : Real.sqrt S.card ≠ 0 := by
    intro h0
    rw [gaussC, h0] at h1
    simp at h1
  rw [gaussC, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)] at h1
  field_simp at h1
  exact h1

/- English proof (translation)
Take `⟨c₀, C₀, hc₀, -, hform⟩` from `formNormEquiv V H hH hP`. Take `⟨u, hu, hule⟩` from `latticeGaussSummable V Λ hL (Real.pi / 2 * c₀) ‖y‖ (by positivity)`. Establish `hfin : μ D' < ⊤` using `hb.measure_lt_top`. Establish `: IsFiniteMeasure (μ.restrict D')` using `⟨by simpa using hfin⟩`. Establish `hbound : ∀ x : Λ, ‖diagCoef H α y (x : V)‖ ≤ u x`.

Introduce `x`. Rewrite using `[norm_diagCoef H α y x hy (hα.1 x x.2)]`. Use `le_trans ?_ (hule x (-y) (by rw [norm_neg]))` and prove the remaining obligations. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Establish `h` using `(hform (y + (x : V))).1`.

Establish `e : (x : V) - -y = y + (x : V)` using `by abel`. Rewrite using `[e]`. Establish `hpi : 0 < Real.pi / 2` using `by positivity`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h hpi.le]`. Establish `hn : ∀ (x : Λ) (z : V), ‖diagCoef H α y (x : V) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H (y + (x : V)) z : ℂ))‖ ≤ u x`.

Introduce `x z`. Rewrite using `[norm_mul, norm_char, mul_one]`. Conclude with `hbound x`. Establish `hcont : Continuous fun z => ∑' x : Λ, diagCoef H α y (x : V) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H (y + (x : V)) z : ℂ))`. Use `continuous_tsum (fun x => ?_) hu hn` and prove the remaining obligations.

Use `continuous_const.mul (Complex.continuous_exp.comp ?_)` and prove the remaining obligations. Conclude with `continuous_const.mul (Complex.continuous_ofReal.comp (continuous_altE H hH _))`. Establish `e : (fun z => α y * opU H y (fun v => kerP H α Λ v z) z * (wt H z : ℂ)) = fun z => ∑' x : Λ, diagCoef H α y (x : V) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H (y + (x : V)) z : ℂ))`. Use function extensionality and compare the values at `fun z => diag_expansion H hH α Λ y z`. Rewrite using `[e]`.

Use `Integrable.of_bound hcont.aestronglyMeasurable (∑' x, u x) (Filter.Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Conclude with `tsum_of_norm_bounded hu.hasSum (fun x => hn x z)`.
-/
theorem diag_integrable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V) (Λ : AddSubgroup V)
    (α : V → ℂ) (hH : IsHerm H) (hP : IsPosDef H) (hL : IsLat Λ) (hα : IsSemiChar H Λ α) (D' : Set V)
    (hb : Bornology.IsBounded D') (y : V) (hy : α y = 1 ∨ α y = -1) :
    Integrable (fun z => α y * opU H y (fun v => kerP H α Λ v z) z * (wt H z : ℂ)) (μ.restrict D') := by
  obtain ⟨c₀, C₀, hc₀, -, hform⟩ := formNormEquiv V H hH hP
  obtain ⟨u, hu, hule⟩ := latticeGaussSummable V Λ hL (Real.pi / 2 * c₀) ‖y‖ (by positivity)
  have hfin : μ D' < ⊤ := hb.measure_lt_top
  have : IsFiniteMeasure (μ.restrict D') := ⟨by simpa using hfin⟩
  have hbound : ∀ x : Λ, ‖diagCoef H α y (x : V)‖ ≤ u x := by
    intro x
    rw [norm_diagCoef H α y x hy (hα.1 x x.2)]
    refine le_trans ?_ (hule x (-y) (by rw [norm_neg]))
    apply Real.exp_le_exp.mpr
    have h := (hform (y + (x : V))).1
    have e : (x : V) - -y = y + (x : V) := by abel
    rw [e]
    have hpi : 0 < Real.pi / 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h hpi.le]
  have hn : ∀ (x : Λ) (z : V), ‖diagCoef H α y (x : V) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H (y + (x : V)) z : ℂ))‖ ≤ u x := by
    intro x z
    rw [norm_mul, norm_char, mul_one]
    exact hbound x
  have hcont : Continuous fun z => ∑' x : Λ, diagCoef H α y (x : V) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H (y + (x : V)) z : ℂ)) := by
    refine continuous_tsum (fun x => ?_) hu hn
    refine continuous_const.mul (Complex.continuous_exp.comp ?_)
    exact continuous_const.mul (Complex.continuous_ofReal.comp (continuous_altE H hH _))
  have e : (fun z => α y * opU H y (fun v => kerP H α Λ v z) z * (wt H z : ℂ))
      = fun z => ∑' x : Λ, diagCoef H α y (x : V) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H (y + (x : V)) z : ℂ)) :=
    funext fun z => diag_expansion H hH α Λ y z
  rw [e]
  refine Integrable.of_bound hcont.aestronglyMeasurable (∑' x, u x)
    (Filter.Eventually.of_forall fun z => ?_)
  exact tsum_of_norm_bounded hu.hasSum (fun x => hn x z)

/- English proof (translation)
Take `⟨c, hc⟩` from `exists_const hL hU hLine`. Use `⟨c, hc, ?_⟩` and prove the remaining obligations. Take `⟨S₂, hS₂⟩` from `(repsExist V Λ (imgLat (δ : V →ₗ[ℂ] V) Λ) hU.idx₂).1`. Establish `hsd2` using `Cay.selfDual_img H Λ δ hU.isom hU.selfDual`. Take `⟨r, hr⟩ : ∃ r : ℂ, r = ((Real.sqrt (relIdx Λ (imgLat (δ : V →ₗ[ℂ] V) Λ)) : ℝ) : ℂ)⁻¹` from `⟨_, rfl⟩`.

Rewrite using `[← hr]`. Establish `hpt : ∀ z, kerP H α Λ (δ.symm z) z * (wt H z : ℂ) = c * r * ∑ y ∈ S₂, α y * opU H y (fun v => kerP H α Λ v z) z * (wt H z : ℂ)`. Introduce `z`. Establish `hm` using `(kerPTh V H Λ α hU.herm hU.pos hL hU.semi z).2`. Establish `h1` using `congrFun (hc _ hm) z`.

Establish `h2` using `interReps V H hU.herm Λ (imgLat (δ : V →ₗ[ℂ] V) Λ) α hU.semi' _ hm.2 S₂ hS₂ z`. Establish `h3 : pullInv δ (fun v => kerP H α Λ v z) z = kerP H α Λ (δ.symm z) z` using `rfl`. Rewrite `h1` using `[h3, Pi.smul_apply, h2, ← hr, sumU, smul_eq_mul]`. Rewrite using `[h1, ← Finset.sum_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hint : ∀ y ∈ S₂, Integrable (fun z => α y * opU H y (fun v => kerP H α Λ v z) z * (wt H z : ℂ)) (μ.restrict D')` using `fun y hy => diag_integrable μ H Λ α hU.herm hU.pos hL hU.semi D' hb y (hU.semi'.1 y (hS₂.1 y hy))`. Establish `hleft` using `unfoldingIntegral V μ H Λ α δ Ae hL hU D' hD' hb S hS`. Rewrite `hleft` using `[(cayleyGaussianIntegral V μ H hU.herm hU.pos δ Ae hU.isom hU.cay).2]`. Rewrite using `[← hleft]`. Repeatedly rewrite using `[hpt]`.

Rewrite using `[integral_const_mul, integral_finsetSum _ hint]`. Establish `hdiag` using `diagonalIntegral V μ H Λ (imgLat (δ : V →ₗ[ℂ] V) Λ) α hU.herm hU.pos hL hU.selfDual hsd2 hU.semi hU.semi' D' hD' hb`. Take `⟨y₀, hy₀, hy₀Λ, hsum⟩` from `Inv.sum_reps hS₂ (fun y => ∫ z in D', α y * opU H y (fun v => kerP H α Λ v z) z * (wt H z : ℂ) ∂μ) (fun y hy hyΛ => by`. Use `hdiag y (hS₂.1 y hy)` as an intermediate fact. Rewrite `this` using `[if_neg hyΛ]`.

Conclude with `this)`. Rewrite using `[hsum]`. Use `hdiag y₀ (hS₂.1 y₀ hy₀)` as an intermediate fact. Rewrite `this` using `[if_pos hy₀Λ]`. Rewrite using `[this]`.
-/
theorem const_value {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] {H : Sesq V} {Λ : AddSubgroup V}
    {α : V → ℂ} {δ Ae : V ≃ₗ[ℂ] V} (hL : IsLat Λ) (hU : UnitaryData H Λ α δ Ae)
    (hLine : AtMostLine H α Λ) {D' : Set V}
    (hD' : IsAddFundamentalDomain (Λ ⊓ imgLat (δ : V →ₗ[ℂ] V) Λ : AddSubgroup V) D' μ)
    (hb : Bornology.IsBounded D') {S : Finset V} (hS : IsReps (latA Λ δ Ae) Λ S) :
    ∃ c : ℂ, (∀ θ ∈ Th H α Λ, pullInv δ θ = c • inter H α Λ (imgLat (δ : V →ₗ[ℂ] V) Λ) θ) ∧
      c * ((Real.sqrt (relIdx Λ (imgLat (δ : V →ₗ[ℂ] V) Λ)) : ℝ) : ℂ)⁻¹ * ((μ D').toReal : ℂ)
        = (∑ x ∈ S, phiC H α Ae x) *
            (((∫ z, wt H z ∂μ : ℝ) : ℂ) / LinearMap.det (Ae : V →ₗ[ℂ] V)) := by
  classical
  obtain ⟨c, hc⟩ := exists_const hL hU hLine
  refine ⟨c, hc, ?_⟩
  obtain ⟨S₂, hS₂⟩ := (repsExist V Λ (imgLat (δ : V →ₗ[ℂ] V) Λ) hU.idx₂).1
  have hsd2 := Cay.selfDual_img H Λ δ hU.isom hU.selfDual
  obtain ⟨r, hr⟩ : ∃ r : ℂ, r = ((Real.sqrt (relIdx Λ (imgLat (δ : V →ₗ[ℂ] V) Λ)) : ℝ) : ℂ)⁻¹ := ⟨_, rfl⟩
  rw [← hr]
  have hpt : ∀ z, kerP H α Λ (δ.symm z) z * (wt H z : ℂ)
      = c * r * ∑ y ∈ S₂, α y * opU H y (fun v => kerP H α Λ v z) z * (wt H z : ℂ) := by
    intro z
    have hm := (kerPTh V H Λ α hU.herm hU.pos hL hU.semi z).2
    have h1 := congrFun (hc _ hm) z
    have h2 := interReps V H hU.herm Λ (imgLat (δ : V →ₗ[ℂ] V) Λ) α hU.semi' _ hm.2 S₂ hS₂ z
    have h3 : pullInv δ (fun v => kerP H α Λ v z) z = kerP H α Λ (δ.symm z) z := rfl
    rw [h3, Pi.smul_apply, h2, ← hr, sumU, smul_eq_mul] at h1
    rw [h1, ← Finset.sum_mul]
    ring
  have hint : ∀ y ∈ S₂, Integrable
      (fun z => α y * opU H y (fun v => kerP H α Λ v z) z * (wt H z : ℂ)) (μ.restrict D') :=
    fun y hy => diag_integrable μ H Λ α hU.herm hU.pos hL hU.semi D' hb y (hU.semi'.1 y (hS₂.1 y hy))
  have hleft := unfoldingIntegral V μ H Λ α δ Ae hL hU D' hD' hb S hS
  rw [(cayleyGaussianIntegral V μ H hU.herm hU.pos δ Ae hU.isom hU.cay).2] at hleft
  rw [← hleft]
  simp_rw [hpt]
  rw [integral_const_mul, integral_finsetSum _ hint]
  have hdiag := diagonalIntegral V μ H Λ (imgLat (δ : V →ₗ[ℂ] V) Λ) α hU.herm hU.pos hL hU.selfDual hsd2
    hU.semi hU.semi' D' hD' hb
  obtain ⟨y₀, hy₀, hy₀Λ, hsum⟩ := Inv.sum_reps hS₂
    (fun y => ∫ z in D', α y * opU H y (fun v => kerP H α Λ v z) z * (wt H z : ℂ) ∂μ)
    (fun y hy hyΛ => by
      have := hdiag y (hS₂.1 y hy)
      rw [if_neg hyΛ] at this
      exact this)
  rw [hsum]
  have := hdiag y₀ (hS₂.1 y₀ hy₀)
  rw [if_pos hy₀Λ] at this
  rw [this]

end UC

end Formalism.L2.Th1.H
