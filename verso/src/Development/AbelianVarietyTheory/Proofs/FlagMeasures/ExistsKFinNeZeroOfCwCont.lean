import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoefExtendsHolomorphically
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CwContIntegralCommStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrechetContinuousContinuousOnOrbitHasDerivAt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

/- English proof (translation)
Take `⟨⟨-, hPJ⟩, hPU⟩` from `hP`. Establish `h1 : Pᴴ * P = 1`. Establish `h` using `Matrix.mem_unitaryGroup_iff'.mp hPU`. Rewrite `h` using `[Matrix.star_eq_conjTranspose]`. Then use the resulting hypothesis. Establish `h2 : P * Pᴴ = 1`.

Establish `h` using `Matrix.mem_unitaryGroup_iff.mp hPU`. Rewrite `h` using `[Matrix.star_eq_conjTranspose]`. Then use the resulting hypothesis. Establish `hcong : ∀ A B : Mx k r, (Pᴴ * A * P) * (Pᴴ * B * P) = Pᴴ * (A * B) * P`. Introduce `A B`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[← Matrix.mul_assoc P Pᴴ, h2, Matrix.one_mul]`. Establish `hherm : ∀ A : Mx k r, (Pᴴ * A * P)ᴴ = Pᴴ * Aᴴ * P`. Introduce `A`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]`. Establish `hJ : Formalism.QuantumDeterminants.Hpk k r = Pᴴ * Formalism.REAL.Jm ε * P` using `hPJ.symm`.

Use `⟨fun x => Pᴴ * Formalism.REAL.toMK x * P, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hc : Continuous (fun x : Formalism.REAL.KG ε => Formalism.REAL.toMK x)` using `Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)`. Conclude with `(continuous_const.matrix_mul hc).matrix_mul continuous_const`. Introduce `x`. Establish `hx : (Formalism.REAL.toMK x)ᴴ * Formalism.REAL.Jm ε * Formalism.REAL.toMK x = Formalism.REAL.Jm ε` using `(x : Formalism.REAL.UJ ε).2`.

Use `show (Pᴴ * Formalism.REAL.toMK x * P)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (Pᴴ * Formalism.REAL.toMK x * P) = Formalism.QuantumDeterminants.Hpk k r`. Rewrite using `[hJ, hherm, hcong, hcong, hx]`. Use `show Pᴴ * Formalism.REAL.toMK (1 : Formalism.REAL.KG ε) * P = 1`. Rewrite using `[show Formalism.REAL.toMK (1 : Formalism.REAL.KG ε) = 1 from rfl, Matrix.mul_one, h1]`. Introduce `x y show Pᴴ * Formalism.REAL.toMK (x * y) * P = (Pᴴ * Formalism.REAL.toMK x * P) * (Pᴴ * Formalism.REAL.toMK y * P)`.

Rewrite using `[hcong]`. Both sides reduce to the same expression. Introduce and unpack `g ⟨hgH, hgU⟩`. Establish `hgH' : gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g = Pᴴ * Formalism.REAL.Jm ε * P`. Establish `h : gᴴ * PI.UpqRep.Hpk k r * g = PI.UpqRep.Hpk k r` using `hgH`.

Rewrite `h` using `[← hPJ]`. Conclude with `h`. Establish `g1 : gᴴ * g = 1`. Establish `h` using `Matrix.mem_unitaryGroup_iff'.mp hgU`. Rewrite `h` using `[Matrix.star_eq_conjTranspose]`. Then use the resulting hypothesis.

Establish `g2 : g * gᴴ = 1`. Establish `h` using `Matrix.mem_unitaryGroup_iff.mp hgU`. Rewrite `h` using `[Matrix.star_eq_conjTranspose]`. Then use the resulting hypothesis. Use `set M := P * g * Pᴴ with hM`. Establish `hMH : Mᴴ = P * gᴴ * Pᴴ`.

Rewrite using `[hM]`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]`. Establish `M1 : Mᴴ * M = 1`. Rewrite using `[hMH, hM]`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[← Matrix.mul_assoc Pᴴ P, h1, Matrix.one_mul, ← Matrix.mul_assoc gᴴ g, g1, Matrix.one_mul, h2]`. Establish `M2 : M * Mᴴ = 1`. Rewrite using `[hMH, hM]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc Pᴴ P, h1, Matrix.one_mul, ← Matrix.mul_assoc g gᴴ, g2, Matrix.one_mul, h2]`.

Establish `MJ : Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hMH, hM]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = P * (Pᴴ * Formalism.REAL.Jm ε * P) * Pᴴ := by rw [hgH']`.

Use `_ = Formalism.REAL.Jm ε := by`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc P Pᴴ, h2, Matrix.one_mul, Matrix.mul_one]`. Establish `MK : M * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * M`. Combine the equalities or inequalities in the displayed calculation.

Establish `MU : M ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ`. Rewrite using `[Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]`. Conclude with `M2`. Set `u : (Mx k r)ˣ` to `⟨M, Mᴴ, M2, M1⟩`. Establish `hu : u ∈ Formalism.REAL.UJ ε` using `MJ`.

Establish `hk : (⟨u, hu⟩ : Formalism.REAL.UJ ε) ∈ Formalism.REAL.KG ε` using `(⟨MU, MK⟩ : M ∈ Formalism.REAL.Kset ε)`. Use `⟨⟨⟨u, hu⟩, hk⟩, ?_⟩` and prove the remaining obligations. Use `show Pᴴ * M * P = g`. Rewrite using `[hM]`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[← Matrix.mul_assoc Pᴴ P, h1, Matrix.one_mul, Matrix.mul_one]`.
-/
theorem exists_param_maxCompact {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Mx k r}
    (hP : PI.UpqRep.IsCayleyU k r ε P) :
    ∃ κ : Formalism.REAL.KG ε → Mx k r, Continuous κ ∧ (∀ x, κ x ∈ GG k r) ∧ κ 1 = 1 ∧
      (∀ x y, κ (x * y) = κ x * κ y) ∧
      ∀ g ∈ PI.UpqRep.UH (PI.UpqRep.Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _),
        ∃ x, κ x = g := by
  obtain ⟨⟨-, hPJ⟩, hPU⟩ := hP
  have h1 : Pᴴ * P = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hPU
    rwa [Matrix.star_eq_conjTranspose] at h
  have h2 : P * Pᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hPU
    rwa [Matrix.star_eq_conjTranspose] at h
  have hcong : ∀ A B : Mx k r, (Pᴴ * A * P) * (Pᴴ * B * P) = Pᴴ * (A * B) * P := by
    intro A B
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P Pᴴ, h2, Matrix.one_mul]
  have hherm : ∀ A : Mx k r, (Pᴴ * A * P)ᴴ = Pᴴ * Aᴴ * P := by
    intro A
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hJ : Formalism.QuantumDeterminants.Hpk k r = Pᴴ * Formalism.REAL.Jm ε * P := hPJ.symm
  refine ⟨fun x => Pᴴ * Formalism.REAL.toMK x * P, ?_, ?_, ?_, ?_, ?_⟩
  · have hc : Continuous (fun x : Formalism.REAL.KG ε => Formalism.REAL.toMK x) :=
      Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
    exact (continuous_const.matrix_mul hc).matrix_mul continuous_const
  · intro x
    have hx : (Formalism.REAL.toMK x)ᴴ * Formalism.REAL.Jm ε * Formalism.REAL.toMK x = Formalism.REAL.Jm ε :=
      (x : Formalism.REAL.UJ ε).2
    show (Pᴴ * Formalism.REAL.toMK x * P)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (Pᴴ * Formalism.REAL.toMK x * P) =
      Formalism.QuantumDeterminants.Hpk k r
    rw [hJ, hherm, hcong, hcong, hx]
  · show Pᴴ * Formalism.REAL.toMK (1 : Formalism.REAL.KG ε) * P = 1
    rw [show Formalism.REAL.toMK (1 : Formalism.REAL.KG ε) = 1 from rfl, Matrix.mul_one, h1]
  · intro x y
    show Pᴴ * Formalism.REAL.toMK (x * y) * P = (Pᴴ * Formalism.REAL.toMK x * P) * (Pᴴ * Formalism.REAL.toMK y * P)
    rw [hcong]
    rfl
  · rintro g ⟨hgH, hgU⟩
    have hgH' : gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g = Pᴴ * Formalism.REAL.Jm ε * P := by
      have h : gᴴ * PI.UpqRep.Hpk k r * g = PI.UpqRep.Hpk k r := hgH
      rw [← hPJ] at h
      exact h
    have g1 : gᴴ * g = 1 := by
      have h := Matrix.mem_unitaryGroup_iff'.mp hgU
      rwa [Matrix.star_eq_conjTranspose] at h
    have g2 : g * gᴴ = 1 := by
      have h := Matrix.mem_unitaryGroup_iff.mp hgU
      rwa [Matrix.star_eq_conjTranspose] at h
    set M := P * g * Pᴴ with hM
    have hMH : Mᴴ = P * gᴴ * Pᴴ := by
      rw [hM]
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    have M1 : Mᴴ * M = 1 := by
      rw [hMH, hM]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Pᴴ P, h1, Matrix.one_mul, ← Matrix.mul_assoc gᴴ g, g1, Matrix.one_mul, h2]
    have M2 : M * Mᴴ = 1 := by
      rw [hMH, hM]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Pᴴ P, h1, Matrix.one_mul, ← Matrix.mul_assoc g gᴴ, g2, Matrix.one_mul, h2]
    have MJ : Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε := by
      calc Mᴴ * Formalism.REAL.Jm ε * M = P * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * Pᴴ := by
            rw [hMH, hM]
            simp only [Matrix.mul_assoc]
        _ = P * (Pᴴ * Formalism.REAL.Jm ε * P) * Pᴴ := by rw [hgH']
        _ = Formalism.REAL.Jm ε := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc P Pᴴ, h2, Matrix.one_mul, Matrix.mul_one]
    have MK : M * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * M := by
      calc M * Formalism.REAL.Jm ε = M * (Mᴴ * Formalism.REAL.Jm ε * M) := by rw [MJ]
        _ = (M * Mᴴ) * Formalism.REAL.Jm ε * M := by simp only [Matrix.mul_assoc]
        _ = Formalism.REAL.Jm ε * M := by rw [M2, Matrix.one_mul]
    have MU : M ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
      exact M2
    let u : (Mx k r)ˣ := ⟨M, Mᴴ, M2, M1⟩
    have hu : u ∈ Formalism.REAL.UJ ε := MJ
    have hk : (⟨u, hu⟩ : Formalism.REAL.UJ ε) ∈ Formalism.REAL.KG ε := (⟨MU, MK⟩ : M ∈ Formalism.REAL.Kset ε)
    refine ⟨⟨⟨u, hu⟩, hk⟩, ?_⟩
    show Pᴴ * M * P = g
    rw [hM]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Pᴴ P, h1, Matrix.one_mul, Matrix.mul_one]

/- English proof (translation)
Introduce `hKS k r ε mu R hR V _ _ _ _ Bm hadd hsmul hcw hex`. Take `⟨v, hv, hBv⟩` from `hex`. Use `haveI : SecondCountableTopology (Formalism.REAL.KG ε) := Topology.IsInducing.subtypeVal.secondCountableTopology`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Take `⟨P, hP, -⟩` from `hR.2`. Take `⟨κ, hκc, hκG, hκ1, hκm, hκs⟩` from `exists_param_maxCompact hP`. Take `⟨hmul, hone, -, -, -, -, -, -, hσc⟩` from `rep_basic_of_isDS hKS k r ε mu R hR`. Establish `hBc` using `(cwCont_continuousOn_hasDerivAt hKS k r ε mu R hR V Bm hadd hsmul hcw v hv).1`. Establish `hf : Continuous (fun x => Bm (R.σ (κ x) v))` using `hBc.comp_continuous hκc hκG`.

Establish `hw : Continuous (fun x => R.σ (κ x) v)` using `(hσc v).comp_continuous hκc hκG`. Establish `hint : ∀ q : Formalism.REAL.KG ε → ℂ, Continuous q → Integrable (fun x => q x • R.σ (κ x) v) (Formalism.REAL.muK ε)` using `fun q hq => (hq.smul hw).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)`. Establish `hsig : ∀ y, ∀ q : Formalism.REAL.KG ε → ℂ, Continuous q → R.σ (κ y) (∫ x, q x • R.σ (κ x) v ∂(Formalism.REAL.muK ε)) = ∫ x, q (y⁻¹ * x) • R.σ (κ x) v ∂(Formalism.REAL.muK ε)`. Introduce `y q hq`. Combine the equalities or inequalities in the displayed calculation.

Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `only [map_smul, inv_mul_cancel_left, hκm, hmul _ (hκG y) _ (hκG x)]`. Use `_ = _ := integral_mul_left_eq_self (μ := Formalism.REAL.muK ε) (fun z => q (y⁻¹ * z) • R.σ (κ z) v) y`. Set `φ : C(Formalism.REAL.KG ε, ℂ)` to `⟨fun x => ⟪Bm v, Bm (R.σ (κ x) v)⟫_ℂ, continuous_const.inner hf⟩`.

Establish `hφ : φ = 0`. Use `KHolExt.eq_zero_of_orth φ (fun p hp => ?_)` and prove the remaining obligations. Take `⟨ι, _, a, b, -, hab⟩` from `hp`. Take `⟨u, hu⟩ : ∃ u, u = ∫ x, p x • R.σ (κ x) v ∂(Formalism.REAL.muK ε)` from `⟨_, rfl⟩`. Take `⟨c, hc⟩ : ∃ c : ι → R.H, ∀ i, c i = ∫ x, b i x • R.σ (κ x) v ∂(Formalism.REAL.muK ε)` from `⟨_, fun _ => rfl⟩`.

Establish `hdec : ∀ y, R.σ (κ y) u = ∑ i, a i y • c i`. Introduce `y`. Rewrite using `[hu, hsig y p p.continuous]`. Establish `hx : ∀ x, p (y⁻¹ * x) • R.σ (κ x) v = ∑ i, a i y • (b i x • R.σ (κ x) v)`. Introduce `x`.

Rewrite using `[hab, Finset.sum_smul]`. Simplify using `only [mul_smul]`. Repeatedly rewrite using `[hx]`. Rewrite using `[integral_finset_sum Finset.univ (f := fun i x => a i y • (b i x • R.σ (κ x) v)) (fun i _ => (hint _ (b i).continuous).smul (a i y))]`. Simplify using `only [integral_smul, hc]`.

Establish `hFT : FiniteDimensional ℂ (Submodule.span ℂ (Set.range c))` using `FiniteDimensional.span_of_finite ℂ (Set.finite_range c)`. Set `S` to `Submodule.span ℂ (Set.range fun y => R.σ (κ y) u)`. Establish `hST : S ≤ Submodule.span ℂ (Set.range c)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨y, rfl⟩`.

Use `show R.σ (κ y) u ∈ Submodule.span ℂ (Set.range c)`. Rewrite using `[hdec y]`. Conclude with `Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))`. Establish `hKF : R.KFin u`. Unfold `BranchingSupport.Rep.KFin PI.UpqRep.IsKFinHpk`.

Use `⟨S, Submodule.finiteDimensional_of_le hST, ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : R.σ (κ 1) u ∈ S` using `Submodule.subset_span ⟨1, rfl⟩`. Rewrite `h1` using `[hκ1, hone]`. Then use the resulting hypothesis. Introduce `g hg x hx`. Take `⟨y', rfl⟩` from `hκs g hg`.

Establish `hmap : S.map (R.σ (κ y') : R.H →ₗ[ℂ] R.H) ≤ S`. Rewrite using `[Submodule.map_span_le]`. Introduce and unpack `_ ⟨y, rfl⟩`. Use `Submodule.subset_span ⟨y' * y, ?_⟩` and prove the remaining obligations. Simplify using `[hκm, hmul _ (hκG y') _ (hκG y)]`.

Conclude with `hmap (Submodule.mem_map_of_mem hx)`. Establish `hus : u ∈ R.sm` using `hKS k r ε mu R.H R.σ hR.1 hR.2 u hKF`. Establish `hB0 : Bm u = 0` using `hcon u hKF`. Establish `hI` using `GlobalTheory.T.cwCont_integral_comm_alt hKS k r ε mu R hR V Bm hadd hsmul hcw (Formalism.REAL.KG ε) (Formalism.REAL.muK ε) κ p hκc hκG p.continuous v hv (hu ▸ hus)`. Establish `hfi : Integrable (fun x => p x • Bm (R.σ (κ x) v)) (Formalism.REAL.muK ε)` using `(p.continuous.smul hf).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)`.

Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `[φ, inner_smul_right]`. Use `_ = innerSL ℂ (Bm v) (∫ x, p x • Bm (R.σ (κ x) v) ∂(Formalism.REAL.muK ε)) := (innerSL ℂ (Bm v)).integral_comp_comm hfi`.

Use `_ = 0 := by rw [← hI, ← hu, hB0, map_zero]`. Establish `h1` using `DFunLike.congr_fun hφ 1`. Express the relevant statement in the definitionally equal form `⟪Bm v, Bm (R.σ (κ 1) v)⟫_ℂ = 0 at h1`. Rewrite `h1` using `[hκ1, hone, inner_self_eq_zero]`. Conclude with `hBv h1`.
-/
theorem exists_kFin_ne_zero_of_cwCont : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (Bm : R.H → V), (∀ v ∈ R.sm, ∀ w ∈ R.sm, Bm (v + w) = Bm v + Bm w) → (∀ (a : ℂ), ∀ v ∈ R.sm, Bm (a • v) = a • Bm v) → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ Bm → (∃ v ∈ R.sm, Bm v ≠ 0) → ∃ x, R.KFin x ∧ Bm x ≠ 0 := by
  intro hKS k r ε mu R hR V _ _ _ _ Bm hadd hsmul hcw hex
  obtain ⟨v, hv, hBv⟩ := hex
  haveI : SecondCountableTopology (Formalism.REAL.KG ε) :=
    Topology.IsInducing.subtypeVal.secondCountableTopology
  by_contra hcon
  push_neg at hcon
  obtain ⟨P, hP, -⟩ := hR.2
  obtain ⟨κ, hκc, hκG, hκ1, hκm, hκs⟩ := exists_param_maxCompact hP
  obtain ⟨hmul, hone, -, -, -, -, -, -, hσc⟩ := rep_basic_of_isDS hKS k r ε mu R hR
  have hBc := (cwCont_continuousOn_hasDerivAt hKS k r ε mu R hR V Bm hadd hsmul hcw v hv).1
  have hf : Continuous (fun x => Bm (R.σ (κ x) v)) := hBc.comp_continuous hκc hκG
  have hw : Continuous (fun x => R.σ (κ x) v) := (hσc v).comp_continuous hκc hκG
  have hint : ∀ q : Formalism.REAL.KG ε → ℂ, Continuous q →
      Integrable (fun x => q x • R.σ (κ x) v) (Formalism.REAL.muK ε) := fun q hq =>
    (hq.smul hw).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsig : ∀ y, ∀ q : Formalism.REAL.KG ε → ℂ, Continuous q →
      R.σ (κ y) (∫ x, q x • R.σ (κ x) v ∂(Formalism.REAL.muK ε)) =
        ∫ x, q (y⁻¹ * x) • R.σ (κ x) v ∂(Formalism.REAL.muK ε) := by
    intro y q hq
    calc R.σ (κ y) (∫ x, q x • R.σ (κ x) v ∂(Formalism.REAL.muK ε))
        = ∫ x, R.σ (κ y) (q x • R.σ (κ x) v) ∂(Formalism.REAL.muK ε) :=
          ((R.σ (κ y)).integral_comp_comm (hint q hq)).symm
      _ = ∫ x, (fun z => q (y⁻¹ * z) • R.σ (κ z) v) (y * x) ∂(Formalism.REAL.muK ε) := by
          congr 1
          funext x
          simp only [map_smul, inv_mul_cancel_left, hκm, hmul _ (hκG y) _ (hκG x)]
      _ = _ := integral_mul_left_eq_self (μ := Formalism.REAL.muK ε) (fun z => q (y⁻¹ * z) • R.σ (κ z) v) y
  let φ : C(Formalism.REAL.KG ε, ℂ) := ⟨fun x => ⟪Bm v, Bm (R.σ (κ x) v)⟫_ℂ, continuous_const.inner hf⟩
  have hφ : φ = 0 := by
    refine KHolExt.eq_zero_of_orth φ (fun p hp => ?_)
    obtain ⟨ι, _, a, b, -, hab⟩ := hp
    obtain ⟨u, hu⟩ : ∃ u, u = ∫ x, p x • R.σ (κ x) v ∂(Formalism.REAL.muK ε) := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c : ι → R.H, ∀ i, c i = ∫ x, b i x • R.σ (κ x) v ∂(Formalism.REAL.muK ε) :=
      ⟨_, fun _ => rfl⟩
    have hdec : ∀ y, R.σ (κ y) u = ∑ i, a i y • c i := by
      intro y
      rw [hu, hsig y p p.continuous]
      have hx : ∀ x, p (y⁻¹ * x) • R.σ (κ x) v = ∑ i, a i y • (b i x • R.σ (κ x) v) := by
        intro x
        rw [hab, Finset.sum_smul]
        simp only [mul_smul]
      simp_rw [hx]
      rw [integral_finset_sum Finset.univ (f := fun i x => a i y • (b i x • R.σ (κ x) v))
        (fun i _ => (hint _ (b i).continuous).smul (a i y))]
      simp only [integral_smul, hc]
    have hFT : FiniteDimensional ℂ (Submodule.span ℂ (Set.range c)) :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_range c)
    let S := Submodule.span ℂ (Set.range fun y => R.σ (κ y) u)
    have hST : S ≤ Submodule.span ℂ (Set.range c) := by
      rw [Submodule.span_le]
      rintro _ ⟨y, rfl⟩
      show R.σ (κ y) u ∈ Submodule.span ℂ (Set.range c)
      rw [hdec y]
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    have hKF : R.KFin u := by
      unfold BranchingSupport.Rep.KFin PI.UpqRep.IsKFinHpk
      refine ⟨S, Submodule.finiteDimensional_of_le hST, ?_, ?_⟩
      · have h1 : R.σ (κ 1) u ∈ S := Submodule.subset_span ⟨1, rfl⟩
        rwa [hκ1, hone] at h1
      · intro g hg x hx
        obtain ⟨y', rfl⟩ := hκs g hg
        have hmap : S.map (R.σ (κ y') : R.H →ₗ[ℂ] R.H) ≤ S := by
          rw [Submodule.map_span_le]
          rintro _ ⟨y, rfl⟩
          refine Submodule.subset_span ⟨y' * y, ?_⟩
          simp [hκm, hmul _ (hκG y') _ (hκG y)]
        exact hmap (Submodule.mem_map_of_mem hx)
    have hus : u ∈ R.sm := hKS k r ε mu R.H R.σ hR.1 hR.2 u hKF
    have hB0 : Bm u = 0 := hcon u hKF
    have hI := GlobalTheory.T.cwCont_integral_comm_alt hKS k r ε mu R hR V Bm hadd hsmul hcw (Formalism.REAL.KG ε) (Formalism.REAL.muK ε) κ p
      hκc hκG p.continuous v hv (hu ▸ hus)
    have hfi : Integrable (fun x => p x • Bm (R.σ (κ x) v)) (Formalism.REAL.muK ε) :=
      (p.continuous.smul hf).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    calc ∫ x, p x * φ x ∂(Formalism.REAL.muK ε)
        = ∫ x, innerSL ℂ (Bm v) (p x • Bm (R.σ (κ x) v)) ∂(Formalism.REAL.muK ε) := by
          congr 1
          funext x
          simp [φ, inner_smul_right]
      _ = innerSL ℂ (Bm v) (∫ x, p x • Bm (R.σ (κ x) v) ∂(Formalism.REAL.muK ε)) :=
          (innerSL ℂ (Bm v)).integral_comp_comm hfi
      _ = 0 := by rw [← hI, ← hu, hB0, map_zero]
  have h1 := DFunLike.congr_fun hφ 1
  change ⟪Bm v, Bm (R.σ (κ 1) v)⟫_ℂ = 0 at h1
  rw [hκ1, hone, inner_self_eq_zero] at h1
  exact hBv h1

end GlobalTheory
