import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCharacterContinuousUnit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CircleZero

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.CfFJ

open Metric Set

variable {D : D7} {n ρ p : ℕ}

/- English proof (translation)
Take `⟨hc, -⟩` from `GlobalTheory.CompanionTheory.CoefWeight.continuous_norm_coefChar D ρ ψ hψ b₀`. Establish `h1 : ∀ z : hermA D ρ, conj (chz ψ b₀ z) = ψ (-halfTr (Matrix.trace (HMul.hMul (b₀.1.map (incA D)) z.1 : Mx D ρ ρ)))`. Introduce `z`. Rewrite using `[AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ.2.1 _)]`. Both sides reduce to the same expression.

Use `⟨by simpa only [h1] using hc, fun z => ?_⟩` and prove the remaining obligations. Rewrite using `[RCLike.norm_conj]`. Conclude with `hψ.2.1 _`.
-/
theorem conj_chz (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) :
    Continuous (fun z : hermA D ρ => conj (chz ψ b₀ z)) ∧ ∀ z : hermA D ρ, ‖conj (chz ψ b₀ z)‖ = 1 := by
  obtain ⟨hc, -⟩ := GlobalTheory.CompanionTheory.CoefWeight.continuous_norm_coefChar D ρ ψ hψ b₀
  have h1 : ∀ z : hermA D ρ, conj (chz ψ b₀ z) =
      ψ (-halfTr (Matrix.trace (HMul.hMul (b₀.1.map (incA D)) z.1 : Mx D ρ ρ))) := by
    intro z
    rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ.2.1 _)]
    rfl
  refine ⟨by simpa only [h1] using hc, fun z => ?_⟩
  rw [RCLike.norm_conj]
  exact hψ.2.1 _

/- English proof (translation)
Establish `h : ∀ w : ℂ, ((2 * Real.pi * Complex.I)⁻¹ * ((w - s₀) ^ (k - 1) / d.eval w)) * E w g = (2 * Real.pi * Complex.I)⁻¹ * ((w - s₀) ^ (k - 1) * (E w g / d.eval w))` using `fun w => by ring`. Simplify using `only [h, circleIntegral.integral_const_mul, cf]`.
-/
theorem cf_eq (d : Polynomial ℂ) (E : ℂ → G D n → ℂ) (s₀ : ℂ) (ε : ℝ) (k : ℕ) (g : G D n) :
    cf d E s₀ ε k g = ∮ w in C(s₀, ε),
      ((2 * Real.pi * Complex.I)⁻¹ * ((w - s₀) ^ (k - 1) / d.eval w)) * E w g := by
  have h : ∀ w : ℂ, ((2 * Real.pi * Complex.I)⁻¹ * ((w - s₀) ^ (k - 1) / d.eval w)) * E w g =
      (2 * Real.pi * Complex.I)⁻¹ * ((w - s₀) ^ (k - 1) * (E w g / d.eval w)) := fun w => by ring
  simp only [h, circleIntegral.integral_const_mul, cf]

/- English proof (translation)
Establish `h : ∀ w : ℂ, ((2 * Real.pi * Complex.I)⁻¹ * ((w - s₀) ^ (k - 1) / d.eval w)) * F w = (2 * Real.pi * Complex.I)⁻¹ * ((w - s₀) ^ (k - 1) * (F w / d.eval w))` using `fun w => by ring`. Simplify using `only [h, circleIntegral.integral_const_mul]`.
-/
theorem ker_eq (d : Polynomial ℂ) (F : ℂ → ℂ) (s₀ : ℂ) (ε : ℝ) (k : ℕ) :
    ∮ w in C(s₀, ε), ((2 * Real.pi * Complex.I)⁻¹ * ((w - s₀) ^ (k - 1) / d.eval w)) * F w =
      (2 * Real.pi * Complex.I)⁻¹ * ∮ w in C(s₀, ε), (w - s₀) ^ (k - 1) * (F w / d.eval w) := by
  have h : ∀ w : ℂ, ((2 * Real.pi * Complex.I)⁻¹ * ((w - s₀) ^ (k - 1) / d.eval w)) * F w =
      (2 * Real.pi * Complex.I)⁻¹ * ((w - s₀) ^ (k - 1) * (F w / d.eval w)) := fun w => by ring
  simp only [h, circleIntegral.integral_const_mul]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `hPc D n H φ s₀ U d E σ hC ε hR`. Take `⟨hε, hB, hroot⟩` from `hR`. Establish `hU` using `hC.isOpen`. Establish `hS : sphere s₀ ε ⊆ U` using `sphere_subset_closedBall.trans hB`. Establish `hsne : ∀ z ∈ sphere s₀ ε, z ≠ s₀`.

Introduce and unpack `z hz rfl`. Simplify using `[hε.ne] at hz`. Use `set a : ℕ → ℂ → ℂ := fun k w => (2 * Real.pi * Complex.I)⁻¹ * ((w - s₀) ^ (k - 1) / d.eval w) with ha_def`. Establish `ha : ∀ k, ContinuousOn (a k) (sphere s₀ ε)` using `fun k => continuousOn_const.mul (((continuousOn_id.sub continuousOn_const).pow _).div d.continuous.continuousOn (fun z hz => hroot z (sphere_subset_closedBall hz) (hsne z hz)))`. Establish `hcf : ∀ k g, cf d E s₀ ε k g = ∮ w in C(s₀, ε), a k w * E w g` using `fun k g => cf_eq d E s₀ ε k g`.

Use `⟨fun k => ⟨?_, ?_⟩, ⟨d.rootMultiplicity s₀ + 1, fun k hk => funext fun g => ?_⟩, ?_⟩` and prove the remaining obligations. Establish `: cf d E s₀ ε k = fun g => ∮ w in C(s₀, ε), a k w * E w g` using `funext (hcf k)`. Rewrite using `[this]`. Conclude with `circle_cont hC.cont hε.le hS (ha k)`. Introduce `γ hγ g`.

Rewrite using `[hcf, hcf]`. Conclude with `circleIntegral.integral_congr hε.le fun w hw => by`. Simplify using `only [hC.inv w (hS hw) γ hγ g]`. Establish `h0` using `circle_zero hU (hC.hol g) hC.ne hε hB hroot (j := k - 1) (by omega)`. Simplify using `only [cf, h0, mul_zero, Pi.zero_apply]`.

Introduce `ρ p hn M m ψ hψ b₀ g η hη`. Take `⟨-, hcov⟩` from `hPc D n ρ p hn M m ψ hψ b₀`. Take `⟨C, hCc, hcover, -⟩` from `hcov g`. Take `⟨i1, i2, i3, i4, -, -⟩` from `lattice_Mx D ρ p`. Use `haveI : BorelSpace (Mx D ρ p) := ⟨rfl⟩`.

Use `haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩`. Use `haveI : BorelSpace (hermA D ρ) := Subtype.borelSpace _`. Use `haveI : FirstCountableTopology (Mx D ρ p) := inferInstance`. Use `haveI : FirstCountableTopology (Mx D ρ p × Mx D ρ p) := inferInstance`. Take `⟨hμh, -, hμ1⟩` from `m.hμ`.

Take `⟨-, -, hl1⟩` from `m.hz`. Use `haveI : SFinite m.μ := inferInstance`. Use `haveI : IsFiniteMeasure (m.lz.restrict m.𝓖) := ⟨by rw [Measure.restrict_apply_univ, hl1]; exact ENNReal.one_lt_top⟩`. Use `haveI : IsFiniteMeasure (m.μ.restrict m.𝓕) := ⟨by rw [Measure.restrict_apply_univ, hμ1]; exact ENNReal.one_lt_top⟩`. Take `⟨hχc, hχ1⟩` from `conj_chz ψ hψ b₀`.

Establish `hκ1 : Integrable (fun z : hermA D ρ => conj (chz ψ b₀ z)) (m.lz.restrict m.𝓖)` using `Integrable.of_bound hχc.aestronglyMeasurable 1 (Eventually.of_forall fun z => (hχ1 z).le)`. Establish `hκ2 : Integrable (fun _ : Mx D ρ p => (1 : ℂ)) (m.μ.restrict m.𝓕)` using `integrable_const _`. Establish `hκ3 : Integrable (fun y => conj (η y)) m.μ` using `Complex.conjCLE.toContinuousLinearMap.integrable_comp hη`. Use `set pt : (Mx D ρ p × Mx D ρ p) × hermA D ρ → G D n := fun u => M.nzx u.2 0 * (M.nzx 0 u.1.2 * (M.sh u.1.1 * g)) with hpt_def`. Establish `hpt : Continuous pt` using `(M.nzx_cont.comp (f := fun u : (Mx D ρ p × Mx D ρ p) × hermA D ρ => (u.2, (0 : Mx D ρ p))) (by fun_prop)).mul ((M.nzx_cont.comp (f := fun u : (Mx D ρ p × Mx D ρ p) × hermA D ρ => ((0 : hermA D ρ), u.1.2)) (by fun_prop)).mul ((M.sh_cont.comp (f := fun u : (Mx D ρ p × Mx D ρ p) × h …`.

Establish `h0 : Fam U (fun w u => E w (pt u))`. Use `⟨hC.cont.comp (continuous_fst.prodMk (hpt.comp continuous_snd)).continuousOn (fun q hq => ⟨hq.1, mem_univ _⟩), fun u => hC.hol _, fun K hK hKc => ?_⟩` and prove the remaining obligations. Take `⟨B, hBd⟩` from `(hKc.prod hCc).exists_bound_of_continuousOn (hC.cont.mono (prod_mono hK (subset_univ _)))`. Use `⟨B, fun w hw u => ?_⟩` and prove the remaining obligations. Take `⟨γ, hγ, hmem⟩` from `hcover u.2 u.1.2 u.1.1`.

Rewrite using `[show E w (pt u) = E w (γ * pt u) from (hC.inv w (hK hw) γ hγ _).symm]`. Conclude with `hBd (w, γ * pt u) ⟨hw, hmem⟩`. Establish `h1 : Fam U (fun w (u : Mx D ρ p × Mx D ρ p) => zc M m ψ b₀ (E w) (M.nzx 0 u.2 * (M.sh u.1 * g)))` using `h0.stage hU hκ1`. Establish `h2 : Fam U (fun w (y : Mx D ρ p) => pc M m ψ b₀ (E w) (M.sh y * g))`. Use `h1.stage hU hκ2` as an intermediate fact.

Simplify using `only [mul_one] at this`. Conclude with `this`. Establish `h3 : Fam U (fun w (_ : Unit) => FJ M m ψ b₀ (E w) g η)` using `(h2.comp (φ := fun u : Unit × Mx D ρ p => u.2) continuous_snd).stage hU hκ3`. Use `⟨h3.hol (), fun k => ?_⟩` and prove the remaining obligations. Establish `e1 : ∀ y x, zc M m ψ b₀ (cf d E s₀ ε k) (M.nzx 0 x * (M.sh y * g)) = ∮ w in C(s₀, ε), a k w * zc M m ψ b₀ (E w) (M.nzx 0 x * (M.sh y * g))`.

Introduce `y x`. Use `(h0.comp (φ := fun z : hermA D ρ => ((y, x), z)) (by fun_prop)).swap hκ1 hε hS (ha k)` as an intermediate fact. Simplify using `only [zc, hcf, pt] at this ⊢`. Conclude with `this`. Establish `e2 : ∀ y, pc M m ψ b₀ (cf d E s₀ ε k) (M.sh y * g) = ∮ w in C(s₀, ε), a k w * pc M m ψ b₀ (E w) (M.sh y * g)`.

Introduce `y`. Use `(h1.comp (φ := fun x : Mx D ρ p => (y, x)) (by fun_prop)).swap hκ2 hε hS (ha k)` as an intermediate fact. Simplify using `only [mul_one] at this`. Simplify using `only [PositivityTheory.Rg.Rsw.pc, e1]`. Conclude with `this`.

Establish `e3 : FJ M m ψ b₀ (cf d E s₀ ε k) g η = ∮ w in C(s₀, ε), a k w * FJ M m ψ b₀ (E w) g η`. Use `h2.swap hκ3 hε hS (ha k)` as an intermediate fact. Simplify using `only [FJ, e2]`. Conclude with `this`. Rewrite using `[e3]`.

Conclude with `ker_eq d _ s₀ ε k`.
-/
theorem cfFJ_of_pcBound : PcBound → CfFJ := by
  intro hPc D n H φ s₀ U d E σ hC ε hR
  obtain ⟨hε, hB, hroot⟩ := hR
  have hU := hC.isOpen
  have hS : sphere s₀ ε ⊆ U := sphere_subset_closedBall.trans hB
  have hsne : ∀ z ∈ sphere s₀ ε, z ≠ s₀ := by
    rintro z hz rfl
    simp [hε.ne] at hz
  set a : ℕ → ℂ → ℂ := fun k w => (2 * Real.pi * Complex.I)⁻¹ * ((w - s₀) ^ (k - 1) / d.eval w) with ha_def
  have ha : ∀ k, ContinuousOn (a k) (sphere s₀ ε) := fun k =>
    continuousOn_const.mul (((continuousOn_id.sub continuousOn_const).pow _).div
      d.continuous.continuousOn (fun z hz => hroot z (sphere_subset_closedBall hz) (hsne z hz)))
  have hcf : ∀ k g, cf d E s₀ ε k g = ∮ w in C(s₀, ε), a k w * E w g := fun k g => cf_eq d E s₀ ε k g
  refine ⟨fun k => ⟨?_, ?_⟩, ⟨d.rootMultiplicity s₀ + 1, fun k hk => funext fun g => ?_⟩, ?_⟩
  · have : cf d E s₀ ε k = fun g => ∮ w in C(s₀, ε), a k w * E w g := funext (hcf k)
    rw [this]
    exact circle_cont hC.cont hε.le hS (ha k)
  · intro γ hγ g
    rw [hcf, hcf]
    exact circleIntegral.integral_congr hε.le fun w hw => by
      simp only [hC.inv w (hS hw) γ hγ g]
  · have h0 := circle_zero hU (hC.hol g) hC.ne hε hB hroot (j := k - 1) (by omega)
    simp only [cf, h0, mul_zero, Pi.zero_apply]
  · intro ρ p hn M m ψ hψ b₀ g η hη
    obtain ⟨-, hcov⟩ := hPc D n ρ p hn M m ψ hψ b₀
    obtain ⟨C, hCc, hcover, -⟩ := hcov g
    obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D ρ p
    haveI : BorelSpace (Mx D ρ p) := ⟨rfl⟩
    haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
    haveI : BorelSpace (hermA D ρ) := Subtype.borelSpace _
    haveI : FirstCountableTopology (Mx D ρ p) := inferInstance
    haveI : FirstCountableTopology (Mx D ρ p × Mx D ρ p) := inferInstance
    obtain ⟨hμh, -, hμ1⟩ := m.hμ
    obtain ⟨-, -, hl1⟩ := m.hz
    haveI : SFinite m.μ := inferInstance
    haveI : IsFiniteMeasure (m.lz.restrict m.𝓖) := ⟨by rw [Measure.restrict_apply_univ, hl1]; exact ENNReal.one_lt_top⟩
    haveI : IsFiniteMeasure (m.μ.restrict m.𝓕) := ⟨by rw [Measure.restrict_apply_univ, hμ1]; exact ENNReal.one_lt_top⟩
    obtain ⟨hχc, hχ1⟩ := conj_chz ψ hψ b₀
    have hκ1 : Integrable (fun z : hermA D ρ => conj (chz ψ b₀ z)) (m.lz.restrict m.𝓖) :=
      Integrable.of_bound hχc.aestronglyMeasurable 1 (Eventually.of_forall fun z => (hχ1 z).le)
    have hκ2 : Integrable (fun _ : Mx D ρ p => (1 : ℂ)) (m.μ.restrict m.𝓕) := integrable_const _
    have hκ3 : Integrable (fun y => conj (η y)) m.μ :=
      Complex.conjCLE.toContinuousLinearMap.integrable_comp hη
    set pt : (Mx D ρ p × Mx D ρ p) × hermA D ρ → G D n :=
      fun u => M.nzx u.2 0 * (M.nzx 0 u.1.2 * (M.sh u.1.1 * g)) with hpt_def
    have hpt : Continuous pt :=
      (M.nzx_cont.comp (f := fun u : (Mx D ρ p × Mx D ρ p) × hermA D ρ => (u.2, (0 : Mx D ρ p))) (by fun_prop)).mul
        ((M.nzx_cont.comp (f := fun u : (Mx D ρ p × Mx D ρ p) × hermA D ρ => ((0 : hermA D ρ), u.1.2)) (by fun_prop)).mul
          ((M.sh_cont.comp (f := fun u : (Mx D ρ p × Mx D ρ p) × hermA D ρ => u.1.1) (by fun_prop)).mul continuous_const))
    have h0 : Fam U (fun w u => E w (pt u)) := by
      refine ⟨hC.cont.comp (continuous_fst.prodMk (hpt.comp continuous_snd)).continuousOn
        (fun q hq => ⟨hq.1, mem_univ _⟩), fun u => hC.hol _, fun K hK hKc => ?_⟩
      obtain ⟨B, hBd⟩ := (hKc.prod hCc).exists_bound_of_continuousOn
        (hC.cont.mono (prod_mono hK (subset_univ _)))
      refine ⟨B, fun w hw u => ?_⟩
      obtain ⟨γ, hγ, hmem⟩ := hcover u.2 u.1.2 u.1.1
      rw [show E w (pt u) = E w (γ * pt u) from (hC.inv w (hK hw) γ hγ _).symm]
      exact hBd (w, γ * pt u) ⟨hw, hmem⟩
    have h1 : Fam U (fun w (u : Mx D ρ p × Mx D ρ p) => zc M m ψ b₀ (E w) (M.nzx 0 u.2 * (M.sh u.1 * g))) :=
      h0.stage hU hκ1
    have h2 : Fam U (fun w (y : Mx D ρ p) => pc M m ψ b₀ (E w) (M.sh y * g)) := by
      have := h1.stage hU hκ2
      simp only [mul_one] at this
      exact this
    have h3 : Fam U (fun w (_ : Unit) => FJ M m ψ b₀ (E w) g η) :=
      (h2.comp (φ := fun u : Unit × Mx D ρ p => u.2) continuous_snd).stage hU hκ3
    refine ⟨h3.hol (), fun k => ?_⟩
    have e1 : ∀ y x, zc M m ψ b₀ (cf d E s₀ ε k) (M.nzx 0 x * (M.sh y * g)) =
        ∮ w in C(s₀, ε), a k w * zc M m ψ b₀ (E w) (M.nzx 0 x * (M.sh y * g)) := by
      intro y x
      have := (h0.comp (φ := fun z : hermA D ρ => ((y, x), z)) (by fun_prop)).swap hκ1 hε hS (ha k)
      simp only [zc, hcf, pt] at this ⊢
      exact this
    have e2 : ∀ y, pc M m ψ b₀ (cf d E s₀ ε k) (M.sh y * g) =
        ∮ w in C(s₀, ε), a k w * pc M m ψ b₀ (E w) (M.sh y * g) := by
      intro y
      have := (h1.comp (φ := fun x : Mx D ρ p => (y, x)) (by fun_prop)).swap hκ2 hε hS (ha k)
      simp only [mul_one] at this
      simp only [PositivityTheory.Rg.Rsw.pc, e1]
      exact this
    have e3 : FJ M m ψ b₀ (cf d E s₀ ε k) g η = ∮ w in C(s₀, ε), a k w * FJ M m ψ b₀ (E w) g η := by
      have := h2.swap hκ3 hε hS (ha k)
      simp only [FJ, e2]
      exact this
    rw [e3]
    exact ker_eq d _ s₀ ε k

end GlobalTheory.CompanionTheory.CfFJ
