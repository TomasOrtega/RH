import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierCoefficientHolomorphicInBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicHolomorphicFourierExpansionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierCoefficientExponentialDecayLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodCharacterUniformlyAwayFromOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiperiodicDifferenceHolomorphicStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormLeTsumOfCubeFourierCoeffLe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.FamilyFourier
open scoped Real ContDiff

noncomputable section

namespace GlobalTheory.CocycleCore

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}

/- English proof (translation)
Unfold `ch`. Use `fun_prop`.
-/
theorem differentiable_ch (n : Fin g → ℤ) : Differentiable ℂ (ch n) := by
  unfold ch; fun_prop

/- English proof (translation)
Simplify using `[ch]`.
-/
theorem ch_zero (z : Fin g → ℂ) : ch (0 : Fin g → ℤ) z = 1 := by simp [ch]

/- English proof (translation)
Simplify using `[cov]`.
-/
theorem mem_cov {V : Set E} {P : Pt E g} : P ∈ cov V g ↔ P.1 ∈ V := by simp [cov]

/- English proof (translation)
Rewrite using `[differentiableOn_pi]`. Introduce `j`. Simplify using `only [per, Pi.add_apply, vecMul, dotProduct]`. Use `DifferentiableOn.add ?_ (differentiableOn_const _)` and prove the remaining obligations. Use `DifferentiableOn.fun_sum fun i _ => ?_` and prove the remaining obligations.

Conclude with `(differentiableOn_const _).mul (hτ.2.1 i j)`.
-/
theorem differentiableOn_per {U : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}
    (hτ : IsPeriodMap U τ) (x : Fl g) : DifferentiableOn ℂ (fun b => per (τ b) x) U := by
  rw [differentiableOn_pi]
  intro j
  simp only [per, Pi.add_apply, vecMul, dotProduct]
  refine DifferentiableOn.add ?_ (differentiableOn_const _)
  refine DifferentiableOn.fun_sum fun i _ => ?_
  exact (differentiableOn_const _).mul (hτ.2.1 i j)

def kc (h : Fin g → Pt E g → ℂ) (τ : E → Matrix (Fin g) (Fin g) ℂ)
    (κ : (n : Fin g → ℤ) → n ≠ 0 → Fin g) (n : Fin g → ℤ) (b : E) : ℂ :=
  if hn : n = 0 then 0 else
    coef (h (κ n hn)) n b / (ch n (per (τ b) (Pi.single (Sum.inl (κ n hn)) (1 : ℝ))) - 1)

/- English proof (translation)
Simplify using `[kc]`.
-/
theorem kc_zero (h : Fin g → Pt E g → ℂ) (τ : E → Matrix (Fin g) (Fin g) ℂ)
    (κ : (n : Fin g → ℤ) → n ≠ 0 → Fin g) (b : E) : kc h τ κ 0 b = 0 := by
  simp [kc]

end GlobalTheory.CocycleCore

open GlobalTheory.CocycleCore in
/- English proof (translation)
Introduce `g E _ _ _ U τ hτ h hh hper hcoc b hb`. Establish `hU : IsOpen U` using `hτ.1`. Take `⟨V, hVo, hbV, hVU, δ, hδ, hrow⟩` from `GlobalTheory.T.period_character_uniformly_away_from_one hτ b hb`. Use `choose κ hκ using hrow`. Establish `hcovV : IsOpen (cov V g)` using `hVo.prod isOpen_univ`.

Establish `hsub : cov V g ⊆ cov U g` using `fun P hP => mem_cov.2 (hVU (mem_cov.1 hP))`. Establish `hne : ∀ n (hn : n ≠ 0), ∀ b ∈ V, ch n (per (τ b) (Pi.single (Sum.inl (κ n hn)) (1 : ℝ))) - 1 ≠ 0`. Introduce `n hn b hb h0`. Use `hκ n hn b hb` as an intermediate fact. Rewrite `this` using `[h0, norm_zero]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hrel : ∀ n, n ≠ 0 → ∀ m, ∀ b ∈ V, kc h τ κ n b * (ch n (per (τ b) (Pi.single (Sum.inl m) (1 : ℝ))) - 1) = coef (h m) n b`. Introduce `n hn m b hb`. Establish `key` using `GlobalTheory.T.quasiperiodic_difference_holomorphic (h (κ n hn)) (h m) (fun b => per (τ b) (Pi.single (Sum.inl (κ n hn)) (1 : ℝ))) (fun b => per (τ b) (Pi.single (Sum.inl m) (1 : ℝ))) hU (hh _) (hh _) (hper _) (hper _) (fun P hP => hcoc (κ n hn) m P hP) b (hVU hb) n`. Simplify using `only [kc, dif_neg hn]`.

Rewrite using `[div_mul_eq_mul_div, key, mul_div_assoc, div_self (hne n hn b hb), mul_one]`. Establish `hkc : ∀ n, DifferentiableOn ℂ (kc h τ κ n) V`. Introduce `n`. Distinguish the cases in `hn : n = 0`. Substitute `hn` using the available equality.

Establish `: kc h τ κ 0 = fun _ => 0` using `funext fun b => kc_zero h τ κ b`. Rewrite using `[this]`. Conclude with `differentiableOn_const _`. Establish `: kc h τ κ n = fun b => coef (h (κ n hn)) n b / (ch n (per (τ b) (Pi.single (Sum.inl (κ n hn)) (1 : ℝ))) - 1)`. Use function extensionality and compare the values at `b`.

Simplify using `only [kc, dif_neg hn]`. Rewrite using `[this]`. Simplify using `only [div_eq_mul_inv]`. Use `((GlobalTheory.T.fourier_coefficient_holomorphic_in_base _ hU (hh _) n).mono hVU).mul (DifferentiableOn.inv ?_ (hne n hn))` and prove the remaining obligations. Conclude with `(((differentiable_ch n).comp_differentiableOn (differentiableOn_per hτ _)).mono hVU).sub (differentiableOn_const _)`.

Establish `hF : ∀ n, DifferentiableOn ℂ (fun P : Pt E g => kc h τ κ n P.1 * ch n P.2) (cov V g)`. Introduce `n`. Conclude with `((hkc n).comp differentiableOn_fst (fun P hP => mem_cov.1 hP)).mul ((differentiable_ch n).comp differentiable_snd).differentiableOn`. Establish `hle : ∀ x ∈ cov V g, ∃ t ∈ nhds x, ∃ u : (Fin g → ℤ) → ℝ, Summable u ∧ ∀ n, ∀ P ∈ t, ‖kc h τ κ n P.1 * ch n P.2‖ ≤ u n`. Introduce `x hx`.

Establish `hx1 : x.1 ∈ U` using `hVU (mem_cov.1 hx)`. Establish `hb` using `fun k => GlobalTheory.T.fourier_coefficient_exponential_decay_local (h k) hU (hh k) (hper k) x.1 hx1 x.2`. Use `choose t ht C hC using hb`. Use `⟨cov V g ∩ ⋂ k, t k, Filter.inter_mem (hcovV.mem_nhds hx) (Filter.iInter_mem.2 ht), fun n => (∑ k, |C k|) * Real.exp (-(2 * π * ∑ i, |(n i : ℝ)|)) / δ, ((GlobalTheory.Koecher.summable_exp_neg_mul_sum_abs (ι := Fin g) (by positivity : (0:ℝ) < 2 * π)).mul_left (∑ k, |C k|)).div_con …` and prove the remaining obligations. Introduce `n P hP`.

Establish `hPV : P.1 ∈ V` using `mem_cov.1 hP.1`. Distinguish the cases in `hn : n = 0`. Substitute `hn` using the available equality. Rewrite using `[kc_zero, zero_mul, norm_zero]`. Check the signs of the components of the expression.

Establish `heq : kc h τ κ n P.1 * ch n P.2 = coef (h (κ n hn)) n P.1 * ch n P.2 / (ch n (per (τ P.1) (Pi.single (Sum.inl (κ n hn)) (1 : ℝ))) - 1)`. Simplify using `only [kc, dif_neg hn]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[heq, norm_div]`. Establish `h1` using `hC (κ n hn) n P (Set.mem_iInter.1 hP.2 (κ n hn))`.

Establish `h2 : C (κ n hn) ≤ ∑ k, |C k|` using `(le_abs_self _).trans (Finset.single_le_sum (f := fun k => |C k|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _))`. Establish `h3` using `hκ n hn P.1 hPV`. Establish `he : 0 ≤ Real.exp (-(2 * π * ∑ i, |(n i : ℝ)|))` using `(Real.exp_pos _).le`. Use `show _ ≤ (∑ k, |C k|) * Real.exp (-(2 * π * ∑ i, |(n i : ℝ)|)) / δ`. Conclude with `div_le_div₀ (by positivity) (h1.trans (mul_le_mul_of_nonneg_right h2 he)) hδ h3`.

Establish `hsumm : ∀ P ∈ cov V g, Summable (fun n => kc h τ κ n P.1 * ch n P.2)`. Introduce `P hP`. Take `⟨t, ht, u, hu, hbd⟩` from `hle P hP`. Conclude with `Summable.of_norm_bounded hu (fun n => hbd n P (mem_of_mem_nhds ht))`. Use `⟨V, hVo, hbV, hVU, fun P => ∑' n, kc h τ κ n P.1 * ch n P.2, GlobalTheory.SCV.differentiableOn_tsum_of_locally_normal hcovV hF hle, ?_, fun k => coef (h k) 0, fun k => (GlobalTheory.T.fourier_coefficient_holomorphic_in_base _ hU (hh k) 0).mono hVU, ?_⟩` and prove the remaining obligations.

Introduce `P _ i`. Use `tsum_congr fun n => ?_` and prove the remaining obligations. Simplify using `only [ch_add, ch_single, mul_one]`. Introduce `m P hP`. Establish `hP' : transl τ (Pi.single (Sum.inl m) (1 : ℝ)) P ∈ cov V g` using `mem_cov.2 (mem_cov.1 hP)`.

Establish `hG : HasSum (fun n => kc h τ κ n P.1 * ch n (P.2 + per (τ P.1) (Pi.single (Sum.inl m) (1 : ℝ))) - kc h τ κ n P.1 * ch n P.2) (h m P - coef (h m) 0 P.1)`. Establish `h1` using `(GlobalTheory.T.periodic_holomorphic_fourier_expansion (h m) hU (hh m) (hper m) P (hsub hP)).update 0 0`. Establish `hfun : (fun n => kc h τ κ n P.1 * ch n (P.2 + per (τ P.1) (Pi.single (Sum.inl m) (1 : ℝ))) - kc h τ κ n P.1 * ch n P.2) = Function.update (fun n => coef (h m) n P.1 * ch n P.2) 0 0`. Use function extensionality and compare the values at `n`. Distinguish the cases in `hn : n = 0`.

Substitute `hn` using the available equality. Simplify using `[kc_zero]`. Rewrite using `[Function.update_of_ne hn, ← hrel n hn m P.1 (mem_cov.1 hP), ch_add]`. Expand and normalize the polynomial expressions, which then agree. Establish `hval : h m P - coef (h m) 0 P.1 = 0 - (fun n => coef (h m) n P.1 * ch n P.2) 0 + h m P`.

Simplify using `only [ch_zero]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hfun, hval]`. Conclude with `h1`. Establish `h2 : HasSum (fun n => kc h τ κ n P.1 * ch n (P.2 + per (τ P.1) (Pi.single (Sum.inl m) (1 : ℝ))) - kc h τ κ n P.1 * ch n P.2) ((∑' n, kc h τ κ n P.1 * ch n (P.2 + per (τ P.1) (Pi.single (Sum.inl m) (1 : ℝ)))) - ∑' n, kc h τ κ n P.1 * ch n P.2)` using `(hsumm _ hP').hasSum.sub (hsumm _ hP).hasSum`.

Use `hG.unique h2` as an intermediate fact. Use `show h m P = (∑' n, kc h τ κ n P.1 * ch n (P.2 + per (τ P.1) (Pi.single (Sum.inl m) (1 : ℝ)))) - (∑' n, kc h τ κ n P.1 * ch n P.2) + coef (h m) 0 P.1`. Take the linear combination `this`.
-/
theorem GlobalTheory.cocycle_core_local_solution : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {U : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap U τ → ∀ h : Fin g → Pt E g → ℂ, (∀ k, DifferentiableOn ℂ (h k) (cov U g)) → (∀ k, ∀ P ∈ cov U g, ∀ i : Fin g, h k (P.1, P.2 + Pi.single i 1) = h k P) → (∀ k m, ∀ P ∈ cov U g, h k (transl τ (Pi.single (Sum.inl m) (1 : ℝ)) P) - h k P = h m (transl τ (Pi.single (Sum.inl k) (1 : ℝ)) P) - h m P) → ∀ b ∈ U, ∃ V : Set E, IsOpen V ∧ b ∈ V ∧ V ⊆ U ∧ ∃ K : Pt E g → ℂ, DifferentiableOn ℂ K (cov V g) ∧ (∀ P ∈ cov V g, ∀ i : Fin g, K (P.1, P.2 + Pi.single i 1) = K P) ∧ ∃ c : Fin g → E → ℂ, (∀ k, DifferentiableOn ℂ (c k) V) ∧ ∀ k, ∀ P ∈ cov V g, h k P = K (transl τ (Pi.single (Sum.inl k) (1 : ℝ)) P) - K P + c k P.1 := by
  intro g E _ _ _ U τ hτ h hh hper hcoc b hb
  have hU : IsOpen U := hτ.1
  obtain ⟨V, hVo, hbV, hVU, δ, hδ, hrow⟩ := GlobalTheory.T.period_character_uniformly_away_from_one hτ b hb
  choose κ hκ using hrow
  have hcovV : IsOpen (cov V g) := hVo.prod isOpen_univ
  have hsub : cov V g ⊆ cov U g := fun P hP => mem_cov.2 (hVU (mem_cov.1 hP))

  have hne : ∀ n (hn : n ≠ 0), ∀ b ∈ V,
      ch n (per (τ b) (Pi.single (Sum.inl (κ n hn)) (1 : ℝ))) - 1 ≠ 0 := by
    intro n hn b hb h0
    have := hκ n hn b hb
    rw [h0, norm_zero] at this
    linarith

  have hrel : ∀ n, n ≠ 0 → ∀ m, ∀ b ∈ V,
      kc h τ κ n b * (ch n (per (τ b) (Pi.single (Sum.inl m) (1 : ℝ))) - 1) = coef (h m) n b := by
    intro n hn m b hb
    have key := GlobalTheory.T.quasiperiodic_difference_holomorphic (h (κ n hn)) (h m)
      (fun b => per (τ b) (Pi.single (Sum.inl (κ n hn)) (1 : ℝ)))
      (fun b => per (τ b) (Pi.single (Sum.inl m) (1 : ℝ))) hU (hh _) (hh _) (hper _) (hper _)
      (fun P hP => hcoc (κ n hn) m P hP) b (hVU hb) n
    simp only [kc, dif_neg hn]
    rw [div_mul_eq_mul_div, key, mul_div_assoc, div_self (hne n hn b hb), mul_one]

  have hkc : ∀ n, DifferentiableOn ℂ (kc h τ κ n) V := by
    intro n
    by_cases hn : n = 0
    · subst hn
      have : kc h τ κ 0 = fun _ => 0 := funext fun b => kc_zero h τ κ b
      rw [this]
      exact differentiableOn_const _
    · have : kc h τ κ n = fun b => coef (h (κ n hn)) n b /
          (ch n (per (τ b) (Pi.single (Sum.inl (κ n hn)) (1 : ℝ))) - 1) := by
        funext b; simp only [kc, dif_neg hn]
      rw [this]
      simp only [div_eq_mul_inv]
      refine ((GlobalTheory.T.fourier_coefficient_holomorphic_in_base _ hU (hh _) n).mono hVU).mul (DifferentiableOn.inv ?_ (hne n hn))
      exact (((differentiable_ch n).comp_differentiableOn (differentiableOn_per hτ _)).mono hVU).sub
        (differentiableOn_const _)
  have hF : ∀ n, DifferentiableOn ℂ (fun P : Pt E g => kc h τ κ n P.1 * ch n P.2) (cov V g) := by
    intro n
    exact ((hkc n).comp differentiableOn_fst (fun P hP => mem_cov.1 hP)).mul
      ((differentiable_ch n).comp differentiable_snd).differentiableOn

  have hle : ∀ x ∈ cov V g, ∃ t ∈ nhds x, ∃ u : (Fin g → ℤ) → ℝ, Summable u ∧
      ∀ n, ∀ P ∈ t, ‖kc h τ κ n P.1 * ch n P.2‖ ≤ u n := by
    intro x hx
    have hx1 : x.1 ∈ U := hVU (mem_cov.1 hx)
    have hb := fun k => GlobalTheory.T.fourier_coefficient_exponential_decay_local (h k) hU (hh k) (hper k) x.1 hx1 x.2
    choose t ht C hC using hb
    refine ⟨cov V g ∩ ⋂ k, t k, Filter.inter_mem (hcovV.mem_nhds hx) (Filter.iInter_mem.2 ht),
      fun n => (∑ k, |C k|) * Real.exp (-(2 * π * ∑ i, |(n i : ℝ)|)) / δ,
      ((GlobalTheory.Koecher.summable_exp_neg_mul_sum_abs (ι := Fin g) (by positivity : (0:ℝ) < 2 * π)).mul_left
        (∑ k, |C k|)).div_const δ, ?_⟩
    intro n P hP
    have hPV : P.1 ∈ V := mem_cov.1 hP.1
    by_cases hn : n = 0
    · subst hn
      rw [kc_zero, zero_mul, norm_zero]
      positivity
    · have heq : kc h τ κ n P.1 * ch n P.2 = coef (h (κ n hn)) n P.1 * ch n P.2 /
          (ch n (per (τ P.1) (Pi.single (Sum.inl (κ n hn)) (1 : ℝ))) - 1) := by
        simp only [kc, dif_neg hn]; ring
      rw [heq, norm_div]
      have h1 := hC (κ n hn) n P (Set.mem_iInter.1 hP.2 (κ n hn))
      have h2 : C (κ n hn) ≤ ∑ k, |C k| := (le_abs_self _).trans
        (Finset.single_le_sum (f := fun k => |C k|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _))
      have h3 := hκ n hn P.1 hPV
      have he : 0 ≤ Real.exp (-(2 * π * ∑ i, |(n i : ℝ)|)) := (Real.exp_pos _).le
      show _ ≤ (∑ k, |C k|) * Real.exp (-(2 * π * ∑ i, |(n i : ℝ)|)) / δ
      exact div_le_div₀ (by positivity) (h1.trans (mul_le_mul_of_nonneg_right h2 he)) hδ h3
  have hsumm : ∀ P ∈ cov V g, Summable (fun n => kc h τ κ n P.1 * ch n P.2) := by
    intro P hP
    obtain ⟨t, ht, u, hu, hbd⟩ := hle P hP
    exact Summable.of_norm_bounded hu (fun n => hbd n P (mem_of_mem_nhds ht))
  refine ⟨V, hVo, hbV, hVU, fun P => ∑' n, kc h τ κ n P.1 * ch n P.2,
    GlobalTheory.SCV.differentiableOn_tsum_of_locally_normal hcovV hF hle, ?_,
    fun k => coef (h k) 0, fun k => (GlobalTheory.T.fourier_coefficient_holomorphic_in_base _ hU (hh k) 0).mono hVU, ?_⟩
  ·
    intro P _ i
    refine tsum_congr fun n => ?_
    simp only [ch_add, ch_single, mul_one]
  ·
    intro m P hP
    have hP' : transl τ (Pi.single (Sum.inl m) (1 : ℝ)) P ∈ cov V g := mem_cov.2 (mem_cov.1 hP)
    have hG : HasSum (fun n => kc h τ κ n P.1 * ch n (P.2 + per (τ P.1) (Pi.single (Sum.inl m) (1 : ℝ)))
        - kc h τ κ n P.1 * ch n P.2) (h m P - coef (h m) 0 P.1) := by
      have h1 := (GlobalTheory.T.periodic_holomorphic_fourier_expansion (h m) hU (hh m) (hper m) P (hsub hP)).update 0 0
      have hfun : (fun n => kc h τ κ n P.1 * ch n (P.2 + per (τ P.1) (Pi.single (Sum.inl m) (1 : ℝ)))
          - kc h τ κ n P.1 * ch n P.2) = Function.update (fun n => coef (h m) n P.1 * ch n P.2) 0 0 := by
        funext n
        by_cases hn : n = 0
        · subst hn
          simp [kc_zero]
        · rw [Function.update_of_ne hn, ← hrel n hn m P.1 (mem_cov.1 hP), ch_add]
          ring
      have hval : h m P - coef (h m) 0 P.1 = 0 - (fun n => coef (h m) n P.1 * ch n P.2) 0 + h m P := by
        simp only [ch_zero]; ring
      rw [hfun, hval]
      exact h1
    have h2 : HasSum (fun n => kc h τ κ n P.1 * ch n (P.2 + per (τ P.1) (Pi.single (Sum.inl m) (1 : ℝ)))
        - kc h τ κ n P.1 * ch n P.2)
        ((∑' n, kc h τ κ n P.1 * ch n (P.2 + per (τ P.1) (Pi.single (Sum.inl m) (1 : ℝ)))) -
          ∑' n, kc h τ κ n P.1 * ch n P.2) :=
      (hsumm _ hP').hasSum.sub (hsumm _ hP).hasSum
    have := hG.unique h2
    show h m P = (∑' n, kc h τ κ n P.1 * ch n (P.2 + per (τ P.1) (Pi.single (Sum.inl m) (1 : ℝ)))) -
      (∑' n, kc h τ κ n P.1 * ch n P.2) + coef (h m) 0 P.1
    linear_combination this
