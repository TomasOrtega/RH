import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InSOfParts
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts

set_option autoImplicit false
noncomputable section
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.ShFam

namespace GlobalTheory.RegEst.Close

/- English proof (translation)
Establish `hab : ∀ τ i, |u τ i| ≤ ‖u‖` using `fun τ i => by`. Rewrite using `[← Real.norm_eq_abs]`. Conclude with `(norm_le_pi_norm (u τ) i).trans (norm_le_pi_norm u τ)`. Establish `hn : 0 ≤ ‖u‖` using `norm_nonneg _`. Establish `term : ∀ τ (i : Fin N), coef u τ i * f τ i ≤ 2 * ‖u‖ * B` using `fun τ i => by`.

Distinguish the cases in `hi : (i : ℕ) + 1 < N`. Establish `h1 : 0 ≤ coef u τ i` using `coef_nonneg (fun τ a b hab => hu τ a b hab) τ hi`. Establish `h2 : coef u τ i ≤ 2 * ‖u‖`. Rewrite using `[coef, dif_pos hi]`. Use `hab τ i` as an intermediate fact.

Use `hab τ ⟨i + 1, hi⟩` as an intermediate fact. Use `le_abs_self (u τ i)` as an intermediate fact. Use `neg_abs_le (u τ ⟨i + 1, hi⟩)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[h₀ τ i hi, mul_zero]`. Check the signs of the components of the expression. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_coef_mul_le {ι : Type} [Fintype ι] {N : ℕ} (u : ι → Fin N → ℝ) (hu : Dom u) (f : ι → Fin N → ℝ) {B : ℝ}
    (hB : 0 ≤ B) (h₀ : ∀ τ (i : Fin N), ¬ (i : ℕ) + 1 < N → f τ i = 0)
    (hf : ∀ τ (i : Fin N), (i : ℕ) + 1 < N → f τ i ≤ B) :
    ∑ τ, ∑ i, coef u τ i * f τ i ≤ 2 * ((Fintype.card ι : ℝ) * N) * ‖u‖ * B := by
  have hab : ∀ τ i, |u τ i| ≤ ‖u‖ := fun τ i => by
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm (u τ) i).trans (norm_le_pi_norm u τ)
  have hn : 0 ≤ ‖u‖ := norm_nonneg _
  have term : ∀ τ (i : Fin N), coef u τ i * f τ i ≤ 2 * ‖u‖ * B := fun τ i => by
    by_cases hi : (i : ℕ) + 1 < N
    · have h1 : 0 ≤ coef u τ i := coef_nonneg (fun τ a b hab => hu τ a b hab) τ hi
      have h2 : coef u τ i ≤ 2 * ‖u‖ := by
        rw [coef, dif_pos hi]
        have := hab τ i
        have := hab τ ⟨i + 1, hi⟩
        have := le_abs_self (u τ i)
        have := neg_abs_le (u τ ⟨i + 1, hi⟩)
        linarith
      calc coef u τ i * f τ i ≤ coef u τ i * B := mul_le_mul_of_nonneg_left (hf τ i hi) h1
        _ ≤ 2 * ‖u‖ * B := mul_le_mul_of_nonneg_right h2 hB
    · rw [h₀ τ i hi, mul_zero]
      positivity
  calc ∑ τ, ∑ i, coef u τ i * f τ i ≤ ∑ _τ : ι, ∑ _i : Fin N, 2 * ‖u‖ * B :=
        Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => term τ i
    _ = 2 * ((Fintype.card ι : ℝ) * N) * ‖u‖ * B := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/- English proof (translation)
Establish `hr0 : 0 < r` using `(Real.exp_pos 1).trans_le (hl.trans hr)`. Establish `h` using `Real.log_div_self_antitoneOn (show l ∈ {x : ℝ | Real.exp 1 ≤ x} from hl) (show r ∈ {x : ℝ | Real.exp 1 ≤ x} from hl.trans hr) hr`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem log_le_div_mul {l r : ℝ} (hl : Real.exp 1 ≤ l) (hr : l ≤ r) : Real.log r ≤ Real.log l / l * r := by
  have hr0 : 0 < r := (Real.exp_pos 1).trans_le (hl.trans hr)
  have h := Real.log_div_self_antitoneOn (show l ∈ {x : ℝ | Real.exp 1 ≤ x} from hl)
    (show r ∈ {x : ℝ | Real.exp 1 ≤ x} from hl.trans hr) hr
  calc Real.log r = Real.log r / r * r := by field_simp
    _ ≤ Real.log l / l * r := mul_le_mul_of_nonneg_right h hr0.le

end GlobalTheory.RegEst.Close

namespace GlobalTheory.RegEst

open Close in

/- English proof (translation)
Introduce `hS hL hC D O hO hN A T H h c`. Take `⟨x, P, hc⟩` from `hO`. Establish `hex : ∃ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y), Nonempty (O.Reads A T H)` using `⟨A, T, H, ⟨h⟩⟩`. Take `⟨C₁, hC₁, hS⟩` from `hS D O x P hc hN hex`. Take `⟨C₂, t₂, hC₂, ht₂, hL⟩` from `hL D O x P hc hN hex`.

Take `⟨t₃, ht₃, hC⟩` from `hC D O x P hc hN hex`. Establish `hA` using `h.an c`. Use `set K : ℝ := (Fintype.card D.what₂.Tau : ℝ) * O.N with hK`. Establish `hK0 : 0 ≤ K` using `by positivity`. Use `set L₀ : ℝ := max 3 (max (-Real.log t₂) (-Real.log t₃)) with hL₀`.

Establish `hL₀3 : 3 ≤ L₀` using `le_max_left _ _`. Establish `hL₀2 : -Real.log t₂ ≤ L₀` using `(le_max_left _ _).trans (le_max_right _ _)`. Establish `hL₀3' : -Real.log t₃ ≤ L₀` using `(le_max_right _ _).trans (le_max_right _ _)`. Establish `hL₀pos : 0 < L₀` using `by linarith`. Use `⟨(Real.sqrt L₀)⁻¹, by positivity, K * (1 + C₁ + C₂), fun C hC0 u hu s hs hss l hl a => ?_⟩` and prove the remaining obligations.

Establish `hlL : L₀ ≤ l`. Establish `h1 : s ^ 2 ≤ L₀⁻¹`. Combine the equalities or inequalities in the displayed calculation. Establish `h2` using `inv_anti₀ (by positivity) h1`. Rewrite `h2` using `[inv_inv, ← hl]`. Then use the resulting hypothesis.

Establish `hl3 : 3 ≤ l` using `hL₀3.trans hlL`. Establish `hle : Real.exp 1 ≤ l` using `by have := Real.exp_one_lt_d9; linarith`. Use `set t := Real.exp (-l) with ht`. Establish `htpos : 0 < t` using `Real.exp_pos _`. Establish `ht2 : t ≤ t₂`.

Rewrite using `[ht, ← Real.exp_log ht₂]`. Conclude with `Real.exp_le_exp.2 (by linarith)`. Establish `ht3 : t ≤ t₃`. Rewrite using `[ht, ← Real.exp_log ht₃]`. Conclude with `Real.exp_le_exp.2 (by linarith)`.

Establish `hlog : Real.log (1 / t) = l` using `by rw [ht, one_div, ← Real.exp_neg, neg_neg, Real.log_exp]`. Establish `hcube : t ^ ((1 : ℝ) / 3) = Real.exp (-l / 3)`. Rewrite using `[ht, ← Real.exp_mul]`. Put the polynomial expressions in normal form. Establish `hts : Real.exp (-(s ^ 2)⁻¹) = t` using `by rw [ht, hl]`.

Establish `hKC : K ≤ C` using `by nlinarith [mul_nonneg hK0 (add_nonneg hC₁ hC₂)]`. Establish `hKC2 : K * (C₁ + C₂) ≤ C` using `by nlinarith`. Establish `hC0' : 0 ≤ C` using `hK0.trans hKC`. Establish `hn : 0 ≤ ‖u‖` using `norm_nonneg u`. Establish `hq0 : 0 ≤ Real.log l / l` using `div_nonneg (Real.log_nonneg (by linarith)) (by linarith)`.

Establish `hex0 : 0 ≤ Real.exp (-l / 3)` using `(Real.exp_pos _).le`. Introduce `z hz`. Establish `hy : (h.man c).pt a z ∈ offBd O.Φ c ((h.man c).ε a)` using `fun hb => hz ((hA.Z a z).2 hb)`. Establish `hr : (T.M c).r a z = O.met.r c ((h.man c).ε a) ((h.man c).pt a z)` using `hA.r a z hz`. Establish `hr1 : 1 ≤ Real.log (O.met.r c ((h.man c).ε a) ((h.man c).pt a z))`.

Use `Setup.Core.exp_le_r ⟨x, P, hc⟩ c ((h.man c).ε a) ((h.man c).pt a z)` as an intermediate fact. Establish `h2` using `Real.log_le_log (Real.exp_pos 1) this`. Rewrite `h2` using `[Real.log_exp]`. Then use the resulting hypothesis. Establish `key : (T.F c).phS u s a z - (T.F c).ph u a z = (∑ τ, ∑ i, coef u τ i * (P.regFund c ((h.man c).ε a) τ i t ((h.man c).pt a z) - phW (metsOf x O.Φ) (refMet x O.Φ) c ((h.man c).ε a) (fund τ i) ((h.man c).pt a z))) / 2`. Rewrite using `[hA.phS u s hs a z, hA.ph u a z hz, hts, hc.reg_eq]`.

Establish `e` using `hc.two_mul_chg c u ((h.man c).ε a) ((h.man c).pt a z)`. Establish `e2 : P.reg c ((h.man c).ε a) u t ((h.man c).pt a z) - phW (metsOf x O.Φ) (refMet x O.Φ) c ((h.man c).ε a) u ((h.man c).pt a z) = ∑ τ, ∑ i, coef u τ i * (P.regFund c ((h.man c).ε a) τ i t ((h.man c).pt a z) - phW (metsOf x O.Φ) (refMet x O.Φ) c ((h.man c).ε a) (fund τ i) ((h.man c …`. Establish `e3` using `phW_eq_sum (metsOf x O.Φ) (refMet x O.Φ) c ((h.man c).ε a) u ((h.man c).pt a z)`. Unfold `PolDat.reg`. Use `erw [e3, ← Finset.sum_sub_distrib]`.

Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => (mul_sub _ _ _).symm`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h₀ : ∀ τ (i : Fin O.N), ¬ (i : ℕ) + 1 < O.N → P.regFund c ((h.man c).ε a) τ i t ((h.man c).pt a z) - phW (metsOf x O.Φ) (refMet x O.Φ) c ((h.man c).ε a) (fund τ i) ((h.man c).pt a z) = 0` using `fun τ i hi => by`.

Simplify using `[PolDat.regFund, hi, extBd, hy]`. Establish `near : (T.M c).r a z ≤ l → (T.F c).phS u s a z - (T.F c).ph u a z ≤ K * ‖u‖ * Real.exp (-l / 3)`. Introduce `hrl`. Establish `hsum : (∑ τ, ∑ i, coef u τ i * (P.regFund c ((h.man c).ε a) τ i t ((h.man c).pt a z) - phW (metsOf x O.Φ) (refMet x O.Φ) c ((h.man c).ε a) (fund τ i) ((h.man c).pt a z))) ≤ 2 * K * ‖u‖ * Real.exp (-l / 3)` using `sum_coef_mul_le u hu _ hex0 h₀ fun τ i hi => by`. Use `hC t htpos ht3 c ((h.man c).ε a) τ i hi _ hy (by rw [← hr, hlog]; exact hrl)` as an intermediate fact.

Rewrite `this` using `[hcube]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[key]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `far : (T.F c).phS u s a z - (T.F c).ph u a z ≤ K * ‖u‖ * ((C₁ + C₂) * Real.log (O.met.r c ((h.man c).ε a) ((h.man c).pt a z)))`.

Establish `hB : 0 ≤ (C₁ + C₂) * Real.log (O.met.r c ((h.man c).ε a) ((h.man c).pt a z))` using `mul_nonneg (add_nonneg hC₁ hC₂) (by linarith)`. Establish `hsum : (∑ τ, ∑ i, coef u τ i * (P.regFund c ((h.man c).ε a) τ i t ((h.man c).pt a z) - phW (metsOf x O.Φ) (refMet x O.Φ) c ((h.man c).ε a) (fund τ i) ((h.man c).pt a z))) ≤ 2 * K * ‖u‖ * ((C₁ + C₂) * Real.log (O.met.r c ((h.man c).ε a) ((h.man c).pt a z)))` using `sum_coef_mul_le u hu _ hB h₀ fun τ i hi => by`. Take `⟨-, hup, -⟩` from `hL t htpos ht2 c ((h.man c).ε a) τ i hi ((h.man c).pt a z)`. Take `⟨hlo, -⟩` from `hS c ((h.man c).ε a) τ i _ hy`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hr1 hC₂]`.

Rewrite using `[key]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨fun hrl => ?_, ?_⟩` and prove the remaining obligations. Use `near hrl` as an intermediate fact. Establish `h1 : K * ‖u‖ * Real.exp (-l / 3) ≤ C * ‖u‖ * Real.exp (-l / 3)` using `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKC hn) hex0`.

Establish `h2 : 0 ≤ C * ‖u‖ * (Real.log l / l)` using `mul_nonneg (mul_nonneg hC0' hn) hq0`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1 : K * ‖u‖ * Real.exp (-l / 3) ≤ C * ‖u‖ * Real.exp (-l / 3)` using `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKC hn) hex0`. Establish `hr0 : 0 ≤ (T.M c).r a z` using `by rw [hr]; linarith [Real.exp_pos 1, Setup.Core.exp_le_r ⟨x, P, hc⟩ c ((h.man c).ε a) ((h.man c).pt a z)]`. Establish `h2 : 0 ≤ C * ‖u‖ * (Real.log l / l) * (T.M c).r a z` using `mul_nonneg (mul_nonneg (mul_nonneg hC0' hn) hq0) hr0`.

Break down `le_or_gt ((T.M c).r a z) l with hrl | hrl` into its components or cases. Use `near hrl` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `far` as an intermediate fact. Establish `h3` using `log_le_div_mul hle (hr ▸ hrl.le)`.

Rewrite `h3`, `this` using `[← hr]`. Establish `h4 : K * ‖u‖ * ((C₁ + C₂) * Real.log ((T.M c).r a z)) ≤ C * ‖u‖ * (Real.log l / l) * (T.M c).r a z`. Establish `h5` using `mul_le_mul_of_nonneg_left h3 (mul_nonneg (mul_nonneg hK0 hn) (add_nonneg hC₁ hC₂))`. Establish `h6` using `mul_le_mul_of_nonneg_right hKC2 (mul_nonneg (mul_nonneg hn hq0) hr0)`. Combine the equalities or inequalities in the displayed calculation.

Establish `h7 : 0 ≤ C * ‖u‖ * Real.exp (-l / 3)` using `mul_nonneg (mul_nonneg hC0' hn) hex0`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem closePart_of_steps : SizeSt → LowSt → CloseSt → OnObj fun _ _ _ T _ _ => ∀ c, GlobalTheory.RegEst.ClosePart (T.F c) := by
  intro hS hL hC D O hO hN A T H h c
  obtain ⟨x, P, hc⟩ := hO
  have hex : ∃ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y), Nonempty (O.Reads A T H) := ⟨A, T, H, ⟨h⟩⟩
  obtain ⟨C₁, hC₁, hS⟩ := hS D O x P hc hN hex
  obtain ⟨C₂, t₂, hC₂, ht₂, hL⟩ := hL D O x P hc hN hex
  obtain ⟨t₃, ht₃, hC⟩ := hC D O x P hc hN hex
  have hA := h.an c
  set K : ℝ := (Fintype.card D.what₂.Tau : ℝ) * O.N with hK
  have hK0 : 0 ≤ K := by positivity
  set L₀ : ℝ := max 3 (max (-Real.log t₂) (-Real.log t₃)) with hL₀
  have hL₀3 : 3 ≤ L₀ := le_max_left _ _
  have hL₀2 : -Real.log t₂ ≤ L₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hL₀3' : -Real.log t₃ ≤ L₀ := (le_max_right _ _).trans (le_max_right _ _)
  have hL₀pos : 0 < L₀ := by linarith
  refine ⟨(Real.sqrt L₀)⁻¹, by positivity, K * (1 + C₁ + C₂), fun C hC0 u hu s hs hss l hl a => ?_⟩
  have hlL : L₀ ≤ l := by
    have h1 : s ^ 2 ≤ L₀⁻¹ := by
      calc s ^ 2 ≤ ((Real.sqrt L₀)⁻¹) ^ 2 := pow_le_pow_left₀ hs.le hss 2
        _ = L₀⁻¹ := by rw [inv_pow, Real.sq_sqrt hL₀pos.le]
    have h2 := inv_anti₀ (by positivity) h1
    rwa [inv_inv, ← hl] at h2
  have hl3 : 3 ≤ l := hL₀3.trans hlL
  have hle : Real.exp 1 ≤ l := by have := Real.exp_one_lt_d9; linarith
  set t := Real.exp (-l) with ht
  have htpos : 0 < t := Real.exp_pos _
  have ht2 : t ≤ t₂ := by
    rw [ht, ← Real.exp_log ht₂]
    exact Real.exp_le_exp.2 (by linarith)
  have ht3 : t ≤ t₃ := by
    rw [ht, ← Real.exp_log ht₃]
    exact Real.exp_le_exp.2 (by linarith)
  have hlog : Real.log (1 / t) = l := by rw [ht, one_div, ← Real.exp_neg, neg_neg, Real.log_exp]
  have hcube : t ^ ((1 : ℝ) / 3) = Real.exp (-l / 3) := by
    rw [ht, ← Real.exp_mul]
    ring_nf
  have hts : Real.exp (-(s ^ 2)⁻¹) = t := by rw [ht, hl]
  have hKC : K ≤ C := by nlinarith [mul_nonneg hK0 (add_nonneg hC₁ hC₂)]
  have hKC2 : K * (C₁ + C₂) ≤ C := by nlinarith
  have hC0' : 0 ≤ C := hK0.trans hKC
  have hn : 0 ≤ ‖u‖ := norm_nonneg u
  have hq0 : 0 ≤ Real.log l / l := div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
  have hex0 : 0 ≤ Real.exp (-l / 3) := (Real.exp_pos _).le
  intro z hz
  have hy : (h.man c).pt a z ∈ offBd O.Φ c ((h.man c).ε a) := fun hb => hz ((hA.Z a z).2 hb)
  have hr : (T.M c).r a z = O.met.r c ((h.man c).ε a) ((h.man c).pt a z) := hA.r a z hz
  have hr1 : 1 ≤ Real.log (O.met.r c ((h.man c).ε a) ((h.man c).pt a z)) := by
    have := Setup.Core.exp_le_r ⟨x, P, hc⟩ c ((h.man c).ε a) ((h.man c).pt a z)
    have h2 := Real.log_le_log (Real.exp_pos 1) this
    rwa [Real.log_exp] at h2

  have key : (T.F c).phS u s a z - (T.F c).ph u a z = (∑ τ, ∑ i, coef u τ i *
      (P.regFund c ((h.man c).ε a) τ i t ((h.man c).pt a z) -
        phW (metsOf x O.Φ) (refMet x O.Φ) c ((h.man c).ε a) (fund τ i) ((h.man c).pt a z))) / 2 := by
    rw [hA.phS u s hs a z, hA.ph u a z hz, hts, hc.reg_eq]
    have e := hc.two_mul_chg c u ((h.man c).ε a) ((h.man c).pt a z)
    have e2 : P.reg c ((h.man c).ε a) u t ((h.man c).pt a z) -
        phW (metsOf x O.Φ) (refMet x O.Φ) c ((h.man c).ε a) u ((h.man c).pt a z) = ∑ τ, ∑ i, coef u τ i *
          (P.regFund c ((h.man c).ε a) τ i t ((h.man c).pt a z) -
            phW (metsOf x O.Φ) (refMet x O.Φ) c ((h.man c).ε a) (fund τ i) ((h.man c).pt a z)) := by
      have e3 := phW_eq_sum (metsOf x O.Φ) (refMet x O.Φ) c ((h.man c).ε a) u ((h.man c).pt a z)
      unfold PolDat.reg
      erw [e3, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => (mul_sub _ _ _).symm
    linarith
  have h₀ : ∀ τ (i : Fin O.N), ¬ (i : ℕ) + 1 < O.N → P.regFund c ((h.man c).ε a) τ i t ((h.man c).pt a z) -
      phW (metsOf x O.Φ) (refMet x O.Φ) c ((h.man c).ε a) (fund τ i) ((h.man c).pt a z) = 0 := fun τ i hi => by
    simp [PolDat.regFund, hi, extBd, hy]

  have near : (T.M c).r a z ≤ l → (T.F c).phS u s a z - (T.F c).ph u a z ≤ K * ‖u‖ * Real.exp (-l / 3) := by
    intro hrl
    have hsum : (∑ τ, ∑ i, coef u τ i *
        (P.regFund c ((h.man c).ε a) τ i t ((h.man c).pt a z) -
          phW (metsOf x O.Φ) (refMet x O.Φ) c ((h.man c).ε a) (fund τ i) ((h.man c).pt a z))) ≤ 2 * K * ‖u‖ * Real.exp (-l / 3) := sum_coef_mul_le u hu _ hex0 h₀ fun τ i hi => by
      have := hC t htpos ht3 c ((h.man c).ε a) τ i hi _ hy (by rw [← hr, hlog]; exact hrl)
      rw [hcube] at this
      linarith
    rw [key]
    linarith

  have far : (T.F c).phS u s a z - (T.F c).ph u a z ≤
      K * ‖u‖ * ((C₁ + C₂) * Real.log (O.met.r c ((h.man c).ε a) ((h.man c).pt a z))) := by
    have hB : 0 ≤ (C₁ + C₂) * Real.log (O.met.r c ((h.man c).ε a) ((h.man c).pt a z)) :=
      mul_nonneg (add_nonneg hC₁ hC₂) (by linarith)
    have hsum : (∑ τ, ∑ i, coef u τ i *
        (P.regFund c ((h.man c).ε a) τ i t ((h.man c).pt a z) -
          phW (metsOf x O.Φ) (refMet x O.Φ) c ((h.man c).ε a) (fund τ i) ((h.man c).pt a z))) ≤ 2 * K * ‖u‖ * ((C₁ + C₂) * Real.log (O.met.r c ((h.man c).ε a) ((h.man c).pt a z))) := sum_coef_mul_le u hu _ hB h₀ fun τ i hi => by
      obtain ⟨-, hup, -⟩ := hL t htpos ht2 c ((h.man c).ε a) τ i hi ((h.man c).pt a z)
      obtain ⟨hlo, -⟩ := hS c ((h.man c).ε a) τ i _ hy
      nlinarith [mul_le_mul_of_nonneg_left hr1 hC₂]
    rw [key]
    linarith
  refine ⟨fun hrl => ?_, ?_⟩
  · have := near hrl
    have h1 : K * ‖u‖ * Real.exp (-l / 3) ≤ C * ‖u‖ * Real.exp (-l / 3) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKC hn) hex0
    have h2 : 0 ≤ C * ‖u‖ * (Real.log l / l) := mul_nonneg (mul_nonneg hC0' hn) hq0
    linarith
  · have h1 : K * ‖u‖ * Real.exp (-l / 3) ≤ C * ‖u‖ * Real.exp (-l / 3) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKC hn) hex0
    have hr0 : 0 ≤ (T.M c).r a z := by rw [hr]; linarith [Real.exp_pos 1, Setup.Core.exp_le_r ⟨x, P, hc⟩ c ((h.man c).ε a) ((h.man c).pt a z)]
    have h2 : 0 ≤ C * ‖u‖ * (Real.log l / l) * (T.M c).r a z := mul_nonneg (mul_nonneg (mul_nonneg hC0' hn) hq0) hr0
    rcases le_or_gt ((T.M c).r a z) l with hrl | hrl
    · have := near hrl
      linarith
    · have := far
      have h3 := log_le_div_mul hle (hr ▸ hrl.le)
      rw [← hr] at h3 this
      have h4 : K * ‖u‖ * ((C₁ + C₂) * Real.log ((T.M c).r a z)) ≤
          C * ‖u‖ * (Real.log l / l) * (T.M c).r a z := by
        have h5 := mul_le_mul_of_nonneg_left h3 (mul_nonneg (mul_nonneg hK0 hn) (add_nonneg hC₁ hC₂))
        have h6 := mul_le_mul_of_nonneg_right hKC2 (mul_nonneg (mul_nonneg hn hq0) hr0)
        calc K * ‖u‖ * ((C₁ + C₂) * Real.log ((T.M c).r a z))
            = K * ‖u‖ * (C₁ + C₂) * Real.log ((T.M c).r a z) := by ring
          _ ≤ K * ‖u‖ * (C₁ + C₂) * (Real.log l / l * (T.M c).r a z) := h5
          _ = K * (C₁ + C₂) * (‖u‖ * (Real.log l / l) * (T.M c).r a z) := by ring
          _ ≤ C * (‖u‖ * (Real.log l / l) * (T.M c).r a z) := h6
          _ = C * ‖u‖ * (Real.log l / l) * (T.M c).r a z := by ring
      have h7 : 0 ≤ C * ‖u‖ * Real.exp (-l / 3) := mul_nonneg (mul_nonneg hC0' hn) hex0
      linarith

end GlobalTheory.RegEst
