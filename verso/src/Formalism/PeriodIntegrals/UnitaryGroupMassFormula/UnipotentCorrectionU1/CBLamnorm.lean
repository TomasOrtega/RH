import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.CADwlSmooth

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
open Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def hhF (k j ρ a b : ℕ) (g : B.Mat k (j + ρ)) : ℂ := (DjU k j ρ g)⁻¹ ^ a * (star (DjU k j ρ g))⁻¹ ^ b

/- English proof (translation)
Establish `e1 : star (Complex.exp ((t : ℂ) * c)) = Complex.exp ((t : ℂ) * conj c)`. Rewrite using `[Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal]`. Rewrite using `[star_mul', e1, mul_inv, mul_inv, mul_pow, mul_pow, ← Complex.exp_neg, ← Complex.exp_neg, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]`. Establish `: Complex.exp ((t : ℂ) * -((a : ℂ) * c + (b : ℂ) * conj c)) = Complex.exp ((a : ℂ) * -((t : ℂ) * c)) * Complex.exp ((b : ℂ) * -((t : ℂ) * conj c))`. Rewrite using `[← Complex.exp_add]`.

Put the polynomial expressions in normal form. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cB_alg (a b : ℕ) (c D : ℂ) (t : ℝ) :
    (Complex.exp ((t : ℂ) * c) * D)⁻¹ ^ a * (star (Complex.exp ((t : ℂ) * c) * D))⁻¹ ^ b =
      Complex.exp ((t : ℂ) * -((a : ℂ) * c + (b : ℂ) * conj c)) * (D⁻¹ ^ a * (star D)⁻¹ ^ b) := by
  have e1 : star (Complex.exp ((t : ℂ) * c)) = Complex.exp ((t : ℂ) * conj c) := by
    rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal]
  rw [star_mul', e1, mul_inv, mul_inv, mul_pow, mul_pow, ← Complex.exp_neg, ← Complex.exp_neg,
    ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  have : Complex.exp ((t : ℂ) * -((a : ℂ) * c + (b : ℂ) * conj c)) =
      Complex.exp ((a : ℂ) * -((t : ℂ) * c)) * Complex.exp ((b : ℂ) * -((t : ℂ) * conj c)) := by
    rw [← Complex.exp_add]; ring_nf
  rw [this]; ring

/- English proof (translation)
Rewrite using `[norm_neg]`. Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast, Complex.norm_conj]`. Use `push_cast`. Establish `ha : (0 : ℝ) ≤ a` using `by positivity`.

Establish `hb : (0 : ℝ) ≤ b` using `by positivity`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hc ha, mul_le_mul_of_nonneg_left hc hb]`.
-/
theorem cB_lamnorm (a b : ℕ) (c : ℂ) {j : ℕ} {m : ℝ} (hc : ‖c‖ ≤ (j : ℝ) * m) :
    ‖-((a : ℂ) * c + (b : ℂ) * conj c)‖ ≤ ((a + b : ℕ) : ℝ) * j * m := by
  rw [norm_neg]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast, Complex.norm_conj]
  push_cast
  have ha : (0 : ℝ) ≤ a := by positivity
  have hb : (0 : ℝ) ≤ b := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hc ha, mul_le_mul_of_nonneg_left hc hb]

/- English proof (translation)
Establish `key : ∀ x : Bool × B.Mat k (j + ρ), ∃ μ : ℂ, inLieP k j ρ x.2 → ‖μ‖ ≤ ((a + b : ℕ) : ℝ) * j * mx x.2 ∧ ∀ (g : B.Mat k (j + ρ)) (t : ℝ), hhF k j ρ a b (crv x g t) = Complex.exp ((t : ℂ) * μ) * hhF k j ρ a b g`. Introduce and unpack `⟨bb, Y⟩`. Distinguish the cases in `hY : inLieP k j ρ Y`. Take `⟨c₁, c₂, h₁, h₂, hcur⟩` from `hC k j ρ Y hY`. Consider the cases of `bb`.

Use `⟨-((a : ℂ) * c₁ + (b : ℂ) * conj c₁), fun _ => ⟨cB_lamnorm a b c₁ h₁, fun g t => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[show crv (false, Y) g t = g * NormedSpace.exp ((t : ℂ) • Y) from rfl]`. Unfold `hhF`. Rewrite using `[(hcur g t).1, cB_alg]`. Use `⟨-((a : ℂ) * c₂ + (b : ℂ) * conj c₂), fun _ => ⟨cB_lamnorm a b c₂ h₂, fun g t => ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[show crv (true, Y) g t = NormedSpace.exp (-((t : ℂ) • Y)) * g from rfl]`. Unfold `hhF`. Rewrite using `[(hcur g t).2, cB_alg]`. Conclude with `⟨0, fun h => absurd h hY⟩`. Use `choose lam hlam using key`.

Conclude with `⟨lam, hlam⟩`.
-/
theorem cB_curve (hC : DjCurve) (k j ρ a b : ℕ) :
    ∃ lam : Bool × B.Mat k (j + ρ) → ℂ, ∀ x : Bool × B.Mat k (j + ρ), inLieP k j ρ x.2 →
      ‖lam x‖ ≤ ((a + b : ℕ) : ℝ) * j * mx x.2 ∧
      ∀ (g : B.Mat k (j + ρ)) (t : ℝ), hhF k j ρ a b (crv x g t) = Complex.exp ((t : ℂ) * lam x) * hhF k j ρ a b g := by
  have key : ∀ x : Bool × B.Mat k (j + ρ), ∃ μ : ℂ, inLieP k j ρ x.2 →
      ‖μ‖ ≤ ((a + b : ℕ) : ℝ) * j * mx x.2 ∧
      ∀ (g : B.Mat k (j + ρ)) (t : ℝ), hhF k j ρ a b (crv x g t) = Complex.exp ((t : ℂ) * μ) * hhF k j ρ a b g := by
    rintro ⟨bb, Y⟩
    by_cases hY : inLieP k j ρ Y
    · obtain ⟨c₁, c₂, h₁, h₂, hcur⟩ := hC k j ρ Y hY
      cases bb
      · refine ⟨-((a : ℂ) * c₁ + (b : ℂ) * conj c₁), fun _ => ⟨cB_lamnorm a b c₁ h₁, fun g t => ?_⟩⟩
        rw [show crv (false, Y) g t = g * NormedSpace.exp ((t : ℂ) • Y) from rfl]
        unfold hhF
        rw [(hcur g t).1, cB_alg]
      · refine ⟨-((a : ℂ) * c₂ + (b : ℂ) * conj c₂), fun _ => ⟨cB_lamnorm a b c₂ h₂, fun g t => ?_⟩⟩
        rw [show crv (true, Y) g t = NormedSpace.exp (-((t : ℂ) • Y)) * g from rfl]
        unfold hhF
        rw [(hcur g t).2, cB_alg]
    · exact ⟨0, fun h => absurd h hY⟩
  choose lam hlam using key
  exact ⟨lam, hlam⟩

/- English proof (translation)
Establish `h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g => (DjU k j ρ g)⁻¹) {g | DjU k j ρ g ≠ 0}` using `hD.contDiffOn.inv (fun g hg => hg)`. Establish `hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g => star (DjU k j ρ g))`. Use `Complex.conjCLE.contDiff.comp hD` as an intermediate fact. Simplify `this` using `[Function.comp_def, Complex.star_def]`. Establish `h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g => (star (DjU k j ρ g))⁻¹) {g | DjU k j ρ g ≠ 0}` using `hs.contDiffOn.inv (fun g hg => by simpa using hg)`.

Conclude with `(hP.contDiffOn.mul (h1.pow a)).mul (h2.pow b)`.
-/
theorem cB_smooth {k j ρ : ℕ} (hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (DjU k j ρ)) {P : B.Mat k (j + ρ) → ℂ}
    (hP : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) P) (a b : ℕ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g => P g * (DjU k j ρ g)⁻¹ ^ a * (star (DjU k j ρ g))⁻¹ ^ b)
      {g | DjU k j ρ g ≠ 0} := by
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g => (DjU k j ρ g)⁻¹) {g | DjU k j ρ g ≠ 0} :=
    hD.contDiffOn.inv (fun g hg => hg)
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g => star (DjU k j ρ g)) := by
    have := Complex.conjCLE.contDiff.comp hD
    simpa [Function.comp_def, Complex.star_def] using this
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g => (star (DjU k j ρ g))⁻¹) {g | DjU k j ρ g ≠ 0} :=
    hs.contDiffOn.inv (fun g hg => by simpa using hg)
  exact (hP.contDiffOn.mul (h1.pow a)).mul (h2.pow b)

/- English proof (translation)
Unfold `mx`. Conclude with `(pi_norm_le_iff_of_nonneg zero_le_one).2 fun a => (pi_norm_le_iff_of_nonneg zero_le_one).2 fun b => hX a b`.
-/
theorem cB_mx_le {α : Type*} [Fintype α] {X : Matrix α α ℂ} (hX : ∀ a b, ‖X a b‖ ≤ 1) : mx X ≤ 1 := by
  unfold mx
  exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun a => (pi_norm_le_iff_of_nonneg zero_le_one).2 fun b => hX a b

/- English proof (translation)
Introduce `X hX` and use `⟨(hu X hX).1.1, (hu X hX).2⟩`.
-/
theorem cB_unitLie {k j ρ : ℕ} {u : List (B.Mat k (j + ρ))} (hu : unitP k j ρ u) :
    ∀ X ∈ u, B.unitLie k (j + ρ) X := fun X hX => ⟨(hu X hX).1.1, (hu X hX).2⟩

/- English proof (translation)
Introduce `x hx`. Simplify using `only [wL, wR, List.mem_append, List.mem_map] at hx`. Break down `hx with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩` into its components or cases. Conclude with `hu X hX`. Conclude with `hv X hX`.
-/
theorem cB_wP {k j ρ : ℕ} {u v : List (B.Mat k (j + ρ))} (hu : unitP k j ρ u) (hv : unitP k j ρ v) :
    ∀ x ∈ wL u ++ wR v, inLieP k j ρ x.2 ∧ ∀ a b, ‖x.2 a b‖ ≤ 1 := by
  intro x hx
  simp only [wL, wR, List.mem_append, List.mem_map] at hx
  rcases hx with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
  · exact hu X hX
  · exact hv X hX

/- English proof (translation)
Take `⟨hPs, hWB⟩` from `hP k (j + ρ) κ P hPd`. Take `⟨CP, hCP⟩` from `hWB n`. Take `⟨lam, hlam⟩` from `cB_curve hC k j ρ a b`. Use `set Λ : ℝ := ((a + b : ℕ) : ℝ) * j with hΛ`. Establish `hΛ0 : 0 ≤ Λ` using `by positivity`.

Use `⟨(1 + Λ) ^ n * (δ⁻¹ ^ (a + b) * |CP|), by positivity, ?_⟩` and prove the remaining obligations. Introduce `u v hu hv hl g hg hDg`. Establish `hw` using `cB_wP hu hv`. Establish `e : (fun g => P g * (DjU k j ρ g)⁻¹ ^ a * (star (DjU k j ρ g))⁻¹ ^ b) = fun g => hhF k j ρ a b g • P g`. Use function extensionality and compare the values at `g`.

Simplify using `only [hhF, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, cA_Dw_expmul lam (hhF k j ρ a b) _ P hPs (fun x hx g t => (hlam x (hw x hx).1).2 g t), norm_smul]`. Establish `hp` using `gN_pos hg`. Establish `hD0 : 0 < ‖DjU k j ρ g‖` using `lt_of_lt_of_le hδ hDg`.

Establish `hh : ‖hhF k j ρ a b g‖ ≤ δ⁻¹ ^ (a + b)`. Unfold `hhF`. Rewrite using `[norm_mul, norm_pow, norm_pow, norm_inv, norm_inv, norm_star, pow_add]`. Establish `: ‖DjU k j ρ g‖⁻¹ ≤ δ⁻¹` using `inv_anti₀ hδ hDg`. Conclude with `mul_le_mul (pow_le_pow_left₀ (by positivity) this a) (pow_le_pow_left₀ (by positivity) this b) (by positivity) (by positivity)`.

Establish `hb` using `cA_Dwl_bound lam hΛ0 g (|CP| * B.gN g ^ (κ : ℝ)) (wL u ++ wR v) P hPs (fun x hx => (hlam x (hw x hx).1).1.trans (by`. Use `cB_mx_le (hw x hx).2` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Use the proof step `(by`. Introduce `s hs`.

Take `⟨u', v', hu', hv', rfl⟩` from `sub_LR hs`. Rewrite using `[← dLR_eq]`. Use `hCP u' v' (fun X hX => cB_unitLie hu X (hu'.subset hX)) (fun X hX => cB_unitLie hv X (hv'.subset hX)) (by have := hu'.length_le; have := hv'.length_le; omega) g hg` as an intermediate fact. Simplify using `only [List.map_append, List.map_const', List.sum_append, Nat.cast_add] at this`. Use `this.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)) |>.trans_eq ?_` and prove the remaining obligations.

Use `congr 2`. Use the proof step `simp)`. Establish `hpow : (1 + Λ) ^ (wL u ++ wR v).length ≤ (1 + Λ) ^ n`. Rewrite using `[len_LR]; exact pow_le_pow_right₀ (by linarith) hl`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem cB_bound (hP : PolyB) (hC : DjCurve) {k j ρ κ : ℕ} {P : B.Mat k (j + ρ) → ℂ} (hPd : IsPolyDeg κ P)
    (a b n : ℕ) {δ : ℝ} (hδ : 0 < δ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : List (B.Mat k (j + ρ)), unitP k j ρ u →
      unitP k j ρ v → u.length + v.length ≤ n → ∀ g ∈ B.GV k (j + ρ), δ ≤ ‖DjU k j ρ g‖ →
        ‖Dw (wL u ++ wR v) (fun g => P g * (DjU k j ρ g)⁻¹ ^ a * (star (DjU k j ρ g))⁻¹ ^ b) g‖ ≤
          C * B.gN g ^ (κ : ℝ) := by
  obtain ⟨hPs, hWB⟩ := hP k (j + ρ) κ P hPd
  obtain ⟨CP, hCP⟩ := hWB n
  obtain ⟨lam, hlam⟩ := cB_curve hC k j ρ a b
  set Λ : ℝ := ((a + b : ℕ) : ℝ) * j with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  refine ⟨(1 + Λ) ^ n * (δ⁻¹ ^ (a + b) * |CP|), by positivity, ?_⟩
  intro u v hu hv hl g hg hDg
  have hw := cB_wP hu hv
  have e : (fun g => P g * (DjU k j ρ g)⁻¹ ^ a * (star (DjU k j ρ g))⁻¹ ^ b) =
      fun g => hhF k j ρ a b g • P g := by
    funext g; simp only [hhF, smul_eq_mul]; ring
  rw [e, cA_Dw_expmul lam (hhF k j ρ a b) _ P hPs (fun x hx g t => (hlam x (hw x hx).1).2 g t), norm_smul]
  have hp := gN_pos hg
  have hD0 : 0 < ‖DjU k j ρ g‖ := lt_of_lt_of_le hδ hDg
  have hh : ‖hhF k j ρ a b g‖ ≤ δ⁻¹ ^ (a + b) := by
    unfold hhF
    rw [norm_mul, norm_pow, norm_pow, norm_inv, norm_inv, norm_star, pow_add]
    have : ‖DjU k j ρ g‖⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ hDg
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) this a) (pow_le_pow_left₀ (by positivity) this b)
      (by positivity) (by positivity)
  have hb := cA_Dwl_bound lam hΛ0 g (|CP| * B.gN g ^ (κ : ℝ)) (wL u ++ wR v) P hPs
    (fun x hx => (hlam x (hw x hx).1).1.trans (by
      have := cB_mx_le (hw x hx).2
      calc ((a + b : ℕ) : ℝ) * j * mx x.2 ≤ ((a + b : ℕ) : ℝ) * j * 1 :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = Λ := by rw [mul_one]))
    (by
      intro s hs
      obtain ⟨u', v', hu', hv', rfl⟩ := sub_LR hs
      rw [← dLR_eq]
      have := hCP u' v' (fun X hX => cB_unitLie hu X (hu'.subset hX)) (fun X hX => cB_unitLie hv X (hv'.subset hX))
        (by have := hu'.length_le; have := hv'.length_le; omega) g hg
      simp only [List.map_append, List.map_const', List.sum_append, Nat.cast_add] at this
      refine this.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)) |>.trans_eq ?_
      congr 2
      simp)
  have hpow : (1 + Λ) ^ (wL u ++ wR v).length ≤ (1 + Λ) ^ n := by
    rw [len_LR]; exact pow_le_pow_right₀ (by linarith) hl
  calc ‖hhF k j ρ a b g‖ * ‖Dwl lam (wL u ++ wR v) P g‖
      ≤ δ⁻¹ ^ (a + b) * ((1 + Λ) ^ n * (|CP| * B.gN g ^ (κ : ℝ))) :=
        mul_le_mul hh (hb.trans (mul_le_mul_of_nonneg_right hpow (by positivity))) (norm_nonneg _) (by positivity)
    _ = (1 + Λ) ^ n * (δ⁻¹ ^ (a + b) * |CP|) * B.gN g ^ (κ : ℝ) := by ring

end PI.UnitaryCorollaryDerivatives
