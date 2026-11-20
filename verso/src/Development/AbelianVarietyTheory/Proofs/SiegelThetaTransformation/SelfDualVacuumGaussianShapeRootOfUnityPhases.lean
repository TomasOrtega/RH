import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsExOfPow
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real

namespace GlobalTheory.Phase.VacShape

open GlobalTheory.SW.Vac

/- English proof (translation)
Take `⟨m, hm, ha⟩` from `ha`. Take `⟨n, hn, hb⟩` from `hb`. Use `⟨m * n, Nat.mul_pos hm hn, ?_⟩` and prove the remaining obligations. Rewrite using `[norm_mul, Complex.ofReal_mul, mul_pow, mul_pow, pow_mul a, ha, pow_mul' b, hb, ← pow_mul, ← pow_mul, mul_comm n m]`.
-/
theorem ph_mul {a b : ℂ} (ha : Ph a) (hb : Ph b) : Ph (a * b) := by
  obtain ⟨m, hm, ha⟩ := ha
  obtain ⟨n, hn, hb⟩ := hb
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  rw [norm_mul, Complex.ofReal_mul, mul_pow, mul_pow, pow_mul a, ha, pow_mul' b, hb, ← pow_mul,
    ← pow_mul, mul_comm n m]

/- English proof (translation)
Take `⟨m, hm, ha⟩` from `ha`. Take `⟨n, hn, hb⟩` from `hb`. Use `⟨m * n, Nat.mul_pos hm hn, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_pow, pow_mul a, ha, pow_mul' b, hb]`. Simplify using the standard rewrite rules.
-/
theorem isMu_mul {a b : ℂ} (ha : IsMu a) (hb : IsMu b) : IsMu (a * b) := by
  obtain ⟨m, hm, ha⟩ := ha
  obtain ⟨n, hn, hb⟩ := hb
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  rw [mul_pow, pow_mul a, ha, pow_mul' b, hb]; simp

/- English proof (translation)
Take `⟨m, hm, ha⟩` from `ha`. Use `⟨m, hm, ?_⟩` and prove the remaining obligations. Rewrite using `[← Complex.ofReal_pow, ← norm_pow, ha]`. Simplify using the standard rewrite rules.
-/
theorem ph_of_isMu {a : ℂ} (ha : IsMu a) : Ph a := by
  obtain ⟨m, hm, ha⟩ := ha
  refine ⟨m, hm, ?_⟩
  rw [← Complex.ofReal_pow, ← norm_pow, ha]; simp

/- English proof (translation)
Use `⟨2 * q.den, Nat.mul_pos two_pos q.den_pos, ?_⟩` and prove the remaining obligations. Rewrite using `[ex, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]`. Use `⟨q.num, ?_⟩` and prove the remaining obligations. Establish `: (q.den : ℂ) * (q : ℂ) = q.num` using `by exact_mod_cast Rat.den_mul_eq_num q`. Rewrite using `[← this]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isMu_ex (q : ℚ) : IsMu (ex q) := by
  refine ⟨2 * q.den, Nat.mul_pos two_pos q.den_pos, ?_⟩
  rw [ex, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
  refine ⟨q.num, ?_⟩
  have : (q.den : ℂ) * (q : ℂ) = q.num := by exact_mod_cast Rat.den_mul_eq_num q
  rw [← this]; push_cast; ring

variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
  {A : AddSubgroup (Matrix κ ι ℚ × Matrix κ ι ℚ)} {ε : Matrix κ ι ℚ × Matrix κ ι ℚ → ℂ}
  {φ : Matrix κ ι ℚ → ℂ}

omit [DecidableEq ι] in
/- English proof (translation)
Introduce `y hy y' hy'`. Rewrite using `[h.semi y hy y' hy', om, om_eq, ex]`.
-/
theorem semi' (h : VacS A ε φ) : ∀ y ∈ A, ∀ y' ∈ A,
    ε (y + y') = ε y * ε y' * ex (pr y.1 y'.2 - pr y'.1 y.2) := by
  intro y hy y' hy'
  rw [h.semi y hy y' hy', om, om_eq, ex]

omit [DecidableEq ι] in
/- English proof (translation)
Take `⟨m, hm, hm'⟩` from `h.ord`. Establish `h0 : ε 0 = 1` using `by simpa using hm' 0 A.zero_mem`. Establish `hpow : ∀ n : ℕ, ε (n • y) = ε y ^ n`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => rw [zero_nsmul, pow_zero]`. Conclude with `h0`. Consider the case `succ n ih`. Rewrite using `[succ_nsmul, semi' h _ (A.nsmul_mem hy n) _ hy, ih, pow_succ, Prod.smul_fst, Prod.smul_snd, ← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ, pr_smul_left, pr_smul_right, sub_self, ex_zero, mul_one]`. Conclude with `⟨m, hm, by rw [← hpow, hm' y hy]⟩`.
-/
theorem isMu_eps (h : VacS A ε φ) {y} (hy : y ∈ A) : IsMu (ε y) := by
  obtain ⟨m, hm, hm'⟩ := h.ord
  have h0 : ε 0 = 1 := by simpa using hm' 0 A.zero_mem
  have hpow : ∀ n : ℕ, ε (n • y) = ε y ^ n := by
    intro n
    induction n with
    | zero => rw [zero_nsmul, pow_zero]; exact h0
    | succ n ih =>
      rw [succ_nsmul, semi' h _ (A.nsmul_mem hy n) _ hy, ih, pow_succ, Prod.smul_fst, Prod.smul_snd,
        ← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ, pr_smul_left, pr_smul_right,
        sub_self, ex_zero, mul_one]
  exact ⟨m, hm, by rw [← hpow, hm' y hy]⟩

/- English proof (translation)
Establish `hfix : ∀ y ∈ A, ∀ x, fac ε y x * φ (x - y.2) = φ x` using `fun y hy => (fixed_iff ε y φ).1 (h.fix y hy)`. Set `f : Matrix κ ι ℚ → ℂ` to `fun b => φ (a + b) / φ a`. Establish `hf : ∀ y ∈ A, f y.2 = fac ε y (a + y.2)`. Introduce `y hy`. Simplify using `only [f]`.

Rewrite using `[← hfix y hy (a + y.2), add_sub_cancel_right, mul_div_cancel_right₀ _ ha]`. Establish `hadd : ∀ y ∈ A, ∀ y' ∈ A, f (y.2 + y'.2) = f y.2 * f y'.2 * ex (2 * pr y'.2 y.1)`. Introduce `y hy y' hy'`. Use `hf _ (A.add_mem hy hy')` as an intermediate fact. Rewrite `this` using `[Prod.snd_add, fac_add (semi' h y hy y' hy')]`.

Rewrite using `[this, hf y hy, hf y' hy', show a + (y.2 + y'.2) - y.2 = a + y'.2 by abel, mul_right_comm]`. Use `congr 1`. Unfold `fac`. Rewrite using `[mul_assoc, ← ex_add]`. Use `congr 2`.

Simplify using `only [pr_add_left]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨A.map (AddMonoidHom.snd _ _), f, ⟨?_, ?_⟩, fun x => ⟨fun _ => ?_, fun hx => ?_⟩⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Express the relevant statement in the definitionally equal form `IsMu (f y.2)`.

Rewrite using `[hf y hy]`. Conclude with `isMu_mul (isMu_eps h hy) (isMu_ex _)`. Introduce and unpack `_ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩`. Express the relevant statement in the definitionally equal form `f (x.2 + y.2 + z.2) * f x.2 * f y.2 * f z.2 = f (x.2 + y.2) * f (y.2 + z.2) * f (x.2 + z.2) * f 0`. Establish `h0 : f 0 = 1` using `by simp [f, ha]`.

Establish `h1` using `hadd _ (A.add_mem hx hy) z hz`. Rewrite `h1` using `[Prod.snd_add, Prod.fst_add, pr_add_right, mul_add, ex_add]`. Rewrite using `[h1, hadd y hy z hz, hadd x hx z hz, h0]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [f]`.

Rewrite using `[add_sub_cancel, mul_div_cancel₀ _ ha]`. Assume the negation of the conclusion as `hne`. Apply `hx` to reduce the goal to its premises. Establish `hd : ∀ y, y ∈ A ↔ ∀ y' ∈ A, ∃ m : ℤ, pr y.1 y'.2 - pr y'.1 y.2 = m`. Introduce `y`.

Simplify `h.dual y` using `only [om, om_eq]`. Establish `key : ∀ b, (b, 0) ∈ A → ∀ w, φ w ≠ 0 → ε (b, 0) * ex (2 * pr w b) = 1`. Introduce `b hb w hw`. Establish `h1` using `hfix _ hb w`. Simplify using `only [sub_zero, fac, pr_zero_right] at h1`.

Apply `mul_right_cancel₀ hw` to reduce the goal to its premises. Rewrite using `[h1, one_mul]`. Take `⟨b, hb⟩` from `exists_lift A h.fg hd (x - a) fun b hb => by`. Establish `h2` using `key b hb x hne`. Establish `h3` using `key b hb a ha`.

Apply `ex_two_eq_one` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, ← ex_add, pr_sub_left]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = 1 := h2`. Conclude with `⟨_, hb, rfl⟩`.
-/
theorem shape_at (h : VacS A ε φ) (a : Matrix κ ι ℚ) (ha : φ a ≠ 0) :
    ∃ (S : AddSubgroup (Matrix κ ι ℚ)) (f : Matrix κ ι ℚ → ℂ), Quad S f ∧
      ∀ x, (x - a ∈ S → φ x = φ a * f (x - a)) ∧ (x - a ∉ S → φ x = 0) := by
  have hfix : ∀ y ∈ A, ∀ x, fac ε y x * φ (x - y.2) = φ x := fun y hy =>
    (fixed_iff ε y φ).1 (h.fix y hy)
  let f : Matrix κ ι ℚ → ℂ := fun b => φ (a + b) / φ a
  have hf : ∀ y ∈ A, f y.2 = fac ε y (a + y.2) := by
    intro y hy
    simp only [f]
    rw [← hfix y hy (a + y.2), add_sub_cancel_right, mul_div_cancel_right₀ _ ha]
  have hadd : ∀ y ∈ A, ∀ y' ∈ A, f (y.2 + y'.2) = f y.2 * f y'.2 * ex (2 * pr y'.2 y.1) := by
    intro y hy y' hy'
    have := hf _ (A.add_mem hy hy')
    rw [Prod.snd_add, fac_add (semi' h y hy y' hy')] at this
    rw [this, hf y hy, hf y' hy', show a + (y.2 + y'.2) - y.2 = a + y'.2 by abel, mul_right_comm]
    congr 1
    unfold fac
    rw [mul_assoc, ← ex_add]
    congr 2
    simp only [pr_add_left]; ring
  refine ⟨A.map (AddMonoidHom.snd _ _), f, ⟨?_, ?_⟩, fun x => ⟨fun _ => ?_, fun hx => ?_⟩⟩
  · rintro _ ⟨y, hy, rfl⟩
    change IsMu (f y.2)
    rw [hf y hy]
    exact isMu_mul (isMu_eps h hy) (isMu_ex _)
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    change f (x.2 + y.2 + z.2) * f x.2 * f y.2 * f z.2 =
      f (x.2 + y.2) * f (y.2 + z.2) * f (x.2 + z.2) * f 0
    have h0 : f 0 = 1 := by simp [f, ha]
    have h1 := hadd _ (A.add_mem hx hy) z hz
    rw [Prod.snd_add, Prod.fst_add, pr_add_right, mul_add, ex_add] at h1
    rw [h1, hadd y hy z hz, hadd x hx z hz, h0]
    ring
  · simp only [f]
    rw [add_sub_cancel, mul_div_cancel₀ _ ha]
  · by_contra hne
    apply hx
    have hd : ∀ y, y ∈ A ↔ ∀ y' ∈ A, ∃ m : ℤ, pr y.1 y'.2 - pr y'.1 y.2 = m := by
      intro y
      simpa only [om, om_eq] using h.dual y
    have key : ∀ b, (b, 0) ∈ A → ∀ w, φ w ≠ 0 → ε (b, 0) * ex (2 * pr w b) = 1 := by
      intro b hb w hw
      have h1 := hfix _ hb w
      simp only [sub_zero, fac, pr_zero_right] at h1
      apply mul_right_cancel₀ hw; rw [h1, one_mul]
    obtain ⟨b, hb⟩ := exists_lift A h.fg hd (x - a) fun b hb => by
      have h2 := key b hb x hne
      have h3 := key b hb a ha
      apply ex_two_eq_one
      calc _ = ε (b, 0) * ex (2 * pr a b) * ex (2 * pr (x - a) b) := by rw [h3, one_mul]
        _ = ε (b, 0) * ex (2 * pr x b) := by
          rw [mul_assoc, ← ex_add, pr_sub_left]; congr 2; ring
        _ = 1 := h2
    exact ⟨_, hb, rfl⟩

/- English proof (translation)
Use `⟨h.fg, h.dual, h.norm, h.semi, h.ord, ?_, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨R, hR, h1, h2⟩` from `h.sb`. Use `⟨R, hR, fun x hx => h1 x fun e => hx (by simp [e]), fun x z hz => ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, h2 x z hz]`. Rewrite using `[fixed_iff]`.

Introduce `x`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Rewrite using `[mul_left_comm, (fixed_iff ε y φ).1 (h.fix y hy) x]`.
-/
theorem vac_smul (h : VacS A ε φ) (u : ℂ) : VacS A ε (u • φ) := by
  refine ⟨h.fg, h.dual, h.norm, h.semi, h.ord, ?_, fun y hy => ?_⟩
  · obtain ⟨R, hR, h1, h2⟩ := h.sb
    refine ⟨R, hR, fun x hx => h1 x fun e => hx (by simp [e]), fun x z hz => ?_⟩
    simp only [Pi.smul_apply, h2 x z hz]
  · rw [fixed_iff]
    intro x
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_left_comm, (fixed_iff ε y φ).1 (h.fix y hy) x]

/- English proof (translation)
Use `⟨⟨A, ε, h⟩, fun x => ?_⟩` and prove the remaining obligations. Take `⟨S, f, hq, hx⟩` from `shape_at h a ha`. Distinguish the cases in `hS : x - a ∈ S`. Rewrite using `[(hx x).1 hS]`. Conclude with `ph_mul hp (ph_of_isMu (hq.1 _ hS))`.

Rewrite using `[(hx x).2 hS]`. Conclude with `ph_zero`.
-/
theorem pv_of_ph (h : VacS A ε φ) (a : Matrix κ ι ℚ) (ha : φ a ≠ 0) (hp : Ph (φ a)) : PV φ := by
  refine ⟨⟨A, ε, h⟩, fun x => ?_⟩
  obtain ⟨S, f, hq, hx⟩ := shape_at h a ha
  by_cases hS : x - a ∈ S
  · rw [(hx x).1 hS]; exact ph_mul hp (ph_of_isMu (hq.1 _ hS))
  · rw [(hx x).2 hS]; exact ph_zero

/- English proof (translation)
Introduce `κ ι _ _ _ φ`. Use `⟨fun A ε h a ha => shape_at h a ha, ?_, fun A ε h => ?_, ?_, fun A ε h a ha hp => pv_of_ph h a ha hp⟩` and prove the remaining obligations. Introduce and unpack `⟨⟨A, ε, h⟩, hp⟩`. Use `⟨h.sb, ?_⟩` and prove the remaining obligations. Distinguish the cases in `h0 : ∃ a, φ a ≠ 0`.

Take `⟨a, ha⟩` from `h0`. Take `⟨S, f, hq, hx⟩` from `shape_at h a ha`. Use `⟨φ a, a, S, f, hp a, hq, fun x => ?_⟩` and prove the remaining obligations. Use `split_ifs with hS`. Conclude with `(hx x).1 hS`.

Conclude with `(hx x).2 hS`. Use `push Not at h0`. Conclude with `⟨0, 0, ⊥, fun _ => 1, ph_zero, ⟨fun _ _ => isMu_one, fun _ _ _ _ _ _ => rfl⟩, fun x => by simp [h0]⟩`. Distinguish the cases in `h0 : ∃ a, φ a ≠ 0`. Take `⟨a, ha⟩` from `h0`.

Establish `hn : ‖φ a‖ ≠ 0` using `norm_ne_zero_iff.2 ha`. Establish `e : ((((‖φ a‖ : ℝ) : ℂ) / φ a) • φ) a = ((‖φ a‖ : ℝ) : ℂ)`. Rewrite using `[Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ ha]`. Use `⟨((‖φ a‖ : ℝ) : ℂ) / φ a, by simp [hn], pv_of_ph (vac_smul h _) a ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[e]`.

Conclude with `hn` after adjusting the coercions. Rewrite using `[e]; exact ⟨1, one_pos, by simp⟩`. Use `push Not at h0`. Conclude with `⟨1, norm_one, ⟨A, ε, vac_smul h _⟩, fun x => by simpa [h0] using ph_zero⟩`. Introduce and unpack `⟨⟨A, ε, h⟩, hp⟩ u hu`.

Conclude with `⟨⟨A, ε, vac_smul h _⟩, fun x => ph_mul hu (hp x)⟩`.
-/
theorem vacuum_shape : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι], ∀ φ : Matrix κ ι ℚ → ℂ, (∀ A ε, VacS A ε φ → ∀ a, φ a ≠ 0 → ∃ (S : AddSubgroup (Matrix κ ι ℚ)) (f : Matrix κ ι ℚ → ℂ), Quad S f ∧ ∀ x, (x - a ∈ S → φ x = φ a * f (x - a)) ∧ (x - a ∉ S → φ x = 0)) ∧ (PV φ → Shape φ) ∧ (∀ A ε, VacS A ε φ → ∃ u : ℂ, ‖u‖ = 1 ∧ PV (u • φ)) ∧ (PV φ → ∀ u : ℂ, Ph u → PV (u • φ)) ∧ ∀ A ε, VacS A ε φ → ∀ a, φ a ≠ 0 → Ph (φ a) → PV φ := by
  intro κ ι _ _ _ φ
  refine ⟨fun A ε h a ha => shape_at h a ha, ?_, fun A ε h => ?_, ?_,
    fun A ε h a ha hp => pv_of_ph h a ha hp⟩
  · rintro ⟨⟨A, ε, h⟩, hp⟩
    refine ⟨h.sb, ?_⟩
    by_cases h0 : ∃ a, φ a ≠ 0
    · obtain ⟨a, ha⟩ := h0
      obtain ⟨S, f, hq, hx⟩ := shape_at h a ha
      refine ⟨φ a, a, S, f, hp a, hq, fun x => ?_⟩
      split_ifs with hS
      · exact (hx x).1 hS
      · exact (hx x).2 hS
    · push Not at h0
      exact ⟨0, 0, ⊥, fun _ => 1, ph_zero, ⟨fun _ _ => isMu_one, fun _ _ _ _ _ _ => rfl⟩,
        fun x => by simp [h0]⟩
  · by_cases h0 : ∃ a, φ a ≠ 0
    · obtain ⟨a, ha⟩ := h0
      have hn : ‖φ a‖ ≠ 0 := norm_ne_zero_iff.2 ha
      have e : ((((‖φ a‖ : ℝ) : ℂ) / φ a) • φ) a = ((‖φ a‖ : ℝ) : ℂ) := by
        rw [Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ ha]
      refine ⟨((‖φ a‖ : ℝ) : ℂ) / φ a, by simp [hn], pv_of_ph (vac_smul h _) a ?_ ?_⟩
      · rw [e]; exact_mod_cast hn
      · rw [e]; exact ⟨1, one_pos, by simp⟩
    · push Not at h0
      exact ⟨1, norm_one, ⟨A, ε, vac_smul h _⟩, fun x => by simpa [h0] using ph_zero⟩
  · rintro ⟨⟨A, ε, h⟩, hp⟩ u hu
    exact ⟨⟨A, ε, vac_smul h _⟩, fun x => ph_mul hu (hp x)⟩

end GlobalTheory.Phase.VacShape
