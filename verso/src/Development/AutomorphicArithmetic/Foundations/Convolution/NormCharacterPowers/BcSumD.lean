import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.OrderAsym

open PositivityTheory.RgJS
open scoped ComplexConjugate

namespace UpperTheory.ConvolutionTheory.R

/- English proof (translation)
Establish `h1 : ∀ j, HasSum (fun i : {i // g i = j} => ‖(wt i : ℂ) * a (g i)‖) (ω j * ‖a j‖)` using `fun j => by`. Establish `e : (fun i : {i // g i = j} => ‖(wt i : ℂ) * a (g i)‖) = fun i => wt i.1 * ‖a j‖` using `funext fun i => by`. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_of_nonneg (h0 _), i.2]`. Rewrite using `[e]`. Conclude with `(hω j).mul_right ‖a j‖`.

Establish `hs : Summable fun i => ‖(wt i : ℂ) * a (g i)‖`. Rewrite using `[← (Equiv.sigmaFiberEquiv g).summable_iff]`. Use `(summable_sigma_of_nonneg fun _ => norm_nonneg _).2 ⟨fun j => (h1 j).summable, ?_⟩` and prove the remaining obligations. Use `Summable.of_nonneg_of_le (fun j => tsum_nonneg fun _ => norm_nonneg _) (fun j => ?_) (ha.mul_left L)` and prove the remaining obligations. Conclude with `((h1 j).tsum_eq).le.trans (mul_le_mul_of_nonneg_right (hL j) (norm_nonneg _))`.

Use `⟨hs, ?_⟩` and prove the remaining obligations. Establish `h2 : Summable fun x : Σ j, {i // g i = j} => (wt x.2 : ℂ) * a (g x.2)` using `(Equiv.sigmaFiberEquiv g).summable_iff.2 hs.of_norm`. Rewrite using `[← (Equiv.sigmaFiberEquiv g).tsum_eq]`. Use `h2.tsum_sigma.trans (tsum_congr fun j => ?_)` and prove the remaining obligations. Establish `h3` using `((Complex.hasSum_ofReal.2 (hω j)).mul_right (a j)).tsum_eq`.

Rewrite using `[← h3]`. Conclude with `tsum_congr fun i => by rw [i.2]`.
-/
private theorem fib_sum {I J : Type} (g : I → J) (wt : I → ℝ) (ω : J → ℝ) (a : J → ℂ) (L : ℝ) (h0 : ∀ i, 0 ≤ wt i)
    (hω : ∀ j, HasSum (fun i : {i // g i = j} => wt i) (ω j)) (hL : ∀ j, ω j ≤ L) (ha : Summable fun j => ‖a j‖) :
    (Summable fun i => ‖(wt i : ℂ) * a (g i)‖) ∧ ∑' i, (wt i : ℂ) * a (g i) = ∑' j, (ω j : ℂ) * a j := by
  have h1 : ∀ j, HasSum (fun i : {i // g i = j} => ‖(wt i : ℂ) * a (g i)‖) (ω j * ‖a j‖) := fun j => by
    have e : (fun i : {i // g i = j} => ‖(wt i : ℂ) * a (g i)‖) = fun i => wt i.1 * ‖a j‖ := funext fun i => by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (h0 _), i.2]
    rw [e]
    exact (hω j).mul_right ‖a j‖
  have hs : Summable fun i => ‖(wt i : ℂ) * a (g i)‖ := by
    rw [← (Equiv.sigmaFiberEquiv g).summable_iff]
    refine (summable_sigma_of_nonneg fun _ => norm_nonneg _).2 ⟨fun j => (h1 j).summable, ?_⟩
    refine Summable.of_nonneg_of_le (fun j => tsum_nonneg fun _ => norm_nonneg _) (fun j => ?_) (ha.mul_left L)
    exact ((h1 j).tsum_eq).le.trans (mul_le_mul_of_nonneg_right (hL j) (norm_nonneg _))
  refine ⟨hs, ?_⟩
  have h2 : Summable fun x : Σ j, {i // g i = j} => (wt x.2 : ℂ) * a (g x.2) :=
    (Equiv.sigmaFiberEquiv g).summable_iff.2 hs.of_norm
  rw [← (Equiv.sigmaFiberEquiv g).tsum_eq]
  refine h2.tsum_sigma.trans (tsum_congr fun j => ?_)
  have h3 := ((Complex.hasSum_ofReal.2 (hω j)).mul_right (a j)).tsum_eq
  rw [← h3]
  exact tsum_congr fun i => by rw [i.2]

open Classical in
/- English proof (translation)
Establish `hf : ∀ w, 1 ≤ f w` using `fun w => by`. Break down `hC.fib (u w) with h | h` into its components or cases. Rewrite using `[h.2.1 w rfl]`. Rewrite using `[h.2.1 w rfl]`. Conclude with `hl`.

Set `g : W' × ℕ → W × ℕ` to `fun p => (u p.1, f p.1 * (p.2 + 1) - 1)`. Establish `hg : ∀ p : W' × ℕ, f p.1 * (p.2 + 1) - 1 + 1 = f p.1 * (p.2 + 1)` using `fun p => Nat.sub_add_cancel (Nat.mul_pos (hf _) (Nat.succ_pos _))`. Establish `e1 : ∀ p, lterm q' ξ ζ s p = ((f p.1 : ℝ) : ℂ) * lterm q α β s (g p)` using `fun p => by`. Establish `h1 : ((f p.1 * (p.2 + 1) - 1 : ℕ) : ℂ) + 1 = (f p.1 : ℂ) * ((p.2 : ℂ) + 1)` using `by exact_mod_cast hg p`. Establish `h2 : ((q' p.1 : ℕ) : ℂ) ^ (-s) = (((q (u p.1) : ℕ) : ℂ) ^ (-s)) ^ f p.1`.

Rewrite using `[hC.norm, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, ← Complex.cpow_nat_mul]`. Establish `h3 : (f p.1 : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 (by have := hf p.1; omega)`. Establish `h4 : (p.2 : ℂ) + 1 ≠ 0` using `Nat.cast_add_one_ne_zero _`. Simplify using `only [lterm, g, hg, h1, hξ, hζ, h2, ← pow_mul, Complex.ofReal_natCast]`. Clear the denominators using the available nonvanishing facts.

Set `ω : W × ℕ → ℝ` to `fun p => if c p.1 ^ (p.2 + 1) = 1 then l else 0`. Establish `hω : ∀ j, HasSum (fun i : {i // g i = j} => (f i.1.1 : ℝ)) (ω j)`. Introduce and unpack `⟨v, k⟩`. Break down `hC.fib v with h | h` into its components or cases. Establish `: Finite {w // u w = v}` using `Nat.finite_of_card_ne_zero (by omega)`.

Use `Fintype.ofFinite {w // u w = v}` as an intermediate fact. Set `e : {w // u w = v} ≃ {i // g i = (v, k)}` to `{ toFun := fun w => ⟨(w.1, k), Prod.ext w.2 (by simp [g, h.2.1 w.1 w.2])⟩ invFun := fun i => ⟨i.1.1, congrArg Prod.fst i.2⟩ left_inv := fun _ => rfl right_inv := fun i => Subtype.ext (Prod.ext rfl (by`. Establish `h1` using `congrArg Prod.snd i.2`. Simplify using `only [g, h.2.1 i.1.1 (congrArg Prod.fst i.2)] at h1`. Simplify using `only`.

Use the proof step `omega)) }`. Rewrite using `[← e.hasSum_iff]`. Establish `h2 : ((fun i : {i // g i = (v, k)} => (f i.1.1 : ℝ)) ∘ e) = fun _ => 1` using `funext fun w => by show (f w.1 : ℝ) = 1`. Rewrite using `[h.2.1 w.1 w.2, Nat.cast_one]`. Rewrite using `[h2]`.

Use `hasSum_fintype (fun _ : {w // u w = v} => (1 : ℝ))` and compare the differences between its conclusion and the goal. Simplify using `[ω, h.2.2, ← h.1]`. Take `⟨⟨w₀, hw₀⟩, hu⟩` from `Nat.card_eq_one_iff_exists.1 h.1`. Distinguish the cases in `hd : l ∣ k + 1`. Take `⟨k', hk'⟩` from `hd`.

Apply the tactic sequence `obtain ⟨k', rfl⟩ : ∃ m, k' = m + 1 := ⟨k' - 1, by rcases k' with _ | k' <;> simp at hk' ⊢⟩`. Establish `hm : g (w₀, k') = (v, k)` using `Prod.ext hw₀ (by simp only [g, h.2.1 w₀ hw₀]; omega)`. Establish `h3 : ω (v, k) = (f w₀ : ℝ)`. Simplify using `only [ω, hk', pow_mul, h.2.2.pow_eq_one, one_pow, if_true, h.2.1 w₀ hw₀]`. Rewrite using `[h3]`.

Use `hasSum_single (f := fun i : {i // g i = (v, k)} => (f i.1.1 : ℝ)) ⟨(w₀, k'), hm⟩ fun i hi => (hi ?_).elim` and prove the remaining obligations. Establish `h4 : i.1.1 = w₀` using `congrArg Subtype.val (hu ⟨i.1.1, congrArg Prod.fst i.2⟩)`. Use `Subtype.ext (Prod.ext h4 ?_)` and prove the remaining obligations. Establish `h5 : f i.1.1 * (i.1.2 + 1) - 1 = k` using `congrArg Prod.snd i.2`. Establish `h6` using `hg i.1`.

Rewrite `h6` using `[h5, hk', h4, h.2.1 w₀ hw₀]`. Use `Nat.eq_of_mul_eq_mul_left hl h6` as an intermediate fact. Simplify using `only`. Use linear arithmetic over natural numbers and integers. Establish `: IsEmpty {i // g i = (v, k)}` using `⟨fun i => hd (by`.

Establish `h5 : f i.1.1 * (i.1.2 + 1) - 1 = k` using `congrArg Prod.snd i.2`. Establish `h6` using `hg i.1`. Rewrite `h6` using `[h5, h.2.1 _ (congrArg Prod.fst i.2)]`. Conclude with `⟨_, h6⟩)⟩`. Establish `h3 : ω (v, k) = 0` using `if_neg fun e => hd ((h.2.2.pow_eq_one_iff_dvd _).1 e)`.

Rewrite using `[h3]`. Conclude with `hasSum_empty`. Apply the tactic sequence `obtain ⟨r1, r2⟩ := fib_sum g (fun p => (f p.1 : ℝ)) ω (lterm q α β s) l (fun _ => Nat.cast_nonneg _) hω (fun j => by simp only [ω]; split_ifs <;> simp) hs`. Use `⟨by simpa only [e1] using r1, ?_⟩` and prove the remaining obligations. Establish `hc : ∀ v, c v ^ l = 1` using `fun v => by`.

Break down `hC.fib v with h | h` into its components or cases. Rewrite using `[h.2.2, one_pow]`. Conclude with `h.2.2.pow_eq_one`. Establish `e2 : ∀ j p, lterm q α (fun v b => β v b * c v ^ j) s p = conj ((c p.1 ^ (p.2 + 1)) ^ j) * lterm q α β s p` using `fun j p => by`. Simplify using `only [lterm, mul_pow, ← Finset.sum_mul, map_mul, ← pow_mul, mul_comm j]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hn : ∀ v, ‖c v‖ = 1` using `fun v => Complex.norm_eq_one_of_pow_eq_one (hc v) (by omega)`. Rewrite using `[tsum_congr e1, r2, ← Summable.tsum_finsetSum fun j _ => Summable.of_norm (by simpa [e2, hn] using hs)]`. Use `tsum_congr fun p => ?_` and prove the remaining obligations. Simplify using `only [e2, ← Finset.sum_mul, ← map_sum]`.

Use `congr 1`. Simplify using `only [ω]`. Use `split_ifs with h`. Simplify using `[h]`. Rewrite using `[geom_sum_eq h, ← pow_mul, mul_comm, pow_mul, hc]`.

Simplify using the standard rewrite rules.
-/
theorem bcSumD (l : ℕ) (W W' : Type) (q : W → ℕ) (q' : W' → ℕ) (u : W' → W) (f : W' → ℕ) (c : W → ℂ) (hl : 1 ≤ l)
    (hq : ∀ v, 1 ≤ q v) (hC : Cover l q q' u f c) (A B A' B' : Type) [Fintype A] [Fintype B] [Fintype A'] [Fintype B']
    (α : W → A → ℂ) (β : W → B → ℂ) (ξ : W' → A' → ℂ) (ζ : W' → B' → ℂ) (s : ℂ)
    (hξ : ∀ w (k : ℕ), ∑ a, ξ w a ^ k = ∑ a, α (u w) a ^ (f w * k)) (hζ : ∀ w (k : ℕ), ∑ b, ζ w b ^ k = ∑ b, β (u w) b ^ (f w * k))
    (hs : Summable fun p => ‖lterm q α β s p‖) : (Summable fun p => ‖lterm q' ξ ζ s p‖) ∧
      ∑' p, lterm q' ξ ζ s p = ∑ j ∈ Finset.range l, ∑' p, lterm q α (fun v b => β v b * c v ^ j) s p := by
  have hf : ∀ w, 1 ≤ f w := fun w => by
    rcases hC.fib (u w) with h | h
    · rw [h.2.1 w rfl]
    · rw [h.2.1 w rfl]; exact hl
  let g : W' × ℕ → W × ℕ := fun p => (u p.1, f p.1 * (p.2 + 1) - 1)
  have hg : ∀ p : W' × ℕ, f p.1 * (p.2 + 1) - 1 + 1 = f p.1 * (p.2 + 1) := fun p =>
    Nat.sub_add_cancel (Nat.mul_pos (hf _) (Nat.succ_pos _))
  have e1 : ∀ p, lterm q' ξ ζ s p = ((f p.1 : ℝ) : ℂ) * lterm q α β s (g p) := fun p => by
    have h1 : ((f p.1 * (p.2 + 1) - 1 : ℕ) : ℂ) + 1 = (f p.1 : ℂ) * ((p.2 : ℂ) + 1) := by exact_mod_cast hg p
    have h2 : ((q' p.1 : ℕ) : ℂ) ^ (-s) = (((q (u p.1) : ℕ) : ℂ) ^ (-s)) ^ f p.1 := by
      rw [hC.norm, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, ← Complex.cpow_nat_mul]
    have h3 : (f p.1 : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by have := hf p.1; omega)
    have h4 : (p.2 : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero _
    simp only [lterm, g, hg, h1, hξ, hζ, h2, ← pow_mul, Complex.ofReal_natCast]
    field_simp
  let ω : W × ℕ → ℝ := fun p => if c p.1 ^ (p.2 + 1) = 1 then l else 0
  have hω : ∀ j, HasSum (fun i : {i // g i = j} => (f i.1.1 : ℝ)) (ω j) := by
    rintro ⟨v, k⟩
    rcases hC.fib v with h | h
    · have : Finite {w // u w = v} := Nat.finite_of_card_ne_zero (by omega)
      have := Fintype.ofFinite {w // u w = v}
      let e : {w // u w = v} ≃ {i // g i = (v, k)} :=
        { toFun := fun w => ⟨(w.1, k), Prod.ext w.2 (by simp [g, h.2.1 w.1 w.2])⟩
          invFun := fun i => ⟨i.1.1, congrArg Prod.fst i.2⟩
          left_inv := fun _ => rfl
          right_inv := fun i => Subtype.ext (Prod.ext rfl (by
            have h1 := congrArg Prod.snd i.2
            simp only [g, h.2.1 i.1.1 (congrArg Prod.fst i.2)] at h1
            simp only
            omega)) }
      rw [← e.hasSum_iff]
      have h2 : ((fun i : {i // g i = (v, k)} => (f i.1.1 : ℝ)) ∘ e) = fun _ => 1 := funext fun w => by
        show (f w.1 : ℝ) = 1
        rw [h.2.1 w.1 w.2, Nat.cast_one]
      rw [h2]
      convert hasSum_fintype (fun _ : {w // u w = v} => (1 : ℝ))
      simp [ω, h.2.2, ← h.1]
    · obtain ⟨⟨w₀, hw₀⟩, hu⟩ := Nat.card_eq_one_iff_exists.1 h.1
      by_cases hd : l ∣ k + 1
      · obtain ⟨k', hk'⟩ := hd
        obtain ⟨k', rfl⟩ : ∃ m, k' = m + 1 := ⟨k' - 1, by rcases k' with _ | k' <;> simp at hk' ⊢⟩
        have hm : g (w₀, k') = (v, k) := Prod.ext hw₀ (by simp only [g, h.2.1 w₀ hw₀]; omega)
        have h3 : ω (v, k) = (f w₀ : ℝ) := by
          simp only [ω, hk', pow_mul, h.2.2.pow_eq_one, one_pow, if_true, h.2.1 w₀ hw₀]
        rw [h3]
        refine hasSum_single (f := fun i : {i // g i = (v, k)} => (f i.1.1 : ℝ)) ⟨(w₀, k'), hm⟩ fun i hi => (hi ?_).elim
        have h4 : i.1.1 = w₀ := congrArg Subtype.val (hu ⟨i.1.1, congrArg Prod.fst i.2⟩)
        refine Subtype.ext (Prod.ext h4 ?_)
        have h5 : f i.1.1 * (i.1.2 + 1) - 1 = k := congrArg Prod.snd i.2
        have h6 := hg i.1
        rw [h5, hk', h4, h.2.1 w₀ hw₀] at h6
        have := Nat.eq_of_mul_eq_mul_left hl h6
        simp only
        omega
      · have : IsEmpty {i // g i = (v, k)} := ⟨fun i => hd (by
          have h5 : f i.1.1 * (i.1.2 + 1) - 1 = k := congrArg Prod.snd i.2
          have h6 := hg i.1
          rw [h5, h.2.1 _ (congrArg Prod.fst i.2)] at h6
          exact ⟨_, h6⟩)⟩
        have h3 : ω (v, k) = 0 := if_neg fun e => hd ((h.2.2.pow_eq_one_iff_dvd _).1 e)
        rw [h3]
        exact hasSum_empty
  obtain ⟨r1, r2⟩ := fib_sum g (fun p => (f p.1 : ℝ)) ω (lterm q α β s) l (fun _ => Nat.cast_nonneg _) hω
    (fun j => by simp only [ω]; split_ifs <;> simp) hs
  refine ⟨by simpa only [e1] using r1, ?_⟩
  have hc : ∀ v, c v ^ l = 1 := fun v => by
    rcases hC.fib v with h | h
    · rw [h.2.2, one_pow]
    · exact h.2.2.pow_eq_one
  have e2 : ∀ j p, lterm q α (fun v b => β v b * c v ^ j) s p = conj ((c p.1 ^ (p.2 + 1)) ^ j) * lterm q α β s p := fun j p => by
    simp only [lterm, mul_pow, ← Finset.sum_mul, map_mul, ← pow_mul, mul_comm j]
    ring
  have hn : ∀ v, ‖c v‖ = 1 := fun v => Complex.norm_eq_one_of_pow_eq_one (hc v) (by omega)
  rw [tsum_congr e1, r2, ← Summable.tsum_finsetSum fun j _ => Summable.of_norm (by simpa [e2, hn] using hs)]
  refine tsum_congr fun p => ?_
  simp only [e2, ← Finset.sum_mul, ← map_sum]
  congr 1
  simp only [ω]
  split_ifs with h
  · simp [h]
  · rw [geom_sum_eq h, ← pow_mul, mul_comm, pow_mul, hc]
    simp

/- English proof (translation)
Introduce `l W W' q q' u f c hl hq hC A B A' B' _ _ _ _ α β ξ ζ σ h1 h2 h3` and use `bcSumD l W W' q q' u f c hl hq hC A B A' B' α β ξ ζ σ h1 h2 h3`.
-/
theorem bcSum_holds : BCSum := fun l W W' q q' u f c hl hq hC A B A' B' _ _ _ _ α β ξ ζ σ h1 h2 h3 =>
  bcSumD l W W' q q' u f c hl hq hC A B A' B' α β ξ ζ σ h1 h2 h3

end UpperTheory.ConvolutionTheory.R
