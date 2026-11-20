import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalSchwartzBruhatAlgebraIntegralLinear

open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real

namespace GlobalTheory.Phase.ShapeOps

/- English proof (translation)
Take `⟨m, hm, ha⟩` from `ha`. Take `⟨n, hn, hb⟩` from `hb`. Use `⟨m * n, Nat.mul_pos hm hn, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_pow, pow_mul, ha, mul_comm m n, pow_mul, hb]`. Simplify using the standard rewrite rules.
-/
theorem mu_mul {a b : ℂ} (ha : IsMu a) (hb : IsMu b) : IsMu (a * b) := by
  obtain ⟨m, hm, ha⟩ := ha
  obtain ⟨n, hn, hb⟩ := hb
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  rw [mul_pow, pow_mul, ha, mul_comm m n, pow_mul, hb]; simp

/- English proof (translation)
Take `⟨m, hm, ha⟩` from `ha`. Conclude with `⟨m, hm, by rw [inv_pow, ha, inv_one]⟩`.
-/
theorem mu_inv {a : ℂ} (ha : IsMu a) : IsMu a⁻¹ := by
  obtain ⟨m, hm, ha⟩ := ha
  exact ⟨m, hm, by rw [inv_pow, ha, inv_one]⟩

/- English proof (translation)
Take `⟨m, hm, ha⟩` from `ha`. Conclude with `⟨m, hm, by rw [← map_pow, ha, map_one]⟩`.
-/
theorem mu_conj {a : ℂ} (ha : IsMu a) : IsMu (conj a) := by
  obtain ⟨m, hm, ha⟩ := ha
  exact ⟨m, hm, by rw [← map_pow, ha, map_one]⟩

/- English proof (translation)
Take `⟨m, hm, ha⟩` from `ha`. Introduce and unpack `rfl`. Rewrite `ha` using `[zero_pow hm.ne']`. Conclude with `zero_ne_one ha`.
-/
theorem mu_ne {a : ℂ} (ha : IsMu a) : a ≠ 0 := by
  obtain ⟨m, hm, ha⟩ := ha
  rintro rfl
  rw [zero_pow hm.ne'] at ha
  exact zero_ne_one ha

/- English proof (translation)
Take `⟨m, hm, ha⟩` from `ha`. Take `⟨n, hn, hb⟩` from `hb`. Use `⟨m * n, Nat.mul_pos hm hn, ?_⟩` and prove the remaining obligations. Rewrite using `[norm_mul, Complex.ofReal_mul, mul_pow, mul_pow, pow_mul a, ha, ← pow_mul, mul_comm m n, pow_mul b, hb, ← pow_mul]`.
-/
theorem ph_mul {a b : ℂ} (ha : Ph a) (hb : Ph b) : Ph (a * b) := by
  obtain ⟨m, hm, ha⟩ := ha
  obtain ⟨n, hn, hb⟩ := hb
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  rw [norm_mul, Complex.ofReal_mul, mul_pow, mul_pow, pow_mul a, ha, ← pow_mul, mul_comm m n, pow_mul b, hb,
    ← pow_mul]

/- English proof (translation)
Take `⟨m, hm, ha⟩` from `ha`. Use `⟨m, hm, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_pow, ha, map_pow, Complex.conj_ofReal, Complex.norm_conj]`.
-/
theorem ph_conj {a : ℂ} (ha : Ph a) : Ph (conj a) := by
  obtain ⟨m, hm, ha⟩ := ha
  refine ⟨m, hm, ?_⟩
  rw [← map_pow, ha, map_pow, Complex.conj_ofReal, Complex.norm_conj]

section Quad

variable {M : Type} [AddCommGroup M]

/- English proof (translation)
Use `⟨fun x hx => mu_mul (hf.1 x hx) (hg.1 x hx), fun x hx y hy z hz => ?_⟩` and prove the remaining obligations. Establish `h1` using `hf.2 x hx y hy z hz`. Establish `h2` using `hg.2 x hx y hy z hz`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem quad_mul {S : AddSubgroup M} {f g : M → ℂ} (hf : Quad S f) (hg : Quad S g) :
    Quad S (fun x => f x * g x) := by
  refine ⟨fun x hx => mu_mul (hf.1 x hx) (hg.1 x hx), fun x hx y hy z hz => ?_⟩
  have h1 := hf.2 x hx y hy z hz
  have h2 := hg.2 x hx y hy z hz
  calc _ = (f (x + y + z) * f x * f y * f z) * (g (x + y + z) * g x * g y * g z) := by ring
    _ = _ := by rw [h1, h2]; ring

/- English proof (translation)
Use `⟨fun x hx => mu_conj (hf.1 x hx), fun x hx y hy z hz => ?_⟩` and prove the remaining obligations. Establish `h1` using `congrArg conj (hf.2 x hx y hy z hz)`. Simplify `h1` using `only [map_mul]`.
-/
theorem quad_conj {S : AddSubgroup M} {f : M → ℂ} (hf : Quad S f) : Quad S (fun x => conj (f x)) := by
  refine ⟨fun x hx => mu_conj (hf.1 x hx), fun x hx y hy z hz => ?_⟩
  have h1 := congrArg conj (hf.2 x hx y hy z hz)
  simpa only [map_mul] using h1

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun x hx => hf.1 x (h hx), fun x hx y hy z hz => hf.2 x (h hx) y (h hy) z (h hz)⟩`.
-/
theorem quad_mono {S S' : AddSubgroup M} {f : M → ℂ} (h : S' ≤ S) (hf : Quad S f) : Quad S' f :=
  ⟨fun x hx => hf.1 x (h hx), fun x hx y hy z hz => hf.2 x (h hx) y (h hy) z (h hz)⟩

/- English proof (translation)
Use `⟨h1, fun x hx y hy z hz => ?_⟩` and prove the remaining obligations. Establish `h0 : h 0 ≠ 0` using `mu_ne (h1 0 S.zero_mem)`. Establish `e1 : h (x + y) = h x * h y / h 0` using `by rw [eq_div_iff h0]; exact h2 x hx y hy`. Establish `e2 : h (y + z) = h y * h z / h 0` using `by rw [eq_div_iff h0]; exact h2 y hy z hz`. Establish `e3 : h (x + z) = h x * h z / h 0` using `by rw [eq_div_iff h0]; exact h2 x hx z hz`.

Establish `e4 : h (x + y + z) = h (x + y) * h z / h 0`. Rewrite using `[eq_div_iff h0]`. Conclude with `h2 _ (S.add_mem hx hy) z hz`. Rewrite using `[e4, e1, e2, e3]`. Clear the denominators using the available nonvanishing facts.
-/
theorem quad_affine {S : AddSubgroup M} {h : M → ℂ} (h1 : ∀ x ∈ S, IsMu (h x))
    (h2 : ∀ x ∈ S, ∀ y ∈ S, h (x + y) * h 0 = h x * h y) : Quad S h := by
  refine ⟨h1, fun x hx y hy z hz => ?_⟩
  have h0 : h 0 ≠ 0 := mu_ne (h1 0 S.zero_mem)
  have e1 : h (x + y) = h x * h y / h 0 := by rw [eq_div_iff h0]; exact h2 x hx y hy
  have e2 : h (y + z) = h y * h z / h 0 := by rw [eq_div_iff h0]; exact h2 y hy z hz
  have e3 : h (x + z) = h x * h z / h 0 := by rw [eq_div_iff h0]; exact h2 x hx z hz
  have e4 : h (x + y + z) = h (x + y) * h z / h 0 := by
    rw [eq_div_iff h0]; exact h2 _ (S.add_mem hx hy) z hz
  rw [e4, e1, e2, e3]
  field_simp

/- English proof (translation)
Establish `hq : Quad S (fun x => f (x + d) * (f x)⁻¹)`. Use `quad_affine (fun x hx => mu_mul (hf.1 _ (S.add_mem hx hd)) (mu_inv (hf.1 x hx))) fun x hx y hy => ?_` and prove the remaining obligations. Establish `h` using `hf.2 x hx y hy d hd`. Establish `n0` using `mu_ne (hf.1 0 S.zero_mem)`. Establish `nx` using `mu_ne (hf.1 x hx)`.

Establish `ny` using `mu_ne (hf.1 y hy)`. Establish `nxy` using `mu_ne (hf.1 _ (S.add_mem hx hy))`. Simplify using `only [zero_add]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `h`.

Establish `hm` using `quad_mul hf hq`. Establish `key : ∀ x ∈ S, f (x + d) = f x * (f (x + d) * (f x)⁻¹)` using `fun x hx => by`. Establish `nx` using `mu_ne (hf.1 x hx)`. Clear the denominators using the available nonvanishing facts. Use `⟨fun x hx => hf.1 _ (S.add_mem hx hd), fun x hx y hy z hz => ?_⟩` and prove the remaining obligations.

Use `hm.2 x hx y hy z hz` as an intermediate fact. Simplify using `only at this ⊢`. Rewrite `this` using `[← key _ hx, ← key _ hy, ← key _ hz, ← key _ S.zero_mem, ← key _ (S.add_mem hx hy), ← key _ (S.add_mem hy hz), ← key _ (S.add_mem hx hz), ← key _ (S.add_mem (S.add_mem hx hy) hz)]`. Conclude with `this`.
-/
theorem quad_shift {S : AddSubgroup M} {f : M → ℂ} (hf : Quad S f) {d : M} (hd : d ∈ S) :
    Quad S (fun x => f (x + d)) := by
  have hq : Quad S (fun x => f (x + d) * (f x)⁻¹) := by
    refine quad_affine (fun x hx => mu_mul (hf.1 _ (S.add_mem hx hd)) (mu_inv (hf.1 x hx)))
      fun x hx y hy => ?_
    have h := hf.2 x hx y hy d hd
    have n0 := mu_ne (hf.1 0 S.zero_mem)
    have nx := mu_ne (hf.1 x hx)
    have ny := mu_ne (hf.1 y hy)
    have nxy := mu_ne (hf.1 _ (S.add_mem hx hy))
    simp only [zero_add]
    field_simp
    linear_combination h
  have hm := quad_mul hf hq
  have key : ∀ x ∈ S, f (x + d) = f x * (f (x + d) * (f x)⁻¹) := fun x hx => by
    have nx := mu_ne (hf.1 x hx)
    field_simp
  refine ⟨fun x hx => hf.1 _ (S.add_mem hx hd), fun x hx y hy z hz => ?_⟩
  have := hm.2 x hx y hy z hz
  simp only at this ⊢
  rw [← key _ hx, ← key _ hy, ← key _ hz, ← key _ S.zero_mem, ← key _ (S.add_mem hx hy),
    ← key _ (S.add_mem hy hz), ← key _ (S.add_mem hx hz),
    ← key _ (S.add_mem (S.add_mem hx hy) hz)] at this
  exact this

end Quad

variable {κ ι : Type} [Fintype κ] [Fintype ι]

/- English proof (translation)
Unfold `chr`. Rewrite using `[← Complex.exp_add, ← mul_add, ← Rat.cast_add, ← Finset.sum_add_distrib]`. Use `congr 3`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← add_dotProduct]`.

Both sides reduce to the same expression.
-/
theorem chr_add (y x x' : Matrix κ ι ℚ) : chr y (x + x') = chr y x * chr y x' := by
  unfold chr
  rw [← Complex.exp_add, ← mul_add, ← Rat.cast_add, ← Finset.sum_add_distrib]
  congr 3
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← add_dotProduct]; rfl

/- English proof (translation)
Use `⟨q.den, q.den_pos, ?_⟩` and prove the remaining obligations. Rewrite using `[← Complex.exp_nat_mul]`. Establish `h : ((q.den : ℚ) * q) = q.num` using `Rat.den_mul_eq_num q`. Establish `h' : ((q.den : ℂ) * q) = q.num` using `by exact_mod_cast congrArg (fun t : ℚ => (t : ℂ)) h`. Rewrite using `[show (q.den : ℂ) * (2 * Real.pi * I * (q : ℂ)) = ((q.den : ℂ) * q) * (2 * Real.pi * I) by ring, h']`.

Conclude with `Complex.exp_int_mul_two_pi_mul_I _`.
-/
theorem mu_exp (q : ℚ) : IsMu (cexp (2 * Real.pi * I * (q : ℂ))) := by
  refine ⟨q.den, q.den_pos, ?_⟩
  rw [← Complex.exp_nat_mul]
  have h : ((q.den : ℚ) * q) = q.num := Rat.den_mul_eq_num q
  have h' : ((q.den : ℂ) * q) = q.num := by exact_mod_cast congrArg (fun t : ℚ => (t : ℂ)) h
  rw [show (q.den : ℂ) * (2 * Real.pi * I * (q : ℂ)) = ((q.den : ℂ) * q) * (2 * Real.pi * I) by ring, h']
  exact Complex.exp_int_mul_two_pi_mul_I _

/- English proof (translation)
Introduce `k i` and use `by rw [Matrix.smul_apply, smul_eq_mul] exact (isIntegral_algebraMap (R := ℤ) (x := (N : ℤ)) |>.mul (hz k i) : IsIntegral ℤ (_ * _))`.
-/
theorem intM_nsmul (N : ℕ) {z : Matrix κ ι ℚ} (hz : IntM z) : IntM ((N : ℚ) • z) := fun k i => by
  rw [Matrix.smul_apply, smul_eq_mul]
  exact (isIntegral_algebraMap (R := ℤ) (x := (N : ℤ)) |>.mul (hz k i) : IsIntegral ℤ (_ * _))

/- English proof (translation)
Use `⟨∏ p : κ × ι, (y p.1 p.2).den, Finset.prod_pos fun p _ => Rat.den_pos _, fun k i => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩ : (y k i).den ∣ ∏ p : κ × ι, (y p.1 p.2).den` from `Finset.dvd_prod_of_mem (fun p : κ × ι => (y p.1 p.2).den) (Finset.mem_univ (k, i))`. Rewrite using `[hc, Matrix.smul_apply, smul_eq_mul]`. Establish `: (((y k i).den * c : ℕ) : ℚ) * y k i = algebraMap ℤ ℚ (c * (y k i).num)`. Establish `h` using `Rat.den_mul_eq_num (y k i)`.

Simplify using `only [eq_intCast]`. Use `push_cast`. Rewrite using `[← h]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `isIntegral_algebraMap`.
-/
theorem exists_den (y : Matrix κ ι ℚ) : ∃ N : ℕ, 0 < N ∧ IntM ((N : ℚ) • y) := by
  classical
  refine ⟨∏ p : κ × ι, (y p.1 p.2).den, Finset.prod_pos fun p _ => Rat.den_pos _, fun k i => ?_⟩
  obtain ⟨c, hc⟩ : (y k i).den ∣ ∏ p : κ × ι, (y p.1 p.2).den :=
    Finset.dvd_prod_of_mem (fun p : κ × ι => (y p.1 p.2).den) (Finset.mem_univ (k, i))
  rw [hc, Matrix.smul_apply, smul_eq_mul]
  have : (((y k i).den * c : ℕ) : ℚ) * y k i = algebraMap ℤ ℚ (c * (y k i).num) := by
    have h := Rat.den_mul_eq_num (y k i)
    simp only [eq_intCast]
    push_cast
    rw [← h]; ring
  rw [this]
  exact isIntegral_algebraMap

/- English proof (translation)
Establish `h : IsIntegral ℤ (∑ k, ((N : ℚ) • z) k ⬝ᵥ y k)`. Use `IsIntegral.sum _ fun k _ => IsIntegral.sum _ fun i _ => ?_` and prove the remaining obligations. Use `(hz k i).mul (hy k i)` as an intermediate fact. Rewrite `this` using `[Matrix.smul_apply, smul_eq_mul]`. Rewrite using `[Matrix.smul_apply, smul_eq_mul]`.

Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Take `⟨n, hn⟩` from `IsIntegrallyClosed.isIntegral_iff.mp h`. Unfold `chr`. Rewrite using `[← hn, mul_comm]`.

Simplify using `only [eq_intCast, Rat.cast_intCast]`. Conclude with `Complex.exp_int_mul_two_pi_mul_I _`.
-/
theorem chr_eq_one {y z : Matrix κ ι ℚ} {N : ℕ} (hy : IntM ((N : ℚ) • y)) (hz : IntM z) :
    chr y ((N : ℚ) • z) = 1 := by
  have h : IsIntegral ℤ (∑ k, ((N : ℚ) • z) k ⬝ᵥ y k) := by
    refine IsIntegral.sum _ fun k _ => IsIntegral.sum _ fun i _ => ?_
    have := (hz k i).mul (hy k i)
    rw [Matrix.smul_apply, smul_eq_mul] at this
    rw [Matrix.smul_apply, smul_eq_mul]
    convert this using 1; ring
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  unfold chr
  rw [← hn, mul_comm]
  simp only [eq_intCast, Rat.cast_intCast]
  exact Complex.exp_int_mul_two_pi_mul_I _

/- English proof (translation)
Take `⟨R, hR, h1, h2⟩` from `h`. Take `⟨N, hN, hy⟩` from `exists_den y`. Use `⟨N * R, Nat.mul_pos hN hR, fun x hx => ?_, fun x z hz => ?_⟩` and prove the remaining obligations. Use `intM_nsmul N (h1 x (left_ne_zero_of_mul hx))` as an intermediate fact. Rewrite `this` using `[smul_smul, ← Nat.cast_mul]`. Then use the resulting hypothesis.

Establish `e1 : ((N * R : ℕ) : ℚ) • z = (R : ℚ) • ((N : ℚ) • z)`. Rewrite using `[smul_smul, Nat.cast_mul, mul_comm]`. Establish `e2 : ((N * R : ℕ) : ℚ) • z = (N : ℚ) • ((R : ℚ) • z)`. Rewrite using `[smul_smul, Nat.cast_mul]`. Establish `a1 : φ (x + ((N * R : ℕ) : ℚ) • z) = φ x` using `by rw [e1]; exact h2 x _ (intM_nsmul N hz)`.

Establish `a2 : chr y (x + ((N * R : ℕ) : ℚ) • z) = chr y x`. Rewrite using `[chr_add, e2, chr_eq_one hy (intM_nsmul R hz), mul_one]`. Simplify using `only [a1, a2]`.
-/
theorem isSB_mul_chr {φ : Matrix κ ι ℚ → ℂ} (h : IsSB φ) (y : Matrix κ ι ℚ) :
    IsSB (fun x => φ x * chr y x) := by
  obtain ⟨R, hR, h1, h2⟩ := h
  obtain ⟨N, hN, hy⟩ := exists_den y
  refine ⟨N * R, Nat.mul_pos hN hR, fun x hx => ?_, fun x z hz => ?_⟩
  · have := intM_nsmul N (h1 x (left_ne_zero_of_mul hx))
    rwa [smul_smul, ← Nat.cast_mul] at this
  · have e1 : ((N * R : ℕ) : ℚ) • z = (R : ℚ) • ((N : ℚ) • z) := by
      rw [smul_smul, Nat.cast_mul, mul_comm]
    have e2 : ((N * R : ℕ) : ℚ) • z = (N : ℚ) • ((R : ℚ) • z) := by
      rw [smul_smul, Nat.cast_mul]
    have a1 : φ (x + ((N * R : ℕ) : ℚ) • z) = φ x := by rw [e1]; exact h2 x _ (intM_nsmul N hz)
    have a2 : chr y (x + ((N * R : ℕ) : ℚ) • z) = chr y x := by
      rw [chr_add, e2, chr_eq_one hy (intM_nsmul R hz), mul_one]
    simp only [a1, a2]

/- English proof (translation)
Take `⟨hs, c, a, S, f, hc, hf, hφ⟩` from `h`. Use `⟨(isSB_algebra_haar_linear ℚ κ ι φ φ hs hs).2.2.2.1, conj c, a, S, _, ph_conj hc, quad_conj hf, fun x => ?_⟩` and prove the remaining obligations. Simplify using `only [hφ x]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem shape_conj {φ : Matrix κ ι ℚ → ℂ} (h : Shape φ) : Shape (fun x => conj (φ x)) := by
  obtain ⟨hs, c, a, S, f, hc, hf, hφ⟩ := h
  refine ⟨(isSB_algebra_haar_linear ℚ κ ι φ φ hs hs).2.2.2.1, conj c, a, S, _, ph_conj hc, quad_conj hf,
    fun x => ?_⟩
  simp only [hφ x]
  split_ifs <;> simp

/- English proof (translation)
Take `⟨hs, c, a, S, f, hc, hf, hφ⟩` from `h`. Establish `hq : Quad S (fun x => chr y (x + a))`. Use `quad_affine (fun x _ => mu_exp _) fun x _ x' _ => ?_` and prove the remaining obligations. Simplify using `only [← chr_add]`. Use `congr 1`.

Normalize the expressions using the abelian group laws. Use `⟨isSB_mul_chr hs y, c, a, S, _, hc, quad_mul hf hq, fun x => ?_⟩` and prove the remaining obligations. Simplify using `only [hφ x, sub_add_cancel]`. Apply the tactic sequence `split_ifs <;> simp [mul_assoc]`.
-/
theorem shape_chr {φ : Matrix κ ι ℚ → ℂ} (h : Shape φ) (y : Matrix κ ι ℚ) :
    Shape (fun x => φ x * chr y x) := by
  obtain ⟨hs, c, a, S, f, hc, hf, hφ⟩ := h
  have hq : Quad S (fun x => chr y (x + a)) := by
    refine quad_affine (fun x _ => mu_exp _) fun x _ x' _ => ?_
    simp only [← chr_add]
    congr 1; abel
  refine ⟨isSB_mul_chr hs y, c, a, S, _, hc, quad_mul hf hq, fun x => ?_⟩
  simp only [hφ x, sub_add_cancel]
  split_ifs <;> simp [mul_assoc]

/- English proof (translation)
Take `⟨hs, c, a, S, f, hc, hf, hφ⟩` from `h`. Take `⟨hs', c', a', S', f', hc', hf', hψ⟩` from `h'`. Use `⟨(isSB_algebra_haar_linear ℚ κ ι φ ψ hs hs').2.2.1, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hb : ∃ b, b - a ∈ S ∧ b - a' ∈ S'`. Take `⟨b, hb, hb'⟩` from `hb`.

Use `⟨c * c', b, S ⊓ S', _, ph_mul hc hc', quad_mul (quad_mono inf_le_left (quad_shift hf hb)) (quad_mono inf_le_right (quad_shift hf' hb')), fun x => ?_⟩` and prove the remaining obligations. Establish `i1 : x - a ∈ S ↔ x - b ∈ S`. Rewrite using `[show x - a = x - b + (b - a) by abel]; exact S.add_mem_cancel_right hb`. Establish `i2 : x - a' ∈ S' ↔ x - b ∈ S'`. Rewrite using `[show x - a' = x - b + (b - a') by abel]; exact S'.add_mem_cancel_right hb'`.

Simplify using `only [hφ x, hψ x, sub_add_sub_cancel]`. Distinguish the cases in `p : x - b ∈ S`. Distinguish the cases in `p' : x - b ∈ S'`. Rewrite using `[if_pos (i1.2 p), if_pos (i2.2 p'), if_pos (AddSubgroup.mem_inf.2 ⟨p, p'⟩)]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[if_neg (mt i2.1 p'), mul_zero, if_neg (fun q => p' (AddSubgroup.mem_inf.1 q).2)]`. Rewrite using `[if_neg (mt i1.1 p), zero_mul, if_neg (fun q => p (AddSubgroup.mem_inf.1 q).1)]`. Use `⟨0, 0, ⊥, fun _ => 1, ph_zero, ⟨fun _ _ => isMu_one, fun _ _ _ _ _ _ => rfl⟩, fun x => ?_⟩` and prove the remaining obligations. Establish `: φ x * ψ x = 0`. Rewrite using `[hφ x, hψ x]`.

Distinguish the cases in `p : x - a ∈ S`. Establish `p' : x - a' ∉ S'` using `fun p' => hb ⟨x, p, p'⟩`. Simplify using `[p']`. Simplify using `[p]`. Simplify using `[this]`.
-/
theorem shape_mul {φ ψ : Matrix κ ι ℚ → ℂ} (h : Shape φ) (h' : Shape ψ) :
    Shape (fun x => φ x * ψ x) := by
  obtain ⟨hs, c, a, S, f, hc, hf, hφ⟩ := h
  obtain ⟨hs', c', a', S', f', hc', hf', hψ⟩ := h'
  refine ⟨(isSB_algebra_haar_linear ℚ κ ι φ ψ hs hs').2.2.1, ?_⟩
  by_cases hb : ∃ b, b - a ∈ S ∧ b - a' ∈ S'
  · obtain ⟨b, hb, hb'⟩ := hb
    refine ⟨c * c', b, S ⊓ S', _, ph_mul hc hc',
      quad_mul (quad_mono inf_le_left (quad_shift hf hb)) (quad_mono inf_le_right (quad_shift hf' hb')),
      fun x => ?_⟩
    have i1 : x - a ∈ S ↔ x - b ∈ S := by
      rw [show x - a = x - b + (b - a) by abel]; exact S.add_mem_cancel_right hb
    have i2 : x - a' ∈ S' ↔ x - b ∈ S' := by
      rw [show x - a' = x - b + (b - a') by abel]; exact S'.add_mem_cancel_right hb'
    simp only [hφ x, hψ x, sub_add_sub_cancel]
    by_cases p : x - b ∈ S
    · by_cases p' : x - b ∈ S'
      · rw [if_pos (i1.2 p), if_pos (i2.2 p'), if_pos (AddSubgroup.mem_inf.2 ⟨p, p'⟩)]; ring
      · rw [if_neg (mt i2.1 p'), mul_zero, if_neg (fun q => p' (AddSubgroup.mem_inf.1 q).2)]
    · rw [if_neg (mt i1.1 p), zero_mul, if_neg (fun q => p (AddSubgroup.mem_inf.1 q).1)]
  · refine ⟨0, 0, ⊥, fun _ => 1, ph_zero, ⟨fun _ _ => isMu_one, fun _ _ _ _ _ _ => rfl⟩, fun x => ?_⟩
    have : φ x * ψ x = 0 := by
      rw [hφ x, hψ x]
      by_cases p : x - a ∈ S
      · have p' : x - a' ∉ S' := fun p' => hb ⟨x, p, p'⟩
        simp [p']
      · simp [p]
    simp [this]

end GlobalTheory.Phase.ShapeOps

/- English proof (translation)
Introduce `_ _ _ _ _ _ h` and use `⟨ShapeOps.shape_conj h, ShapeOps.shape_chr h, fun _ h' => ShapeOps.shape_mul h h'⟩`.
-/
theorem GlobalTheory.Phase.shape_conj_chr_mul : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι], ∀ φ : Matrix κ ι ℚ → ℂ, Shape φ → Shape (fun x => conj (φ x)) ∧ (∀ y, Shape (fun x => φ x * chr y x)) ∧ ∀ ψ, Shape ψ → Shape (fun x => φ x * ψ x) :=
  fun _ _ _ _ _ _ h => ⟨ShapeOps.shape_conj h, ShapeOps.shape_chr h, fun _ h' => ShapeOps.shape_mul h h'⟩
