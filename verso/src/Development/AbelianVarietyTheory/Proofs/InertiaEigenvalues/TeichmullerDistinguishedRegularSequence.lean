import Mathlib

open scoped NNReal

namespace GlobalTheory

/- English proof (translation)
Take `⟨b, hb⟩` from `h`. Establish `h0 : (((l : ℕ) : WittVector l O) * a).coeff 0 = 0`. Rewrite using `[← WittVector.mem_span_p_iff_coeff_zero_eq_zero]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)`. Rewrite `h0` using `[hb, WittVector.mul_coeff_zero, WittVector.teichmuller_coeff_zero]`.

Establish `hb0 : b.coeff 0 = 0` using `(mul_eq_zero.mp h0).resolve_left hx`. Rewrite `hb0` using `[← WittVector.mem_span_p_iff_coeff_zero_eq_zero, Ideal.mem_span_singleton]`. Take `⟨c, rfl⟩` from `hb0`. Establish `hl : ((l : ℕ) : WittVector l O) ≠ 0` using `WittVector.p_nonzero l O`. Use `⟨c, mul_left_cancel₀ hl ?_⟩` and prove the remaining obligations.

Rewrite using `[hb]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem teichmuller_dvd_of_dvd_natCast_mul (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O]
    [IsDomain O] [CharP O l] [PerfectRing O l] (x : O) (hx : x ≠ 0) (a : WittVector l O)
    (h : WittVector.teichmuller l x ∣ ((l : ℕ) : WittVector l O) * a) :
    WittVector.teichmuller l x ∣ a := by
  obtain ⟨b, hb⟩ := h
  have h0 : (((l : ℕ) : WittVector l O) * a).coeff 0 = 0 := by
    rw [← WittVector.mem_span_p_iff_coeff_zero_eq_zero]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  rw [hb, WittVector.mul_coeff_zero, WittVector.teichmuller_coeff_zero] at h0
  have hb0 : b.coeff 0 = 0 := (mul_eq_zero.mp h0).resolve_left hx
  rw [← WittVector.mem_span_p_iff_coeff_zero_eq_zero, Ideal.mem_span_singleton] at hb0
  obtain ⟨c, rfl⟩ := hb0
  have hl : ((l : ℕ) : WittVector l O) ≠ 0 := WittVector.p_nonzero l O
  refine ⟨c, mul_left_cancel₀ hl ?_⟩
  rw [hb]; ring

/- English proof (translation)
Introduce `l _ O _ _ _ _ x e w E' hx he hw hE`. Establish `hT : WittVector.teichmuller l x ≠ 0`. Introduce `h`. Apply `hx` to reduce the goal to its premises. Rewrite using `[← WittVector.teichmuller_coeff_zero l x, h]`.

Simplify using the standard rewrite rules. Establish `h1 : ∀ a : WittVector l O, WittVector.teichmuller l x ∣ E' * a → WittVector.teichmuller l x ∣ a`. Introduce `a h`. Rewrite `h` using `[hE, add_mul]`. Establish `h2 : WittVector.teichmuller l x ∣ WittVector.teichmuller l x ^ e * a` using `(dvd_pow_self _ he.ne').mul_right a`.

Establish `h3` using `(dvd_add_right h2).mp h`. Rewrite `h3` using `[mul_assoc]`. Conclude with `hw.dvd_mul_left.mp (teichmuller_dvd_of_dvd_natCast_mul l O x hx _ h3)`. Establish `hk : ∀ (k : ℕ) (a : WittVector l O), WittVector.teichmuller l x ^ k ∣ E' * a → WittVector.teichmuller l x ^ k ∣ a`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => intro a _`. Simplify using the standard rewrite rules. Consider the case `succ k ih`. Introduce `a h`.

Take `⟨c, rfl⟩` from `h1 a ((dvd_pow_self _ k.succ_ne_zero).trans h)`. Rewrite `h` using `[pow_succ', mul_left_comm, mul_dvd_mul_iff_left hT]`. Rewrite using `[pow_succ']`. Conclude with `mul_dvd_mul_left _ (ih c h)`. Introduce `k a`.

Use `⟨hk k a, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨b, hb⟩`. Take `⟨c, rfl⟩` from `hk k b ⟨a, hb.symm⟩`. Use `⟨c, mul_left_cancel₀ (pow_ne_zero k hT) ?_⟩` and prove the remaining obligations. Rewrite using `[hb]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem teichmuller_distinguished_regular : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [CharP O l] [PerfectRing O l] (x : O) (e : ℕ) (w E' : WittVector l O), x ≠ 0 → 0 < e → IsUnit w → E' = WittVector.teichmuller l x ^ e + ((l : ℕ) : WittVector l O) * w → ∀ (k : ℕ) (a : WittVector l O), (WittVector.teichmuller l x ^ k ∣ E' * a → WittVector.teichmuller l x ^ k ∣ a) ∧ (E' ∣ WittVector.teichmuller l x ^ k * a → E' ∣ a) := by
  intro l _ O _ _ _ _ x e w E' hx he hw hE
  have hT : WittVector.teichmuller l x ≠ 0 := by
    intro h
    apply hx
    rw [← WittVector.teichmuller_coeff_zero l x, h]
    simp
  have h1 : ∀ a : WittVector l O, WittVector.teichmuller l x ∣ E' * a →
      WittVector.teichmuller l x ∣ a := by
    intro a h
    rw [hE, add_mul] at h
    have h2 : WittVector.teichmuller l x ∣ WittVector.teichmuller l x ^ e * a :=
      (dvd_pow_self _ he.ne').mul_right a
    have h3 := (dvd_add_right h2).mp h
    rw [mul_assoc] at h3
    exact hw.dvd_mul_left.mp (teichmuller_dvd_of_dvd_natCast_mul l O x hx _ h3)
  have hk : ∀ (k : ℕ) (a : WittVector l O), WittVector.teichmuller l x ^ k ∣ E' * a →
      WittVector.teichmuller l x ^ k ∣ a := by
    intro k
    induction k with
    | zero => intro a _; simp
    | succ k ih =>
      intro a h
      obtain ⟨c, rfl⟩ := h1 a ((dvd_pow_self _ k.succ_ne_zero).trans h)
      rw [pow_succ', mul_left_comm, mul_dvd_mul_iff_left hT] at h
      rw [pow_succ']
      exact mul_dvd_mul_left _ (ih c h)
  intro k a
  refine ⟨hk k a, ?_⟩
  rintro ⟨b, hb⟩
  obtain ⟨c, rfl⟩ := hk k b ⟨a, hb.symm⟩
  refine ⟨c, mul_left_cancel₀ (pow_ne_zero k hT) ?_⟩
  rw [hb]; ring

end GlobalTheory
