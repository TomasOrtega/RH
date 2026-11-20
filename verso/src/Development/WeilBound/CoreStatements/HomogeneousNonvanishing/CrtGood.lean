import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.ProIsoAt
open NumberField TensorProduct GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.recOnPosPrimePosCoprime with`. Consider the case `prime_pow p k hp _ => intro _ h`. Conclude with `h p k hp dvd_rfl`. Consider the case `zero => intro h`.

Use linear arithmetic over natural numbers and integers. Consider the case `one => intro _ _; exact ⟨x, by simp⟩`. Consider the case `coprime a b ha hb hab iha ihb`. Introduce `_ h`. Take `⟨e, he⟩` from `iha (by omega) fun p k hp hk => h p k hp (hk.mul_right b)`.

Take `⟨f, hf⟩` from `ihb (by omega) fun p k hp hk => h p k hp (hk.mul_left a)`. Take `⟨u, v, huv⟩` from `Nat.isCoprime_iff_coprime.2 hab`. Use `⟨u • f + v • e, ?_⟩` and prove the remaining obligations. Establish `h1 : x = (u * a) • x + (v * b) • x` using `by rw [← add_smul, huv, one_smul]`. Establish `h2 : (u * a) • x = (a * b) • (u • f)`.

Rewrite using `[hf, ← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : (v * b) • x = (a * b) • (v • e)`.

Rewrite using `[he, ← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[smul_add, ← h2, ← h3, ← h1]`.
-/
theorem crt_div {M : Type} [AddCommGroup M] (x : M) : ∀ n : ℕ, 0 < n →
    (∀ p k : ℕ, p.Prime → p ^ k ∣ n → ∃ e, x = p ^ k • e) → ∃ e, x = n • e := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp _ => intro _ h; exact h p k hp dvd_rfl
  | zero => intro h; omega
  | one => intro _ _; exact ⟨x, by simp⟩
  | coprime a b ha hb hab iha ihb =>
    intro _ h
    obtain ⟨e, he⟩ := iha (by omega) fun p k hp hk => h p k hp (hk.mul_right b)
    obtain ⟨f, hf⟩ := ihb (by omega) fun p k hp hk => h p k hp (hk.mul_left a)
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hab
    refine ⟨u • f + v • e, ?_⟩
    have h1 : x = (u * a) • x + (v * b) • x := by rw [← add_smul, huv, one_smul]
    have h2 : (u * a) • x = (a * b) • (u • f) := by
      rw [hf, ← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul]
      congr 1; push_cast; ring
    have h3 : (v * b) • x = (a * b) • (v • e) := by
      rw [he, ← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul]
      congr 1; push_cast; ring
    rw [smul_add, ← h2, ← h3, ← h1]

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `succ j ih`. Take `⟨e, he⟩` from `ih`. Take `⟨e', he'⟩` from `f.compat (k + j) x`.

Use `⟨e + p ^ j • e', ?_⟩` and prove the remaining obligations. Rewrite using `[← add_assoc, he', he, smul_add, smul_smul, ← pow_add, add_assoc]`.
-/
theorem crt_le {p : ℕ} {O : Type} [CommRing O] {L L' : Type} [AddCommGroup L] [Module O L] [AddCommGroup L']
    [Module O L'] {B : LinearMap.BilinForm ℤ L} {B' : LinearMap.BilinForm ℤ L'} (f : ProIsoAt p O B B')
    (k j : ℕ) (x : L) : ∃ e, f.a (k + j) x = f.a k x + p ^ k • e := by
  induction j with
  | zero => exact ⟨0, by simp⟩
  | succ j ih =>
    obtain ⟨e, he⟩ := ih
    obtain ⟨e', he'⟩ := f.compat (k + j) x
    refine ⟨e + p ^ j • e', ?_⟩
    rw [← add_assoc, he', he, smul_add, smul_smul, ← pow_add, add_assoc]

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.recOnPosPrimePosCoprime with`. Consider the case `prime_pow q m hq _`. Use `⟨(f q hq).a m, fun _ p k hp hk x => ?_⟩` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos k with rfl | hk0` into its components or cases.

Conclude with `⟨(f q hq).a m x - (f p hp).a 0 x, by simp⟩`. Establish `hpq : p = q` using `(Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow ((dvd_pow_self p hk0.ne').trans hk))`. Substitute `hpq` using the available equality. Take `⟨j, rfl⟩` from `Nat.exists_eq_add_of_le ((Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hk)`. Conclude with `crt_le _ k j x`.

Consider the case `zero => exact ⟨0, fun h => by omega⟩`. Consider the case `one`. Use `⟨0, fun _ p k hp hk x => ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.dvd_one.1 hk]`. Conclude with `⟨-(f p hp).a k x, by simp⟩`.

Consider the case `coprime a b ha hb hab iha ihb`. Take `⟨A, hA⟩` from `iha`. Take `⟨C, hC⟩` from `ihb`. Take `⟨u, v, huv⟩` from `Nat.isCoprime_iff_coprime.2 hab`. Use `⟨(v * b) • A + (u * a) • C, fun _ p k hp hk x => ?_⟩` and prove the remaining obligations.

Establish `hor : p ^ k ∣ a ∨ p ^ k ∣ b`. Distinguish the cases in `hpa : p ∣ a`. Use `left`. Establish `: Nat.Coprime (p ^ k) b` using `Nat.Coprime.pow_left k (Nat.Coprime.coprime_dvd_left hpa hab)`. Conclude with `this.dvd_of_dvd_mul_right hk`.

Use `right`. Establish `: Nat.Coprime (p ^ k) a` using `Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hpa)`. Conclude with `this.dvd_of_dvd_mul_left hk`. Break down `hor with h | h` into its components or cases. Take `⟨e, he⟩` from `hA (by omega) p k hp h x`.

Take `⟨c, hc⟩` from `h`. Use `⟨e + (u * c) • (C x - A x), ?_⟩` and prove the remaining obligations. Establish `h1 : v * b = 1 - u * a` using `by linarith`. Establish `h2 : p ^ k • ((u * c) • (C x - A x)) = (u * a) • (C x - A x)`. Rewrite using `[← natCast_zsmul, smul_smul]`.

Use `congr 1`. Rewrite using `[hc]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[smul_add, h2, ← add_assoc, ← he, h1]`.

Simplify using `only [LinearMap.add_apply, LinearMap.smul_apply, sub_smul, one_smul, smul_sub, LinearMap.sub_apply]`. Normalize the expressions using the abelian group laws. Take `⟨e, he⟩` from `hC (by omega) p k hp h x`. Take `⟨c, hc⟩` from `h`. Use `⟨e + (v * c) • (A x - C x), ?_⟩` and prove the remaining obligations.

Establish `h1 : u * a = 1 - v * b` using `by linarith`. Establish `h2 : p ^ k • ((v * c) • (A x - C x)) = (v * b) • (A x - C x)`. Rewrite using `[← natCast_zsmul, smul_smul]`. Use `congr 1`. Rewrite using `[hc]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[smul_add, h2, ← add_assoc, ← he, h1]`. Simplify using `only [LinearMap.add_apply, LinearMap.smul_apply, sub_smul, one_smul, smul_sub, LinearMap.sub_apply]`. Normalize the expressions using the abelian group laws.
-/
theorem crt_good {O : Type} [CommRing O] {L L' : Type} [AddCommGroup L] [Module O L] [AddCommGroup L']
    [Module O L'] {B : LinearMap.BilinForm ℤ L} {B' : LinearMap.BilinForm ℤ L'}
    (f : ∀ p : ℕ, p.Prime → ProIsoAt p O B B') : ∀ n : ℕ, ∃ a : L →ₗ[O] L', 0 < n →
      ∀ (p k : ℕ) (hp : p.Prime), p ^ k ∣ n → ∀ x, ∃ e, a x = (f p hp).a k x + p ^ k • e := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow q m hq _ =>
    refine ⟨(f q hq).a m, fun _ p k hp hk x => ?_⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact ⟨(f q hq).a m x - (f p hp).a 0 x, by simp⟩
    · have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).1
        (hp.dvd_of_dvd_pow ((dvd_pow_self p hk0.ne').trans hk))
      subst hpq
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le ((Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hk)
      exact crt_le _ k j x
  | zero => exact ⟨0, fun h => by omega⟩
  | one =>
    refine ⟨0, fun _ p k hp hk x => ?_⟩
    rw [Nat.dvd_one.1 hk]
    exact ⟨-(f p hp).a k x, by simp⟩
  | coprime a b ha hb hab iha ihb =>
    obtain ⟨A, hA⟩ := iha
    obtain ⟨C, hC⟩ := ihb
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hab
    refine ⟨(v * b) • A + (u * a) • C, fun _ p k hp hk x => ?_⟩
    have hor : p ^ k ∣ a ∨ p ^ k ∣ b := by
      by_cases hpa : p ∣ a
      · left
        have : Nat.Coprime (p ^ k) b := Nat.Coprime.pow_left k (Nat.Coprime.coprime_dvd_left hpa hab)
        exact this.dvd_of_dvd_mul_right hk
      · right
        have : Nat.Coprime (p ^ k) a := Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hpa)
        exact this.dvd_of_dvd_mul_left hk
    rcases hor with h | h
    · obtain ⟨e, he⟩ := hA (by omega) p k hp h x
      obtain ⟨c, hc⟩ := h
      refine ⟨e + (u * c) • (C x - A x), ?_⟩
      have h1 : v * b = 1 - u * a := by linarith
      have h2 : p ^ k • ((u * c) • (C x - A x)) = (u * a) • (C x - A x) := by
        rw [← natCast_zsmul, smul_smul]; congr 1; rw [hc]; push_cast; ring
      rw [smul_add, h2, ← add_assoc, ← he, h1]
      simp only [LinearMap.add_apply, LinearMap.smul_apply, sub_smul, one_smul, smul_sub, LinearMap.sub_apply]
      abel
    · obtain ⟨e, he⟩ := hC (by omega) p k hp h x
      obtain ⟨c, hc⟩ := h
      refine ⟨e + (v * c) • (A x - C x), ?_⟩
      have h1 : u * a = 1 - v * b := by linarith
      have h2 : p ^ k • ((v * c) • (A x - C x)) = (v * b) • (A x - C x) := by
        rw [← natCast_zsmul, smul_smul]; congr 1; rw [hc]; push_cast; ring
      rw [smul_add, h2, ← add_assoc, ← he, h1]
      simp only [LinearMap.add_apply, LinearMap.smul_apply, sub_smul, one_smul, smul_sub, LinearMap.sub_apply]
      abel

/- English proof (translation)
Introduce `O _ L L' _ _ _ _ B B' h`. Set `f : ∀ p : ℕ, p.Prime → ProIsoAt p O B B'` to `fun p hp => (h p hp).some`. Use `choose a ha using crt_good f`. Use `⟨⟨a, ?_, ?_, ?_, ?_⟩⟩` and prove the remaining obligations. Introduce `n hn x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy⟩`. Use `crt_div x n hn fun p k hp hk => ?_` and prove the remaining obligations. Take `⟨e, he⟩` from `ha n hn p k hp hk x`. Take `⟨c, hc⟩` from `hk`.

Use `((f p hp).inj k x).1 ⟨c • y - e, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_sub, smul_smul, ← hc, ← hy, he]`. Normalize the expressions using the abelian group laws. Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨a n y, map_nsmul _ _ _⟩`.

Introduce `n hn y`. Take `⟨e, he⟩` from `crt_div ((LinearMap.range (a n)).mkQ y) n hn fun p k hp hk => by`. Take `⟨x, e, rfl⟩` from `(f p hp).surj k y`. Take `⟨e', he'⟩` from `ha n hn p k hp hk x`. Use `⟨(LinearMap.range (a n)).mkQ (e - e'), ?_⟩` and prove the remaining obligations.

Rewrite using `[← map_nsmul, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]`. Conclude with `⟨x, by rw [he', smul_sub]; abel⟩`. Take `⟨e, rfl⟩` from `Submodule.mkQ_surjective _ e`. Rewrite `he` using `[← map_nsmul, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]`. Take `⟨x, hx⟩` from `he`.

Conclude with `⟨x, e, by rw [hx]; abel⟩`. Introduce `n hn x y`. Take `⟨e, he⟩` from `crt_div (B' (a n x) (a n y) - B x y) n hn fun p k hp hk => by`. Take `⟨e, he⟩` from `ha n hn p k hp hk x`. Take `⟨e', he'⟩` from `ha n hn p k hp hk y`.

Take `⟨c, hc⟩` from `(f p hp).isom k x y`. Use `⟨c + B' e (a n y) + B' ((f p hp).a k x) e', ?_⟩` and prove the remaining obligations. Establish `h1 : B' (a n x) (a n y) = B' ((f p hp).a k x) (a n y) + p ^ k • B' e (a n y)`. Rewrite using `[he, map_add, map_nsmul]`. Both sides reduce to the same expression.

Establish `h2 : B' ((f p hp).a k x) (a n y) = B' ((f p hp).a k x) ((f p hp).a k y) + p ^ k • B' ((f p hp).a k x) e'`. Rewrite using `[he', map_add, map_nsmul]`. Rewrite using `[h1, h2]`. Simplify using `only [nsmul_eq_mul]`. Use `push_cast`.

Take the linear combination `hc`. Conclude with `⟨e, by rw [he, nsmul_eq_mul]⟩`. Introduce `n m hn hm x`. Take `⟨e, he⟩` from `crt_div (a (n * m) x - a n x) n hn fun p k hp hk => by`. Take `⟨e, he⟩` from `ha n hn p k hp hk x`.

Take `⟨e', he'⟩` from `ha (n * m) (Nat.mul_pos hn hm) p k hp (hk.mul_right m) x`. Conclude with `⟨e' - e, by rw [he, he', smul_sub]; abel⟩`. Conclude with `⟨e, by rw [← he]; abel⟩`.
-/
theorem tw_crt : ∀ (O : Type) [CommRing O] (L L' : Type) [AddCommGroup L] [Module O L] [AddCommGroup L'] [Module O L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L'), (∀ p : ℕ, p.Prime → Nonempty (ProIsoAt p O B B')) → Nonempty (ProIso O B B') := by
  intro O _ L L' _ _ _ _ B B' h
  let f : ∀ p : ℕ, p.Prime → ProIsoAt p O B B' := fun p hp => (h p hp).some
  choose a ha using crt_good f
  refine ⟨⟨a, ?_, ?_, ?_, ?_⟩⟩
  · intro n hn x
    constructor
    · rintro ⟨y, hy⟩
      refine crt_div x n hn fun p k hp hk => ?_
      obtain ⟨e, he⟩ := ha n hn p k hp hk x
      obtain ⟨c, hc⟩ := hk
      refine ((f p hp).inj k x).1 ⟨c • y - e, ?_⟩
      rw [smul_sub, smul_smul, ← hc, ← hy, he]; abel
    · rintro ⟨y, rfl⟩
      exact ⟨a n y, map_nsmul _ _ _⟩
  · intro n hn y
    obtain ⟨e, he⟩ := crt_div ((LinearMap.range (a n)).mkQ y) n hn fun p k hp hk => by
      obtain ⟨x, e, rfl⟩ := (f p hp).surj k y
      obtain ⟨e', he'⟩ := ha n hn p k hp hk x
      refine ⟨(LinearMap.range (a n)).mkQ (e - e'), ?_⟩
      rw [← map_nsmul, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      exact ⟨x, by rw [he', smul_sub]; abel⟩
    obtain ⟨e, rfl⟩ := Submodule.mkQ_surjective _ e
    rw [← map_nsmul, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at he
    obtain ⟨x, hx⟩ := he
    exact ⟨x, e, by rw [hx]; abel⟩
  · intro n hn x y
    obtain ⟨e, he⟩ := crt_div (B' (a n x) (a n y) - B x y) n hn fun p k hp hk => by
      obtain ⟨e, he⟩ := ha n hn p k hp hk x
      obtain ⟨e', he'⟩ := ha n hn p k hp hk y
      obtain ⟨c, hc⟩ := (f p hp).isom k x y
      refine ⟨c + B' e (a n y) + B' ((f p hp).a k x) e', ?_⟩
      have h1 : B' (a n x) (a n y) = B' ((f p hp).a k x) (a n y) + p ^ k • B' e (a n y) := by
        rw [he, map_add, map_nsmul]; rfl
      have h2 : B' ((f p hp).a k x) (a n y) = B' ((f p hp).a k x) ((f p hp).a k y)
          + p ^ k • B' ((f p hp).a k x) e' := by
        rw [he', map_add, map_nsmul]
      rw [h1, h2]
      simp only [nsmul_eq_mul]
      push_cast
      linear_combination hc
    exact ⟨e, by rw [he, nsmul_eq_mul]⟩
  · intro n m hn hm x
    obtain ⟨e, he⟩ := crt_div (a (n * m) x - a n x) n hn fun p k hp hk => by
      obtain ⟨e, he⟩ := ha n hn p k hp hk x
      obtain ⟨e', he'⟩ := ha (n * m) (Nat.mul_pos hn hm) p k hp (hk.mul_right m) x
      exact ⟨e' - e, by rw [he, he', smul_sub]; abel⟩
    exact ⟨e, by rw [← he]; abel⟩

end PositivityTheory.UnitarySelfGeneration
