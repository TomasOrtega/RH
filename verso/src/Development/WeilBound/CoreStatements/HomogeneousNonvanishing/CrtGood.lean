import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.ProIsoAt
open NumberField TensorProduct GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately. Use linear arithmetic over natural numbers and integers.

Treat this case separately. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Proceed by induction. Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
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
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis.

Supply the required witnesses or components. Establish an intermediate fact. Substitute using the available equality. Extract witnesses or component facts from the available result. Treat this case separately.

Treat this case separately. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Treat this case separately.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Consider separately whether the proposition holds or fails. Establish an intermediate fact. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities.

Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws.

A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Supply the required witnesses or components. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations. Take a linear combination of the given relations to obtain the conclusion.

Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Supply the required witnesses or components. A detailed English derivation is pending.
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
