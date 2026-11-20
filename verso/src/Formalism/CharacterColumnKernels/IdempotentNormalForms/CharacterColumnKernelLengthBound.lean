import Formalism.CharacterColumnKernels.Statement
import Formalism.CharacterColumnKernels.CharacterColumnKernelLengthBound
import Formalism.CharacterColumnKernels.IdempotentNormalForms.ProdEraseZero

open Finset

namespace Formalism.NG

/- English proof (translation)
Establish `hz' : z.natAbs ≠ 0` using `Int.natAbs_ne_zero.mpr hz`. Rewrite using `[show padicValInt l z = padicValNat l z.natAbs from rfl, padicValNat_eq_emultiplicity hz', ← Int.natCast_emultiplicity, Int.natCast_natAbs]`. Break down `abs_choice z with h | h` into its components or cases. Rewrite using `[h]`. Rewrite using `[h, emultiplicity_neg]`.
-/
private lemma padicValInt_eq_emultiplicity (l : ℕ) [hl : Fact l.Prime] {z : ℤ} (hz : z ≠ 0) :
    (padicValInt l z : ℕ∞) = emultiplicity (l : ℤ) z := by
  have hz' : z.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hz
  rw [show padicValInt l z = padicValNat l z.natAbs from rfl, padicValNat_eq_emultiplicity hz',
    ← Int.natCast_emultiplicity, Int.natCast_natAbs]
  rcases abs_choice z with h | h
  · rw [h]
  · rw [h, emultiplicity_neg]

/- English proof (translation)
Establish `hlp` using `hl.out`. Establish `hE1 : emultiplicity (l : ℤ) (x - 1) = s₀` using `emultiplicity_eq_coe.mpr ⟨hx1, hx2⟩`. Establish `hdvd : (l : ℤ) ∣ x - 1` using `(dvd_pow_self (l : ℤ) (by omega)).trans hx1`. Establish `hlx : ¬ (l : ℤ) ∣ x`. Introduce `h`.

Establish `h1 : (l : ℤ) ∣ 1` using `by have := dvd_sub h hdvd; simpa using this`. Conclude with `(Nat.prime_iff_prime_int.mp hlp).not_dvd_one h1`. Establish `hE : emultiplicity (l : ℤ) (x ^ n - 1) = (s₀ : ℕ∞) + emultiplicity l n`. Break down `hlp.eq_two_or_odd' with h2 | hodd` into its components or cases. Substitute `h2` using the available equality.

Establish `h4 : (4 : ℤ) ∣ x - 1`. Use `(pow_dvd_pow ((2 : ℕ) : ℤ) (hs2 rfl)).trans hx1` as an intermediate fact. Evaluate the numerical expressions using `at this`. Conclude with `this`. Move the coercions through the operations in `at hlx hE1 ⊢`.

Use `Int.two_pow_sub_pow' n h4 hlx` as an intermediate fact. Rewrite `this` using `[one_pow]`. Establish `hc` using `Int.natCast_emultiplicity 2 n`. Move the coercions through the operations in `at hc`. Rewrite using `[this, hE1, hc]`.

Use `Int.emultiplicity_pow_sub_pow hlp hodd (y := 1) hdvd hlx n` as an intermediate fact. Rewrite `this` using `[one_pow]`. Rewrite using `[this, hE1]`. Establish `hfin : emultiplicity (l : ℤ) (x ^ n - 1) = ((s₀ + padicValNat l n : ℕ) : ℕ∞)`. Rewrite using `[hE, ← padicValNat_eq_emultiplicity hn0]`.

Use `norm_cast`. Establish `hne : x ^ n - 1 ≠ 0`. Introduce `h`. Rewrite `hfin` using `[h, emultiplicity_zero]`. Conclude with `ENat.top_ne_coe _ hfin`.

Use `⟨hne, ?_⟩` and prove the remaining obligations. Use `padicValInt_eq_emultiplicity l hne` as an intermediate fact. Rewrite `this` using `[hfin]`. Conclude with `this` after adjusting the coercions.
-/
private lemma padicValInt_pow_sub_one_eq_add (l : ℕ) [hl : Fact l.Prime] (s₀ : ℕ) (hs : 1 ≤ s₀) (hs2 : l = 2 → 2 ≤ s₀)
    (x : ℤ) (hx1 : (l : ℤ) ^ s₀ ∣ x - 1) (hx2 : ¬ (l : ℤ) ^ (s₀ + 1) ∣ x - 1)
    (n : ℕ) (hn0 : n ≠ 0) :
    x ^ n - 1 ≠ 0 ∧ padicValInt l (x ^ n - 1) = s₀ + padicValNat l n := by
  have hlp := hl.out
  have hE1 : emultiplicity (l : ℤ) (x - 1) = s₀ := emultiplicity_eq_coe.mpr ⟨hx1, hx2⟩
  have hdvd : (l : ℤ) ∣ x - 1 := (dvd_pow_self (l : ℤ) (by omega)).trans hx1
  have hlx : ¬ (l : ℤ) ∣ x := by
    intro h
    have h1 : (l : ℤ) ∣ 1 := by have := dvd_sub h hdvd; simpa using this
    exact (Nat.prime_iff_prime_int.mp hlp).not_dvd_one h1
  have hE : emultiplicity (l : ℤ) (x ^ n - 1) = (s₀ : ℕ∞) + emultiplicity l n := by
    rcases hlp.eq_two_or_odd' with h2 | hodd
    · subst h2
      have h4 : (4 : ℤ) ∣ x - 1 := by
        have := (pow_dvd_pow ((2 : ℕ) : ℤ) (hs2 rfl)).trans hx1
        norm_num at this
        exact this
      push_cast at hlx hE1 ⊢
      have := Int.two_pow_sub_pow' n h4 hlx
      rw [one_pow] at this
      have hc := Int.natCast_emultiplicity 2 n
      push_cast at hc
      rw [this, hE1, hc]
    · have := Int.emultiplicity_pow_sub_pow hlp hodd (y := 1) hdvd hlx n
      rw [one_pow] at this
      rw [this, hE1]
  have hfin : emultiplicity (l : ℤ) (x ^ n - 1) = ((s₀ + padicValNat l n : ℕ) : ℕ∞) := by
    rw [hE, ← padicValNat_eq_emultiplicity hn0]
    norm_cast
  have hne : x ^ n - 1 ≠ 0 := by
    intro h
    rw [h, emultiplicity_zero] at hfin
    exact ENat.top_ne_coe _ hfin
  refine ⟨hne, ?_⟩
  have := padicValInt_eq_emultiplicity l hne
  rw [hfin] at this
  exact_mod_cast this

/- English proof (translation)
Introduce `l hl s₀ hs hs2 x hx1 hx2 a b hab`. Establish `hlp` using `Nat.prime_iff_prime_int.mp hl.out`. Take `⟨hne, hv⟩` from `padicValInt_pow_sub_one_eq_add l s₀ hs hs2 x hx1 hx2 (b - a) (by omega)`. Establish `hdvd : (l : ℤ) ∣ x - 1` using `(dvd_pow_self (l : ℤ) (by omega)).trans hx1`. Establish `hlx : ¬ (l : ℤ) ∣ x ^ a`.

Introduce `h`. Establish `h' : (l : ℤ) ∣ x` using `hlp.dvd_of_dvd_pow h`. Establish `h1 : (l : ℤ) ∣ 1` using `by have := dvd_sub h' hdvd; simpa using this`. Conclude with `hlp.not_dvd_one h1`. Establish `hxa : x ^ a ≠ 0` using `fun h ↦ hlx (h ▸ dvd_zero _)`.

Establish `e : x ^ b - x ^ a = x ^ a * (x ^ (b - a) - 1)`. Rewrite using `[mul_sub, ← pow_add, Nat.add_sub_of_le hab.le, mul_one]`. Rewrite using `[e, padicValInt.mul hxa hne, padicValInt.eq_zero_of_not_dvd hlx, zero_add, hv]`.
-/
theorem character_column_kernel_length_bound : characterColumnKernelLengthBound := by
  intro l hl s₀ hs hs2 x hx1 hx2 a b hab
  have hlp := Nat.prime_iff_prime_int.mp hl.out
  obtain ⟨hne, hv⟩ := padicValInt_pow_sub_one_eq_add l s₀ hs hs2 x hx1 hx2 (b - a) (by omega)
  have hdvd : (l : ℤ) ∣ x - 1 := (dvd_pow_self (l : ℤ) (by omega)).trans hx1
  have hlx : ¬ (l : ℤ) ∣ x ^ a := by
    intro h
    have h' : (l : ℤ) ∣ x := hlp.dvd_of_dvd_pow h
    have h1 : (l : ℤ) ∣ 1 := by have := dvd_sub h' hdvd; simpa using this
    exact hlp.not_dvd_one h1
  have hxa : x ^ a ≠ 0 := fun h ↦ hlx (h ▸ dvd_zero _)
  have e : x ^ b - x ^ a = x ^ a * (x ^ (b - a) - 1) := by
    rw [mul_sub, ← pow_add, Nat.add_sub_of_le hab.le, mul_one]
  rw [e, padicValInt.mul hxa hne, padicValInt.eq_zero_of_not_dvd hlx, zero_add, hv]

/- English proof (translation)
Rewrite using `[Fin.univ_succ, Finset.erase_cons, Finset.prod_map]`. Both sides reduce to the same expression.
-/
private lemma prod_univ_erase_zero_eq_prod_succ {M : Type*} [CommMonoid M] (t : ℕ) (f : Fin (t + 1) → M) :
    ∏ i ∈ univ.erase (0 : Fin (t + 1)), f i = ∏ i : Fin t, f i.succ := by
  rw [Fin.univ_succ, Finset.erase_cons, Finset.prod_map]
  rfl

/- English proof (translation)
Introduce `l hl s₀ hs hs2 x hx1 hx2 u hu w t`. Establish `hlp` using `Nat.prime_iff_prime_int.mp hl.out`. Establish `hdvd : (l : ℤ) ∣ x - 1` using `(dvd_pow_self (l : ℤ) (by omega)).trans hx1`. Establish `hlx : ¬ (l : ℤ) ∣ x`. Introduce `h`.

Establish `h1 : (l : ℤ) ∣ 1` using `by have := dvd_sub h hdvd; simpa using this`. Conclude with `hlp.not_dvd_one h1`. Establish `hux : ¬ (l : ℤ) ∣ u * x ^ w`. Introduce `h`. Break down `hlp.dvd_or_dvd h with h | h` into its components or cases.

Conclude with `hu h`. Conclude with `hlx (hlp.dvd_of_dvd_pow h)`. Establish `hux0 : u * x ^ w ≠ 0` using `fun h ↦ hux (h ▸ dvd_zero _)`. Establish `hneg : ∀ z : ℤ, padicValInt l (-z) = padicValInt l z` using `fun z ↦ by simp [padicValInt]`. Establish `hg : ∀ i : ℕ, u * x ^ w - u * x ^ (w + (i + 1)) ≠ 0 ∧ padicValInt l (u * x ^ w - u * x ^ (w + (i + 1))) = s₀ + padicValNat l (i + 1)`.

Introduce `i`. Take `⟨hne, hv⟩` from `padicValInt_pow_sub_one_eq_add l s₀ hs hs2 x hx1 hx2 (i + 1) (by omega)`. Establish `e : u * x ^ w - u * x ^ (w + (i + 1)) = -((u * x ^ w) * (x ^ (i + 1) - 1))` using `by ring`. Establish `hm : (u * x ^ w) * (x ^ (i + 1) - 1) ≠ 0` using `mul_ne_zero hux0 hne`. Use `⟨by rw [e]; exact neg_ne_zero.mpr hm, ?_⟩` and prove the remaining obligations.

Rewrite using `[e, hneg, padicValInt.mul hux0 hne, padicValInt.eq_zero_of_not_dvd hux, zero_add, hv]`. Establish `key : ∀ t : ℕ, (∏ i ∈ Finset.range t, (u * x ^ w - u * x ^ (w + (i + 1)))) ≠ 0 ∧ padicValInt l (∏ i ∈ Finset.range t, (u * x ^ w - u * x ^ (w + (i + 1)))) = t * s₀ + padicValNat l t.factorial`. Introduce `t`. Proceed by induction on `t with`. Consider the case `zero => simp`.

Consider the case `succ k ih`. Rewrite using `[Finset.prod_range_succ]`. Use `⟨mul_ne_zero ih.1 (hg k).1, ?_⟩` and prove the remaining obligations. Rewrite using `[padicValInt.mul ih.1 (hg k).1, ih.2, (hg k).2, Nat.factorial_succ, padicValNat.mul (by omega) (Nat.factorial_ne_zero k)]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hd : delta (fun i : Fin (t + 1) ↦ u * x ^ (w + (i : ℕ))) = ∏ i ∈ Finset.range t, (u * x ^ w - u * x ^ (w + (i + 1)))`. Rewrite using `[delta, prod_univ_erase_zero_eq_prod_succ]`. Simplify using `only [Fin.val_zero, Fin.val_succ, add_zero]`. Conclude with `Fin.prod_univ_eq_prod_range (fun i ↦ u * x ^ w - u * x ^ (w + (i + 1))) t`. Rewrite using `[hd, (key t).2]`.
-/
theorem idempotentNormalForms_fact : characterColumnKernelBlockBound := by
  intro l hl s₀ hs hs2 x hx1 hx2 u hu w t
  have hlp := Nat.prime_iff_prime_int.mp hl.out
  have hdvd : (l : ℤ) ∣ x - 1 := (dvd_pow_self (l : ℤ) (by omega)).trans hx1
  have hlx : ¬ (l : ℤ) ∣ x := by
    intro h
    have h1 : (l : ℤ) ∣ 1 := by have := dvd_sub h hdvd; simpa using this
    exact hlp.not_dvd_one h1
  have hux : ¬ (l : ℤ) ∣ u * x ^ w := by
    intro h
    rcases hlp.dvd_or_dvd h with h | h
    · exact hu h
    · exact hlx (hlp.dvd_of_dvd_pow h)
  have hux0 : u * x ^ w ≠ 0 := fun h ↦ hux (h ▸ dvd_zero _)
  have hneg : ∀ z : ℤ, padicValInt l (-z) = padicValInt l z := fun z ↦ by simp [padicValInt]
  have hg : ∀ i : ℕ, u * x ^ w - u * x ^ (w + (i + 1)) ≠ 0 ∧
      padicValInt l (u * x ^ w - u * x ^ (w + (i + 1))) = s₀ + padicValNat l (i + 1) := by
    intro i
    obtain ⟨hne, hv⟩ := padicValInt_pow_sub_one_eq_add l s₀ hs hs2 x hx1 hx2 (i + 1) (by omega)
    have e : u * x ^ w - u * x ^ (w + (i + 1)) = -((u * x ^ w) * (x ^ (i + 1) - 1)) := by ring
    have hm : (u * x ^ w) * (x ^ (i + 1) - 1) ≠ 0 := mul_ne_zero hux0 hne
    refine ⟨by rw [e]; exact neg_ne_zero.mpr hm, ?_⟩
    rw [e, hneg, padicValInt.mul hux0 hne, padicValInt.eq_zero_of_not_dvd hux, zero_add, hv]
  have key : ∀ t : ℕ, (∏ i ∈ Finset.range t, (u * x ^ w - u * x ^ (w + (i + 1)))) ≠ 0 ∧
      padicValInt l (∏ i ∈ Finset.range t, (u * x ^ w - u * x ^ (w + (i + 1)))) =
        t * s₀ + padicValNat l t.factorial := by
    intro t
    induction t with
    | zero => simp
    | succ k ih =>
      rw [Finset.prod_range_succ]
      refine ⟨mul_ne_zero ih.1 (hg k).1, ?_⟩
      rw [padicValInt.mul ih.1 (hg k).1, ih.2, (hg k).2, Nat.factorial_succ,
        padicValNat.mul (by omega) (Nat.factorial_ne_zero k)]
      ring
  have hd : delta (fun i : Fin (t + 1) ↦ u * x ^ (w + (i : ℕ))) =
      ∏ i ∈ Finset.range t, (u * x ^ w - u * x ^ (w + (i + 1))) := by
    rw [delta, prod_univ_erase_zero_eq_prod_succ]
    simp only [Fin.val_zero, Fin.val_succ, add_zero]
    exact Fin.prod_univ_eq_prod_range (fun i ↦ u * x ^ w - u * x ^ (w + (i + 1))) t
  rw [hd, (key t).2]

end Formalism.NG
