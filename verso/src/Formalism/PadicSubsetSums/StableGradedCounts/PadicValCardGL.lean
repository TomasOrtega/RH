import Formalism.PadicSubsetSums.CentralIdempotents.WindowSums

namespace Formalism.IrreducibleCountingLemmas.WindowSums

/- English proof (translation)
Use `revert h`. Use `Finset.induction_on s (fun _ => by simp) ?_` and prove the remaining obligations. Introduce `a t ha ih h`. Establish `hrest : ∀ i ∈ t, f i ≠ 0` using `fun i hi => h i (Finset.mem_insert_of_mem hi)`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha, padicValNat.mul (h a (Finset.mem_insert_self a t)) (Finset.prod_ne_zero_iff.mpr hrest), ih hrest]`.
-/
theorem padicValNat_finset_prod {ι : Type} (p : ℕ) [Fact p.Prime] (s : Finset ι) (f : ι → ℕ)
    (h : ∀ i ∈ s, f i ≠ 0) : padicValNat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValNat p (f i) := by
  classical
  revert h
  refine Finset.induction_on s (fun _ => by simp) ?_
  intro a t ha ih h
  have hrest : ∀ i ∈ t, f i ≠ 0 := fun i hi => h i (Finset.mem_insert_of_mem hi)
  rw [Finset.prod_insert ha, Finset.sum_insert ha,
    padicValNat.mul (h a (Finset.mem_insert_self a t)) (Finset.prod_ne_zero_iff.mpr hrest),
    ih hrest]

/- English proof (translation)
Establish `h1 : q ^ r = q ^ i * q ^ (r - i)` using `by rw [← pow_add, Nat.add_sub_cancel' hi.le]`. Establish `h2 : 1 ≤ q ^ (r - i)` using `Nat.one_le_pow _ _ hq`. Take `⟨k, hk⟩ : ∃ k, q ^ (r - i) = k + 1` from `⟨q ^ (r - i) - 1, (Nat.sub_add_cancel h2).symm⟩`. Rewrite using `[h1, hk]`. Simplify using `[mul_add]`.
-/
private theorem pow_sub_pow_eq_pow_mul_pow_sub_one_of_lt (q r i : ℕ) (hq : 0 < q) (hi : i < r) :
    q ^ r - q ^ i = q ^ i * (q ^ (r - i) - 1) := by
  have h1 : q ^ r = q ^ i * q ^ (r - i) := by rw [← pow_add, Nat.add_sub_cancel' hi.le]
  have h2 : 1 ≤ q ^ (r - i) := Nat.one_le_pow _ _ hq
  obtain ⟨k, hk⟩ : ∃ k, q ^ (r - i) = k + 1 := ⟨q ^ (r - i) - 1, (Nat.sub_add_cancel h2).symm⟩
  rw [h1, hk]
  simp [mul_add]

/- English proof (translation)
Establish `hq0 : 0 < q` using `by omega`. Establish `hbig : ∀ i ∈ Finset.range r, q ^ (r - i) - 1 ≠ 0`. Introduce `i hi`. Establish `hi' : i < r` using `Finset.mem_range.mp hi`. Establish `h3 : q ≤ q ^ (r - i)`.

Simplify using `using Nat.pow_le_pow_right hq0 (show 1 ≤ r - i by omega)`. Use linear arithmetic over natural numbers and integers. Establish `hne : ∀ i ∈ Finset.range r, q ^ r - q ^ i ≠ 0`. Introduce `i hi`. Rewrite using `[pow_sub_pow_eq_pow_mul_pow_sub_one_of_lt q r i hq0 (Finset.mem_range.mp hi)]`.

Conclude with `Nat.mul_ne_zero (pow_ne_zero _ hq0.ne') (hbig i hi)`. Establish `term : ∀ i ∈ Finset.range r, padicValNat g (q ^ r - q ^ i) = i * padicValNat g q + padicValNat g (q ^ (r - i) - 1)`. Introduce `i hi`. Rewrite using `[pow_sub_pow_eq_pow_mul_pow_sub_one_of_lt q r i hq0 (Finset.mem_range.mp hi), padicValNat.mul (pow_ne_zero _ hq0.ne') (hbig i hi), padicValNat.pow]`. Rewrite using `[padicValNat_finset_prod g _ _ hne, Finset.sum_congr rfl term, Finset.sum_add_distrib, ← Finset.sum_mul]`.

Use `congr 1`. Apply `Finset.sum_nbij' (fun i => r - i) (fun a => r - a)` to reduce the goal to its premises. Apply the tactic sequence `all_goals intro a ha`. Apply the tactic sequence `all_goals (try simp only [Finset.mem_range, Finset.mem_Icc] at ha ⊢)`. Apply the tactic sequence `all_goals (first | rfl | omega)`.
-/
theorem padicValNat_prod_pow_sub (g q r : ℕ) [Fact g.Prime] (hq : 2 ≤ q) :
    padicValNat g (∏ i ∈ Finset.range r, (q ^ r - q ^ i)) =
      (∑ i ∈ Finset.range r, i) * padicValNat g q +
        ∑ a ∈ Finset.Icc 1 r, padicValNat g (q ^ a - 1) := by
  have hq0 : 0 < q := by omega
  have hbig : ∀ i ∈ Finset.range r, q ^ (r - i) - 1 ≠ 0 := by
    intro i hi
    have hi' : i < r := Finset.mem_range.mp hi
    have h3 : q ≤ q ^ (r - i) := by
      simpa using Nat.pow_le_pow_right hq0 (show 1 ≤ r - i by omega)
    omega
  have hne : ∀ i ∈ Finset.range r, q ^ r - q ^ i ≠ 0 := by
    intro i hi
    rw [pow_sub_pow_eq_pow_mul_pow_sub_one_of_lt q r i hq0 (Finset.mem_range.mp hi)]
    exact Nat.mul_ne_zero (pow_ne_zero _ hq0.ne') (hbig i hi)
  have term : ∀ i ∈ Finset.range r, padicValNat g (q ^ r - q ^ i) =
      i * padicValNat g q + padicValNat g (q ^ (r - i) - 1) := by
    intro i hi
    rw [pow_sub_pow_eq_pow_mul_pow_sub_one_of_lt q r i hq0 (Finset.mem_range.mp hi),
      padicValNat.mul (pow_ne_zero _ hq0.ne') (hbig i hi), padicValNat.pow]
  rw [padicValNat_finset_prod g _ _ hne, Finset.sum_congr rfl term, Finset.sum_add_distrib,
    ← Finset.sum_mul]
  congr 1
  apply Finset.sum_nbij' (fun i => r - i) (fun a => r - a)
  all_goals intro a ha
  all_goals (try simp only [Finset.mem_range, Finset.mem_Icc] at ha ⊢)
  all_goals (first | rfl | omega)

/- English proof (translation)
Establish `: NeZero q` using `⟨(Fact.out : q.Prime).ne_zero⟩`. Rewrite using `[Matrix.card_GL_field, ZMod.card]`. Conclude with `Fin.prod_univ_eq_prod_range (fun i => q ^ r - q ^ i) r`.
-/
theorem card_GL_zmod (q r : ℕ) [Fact q.Prime] :
    Nat.card (Matrix.GeneralLinearGroup (Fin r) (ZMod q)) =
      ∏ i ∈ Finset.range r, (q ^ r - q ^ i) := by
  have : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  rw [Matrix.card_GL_field, ZMod.card]
  exact Fin.prod_univ_eq_prod_range (fun i => q ^ r - q ^ i) r

/- English proof (translation)
Unfold `GLCardVal`. Introduce `g g' r instg instg' hne`. Establish `hg : g.Prime` using `instg.out`. Establish `hg' : g'.Prime` using `instg'.out`. Prove the components needed by the constructor for the conclusion.

Rewrite using `[card_GL_zmod, padicValNat_prod_pow_sub g g r hg.two_le, padicValNat_self, mul_one, Finset.sum_range_id, Finset.sum_eq_zero, add_zero]`. Introduce `a ha`. Apply `padicValNat.eq_zero_of_not_dvd` to reduce the goal to its premises. Introduce `hd`. Establish `ha1 : 1 ≤ a` using `(Finset.mem_Icc.mp ha).1`.

Establish `h1 : g ∣ g ^ a` using `dvd_pow_self g (by omega)`. Establish `h2 : 1 ≤ g ^ a` using `Nat.one_le_pow _ _ hg.pos`. Establish `h3 : g ∣ g ^ a - (g ^ a - 1)` using `by first`. Consider the case `exact Nat.dvd_sub' h1 hd`. Consider the case `exact Nat.dvd_sub h1 hd`.

Rewrite `h3` using `[Nat.sub_sub_self h2]`. Conclude with `hg.one_lt.ne' (Nat.dvd_one.mp h3)`. Rewrite using `[card_GL_zmod, padicValNat_prod_pow_sub g g' r hg'.two_le]`. Establish `h0 : padicValNat g g' = 0` using `padicValNat.eq_zero_of_not_dvd fun hd => hne ((Nat.prime_dvd_prime_iff_eq hg hg').mp hd)`. Rewrite using `[h0, mul_zero, zero_add]`.
-/
theorem padicValCardGeneralLinear : GLCardVal := by
  unfold GLCardVal
  intro g g' r instg instg' hne
  have hg : g.Prime := instg.out
  have hg' : g'.Prime := instg'.out
  constructor
  · rw [card_GL_zmod, padicValNat_prod_pow_sub g g r hg.two_le, padicValNat_self,
      mul_one, Finset.sum_range_id, Finset.sum_eq_zero, add_zero]
    intro a ha
    apply padicValNat.eq_zero_of_not_dvd
    intro hd
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
    have h1 : g ∣ g ^ a := dvd_pow_self g (by omega)
    have h2 : 1 ≤ g ^ a := Nat.one_le_pow _ _ hg.pos
    have h3 : g ∣ g ^ a - (g ^ a - 1) := by
      first
        | exact Nat.dvd_sub' h1 hd
        | exact Nat.dvd_sub h1 hd
    rw [Nat.sub_sub_self h2] at h3
    exact hg.one_lt.ne' (Nat.dvd_one.mp h3)
  · rw [card_GL_zmod, padicValNat_prod_pow_sub g g' r hg'.two_le]
    have h0 : padicValNat g g' = 0 :=
      padicValNat.eq_zero_of_not_dvd fun hd => hne ((Nat.prime_dvd_prime_iff_eq hg hg').mp hd)
    rw [h0, mul_zero, zero_add]

end Formalism.IrreducibleCountingLemmas.WindowSums
