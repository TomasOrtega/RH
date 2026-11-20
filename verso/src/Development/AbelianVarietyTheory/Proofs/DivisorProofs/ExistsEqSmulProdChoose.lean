import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

namespace GlobalTheory.SymCocycleMV

/- English proof (translation)
The claim follows from `| 0, x => by simp [Nat.ModEq] | j + 1, x => by have h := @Choose.choose_modEq_choose_mod_mul_choose_div_nat x (p * p ^ j) p _ rw [Nat.mul_mod_right, Nat.choose_zero_right, one_mul, Nat.mul_div_cancel_left _ hp.out.pos] at h rw [pow_succ'] refine h.trans ?_ rw [← Nat.div_div_eq_di …`.
-/
theorem choose_pow_modEq (p : ℕ) [hp : Fact p.Prime] : ∀ (j x : ℕ), x.choose (p ^ j) ≡ x / p ^ j [MOD p]
  | 0, x => by simp [Nat.ModEq]
  | j + 1, x => by
    have h := @Choose.choose_modEq_choose_mod_mul_choose_div_nat x (p * p ^ j) p _
    rw [Nat.mul_mod_right, Nat.choose_zero_right, one_mul, Nat.mul_div_cancel_left _ hp.out.pos] at h
    rw [pow_succ']
    refine h.trans ?_
    rw [← Nat.div_div_eq_div_mul]
    exact choose_pow_modEq p j (x / p)

/- English proof (translation)
The claim follows from `not_congr ((choose_pow_modEq p j x).dvd_iff dvd_rfl)`.
-/
theorem not_dvd_choose_pow_iff (p : ℕ) [hp : Fact p.Prime] (j x : ℕ) :
    ¬ p ∣ x.choose (p ^ j) ↔ ¬ p ∣ x / p ^ j :=
  not_congr ((choose_pow_modEq p j x).dvd_iff dvd_rfl)

/- English proof (translation)
Introduce `s`. Proceed by induction on `s with`. Consider the case `zero`. Introduce `A B hB`. Establish `: B = 0` using `by simpa using hB`.

Substitute `this` using the available equality. Simplify using `using hp.out.not_dvd_one`. Consider the case `succ s ih`. Introduce `A B hB hd`. Establish `h` using `@Choose.choose_modEq_choose_mod_mul_choose_div_nat (p ^ (s + 1) * A + B) B p _`.

Establish `e0 : p ^ (s + 1) * A + B = B + p * (p ^ s * A)` using `by ring`. Rewrite `h` using `[e0, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ hp.out.pos, Nat.choose_self, one_mul]`. Establish `hB' : B / p < p ^ s`. Rewrite using `[Nat.div_lt_iff_lt_mul hp.out.pos, ← pow_succ]`. Conclude with `hB`.

Apply `ih A (B / p) hB'` to reduce the goal to its premises. Rewrite using `[add_comm (p ^ s * A)]`. Rewrite `hd` using `[e0]`. Conclude with `(h.dvd_iff dvd_rfl).1 hd`.
-/
theorem not_dvd_choose_pow_mul_add (p : ℕ) [hp : Fact p.Prime] :
    ∀ (s A B : ℕ), B < p ^ s → ¬ p ∣ (p ^ s * A + B).choose B := by
  intro s
  induction s with
  | zero =>
    intro A B hB
    have : B = 0 := by simpa using hB
    subst this; simpa using hp.out.not_dvd_one
  | succ s ih =>
    intro A B hB hd
    have h := @Choose.choose_modEq_choose_mod_mul_choose_div_nat (p ^ (s + 1) * A + B) B p _
    have e0 : p ^ (s + 1) * A + B = B + p * (p ^ s * A) := by ring
    rw [e0, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ hp.out.pos, Nat.choose_self,
      one_mul] at h
    have hB' : B / p < p ^ s := by
      rw [Nat.div_lt_iff_lt_mul hp.out.pos, ← pow_succ]; exact hB
    apply ih A (B / p) hB'
    rw [add_comm (p ^ s * A)]
    rw [e0] at hd
    exact (h.dvd_iff dvd_rfl).1 hd

/- English proof (translation)
Rewrite using `[Finset.prod_eq_single i]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Finsupp.single_apply, Ne.symm hb]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ i) h`.
-/
theorem prod_choose_single {d : ℕ} (y : Fin d →₀ ℕ) (i : Fin d) (q : ℕ) :
    ∏ k, (y k).choose (Finsupp.single i q k) = (y i).choose q := by
  rw [Finset.prod_eq_single i]
  · simp
  · intro b _ hb; simp [Finsupp.single_apply, Ne.symm hb]
  · intro h; exact absurd (Finset.mem_univ i) h

variable {p : ℕ} [hp : Fact p.Prime] {M : Type} [AddCommGroup M] {d : ℕ}

def IsSym (n : Fin d →₀ ℕ) (c : (Fin d →₀ ℕ) → M) : Prop := ∀ a, a ≤ n → c a = c (n - a)

def IsRel (n : Fin d →₀ ℕ) (c : (Fin d →₀ ℕ) → M) : Prop :=
  ∀ a b, a ≠ 0 → b ≠ 0 → a + b ≤ n → a + b ≠ n →
    (∏ i, Nat.choose ((a + b : Fin d →₀ ℕ) i) (a i)) • c (a + b) =
      (∏ i, Nat.choose ((n - a : Fin d →₀ ℕ) i) (b i)) • c a

omit hp in
/- English proof (translation)
Establish `hc : Nat.Coprime k p` using `Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hpp).2 hk)`. Conclude with `(hu k hc).1 (by simp only [h, smul_zero])`.
-/
theorem smul_eq_zero_of_not_dvd (hu : ∀ k : ℕ, Nat.Coprime k p → Function.Bijective fun m : M => k • m)
    (hpp : p.Prime) {k : ℕ} (hk : ¬ p ∣ k) {m : M} (h : k • m = 0) : m = 0 := by
  have hc : Nat.Coprime k p := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hpp).2 hk)
  exact (hu k hc).1 (by simp only [h, smul_zero])

/- English proof (translation)
Distinguish the cases in `he : x = y`. Rewrite using `[← he]`. Conclude with `h0`. Establish `hb : y - x ≠ 0`. Introduce `h`.

Conclude with `he (le_antisymm hxy (tsub_eq_zero_iff_le.1 h))`. Establish `h` using `hrel x (y - x) hx hb (by rwa [add_tsub_cancel_of_le hxy]) (by rwa [add_tsub_cancel_of_le hxy])`. Rewrite `h` using `[add_tsub_cancel_of_le hxy, h0, smul_zero]`. Conclude with `smul_eq_zero_of_not_dvd hu hp.out hd h`.
-/
theorem eq_zero_of_le (n : Fin d →₀ ℕ) (c : (Fin d →₀ ℕ) → M)
    (hu : ∀ k : ℕ, Nat.Coprime k p → Function.Bijective fun m : M => k • m) (hrel : IsRel n c)
    (x y : Fin d →₀ ℕ) (hx : x ≠ 0) (hxy : x ≤ y) (hy : y ≤ n) (hyn : y ≠ n)
    (hd : ¬ p ∣ ∏ k, (y k).choose (x k)) (h0 : c x = 0) : c y = 0 := by
  by_cases he : x = y
  · rw [← he]; exact h0
  · have hb : y - x ≠ 0 := by
      intro h; exact he (le_antisymm hxy (tsub_eq_zero_iff_le.1 h))
    have h := hrel x (y - x) hx hb (by rwa [add_tsub_cancel_of_le hxy]) (by rwa [add_tsub_cancel_of_le hxy])
    rw [add_tsub_cancel_of_le hxy, h0, smul_zero] at h
    exact smul_eq_zero_of_not_dvd hu hp.out hd h

/- English proof (translation)
Introduce `hd`. Take `⟨k, -, hk⟩` from `(Prime.dvd_finset_prod_iff hp.out.prime f).1 hd`. Conclude with `h k hk`.
-/
theorem not_dvd_prod (f : Fin d → ℕ) (h : ∀ k, ¬ p ∣ f k) : ¬ p ∣ ∏ k, f k := by
  intro hd
  obtain ⟨k, -, hk⟩ := (Prime.dvd_finset_prod_iff hp.out.prime f).1 hd
  exact h k hk

/- English proof (translation)
Introduce `a han ha0 han'`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, a i ≠ 0 := by`. Assume the negation of the conclusion as `h; push_neg at h; exact ha0 (Finsupp.ext fun i => by simp [h i])`. Take `⟨j, m, hm, he⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hi p hp.out.one_lt.ne'`. Establish `hm0 : 0 < m` using `Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at he; exact hi he)`.

Establish `hja : p ^ j ≤ a i` using `by rw [he]; exact Nat.le_mul_of_pos_right _ hm0`. Establish `hle : Finsupp.single i (p ^ j) ≤ a` using `Finsupp.single_le_iff.2 hja`. Establish `hne : Finsupp.single i (p ^ j) ≠ n` using `fun h => han' (le_antisymm han (h ▸ hle))`. Establish `hjn : p ^ j ≤ n i` using `le_trans hja (Finsupp.le_def.1 han i)`. Use `eq_zero_of_le n c hu hrel _ a (Finsupp.single_ne_zero.2 (pow_ne_zero _ hp.out.ne_zero)) hle han han' ?_ (hat i j hjn hne)` and prove the remaining obligations.

Rewrite using `[prod_choose_single, not_dvd_choose_pow_iff, he, Nat.mul_div_cancel_left _ (pow_pos hp.out.pos j)]`. Conclude with `hm`.
-/
theorem eq_zero_of_atoms (n : Fin d →₀ ℕ) (c : (Fin d →₀ ℕ) → M)
    (hu : ∀ k : ℕ, Nat.Coprime k p → Function.Bijective fun m : M => k • m) (hrel : IsRel n c)
    (hat : ∀ i j, p ^ j ≤ n i → Finsupp.single i (p ^ j) ≠ n → c (Finsupp.single i (p ^ j)) = 0) :
    ∀ a, a ≤ n → a ≠ 0 → a ≠ n → c a = 0 := by
  intro a han ha0 han'
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h; push_neg at h; exact ha0 (Finsupp.ext fun i => by simp [h i])
  obtain ⟨j, m, hm, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd hi p hp.out.one_lt.ne'
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at he; exact hi he)
  have hja : p ^ j ≤ a i := by rw [he]; exact Nat.le_mul_of_pos_right _ hm0
  have hle : Finsupp.single i (p ^ j) ≤ a := Finsupp.single_le_iff.2 hja
  have hne : Finsupp.single i (p ^ j) ≠ n := fun h => han' (le_antisymm han (h ▸ hle))
  have hjn : p ^ j ≤ n i := le_trans hja (Finsupp.le_def.1 han i)
  refine eq_zero_of_le n c hu hrel _ a (Finsupp.single_ne_zero.2 (pow_ne_zero _ hp.out.ne_zero))
    hle han han' ?_ (hat i j hjn hne)
  rw [prod_choose_single, not_dvd_choose_pow_iff, he, Nat.mul_div_cancel_left _ (pow_pos hp.out.pos j)]
  exact hm

/- English proof (translation)
Introduce `h`. Use `congrArg (fun f : Fin d →₀ ℕ => f i) h` as an intermediate fact. Simplify using `only [Finsupp.tsub_apply, Finsupp.single_eq_same] at this`. Use linear arithmetic over natural numbers and integers.
-/
theorem tsub_single_ne (n : Fin d →₀ ℕ) (i : Fin d) (q : ℕ) (hq : 0 < q) (hqn : q ≤ n i) :
    n - Finsupp.single i q ≠ n := by
  intro h
  have := congrArg (fun f : Fin d →₀ ℕ => f i) h
  simp only [Finsupp.tsub_apply, Finsupp.single_eq_same] at this
  omega

/- English proof (translation)
Introduce `i j hii hj`. Establish `htn : Finsupp.single i (p ^ j) ≤ n` using `Finsupp.single_le_iff.2 hj`. Rewrite using `[hsym _ htn]`. Use `eq_zero_of_le n c hu hrel _ _ (Finsupp.single_ne_zero.2 (pow_ne_zero _ hp.out.ne_zero)) ?_ tsub_le_self (tsub_single_ne n i _ (pow_pos hp.out.pos j) hj) ?_ h0` and prove the remaining obligations. Rewrite using `[Finsupp.single_le_iff, Finsupp.tsub_apply, Finsupp.single_apply, if_neg hii, Nat.sub_zero]`.

Conclude with `hjn'`. Rewrite using `[prod_choose_single, not_dvd_choose_pow_iff, Finsupp.tsub_apply, Finsupp.single_apply, if_neg hii, Nat.sub_zero]`. Conclude with `hj'`.
-/
theorem atom_cross (n : Fin d →₀ ℕ) (c : (Fin d →₀ ℕ) → M)
    (hu : ∀ k : ℕ, Nat.Coprime k p → Function.Bijective fun m : M => k • m) (hrel : IsRel n c)
    (hsym : IsSym n c) (i' : Fin d) (j' : ℕ) (hj' : ¬ p ∣ n i' / p ^ j') (hjn' : p ^ j' ≤ n i')
    (h0 : c (Finsupp.single i' (p ^ j')) = 0) :
    ∀ i j, i ≠ i' → p ^ j ≤ n i → c (Finsupp.single i (p ^ j)) = 0 := by
  intro i j hii hj
  have htn : Finsupp.single i (p ^ j) ≤ n := Finsupp.single_le_iff.2 hj
  rw [hsym _ htn]
  refine eq_zero_of_le n c hu hrel _ _ (Finsupp.single_ne_zero.2 (pow_ne_zero _ hp.out.ne_zero)) ?_
    tsub_le_self (tsub_single_ne n i _ (pow_pos hp.out.pos j) hj) ?_ h0
  · rw [Finsupp.single_le_iff, Finsupp.tsub_apply, Finsupp.single_apply, if_neg hii, Nat.sub_zero]
    exact hjn'
  · rw [prod_choose_single, not_dvd_choose_pow_iff, Finsupp.tsub_apply, Finsupp.single_apply, if_neg hii,
      Nat.sub_zero]
    exact hj'

/- English proof (translation)
Introduce `j hj`. Establish `hps : 0 < p ^ s` using `pow_pos hp.out.pos s`. Establish `hpj : 0 < p ^ j` using `pow_pos hp.out.pos j`. Establish `htn : Finsupp.single i0 (p ^ j) ≤ n` using `Finsupp.single_le_iff.2 hj.le`. Establish `hyn` using `tsub_single_ne n i0 _ hpj hj.le`.

Rewrite using `[hsym _ htn]`. Take `⟨K', rfl⟩ : ∃ K', K = K' + 1` from `⟨K - 1, by omega⟩`. Establish `hK1 : p ^ s ≤ p ^ s * K'` using `Nat.le_mul_of_pos_right _ (by omega)`. Establish `hN' : n i0 = p ^ s * K' + p ^ s` using `by rw [hN]; ring`. Break down `(show j ≤ s ∨ s < j from (by omega)) with hjs | hjs` into its components or cases.

Establish `hjs' : p ^ j ≤ p ^ s` using `Nat.pow_le_pow_right hp.out.pos hjs`. Establish `hsn : Finsupp.single i0 (p ^ s) ≤ n` using `Finsupp.single_le_iff.2 (by omega)`. Establish `hx0 : c (n - Finsupp.single i0 (p ^ s)) = 0` using `by rw [← hsym _ hsn]; exact h0`. Use `eq_zero_of_le n c hu hrel _ _ ?_ ?_ tsub_le_self hyn ?_ hx0` and prove the remaining obligations. Introduce `h`.

Use `congrArg (fun f : Fin d →₀ ℕ => f i0) h` as an intermediate fact. Simplify using `only [Finsupp.tsub_apply, Finsupp.single_eq_same, Finsupp.coe_zero, Pi.zero_apply] at this`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Finsupp.le_def]`. Introduce `k`.

Simplify using `only [Finsupp.tsub_apply, Finsupp.single_apply]`. Apply the tactic sequence `split_ifs <;> omega`. Apply `not_dvd_prod` to reduce the goal to its premises. Introduce `k`. Distinguish the cases in `hk : k = i0`.

Substitute `hk` using the available equality. Simplify using `only [Finsupp.tsub_apply, Finsupp.single_eq_same]`. Establish `e1 : n k - p ^ j = p ^ s * K' + (p ^ s - p ^ j)` using `by omega`. Establish `e2 : n k - p ^ s = p ^ s * K'` using `by omega`. Rewrite using `[e1, e2, Nat.choose_symm_add]`.

Conclude with `not_dvd_choose_pow_mul_add p s K' _ (by omega)`. Simplify using `only [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (Ne.symm hk), Nat.sub_zero, Nat.choose_self]`. Conclude with `hp.out.not_dvd_one`. Establish `hq` using `hK' j hjs hj`. Establish `hle : p ^ s ≤ n i0 - p ^ j`.

Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Conclude with `hq (by rw [Nat.div_eq_of_lt hlt]; exact dvd_zero p)`. Use `eq_zero_of_le n c hu hrel _ _ (Finsupp.single_ne_zero.2 hps.ne') ?_ tsub_le_self hyn ?_ h0` and prove the remaining obligations. Rewrite using `[Finsupp.single_le_iff, Finsupp.tsub_apply, Finsupp.single_eq_same]`.

Conclude with `hle`. Rewrite using `[prod_choose_single, not_dvd_choose_pow_iff, Finsupp.tsub_apply, Finsupp.single_eq_same]`. Conclude with `hq`.
-/
theorem atom_line (n : Fin d →₀ ℕ) (c : (Fin d →₀ ℕ) → M)
    (hu : ∀ k : ℕ, Nat.Coprime k p → Function.Bijective fun m : M => k • m) (hrel : IsRel n c)
    (hsym : IsSym n c) (i0 : Fin d) (s K : ℕ) (hN : n i0 = p ^ s * K) (hK : 2 ≤ K)
    (hK' : ∀ j, s < j → p ^ j < n i0 → ¬ p ∣ (n i0 - p ^ j) / p ^ s)
    (h0 : c (Finsupp.single i0 (p ^ s)) = 0) :
    ∀ j, p ^ j < n i0 → c (Finsupp.single i0 (p ^ j)) = 0 := by
  intro j hj
  have hps : 0 < p ^ s := pow_pos hp.out.pos s
  have hpj : 0 < p ^ j := pow_pos hp.out.pos j
  have htn : Finsupp.single i0 (p ^ j) ≤ n := Finsupp.single_le_iff.2 hj.le
  have hyn := tsub_single_ne n i0 _ hpj hj.le
  rw [hsym _ htn]
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  have hK1 : p ^ s ≤ p ^ s * K' := Nat.le_mul_of_pos_right _ (by omega)
  have hN' : n i0 = p ^ s * K' + p ^ s := by rw [hN]; ring
  rcases (show j ≤ s ∨ s < j from (by omega)) with hjs | hjs
  · have hjs' : p ^ j ≤ p ^ s := Nat.pow_le_pow_right hp.out.pos hjs
    have hsn : Finsupp.single i0 (p ^ s) ≤ n := Finsupp.single_le_iff.2 (by omega)
    have hx0 : c (n - Finsupp.single i0 (p ^ s)) = 0 := by rw [← hsym _ hsn]; exact h0
    refine eq_zero_of_le n c hu hrel _ _ ?_ ?_ tsub_le_self hyn ?_ hx0
    · intro h
      have := congrArg (fun f : Fin d →₀ ℕ => f i0) h
      simp only [Finsupp.tsub_apply, Finsupp.single_eq_same, Finsupp.coe_zero, Pi.zero_apply] at this
      omega
    · rw [Finsupp.le_def]; intro k
      simp only [Finsupp.tsub_apply, Finsupp.single_apply]
      split_ifs <;> omega
    · apply not_dvd_prod; intro k
      by_cases hk : k = i0
      · subst hk
        simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
        have e1 : n k - p ^ j = p ^ s * K' + (p ^ s - p ^ j) := by omega
        have e2 : n k - p ^ s = p ^ s * K' := by omega
        rw [e1, e2, Nat.choose_symm_add]
        exact not_dvd_choose_pow_mul_add p s K' _ (by omega)
      · simp only [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (Ne.symm hk), Nat.sub_zero,
          Nat.choose_self]
        exact hp.out.not_dvd_one
  · have hq := hK' j hjs hj
    have hle : p ^ s ≤ n i0 - p ^ j := by
      by_contra hlt; push_neg at hlt
      exact hq (by rw [Nat.div_eq_of_lt hlt]; exact dvd_zero p)
    refine eq_zero_of_le n c hu hrel _ _ (Finsupp.single_ne_zero.2 hps.ne') ?_ tsub_le_self hyn ?_ h0
    · rw [Finsupp.single_le_iff, Finsupp.tsub_apply, Finsupp.single_eq_same]; exact hle
    · rw [prod_choose_single, not_dvd_choose_pow_iff, Finsupp.tsub_apply, Finsupp.single_eq_same]
      exact hq

/- English proof (translation)
Establish `hpow : ∀ v : ℕ, ∀ m : M, ∃ g : M, p ^ v • g = m`. Introduce `v`. Proceed by induction on `v with`. Consider the case `zero => intro m; exact ⟨m, by rw [pow_zero, one_smul]⟩`. Consider the case `succ v ih`.

Introduce `m`. Take `⟨g, hg⟩` from `ih m`. Take `⟨g', hg'⟩` from `hdiv g`. Conclude with `⟨g', by rw [pow_succ, mul_smul, hg', hg]⟩`. Introduce `k hk m`.

Take `⟨v, u, hu', rfl⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hk.ne' p hp.out.one_lt.ne'`. Take `⟨g1, hg1⟩` from `hpow v m`. Establish `hc : Nat.Coprime u p` using `Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hu')`. Take `⟨g, hg⟩` from `(hu u hc).2 g1`. Conclude with `⟨g, by rw [mul_smul]; simp only at hg; rw [hg, hg1]⟩`.
-/
theorem exists_smul_eq (hdiv : ∀ m : M, ∃ m', p • m' = m)
    (hu : ∀ k : ℕ, Nat.Coprime k p → Function.Bijective fun m : M => k • m) :
    ∀ k : ℕ, 0 < k → ∀ m : M, ∃ g : M, k • g = m := by
  have hpow : ∀ v : ℕ, ∀ m : M, ∃ g : M, p ^ v • g = m := by
    intro v
    induction v with
    | zero => intro m; exact ⟨m, by rw [pow_zero, one_smul]⟩
    | succ v ih =>
      intro m
      obtain ⟨g, hg⟩ := ih m
      obtain ⟨g', hg'⟩ := hdiv g
      exact ⟨g', by rw [pow_succ, mul_smul, hg', hg]⟩
  intro k hk m
  obtain ⟨v, u, hu', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk.ne' p hp.out.one_lt.ne'
  obtain ⟨g1, hg1⟩ := hpow v m
  have hc : Nat.Coprime u p := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hu')
  obtain ⟨g, hg⟩ := (hu u hc).2 g1
  exact ⟨g, by rw [mul_smul]; simp only at hg; rw [hg, hg1]⟩

/- English proof (translation)
Introduce `a ha`. Simplify using `only`. Rewrite using `[← hsym a ha]`. Use `congr 2`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Finsupp.tsub_apply, Nat.choose_symm (Finsupp.le_def.1 ha i)]`.
-/
theorem sub_isSym (n : Fin d →₀ ℕ) (c : (Fin d →₀ ℕ) → M) (g : M) (hsym : IsSym n c) :
    IsSym n (fun a => c a - (∏ i, (n i).choose (a i)) • g) := by
  intro a ha
  simp only
  rw [← hsym a ha]
  congr 2
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finsupp.tsub_apply, Nat.choose_symm (Finsupp.le_def.1 ha i)]

/- English proof (translation)
Introduce `a b ha hb hab hab'`. Simplify using `only [smul_sub]`. Rewrite using `[hrel a b ha hb hab hab', smul_smul, smul_smul, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]`. Use `congr 2`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Establish `hi` using `Finsupp.le_def.1 hab i`. Simplify using `only [Finsupp.add_apply, Finsupp.tsub_apply] at hi ⊢`. Establish `h` using `Nat.choose_mul (n := n i) (k := a i + b i) (s := a i) (by omega)`. Rewrite `h` using `[Nat.add_sub_cancel_left]`. Rewrite using `[mul_comm, h, mul_comm]`.
-/
theorem sub_isRel (n : Fin d →₀ ℕ) (c : (Fin d →₀ ℕ) → M) (g : M) (hrel : IsRel n c) :
    IsRel n (fun a => c a - (∏ i, (n i).choose (a i)) • g) := by
  intro a b ha hb hab hab'
  simp only [smul_sub]
  rw [hrel a b ha hb hab hab', smul_smul, smul_smul, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  congr 2
  refine Finset.prod_congr rfl fun i _ => ?_
  have hi := Finsupp.le_def.1 hab i
  simp only [Finsupp.add_apply, Finsupp.tsub_apply] at hi ⊢
  have h := Nat.choose_mul (n := n i) (k := a i + b i) (s := a i) (by omega)
  rw [Nat.add_sub_cancel_left] at h
  rw [mul_comm, h, mul_comm]

/- English proof (translation)
Introduce `p _ M _ hdiv hu d n c hsym hrel`. Establish `hp : p.Prime` using `Fact.out`. Establish `hps : ∀ j, 0 < p ^ j` using `fun j => pow_pos hp.pos j`. Establish `mk : ∀ i0 j0, p ^ j0 ≤ n i0 → ∃ g : M, (fun a => c a - (∏ i, (n i).choose (a i)) • g) (Finsupp.single i0 (p ^ j0)) = 0`. Introduce `i0 j0 hj0`.

Take `⟨g, hg⟩` from `exists_smul_eq hdiv hu ((n i0).choose (p ^ j0)) (Nat.choose_pos hj0) (c (Finsupp.single i0 (p ^ j0)))`. Conclude with `⟨g, by simp only; rw [prod_choose_single, hg, sub_self]⟩`. Establish `fin : ∀ g : M, (∀ a, a ≤ n → a ≠ 0 → a ≠ n → c a - (∏ i, (n i).choose (a i)) • g = 0) → ∃ g : M, ∀ a, a ≤ n → a ≠ 0 → a ≠ n → c a = (∏ i, Nat.choose (n i) (a i)) • g` using `fun g h => ⟨g, fun a h1 h2 h3 => sub_eq_zero.1 (h a h1 h2 h3)⟩`. Establish `hsym'` using `fun g => sub_isSym n c g hsym`. Establish `hrel'` using `fun g => sub_isRel n c g hrel`.

Distinguish the cases in `hA : ∃ i0 i1, i0 ≠ i1 ∧ n i0 ≠ 0 ∧ n i1 ≠ 0`. Take `⟨i0, i1, hne, h0, h1⟩` from `hA`. Take `⟨s, m, hm, he⟩` from `Nat.exists_eq_pow_mul_and_not_dvd h0 p hp.one_lt.ne'`. Take `⟨s1, m1, hm1, he1⟩` from `Nat.exists_eq_pow_mul_and_not_dvd h1 p hp.one_lt.ne'`. Establish `hs : p ^ s ≤ n i0`.

Rewrite using `[he]; exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (by rintro rfl; simp at he; exact h0 he))`. Establish `hs1 : p ^ s1 ≤ n i1`. Rewrite using `[he1]; exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (by rintro rfl; simp at he1; exact h1 he1))`. Take `⟨g, hg⟩` from `mk i0 s hs`. Use `fin g (eq_zero_of_atoms n _ hu (hrel' g) ?_)` and prove the remaining obligations.

Establish `hc1` using `atom_cross n _ hu (hrel' g) (hsym' g) i0 s (by rw [he, Nat.mul_div_cancel_left _ (hps s)]; exact hm) hs hg`. Introduce `i j hj _`. Distinguish the cases in `hi : i = i0`. Substitute `hi` using the available equality. Conclude with `atom_cross n _ hu (hrel' g) (hsym' g) i1 s1 (by rw [he1, Nat.mul_div_cancel_left _ (hps s1)]; exact hm1) hs1 (hc1 i1 s1 (Ne.symm hne) hs1) i j hne hj`.

Conclude with `hc1 i j hi hj`. Use `push_neg at hA`. Distinguish the cases in `h2 : ∃ i0, 2 ≤ n i0`. Take `⟨i0, hN2⟩` from `h2`. Establish `hz : ∀ k, k ≠ i0 → n k = 0` using `fun k hk => hA i0 k (Ne.symm hk) (by omega)`.

Take `⟨r, m, hm, he⟩` from `Nat.exists_eq_pow_mul_and_not_dvd (by omega : n i0 ≠ 0) p hp.one_lt.ne'`. Choose the witnesses or unpack the hypotheses as in `⟨s, K, hN, hK, hK'⟩ : ∃ s K, n i0 = p ^ s * K ∧ 2 ≤ K ∧ (∀ j, s < j → p ^ j < n i0 → ¬ p ∣ (n i0 - p ^ j) / p ^ s) := by`. Distinguish the cases in `hm1 : m = 1`. Substitute `hm1` using the available equality. Rewrite `he` using `[mul_one]`.

Establish `hr : 0 < r`. Break down `Nat.eq_zero_or_pos r with h | h` into its components or cases. Substitute `h` using the available equality. Simplify using `at he`. Use linear arithmetic over natural numbers and integers.

Conclude with `h`. Use `⟨r - 1, p, ?_, hp.two_le, ?_⟩` and prove the remaining obligations. Rewrite using `[he, ← pow_succ]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.

Introduce `j hj hlt`. It suffices to derive a contradiction. Establish `: p ^ r ≤ p ^ j` using `Nat.pow_le_pow_right hp.pos (by omega)`. Use linear arithmetic over natural numbers and integers. Establish `hm0 : m ≠ 0` using `by rintro rfl; simp at he; omega`.

Use `⟨r, m, he, by omega, ?_⟩` and prove the remaining obligations. Introduce `j hj hlt`. Establish `ej : p ^ j = p ^ r * p ^ (j - r)` using `by rw [← pow_add]; congr 1; omega`. Rewrite `hlt`, the goal using `[he, ej]`. Establish `hlt' : p ^ (j - r) < m` using `Nat.lt_of_mul_lt_mul_left hlt`.

Rewrite using `[← Nat.mul_sub, Nat.mul_div_cancel_left _ (hps r)]`. Introduce `hd`. Apply `hm` to reduce the goal to its premises. Establish `h3` using `Nat.dvd_add hd (dvd_pow_self p (by omega : j - r ≠ 0))`. Rewrite `h3` using `[Nat.sub_add_cancel hlt'.le]`. Then use the resulting hypothesis.

Establish `hsle : p ^ s ≤ n i0` using `by rw [hN]; exact Nat.le_mul_of_pos_right _ (by omega)`. Take `⟨g, hg⟩` from `mk i0 s hsle`. Use `fin g (eq_zero_of_atoms n _ hu (hrel' g) ?_)` and prove the remaining obligations. Introduce `i j hj hne`. Establish `hi : i = i0`.

Assume the negation of the conclusion as `hi; rw [hz i hi] at hj; exact absurd hj (by have := hps j; omega)`. Substitute `hi` using the available equality. Use `atom_line n _ hu (hrel' g) (hsym' g) i s K hN hK hK' hg j ?_` and prove the remaining obligations. Break down `Nat.lt_or_ge (p ^ j) (n i) with h | h` into its components or cases. Conclude with `h`.

It suffices to derive a contradiction. Apply `hne` to reduce the goal to its premises. Use extensionality with `k`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality.

Simplify using `only [Finsupp.single_eq_same]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Finsupp.single_apply, if_neg (Ne.symm hk), hz k hk]`. Use `push_neg at h2`. Use `fin 0 ?_` and prove the remaining obligations.

Introduce `a han ha0 han'`. It suffices to derive a contradiction. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, a i ≠ 0 := by`. Assume the negation of the conclusion as `h; push_neg at h; exact ha0 (Finsupp.ext fun i => by simp [h i])`. Apply `han'` to reduce the goal to its premises.

Use extensionality with `k`. Establish `hak` using `Finsupp.le_def.1 han k`. Establish `hai` using `Finsupp.le_def.1 han i`. Establish `h2i` using `h2 i`. Distinguish the cases in `hk : k = i`.

Substitute `hk` using the available equality. Use linear arithmetic over natural numbers and integers. Use `hA i k (Ne.symm hk) (by omega)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_eq_smul_prod_choose : ∀ (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M],
    (∀ m : M, ∃ m', p • m' = m) → (∀ n : ℕ, Nat.Coprime n p → Function.Bijective fun m : M => n • m) →
    ∀ (d : ℕ) (n : Fin d →₀ ℕ) (c : (Fin d →₀ ℕ) → M), (∀ a, a ≤ n → c a = c (n - a)) →
    (∀ a b, a ≠ 0 → b ≠ 0 → a + b ≤ n → a + b ≠ n →
      (∏ i, Nat.choose ((a + b : Fin d →₀ ℕ) i) (a i)) • c (a + b) =
        (∏ i, Nat.choose ((n - a : Fin d →₀ ℕ) i) (b i)) • c a) →
    ∃ g : M, ∀ a, a ≤ n → a ≠ 0 → a ≠ n → c a = (∏ i, Nat.choose (n i) (a i)) • g := by
  intro p _ M _ hdiv hu d n c hsym hrel
  have hp : p.Prime := Fact.out
  have hps : ∀ j, 0 < p ^ j := fun j => pow_pos hp.pos j

  have mk : ∀ i0 j0, p ^ j0 ≤ n i0 → ∃ g : M,
      (fun a => c a - (∏ i, (n i).choose (a i)) • g) (Finsupp.single i0 (p ^ j0)) = 0 := by
    intro i0 j0 hj0
    obtain ⟨g, hg⟩ := exists_smul_eq hdiv hu ((n i0).choose (p ^ j0)) (Nat.choose_pos hj0)
      (c (Finsupp.single i0 (p ^ j0)))
    exact ⟨g, by simp only; rw [prod_choose_single, hg, sub_self]⟩
  have fin : ∀ g : M, (∀ a, a ≤ n → a ≠ 0 → a ≠ n → c a - (∏ i, (n i).choose (a i)) • g = 0) →
      ∃ g : M, ∀ a, a ≤ n → a ≠ 0 → a ≠ n → c a = (∏ i, Nat.choose (n i) (a i)) • g :=
    fun g h => ⟨g, fun a h1 h2 h3 => sub_eq_zero.1 (h a h1 h2 h3)⟩
  have hsym' := fun g => sub_isSym n c g hsym
  have hrel' := fun g => sub_isRel n c g hrel
  by_cases hA : ∃ i0 i1, i0 ≠ i1 ∧ n i0 ≠ 0 ∧ n i1 ≠ 0
  · obtain ⟨i0, i1, hne, h0, h1⟩ := hA
    obtain ⟨s, m, hm, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd h0 p hp.one_lt.ne'
    obtain ⟨s1, m1, hm1, he1⟩ := Nat.exists_eq_pow_mul_and_not_dvd h1 p hp.one_lt.ne'
    have hs : p ^ s ≤ n i0 := by
      rw [he]; exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (by rintro rfl; simp at he; exact h0 he))
    have hs1 : p ^ s1 ≤ n i1 := by
      rw [he1]; exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (by rintro rfl; simp at he1; exact h1 he1))
    obtain ⟨g, hg⟩ := mk i0 s hs
    refine fin g (eq_zero_of_atoms n _ hu (hrel' g) ?_)
    have hc1 := atom_cross n _ hu (hrel' g) (hsym' g) i0 s
      (by rw [he, Nat.mul_div_cancel_left _ (hps s)]; exact hm) hs hg
    intro i j hj _
    by_cases hi : i = i0
    · subst hi
      exact atom_cross n _ hu (hrel' g) (hsym' g) i1 s1
        (by rw [he1, Nat.mul_div_cancel_left _ (hps s1)]; exact hm1) hs1 (hc1 i1 s1 (Ne.symm hne) hs1) i j hne hj
    · exact hc1 i j hi hj
  · push_neg at hA
    by_cases h2 : ∃ i0, 2 ≤ n i0
    · obtain ⟨i0, hN2⟩ := h2
      have hz : ∀ k, k ≠ i0 → n k = 0 := fun k hk => hA i0 k (Ne.symm hk) (by omega)
      obtain ⟨r, m, hm, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : n i0 ≠ 0) p hp.one_lt.ne'
      obtain ⟨s, K, hN, hK, hK'⟩ : ∃ s K, n i0 = p ^ s * K ∧ 2 ≤ K ∧
          (∀ j, s < j → p ^ j < n i0 → ¬ p ∣ (n i0 - p ^ j) / p ^ s) := by
        by_cases hm1 : m = 1
        · subst hm1
          rw [mul_one] at he
          have hr : 0 < r := by
            rcases Nat.eq_zero_or_pos r with h | h
            · subst h; simp at he; omega
            · exact h
          refine ⟨r - 1, p, ?_, hp.two_le, ?_⟩
          · rw [he, ← pow_succ]; congr 1; omega
          · intro j hj hlt
            exfalso
            have : p ^ r ≤ p ^ j := Nat.pow_le_pow_right hp.pos (by omega)
            omega
        · have hm0 : m ≠ 0 := by rintro rfl; simp at he; omega
          refine ⟨r, m, he, by omega, ?_⟩
          intro j hj hlt
          have ej : p ^ j = p ^ r * p ^ (j - r) := by rw [← pow_add]; congr 1; omega
          rw [he, ej] at hlt ⊢
          have hlt' : p ^ (j - r) < m := Nat.lt_of_mul_lt_mul_left hlt
          rw [← Nat.mul_sub, Nat.mul_div_cancel_left _ (hps r)]
          intro hd
          apply hm
          have h3 := Nat.dvd_add hd (dvd_pow_self p (by omega : j - r ≠ 0))
          rwa [Nat.sub_add_cancel hlt'.le] at h3
      have hsle : p ^ s ≤ n i0 := by rw [hN]; exact Nat.le_mul_of_pos_right _ (by omega)
      obtain ⟨g, hg⟩ := mk i0 s hsle
      refine fin g (eq_zero_of_atoms n _ hu (hrel' g) ?_)
      intro i j hj hne
      have hi : i = i0 := by
        by_contra hi; rw [hz i hi] at hj; exact absurd hj (by have := hps j; omega)
      subst hi
      refine atom_line n _ hu (hrel' g) (hsym' g) i s K hN hK hK' hg j ?_
      rcases Nat.lt_or_ge (p ^ j) (n i) with h | h
      · exact h
      · exfalso; apply hne
        ext k
        by_cases hk : k = i
        · subst hk; simp only [Finsupp.single_eq_same]; omega
        · rw [Finsupp.single_apply, if_neg (Ne.symm hk), hz k hk]
    · push_neg at h2
      refine fin 0 ?_
      intro a han ha0 han'
      exfalso
      obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
        by_contra h; push_neg at h; exact ha0 (Finsupp.ext fun i => by simp [h i])
      apply han'
      ext k
      have hak := Finsupp.le_def.1 han k
      have hai := Finsupp.le_def.1 han i
      have h2i := h2 i
      by_cases hk : k = i
      · subst hk; omega
      · have := hA i k (Ne.symm hk) (by omega)
        omega

end GlobalTheory.SymCocycleMV
