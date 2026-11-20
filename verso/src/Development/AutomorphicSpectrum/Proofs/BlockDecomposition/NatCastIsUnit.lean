import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.RootsDivide

/- English proof (translation)
Take `⟨r, hr⟩` from `exists_add_pow_prime_eq hp (y - 1) (1 : B)`. Establish `e1 : (y - 1) ^ p = (y ^ p - 1) - (p : B) * ((y - 1) * r)`. Establish `: (y - 1 + 1) = y` using `by ring`. Rewrite `hr` using `[this]`. Rewrite using `[hr]`.

Simplify using `only [one_pow]`. Expand and normalize the polynomial expressions, which then agree. Use `IsNilpotent.of_pow (m := p) ?_` and prove the remaining obligations. Rewrite using `[e1]`. Conclude with `(Commute.all _ _).isNilpotent_sub h ((Commute.all _ _).isNilpotent_mul_right hpn)`.
-/
theorem nilp_step {B : Type} [CommRing B] (p : ℕ) (hp : p.Prime) (hpn : IsNilpotent (p : B))
    (y : B) (h : IsNilpotent (y ^ p - 1)) : IsNilpotent (y - 1) := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (y - 1) (1 : B)
  have e1 : (y - 1) ^ p = (y ^ p - 1) - (p : B) * ((y - 1) * r) := by
    have : (y - 1 + 1) = y := by ring
    rw [this] at hr
    rw [hr]; simp only [one_pow]; ring
  refine IsNilpotent.of_pow (m := p) ?_
  rw [e1]
  exact (Commute.all _ _).isNilpotent_sub h ((Commute.all _ _).isNilpotent_mul_right hpn)

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => exact h0`. Consider the case `succ k ih => exact nilp_step p hp hpn _ (by rw [he]; exact ih)`.
-/
theorem nilp_all {B : Type} [CommRing B] (p : ℕ) (hp : p.Prime) (e : ℕ → B)
    (hpn : IsNilpotent (p : B)) (he : ∀ k, e (k + 1) ^ p = e k)
    (h0 : IsNilpotent (e 0 - 1)) (k : ℕ) : IsNilpotent (e k - 1) := by
  induction k with
  | zero => exact h0
  | succ k ih => exact nilp_step p hp hpn _ (by rw [he]; exact ih)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[pow_succ', pow_mul, ← add_assoc, he, ih]`.
-/
theorem pow_tower {B : Type} [CommRing B] (p : ℕ) (e : ℕ → B)
    (he : ∀ k, e (k + 1) ^ p = e k) (k n : ℕ) : e (k + n) ^ (p ^ n) = e k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_mul, ← add_assoc, he, ih]

/- English proof (translation)
Establish `hcop : IsCoprime (c : ℤ) (p : ℤ)`. Rewrite using `[Nat.isCoprime_iff_coprime]`. Conclude with `((Nat.Prime.coprime_iff_not_dvd hp).2 hc).symm`. Take `⟨a, b, hab⟩` from `hcop`. Establish `h1 : (a : B) * (c : B) + (b : B) * (p : B) = 1`.

Use `congrArg (Int.cast : ℤ → B) hab` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`. Establish `h2 : IsUnit ((a : B) * (c : B))`. Establish `: (a : B) * (c : B) = 1 - (b : B) * (p : B)` using `by rw [← h1]; ring`.

Rewrite using `[this]`. Conclude with `((Commute.all _ _).isNilpotent_mul_left hpn).isUnit_one_sub`. Conclude with `isUnit_of_mul_isUnit_right h2`.
-/
theorem natCast_isUnit {B : Type} [CommRing B] (p : ℕ) (hp : p.Prime)
    (hpn : IsNilpotent (p : B)) (c : ℕ) (hc : ¬ p ∣ c) : IsUnit (c : B) := by
  have hcop : IsCoprime (c : ℤ) (p : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact ((Nat.Prime.coprime_iff_not_dvd hp).2 hc).symm
  obtain ⟨a, b, hab⟩ := hcop
  have h1 : (a : B) * (c : B) + (b : B) * (p : B) = 1 := by
    have := congrArg (Int.cast : ℤ → B) hab
    push_cast at this
    exact this
  have h2 : IsUnit ((a : B) * (c : B)) := by
    have : (a : B) * (c : B) = 1 - (b : B) * (p : B) := by rw [← h1]; ring
    rw [this]
    exact ((Commute.all _ _).isNilpotent_mul_left hpn).isUnit_one_sub
  exact isUnit_of_mul_isUnit_right h2

/- English proof (translation)
Establish `hd : (x - 1) ∣ (∑ i ∈ Finset.range n, x ^ i) - (n : B)`. Establish `: (∑ i ∈ Finset.range n, x ^ i) - (n : B) = ∑ i ∈ Finset.range n, (x ^ i - 1)`. Simplify using `[Finset.sum_sub_distrib]`. Rewrite using `[this]`. Use `Finset.dvd_sum fun i _ => ?_` and prove the remaining obligations.

Simplify using `using sub_dvd_pow_sub_pow x 1 i`. Take `⟨t, ht⟩` from `hd`. Establish `hnil : IsNilpotent ((∑ i ∈ Finset.range n, x ^ i) - (n : B))`. Rewrite using `[ht]`. Conclude with `(Commute.all _ _).isNilpotent_mul_right hx`.

Establish `: (∑ i ∈ Finset.range n, x ^ i) = (n : B) + ((∑ i ∈ Finset.range n, x ^ i) - (n : B))`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `hnil.isUnit_add_left_of_commute hn (Commute.all _ _)`.
-/
theorem geom_isUnit {B : Type} [CommRing B] (x : B) (hx : IsNilpotent (x - 1)) (n : ℕ)
    (hn : IsUnit (n : B)) : IsUnit (∑ i ∈ Finset.range n, x ^ i) := by
  have hd : (x - 1) ∣ (∑ i ∈ Finset.range n, x ^ i) - (n : B) := by
    have : (∑ i ∈ Finset.range n, x ^ i) - (n : B) = ∑ i ∈ Finset.range n, (x ^ i - 1) := by
      simp [Finset.sum_sub_distrib]
    rw [this]
    refine Finset.dvd_sum fun i _ => ?_
    simpa using sub_dvd_pow_sub_pow x 1 i
  obtain ⟨t, ht⟩ := hd
  have hnil : IsNilpotent ((∑ i ∈ Finset.range n, x ^ i) - (n : B)) := by
    rw [ht]; exact (Commute.all _ _).isNilpotent_mul_right hx
  have : (∑ i ∈ Finset.range n, x ^ i) = (n : B) + ((∑ i ∈ Finset.range n, x ^ i) - (n : B)) := by
    ring
  rw [this]
  exact hnil.isUnit_add_left_of_commute hn (Commute.all _ _)

/- English proof (translation)
Introduce `p hp B _ e hpn he h0 m c hc`. Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`. Conclude with `hc (dvd_zero _)`. Take `⟨j, c', hpc, rfl⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hc0 p hp.ne_one`.

Establish `hjm : j < m`. Assume the negation of the conclusion as `hle`. Conclude with `hc (Dvd.dvd.mul_right (pow_dvd_pow p (not_lt.1 hle)) c')`. Take `⟨l, rfl⟩ : ∃ l, m = (l + 1) + j` from `⟨m - j - 1, by omega⟩`. Use `set x := e (l + 1) with hxdef`.

Establish `hem : e (l + 1 + j) ^ (p ^ j * c') = x ^ c'`. Rewrite using `[pow_mul, pow_tower p e he]`. Rewrite using `[hem]`. Establish `hxn : IsNilpotent (x - 1)` using `nilp_all p hp e hpn he h0 _`. Establish `hu : IsUnit (∑ i ∈ Finset.range c', x ^ i)` using `geom_isUnit x hxn c' (natCast_isUnit p hp hpn c' hpc)`.

Establish `hfac : x ^ c' - 1 = (x - 1) * ∑ i ∈ Finset.range c', x ^ i`. Rewrite using `[mul_comm, geom_sum_mul]`. Rewrite using `[hfac, hu.mul_right_dvd]`. Establish `h1 : x ^ (p ^ l) = e 1`. Use `pow_tower p e he 1 l` as an intermediate fact.

Rewrite `this` using `[add_comm 1 l]`. Then use the resulting hypothesis. Rewrite using `[← h1]`. Simplify using `using sub_dvd_pow_sub_pow x 1 (p ^ l)`.
-/
theorem sub_one_dvd : ∀ (p : ℕ), p.Prime → ∀ {B : Type} [CommRing B] (e : ℕ → B),
    IsNilpotent (p : B) → (∀ k, e (k + 1) ^ p = e k) → IsNilpotent (e 0 - 1) →
    ∀ m c : ℕ, ¬ p ^ m ∣ c → (e m ^ c - 1) ∣ (e 1 - 1) := by
  intro p hp B _ e hpn he h0 m c hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hc (dvd_zero _)
  obtain ⟨j, c', hpc, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hc0 p hp.ne_one
  have hjm : j < m := by
    by_contra hle
    exact hc (Dvd.dvd.mul_right (pow_dvd_pow p (not_lt.1 hle)) c')
  obtain ⟨l, rfl⟩ : ∃ l, m = (l + 1) + j := ⟨m - j - 1, by omega⟩
  set x := e (l + 1) with hxdef
  have hem : e (l + 1 + j) ^ (p ^ j * c') = x ^ c' := by
    rw [pow_mul, pow_tower p e he]
  rw [hem]
  have hxn : IsNilpotent (x - 1) := nilp_all p hp e hpn he h0 _
  have hu : IsUnit (∑ i ∈ Finset.range c', x ^ i) :=
    geom_isUnit x hxn c' (natCast_isUnit p hp hpn c' hpc)
  have hfac : x ^ c' - 1 = (x - 1) * ∑ i ∈ Finset.range c', x ^ i := by
    rw [mul_comm, geom_sum_mul]
  rw [hfac, hu.mul_right_dvd]
  have h1 : x ^ (p ^ l) = e 1 := by
    have := pow_tower p e he 1 l
    rwa [add_comm 1 l] at this
  rw [← h1]
  simpa using sub_dvd_pow_sub_pow x 1 (p ^ l)

end GlobalTheory.CompanionTheory.RootsDivide
