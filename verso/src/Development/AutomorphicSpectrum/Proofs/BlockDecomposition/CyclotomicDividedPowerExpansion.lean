import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.QPd

/- English proof (translation)
Use `haveI : Fact p.Prime := ⟨hp⟩`. Establish `hmod : ((X - 1 : (ZMod p)[X]) ^ (p - 1) - ∑ i ∈ Finset.range p, (X : (ZMod p)[X]) ^ i) = 0`. Establish `h1 : (X - 1 : (ZMod p)[X]) ^ p = X ^ p - 1`. Simplify using `using sub_pow_char (X : (ZMod p)[X]) 1`. Establish `h2 : (X - 1 : (ZMod p)[X]) * ∑ i ∈ Finset.range p, (X : (ZMod p)[X]) ^ i = X ^ p - 1` using `mul_geom_sum _ _`.

Establish `h3 : (X - 1 : (ZMod p)[X]) ≠ 0`. Simplify using `using Polynomial.X_sub_C_ne_zero (1 : ZMod p)`. Establish `h4 : (X - 1 : (ZMod p)[X]) * ((X - 1) ^ (p - 1) - ∑ i ∈ Finset.range p, (X : (ZMod p)[X]) ^ i) = 0`. Rewrite using `[mul_sub, h2, ← pow_succ', Nat.sub_add_cancel hp.one_lt.le, h1, sub_self]`. Conclude with `(mul_eq_zero.1 h4).resolve_left h3`.

Establish `hdvd : C (p : ℤ) ∣ ((X - 1 : ℤ[X]) ^ (p - 1) - ∑ i ∈ Finset.range p, (X : ℤ[X]) ^ i)`. Establish `hmap : ((X - 1 : ℤ[X]) ^ (p - 1) - ∑ i ∈ Finset.range p, (X : ℤ[X]) ^ i).map (Int.castRingHom (ZMod p)) = 0`. Simplify `hmod` using `[Polynomial.map_sum]`. Rewrite using `[Polynomial.C_dvd_iff_dvd_coeff]`. Introduce `i`.

Establish `h5` using `congrArg (fun f ↦ coeff f i) hmap`. Simplify using `only [coeff_map, coeff_zero] at h5`. Conclude with `(ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 (by simpa using h5)`. Take `⟨g, hg⟩` from `hdvd`. Use `⟨-aeval x g, ?_⟩` and prove the remaining obligations.

Use `congrArg (aeval x) hg` as an intermediate fact. Simplify using `only [map_sub, map_pow, aeval_X, map_one, map_sum, map_mul, aeval_C] at this`. Simplify using `only [algebraMap_int_eq, eq_intCast, Int.cast_natCast] at this`. Take the linear combination `this`.
-/
theorem exists_sub_one_pow {p : ℕ} (hp : p.Prime) {B : Type} [CommRing B] (x : B) :
    ∃ z : B, (x - 1) ^ (p - 1) = (∑ i ∈ Finset.range p, x ^ i) - (p : B) * z := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hmod : ((X - 1 : (ZMod p)[X]) ^ (p - 1) - ∑ i ∈ Finset.range p, (X : (ZMod p)[X]) ^ i) = 0 := by
    have h1 : (X - 1 : (ZMod p)[X]) ^ p = X ^ p - 1 := by
      simpa using sub_pow_char (X : (ZMod p)[X]) 1
    have h2 : (X - 1 : (ZMod p)[X]) * ∑ i ∈ Finset.range p, (X : (ZMod p)[X]) ^ i = X ^ p - 1 :=
      mul_geom_sum _ _
    have h3 : (X - 1 : (ZMod p)[X]) ≠ 0 := by
      simpa using Polynomial.X_sub_C_ne_zero (1 : ZMod p)
    have h4 : (X - 1 : (ZMod p)[X]) * ((X - 1) ^ (p - 1) - ∑ i ∈ Finset.range p, (X : (ZMod p)[X]) ^ i) = 0 := by
      rw [mul_sub, h2, ← pow_succ', Nat.sub_add_cancel hp.one_lt.le, h1, sub_self]
    exact (mul_eq_zero.1 h4).resolve_left h3
  have hdvd : C (p : ℤ) ∣ ((X - 1 : ℤ[X]) ^ (p - 1) - ∑ i ∈ Finset.range p, (X : ℤ[X]) ^ i) := by
    have hmap : ((X - 1 : ℤ[X]) ^ (p - 1) - ∑ i ∈ Finset.range p, (X : ℤ[X]) ^ i).map
        (Int.castRingHom (ZMod p)) = 0 := by
      simpa [Polynomial.map_sum] using hmod
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    have h5 := congrArg (fun f ↦ coeff f i) hmap
    simp only [coeff_map, coeff_zero] at h5
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 (by simpa using h5)
  obtain ⟨g, hg⟩ := hdvd
  refine ⟨-aeval x g, ?_⟩
  have := congrArg (aeval x) hg
  simp only [map_sub, map_pow, aeval_X, map_one, map_sum, map_mul, aeval_C] at this
  simp only [algebraMap_int_eq, eq_intCast, Int.cast_natCast] at this
  linear_combination this

/- English proof (translation)
Use `haveI : Fact p.Prime := ⟨hp⟩`. Establish `h` using `Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := a * p + c) (k := c)`. Establish `h1 : (a * p + c) % p = c`. Apply the tactic sequence `rw [Nat.mul_add_mod_of_lt hc] <;> simp`. Establish `h2 : c % p = c` using `Nat.mod_eq_of_lt hc`.

Establish `h3 : c / p = 0` using `Nat.div_eq_of_lt hc`. Rewrite `h` using `[h1, h2, h3]`. Simplify using `only [Nat.choose_self, Nat.choose_zero_right, mul_one] at h`. Introduce `hd`. Establish `h0` using `(Nat.modEq_zero_iff_dvd.2 hd).symm.trans h`.

Use `(Nat.modEq_iff_dvd.1 h0)` as an intermediate fact. Simplify using `at this`. Establish `h5 : p ∣ 1` using `by exact_mod_cast this`. Conclude with `hp.one_lt.ne' (Nat.dvd_one.1 h5)`.
-/
theorem not_dvd_choose {p : ℕ} (hp : p.Prime) (a c : ℕ) (hc : c < p) :
    ¬ p ∣ (a * p + c).choose c := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := a * p + c) (k := c)
  have h1 : (a * p + c) % p = c := by
    rw [Nat.mul_add_mod_of_lt hc] <;> simp
  have h2 : c % p = c := Nat.mod_eq_of_lt hc
  have h3 : c / p = 0 := Nat.div_eq_of_lt hc
  rw [h1, h2, h3] at h
  simp only [Nat.choose_self, Nat.choose_zero_right, mul_one] at h
  intro hd
  have h0 := (Nat.modEq_zero_iff_dvd.2 hd).symm.trans h
  have := (Nat.modEq_iff_dvd.1 h0)
  simp at this
  have h5 : p ∣ 1 := by exact_mod_cast this
  exact hp.one_lt.ne' (Nat.dvd_one.1 h5)

/- English proof (translation)
Proceed by induction on `a with`. Consider the case `zero => simpa [Nat.uniformBell_zero_left] using hp.one_lt.ne'`. Consider the case `succ a ih`. Rewrite using `[Nat.uniformBell_succ_left]`. Introduce `h`.

Break down `(hp.dvd_mul).1 h with h | h` into its components or cases. Use `not_dvd_choose hp a (p - 1) (Nat.sub_lt hp.pos one_pos) ?_` and prove the remaining obligations. Establish `h6 : a * p + (p - 1) = a * p + p - 1` using `by have := hp.pos; omega`. Rewrite using `[h6]` and apply the resulting hypothesis. Conclude with `ih h`.
-/
theorem not_dvd_uniformBell {p : ℕ} (hp : p.Prime) (a : ℕ) : ¬ p ∣ Nat.uniformBell a p := by
  induction a with
  | zero => simpa [Nat.uniformBell_zero_left] using hp.one_lt.ne'
  | succ a ih =>
    rw [Nat.uniformBell_succ_left]
    intro h
    rcases (hp.dvd_mul).1 h with h | h
    · refine not_dvd_choose hp a (p - 1) (Nat.sub_lt hp.pos one_pos) ?_
      have h6 : a * p + (p - 1) = a * p + p - 1 := by have := hp.pos; omega
      rwa [h6]
    · exact ih h

/- English proof (translation)
Take `⟨e, he⟩` from `hnil`. Establish `hc : IsCoprime (N : ℤ) ((p : ℤ) ^ e)`. Apply `IsCoprime.pow_right` to reduce the goal to its premises. Rewrite using `[Nat.isCoprime_iff_coprime]`. Conclude with `((Nat.Prime.coprime_iff_not_dvd hp).2 h).symm`.

Take `⟨s, t, hst⟩` from `hc`. Use `⟨s, ?_⟩` and prove the remaining obligations. Use `congrArg (Int.cast : ℤ → B) hst` as an intermediate fact. Move the coercions through the operations in `at this`. Rewrite `this` using `[he]`.

Simplify using `using this`.
-/
theorem exists_inv {B : Type} [CommRing B] {p N : ℕ} (hp : p.Prime) (hnil : IsNilpotent (p : B))
    (h : ¬ p ∣ N) : ∃ v : B, v * N = 1 := by
  obtain ⟨e, he⟩ := hnil
  have hc : IsCoprime (N : ℤ) ((p : ℤ) ^ e) := by
    apply IsCoprime.pow_right
    rw [Nat.isCoprime_iff_coprime]
    exact ((Nat.Prime.coprime_iff_not_dvd hp).2 h).symm
  obtain ⟨s, t, hst⟩ := hc
  refine ⟨s, ?_⟩
  have := congrArg (Int.cast : ℤ → B) hst
  push_cast at this
  rw [he] at this
  simpa using this

/- English proof (translation)
Proceed by induction on `e with`. Consider the case `zero => simp`. Consider the case `succ e ih`. Rewrite using `[pow_succ, Nat.mul_succ]`. Conclude with `(mul_dvd_mul ih (Nat.dvd_factorial hp.pos le_rfl)).trans (Nat.factorial_mul_factorial_dvd_factorial_add _ _)`.
-/
theorem pow_dvd_factorial {p : ℕ} (hp : p.Prime) (e : ℕ) : p ^ e ∣ (p * e).factorial := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ, Nat.mul_succ]
    exact (mul_dvd_mul ih (Nat.dvd_factorial hp.pos le_rfl)).trans
      (Nat.factorial_mul_factorial_dvd_factorial_add _ _)

/- English proof (translation)
Take `⟨e, he⟩` from `hnil`. Use `⟨p * e, fun y hy ↦ ?_⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `pow_dvd_factorial hp e`. Rewrite using `[← δ.factorial_mul_dpow_eq_pow hy, hk]`. Use `push_cast`.

Rewrite using `[he]`. Simplify using the standard rewrite rules.
-/
theorem exists_pow_eq_zero {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {p : ℕ}
    (hp : p.Prime) (hnil : IsNilpotent (p : B)) : ∃ n : ℕ, ∀ y ∈ J, y ^ n = 0 := by
  obtain ⟨e, he⟩ := hnil
  refine ⟨p * e, fun y hy ↦ ?_⟩
  obtain ⟨k, hk⟩ := pow_dvd_factorial hp e
  rw [← δ.factorial_mul_dpow_eq_pow hy, hk]
  push_cast
  rw [he]
  simp

/- English proof (translation)
Rewrite using `[Nat.choose_symm_add]`. Introduce `h`. Break down `(hp.dvd_mul).1 h with h | h` into its components or cases. Break down `(hp.dvd_mul).1 h with h | h` into its components or cases. Conclude with `not_dvd_uniformBell hp a h`.

Conclude with `not_dvd_choose hp a c hc h`. Conclude with `absurd ((hp.dvd_factorial).1 h) (not_le.2 hc)`.
-/
theorem not_dvd_coeff {p : ℕ} (hp : p.Prime) (a c : ℕ) (hc : c < p) :
    ¬ p ∣ Nat.uniformBell a p * (a * p + c).choose (a * p) * c.factorial := by
  rw [Nat.choose_symm_add]
  intro h
  rcases (hp.dvd_mul).1 h with h | h
  · rcases (hp.dvd_mul).1 h with h | h
    · exact not_dvd_uniformBell hp a h
    · exact not_dvd_choose hp a c hc h
  · exact absurd ((hp.dvd_factorial).1 h) (not_le.2 hc)

section
variable {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J)

/- English proof (translation)
Establish `h1 : (Nat.uniformBell a p : B) * δ.dpow (a * p) μ = μ ^ a * δ.dpow a w`. Rewrite using `[← δ.dpow_comp hp.ne_zero hμ, h, δ.dpow_mul hw]`. Establish `h2` using `δ.mul_dpow (m := a * p) (n := c) hμ`. Establish `h3` using `δ.factorial_mul_dpow_eq_pow (n := c) hμ`. Use `push_cast`.

Rewrite using `[pow_add]`. Take the linear combination `(-(Nat.uniformBell a p : B) * (c.factorial : B)) * h2 + (c.factorial : B) * δ.dpow c μ * h1 + μ ^ a * δ.dpow a w * h3`.
-/
theorem coeff_mul_dpow {p : ℕ} (hp : p.Prime) {μ w : B} (hμ : μ ∈ J) (hw : w ∈ J)
    (h : δ.dpow p μ = μ * w) (a c : ℕ) :
    ((Nat.uniformBell a p * (a * p + c).choose (a * p) * c.factorial : ℕ) : B) *
        δ.dpow (a * p + c) μ = μ ^ (a + c) * δ.dpow a w := by
  have h1 : (Nat.uniformBell a p : B) * δ.dpow (a * p) μ = μ ^ a * δ.dpow a w := by
    rw [← δ.dpow_comp hp.ne_zero hμ, h, δ.dpow_mul hw]
  have h2 := δ.mul_dpow (m := a * p) (n := c) hμ
  have h3 := δ.factorial_mul_dpow_eq_pow (n := c) hμ
  push_cast
  rw [pow_add]
  linear_combination (-(Nat.uniformBell a p : B) * (c.factorial : B)) * h2 +
    (c.factorial : B) * δ.dpow c μ * h1 + μ ^ a * δ.dpow a w * h3

/- English proof (translation)
Take `⟨q, rfl⟩ : ∃ q, p = q + 1` from `⟨p - 1, (Nat.sub_add_cancel hp.one_lt.le).symm⟩`. Simplify using `only [Nat.add_sub_cancel] at *`. Use `set ξ := ∑ i ∈ Finset.range (q + 1), x ^ i with hξdef`. Take `⟨z, hz⟩` from `exists_sub_one_pow hp x`. Simplify using `only [Nat.add_sub_cancel, ← hξdef] at hz`.

Take `⟨u, hu⟩` from `exists_inv (N := q.factorial) hp hnil (fun h ↦ absurd ((hp.dvd_factorial).1 h) (by omega))`. Establish `hμ : x ^ (q + 1) - 1 = (x - 1) * ξ` using `(mul_geom_sum x (q + 1)).symm`. Establish `h2` using `δ.factorial_mul_dpow_eq_pow (n := q + 1) hξ`. Rewrite `h2` using `[Nat.factorial_succ]`. Move the coercions through the operations in `at h2 hz`.

Use `⟨δ.dpow (q + 1) ξ - z * u * ξ ^ q, ?_, ?_⟩` and prove the remaining obligations. Use `Ideal.sub_mem _ (GlobalTheory.Cris.ExpBij.dpFil_anti δ (Nat.le_succ q) (GlobalTheory.Cris.ExpBij.dpow_mem_dpFil δ hξ _)) (Ideal.mul_mem_left _ _ ?_)` and prove the remaining obligations. Simplify using `using GlobalTheory.Cris.ExpBij.pow_mem_dpFil δ (GlobalTheory.Cris.ExpBij.mem_dpFil_one δ hξ) q`. Rewrite using `[hμ, δ.dpow_mul hξ, pow_succ]`. Take the linear combination `(x - 1) * δ.dpow (q + 1) ξ * hz + (x - 1) * z * ((q : B) + 1) * δ.dpow (q + 1) ξ * hu - (x - 1) * z * u * h2`.
-/
theorem exists_dpow_prime_eq {p : ℕ} (hp : p.Prime) (hnil : IsNilpotent (p : B)) (x : B)
    (hξ : (∑ i ∈ Finset.range p, x ^ i) ∈ J) :
    ∃ w ∈ GlobalTheory.Cris.ExpBij.dpFil δ (p - 1), δ.dpow p (x ^ p - 1) = (x ^ p - 1) * w := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.sub_add_cancel hp.one_lt.le).symm⟩
  simp only [Nat.add_sub_cancel] at *
  set ξ := ∑ i ∈ Finset.range (q + 1), x ^ i with hξdef
  obtain ⟨z, hz⟩ := exists_sub_one_pow hp x
  simp only [Nat.add_sub_cancel, ← hξdef] at hz
  obtain ⟨u, hu⟩ := exists_inv (N := q.factorial) hp hnil
    (fun h ↦ absurd ((hp.dvd_factorial).1 h) (by omega))
  have hμ : x ^ (q + 1) - 1 = (x - 1) * ξ := (mul_geom_sum x (q + 1)).symm
  have h2 := δ.factorial_mul_dpow_eq_pow (n := q + 1) hξ
  rw [Nat.factorial_succ] at h2
  push_cast at h2 hz
  refine ⟨δ.dpow (q + 1) ξ - z * u * ξ ^ q, ?_, ?_⟩
  · refine Ideal.sub_mem _ (GlobalTheory.Cris.ExpBij.dpFil_anti δ (Nat.le_succ q)
      (GlobalTheory.Cris.ExpBij.dpow_mem_dpFil δ hξ _)) (Ideal.mul_mem_left _ _ ?_)
    simpa using GlobalTheory.Cris.ExpBij.pow_mem_dpFil δ (GlobalTheory.Cris.ExpBij.mem_dpFil_one δ hξ) q
  · rw [hμ, δ.dpow_mul hξ, pow_succ]
    linear_combination (x - 1) * δ.dpow (q + 1) ξ * hz +
      (x - 1) * z * ((q : B) + 1) * δ.dpow (q + 1) ξ * hu - (x - 1) * z * u * h2

end

/- English proof (translation)
Introduce `B _ J δ p hp hnil x hξ`. Establish `hμJ : x ^ p - 1 ∈ J`. Rewrite using `[← mul_geom_sum]`. Conclude with `J.mul_mem_left _ hξ`. Take `⟨n, hn⟩` from `exists_pow_eq_zero δ hp hnil`.

Take `⟨w, hwf, hw⟩` from `exists_dpow_prime_eq δ hp hnil x hξ`. Establish `hp2` using `hp.two_le`. Establish `hp1 : 1 ≤ p - 1` using `by omega`. Establish `hwJ : w ∈ J` using `GlobalTheory.Cris.ExpBij.dpFil_le δ hp1 hwf`. Generalize the expression as in `x ^ p - 1 = μ at hμJ hw ⊢`.

Establish `key : ∀ m, ∃ b : B, (m = 1 → b = 1) ∧ (1 ≤ m → δ.dpow m μ = μ * b ∧ b ∈ GlobalTheory.Cris.ExpBij.dpFil δ (m - 1)) ∧ (p * (n + 2) ≤ m → b = 0)`. Introduce `m`. Break down `Nat.lt_or_ge m 2 with h | h` into its components or cases. Use `interval_cases m`. Conclude with `⟨0, by simp, by simp, fun _ ↦ rfl⟩`.

Use `⟨1, fun _ ↦ rfl, fun _ ↦ ⟨by rw [δ.dpow_one hμJ, mul_one], GlobalTheory.Cris.ExpBij.mem_dpFil_zero δ 1⟩, fun h ↦ ?_⟩` and prove the remaining obligations. Use the polynomial consequences of the given equalities and inequalities. Take `⟨a, c, hc, rfl⟩ : ∃ a c, c < p ∧ a * p + c = m` from `⟨m / p, m % p, Nat.mod_lt _ hp.pos, Nat.div_add_mod' m p⟩`. Take `⟨v, hv⟩` from `exists_inv hp hnil (not_dvd_coeff hp a c hc)`. Establish `hco` using `coeff_mul_dpow δ hp hμJ hwJ hw a c`.

Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k, a + c = k + 1 := by`. Use `⟨a + c - 1, ?_⟩` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos a with rfl | ha` into its components or cases. Simplify using `only [zero_mul, zero_add] at h ⊢`. Use linear arithmetic over natural numbers and integers.

Use linear arithmetic over natural numbers and integers. Take `⟨q, rfl⟩ : ∃ q, p = q + 1` from `⟨p - 1, by omega⟩`. Use `⟨v * (μ ^ k * δ.dpow a w), fun h1 ↦ by omega, fun _ ↦ ⟨?_, ?_⟩, fun hM ↦ ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Establish `h5` using `GlobalTheory.Cris.ExpBij.mul_mem_dpFil δ (GlobalTheory.Cris.ExpBij.pow_mem_dpFil δ (GlobalTheory.Cris.ExpBij.mem_dpFil_one δ hμJ) k) (GlobalTheory.Cris.ExpBij.dpow_mem_dpFil_mul δ hp1 hwf a)`.

Establish `e : a * (q + 1) + c - 1 = k * 1 + a * (q + 1 - 1)`. Rewrite using `[Nat.add_sub_cancel, Nat.mul_succ]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[e]`. Conclude with `Ideal.mul_mem_left _ _ h5`.

Establish `h6 : n + 2 ≤ a`. Assume the negation of the conclusion as `hlt`. Establish `h7 : a + 1 ≤ n + 2` using `by omega`. Establish `h8` using `Nat.mul_le_mul_left (q + 1) h7`. Use the polynomial consequences of the given equalities and inequalities.

Establish `h9 : μ ^ k = 0` using `pow_eq_zero_of_le (by omega : n ≤ k) (hn μ hμJ)`. Simplify using `[h9]`. Use `choose ν h1 h2 h3 using key`. Use `⟨⟨n, hn _ hμJ⟩, ν, h1 1 rfl, fun m ↦ (h2 (m + 1) (by omega)).1, fun m ↦ ?_, fun m hm ↦ ?_, p * (n + 2), fun m hm ↦ h3 m hm⟩` and prove the remaining obligations. Establish `h` using `(h2 (m + 1) (by omega)).2`.

Rewrite `h` using `[Nat.add_sub_cancel]`. Conclude with `h`. Conclude with `⟨n, hn _ (GlobalTheory.Cris.ExpBij.dpFil_le δ (show 1 ≤ m - 1 by omega) (h2 m (by omega)).2)⟩`.
-/
theorem dpow_pow_sub_one : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (p : ℕ), p.Prime → IsNilpotent (p : B) → ∀ x : B, (∑ i ∈ Finset.range p, x ^ i) ∈ J → IsNilpotent (x ^ p - 1) ∧ ∃ ν : ℕ → B, ν 1 = 1 ∧ (∀ m, δ.dpow (m + 1) (x ^ p - 1) = (x ^ p - 1) * ν (m + 1)) ∧ (∀ m, ν (m + 1) ∈ fil δ m) ∧ (∀ m, 2 ≤ m → IsNilpotent (ν m)) ∧ ∃ M, ∀ m, M ≤ m → ν m = 0 := by
  intro B _ J δ p hp hnil x hξ
  have hμJ : x ^ p - 1 ∈ J := by
    rw [← mul_geom_sum]
    exact J.mul_mem_left _ hξ
  obtain ⟨n, hn⟩ := exists_pow_eq_zero δ hp hnil
  obtain ⟨w, hwf, hw⟩ := exists_dpow_prime_eq δ hp hnil x hξ
  have hp2 := hp.two_le
  have hp1 : 1 ≤ p - 1 := by omega
  have hwJ : w ∈ J := GlobalTheory.Cris.ExpBij.dpFil_le δ hp1 hwf
  generalize x ^ p - 1 = μ at hμJ hw ⊢
  have key : ∀ m, ∃ b : B, (m = 1 → b = 1) ∧
      (1 ≤ m → δ.dpow m μ = μ * b ∧ b ∈ GlobalTheory.Cris.ExpBij.dpFil δ (m - 1)) ∧
      (p * (n + 2) ≤ m → b = 0) := by
    intro m
    rcases Nat.lt_or_ge m 2 with h | h
    · interval_cases m
      · exact ⟨0, by simp, by simp, fun _ ↦ rfl⟩
      · refine ⟨1, fun _ ↦ rfl, fun _ ↦ ⟨by rw [δ.dpow_one hμJ, mul_one],
          GlobalTheory.Cris.ExpBij.mem_dpFil_zero δ 1⟩, fun h ↦ ?_⟩
        nlinarith
    · obtain ⟨a, c, hc, rfl⟩ : ∃ a c, c < p ∧ a * p + c = m :=
        ⟨m / p, m % p, Nat.mod_lt _ hp.pos, Nat.div_add_mod' m p⟩
      obtain ⟨v, hv⟩ := exists_inv hp hnil (not_dvd_coeff hp a c hc)
      have hco := coeff_mul_dpow δ hp hμJ hwJ hw a c
      obtain ⟨k, hk⟩ : ∃ k, a + c = k + 1 := by
        refine ⟨a + c - 1, ?_⟩
        rcases Nat.eq_zero_or_pos a with rfl | ha
        · simp only [zero_mul, zero_add] at h ⊢
          omega
        · omega
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      refine ⟨v * (μ ^ k * δ.dpow a w), fun h1 ↦ by omega, fun _ ↦ ⟨?_, ?_⟩, fun hM ↦ ?_⟩
      · calc δ.dpow (a * (q + 1) + c) μ
            = (v * ((Nat.uniformBell a (q + 1) * (a * (q + 1) + c).choose (a * (q + 1)) *
                c.factorial : ℕ) : B)) * δ.dpow (a * (q + 1) + c) μ := by rw [hv, one_mul]
          _ = v * (μ ^ (a + c) * δ.dpow a w) := by rw [mul_assoc, hco]
          _ = μ * (v * (μ ^ k * δ.dpow a w)) := by rw [hk, pow_succ]; ring
      · have h5 := GlobalTheory.Cris.ExpBij.mul_mem_dpFil δ
          (GlobalTheory.Cris.ExpBij.pow_mem_dpFil δ (GlobalTheory.Cris.ExpBij.mem_dpFil_one δ hμJ) k)
          (GlobalTheory.Cris.ExpBij.dpow_mem_dpFil_mul δ hp1 hwf a)
        have e : a * (q + 1) + c - 1 = k * 1 + a * (q + 1 - 1) := by
          rw [Nat.add_sub_cancel, Nat.mul_succ]
          omega
        rw [e]
        exact Ideal.mul_mem_left _ _ h5
      · have h6 : n + 2 ≤ a := by
          by_contra hlt
          have h7 : a + 1 ≤ n + 2 := by omega
          have h8 := Nat.mul_le_mul_left (q + 1) h7
          nlinarith
        have h9 : μ ^ k = 0 := pow_eq_zero_of_le (by omega : n ≤ k) (hn μ hμJ)
        simp [h9]
  choose ν h1 h2 h3 using key
  refine ⟨⟨n, hn _ hμJ⟩, ν, h1 1 rfl, fun m ↦ (h2 (m + 1) (by omega)).1, fun m ↦ ?_, fun m hm ↦ ?_,
    p * (n + 2), fun m hm ↦ h3 m hm⟩
  · have h := (h2 (m + 1) (by omega)).2
    rw [Nat.add_sub_cancel] at h
    exact h
  · exact ⟨n, hn _ (GlobalTheory.Cris.ExpBij.dpFil_le δ (show 1 ≤ m - 1 by omega) (h2 m (by omega)).2)⟩

end GlobalTheory.CompanionTheory.QPd
