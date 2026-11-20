import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.DirichletCharacterLevelRaising

open Finset UpperTheory.V.Bern

/- English proof (translation)
Apply `MulChar.map_nonunit` to reduce the goal to its premises. Rewrite using `[ZMod.isUnit_iff_coprime]`. Introduce `hc`. Conclude with `hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hc hpN)`.
-/
private theorem UpperTheory.V.Bern.level_zero {R : Type} [CommRing R] {N p : ℕ} (χ : DirichletCharacter R N)
    (hp : p.Prime) (hpN : p ∣ N) : χ (p : ZMod N) = 0 := by
  apply MulChar.map_nonunit
  rw [ZMod.isUnit_iff_coprime]
  intro hc
  exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hc hpN)

/- English proof (translation)
Establish `hc : p.Coprime M` using `(Nat.Prime.coprime_iff_not_dvd hp).2 hpM`. Use `DirichletCharacter.changeLevel_eq_cast_of_dvd χ h (ZMod.unitOfCoprime p hc)` as an intermediate fact. Rewrite `this` using `[ZMod.coe_unitOfCoprime, ZMod.cast_natCast h]`. Conclude with `this`.
-/
private theorem UpperTheory.V.Bern.level_val {R : Type} [CommRing R] {N M p : ℕ} (h : N ∣ M)
    (χ : DirichletCharacter R N) (hp : p.Prime) (hpM : ¬ p ∣ M) :
    DirichletCharacter.changeLevel h χ (p : ZMod M) = χ (p : ZMod N) := by
  have hc : p.Coprime M := (Nat.Prime.coprime_iff_not_dvd hp).2 hpM
  have := DirichletCharacter.changeLevel_eq_cast_of_dvd χ h (ZMod.unitOfCoprime p hc)
  rw [ZMod.coe_unitOfCoprime, ZMod.cast_natCast h] at this
  exact this

/- English proof (translation)
Proceed by induction on `m using induction_on_primes with`. Consider the case `zero => intro h`. Conclude with `absurd h (lt_irrefl 0)`. Consider the case `one`. Introduce `_ M h hM`.

Rewrite `hM` using `[mul_one]`. Substitute `hM` using the available equality. Rewrite using `[DirichletCharacter.changeLevel_self, Finset.prod_eq_one, mul_one]`. Introduce `p hp`. Rewrite using `[level_zero χ (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp), zero_mul, sub_zero]`.

Consider the case `prime_mul p a hp ih`. Introduce `hpa M h hM`. Establish `ha : 0 < a` using `Nat.pos_of_mul_pos_left hpa`. Establish `hM' : M = N * a * p` using `by rw [hM]; ring`. Substitute `hM'` using the available equality.

Establish `hNa : 0 < N * a` using `Nat.mul_pos hN ha`. Establish `ih'` using `ih ha (N * a) (dvd_mul_right N a) rfl`. Establish `hs` using `b_step k (DirichletCharacter.changeLevel (dvd_mul_right N a) χ) hNa hp hk`. Rewrite `hs` using `[← DirichletCharacter.changeLevel_trans]`. Rewrite using `[hs, ih', Nat.primeFactors_mul hNa.ne' hp.ne_zero, hp.primeFactors]`.

Distinguish the cases in `hd : p ∣ N * a`. Rewrite using `[level_zero _ hp hd, Finset.union_eq_left.2 (by`. Simplify using `using ⟨hp, hd, hN.ne', ha.ne'⟩)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[level_val _ χ hp hd, Finset.prod_union (by`.

Rewrite using `[Finset.disjoint_singleton_right]`. Conclude with `fun hh => hd (Nat.dvd_of_mem_primeFactors hh)), Finset.prod_singleton]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem UpperTheory.V.Bern.generalized_bernoulli_change_level {R : Type} [CommRing R] [Algebra ℚ R] {N : ℕ} (k : ℕ)
    (χ : DirichletCharacter R N) (hN : 0 < N) (hk : 1 ≤ k) (m : ℕ) :
    0 < m → ∀ (M : ℕ) (h : N ∣ M), M = N * m →
      genB k (DirichletCharacter.changeLevel h χ : ZMod M → R)
        = genB k χ * ∏ p ∈ M.primeFactors, (1 - χ (p : ZMod N) * (p : R) ^ (k - 1)) := by
  induction m using induction_on_primes with
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | one =>
    intro _ M h hM
    rw [mul_one] at hM
    subst hM
    rw [DirichletCharacter.changeLevel_self, Finset.prod_eq_one, mul_one]
    intro p hp
    rw [level_zero χ (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp), zero_mul, sub_zero]
  | prime_mul p a hp ih =>
    intro hpa M h hM
    have ha : 0 < a := Nat.pos_of_mul_pos_left hpa
    have hM' : M = N * a * p := by rw [hM]; ring
    subst hM'
    have hNa : 0 < N * a := Nat.mul_pos hN ha
    have ih' := ih ha (N * a) (dvd_mul_right N a) rfl
    have hs := b_step k (DirichletCharacter.changeLevel (dvd_mul_right N a) χ) hNa hp hk
    rw [← DirichletCharacter.changeLevel_trans] at hs
    rw [hs, ih', Nat.primeFactors_mul hNa.ne' hp.ne_zero, hp.primeFactors]
    by_cases hd : p ∣ N * a
    · rw [level_zero _ hp hd, Finset.union_eq_left.2 (by
        simpa using ⟨hp, hd, hN.ne', ha.ne'⟩)]
      ring
    · rw [level_val _ χ hp hd, Finset.prod_union (by
        rw [Finset.disjoint_singleton_right]
        exact fun hh => hd (Nat.dvd_of_mem_primeFactors hh)), Finset.prod_singleton]
      ring

/- English proof (translation)
Introduce `R _ _ N M h k χ hM hk`. Take `⟨m, hm⟩` from `id h`. Establish `hpos : 0 < N * m` using `hm ▸ hM`. Conclude with `generalized_bernoulli_change_level k χ (Nat.pos_of_mul_pos_right hpos) hk m (Nat.pos_of_mul_pos_left hpos) M h hm`.
-/
theorem UpperTheory.V.Bern.b_level :
    ∀ {R : Type} [CommRing R] [Algebra ℚ R] {N M : ℕ} (h : N ∣ M) (k : ℕ) (χ : DirichletCharacter R N), 0 < M → 1 ≤ k → genB k (DirichletCharacter.changeLevel h χ : ZMod M → R) = genB k χ * ∏ p ∈ M.primeFactors, (1 - χ (p : ZMod N) * (p : R) ^ (k - 1)) := by
  intro R _ _ N M h k χ hM hk
  obtain ⟨m, hm⟩ := id h
  have hpos : 0 < N * m := hm ▸ hM
  exact generalized_bernoulli_change_level k χ (Nat.pos_of_mul_pos_right hpos) hk m (Nat.pos_of_mul_pos_left hpos) M h hm
