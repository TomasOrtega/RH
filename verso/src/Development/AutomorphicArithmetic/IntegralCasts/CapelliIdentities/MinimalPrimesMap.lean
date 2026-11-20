import Mathlib

/- English proof (translation)
Use `(Ideal.map_mono h.le).lt_of_not_ge fun e => h.not_ge ?_` and prove the remaining obligations. Establish `e'` using `Ideal.comap_mono (f := Ideal.Quotient.mk P) e`. Rewrite `e'` using `[Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hI, sup_eq_left.mpr (hI.trans h.le)]`. Conclude with `e'`.
-/
private lemma UpperTheory.Reformulated.B.MinimalPrimesMap.map_lt_map {A : Type} [CommRing A] {P I J : Ideal A}
    (hI : P ≤ I) (h : I < J) :
    I.map (Ideal.Quotient.mk P) < J.map (Ideal.Quotient.mk P) := by
  refine (Ideal.map_mono h.le).lt_of_not_ge fun e => h.not_ge ?_
  have e' := Ideal.comap_mono (f := Ideal.Quotient.mk P) e
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hI,
    sup_eq_left.mpr (hI.trans h.le)] at e'
  exact e'

/- English proof (translation)
Introduce `A _ _ P Q W hP hQ s hW hPQ hQW`. Assume the negation of the conclusion as `hne`. Rewrite `hne` using `[not_or]`. Establish `hW' : W.IsPrime` using `hW.1.1`. Establish `hprime : ∀ I : Ideal A, I.IsPrime → P ≤ I → (I.map (Ideal.Quotient.mk P)).IsPrime` using `fun I hI hle => Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])`.

Establish `i1` using `hprime P hP le_rfl`. Establish `i2` using `hprime Q hQ hPQ`. Establish `i3` using `hprime W hW' (hPQ.trans hQW)`. Establish `h1` using `Ideal.height_add_one_le_of_lt_of_isPrime (UpperTheory.Reformulated.B.MinimalPrimesMap.map_lt_map le_rfl (lt_of_le_of_ne hPQ (Ne.symm hne.1)))`. Establish `h2` using `Ideal.height_add_one_le_of_lt_of_isPrime (UpperTheory.Reformulated.B.MinimalPrimesMap.map_lt_map hPQ (lt_of_le_of_ne hQW hne.2))`.

Establish `h3` using `Ideal.map_height_le_one_of_mem_minimalPrimes hW`. Establish `h4 : (1 : ℕ∞) ≤ (Q.map (Ideal.Quotient.mk P)).height` using `le_add_self.trans h1`. Establish `h5 : (1 : ℕ∞) + 1 ≤ 1` using `(add_le_add h4 le_rfl).trans (h2.trans h3)`. Conclude with `absurd h5 (by decide)`.
-/
theorem UpperTheory.Reformulated.B.MinimalPrimesMap.eq_or_eq_of_mem_minimalPrimes :
    ∀ {A : Type} [inst : CommRing A] [IsNoetherianRing A]
    {P Q W : Ideal A} [hP : P.IsPrime] [hQ : Q.IsPrime] {s : A},
    W ∈ (P ⊔ Ideal.span {s}).minimalPrimes → P ≤ Q → Q ≤ W → Q = P ∨ Q = W := by
  intro A _ _ P Q W hP hQ s hW hPQ hQW
  by_contra hne
  rw [not_or] at hne
  have hW' : W.IsPrime := hW.1.1
  have hprime : ∀ I : Ideal A, I.IsPrime → P ≤ I → (I.map (Ideal.Quotient.mk P)).IsPrime :=
    fun I hI hle => Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rwa [Ideal.mk_ker])
  have i1 := hprime P hP le_rfl
  have i2 := hprime Q hQ hPQ
  have i3 := hprime W hW' (hPQ.trans hQW)
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime
    (UpperTheory.Reformulated.B.MinimalPrimesMap.map_lt_map le_rfl (lt_of_le_of_ne hPQ (Ne.symm hne.1)))
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime
    (UpperTheory.Reformulated.B.MinimalPrimesMap.map_lt_map hPQ (lt_of_le_of_ne hQW hne.2))
  have h3 := Ideal.map_height_le_one_of_mem_minimalPrimes hW
  have h4 : (1 : ℕ∞) ≤ (Q.map (Ideal.Quotient.mk P)).height := le_add_self.trans h1
  have h5 : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add h4 le_rfl).trans (h2.trans h3)
  exact absurd h5 (by decide)
