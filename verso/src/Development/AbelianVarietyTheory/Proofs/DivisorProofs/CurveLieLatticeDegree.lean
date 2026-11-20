import Mathlib
open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.EtaleHeightOne

/- English proof (translation)
Use `set p : Ideal A := Q.comap (algebraMap A B) with hp`. Use `haveI : p.IsPrime := Ideal.comap_isPrime _ Q`. Use `haveI : Q.LiesOver p := ⟨rfl⟩`. Rewrite using `[show ((1 : ℕ∞)) = ((1 : ℕ) : ℕ∞) from rfl, Ideal.height_le_iff]`. Introduce `r hr hrp`.

Assume the negation of the conclusion as `hcon`. Establish `hr0 : r ≠ ⊥`. Introduce and unpack `rfl`. Simplify using `at hcon`. Use `haveI := hr`.

Take `⟨P₁, hP₁Q, hP₁, hP₁o⟩` from `Ideal.exists_ideal_lt_liesOver_of_lt (p := r) (q := p) Q hrp`. Use `haveI := hP₁`. Use `haveI : (⊥ : Ideal A).IsPrime := Ideal.bot_prime`. Take `⟨P₀, hP₀P₁, hP₀, -⟩` from `Ideal.exists_ideal_lt_liesOver_of_lt (p := ⊥) (q := r) P₁ (bot_lt_iff_ne_bot.mpr hr0)`. Use `haveI := hP₀`.

Establish `h1` using `Ideal.height_add_one_le_of_lt_of_isPrime hP₀P₁`. Establish `h2` using `Ideal.height_add_one_le_of_lt_of_isPrime hP₁Q`. Establish `h4 : (1 : ℕ∞) ≤ P₁.height` using `le_trans le_add_self h1`. Establish `h3 : (1 : ℕ∞) + 1 ≤ 1` using `le_trans (by gcongr) (h2.trans hQ)`. Conclude with `absurd h3 (by decide)`.
-/
theorem height_comap_le_one_of_goingDown {A B : Type} [CommRing A] [IsDomain A] [CommRing B]
    [Algebra A B] [Algebra.HasGoingDown A B] (Q : Ideal B) [Q.IsPrime] (hQ : Q.height ≤ 1) :
    (Q.comap (algebraMap A B)).height ≤ 1 := by
  set p : Ideal A := Q.comap (algebraMap A B) with hp
  haveI : p.IsPrime := Ideal.comap_isPrime _ Q
  haveI : Q.LiesOver p := ⟨rfl⟩
  rw [show ((1 : ℕ∞)) = ((1 : ℕ) : ℕ∞) from rfl, Ideal.height_le_iff]
  intro r hr hrp
  by_contra hcon
  have hr0 : r ≠ ⊥ := by
    rintro rfl
    simp at hcon
  haveI := hr
  obtain ⟨P₁, hP₁Q, hP₁, hP₁o⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := r) (q := p) Q hrp
  haveI := hP₁
  haveI : (⊥ : Ideal A).IsPrime := Ideal.bot_prime
  obtain ⟨P₀, hP₀P₁, hP₀, -⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := ⊥) (q := r) P₁
    (bot_lt_iff_ne_bot.mpr hr0)
  haveI := hP₀
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hP₀P₁
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hP₁Q
  have h4 : (1 : ℕ∞) ≤ P₁.height := le_trans le_add_self h1
  have h3 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (by gcongr) (h2.trans hQ)
  exact absurd h3 (by decide)

/- English proof (translation)
Introduce `A _ _ _ _ E _ _ _ _ _ Q _ P _ a ha haP hP`. Use `set R := Localization.AtPrime Q`. Use `haveI : Module.Flat A[X] E := inferInstance`. Use `haveI : Module.Flat A E := Module.Flat.trans A A[X] E`. Use `haveI : Module.Flat E R := inferInstance`.

Use `haveI : Module.Flat A R := Module.Flat.trans A E R`. Use `haveI : Module.Flat A[X] R := Module.Flat.trans A[X] E R`. Use `haveI : Algebra.HasGoingDown A R := Algebra.HasGoingDown.of_flat`. Use `haveI : Algebra.HasGoingDown A[X] R := Algebra.HasGoingDown.of_flat`. Use `set p := P.comap (algebraMap A R) with hp`.

Use `haveI : p.IsPrime := Ideal.comap_isPrime _ P`. Establish `hpne : p ≠ ⊥`. Introduce `h`. Establish `: a ∈ p` using `haP`. Rewrite `this` using `[h, Ideal.mem_bot]`.

Conclude with `ha this`. Use `haveI : (⊥ : Ideal A).IsPrime := Ideal.bot_prime`. Establish `hp1 : 1 ≤ p.height`. Use `Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hpne)` as an intermediate fact. Simplify using `using this`.

Use `⟨le_antisymm (height_comap_le_one_of_goingDown P hP) hp1, ?_⟩` and prove the remaining obligations. Establish `htower : algebraMap A R = (algebraMap A[X] R).comp (Polynomial.C : A →+* A[X])`. Rewrite using `[IsScalarTower.algebraMap_eq A E R, IsScalarTower.algebraMap_eq A[X] E R, IsScalarTower.algebraMap_eq A A[X] E, ← Polynomial.algebraMap_eq]`. Both sides reduce to the same expression. Use `set P' := P.comap (algebraMap A[X] R) with hP'`.

Use `haveI : P'.IsPrime := Ideal.comap_isPrime _ P`. Use `haveI hCp : (p.map (Polynomial.C : A →+* A[X])).IsPrime := Ideal.isPrime_map_C_of_isPrime`. Establish `hle : p.map (Polynomial.C : A →+* A[X]) ≤ P'`. Rewrite using `[Ideal.map_le_iff_le_comap, hP', Ideal.comap_comap, ← htower]`. Establish `hP'1 : P'.height ≤ 1` using `height_comap_le_one_of_goingDown P hP`.

Assume the negation of the conclusion as `hne`. Establish `hlt : p.map (Polynomial.C : A →+* A[X]) < P'` using `lt_of_le_of_ne hle (Ne.symm hne)`. Establish `hCne : p.map (Polynomial.C : A →+* A[X]) ≠ ⊥`. Introduce `h`. Apply `hpne` to reduce the goal to its premises.

Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Establish `: Polynomial.C x ∈ p.map (Polynomial.C : A →+* A[X])` using `Ideal.mem_map_of_mem _ hx`. Rewrite `this` using `[h, Ideal.mem_bot, Polynomial.C_eq_zero]`. Simplify using `[this]`.

Use `haveI : (⊥ : Ideal A[X]).IsPrime := Ideal.bot_prime`. Establish `h1` using `Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hCne)`. Establish `h2` using `Ideal.height_add_one_le_of_lt_of_isPrime hlt`. Establish `h4 : (1 : ℕ∞) ≤ (p.map (Polynomial.C : A →+* A[X])).height` using `by simpa using h1`. Establish `h3 : (1 : ℕ∞) + 1 ≤ 1` using `le_trans (by gcongr) (h2.trans hP'1)`.

Conclude with `absurd h3 (by decide)`.
-/
theorem height_one_and_comap_eq_map_C : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (E : Type) [CommRing E] [Algebra A[X] E] [Algebra A E] [IsScalarTower A A[X] E]
    [Algebra.Etale A[X] E] (Q : Ideal E) [Q.IsPrime] (P : Ideal (Localization.AtPrime Q)) [P.IsPrime]
    (a : A), a ≠ 0 → algebraMap A (Localization.AtPrime Q) a ∈ P → P.height ≤ 1 →
    (P.comap (algebraMap A (Localization.AtPrime Q))).height = 1 ∧
      P.comap (algebraMap A[X] (Localization.AtPrime Q)) =
        (P.comap (algebraMap A (Localization.AtPrime Q))).map (Polynomial.C : A →+* A[X]) := by
  intro A _ _ _ _ E _ _ _ _ _ Q _ P _ a ha haP hP
  set R := Localization.AtPrime Q
  haveI : Module.Flat A[X] E := inferInstance
  haveI : Module.Flat A E := Module.Flat.trans A A[X] E
  haveI : Module.Flat E R := inferInstance
  haveI : Module.Flat A R := Module.Flat.trans A E R
  haveI : Module.Flat A[X] R := Module.Flat.trans A[X] E R
  haveI : Algebra.HasGoingDown A R := Algebra.HasGoingDown.of_flat
  haveI : Algebra.HasGoingDown A[X] R := Algebra.HasGoingDown.of_flat
  set p := P.comap (algebraMap A R) with hp
  haveI : p.IsPrime := Ideal.comap_isPrime _ P
  have hpne : p ≠ ⊥ := by
    intro h
    have : a ∈ p := haP
    rw [h, Ideal.mem_bot] at this
    exact ha this
  haveI : (⊥ : Ideal A).IsPrime := Ideal.bot_prime
  have hp1 : 1 ≤ p.height := by
    have := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hpne)
    simpa using this
  refine ⟨le_antisymm (height_comap_le_one_of_goingDown P hP) hp1, ?_⟩
  have htower : algebraMap A R = (algebraMap A[X] R).comp (Polynomial.C : A →+* A[X]) := by
    rw [IsScalarTower.algebraMap_eq A E R, IsScalarTower.algebraMap_eq A[X] E R,
      IsScalarTower.algebraMap_eq A A[X] E, ← Polynomial.algebraMap_eq]
    rfl
  set P' := P.comap (algebraMap A[X] R) with hP'
  haveI : P'.IsPrime := Ideal.comap_isPrime _ P
  haveI hCp : (p.map (Polynomial.C : A →+* A[X])).IsPrime := Ideal.isPrime_map_C_of_isPrime
  have hle : p.map (Polynomial.C : A →+* A[X]) ≤ P' := by
    rw [Ideal.map_le_iff_le_comap, hP', Ideal.comap_comap, ← htower]
  have hP'1 : P'.height ≤ 1 := height_comap_le_one_of_goingDown P hP
  by_contra hne
  have hlt : p.map (Polynomial.C : A →+* A[X]) < P' := lt_of_le_of_ne hle (Ne.symm hne)
  have hCne : p.map (Polynomial.C : A →+* A[X]) ≠ ⊥ := by
    intro h
    apply hpne
    rw [eq_bot_iff]
    intro x hx
    have : Polynomial.C x ∈ p.map (Polynomial.C : A →+* A[X]) := Ideal.mem_map_of_mem _ hx
    rw [h, Ideal.mem_bot, Polynomial.C_eq_zero] at this
    simp [this]
  haveI : (⊥ : Ideal A[X]).IsPrime := Ideal.bot_prime
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hCne)
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have h4 : (1 : ℕ∞) ≤ (p.map (Polynomial.C : A →+* A[X])).height := by simpa using h1
  have h3 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (by gcongr) (h2.trans hP'1)
  exact absurd h3 (by decide)

end GlobalTheory.EtaleHeightOne
