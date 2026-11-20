import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

/- English proof (translation)
The claim follows from `Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) z`.
-/
private lemma traceCM_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (z : E) :
    Algebra.trace ℚ E (IsCMField.complexConj E z) = Algebra.trace ℚ E z :=
  Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) z

/- English proof (translation)
The claim follows from `IsCMField.complexConj_apply_apply E z`.
-/
private lemma conj_conj' {E : Type} [Field E] [NumberField E] [IsCMField E] (z : E) :
    IsCMField.complexConj E (IsCMField.complexConj E z) = z :=
  IsCMField.complexConj_apply_apply E z

/- English proof (translation)
Introduce `x`. Take `⟨m, hm⟩` from `hy (bar.symm x)`. Use `⟨m, ?_⟩` and prove the remaining obligations. Establish `h : IsCMField.complexConj E y * (x : E) = IsCMField.complexConj E (y * ((bar.symm x : 𝓞 E) : E))`. Rewrite using `[map_mul, ← hbar, RingEquiv.apply_symm_apply]`.

Rewrite using `[h, traceCM_conj, hm]`.
-/
private lemma inCodiff_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E)
    (hbar : ∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) {y : E} (hy : InCodiff y) :
    InCodiff (IsCMField.complexConj E y) := by
  intro x
  obtain ⟨m, hm⟩ := hy (bar.symm x)
  refine ⟨m, ?_⟩
  have h : IsCMField.complexConj E y * (x : E) =
      IsCMField.complexConj E (y * ((bar.symm x : 𝓞 E) : E)) := by
    rw [map_mul, ← hbar, RingEquiv.apply_symm_apply]
  rw [h, traceCM_conj, hm]

/- English proof (translation)
Introduce `x`. Take `⟨m, hm⟩` from `hy (a * x)`. Use `⟨m, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_assoc, ← hm]`. Use `push_cast`.

Both sides reduce to the same expression.
-/
private lemma inCodiff_mul {E : Type} [Field E] [NumberField E] {y : E} (hy : InCodiff y) (a : 𝓞 E) :
    InCodiff (y * (a : E)) := by
  intro x
  obtain ⟨m, hm⟩ := hy (a * x)
  refine ⟨m, ?_⟩
  rw [mul_assoc, ← hm]
  push_cast
  rfl

/- English proof (translation)
Introduce `x`. Take `⟨m, hm⟩` from `hy x`. Take `⟨n, hn⟩` from `hz x`. Use `⟨m + n, ?_⟩` and prove the remaining obligations. Rewrite using `[add_mul, map_add, hm, hn]`.

Use `push_cast`. Both sides reduce to the same expression.
-/
private lemma inCodiff_add {E : Type} [Field E] [NumberField E] {y z : E} (hy : InCodiff y) (hz : InCodiff z) :
    InCodiff (y + z) := by
  intro x
  obtain ⟨m, hm⟩ := hy x
  obtain ⟨n, hn⟩ := hz x
  refine ⟨m + n, ?_⟩
  rw [add_mul, map_add, hm, hn]
  push_cast
  rfl

/- English proof (translation)
Introduce `hgen hunit E _ _ _ bar hbar M hM ε hε`. Take `⟨y, hy⟩` from `hgen E M hM`. Distinguish the cases in `hy0 : y = 0`. Substitute `hy0` using the available equality. Conclude with `⟨0, map_zero _, hy⟩`.

Take `⟨hyc, e, he, hegen⟩` from `hy`. Establish `hcy : InCodiff (IsCMField.complexConj E y)` using `inCodiff_conj bar hbar hyc`. Take `⟨x0, hx0⟩` from `hegen _ hcy`. Establish `hx0' : (e : E) * y = IsCMField.complexConj E y * ((bar x0 : 𝓞 E) : E)`. Establish `h` using `congrArg (IsCMField.complexConj E) hx0`.

Rewrite `h` using `[map_mul, map_mul, conj_conj', map_natCast]`. Rewrite using `[hbar, h]`. Establish `hnorm : x0 * bar x0 = (e : 𝓞 E) ^ 2`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Establish `h1 : y * ((e : E) ^ 2) = y * ((x0 : E) * ((bar x0 : 𝓞 E) : E))`.

Combine the equalities or inequalities in the displayed calculation. Establish `h2` using `mul_left_cancel₀ hy0 h1`. Use `push_cast`. Conclude with `h2.symm`. Use `set t : E := y * (ε : E) + IsCMField.complexConj E (y * (ε : E)) with ht`.

Use `⟨t, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[ht, map_add, conj_conj', add_comm]`. Apply `hunit E M hM y t ⟨hyc, e, he, hegen⟩ (inCodiff_add (inCodiff_mul hyc ε) (inCodiff_conj bar hbar (inCodiff_mul hyc ε)))` to reduce the goal to its premises. Introduce `P hP hMP`. Establish `heP : (e : 𝓞 E) ∉ P`.

Introduce `heP`. Take `⟨a, b, hab⟩` from `Nat.isCoprime_iff_coprime.mpr he`. Apply `hP.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one]`. Establish `h3 : ((a * e + b * M : ℤ) : 𝓞 E) = 1` using `by rw [hab]; simp`.

Rewrite using `[← h3]`. Use `push_cast`. Conclude with `P.add_mem (P.mul_mem_left _ heP) (P.mul_mem_left _ hMP)`. Establish `hx0P : x0 ∉ P`. Introduce `h`.

Apply `heP` to reduce the goal to its premises. Establish `h4 : (e : 𝓞 E) ^ 2 ∈ P` using `hnorm ▸ P.mul_mem_right _ h`. Conclude with `hP.isPrime.mem_of_pow_mem 2 h4`. Take `⟨h1, h2⟩` from `hε P hP hMP`. Use `⟨e, e * ε + x0 * bar ε, heP, ?_, ?_⟩` and prove the remaining obligations.

Introduce `hu`. Break down `hP.isPrime.mem_or_mem h2 with hεP | hεP` into its components or cases. Apply `hx0P` to reduce the goal to its premises. Establish `h5 : x0 = (e * ε + x0 * bar ε) - (e - x0) * ε - x0 * (ε + bar ε - 1)` using `by ring`. Rewrite using `[h5]`.

Conclude with `P.sub_mem (P.sub_mem hu (P.mul_mem_left _ hεP)) (P.mul_mem_left _ h1)`. Apply `heP` to reduce the goal to its premises. Establish `h5 : (e : 𝓞 E) = (e * ε + x0 * bar ε) - e * (ε + bar ε - 1) + (e - x0) * bar ε` using `by ring`. Rewrite using `[h5]`. Conclude with `P.add_mem (P.sub_mem hu (P.mul_mem_left _ h1)) (P.mul_mem_left _ hεP)`.

Rewrite using `[ht, map_mul, ← hbar]`. Use `push_cast`. Take the linear combination `((bar ε : 𝓞 E) : E) * hx0`.
-/
theorem UpperTheory.Gal.W2.Seed.pRealGen :
    CodiffGen → CodiffUnit → RealGen := by
  intro hgen hunit E _ _ _ bar hbar M hM ε hε
  obtain ⟨y, hy⟩ := hgen E M hM
  by_cases hy0 : y = 0
  · subst hy0
    exact ⟨0, map_zero _, hy⟩
  obtain ⟨hyc, e, he, hegen⟩ := hy
  have hcy : InCodiff (IsCMField.complexConj E y) := inCodiff_conj bar hbar hyc
  obtain ⟨x0, hx0⟩ := hegen _ hcy
  have hx0' : (e : E) * y = IsCMField.complexConj E y * ((bar x0 : 𝓞 E) : E) := by
    have h := congrArg (IsCMField.complexConj E) hx0
    rw [map_mul, map_mul, conj_conj', map_natCast] at h
    rw [hbar, h]
  have hnorm : x0 * bar x0 = (e : 𝓞 E) ^ 2 := by
    apply RingOfIntegers.ext
    have h1 : y * ((e : E) ^ 2) = y * ((x0 : E) * ((bar x0 : 𝓞 E) : E)) := by
      calc y * ((e : E) ^ 2) = (e : E) * ((e : E) * y) := by ring
        _ = (e : E) * IsCMField.complexConj E y * ((bar x0 : 𝓞 E) : E) := by rw [hx0']; ring
        _ = y * (x0 : E) * ((bar x0 : 𝓞 E) : E) := by rw [hx0]
        _ = _ := by ring
    have h2 := mul_left_cancel₀ hy0 h1
    push_cast
    exact h2.symm
  set t : E := y * (ε : E) + IsCMField.complexConj E (y * (ε : E)) with ht
  refine ⟨t, ?_, ?_⟩
  · rw [ht, map_add, conj_conj', add_comm]
  · apply hunit E M hM y t ⟨hyc, e, he, hegen⟩
      (inCodiff_add (inCodiff_mul hyc ε) (inCodiff_conj bar hbar (inCodiff_mul hyc ε)))
    intro P hP hMP
    have heP : (e : 𝓞 E) ∉ P := by
      intro heP
      obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr he
      apply hP.ne_top
      rw [Ideal.eq_top_iff_one]
      have h3 : ((a * e + b * M : ℤ) : 𝓞 E) = 1 := by rw [hab]; simp
      rw [← h3]
      push_cast
      exact P.add_mem (P.mul_mem_left _ heP) (P.mul_mem_left _ hMP)
    have hx0P : x0 ∉ P := by
      intro h
      apply heP
      have h4 : (e : 𝓞 E) ^ 2 ∈ P := hnorm ▸ P.mul_mem_right _ h
      exact hP.isPrime.mem_of_pow_mem 2 h4
    obtain ⟨h1, h2⟩ := hε P hP hMP
    refine ⟨e, e * ε + x0 * bar ε, heP, ?_, ?_⟩
    · intro hu
      rcases hP.isPrime.mem_or_mem h2 with hεP | hεP
      · apply hx0P
        have h5 : x0 = (e * ε + x0 * bar ε) - (e - x0) * ε - x0 * (ε + bar ε - 1) := by ring
        rw [h5]
        exact P.sub_mem (P.sub_mem hu (P.mul_mem_left _ hεP)) (P.mul_mem_left _ h1)
      · apply heP
        have h5 : (e : 𝓞 E) = (e * ε + x0 * bar ε) - e * (ε + bar ε - 1) + (e - x0) * bar ε := by ring
        rw [h5]
        exact P.add_mem (P.sub_mem hu (P.mul_mem_left _ h1)) (P.mul_mem_left _ hεP)
    · rw [ht, map_mul, ← hbar]
      push_cast
      linear_combination ((bar ε : 𝓞 E) : E) * hx0
