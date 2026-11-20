import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup

open NumberField in
/- English proof (translation)
Introduce `h F _ _ _`. Take `⟨L, i1, i2, i3, i, s, hs, hfix⟩` from `h F`. Use `⟨L, i1, i2, i3, RingOfIntegers.mapRingHom i, RingOfIntegers.mapRingHom s, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `w x`. Conclude with `hs w.embedding (x : L)`.

Introduce `x y hxy`. Establish `h1 : i (x : F) = i (y : F)` using `congrArg (fun z : 𝓞 L => (z : L)) hxy`. Conclude with `RingOfIntegers.ext (i.injective h1)`. Introduce `x`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Establish `h1 : s (x : L) = (x : L)` using `congrArg (fun z : 𝓞 L => (z : L)) hx`. Take `⟨y, hy⟩` from `(hfix _).1 h1`. Establish `hi : IsIntegral ℤ y`. Establish `h2 : IsIntegral ℤ (i.toIntAlgHom y)`.

Establish `: i.toIntAlgHom y = (x : L)` using `hy`. Rewrite using `[this]`. Conclude with `x.isIntegral_coe`. Conclude with `(isIntegral_algHom_iff i.toIntAlgHom i.injective).1 h2`. Conclude with `⟨⟨y, hi⟩, RingOfIntegers.ext hy⟩`.

Introduce and unpack `⟨y, hy⟩`. Establish `h1 : i (y : F) = (x : L)` using `congrArg (fun z : 𝓞 L => (z : L)) hy`. Conclude with `RingOfIntegers.ext ((hfix _).2 ⟨_, h1⟩)`.
-/
theorem UpperTheory.exists_CM_integral_of_exists_CM :
    UpperTheory.V.Af.BA.ExCM → UpperTheory.V.Af.BA.ExCMInt := by
  intro h F _ _ _
  obtain ⟨L, i1, i2, i3, i, s, hs, hfix⟩ := h F
  refine ⟨L, i1, i2, i3, RingOfIntegers.mapRingHom i, RingOfIntegers.mapRingHom s, ?_, ?_, ?_⟩
  · intro w x
    exact hs w.embedding (x : L)
  · intro x y hxy
    have h1 : i (x : F) = i (y : F) := congrArg (fun z : 𝓞 L => (z : L)) hxy
    exact RingOfIntegers.ext (i.injective h1)
  · intro x
    constructor
    · intro hx
      have h1 : s (x : L) = (x : L) := congrArg (fun z : 𝓞 L => (z : L)) hx
      obtain ⟨y, hy⟩ := (hfix _).1 h1
      have hi : IsIntegral ℤ y := by
        have h2 : IsIntegral ℤ (i.toIntAlgHom y) := by
          have : i.toIntAlgHom y = (x : L) := hy
          rw [this]
          exact x.isIntegral_coe
        exact (isIntegral_algHom_iff i.toIntAlgHom i.injective).1 h2
      exact ⟨⟨y, hi⟩, RingOfIntegers.ext hy⟩
    · rintro ⟨y, hy⟩
      have h1 : i (y : F) = (x : L) := congrArg (fun z : 𝓞 L => (z : L)) hy
      exact RingOfIntegers.ext ((hfix _).2 ⟨_, h1⟩)
