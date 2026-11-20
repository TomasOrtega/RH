import Mathlib

open IsLocalRing

namespace GlobalTheory

/- English proof (translation)
Use `set p := (maximalIdeal B).comap (algebraMap A B) with hp`. Use `haveI : p.IsPrime := Ideal.comap_isPrime _ _`. Set `A'` to `Localization.AtPrime p`. Establish `hg : ∀ y : p.primeCompl, IsUnit (algebraMap A B y)`. Introduce `y`.

Establish `: (y : A) ∉ p` using `y.2`. Conclude with `IsLocalRing.notMem_maximalIdeal.mp this`. Set `f : A' →+* B` to `IsLocalization.lift (M := p.primeCompl) hg`. Use `letI : Algebra A' B := f.toAlgebra`. Use `haveI : IsScalarTower A A' B := IsScalarTower.of_algebraMap_eq (fun x => (IsLocalization.lift_eq (M := p.primeCompl) hg x).symm)`.

Use `haveI : IsLocalHom (algebraMap A' B) := by`. Prove the components needed by the constructor for the conclusion. Introduce `x hx`. Take `⟨⟨a, s⟩, rfl⟩` from `IsLocalization.mk'_surjective p.primeCompl x`. Establish `e : IsLocalization.mk' A' a s * algebraMap A A' s = algebraMap A A' a` using `IsLocalization.mk'_spec A' a s`.

Establish `hs : IsUnit (algebraMap A' B (algebraMap A A' s))`. Rewrite using `[← IsScalarTower.algebraMap_apply]`. Conclude with `hg s`. Establish `ha : IsUnit (algebraMap A B a)`. Rewrite using `[IsScalarTower.algebraMap_apply A A' B, ← e, map_mul]`.

Conclude with `hx.mul hs`. Establish `ha' : a ∈ p.primeCompl` using `by show a ∉ p`. Rewrite using `[hp, Ideal.mem_comap]`. Conclude with `IsLocalRing.notMem_maximalIdeal.mpr ha`. Establish `hu : IsUnit (algebraMap A A' a)` using `IsLocalization.map_units A' (⟨a, ha'⟩ : p.primeCompl)`.

Rewrite `hu` using `[← e]`. Conclude with `isUnit_of_mul_isUnit_left hu`. Use `haveI : Algebra.FormallyUnramified A' B := .of_restrictScalars A A' B`. Use `haveI : Algebra.EssFiniteType A' B := .of_comp A A' B`. Establish `h` using `Algebra.FormallyUnramified.map_maximalIdeal (R := A') (S := B)`.

Rewrite `h` using `[← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq]`. Conclude with `h`.
-/
theorem map_comap_maximalIdeal_eq_of_formallyUnramified
    (A B : Type) [CommRing A] [CommRing B] [IsLocalRing B] [Algebra A B]
    [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B] :
    ((IsLocalRing.maximalIdeal B).comap (algebraMap A B)).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B := by
  set p := (maximalIdeal B).comap (algebraMap A B) with hp
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  let A' := Localization.AtPrime p
  have hg : ∀ y : p.primeCompl, IsUnit (algebraMap A B y) := by
    intro y
    have : (y : A) ∉ p := y.2
    exact IsLocalRing.notMem_maximalIdeal.mp this
  let f : A' →+* B := IsLocalization.lift (M := p.primeCompl) hg
  letI : Algebra A' B := f.toAlgebra
  haveI : IsScalarTower A A' B := IsScalarTower.of_algebraMap_eq
    (fun x => (IsLocalization.lift_eq (M := p.primeCompl) hg x).symm)
  haveI : IsLocalHom (algebraMap A' B) := by
    constructor
    intro x hx
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl x
    have e : IsLocalization.mk' A' a s * algebraMap A A' s = algebraMap A A' a :=
      IsLocalization.mk'_spec A' a s
    have hs : IsUnit (algebraMap A' B (algebraMap A A' s)) := by
      rw [← IsScalarTower.algebraMap_apply]; exact hg s
    have ha : IsUnit (algebraMap A B a) := by
      rw [IsScalarTower.algebraMap_apply A A' B, ← e, map_mul]; exact hx.mul hs
    have ha' : a ∈ p.primeCompl := by
      show a ∉ p
      rw [hp, Ideal.mem_comap]
      exact IsLocalRing.notMem_maximalIdeal.mpr ha
    have hu : IsUnit (algebraMap A A' a) := IsLocalization.map_units A' (⟨a, ha'⟩ : p.primeCompl)
    rw [← e] at hu
    exact isUnit_of_mul_isUnit_left hu
  haveI : Algebra.FormallyUnramified A' B := .of_restrictScalars A A' B
  haveI : Algebra.EssFiniteType A' B := .of_comp A A' B
  have h := Algebra.FormallyUnramified.map_maximalIdeal (R := A') (S := B)
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq] at h
  exact h

end GlobalTheory
