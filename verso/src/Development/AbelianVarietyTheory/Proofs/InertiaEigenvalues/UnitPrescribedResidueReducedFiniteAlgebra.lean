import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory

/- English proof (translation)
Use `haveI : IsArtinianRing B.A := IsArtinianRing.of_finite K.E B.A`. Set `e` to `IsArtinianRing.equivPi B.A`. Set `v : (I : MaximalSpectrum B.A) → B.A ⧸ I.asIdeal` to `fun I => if h : I = m then h ▸ z else 1`. Establish `hv : IsUnit v`. Rewrite using `[Pi.isUnit_iff]`.

Introduce `I`. Use `letI := Ideal.Quotient.field I.asIdeal`. Rewrite using `[isUnit_iff_ne_zero]`. Distinguish the cases in `h : I = m`. Substitute `h` using the available equality.

Simplify `hz` using `[v]`. Simplify using `[v, h]`. Establish `hy : IsUnit (e.symm v)` using `hv.map e.symm`. Use `⟨hy.unit, ?_, ?_⟩` and prove the remaining obligations. Use `IsArtinianRing.equivPi_apply B.A (e.symm v) m` as an intermediate fact.

Rewrite `this` using `[AlgEquiv.apply_symm_apply]`. Simplify using `only [IsUnit.unit_spec]`. Rewrite using `[← this]`. Simplify using `[v]`. Introduce `m' hm'`.

Use `IsArtinianRing.equivPi_apply B.A (e.symm v) m'` as an intermediate fact. Rewrite `this` using `[AlgEquiv.apply_symm_apply]`. Simplify using `only [IsUnit.unit_spec]`. Rewrite using `[← this]`. Simplify using `[v, hm']`.
-/
theorem UnitLemma.exists_unit_residue (K : UQ) (B : InvAlg K) (hB : IsReduced B.A) (m : MaximalSpectrum B.A)
    (z : B.A ⧸ m.asIdeal) (hz : z ≠ 0) :
    ∃ y : B.Aˣ, Ideal.Quotient.mk m.asIdeal (y : B.A) = z ∧
      ∀ m' : MaximalSpectrum B.A, m' ≠ m → Ideal.Quotient.mk m'.asIdeal (y : B.A) = 1 := by
  classical
  haveI : IsArtinianRing B.A := IsArtinianRing.of_finite K.E B.A
  let e := IsArtinianRing.equivPi B.A
  let v : (I : MaximalSpectrum B.A) → B.A ⧸ I.asIdeal := fun I =>
    if h : I = m then h ▸ z else 1
  have hv : IsUnit v := by
    rw [Pi.isUnit_iff]
    intro I
    letI := Ideal.Quotient.field I.asIdeal
    rw [isUnit_iff_ne_zero]
    by_cases h : I = m
    · subst h; simpa [v] using hz
    · simp [v, h]
  have hy : IsUnit (e.symm v) := hv.map e.symm
  refine ⟨hy.unit, ?_, ?_⟩
  · have := IsArtinianRing.equivPi_apply B.A (e.symm v) m
    rw [AlgEquiv.apply_symm_apply] at this
    simp only [IsUnit.unit_spec]
    rw [← this]; simp [v]
  · intro m' hm'
    have := IsArtinianRing.equivPi_apply B.A (e.symm v) m'
    rw [AlgEquiv.apply_symm_apply] at this
    simp only [IsUnit.unit_spec]
    rw [← this]; simp [v, hm']

/- English proof (translation)
Introduce `K B hB m z hz` and use `UnitLemma.exists_unit_residue K B hB m z hz`.
-/
theorem UnitLemma.unit_prescribed_residue : ∀ (K : UQ) (B : InvAlg K), IsReduced B.A → ∀ (m : MaximalSpectrum B.A)
    (z : B.A ⧸ m.asIdeal), z ≠ 0 → ∃ y : B.Aˣ, Ideal.Quotient.mk m.asIdeal (y : B.A) = z ∧
      ∀ m' : MaximalSpectrum B.A, m' ≠ m → Ideal.Quotient.mk m'.asIdeal (y : B.A) = 1 :=
  fun K B hB m z hz => UnitLemma.exists_unit_residue K B hB m z hz

end GlobalTheory
