import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.CongruenceSubgroups

/- English proof (translation)
Introduce `k _ _ _ _ N m m' h`. Introduce and unpack `_ ⟨g, hg, rfl⟩`. Use `⟨g, ?_, rfl⟩` and prove the remaining obligations. Establish `hle : Ideal.span {Zls.unif k ^ m'} ≤ Ideal.span {Zls.unif k ^ m}` using `Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ h)`. Establish `hg' : Matrix.GeneralLinearGroup.map (n` using `Fin N) (Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m'})) g = 1 := hg`.

Establish `h2` using `congrArg (Matrix.GeneralLinearGroup.map (n := Fin N) (Ideal.Quotient.factor hle)) hg'`. Rewrite `h2` using `[map_one]`. Use `show Matrix.GeneralLinearGroup.map (n := Fin N) (Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m})) g = 1`. Rewrite using `[← h2]`. Use extensionality with `i j`.

Simplify using `[Matrix.GeneralLinearGroup.map]`.
-/
theorem Km_antitone : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N m m' : ℕ), m ≤ m' → Zls.Km k N m' ≤ Zls.Km k N m := by
  intro k _ _ _ _ N m m' h
  rintro _ ⟨g, hg, rfl⟩
  refine ⟨g, ?_, rfl⟩
  have hle : Ideal.span {Zls.unif k ^ m'} ≤ Ideal.span {Zls.unif k ^ m} :=
    Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ h)
  have hg' : Matrix.GeneralLinearGroup.map (n := Fin N)
      (Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m'})) g = 1 := hg
  have h2 := congrArg (Matrix.GeneralLinearGroup.map (n := Fin N) (Ideal.Quotient.factor hle)) hg'
  rw [map_one] at h2
  show Matrix.GeneralLinearGroup.map (n := Fin N)
      (Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m})) g = 1
  rw [← h2]
  ext i j
  simp [Matrix.GeneralLinearGroup.map]

end GlobalTheory.CompanionTheory.CongruenceSubgroups
