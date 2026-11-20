import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotCrysAtOfMono0
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIdeleCharLocalFactorization

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory

namespace GlobalTheory.NormDegOne

/- English proof (translation)
Introduce `K L _ _ _ _ _ w h`. Use `set P := w.asIdeal with hP`. Use `set Q := (w.under (𝓞 K)).asIdeal with hQ`. Establish `hQP : Q = P.under (𝓞 K)` using `rfl`. Establish `: P.IsPrime` using `w.isPrime`.

Establish `: Q.IsPrime` using `(w.under (𝓞 K)).isPrime`. Establish `hlo : P.LiesOver Q` using `⟨hQP⟩`. Establish `htow` using `Ideal.inertiaDeg_tower (R := ℤ) Q P`. Rewrite `htow` using `[h]`. Establish `hQ1 : Q.inertiaDeg ℤ = 1` using `Nat.eq_one_of_mul_eq_one_right htow.symm`.

Establish `hunder : Q.under ℤ = P.under ℤ` using `by rw [hQP, Ideal.under_under]`. Establish `e1` using `Ideal.absNorm_pow_inertiaDeg (P.under ℤ) P`. Establish `: Q.LiesOver (P.under ℤ)` using `⟨hunder.symm⟩`. Establish `e2` using `Ideal.absNorm_pow_inertiaDeg (P.under ℤ) Q`. Rewrite `e1` using `[h, pow_one]`.

Rewrite `e2` using `[hQ1, pow_one]`. Express the relevant statement in the definitionally equal form `Nat.card (𝓞 K ⧸ Q) = Nat.card (𝓞 L ⧸ P)`. Express the relevant statement in the definitionally equal form `Ideal.absNorm Q = Ideal.absNorm P`. Rewrite using `[← e1, ← e2]`.
-/
theorem normV_under_eq : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (w : HeightOneSpectrum (𝓞 L)), w.asIdeal.inertiaDeg ℤ = 1 → normV (w.under (𝓞 K)) = normV w := by
  intro K L _ _ _ _ _ w h
  classical
  set P := w.asIdeal with hP
  set Q := (w.under (𝓞 K)).asIdeal with hQ
  have hQP : Q = P.under (𝓞 K) := rfl
  have : P.IsPrime := w.isPrime
  have : Q.IsPrime := (w.under (𝓞 K)).isPrime
  have hlo : P.LiesOver Q := ⟨hQP⟩
  have htow := Ideal.inertiaDeg_tower (R := ℤ) Q P
  rw [h] at htow
  have hQ1 : Q.inertiaDeg ℤ = 1 := Nat.eq_one_of_mul_eq_one_right htow.symm
  have hunder : Q.under ℤ = P.under ℤ := by rw [hQP, Ideal.under_under]
  have e1 := Ideal.absNorm_pow_inertiaDeg (P.under ℤ) P
  have : Q.LiesOver (P.under ℤ) := ⟨hunder.symm⟩
  have e2 := Ideal.absNorm_pow_inertiaDeg (P.under ℤ) Q
  rw [h, pow_one] at e1
  rw [hQ1, pow_one] at e2
  change Nat.card (𝓞 K ⧸ Q) = Nat.card (𝓞 L ⧸ P)
  change Ideal.absNorm Q = Ideal.absNorm P
  rw [← e1, ← e2]

end GlobalTheory.NormDegOne
