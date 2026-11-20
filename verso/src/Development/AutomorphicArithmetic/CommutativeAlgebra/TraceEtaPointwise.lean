import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo

/- English proof (translation)
Introduce `p _ D G L R _ _ gb h X s N' N o' o ψ hT Ω _ _ z x`. Take `⟨-, -, -, -, hgeo⟩` from `hT`. Establish `hz : z ≫ s = spMap (Spec.preimage (z ≫ s)).hom`. Simplify using `[spMap, Spec.map_preimage]`. Take `⟨I', I'', h1, h2, h3⟩` from `hgeo Ω z _ hz`.

Establish `hpos : ∀ M : Lv p, 0 < (M : ℕ)` using `fun M => by`. Use `M.2.1` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hzero : ∀ n : ℕ, I''.ev n 0 = 1` using `fun n => by`. Establish `h` using `I''.add n 0 0`.

Rewrite `h` using `[add_zero]`. Conclude with `(mul_eq_left.mp h.symm)`. Establish `hin0 : inAf D 0 = 0`. Simplify using `[inAf]`. Establish `e1` using `congrArg (· ≫ ψ) (h1 x)`.

Simplify using `only [Category.assoc] at e1`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `Iff.trans ?_ ((h3 _ (hpos N') N'.2.2 x 0).trans ?_)` and prove the remaining obligations. Rewrite using `[e1] first`. Consider the case `simp only [hzero]`.

Consider the case `erw [hzero]`. Simplify using `only [hin0, zero_add]`. Introduce and unpack `rfl y hxy`. Use `(h3 _ (hpos N') N'.2.2 x y).mp ?_` and prove the remaining obligations. Rewrite using `[← e1, hxy]`.

Conclude with `h2 y`.
-/
theorem UpperTheory.trace_eta_pointwise : TrEtaPt := by
  intro p _ D G L R _ _ gb h X s N' N o' o ψ hT Ω _ _ z x
  obtain ⟨-, -, -, -, hgeo⟩ := hT
  have hz : z ≫ s = spMap (Spec.preimage (z ≫ s)).hom := by
    simp [spMap, Spec.map_preimage]
  obtain ⟨I', I'', h1, h2, h3⟩ := hgeo Ω z _ hz
  have hpos : ∀ M : Lv p, 0 < (M : ℕ) := fun M => by
    have := M.2.1
    omega
  have hzero : ∀ n : ℕ, I''.ev n 0 = 1 := fun n => by
    have h := I''.add n 0 0
    rw [add_zero] at h
    exact (mul_eq_left.mp h.symm)
  have hin0 : inAf D 0 = 0 := by
    simp [inAf]
  have e1 := congrArg (· ≫ ψ) (h1 x)
  simp only [Category.assoc] at e1
  refine ⟨?_, ?_⟩
  · refine Iff.trans ?_ ((h3 _ (hpos N') N'.2.2 x 0).trans ?_)
    · rw [e1]
      first
        | simp only [hzero]
        | erw [hzero]
    · simp only [hin0, zero_add]
  · rintro rfl y hxy
    refine (h3 _ (hpos N') N'.2.2 x y).mp ?_
    rw [← e1, hxy]
    exact h2 y
