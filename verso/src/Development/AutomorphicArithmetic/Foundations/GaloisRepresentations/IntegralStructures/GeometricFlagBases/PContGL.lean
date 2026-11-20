import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FlagBasis

open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

/- English proof (translation)
Introduce `Γ k _ _ _ _ _ _ d ρ`. Prove the components needed by the constructor for the conclusion. Introduce `hρ i j`. Conclude with `(Units.continuous_val.comp hρ).matrix_elem i j`. Introduce `h`.

Establish `hval : Continuous fun g : Γ => ((ρ g : GL (Fin d) k) : Matrix (Fin d) (Fin d) k)` using `continuous_matrix h`. Rewrite using `[Units.continuous_iff]`. Use `⟨hval, ?_⟩` and prove the remaining obligations. Establish `hinv : (fun g : Γ => (((ρ g)⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k)) = fun g => ((ρ g⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k)`. Use function extensionality and compare the values at `g`.

Rewrite using `[map_inv]`. Rewrite using `[hinv]`. Conclude with `hval.comp continuous_inv`.
-/
theorem UpperTheory.Gal.Int.Geo.contGL_of :
    ContGL := by
  intro Γ k _ _ _ _ _ _ d ρ
  constructor
  · intro hρ i j
    exact (Units.continuous_val.comp hρ).matrix_elem i j
  · intro h
    have hval : Continuous fun g : Γ => ((ρ g : GL (Fin d) k) : Matrix (Fin d) (Fin d) k) :=
      continuous_matrix h
    rw [Units.continuous_iff]
    refine ⟨hval, ?_⟩
    have hinv : (fun g : Γ => (((ρ g)⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k)) =
        fun g => ((ρ g⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k) := by
      funext g
      rw [map_inv]
    rw [hinv]
    exact hval.comp continuous_inv
