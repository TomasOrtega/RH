import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar Formalism.BasicNotions GlobalTheory.TrueGeo

namespace GlobalTheory

/- English proof (translation)
Introduce `X _ V hV hne M hM`. Establish `hMd : Dense M`. Rewrite using `[dense_iff_closure_eq, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]`. Establish `: PrimeSpectrum.vanishingIdeal M = ⊥`. Rewrite using `[← hM]`.

Apply `le_antisymm` to reduce the goal to its premises. Introduce `f hf`. Rewrite using `[Submodule.mem_sInf]`. Introduce and unpack `_ ⟨p, hp, rfl⟩`. Conclude with `(PrimeSpectrum.mem_vanishingIdeal M f).1 hf p hp`.

Introduce `f hf`. Rewrite using `[PrimeSpectrum.mem_vanishingIdeal]`. Introduce `p hp`. Rewrite `hf` using `[Submodule.mem_sInf]`. Conclude with `hf _ ⟨p, hp, rfl⟩`.

Rewrite using `[this, PrimeSpectrum.zeroLocus_bot]`. Establish `hr : DenseRange hV.fromSpec`. Establish `h1 : Set.range hV.fromSpec = (V : Set X)` using `hV.range_fromSpec`. Unfold `DenseRange`. Rewrite using `[h1]`.

Conclude with `V.2.dense hne`. Conclude with `hr.dense_image hV.fromSpec.continuous hMd`.
-/
theorem dense_fromSpec_image_of_sInf_asIdeal_eq_bot :
    ∀ (X : Scheme.{0}) [IsIntegral X] (V : X.Opens) (hV : IsAffineOpen V), (V : Set X).Nonempty →
    ∀ (M : Set (PrimeSpectrum Γ(X, V))), sInf (PrimeSpectrum.asIdeal '' M) = ⊥ → Dense (hV.fromSpec '' M) := by
  intro X _ V hV hne M hM
  have hMd : Dense M := by
    rw [dense_iff_closure_eq, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    have : PrimeSpectrum.vanishingIdeal M = ⊥ := by
      rw [← hM]
      apply le_antisymm
      · intro f hf
        rw [Submodule.mem_sInf]
        rintro _ ⟨p, hp, rfl⟩
        exact (PrimeSpectrum.mem_vanishingIdeal M f).1 hf p hp
      · intro f hf
        rw [PrimeSpectrum.mem_vanishingIdeal]
        intro p hp
        rw [Submodule.mem_sInf] at hf
        exact hf _ ⟨p, hp, rfl⟩
    rw [this, PrimeSpectrum.zeroLocus_bot]
  have hr : DenseRange hV.fromSpec := by
    have h1 : Set.range hV.fromSpec = (V : Set X) := hV.range_fromSpec
    unfold DenseRange
    rw [h1]
    exact V.2.dense hne
  exact hr.dense_image hV.fromSpec.continuous hMd

end GlobalTheory
