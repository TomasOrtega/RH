import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FlagBasis

open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

/- English proof (translation)
Introduce `h l _ k Ω _ _ _ _ X p hqc hqs n i x m`. Take `⟨L, hL, z, hz⟩` from `h (l ^ m) k Ω p hqc hqs n i (x.1 m)`. Establish `fix : ∀ τ ∈ L.fixingSubgroup, GlobalTheory.EtC.pull (ZMod (l ^ m)) (sch.map (galMap Ω p τ)) (tw (l ^ m) i) n (x.1 m) = x.1 m`. Introduce `τ hτ`. Rewrite using `[← hz, ← GlobalTheory.EtC.pull_comp, ← Functor.map_comp, LateralTheory.EWeil.StabPf.galMap_proj L p τ hτ]`.

Rewrite using `[isOpen_iff_forall_mem_open]`. Introduce `σ hσ`. Use `⟨(fun g => g * σ⁻¹) ⁻¹' (L.fixingSubgroup : Set _), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `g hg`. Establish `hg' : g * σ⁻¹ ∈ L.fixingSubgroup` using `hg`.

Establish `e : g = (g * σ⁻¹) * σ` using `by group`. Use `show ((galHl l Ω p n i g) x).1 m = x.1 m`. Rewrite using `[e, map_mul, Module.End.mul_apply]`. Express the relevant statement in the definitionally equal form `GlobalTheory.EtC.pull (ZMod (l ^ m)) (sch.map (galMap Ω p (g * σ⁻¹))) (tw (l ^ m) i) n (((galHl l Ω p n i σ) x).1 m) = x.1 m`. Establish `hσ' : ((galHl l Ω p n i σ) x).1 m = x.1 m` using `hσ`.

Rewrite using `[hσ']`. Conclude with `fix _ hg'`. Conclude with `(IntermediateField.fixingSubgroup_isOpen L).preimage (continuous_mul_right σ⁻¹)`. Use `show σ * σ⁻¹ ∈ L.fixingSubgroup`. Rewrite using `[mul_inv_cancel]`.

Conclude with `one_mem _`.
-/
theorem UpperTheory.Gal.Int.Geo.stabOpen_of :
    HtDesc → StabOpen := by
  intro h l _ k Ω _ _ _ _ X p hqc hqs n i x m
  obtain ⟨L, hL, z, hz⟩ := h (l ^ m) k Ω p hqc hqs n i (x.1 m)
  have fix : ∀ τ ∈ L.fixingSubgroup,
      GlobalTheory.EtC.pull (ZMod (l ^ m)) (sch.map (galMap Ω p τ)) (tw (l ^ m) i) n (x.1 m) = x.1 m := by
    intro τ hτ
    rw [← hz, ← GlobalTheory.EtC.pull_comp, ← Functor.map_comp, LateralTheory.EWeil.StabPf.galMap_proj L p τ hτ]
  rw [isOpen_iff_forall_mem_open]
  intro σ hσ
  refine ⟨(fun g => g * σ⁻¹) ⁻¹' (L.fixingSubgroup : Set _), ?_, ?_, ?_⟩
  · intro g hg
    have hg' : g * σ⁻¹ ∈ L.fixingSubgroup := hg
    have e : g = (g * σ⁻¹) * σ := by group
    show ((galHl l Ω p n i g) x).1 m = x.1 m
    rw [e, map_mul, Module.End.mul_apply]
    change GlobalTheory.EtC.pull (ZMod (l ^ m)) (sch.map (galMap Ω p (g * σ⁻¹))) (tw (l ^ m) i) n
      (((galHl l Ω p n i σ) x).1 m) = x.1 m
    have hσ' : ((galHl l Ω p n i σ) x).1 m = x.1 m := hσ
    rw [hσ']
    exact fix _ hg'
  · exact (IntermediateField.fixingSubgroup_isOpen L).preimage (continuous_mul_right σ⁻¹)
  · show σ * σ⁻¹ ∈ L.fixingSubgroup
    rw [mul_inv_cancel]
    exact one_mem _
