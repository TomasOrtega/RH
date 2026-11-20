import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Divisors.PreUMono
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureCohomologyFlatBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

/- English proof (translation)
Introduce `K L _ _ _ A _ B _ φ hpb hA g hfin hrank`. Use `haveI := hA.proper`. Take `⟨⟨e, -⟩, -⟩` from `flat_baseChange_HO K L A.left B.left A.hom B.hom φ hpb.1 inferInstance inferInstance`. Use `haveI : Module.Finite L (L ⊗[K] HO1 A.hom) := Module.Finite.equiv e.symm`. Establish `hr : Module.rank L (L ⊗[K] HO1 A.hom) = Cardinal.lift (Module.rank K (HO1 A.hom))` using `Module.rank_baseChange`.

Establish `hfinA : Module.Finite K (HO1 A.hom)`. Rewrite using `[← Module.rank_lt_aleph0_iff]`. Establish `h1 : Module.rank L (L ⊗[K] HO1 A.hom) < Cardinal.aleph0` using `Module.rank_lt_aleph0 L _`. Rewrite `h1` using `[hr]`. Simplify using `using h1`.

Use `⟨hfinA, ?_⟩` and prove the remaining obligations. Rewrite using `[← hrank, ← e.finrank_eq, Module.finrank_baseChange]`.
-/
theorem finrank_HO1_descend_field : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (A : Over (Sp K)) [GrpObj A] (B : Over (Sp L)) [GrpObj B] (φ : B.left ⟶ A.left), IsGrpPullback B A (spMap (algebraMap K L)) φ → IsAbelianScheme A → ∀ g : ℕ, Module.Finite L (HO1 B.hom) → Module.finrank L (HO1 B.hom) = g → Module.Finite K (HO1 A.hom) ∧ Module.finrank K (HO1 A.hom) = g := by
  intro K L _ _ _ A _ B _ φ hpb hA g hfin hrank
  haveI := hA.proper
  obtain ⟨⟨e, -⟩, -⟩ := flat_baseChange_HO K L A.left B.left A.hom B.hom φ hpb.1 inferInstance inferInstance
  haveI : Module.Finite L (L ⊗[K] HO1 A.hom) := Module.Finite.equiv e.symm
  have hr : Module.rank L (L ⊗[K] HO1 A.hom) = Cardinal.lift (Module.rank K (HO1 A.hom)) :=
    Module.rank_baseChange
  have hfinA : Module.Finite K (HO1 A.hom) := by
    rw [← Module.rank_lt_aleph0_iff]
    have h1 : Module.rank L (L ⊗[K] HO1 A.hom) < Cardinal.aleph0 := Module.rank_lt_aleph0 L _
    rw [hr] at h1
    simpa using h1
  refine ⟨hfinA, ?_⟩
  rw [← hrank, ← e.finrank_eq, Module.finrank_baseChange]

end GlobalTheory.AbCoh
