import ReciprocityTheory.GaloisValuations.Global
import ReciprocityTheory.Hypotheses.Descent

noncomputable section

open NumberField IsDedekindDomain Pointwise

namespace ReciprocityTheory.Gal

open Formalism.ConjugateSelfDual ReciprocityTheory.Hyp

section res

variable {F L Ω : Type*} [Field F] [Field L] [Field Ω] [Algebra F L] [Algebra F Ω] [Algebra L Ω]
  [IsScalarTower F L Ω]

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem resGal_apply (σ : G L Ω) (x : Ω) : resGal F L Ω σ x = σ x := rfl

/- English proof (translation)
Introduce `σ τ h` and use `AlgEquiv.ext fun x => by simpa using DFunLike.congr_fun h x`.
-/
theorem resGal_injective : Function.Injective (resGal F L Ω) := fun σ τ h =>
  AlgEquiv.ext fun x => by simpa using DFunLike.congr_fun h x

/- English proof (translation)
Use `continuous_of_continuousAt_one (resGal F L Ω) ?_` and prove the remaining obligations. Rewrite using `[ContinuousAt, map_one]`. Introduce `s hs`. Take `⟨E, hE, hEs⟩` from `(krullTopology_mem_nhds_one_iff F Ω s).1 hs`. Set `b` to `Module.finBasis F E`.

Set `S : Set Ω` to `Set.range (fun i => (b i : Ω))`. Establish `hint : ∀ x ∈ S, IsIntegral L x` using `fun x _ => (Algebra.IsIntegral.isIntegral (R := F) x).tower_top`. Establish `: FiniteDimensional L (IntermediateField.adjoin L S)` using `IntermediateField.finiteDimensional_adjoin hint`. Rewrite using `[Filter.mem_map, krullTopology_mem_nhds_one_iff]`. Use `⟨IntermediateField.adjoin L S, this, fun σ hσ => hEs ?_⟩` and prove the remaining obligations.

Rewrite `hσ`, the goal using `[SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]`. Establish `hb : ∀ i, σ (b i : Ω) = b i` using `fun i => hσ _ (IntermediateField.subset_adjoin L S ⟨i, rfl⟩)`. Introduce `x hx`. Establish `hx' : x = ((⟨x, hx⟩ : E) : Ω)` using `rfl`. Rewrite using `[hx', ← b.sum_repr ⟨x, hx⟩]`.

Simplify using `only [IntermediateField.coe_sum, IntermediateField.coe_smul]`. Express the relevant statement in the definitionally equal form `resGal F L Ω σ _ = _`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `σ (((b.repr ⟨x, hx⟩) i) • (b i : Ω)) = _`.

Rewrite using `[← algebraMap_smul L ((b.repr ⟨x, hx⟩) i) (b i : Ω), map_smul, hb]`.
-/
theorem continuous_resGal [Algebra.IsAlgebraic F Ω] : Continuous (resGal F L Ω) := by
  refine continuous_of_continuousAt_one (resGal F L Ω) ?_
  rw [ContinuousAt, map_one]
  intro s hs
  obtain ⟨E, hE, hEs⟩ := (krullTopology_mem_nhds_one_iff F Ω s).1 hs
  let b := Module.finBasis F E
  let S : Set Ω := Set.range (fun i => (b i : Ω))
  have hint : ∀ x ∈ S, IsIntegral L x := fun x _ =>
    (Algebra.IsIntegral.isIntegral (R := F) x).tower_top
  have : FiniteDimensional L (IntermediateField.adjoin L S) :=
    IntermediateField.finiteDimensional_adjoin hint
  rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
  refine ⟨IntermediateField.adjoin L S, this, fun σ hσ => hEs ?_⟩
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
  have hb : ∀ i, σ (b i : Ω) = b i := fun i =>
    hσ _ (IntermediateField.subset_adjoin L S ⟨i, rfl⟩)
  intro x hx
  have hx' : x = ((⟨x, hx⟩ : E) : Ω) := rfl
  rw [hx', ← b.sum_repr ⟨x, hx⟩]
  simp only [IntermediateField.coe_sum, IntermediateField.coe_smul]
  change resGal F L Ω σ _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  change σ (((b.repr ⟨x, hx⟩) i) • (b i : Ω)) = _
  rw [← algebraMap_smul L ((b.repr ⟨x, hx⟩) i) (b i : Ω), map_smul, hb]

/- English proof (translation)
Assemble the required witnesses or components as `⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.tower_top (K := F) L⟩`.
-/
theorem isAlgClosure_top [IsAlgClosure F Ω] : IsAlgClosure L Ω :=
  ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.tower_top (K := F) L⟩

/- English proof (translation)
Use `isAlgClosure_top (F := F) (L := L) (Ω := Ω)` as an intermediate fact. Establish `: T2Space (G F Ω)` using `krullTopology_t2`. Conclude with `continuous_resGal.isClosedEmbedding resGal_injective`.
-/
theorem isClosedEmbedding_resGal [IsAlgClosure F Ω] [CharZero L] :
    Topology.IsClosedEmbedding (resGal F L Ω) := by
  have := isAlgClosure_top (F := F) (L := L) (Ω := Ω)
  have : T2Space (G F Ω) := krullTopology_t2
  exact continuous_resGal.isClosedEmbedding resGal_injective

end res

section places

variable {F L Ω : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω] [Algebra F L]
  [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω]

variable (F) in

def belowV (w : HeightOneSpectrum (𝓞 L)) : HeightOneSpectrum (𝓞 F) where
  asIdeal := w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 L))
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
    exact Ideal.comap_ne_bot_of_integral_mem hy0 hy (Algebra.IsIntegral.isIntegral y)

end places

end ReciprocityTheory.Gal
