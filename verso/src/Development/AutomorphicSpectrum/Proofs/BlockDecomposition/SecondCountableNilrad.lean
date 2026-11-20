import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousConjNilSymm

noncomputable section

open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.LocVan

variable {n : ℕ}

/- English proof (translation)
Use `haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))`. Conclude with `Units.isClosedEmbedding_embedProduct.locallyCompactSpace`.
-/
theorem locallyCompact_GL (n : ℕ) : LocallyCompactSpace (GL (Fin n) ℂ) := by
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

/- English proof (translation)
Use `haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))`. Use `haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology`. Conclude with `Units.isEmbedding_embedProduct.secondCountableTopology`.
-/
theorem secondCountable_GL (n : ℕ) : SecondCountableTopology (GL (Fin n) ℂ) := by
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

/- English proof (translation)
Use `haveI : FiniteDimensional ℂ (Matrix (Fin n) (Fin n) ℂ) := inferInstance`. Use `letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedAddCommGroup`. Use `letI : NormedSpace ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedSpace`. Conclude with `Submodule.closed_of_finiteDimensional (nilrad W₁ W₂)`.
-/
theorem isClosed_nilrad (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) :
    IsClosed (nilrad W₁ W₂ : Set (Matrix (Fin n) (Fin n) ℂ)) := by
  haveI : FiniteDimensional ℂ (Matrix (Fin n) (Fin n) ℂ) := inferInstance
  letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedAddCommGroup
  letI : NormedSpace ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedSpace
  exact Submodule.closed_of_finiteDimensional (nilrad W₁ W₂)

/- English proof (translation)
Use `haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))`. Conclude with `(isClosed_nilrad W₁ W₂).isClosedEmbedding_subtypeVal.locallyCompactSpace`.
-/
theorem locallyCompact_nilrad (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) :
    LocallyCompactSpace (nilrad W₁ W₂) := by
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  exact (isClosed_nilrad W₁ W₂).isClosedEmbedding_subtypeVal.locallyCompactSpace

/- English proof (translation)
Use `haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))`. Conclude with `TopologicalSpace.Subtype.secondCountableTopology _`.
-/
theorem secondCountable_nilrad (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) :
    SecondCountableTopology (nilrad W₁ W₂) := by
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  exact TopologicalSpace.Subtype.secondCountableTopology _

/- English proof (translation)
Use `⟨fun y => ?_, fun y hy => ?_, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.mulVec_mulVec]`. Conclude with `hW (hX.2.1 _ (hY.1 y))`. Rewrite using `[← Matrix.mulVec_mulVec, hX.2.2 _ (hY.2.1 y hy)]`. Conclude with `W₁.zero_mem`.

Rewrite using `[← Matrix.mulVec_mulVec, hY.2.2 y hy, Matrix.mulVec_zero]`.
-/
theorem nil_mul_mem {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (hW : W₁ ≤ W₂)
    {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ nilrad W₁ W₂) (hY : Y ∈ nilrad W₁ W₂) :
    X * Y ∈ nilrad W₁ W₂ := by
  refine ⟨fun y => ?_, fun y hy => ?_, fun y hy => ?_⟩
  · rw [← Matrix.mulVec_mulVec]; exact hW (hX.2.1 _ (hY.1 y))
  · rw [← Matrix.mulVec_mulVec, hX.2.2 _ (hY.2.1 y hy)]; exact W₁.zero_mem
  · rw [← Matrix.mulVec_mulVec, hY.2.2 y hy, Matrix.mulVec_zero]

def nmul {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (hW : W₁ ≤ W₂) (Y X : nilrad W₁ W₂) : nilrad W₁ W₂ :=
  ⟨Y.1 + X.1 + Y.1 * X.1, (nilrad W₁ W₂).add_mem ((nilrad W₁ W₂).add_mem Y.2 X.2) (nil_mul_mem hW Y.2 X.2)⟩

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [uOf_val, Units.val_mul, nmul]`. Use `noncomm_ring`.
-/
theorem uOf_nmul {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (hW : W₁ ≤ W₂) (Y X : nilrad W₁ W₂) :
    uOf (nmul hW Y X) = uOf Y * uOf X := by
  apply Units.ext
  simp only [uOf_val, Units.val_mul, nmul]
  noncomm_ring

def ninv {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (hW : W₁ ≤ W₂) (X : nilrad W₁ W₂) : nilrad W₁ W₂ :=
  ⟨-X.1 + X.1 * X.1, (nilrad W₁ W₂).add_mem ((nilrad W₁ W₂).neg_mem X.2) (nil_mul_mem hW X.2 X.2)⟩

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[uOf_val, ninv]`. Express the relevant statement in the definitionally equal form `_ = 1 - X.1 + X.1 * X.1`. Use `noncomm_ring`.
-/
theorem uOf_ninv {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (hW : W₁ ≤ W₂) (X : nilrad W₁ W₂) :
    uOf (ninv hW X) = (uOf X)⁻¹ := by
  apply Units.ext
  rw [uOf_val, ninv]
  change _ = 1 - X.1 + X.1 * X.1
  noncomm_ring

def nSet (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (C : Set (GL (Fin n) ℂ)) : Set (GL (Fin n) ℂ) :=
  {g | ∃ X : nilrad W₁ W₂, ∃ c ∈ C, uOf X * c = g}

/- English proof (translation)
Use `haveI := locallyCompact_GL n`. Use `haveI := secondCountable_GL n`. Use `haveI : SigmaCompactSpace (GL (Fin n) ℂ) := inferInstance`. Set `K` to `CompactExhaustion.choice (GL (Fin n) ℂ)`. Use `⟨fun i => interior (K i), fun i => isOpen_interior, fun i => ?_, fun g => ?_⟩` and prove the remaining obligations.

Conclude with `(K.isCompact i).of_isClosed_subset isClosed_closure (closure_minimal interior_subset (K.isCompact i).isClosed)`. Take `⟨i, hi⟩` from `K.exists_mem g`. Conclude with `⟨i + 1, K.subset_interior_succ i hi⟩`.
-/
theorem exists_open_cover (n : ℕ) : ∃ U : ℕ → Set (GL (Fin n) ℂ),
    (∀ i, IsOpen (U i)) ∧ (∀ i, IsCompact (closure (U i))) ∧ ∀ g, ∃ i, g ∈ U i := by
  haveI := locallyCompact_GL n
  haveI := secondCountable_GL n
  haveI : SigmaCompactSpace (GL (Fin n) ℂ) := inferInstance
  let K := CompactExhaustion.choice (GL (Fin n) ℂ)
  refine ⟨fun i => interior (K i), fun i => isOpen_interior, fun i => ?_, fun g => ?_⟩
  · exact (K.isCompact i).of_isClosed_subset isClosed_closure
      (closure_minimal interior_subset (K.isCompact i).isClosed)
  · obtain ⟨i, hi⟩ := K.exists_mem g
    exact ⟨i + 1, K.subset_interior_succ i hi⟩

/- English proof (translation)
Establish `h : Continuous fun g : GL (Fin n) ℂ => g⁻¹ * d * thC n g` using `(continuous_inv.mul continuous_const).mul continuous_thC`. Conclude with `isClosed_eq h continuous_const`.
-/
theorem isClosed_twCent (d : GL (Fin n) ℂ) :
    IsClosed (twCent (thC n) d : Set (GL (Fin n) ℂ)) := by
  have h : Continuous fun g : GL (Fin n) ℂ => g⁻¹ * d * thC n g :=
    (continuous_inv.mul continuous_const).mul continuous_thC
  exact isClosed_eq h continuous_const

/- English proof (translation)
Use `haveI := locallyCompact_GL n`. Conclude with `(isClosed_twCent d).isClosedEmbedding_subtypeVal.locallyCompactSpace`.
-/
theorem locallyCompact_twCent (d : GL (Fin n) ℂ) : LocallyCompactSpace (twCent (thC n) d) := by
  haveI := locallyCompact_GL n
  exact (isClosed_twCent d).isClosedEmbedding_subtypeVal.locallyCompactSpace

/- English proof (translation)
Use `haveI := locallyCompact_twCent d`. Use `haveI := secondCountable_GL n`. Use `haveI : SecondCountableTopology (twCent (thC n) d) := TopologicalSpace.Subtype.secondCountableTopology _`. Use `infer_instance`.
-/
theorem sigmaFinite_twCent [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)]
    (d : GL (Fin n) ℂ) (μd : Measure (twCent (thC n) d)) [μd.IsHaarMeasure] : SigmaFinite μd := by
  haveI := locallyCompact_twCent d
  haveI := secondCountable_GL n
  haveI : SecondCountableTopology (twCent (thC n) d) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  infer_instance

/- English proof (translation)
Use `haveI := locallyCompact_twCent d`. Use `haveI := secondCountable_GL n`. Use `letI : CommGroup (twCent (thC n) d) := { (inferInstance : Group (twCent (thC n) d)) with mul_comm := fun a b => Subtype.ext (hc a a.2 b b.2) }`. Use `haveI : SecondCountableTopology (twCent (thC n) d) := TopologicalSpace.Subtype.secondCountableTopology _`. Conclude with `Measure.IsHaarMeasure.isInvInvariant_of_regular μd`.
-/
theorem invInvariant_twCent [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)]
    (d : GL (Fin n) ℂ) (μd : Measure (twCent (thC n) d)) [μd.IsHaarMeasure]
    (hc : ∀ a ∈ twCent (thC n) d, ∀ b ∈ twCent (thC n) d, a * b = b * a) : μd.IsInvInvariant := by
  haveI := locallyCompact_twCent d
  haveI := secondCountable_GL n
  letI : CommGroup (twCent (thC n) d) :=
    { (inferInstance : Group (twCent (thC n) d)) with
      mul_comm := fun a b => Subtype.ext (hc a a.2 b b.2) }
  haveI : SecondCountableTopology (twCent (thC n) d) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  exact Measure.IsHaarMeasure.isInvInvariant_of_regular μd

end GlobalTheory.CompanionTheory.LocVan
end
