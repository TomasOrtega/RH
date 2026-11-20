import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.LiftFactorization

open MeasureTheory

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
private theorem cptConj_zpowers {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    (j : H →* G) (hj : Topology.IsClosedEmbedding j) (t : H) :
    IsCompact (closure (Subgroup.zpowers (j t) : Set G)) ↔ IsCompact (closure (Subgroup.zpowers t : Set H)) := by
  have h1 : (Subgroup.zpowers (j t) : Set G) = j '' (Subgroup.zpowers t : Set H) := by
    rw [← MonoidHom.map_zpowers, Subgroup.coe_map]
  rw [h1, hj.closure_image_eq, hj.isInducing.isCompact_iff]

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem cptConj_conj {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (c : G) :
    Topology.IsClosedEmbedding (MulAut.conj c).toMonoidHom := by
  have e : ⇑(MulAut.conj c).toMonoidHom = ⇑((Homeomorph.mulRight c⁻¹).trans (Homeomorph.mulLeft c)) := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [e]
  exact Homeomorph.isClosedEmbedding _

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem cptConj_map {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] (j : H →* G) (hj : Topology.IsClosedEmbedding j)
    (S : Subgroup G) (T : Subgroup H) (h : G) (hST : ∀ x, x ∈ S ↔ ∃ t ∈ T, h⁻¹ * x * h = j t) :
    (GlobalTheory.BCT.cptPart S).map (MulAut.conj h⁻¹).toMonoidHom = (GlobalTheory.BCT.cptPart T).map j := by
  have hc := cptConj_conj h⁻¹
  have key : ∀ x : G, (MulAut.conj h⁻¹).toMonoidHom x = h⁻¹ * x * h := by
    intro x
    simp [MulAut.conj_apply]
  unfold GlobalTheory.BCT.cptPart
  rw [MonoidHom.map_closure, MonoidHom.map_closure]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, ⟨hxS, hxc⟩, rfl⟩
    obtain ⟨t, htT, hxt⟩ := (hST x).mp hxS
    refine ⟨t, ⟨htT, ?_⟩, ?_⟩
    · rw [← cptConj_zpowers j hj, ← hxt, ← key, cptConj_zpowers _ hc]
      exact hxc
    · rw [key, hxt]
  · rintro ⟨t, ⟨htT, htc⟩, rfl⟩
    refine ⟨h * j t * h⁻¹, ⟨(hST _).mpr ⟨t, htT, by group⟩, ?_⟩, ?_⟩
    · rw [← cptConj_zpowers _ hc, key, show h⁻¹ * (h * j t * h⁻¹) * h = j t by group,
        cptConj_zpowers j hj]
      exact htc
    · rw [key]
      group

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Use the resulting assumption. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.InertialTypesAlt.L.cptConj :
    UpperTheory.Gal.InertialTypesAlt.L.CptConj := by
  intro G H _ _ _ _ _ _ _ _ _ _ _ _ j hj S T h hST hcpt μ ν hμν
  have hmap := cptConj_map j hj S T h hST
  have hCm : MeasurableSet (((GlobalTheory.BCT.cptPart T).map j : Subgroup G) : Set G) := by
    rw [Subgroup.coe_map]
    exact (hcpt.image hj.continuous).isClosed.measurableSet
  have hf : Measurable (fun x : S => h⁻¹ * (x : G) * h) :=
    ((continuous_const.mul continuous_id).mul continuous_const).measurable.comp measurable_subtype_coe
  have hg : Measurable (fun t : T => j (t : H)) := hj.continuous.measurable.comp measurable_subtype_coe
  have h1 : {x : S | (x : G) ∈ GlobalTheory.BCT.cptPart S} =
      (fun x : S => h⁻¹ * (x : G) * h) ⁻¹' (((GlobalTheory.BCT.cptPart T).map j : Subgroup G) : Set G) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe]
    rw [← hmap, Subgroup.mem_map]
    constructor
    · intro hx
      exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
    · rintro ⟨y, hy, hyx⟩
      have hyx' : y = (x : G) := by
        simpa [MulAut.conj_apply] using hyx
      rwa [← hyx']
  have h2 : {t : T | (t : H) ∈ GlobalTheory.BCT.cptPart T} =
      (fun t : T => j (t : H)) ⁻¹' (((GlobalTheory.BCT.cptPart T).map j : Subgroup G) : Set G) := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe]
    exact (Subgroup.mem_map_iff_mem hj.injective).symm
  simp only [Measure.real]
  rw [h1, h2, ← Measure.map_apply hf hCm, ← Measure.map_apply hg hCm, hμν]
