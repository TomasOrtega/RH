import Mathlib
import GroundTheory.AutomorphicForms.TensorProductTheorem.KFinite
import GroundTheory.AutomorphicForms.TensorProductTheorem.GenWindow

noncomputable section

namespace GroundTheory.Automorphic

namespace CompactRep

open Module Set RestrictedTensor

variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [T2Space K] {X : Type*} [AddCommGroup X] [Module ℂ X] {σ : Representation ℂ K X}

def kProj (hσ : IsKFinite σ) {c : Submodule (MonoidAlgebra ℂ K) σ.asModule}
    (hc : c ∈ isotypicComponents (MonoidAlgebra ℂ K) σ.asModule) : End ℂ X :=
  haveI := isSemisimpleModule_asModule hσ
  σ.asModuleEquiv.toLinearMap ∘ₗ (isoProj hc).restrictScalars ℂ ∘ₗ
    σ.asModuleEquiv.symm.toLinearMap

variable (hσ : IsKFinite σ) {c : Submodule (MonoidAlgebra ℂ K) σ.asModule}
  (hc : c ∈ isotypicComponents (MonoidAlgebra ℂ K) σ.asModule)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem kProj_apply_eq_self_iff {v : X} : kProj hσ hc v = v ↔ (v : σ.asModule) ∈ c := by
  haveI := isSemisimpleModule_asModule hσ
  constructor
  · intro h
    have : isoProj hc (v : σ.asModule) ∈ c := isoProj_mem_isotypicComponent hc _
    exact h ▸ this
  · intro h
    exact isoProj_apply_of_mem hc h

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kProj_mem_component (v : X) : (kProj hσ hc v : σ.asModule) ∈ c := by
  haveI := isSemisimpleModule_asModule hσ
  exact isoProj_mem_isotypicComponent hc _

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kProj_kProj (v : X) : kProj hσ hc (kProj hσ hc v) = kProj hσ hc v :=
  (kProj_apply_eq_self_iff hσ hc).2 (kProj_mem_component hσ hc v)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem kProj_σ (k : K) (v : X) : kProj hσ hc (σ k v) = σ k (kProj hσ hc v) := by
  haveI := isSemisimpleModule_asModule hσ
  show σ.asModuleEquiv (isoProj hc (σ.asModuleEquiv.symm (σ k v))) =
    σ k (σ.asModuleEquiv (isoProj hc (σ.asModuleEquiv.symm v)))
  rw [Representation.asModuleEquiv_symm_map_rho, map_smul, Representation.asModuleEquiv_map_smul,
    MonoidAlgebra.of_apply, Representation.asAlgebraHom_single_one]

/- English proof (translation)
Introduce a local definition for the expression. A detailed English derivation is pending.
-/
theorem kProj_comm {T : End ℂ X} (hT : ∀ k, T * σ k = σ k * T) (v : X) :
    kProj hσ hc (T v) = T (kProj hσ hc v) := by
  haveI := isSemisimpleModule_asModule hσ
  let f : Representation.IntertwiningMap σ σ := ⟨T, hT⟩
  exact isoProj_comm hc (Representation.IntertwiningMap.equivLinearMapAsModule σ σ f) v

/- English proof (translation)
Introduce a local definition for the expression. A detailed English derivation is pending.
-/
theorem kProj_mem {Y : Submodule ℂ X} (hY : ∀ k, ∀ y ∈ Y, σ k y ∈ Y) {y : X} (hy : y ∈ Y) :
    kProj hσ hc y ∈ Y := by
  haveI := isSemisimpleModule_asModule hσ
  let P : Subrepresentation σ := ⟨Y, fun k y hy => hY k y hy⟩
  exact isoProj_mem hc (Subrepresentation.subrepresentationSubmoduleOrderIso P) hy

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem isWinProj_kProj {M : Type*} [Monoid M] {ρ : Representation ℂ M X}
    (hsub : ∀ Y : Subrepresentation ρ, ∀ k, ∀ y ∈ Y.toSubmodule, σ k y ∈ Y.toSubmodule) :
    IsWinProj ρ (kProj hσ hc) :=
  ⟨kProj_kProj hσ hc, fun Y _ hy => kProj_mem hσ hc (hsub Y) hy⟩

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem exists_kProj_eq_self {Y : Submodule ℂ X} (hY : ∀ k, ∀ y ∈ Y, σ k y ∈ Y) (hY0 : Y ≠ ⊥) :
    ∃ (c : Submodule (MonoidAlgebra ℂ K) σ.asModule)
      (hc : c ∈ isotypicComponents (MonoidAlgebra ℂ K) σ.asModule),
      ∃ y ∈ Y, y ≠ 0 ∧ kProj hσ hc y = y := by
  haveI := isSemisimpleModule_asModule hσ
  let P : Subrepresentation σ := ⟨Y, fun k y hy => hY k y hy⟩
  set N := Subrepresentation.subrepresentationSubmoduleOrderIso P
  have hN0 : N ≠ ⊥ := by
    intro h
    apply hY0
    have : P = ⊥ := by
      have := congrArg (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := σ)).symm h
      rwa [OrderIso.symm_apply_apply, OrderIso.map_bot] at this
    have := congrArg Subrepresentation.toSubmodule this
    exact this
  obtain ⟨S, hSatom, hSN⟩ := (eq_bot_or_exists_atom_le N).resolve_left hN0
  have hS : IsSimpleModule (MonoidAlgebra ℂ K) S := (isSimpleModule_iff_isAtom).2 hSatom
  obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hSatom.1
  refine ⟨isotypicComponent (MonoidAlgebra ℂ K) σ.asModule S, ⟨S, hS, rfl⟩, s, hSN hs, hs0, ?_⟩
  exact (kProj_apply_eq_self_iff hσ _).2 (Submodule.le_isotypicComponent S hs)

end CompactRep

end GroundTheory.Automorphic
