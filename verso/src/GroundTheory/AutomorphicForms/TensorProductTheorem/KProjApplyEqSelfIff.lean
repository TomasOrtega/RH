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
Use `haveI := isSemisimpleModule_asModule hσ`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `: isoProj hc (v : σ.asModule) ∈ c` using `isoProj_mem_isotypicComponent hc _`. Conclude with `h ▸ this`.

Introduce `h`. Conclude with `isoProj_apply_of_mem hc h`.
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
Use `haveI := isSemisimpleModule_asModule hσ`. Conclude with `isoProj_mem_isotypicComponent hc _`.
-/
theorem kProj_mem_component (v : X) : (kProj hσ hc v : σ.asModule) ∈ c := by
  haveI := isSemisimpleModule_asModule hσ
  exact isoProj_mem_isotypicComponent hc _

/- English proof (translation)
The claim follows from `(kProj_apply_eq_self_iff hσ hc).2 (kProj_mem_component hσ hc v)`.
-/
theorem kProj_kProj (v : X) : kProj hσ hc (kProj hσ hc v) = kProj hσ hc v :=
  (kProj_apply_eq_self_iff hσ hc).2 (kProj_mem_component hσ hc v)

/- English proof (translation)
Use `haveI := isSemisimpleModule_asModule hσ`. Use `show σ.asModuleEquiv (isoProj hc (σ.asModuleEquiv.symm (σ k v))) = σ k (σ.asModuleEquiv (isoProj hc (σ.asModuleEquiv.symm v)))`. Rewrite using `[Representation.asModuleEquiv_symm_map_rho, map_smul, Representation.asModuleEquiv_map_smul, MonoidAlgebra.of_apply, Representation.asAlgebraHom_single_one]`.
-/
theorem kProj_σ (k : K) (v : X) : kProj hσ hc (σ k v) = σ k (kProj hσ hc v) := by
  haveI := isSemisimpleModule_asModule hσ
  show σ.asModuleEquiv (isoProj hc (σ.asModuleEquiv.symm (σ k v))) =
    σ k (σ.asModuleEquiv (isoProj hc (σ.asModuleEquiv.symm v)))
  rw [Representation.asModuleEquiv_symm_map_rho, map_smul, Representation.asModuleEquiv_map_smul,
    MonoidAlgebra.of_apply, Representation.asAlgebraHom_single_one]

/- English proof (translation)
Use `haveI := isSemisimpleModule_asModule hσ`. Set `f : Representation.IntertwiningMap σ σ` to `⟨T, hT⟩`. Conclude with `isoProj_comm hc (Representation.IntertwiningMap.equivLinearMapAsModule σ σ f) v`.
-/
theorem kProj_comm {T : End ℂ X} (hT : ∀ k, T * σ k = σ k * T) (v : X) :
    kProj hσ hc (T v) = T (kProj hσ hc v) := by
  haveI := isSemisimpleModule_asModule hσ
  let f : Representation.IntertwiningMap σ σ := ⟨T, hT⟩
  exact isoProj_comm hc (Representation.IntertwiningMap.equivLinearMapAsModule σ σ f) v

/- English proof (translation)
Use `haveI := isSemisimpleModule_asModule hσ`. Set `P : Subrepresentation σ` to `⟨Y, fun k y hy => hY k y hy⟩`. Conclude with `isoProj_mem hc (Subrepresentation.subrepresentationSubmoduleOrderIso P) hy`.
-/
theorem kProj_mem {Y : Submodule ℂ X} (hY : ∀ k, ∀ y ∈ Y, σ k y ∈ Y) {y : X} (hy : y ∈ Y) :
    kProj hσ hc y ∈ Y := by
  haveI := isSemisimpleModule_asModule hσ
  let P : Subrepresentation σ := ⟨Y, fun k y hy => hY k y hy⟩
  exact isoProj_mem hc (Subrepresentation.subrepresentationSubmoduleOrderIso P) hy

/- English proof (translation)
Assemble the required witnesses or components as `⟨kProj_kProj hσ hc, fun Y _ hy => kProj_mem hσ hc (hsub Y) hy⟩`.
-/
theorem isWinProj_kProj {M : Type*} [Monoid M] {ρ : Representation ℂ M X}
    (hsub : ∀ Y : Subrepresentation ρ, ∀ k, ∀ y ∈ Y.toSubmodule, σ k y ∈ Y.toSubmodule) :
    IsWinProj ρ (kProj hσ hc) :=
  ⟨kProj_kProj hσ hc, fun Y _ hy => kProj_mem hσ hc (hsub Y) hy⟩

/- English proof (translation)
Use `haveI := isSemisimpleModule_asModule hσ`. Set `P : Subrepresentation σ` to `⟨Y, fun k y hy => hY k y hy⟩`. Use `set N := Subrepresentation.subrepresentationSubmoduleOrderIso P`. Establish `hN0 : N ≠ ⊥`. Introduce `h`.

Apply `hY0` to reduce the goal to its premises. Establish `: P = ⊥`. Use `congrArg (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := σ)).symm h` as an intermediate fact. Rewrite `this` using `[OrderIso.symm_apply_apply, OrderIso.map_bot]`. Then use the resulting hypothesis. Use `congrArg Subrepresentation.toSubmodule this` as an intermediate fact.

Conclude with `this`. Take `⟨S, hSatom, hSN⟩` from `(eq_bot_or_exists_atom_le N).resolve_left hN0`. Establish `hS : IsSimpleModule (MonoidAlgebra ℂ K) S` using `(isSimpleModule_iff_isAtom).2 hSatom`. Take `⟨s, hs, hs0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hSatom.1`. Use `⟨isotypicComponent (MonoidAlgebra ℂ K) σ.asModule S, ⟨S, hS, rfl⟩, s, hSN hs, hs0, ?_⟩` and prove the remaining obligations.

Conclude with `(kProj_apply_eq_self_iff hσ _).2 (Submodule.le_isotypicComponent S hs)`.
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
