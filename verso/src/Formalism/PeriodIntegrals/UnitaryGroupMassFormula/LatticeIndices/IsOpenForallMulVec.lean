import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LatOpenCompact

noncomputable section

namespace MassDataIdxK

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain Topology
open scoped Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : ℕ} (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Use `fdFE (F := F) (E := E)` as an intermediate fact. Use `MassDataIdxSteps.tens_topRing (F := F) (E := E) v` as an intermediate fact. Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `A0 hA0`. Conclude with `hΛ.eventually_forall_of_forall_eventually fun y hy => (continuous_fst.matrix_mulVec continuous_snd).continuousAt.preimage_mem_nhds (hU.mem_nhds (hA0 y hy))`.
-/
theorem isOpen_forall_mulVec {Λ U : Set (Fin n → Fv F v ⊗[F] E)} (hΛ : IsCompact Λ) (hU : IsOpen U) :
    IsOpen {A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) | ∀ y ∈ Λ, A *ᵥ y ∈ U} := by
  have := fdFE (F := F) (E := E)
  have := MassDataIdxSteps.tens_topRing (F := F) (E := E) v
  rw [isOpen_iff_mem_nhds]
  intro A0 hA0
  exact hΛ.eventually_forall_of_forall_eventually fun y hy =>
    (continuous_fst.matrix_mulVec continuous_snd).continuousAt.preimage_mem_nhds (hU.mem_nhds (hA0 y hy))

/- English proof (translation)
Use `fdFE (F := F) (E := E)` as an intermediate fact. Use `MassDataIdxSteps.tens_topRing (F := F) (E := E) v` as an intermediate fact. Use `set Λ : Set (Fin n → Fv F v ⊗[F] E) := (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) with hΛ`. Take `⟨m, b, hbΛ, hsp, -⟩` from `latImage v L hL hfg`. Take `⟨hΛo, hΛc⟩` from `latOpenCompact v L hL hfg`.

Establish `hΛcl : IsClosed Λ` using `AddSubgroup.isClosed_of_isOpen (latLoc (E := E) v (L : Set (Fin n → E))).toAddSubgroup hΛo`. Establish `hclosed : IsClosed {A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) | ∀ y ∈ Λ, A *ᵥ y ∈ Λ}`. Establish `: {A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) | ∀ y ∈ Λ, A *ᵥ y ∈ Λ} = ⋂ y ∈ Λ, (fun A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) => A *ᵥ y) ⁻¹' Λ`. Use extensionality with `A`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Conclude with `isClosed_biInter fun y _ => hΛcl.preimage (continuous_id.matrix_mulVec continuous_const)`. Set `Ψ : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) →ₗ[Fv F v] (Fin m → Fin n → Fv F v ⊗[F] E)` to `{ toFun := fun A i => A *ᵥ b i map_add' := fun A B => by funext i; exact Matrix.add_mulVec A B (b i) map_smul' := fun r A => by`. Use function extensionality and compare the values at `i j`. Simplify using `[Matrix.mulVec, dotProduct, Finset.smul_sum, smul_mul_assoc] }`.

Establish `hinj : LinearMap.ker Ψ = ⊥`. Rewrite using `[LinearMap.ker_eq_bot']`. Introduce `A hA`. Set `Al : (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v] (Fin n → Fv F v ⊗[F] E)` to `{ toFun := fun x => A *ᵥ x map_add' := Matrix.mulVec_add A map_smul' := fun r x => Matrix.mulVec_smul A r x }`. Establish `hAl : Al = 0` using `LinearMap.ext_on_range hsp (fun i => congrFun hA i)`.

Use extensionality with `i j`. Use `congrFun (LinearMap.congr_fun hAl (Pi.single j 1)) i` as an intermediate fact. Simplify `this` using `[Al, Matrix.mulVec_single_one]`. Take `⟨Ψ', hΨ'⟩` from `LinearMap.exists_leftInverse_of_injective Ψ hinj`. Establish `hc : Continuous Ψ'` using `IsModuleTopology.continuous_of_linearMap Ψ'`.

Establish `hsub : {A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) | ∀ y ∈ Λ, A *ᵥ y ∈ Λ} ⊆ Ψ' '' Set.pi Set.univ (fun _ => Λ)`. Introduce `A hA`. Conclude with `⟨Ψ A, fun i _ => hA _ (hbΛ i), by rw [← LinearMap.comp_apply, hΨ', LinearMap.id_apply]⟩`. Conclude with `((isCompact_univ_pi fun _ => hΛc).image hc).of_isClosed_subset hclosed hsub`.
-/
theorem isCompact_stab (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (hfg : L.FG) :
    IsCompact {A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) | ∀ y ∈ (latLoc (E := E) v (L : Set (Fin n → E)) :
      Set (Fin n → Fv F v ⊗[F] E)), A *ᵥ y ∈ (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E))} := by
  have := fdFE (F := F) (E := E)
  have := MassDataIdxSteps.tens_topRing (F := F) (E := E) v
  set Λ : Set (Fin n → Fv F v ⊗[F] E) := (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) with hΛ
  obtain ⟨m, b, hbΛ, hsp, -⟩ := latImage v L hL hfg
  obtain ⟨hΛo, hΛc⟩ := latOpenCompact v L hL hfg
  have hΛcl : IsClosed Λ :=
    AddSubgroup.isClosed_of_isOpen (latLoc (E := E) v (L : Set (Fin n → E))).toAddSubgroup hΛo
  have hclosed : IsClosed {A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) | ∀ y ∈ Λ, A *ᵥ y ∈ Λ} := by
    have : {A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) | ∀ y ∈ Λ, A *ᵥ y ∈ Λ} =
        ⋂ y ∈ Λ, (fun A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) => A *ᵥ y) ⁻¹' Λ := by
      ext A; simp
    rw [this]
    exact isClosed_biInter fun y _ => hΛcl.preimage (continuous_id.matrix_mulVec continuous_const)
  let Ψ : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) →ₗ[Fv F v] (Fin m → Fin n → Fv F v ⊗[F] E) :=
    { toFun := fun A i => A *ᵥ b i
      map_add' := fun A B => by funext i; exact Matrix.add_mulVec A B (b i)
      map_smul' := fun r A => by
        funext i j
        simp [Matrix.mulVec, dotProduct, Finset.smul_sum, smul_mul_assoc] }
  have hinj : LinearMap.ker Ψ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro A hA
    let Al : (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v] (Fin n → Fv F v ⊗[F] E) :=
      { toFun := fun x => A *ᵥ x
        map_add' := Matrix.mulVec_add A
        map_smul' := fun r x => Matrix.mulVec_smul A r x }
    have hAl : Al = 0 := LinearMap.ext_on_range hsp (fun i => congrFun hA i)
    ext i j
    have := congrFun (LinearMap.congr_fun hAl (Pi.single j 1)) i
    simpa [Al, Matrix.mulVec_single_one] using this
  obtain ⟨Ψ', hΨ'⟩ := LinearMap.exists_leftInverse_of_injective Ψ hinj
  have hc : Continuous Ψ' := IsModuleTopology.continuous_of_linearMap Ψ'
  have hsub : {A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) | ∀ y ∈ Λ, A *ᵥ y ∈ Λ} ⊆
      Ψ' '' Set.pi Set.univ (fun _ => Λ) := by
    intro A hA
    exact ⟨Ψ A, fun i _ => hA _ (hbΛ i), by rw [← LinearMap.comp_apply, hΨ', LinearMap.id_apply]⟩
  exact ((isCompact_univ_pi fun _ => hΛc).image hc).of_isClosed_subset hclosed hsub

/- English proof (translation)
Use `fdFE (F := F) (E := E)` as an intermediate fact. Use `MassDataIdxSteps.tens_topRing (F := F) (E := E) v` as an intermediate fact. Use `t2Space_scalarTensorExt (F := F) (E := E) v` as an intermediate fact. Use `set Λ : Set (Fin n → Fv F v ⊗[F] E) := (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) with hΛ`. Use `set S := {A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) | ∀ y ∈ Λ, A *ᵥ y ∈ Λ} with hS`.

Take `⟨hΛo, hΛc⟩` from `latOpenCompact v L hL hfg`. Establish `hSo : IsOpen S` using `isOpen_forall_mulVec v hΛc hΛo`. Establish `hSc : IsCompact S` using `isCompact_stab v L hL hfg`. Establish `heq : (Kloc (E` using `E) v (L : Set (Fin n → E)) : Set (GL (Fin n) (Fv F v ⊗[F] E))) = Units.embedProduct _ ⁻¹' (S ×ˢ (MulOpposite.unop ⁻¹' S)) := by`. Use extensionality with `g`.

Use `show (∀ x, x ∈ Λ ↔ (g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ x ∈ Λ) ↔ ((g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) ∈ S ∧ ((g⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) ∈ S)`. Prove the components needed by the constructor for the conclusion. Introduce `hg`. Use `⟨fun y hy => (hg y).1 hy, fun y hy => ?_⟩` and prove the remaining obligations. Use `(hg (((g⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) _) *ᵥ y)).2` as an intermediate fact.

Rewrite `this` using `[Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`. Conclude with `this hy`. Introduce and unpack `⟨h1, h2⟩ x`. Use `⟨h1 x, fun hx => ?_⟩` and prove the remaining obligations. Use `h2 _ hx` as an intermediate fact.

Rewrite `this` using `[Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`. Then use the resulting hypothesis. Rewrite using `[heq]`. Use `⟨(hSo.prod (hSo.preimage MulOpposite.continuous_unop)).preimage Units.isEmbedding_embedProduct.continuous, ?_⟩` and prove the remaining obligations. Conclude with `Units.isClosedEmbedding_embedProduct.isCompact_preimage (hSc.prod ((MulOpposite.opHomeomorph.symm.isCompact_preimage).2 hSc))`.
-/
theorem kloc_open_compact (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (hfg : L.FG) :
    IsOpen (Kloc (E := E) v (L : Set (Fin n → E)) : Set (GL (Fin n) (Fv F v ⊗[F] E))) ∧
      IsCompact (Kloc (E := E) v (L : Set (Fin n → E)) : Set (GL (Fin n) (Fv F v ⊗[F] E))) := by
  have := fdFE (F := F) (E := E)
  have := MassDataIdxSteps.tens_topRing (F := F) (E := E) v
  have := t2Space_scalarTensorExt (F := F) (E := E) v
  set Λ : Set (Fin n → Fv F v ⊗[F] E) := (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) with hΛ
  set S := {A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) | ∀ y ∈ Λ, A *ᵥ y ∈ Λ} with hS
  obtain ⟨hΛo, hΛc⟩ := latOpenCompact v L hL hfg
  have hSo : IsOpen S := isOpen_forall_mulVec v hΛc hΛo
  have hSc : IsCompact S := isCompact_stab v L hL hfg
  have heq : (Kloc (E := E) v (L : Set (Fin n → E)) : Set (GL (Fin n) (Fv F v ⊗[F] E))) =
      Units.embedProduct _ ⁻¹' (S ×ˢ (MulOpposite.unop ⁻¹' S)) := by
    ext g
    show (∀ x, x ∈ Λ ↔ (g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ x ∈ Λ) ↔
      ((g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) ∈ S ∧
        ((g⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) ∈ S)
    constructor
    · intro hg
      refine ⟨fun y hy => (hg y).1 hy, fun y hy => ?_⟩
      have := (hg (((g⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) _) *ᵥ y)).2
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at this
      exact this hy
    · rintro ⟨h1, h2⟩ x
      refine ⟨h1 x, fun hx => ?_⟩
      have := h2 _ hx
      rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this
  rw [heq]
  refine ⟨(hSo.prod (hSo.preimage MulOpposite.continuous_unop)).preimage
    Units.isEmbedding_embedProduct.continuous, ?_⟩
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage
    (hSc.prod ((MulOpposite.opHomeomorph.symm.isCompact_preimage).2 hSc))

def sigL (σ : E →ₐ[F] E) : (Fv F v ⊗[F] E) →ₗ[Fv F v] (Fv F v ⊗[F] E) where
  toFun := sigR (Fv F v) σ
  map_add' := map_add _
  map_smul' := fun r x => by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1
    rw [Algebra.TensorProduct.algebraMap_apply]
    show Algebra.TensorProduct.map (AlgHom.id F (Fv F v)) σ (algebraMap (Fv F v) (Fv F v) r ⊗ₜ 1) = _
    rw [Algebra.TensorProduct.map_tmul, map_one]
    rfl

/- English proof (translation)
Use `fdFE (F := F) (E := E)` as an intermediate fact. Use `MassDataIdxSteps.tens_topRing (F := F) (E := E) v` as an intermediate fact. Use `t2Space_scalarTensorExt (F := F) (E := E) v` as an intermediate fact. Establish `hσ : Continuous (sigR (F` using `F) (Fv F v) σ) := IsModuleTopology.continuous_of_linearMap (sigL v σ)`. Establish `hval : Continuous (fun g : GL (Fin n) (Fv F v ⊗[F] E) => (g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)))` using `Units.continuous_val`.

Conclude with `isClosed_eq (((hval.matrix_map hσ).matrix_transpose.matrix_mul continuous_const).matrix_mul hval) continuous_const`.
-/
theorem isClosed_HR (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) :
    IsClosed ((HR (Fv F v) σ J : Subgroup (GL (Fin n) (Fv F v ⊗[F] E))) : Set (GL (Fin n) (Fv F v ⊗[F] E))) := by
  have := fdFE (F := F) (E := E)
  have := MassDataIdxSteps.tens_topRing (F := F) (E := E) v
  have := t2Space_scalarTensorExt (F := F) (E := E) v
  have hσ : Continuous (sigR (F := F) (Fv F v) σ) := IsModuleTopology.continuous_of_linearMap (sigL v σ)
  have hval : Continuous (fun g : GL (Fin n) (Fv F v ⊗[F] E) => (g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) :=
    Units.continuous_val
  exact isClosed_eq (((hval.matrix_map hσ).matrix_transpose.matrix_mul continuous_const).matrix_mul hval)
    continuous_const

end MassDataIdxK
