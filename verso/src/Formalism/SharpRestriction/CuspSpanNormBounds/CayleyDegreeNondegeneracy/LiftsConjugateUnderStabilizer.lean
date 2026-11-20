import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GluingMassOfIsoAutCountGenus

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence.LatticeLiftIndependence

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LiftsConjugateUnderStabilizer (D : D7) (u : D.what₂.Word) : Prop :=
  ForPrimeFlag D u fun F0 => ∀ Λ₁ Λ₂ : LatV D, IsRowLat D F0 Λ₁ → IsRowLat D F0 Λ₂ →
    Lsub Λ₁ (lf D F0) = Lsub Λ₂ (lf D F0) →
    ∃ n ∈ stabF D F0, (∀ x ∈ orth (hS D) F0.X, n x - x ∈ F0.X) ∧ gmap n Λ₁ = Λ₂

section Cl

variable {D : D7}

/- English proof (translation)
Unfold `FlagG.Xa FlagG.X`. Use `congr 1`. Use extensionality with `x`. Simplify using the standard rewrite rules.
-/
theorem partial_isotropic_top {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) : F0.Xa D.R.rS = F0.X := by
  unfold FlagG.Xa FlagG.X
  congr 1
  ext x
  simp

/- English proof (translation)
The claim follows from `Submodule.span_mono (Set.image_subset_range _ _)`.
-/
theorem partial_isotropic_le {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (j : ℕ) : F0.Xa j ≤ F0.X :=
  Submodule.span_mono (Set.image_subset_range _ _)

/- English proof (translation)
Introduce `y hy`. Rewrite using `[Formalism.MainNotions.mem_orth_iff]`. Introduce `x hx`. Conclude with `Formalism.MainNotions.hT_swap_zero (Formalism.MainNotions.hT_zero_of_mem_X F0 (fun a => Formalism.MainNotions.hT_swap_zero (Formalism.MainNotions.hT_zero_of_mem_X F0 (fun b => F0.e_iso b a) x hx)) y hy)`.
-/
theorem isotropic_le_orth_isotropic {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) : F0.X ≤ orth (hS D) F0.X := by
  intro y hy
  rw [Formalism.MainNotions.mem_orth_iff]
  intro x hx
  exact Formalism.MainNotions.hT_swap_zero (Formalism.MainNotions.hT_zero_of_mem_X F0
    (fun a => Formalism.MainNotions.hT_swap_zero (Formalism.MainNotions.hT_zero_of_mem_X F0 (fun b => F0.e_iso b a) x hx)) y hy)

/- English proof (translation)
The claim follows from `le_inf le_sup_right (fun _ hx => isotropic_le_orth_isotropic F0 hx)`.
-/
theorem isotropic_le_Lsub {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : LatV D) :
    toO (hS D) F0.X ≤ Lsub Λ (lf D F0) :=
  le_inf le_sup_right (fun _ hx => isotropic_le_orth_isotropic F0 hx)

/- English proof (translation)
Establish `hσ' : ∀ x y, (VS D).hT (σ x) (σ y) = (VS D).hT x y` using `hσ`. Establish `hmem : ∀ x, σ.symm x ∈ F0.X ↔ x ∈ F0.X`. Introduce `x`. Use `conv_rhs => rw [← hX]`. Rewrite using `[Submodule.mem_map_equiv]`.

Establish `hgX : gmap σ (toO (hS D) F0.X) = toO (hS D) F0.X`. Use extensionality with `x`. Rewrite using `[isomAct_mem_gmap]`. Conclude with `hmem x`. Establish `hgO : gmap σ (toO (hS D) (orth (hS D) F0.X)) = toO (hS D) (orth (hS D) F0.X)`.

Use extensionality with `y`. Rewrite using `[isomAct_mem_gmap]`. Express the relevant statement in the definitionally equal form `σ.symm y ∈ orth (hS D) F0.X ↔ y ∈ orth (hS D) F0.X`. Rewrite using `[Formalism.MainNotions.mem_orth_iff, Formalism.MainNotions.mem_orth_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce `h x hx`. Use `h (σ.symm x) ((hmem x).2 hx)` as an intermediate fact. Rewrite `this` using `[← hσ' (σ.symm x) (σ.symm y), LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]`. Then use the resulting hypothesis. Introduce `h x hx`. Establish `hx' : σ x ∈ F0.X`.

Rewrite using `[← hmem, LinearEquiv.symm_apply_apply]`. Conclude with `hx`. Use `h (σ x) hx'` as an intermediate fact. Rewrite using `[← hσ' x (σ.symm y), LinearEquiv.apply_symm_apply]` and apply the resulting hypothesis. Unfold `Lsub Lrep`.

Rewrite using `[gmap_inf_cayley_degree_nondegeneracy, gmap_sup_cayley_degree_nondegeneracy, gmap_inf_cayley_degree_nondegeneracy]`. Express the relevant statement in the definitionally equal form `(gmap σ Λ ⊓ toO (hS D) (orth (hS D) F0.X) ⊔ toO (hS D) F0.X) ⊓ toO (hS D) (orth (hS D) F0.X) = (gmap σ Λ ⊓ gmap σ (toO (hS D) (orth (hS D) F0.X)) ⊔ gmap σ (toO (hS D) F0.X)) ⊓ gmap σ (toO (hS D) (orth (hS D) F0.X))`. Rewrite using `[hgX, hgO]`.
-/
theorem Lsub_gmap_of_isometry {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hσ : σ ∈ isom (VS D).hT) (hX : F0.X.map (σ : (VS D).V →ₗ[D.host.E] (VS D).V) = F0.X) (Λ : LatV D) :
    Lsub (gmap σ Λ) (lf D F0) = gmap σ (Lsub Λ (lf D F0)) := by
  have hσ' : ∀ x y, (VS D).hT (σ x) (σ y) = (VS D).hT x y := hσ
  have hmem : ∀ x, σ.symm x ∈ F0.X ↔ x ∈ F0.X := by
    intro x
    conv_rhs => rw [← hX]
    rw [Submodule.mem_map_equiv]
  have hgX : gmap σ (toO (hS D) F0.X) = toO (hS D) F0.X := by
    ext x
    rw [isomAct_mem_gmap]
    exact hmem x
  have hgO : gmap σ (toO (hS D) (orth (hS D) F0.X)) = toO (hS D) (orth (hS D) F0.X) := by
    ext y
    rw [isomAct_mem_gmap]
    change σ.symm y ∈ orth (hS D) F0.X ↔ y ∈ orth (hS D) F0.X
    rw [Formalism.MainNotions.mem_orth_iff, Formalism.MainNotions.mem_orth_iff]
    constructor
    · intro h x hx
      have := h (σ.symm x) ((hmem x).2 hx)
      rwa [← hσ' (σ.symm x) (σ.symm y), LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at this
    · intro h x hx
      have hx' : σ x ∈ F0.X := by
        rw [← hmem, LinearEquiv.symm_apply_apply]
        exact hx
      have := h (σ x) hx'
      rwa [← hσ' x (σ.symm y), LinearEquiv.apply_symm_apply]
  unfold Lsub Lrep
  rw [gmap_inf_cayley_degree_nondegeneracy, gmap_sup_cayley_degree_nondegeneracy, gmap_inf_cayley_degree_nondegeneracy]
  change (gmap σ Λ ⊓ toO (hS D) (orth (hS D) F0.X) ⊔ toO (hS D) F0.X) ⊓ toO (hS D) (orth (hS D) F0.X) =
    (gmap σ Λ ⊓ gmap σ (toO (hS D) (orth (hS D) F0.X)) ⊔ gmap σ (toO (hS D) F0.X)) ⊓
      gmap σ (toO (hS D) (orth (hS D) F0.X))
  rw [hgX, hgO]

/- English proof (translation)
Use `⟨(isom (VS D).hT).mul_mem ha.1 hb.1, fun j => ?_, ?_⟩` and prove the remaining obligations. Establish `e : ((a * b : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V) = (a : (VS D).V →ₗ[D.host.E] (VS D).V) ∘ₗ (b : (VS D).V →ₗ[D.host.E] (VS D).V)` using `rfl`. Rewrite using `[e, Submodule.map_comp, hb.2.1 j, ha.2.1 j]`. Express the relevant statement in the definitionally equal form `a (b F0.z) = F0.z`. Rewrite using `[hb.2.2, ha.2.2]`.
-/
theorem mul_mem_flag_stabilizer {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) {a b : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (ha : a ∈ stabF D F0) (hb : b ∈ stabF D F0) : a * b ∈ stabF D F0 := by
  refine ⟨(isom (VS D).hT).mul_mem ha.1 hb.1, fun j => ?_, ?_⟩
  · have e : ((a * b : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V) =
        (a : (VS D).V →ₗ[D.host.E] (VS D).V) ∘ₗ (b : (VS D).V →ₗ[D.host.E] (VS D).V) := rfl
    rw [e, Submodule.map_comp, hb.2.1 j, ha.2.1 j]
  · change a (b F0.z) = F0.z
    rw [hb.2.2, ha.2.2]

end Cl

end Formalism.MainNotions.BridgeLemma₂

end
