import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.LatticeVectorsBoundedBelow

set_option autoImplicit false

noncomputable section

open NumberField Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

/- English proof (translation)
Apply `Subring.subset_closure` to reduce the goal to its premises. Use `left`. Conclude with `⟨⟨(c : I.E), c, rfl⟩, rfl⟩`.
-/
theorem inclE_mem_intAf (I : AutInst) (c : 𝓞 I.E) :
    Formalism.UG.inclE (F := I.F) (Af I.F) (c : I.E) ∈ IntAf I.F I.E := by
  apply Subring.subset_closure
  left
  exact ⟨⟨(c : I.E), c, rfl⟩, rfl⟩

def latSubmodule (I : AutInst) (x : I.GA) : Submodule (𝓞 I.E) (Fin I.n → I.E) where
  carrier := latSet I x
  zero_mem' := by
    show (I.fmat x.2⁻¹) *ᵥ _ ∈ I.Lf
    have : (fun i : Fin I.n => Formalism.UG.inclE (F := I.F) (Af I.F) ((0 : Fin I.n → I.E) i)) = 0 := by
      funext i; simp
    rw [this, Matrix.mulVec_zero]
    exact I.Lf.zero_mem
  add_mem' := by
    intro u w hu hw
    show (I.fmat x.2⁻¹) *ᵥ _ ∈ I.Lf
    have h : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((u + w) i)) =
        (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (u i)) +
          (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (w i)) := by
      funext i; simp
    rw [h, Matrix.mulVec_add]
    exact I.Lf.add_mem hu hw
  smul_mem' := by
    intro c u hu
    show (I.fmat x.2⁻¹) *ᵥ _ ∈ I.Lf
    have h : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((c • u) i)) =
        Formalism.UG.inclE (F := I.F) (Af I.F) (c : I.E) •
          (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (u i)) := by
      funext i
      simp [Algebra.smul_def]
    rw [h, Matrix.mulVec_smul]
    have := I.Lf.smul_mem (⟨_, inclE_mem_intAf I c⟩ : IntAf I.F I.E) hu
    exact this

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_latSubmodule (I : AutInst) (x : I.GA) :
    ((latSubmodule I x : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Set (Fin I.n → I.E)) = latSet I x := rfl

/- English proof (translation)
Introduce `I x`. Take `⟨m, hm1, hA, -⟩` from `h0 I x`. Use `⟨latSubmodule I x, ?_, coe_latSubmodule I x⟩` and prove the remaining obligations. Establish `hm0 : (m : I.E) ≠ 0` using `Nat.cast_ne_zero.2 (by omega)`. Set `φ : (Fin I.n → I.E) →ₗ[𝓞 I.E] (Fin I.n → I.E)` to `(((m : I.E)⁻¹ • LinearMap.id : (Fin I.n → I.E) →ₗ[I.E] (Fin I.n → I.E))).restrictScalars (𝓞 I.E)`.

Establish `hle : latSubmodule I x ≤ I.L.map φ`. Introduce `u hu`. Use `⟨(m : I.E) • u, hA u hu, ?_⟩` and prove the remaining obligations. Simplify using `[φ, smul_smul, inv_mul_cancel₀ hm0]`. Establish `hfg : (I.L.map φ).FG` using `I.L_fg.map φ`.

Use `haveI := isNoetherian_of_fg_of_noetherian _ hfg`. Establish `h1` using `IsNoetherian.noetherian ((latSubmodule I x).comap (I.L.map φ).subtype)`. Establish `h2` using `h1.map (I.L.map φ).subtype`. Rewrite `h2` using `[Submodule.map_comap_subtype, inf_eq_right.2 hle]`. Then use the resulting hypothesis.
-/
theorem lattice_finitelyGenerated_of_commensurable (h0 : LatticeCommensurable) : LatticeFinitelyGenerated := by
  intro I x
  obtain ⟨m, hm1, hA, -⟩ := h0 I x
  refine ⟨latSubmodule I x, ?_, coe_latSubmodule I x⟩
  have hm0 : (m : I.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  let φ : (Fin I.n → I.E) →ₗ[𝓞 I.E] (Fin I.n → I.E) :=
    (((m : I.E)⁻¹ • LinearMap.id : (Fin I.n → I.E) →ₗ[I.E] (Fin I.n → I.E))).restrictScalars (𝓞 I.E)
  have hle : latSubmodule I x ≤ I.L.map φ := by
    intro u hu
    refine ⟨(m : I.E) • u, hA u hu, ?_⟩
    simp [φ, smul_smul, inv_mul_cancel₀ hm0]
  have hfg : (I.L.map φ).FG := I.L_fg.map φ
  haveI := isNoetherian_of_fg_of_noetherian _ hfg
  have h1 := IsNoetherian.noetherian ((latSubmodule I x).comap (I.L.map φ).subtype)
  have h2 := h1.map (I.L.map φ).subtype
  rwa [Submodule.map_comap_subtype, inf_eq_right.2 hle] at h2

end Formalism.L2.SG.Pf.Tau
