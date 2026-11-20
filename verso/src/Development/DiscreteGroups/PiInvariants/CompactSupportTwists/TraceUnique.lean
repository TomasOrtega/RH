import Mathlib
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.TraceUniqueMatrix

set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

noncomputable section

namespace DiscreteGroups.T1.Desc.Swap3
open DiscreteGroups.T1.Desc.TraceUniqueU3

section Schur

variable {Y : Type} [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]

/- English proof (translation)
Take `⟨μ, hμ⟩` from `Module.End.exists_eigenvalue z`. Take `⟨v, hv⟩` from `hμ.exists_hasEigenvector`. Use `⟨μ, ?_⟩` and prove the remaining obligations. Set `W : Submodule ℂ Y` to `LinearMap.ker (z - μ • LinearMap.id)`. Establish `hmem : ∀ y, y ∈ W ↔ z y = μ • y` using `fun y => by`.

Simplify using `only [W, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]`. Establish `hW : ∀ g ∈ S, ∀ y ∈ W, g y ∈ W`. Introduce `g hg y hy`. Rewrite `hy`, the goal using `[hmem]`. Establish `h` using `LinearMap.congr_fun (hz g hg).eq y`.

Simplify using `only [Module.End.mul_apply] at h`. Rewrite using `[h, hy, map_smul]`. Break down `hirr W hW with h | h` into its components or cases. Conclude with `absurd ((Submodule.eq_bot_iff W).1 h v ((hmem v).2 hv.apply_eq_smul)) hv.2`. Introduce `y`.

Conclude with `(hmem y).1 (h ▸ Submodule.mem_top)`.
-/
theorem schur [Nontrivial Y] (S : Set (Module.End ℂ Y))
    (hirr : ∀ W : Submodule ℂ Y, (∀ g ∈ S, ∀ y ∈ W, g y ∈ W) → W = ⊥ ∨ W = ⊤)
    (z : Module.End ℂ Y) (hz : ∀ g ∈ S, Commute z g) : ∃ μ : ℂ, ∀ y, z y = μ • y := by
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue z
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  refine ⟨μ, ?_⟩
  let W : Submodule ℂ Y := LinearMap.ker (z - μ • LinearMap.id)
  have hmem : ∀ y, y ∈ W ↔ z y = μ • y := fun y => by
    simp only [W, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  have hW : ∀ g ∈ S, ∀ y ∈ W, g y ∈ W := by
    intro g hg y hy
    rw [hmem] at hy ⊢
    have h := LinearMap.congr_fun (hz g hg).eq y
    simp only [Module.End.mul_apply] at h
    rw [h, hy, map_smul]
  rcases hirr W hW with h | h
  · exact absurd ((Submodule.eq_bot_iff W).1 h v ((hmem v).2 hv.apply_eq_smul)) hv.2
  · intro y
    exact (hmem y).1 (h ▸ Submodule.mem_top)

/- English proof (translation)
Use `letI : Module R Y := Module.compHom Y φ.toRingHom`. Establish `hsmul : ∀ (r : R) (y : Y), r • y = φ r y` using `fun r y => rfl`. Establish `hc : ∀ (c : ℂ) (y : Y), (algebraMap ℂ R c) • y = c • y` using `fun c y => by`. Rewrite using `[hsmul, AlgHom.commutes, Module.algebraMap_end_apply]`. Establish `hnt : Nontrivial (Submodule R Y)`.

Use `⟨⟨⊥, ⊤, fun h => ?_⟩⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `exists_ne (0 : Y)`. Establish `: y ∈ (⊥ : Submodule R Y)` using `h ▸ Submodule.mem_top`. Conclude with `hy ((Submodule.mem_bot R).1 this)`. Establish `hsimple : IsSimpleModule R Y`.

Use `{ exists_pair_ne := hnt.exists_pair_ne, eq_bot_or_eq_top := fun W => ?_ }` and prove the remaining obligations. Set `W' : Submodule ℂ Y` to `{ carrier := W add_mem' := W.add_mem zero_mem' := W.zero_mem smul_mem' := fun c y hy => by`. Rewrite using `[← hc]`. Conclude with `W.smul_mem _ hy }`. Break down `hirr W' (fun r y hy => by` into its components or cases.

Rewrite using `[← hsmul]`. Conclude with `W.smul_mem r hy) with h | h`. Use `left`. Conclude with `(Submodule.eq_bot_iff W).2 fun y hy => (Submodule.eq_bot_iff W').1 h y hy`. Use `right`.

Conclude with `Submodule.eq_top_iff'.2 fun y => Submodule.eq_top_iff'.1 h y`. Establish `hsc : ∀ ψ : Module.End R Y, ∃ μ : ℂ, ∀ y, ψ y = μ • y` using `fun ψ => by`. Set `ψc : Module.End ℂ Y` to `{ toFun := ψ map_add' := ψ.map_add map_smul' := fun c y => by`. Rewrite using `[RingHom.id_apply, ← hc, ψ.map_smul, hc] }`. Use `schur (Set.range φ) (fun W hW => hirr W fun r y hy => hW _ ⟨r, rfl⟩ y hy) ψc ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨r, rfl⟩`. Use `LinearMap.ext fun y => ?_` and prove the remaining obligations. Use `show ψ (φ r y) = φ r (ψ y)`. Rewrite using `[← hsmul, ψ.map_smul, hsmul]`. Introduce `g`.

Set `G : Module.End (Module.End R Y) Y` to `{ toFun := g map_add' := g.map_add map_smul' := fun ψ y => by`. Take `⟨μ, hμ⟩` from `hsc ψ`. Simplify using `only [Module.End.smul_def, RingHom.id_apply]`. Rewrite using `[hμ, hμ, g.map_smul] }`. Set `b` to `Module.finBasis ℂ Y`.

Take `⟨r, hr⟩` from `jacobson_density G (Finset.univ.image b)`. Use `⟨r, (Module.Basis.ext b fun i => ?_).symm⟩` and prove the remaining obligations. Conclude with `hr (b i) (Finset.mem_image_of_mem b (Finset.mem_univ i))`.
-/
theorem burnside [Nontrivial Y] {R : Type} [Ring R] [Algebra ℂ R] (φ : R →ₐ[ℂ] Module.End ℂ Y)
    (hirr : ∀ W : Submodule ℂ Y, (∀ r, ∀ y ∈ W, φ r y ∈ W) → W = ⊥ ∨ W = ⊤) :
    Function.Surjective φ := by
  classical
  letI : Module R Y := Module.compHom Y φ.toRingHom
  have hsmul : ∀ (r : R) (y : Y), r • y = φ r y := fun r y => rfl
  have hc : ∀ (c : ℂ) (y : Y), (algebraMap ℂ R c) • y = c • y := fun c y => by
    rw [hsmul, AlgHom.commutes, Module.algebraMap_end_apply]
  have hnt : Nontrivial (Submodule R Y) := by
    refine ⟨⟨⊥, ⊤, fun h => ?_⟩⟩
    obtain ⟨y, hy⟩ := exists_ne (0 : Y)
    have : y ∈ (⊥ : Submodule R Y) := h ▸ Submodule.mem_top
    exact hy ((Submodule.mem_bot R).1 this)
  have hsimple : IsSimpleModule R Y := by
    refine { exists_pair_ne := hnt.exists_pair_ne, eq_bot_or_eq_top := fun W => ?_ }
    let W' : Submodule ℂ Y :=
      { carrier := W
        add_mem' := W.add_mem
        zero_mem' := W.zero_mem
        smul_mem' := fun c y hy => by
          rw [← hc]
          exact W.smul_mem _ hy }
    rcases hirr W' (fun r y hy => by
        rw [← hsmul]
        exact W.smul_mem r hy) with h | h
    · left
      exact (Submodule.eq_bot_iff W).2 fun y hy => (Submodule.eq_bot_iff W').1 h y hy
    · right
      exact Submodule.eq_top_iff'.2 fun y => Submodule.eq_top_iff'.1 h y
  have hsc : ∀ ψ : Module.End R Y, ∃ μ : ℂ, ∀ y, ψ y = μ • y := fun ψ => by
    let ψc : Module.End ℂ Y :=
      { toFun := ψ
        map_add' := ψ.map_add
        map_smul' := fun c y => by
          rw [RingHom.id_apply, ← hc, ψ.map_smul, hc] }
    refine schur (Set.range φ) (fun W hW => hirr W fun r y hy => hW _ ⟨r, rfl⟩ y hy) ψc ?_
    rintro _ ⟨r, rfl⟩
    refine LinearMap.ext fun y => ?_
    show ψ (φ r y) = φ r (ψ y)
    rw [← hsmul, ψ.map_smul, hsmul]
  intro g
  let G : Module.End (Module.End R Y) Y :=
    { toFun := g
      map_add' := g.map_add
      map_smul' := fun ψ y => by
        obtain ⟨μ, hμ⟩ := hsc ψ
        simp only [Module.End.smul_def, RingHom.id_apply]
        rw [hμ, hμ, g.map_smul] }
  let b := Module.finBasis ℂ Y
  obtain ⟨r, hr⟩ := jacobson_density G (Finset.univ.image b)
  refine ⟨r, (Module.Basis.ext b fun i => ?_).symm⟩
  exact hr (b i) (Finset.mem_image_of_mem b (Finset.mem_univ i))

end Schur

/- English proof (translation)
Set `b` to `Module.finBasis ℂ V`. Set `e` to `LinearMap.toMatrixAlgEquiv b`. Set `g' : Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ →ₗ[ℂ] ℂ` to `g.comp e.symm.toLinearMap`. Take `⟨c, hc⟩` from `trace_unique_matrix g' fun A B => by`. Simplify using `only [g', LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_mul]`.

Conclude with `hg _ _`. Use `⟨c, fun z => ?_⟩` and prove the remaining obligations. Use `hc (e z)` as an intermediate fact. Simplify using `only [g', LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, AlgEquiv.symm_apply_apply] at this`. Rewrite using `[this, LinearMap.trace_eq_matrix_trace ℂ b]`.

Both sides reduce to the same expression.
-/
theorem trace_unique {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (g : Module.End ℂ V →ₗ[ℂ] ℂ) (hg : ∀ a b, g (a * b) = g (b * a)) :
    ∃ c : ℂ, ∀ z, g z = c * LinearMap.trace ℂ V z := by
  let b := Module.finBasis ℂ V
  let e := LinearMap.toMatrixAlgEquiv b
  let g' : Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ →ₗ[ℂ] ℂ :=
    g.comp e.symm.toLinearMap
  obtain ⟨c, hc⟩ := trace_unique_matrix g' fun A B => by
    simp only [g', LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_mul]
    exact hg _ _
  refine ⟨c, fun z => ?_⟩
  have := hc (e z)
  simp only [g', LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, AlgEquiv.symm_apply_apply] at this
  rw [this, LinearMap.trace_eq_matrix_trace ℂ b]
  rfl

end DiscreteGroups.T1.Desc.Swap3

end
