import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.LatticeProjection

/- English proof (translation)
Use `⟨fun s => ?_, fun v => ?_, fun {x y} h => ⟨1, by rw [Subtype.ext h]⟩⟩` and prove the remaining obligations. Conclude with `(isLocalizedModule_id (nonZeroDivisors O) V E).map_units s`. Establish `hv : v ∈ Submodule.span E (B : Set V)` using `hB ▸ Submodule.mem_top`. Take `⟨t, ht⟩` from `multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) E (B : Set V) v hv`. Rewrite `ht` using `[Submodule.span_eq]`.

Conclude with `⟨(⟨t • v, ht⟩, t), rfl⟩`.
-/
theorem isLocalizedModule_subtype {O E V : Type*} [CommRing O] [IsDomain O] [Field E] [Algebra O E]
    [IsFractionRing O E] [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V]
    (B : Submodule O V) (hB : Submodule.span E (B : Set V) = ⊤) :
    IsLocalizedModule (nonZeroDivisors O) B.subtype := by
  refine ⟨fun s => ?_, fun v => ?_, fun {x y} h => ⟨1, by rw [Subtype.ext h]⟩⟩
  · exact (isLocalizedModule_id (nonZeroDivisors O) V E).map_units s
  · have hv : v ∈ Submodule.span E (B : Set V) := hB ▸ Submodule.mem_top
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) E (B : Set V) v hv
    rw [Submodule.span_eq] at ht
    exact ⟨(⟨t • v, ht⟩, t), rfl⟩

/- English proof (translation)
Use `set B := L₁ ⊔ L₃ with hBdef`. Use `haveI : Module.Finite O B := Module.Finite.iff_fg.2 (h₁.sup h₃)`. Use `haveI : Module.IsTorsionFree O V := Module.IsTorsionFree.trans_faithfulSMul O E V`. Use `haveI : Module.FinitePresentation O B := Module.finitePresentation_of_finite O B`. Use `haveI : Module.Flat O B := inferInstance`.

Use `haveI : Module.Projective O B := Module.Flat.projective_of_finitePresentation`. Set `p : (L₁ × L₃) →ₗ[O] B` to `LinearMap.coprod (Submodule.inclusion le_sup_left) (Submodule.inclusion le_sup_right)`. Establish `hp : Function.Surjective p`. Introduce and unpack `⟨v, hv⟩`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 hv`.

Conclude with `⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩`. Take `⟨s, hs⟩` from `Module.projective_lifting_property p LinearMap.id hp`. Set `f : B →ₗ[O] V` to `L₁.subtype ∘ₗ LinearMap.fst O L₁ L₃ ∘ₗ s`. Use `haveI := isLocalizedModule_subtype (E := E) B hB`. Establish `hu` using `(isLocalizedModule_id (nonZeroDivisors O) V E).map_units`.

Set `g : V →ₗ[O] V` to `IsLocalizedModule.lift (nonZeroDivisors O) B.subtype f hu`. Use `⟨g.extendScalarsOfIsLocalization (nonZeroDivisors O) E, fun v hv => ?_⟩` and prove the remaining obligations. Establish `hg : g v = ((s ⟨v, hv⟩).1 : V)` using `IsLocalizedModule.lift_apply (nonZeroDivisors O) B.subtype f hu ⟨v, hv⟩`. Establish `hsum : ((s ⟨v, hv⟩).1 : V) + ((s ⟨v, hv⟩).2 : V) = v` using `congrArg Subtype.val (LinearMap.congr_fun hs ⟨v, hv⟩)`. Rewrite using `[LinearMap.extendScalarsOfIsLocalization_apply', hg]`.

Use `⟨(s ⟨v, hv⟩).1.2, ?_⟩` and prove the remaining obligations. Rewrite using `[sub_eq_of_eq_add' hsum.symm]`. Conclude with `(s ⟨v, hv⟩).2.2`.
-/
theorem exists_linear_projection {O E V : Type*} [CommRing O] [IsDedekindDomain O] [Field E] [Algebra O E]
    [IsFractionRing O E] [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V]
    (L₁ L₃ : Submodule O V) (h₁ : L₁.FG) (h₃ : L₃.FG)
    (hB : Submodule.span E ((L₁ ⊔ L₃ : Submodule O V) : Set V) = ⊤) :
    ∃ π : V →ₗ[E] V, ∀ v ∈ L₁ ⊔ L₃, π v ∈ L₁ ∧ v - π v ∈ L₃ := by
  set B := L₁ ⊔ L₃ with hBdef
  haveI : Module.Finite O B := Module.Finite.iff_fg.2 (h₁.sup h₃)
  haveI : Module.IsTorsionFree O V := Module.IsTorsionFree.trans_faithfulSMul O E V
  haveI : Module.FinitePresentation O B := Module.finitePresentation_of_finite O B
  haveI : Module.Flat O B := inferInstance
  haveI : Module.Projective O B := Module.Flat.projective_of_finitePresentation
  let p : (L₁ × L₃) →ₗ[O] B := LinearMap.coprod (Submodule.inclusion le_sup_left) (Submodule.inclusion le_sup_right)
  have hp : Function.Surjective p := by
    rintro ⟨v, hv⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p LinearMap.id hp
  let f : B →ₗ[O] V := L₁.subtype ∘ₗ LinearMap.fst O L₁ L₃ ∘ₗ s
  haveI := isLocalizedModule_subtype (E := E) B hB
  have hu := (isLocalizedModule_id (nonZeroDivisors O) V E).map_units
  let g : V →ₗ[O] V := IsLocalizedModule.lift (nonZeroDivisors O) B.subtype f hu
  refine ⟨g.extendScalarsOfIsLocalization (nonZeroDivisors O) E, fun v hv => ?_⟩
  have hg : g v = ((s ⟨v, hv⟩).1 : V) := IsLocalizedModule.lift_apply (nonZeroDivisors O) B.subtype f hu ⟨v, hv⟩
  have hsum : ((s ⟨v, hv⟩).1 : V) + ((s ⟨v, hv⟩).2 : V) = v :=
    congrArg Subtype.val (LinearMap.congr_fun hs ⟨v, hv⟩)
  rw [LinearMap.extendScalarsOfIsLocalization_apply', hg]
  refine ⟨(s ⟨v, hv⟩).1.2, ?_⟩
  rw [sub_eq_of_eq_add' hsum.symm]
  exact (s ⟨v, hv⟩).2.2

/- English proof (translation)
Introduce `D n L₁ L₃ h₁ h₃`. Take `⟨f₁, s₁, -⟩` from `(sd_iff D L₁).1 h₁`. Take `⟨f₃, -, -⟩` from `(sd_iff D L₃).1 h₃`. Take `⟨π, hπ⟩` from `exists_linear_projection (E := D.host.E) L₁ L₃ f₁ f₃ (top_le_iff.1 (s₁ ▸ Submodule.span_mono (fun x hx => Submodule.mem_sup_left hx)))`. Apply the tactic sequence `refine ⟨LinearMap.toMatrix' π, fun v hv => ?_, fun v hv => ?_, fun v hv => ?_⟩ <;>`.

Rewrite using `[LinearMap.toMatrix'_mulVec]`. Conclude with `(hπ v hv).1`. Simplify using `using L₃.sub_mem hv (hπ v (Submodule.mem_sup_right hv)).2`. Conclude with `(hπ v (Submodule.mem_sup_left hv)).2`.
-/
theorem exists_matrix_projection : ∀ (D : D7) (n : ℕ) (L₁ L₃ : Lat D n), SD D L₁ → SD D L₃ →
    ∃ π : Matrix (Fin n) (Fin n) D.host.E, (∀ v ∈ L₁ ⊔ L₃, π.mulVec v ∈ L₁) ∧ (∀ v ∈ L₃, π.mulVec v ∈ L₃) ∧
      ∀ v ∈ L₁, v - π.mulVec v ∈ L₃ := by
  intro D n L₁ L₃ h₁ h₃
  obtain ⟨f₁, s₁, -⟩ := (sd_iff D L₁).1 h₁
  obtain ⟨f₃, -, -⟩ := (sd_iff D L₃).1 h₃
  obtain ⟨π, hπ⟩ := exists_linear_projection (E := D.host.E) L₁ L₃ f₁ f₃
    (top_le_iff.1 (s₁ ▸ Submodule.span_mono (fun x hx => Submodule.mem_sup_left hx)))
  refine ⟨LinearMap.toMatrix' π, fun v hv => ?_, fun v hv => ?_, fun v hv => ?_⟩ <;>
    rw [LinearMap.toMatrix'_mulVec]
  · exact (hπ v hv).1
  · simpa using L₃.sub_mem hv (hπ v (Submodule.mem_sup_right hv)).2
  · exact (hπ v (Submodule.mem_sup_left hv)).2

end GlobalTheory.LatticeProjection
