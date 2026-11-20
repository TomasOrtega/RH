import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCoeffOfSeparating
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.AutGrowth

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.ContinuousRepresentationCoefficients.isContRep_sub`. Consider the case `exact _root_.GlobalTheory.ContinuousRepresentationCoefficients.isContRep_sub`. Consider the case `(apply _root_.GlobalTheory.ContinuousRepresentationCoefficients.isContRep_sub <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.ContinuousRepresentationCoefficients.isContRep_sub <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.ContinuousRepresentationCoefficients.isContRep_sub <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.ContinuousRepresentationCoefficients.isContRep_sub ..)`.
-/
theorem isContRep_sub_cptRep (W : Submodule ℂ (Sm E a)) (hW : ∀ k, ∀ w ∈ W, cptRep E a k w ∈ W)
    [FiniteDimensional ℂ W] : GlobalTheory.Published.AutFin.IsContRep (GlobalTheory.PRep.sub (cptRep E a) W hW) := by
  first
  | exact @_root_.GlobalTheory.ContinuousRepresentationCoefficients.isContRep_sub
  | exact _root_.GlobalTheory.ContinuousRepresentationCoefficients.isContRep_sub
  | (apply _root_.GlobalTheory.ContinuousRepresentationCoefficients.isContRep_sub <;> assumption)
  | (intros; apply _root_.GlobalTheory.ContinuousRepresentationCoefficients.isContRep_sub <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ContinuousRepresentationCoefficients.isContRep_sub <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ContinuousRepresentationCoefficients.isContRep_sub ..)

/- English proof (translation)
Introduce `hHC E _ _ _ a L hL W hW hWf c N hN hcap`. Use `haveI := hWf`. Establish `hF` using `hHC E a L hL W (GlobalTheory.PRep.sub (cptRep E a) W hW) (isContRep_sub_cptRep W hW) c`. Use `haveI := hF`. Establish `hmem : ∀ T ∈ N, ∀ w, T w ∈ GlobalTheory.Published.AutFinGL.forms L (GlobalTheory.PRep.sub (cptRep E a) W hW) c`.

Introduce `T hT w`. Establish `hm : (∀ k w, T (GlobalTheory.PRep.sub (cptRep E a) W hW k w) = cptRep E a k (T w)) ∧ ∀ w, T w ∈ tame E a ∧ (∀ γ g, (T w).1 (ratGL E a γ * g) = (T w).1 g) ∧ ∀ k ∈ L, finRep E a k (T w) = T w` using `hN hT`. Take `⟨heq, hall⟩` from `hm`. Take `⟨htame, hleft, hfix⟩` from `hall w`. Establish `hZ : ∀ z ∈ Zalg E a, ∃ s : ℂ, z ∘ₗ T = s • T`.

Introduce `z hz`. Proceed by induction on `hz using Algebra.adjoin_induction with`. Consider the case `mem x hx => obtain ⟨τ, u, rfl⟩ := hx`. Conclude with `⟨c τ u, hcap T hT τ u⟩`. Consider the case `algebraMap r => exact ⟨r, LinearMap.ext fun v => by simp⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨s, hs⟩` from `hx`. Take `⟨t, ht⟩` from `hy`. Conclude with `⟨s + t, by rw [LinearMap.add_comp, hs, ht, add_smul]⟩`. Consider the case `mul x y _ _ hx hy`.

Take `⟨s, hs⟩` from `hx`. Take `⟨t, ht⟩` from `hy`. Conclude with `⟨t * s, by rw [Module.End.mul_eq_comp, LinearMap.comp_assoc, ht, LinearMap.comp_smul, hs, smul_smul]⟩`. Use `⟨⟨hleft, ?_, ?_, ?_, ?_⟩, hfix, GlobalTheory.Published.AutFinGL.type_of_map _ T heq w, fun τ u => ?_⟩` and prove the remaining obligations. Conclude with `isOpen_stab_of_mem_nhds (finRep E a) (T w) (Filter.mem_of_superset (hL.mem_nhds L.one_mem) fun k hk => hfix k hk)`.

Use `Submodule.finiteDimensional_of_le (S₂ := LinearMap.range T) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `⟨_, heq k w⟩`. Use `Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {T w}) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨z, hz, rfl⟩`.

Take `⟨s, hs⟩` from `hZ z hz`. Establish `e : z (T w) = s • T w` using `LinearMap.congr_fun hs w`. Use `show z (T w) ∈ _`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ s (Submodule.mem_span_singleton_self _)`.

Conclude with `growth_of_tame htame`. Conclude with `LinearMap.congr_fun (hcap T hT τ u) w`. Set `Φ : N →ₗ[ℂ] (W →ₗ[ℂ] Submodule.span ℂ (GlobalTheory.Published.AutFinGL.forms L (GlobalTheory.PRep.sub (cptRep E a) W hW) c))` to `{ toFun := fun T => LinearMap.codRestrict _ T.1 fun w => Submodule.subset_span (hmem T.1 T.2 w) map_add' := fun T T' => LinearMap.ext fun w => rfl map_smul' := fun r T => LinearMap.ext fun w => rfl }`. Establish `hinj : Function.Injective Φ` using `fun T T' h => Subtype.ext (LinearMap.ext fun w => congrArg Subtype.val (LinearMap.congr_fun h w))`. Conclude with `Module.Finite.of_injective Φ hinj`.
-/
theorem finiteDimensional_capEigen_maps : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ (W : Submodule ℂ (Sm E a)) (hW : ∀ k, ∀ w ∈ W, cptRep E a k w ∈ W), FiniteDimensional ℂ W → ∀ (c : (E →+* ℂ) → ℂ → ℂ) (N : Submodule ℂ (W →ₗ[ℂ] Sm E a)), N ≤ maps L W hW → (∀ T ∈ N, ∀ τ u, cap τ u ∘ₗ T = c τ u • T) → FiniteDimensional ℂ N := by
  intro hHC E _ _ _ a L hL W hW hWf c N hN hcap
  haveI := hWf
  have hF := hHC E a L hL W (GlobalTheory.PRep.sub (cptRep E a) W hW) (isContRep_sub_cptRep W hW) c
  haveI := hF
  have hmem : ∀ T ∈ N, ∀ w, T w ∈ GlobalTheory.Published.AutFinGL.forms L (GlobalTheory.PRep.sub (cptRep E a) W hW) c := by
    intro T hT w
    have hm : (∀ k w, T (GlobalTheory.PRep.sub (cptRep E a) W hW k w) = cptRep E a k (T w)) ∧
        ∀ w, T w ∈ tame E a ∧ (∀ γ g, (T w).1 (ratGL E a γ * g) = (T w).1 g) ∧
          ∀ k ∈ L, finRep E a k (T w) = T w := hN hT
    obtain ⟨heq, hall⟩ := hm
    obtain ⟨htame, hleft, hfix⟩ := hall w
    have hZ : ∀ z ∈ Zalg E a, ∃ s : ℂ, z ∘ₗ T = s • T := by
      intro z hz
      induction hz using Algebra.adjoin_induction with
      | mem x hx => obtain ⟨τ, u, rfl⟩ := hx; exact ⟨c τ u, hcap T hT τ u⟩
      | algebraMap r => exact ⟨r, LinearMap.ext fun v => by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨s, hs⟩ := hx
        obtain ⟨t, ht⟩ := hy
        exact ⟨s + t, by rw [LinearMap.add_comp, hs, ht, add_smul]⟩
      | mul x y _ _ hx hy =>
        obtain ⟨s, hs⟩ := hx
        obtain ⟨t, ht⟩ := hy
        exact ⟨t * s, by rw [Module.End.mul_eq_comp, LinearMap.comp_assoc, ht, LinearMap.comp_smul, hs, smul_smul]⟩
    refine ⟨⟨hleft, ?_, ?_, ?_, ?_⟩, hfix, GlobalTheory.Published.AutFinGL.type_of_map _ T heq w, fun τ u => ?_⟩
    · exact isOpen_stab_of_mem_nhds (finRep E a) (T w)
        (Filter.mem_of_superset (hL.mem_nhds L.one_mem) fun k hk => hfix k hk)
    · refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range T) (Submodule.span_le.2 ?_)
      rintro _ ⟨k, rfl⟩
      exact ⟨_, heq k w⟩
    · refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {T w}) (Submodule.span_le.2 ?_)
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨s, hs⟩ := hZ z hz
      have e : z (T w) = s • T w := LinearMap.congr_fun hs w
      show z (T w) ∈ _
      rw [e]
      exact Submodule.smul_mem _ s (Submodule.mem_span_singleton_self _)
    · exact growth_of_tame htame
    · exact LinearMap.congr_fun (hcap T hT τ u) w
  let Φ : N →ₗ[ℂ] (W →ₗ[ℂ] Submodule.span ℂ (GlobalTheory.Published.AutFinGL.forms L (GlobalTheory.PRep.sub (cptRep E a) W hW) c)) :=
    { toFun := fun T => LinearMap.codRestrict _ T.1 fun w => Submodule.subset_span (hmem T.1 T.2 w)
      map_add' := fun T T' => LinearMap.ext fun w => rfl
      map_smul' := fun r T => LinearMap.ext fun w => rfl }
  have hinj : Function.Injective Φ := fun T T' h =>
    Subtype.ext (LinearMap.ext fun w => congrArg Subtype.val (LinearMap.congr_fun h w))
  exact Module.Finite.of_injective Φ hinj

end GlobalTheory.AutGrowth

end
