import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.QCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

/- English proof (translation)
Use `⟨?_, fun t => ?_⟩` and prove the remaining obligations. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `s hs`. Apply `(sectionsOn.toΓ F ⊤).injective` to reduce the goal to its premises. Rewrite using `[map_zero]`.

Use `section_eq_zero_of_germ _ fun x hx => ?_` and prove the remaining obligations. Distinguish the cases in `hxs : x ∈ support F`. Take `⟨i, hi⟩` from `Set.mem_iUnion.1 (hcov hxs)`. Establish `h0 : sectionsOn.res R F (le_top : W i ≤ ⊤) s = 0` using `congrFun hs i`. Use `congrArg (fun u => F.presheaf.germ (W i) x hi (sectionsOn.toΓ F (W i) u)) h0` as an intermediate fact.

Simplify using `only [sectionsOn.toΓ_res, map_zero] at this`. Rewrite `this` using `[F.presheaf.germ_res_apply]`. Then use the resulting hypothesis. Conclude with `(notMem_support_iff.1 hxs).elim _ _`. Establish `key (i : ι) : ∃ s : sectionsOn F ⊤, sectionsOn.res R F (le_top : W i ≤ ⊤) s = t i ∧ ∀ j, j ≠ i → sectionsOn.res R F (le_top : W j ≤ ⊤) s = 0`. Set `C : X.Opens` to `⟨(support F)ᶜ, (isClosed_support F).isOpen_compl⟩`.

Set `V : X.Opens` to `(⨆ (j : ι) (_ : j ≠ i), W j) ⊔ C`. Establish `hWV (j : ι) (hj : j ≠ i) : W j ≤ V` using `le_sup_of_le_left (le_iSup₂ (f := fun (j : ι) (_ : j ≠ i) => W j) j hj)`. Establish `hcovV : (⊤ : X.Opens) ≤ W i ⊔ V` using `fun x _ => by`. Distinguish the cases in `hxs : x ∈ support F`. Take `⟨j, hj⟩` from `Set.mem_iUnion.1 (hcov hxs)`.

Distinguish the cases in `hji : j = i`. Conclude with `Or.inl (hji ▸ hj)`. Conclude with `Or.inr (hWV j hji hj)`. Conclude with `Or.inr (Or.inr hxs)`. Establish `: Subsingleton Γ(F, W i ⊓ V)` using `subsingleton_sections_of_notMem_support fun y hy hys => by`.

Break down `hy.2 with hy' | hy'` into its components or cases. Choose the witnesses or unpack the hypotheses as in `⟨j, hj, hyj⟩ : ∃ j, j ≠ i ∧ y ∈ W j := by`. Simplify `hy'` using `[Opens.mem_iSup]`. Conclude with `hdisj i j (Ne.symm hj) y hys hy.1 hyj`. Conclude with `hy' hys`.

Take `⟨s, h₁, h₂⟩` from `Qcqs.exists_section_glue₂ F (V₁ := W i) (V₂ := V) (W := ⊤) le_top le_top hcovV (sectionsOn.toΓ F (W i) (t i)) 0 (Subsingleton.elim _ _)`. Use `⟨(sectionsOn.toΓ F ⊤).symm s, (sectionsOn.toΓ F (W i)).injective ?_, fun j hj => (sectionsOn.toΓ F (W j)).injective ?_⟩` and prove the remaining obligations. Rewrite using `[sectionsOn.toΓ_res, AddEquiv.apply_symm_apply]`. Conclude with `h₁`. Rewrite using `[sectionsOn.toΓ_res, AddEquiv.apply_symm_apply, map_zero]`.

Establish `e` using `congrArg (F.presheaf.map (homOfLE (hWV j hj)).op) h₂`. Rewrite `e` using `[map_zero, ← ConcreteCategory.comp_apply, ← Functor.map_comp]`. Conclude with `e`. Use `choose s h₁ h₂ using key`. Use `⟨∑ i, s i, funext fun j => ?_⟩` and prove the remaining obligations.

Rewrite using `[LinearMap.pi_apply, map_sum, Finset.sum_eq_single j (fun i _ hi => h₂ i j hi.symm) (by simp), h₁]`.
-/
theorem sectionsOn_res_pi_bijective_of_separating {X : Scheme.{0}} (F : X.Modules) [IsFiniteQC F]
    (R : Type) [CommRing R] [Algebra R Γ(X, ⊤)] {ι : Type} [Fintype ι] (W : ι → X.Opens)
    (hcov : support F ⊆ ⋃ i, (W i : Set X))
    (hdisj : ∀ i j, i ≠ j → ∀ x ∈ support F, x ∈ W i → x ∉ W j) :
    Function.Bijective
      (LinearMap.pi fun i => sectionsOn.res R F (le_top : W i ≤ ⊤) :
        sectionsOn F ⊤ →ₗ[R] ∀ i, sectionsOn F (W i)) := by
  classical
  refine ⟨?_, fun t => ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro s hs
    apply (sectionsOn.toΓ F ⊤).injective
    rw [map_zero]
    refine section_eq_zero_of_germ _ fun x hx => ?_
    by_cases hxs : x ∈ support F
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov hxs)
      have h0 : sectionsOn.res R F (le_top : W i ≤ ⊤) s = 0 := congrFun hs i
      have := congrArg (fun u => F.presheaf.germ (W i) x hi (sectionsOn.toΓ F (W i) u)) h0
      simp only [sectionsOn.toΓ_res, map_zero] at this
      rwa [F.presheaf.germ_res_apply] at this
    · exact (notMem_support_iff.1 hxs).elim _ _
  have key (i : ι) : ∃ s : sectionsOn F ⊤, sectionsOn.res R F (le_top : W i ≤ ⊤) s = t i ∧
      ∀ j, j ≠ i → sectionsOn.res R F (le_top : W j ≤ ⊤) s = 0 := by
    let C : X.Opens := ⟨(support F)ᶜ, (isClosed_support F).isOpen_compl⟩
    let V : X.Opens := (⨆ (j : ι) (_ : j ≠ i), W j) ⊔ C
    have hWV (j : ι) (hj : j ≠ i) : W j ≤ V :=
      le_sup_of_le_left (le_iSup₂ (f := fun (j : ι) (_ : j ≠ i) => W j) j hj)
    have hcovV : (⊤ : X.Opens) ≤ W i ⊔ V := fun x _ => by
      by_cases hxs : x ∈ support F
      · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hcov hxs)
        by_cases hji : j = i
        · exact Or.inl (hji ▸ hj)
        · exact Or.inr (hWV j hji hj)
      · exact Or.inr (Or.inr hxs)
    have : Subsingleton Γ(F, W i ⊓ V) := subsingleton_sections_of_notMem_support fun y hy hys => by
      rcases hy.2 with hy' | hy'
      · obtain ⟨j, hj, hyj⟩ : ∃ j, j ≠ i ∧ y ∈ W j := by
          simpa [Opens.mem_iSup] using hy'
        exact hdisj i j (Ne.symm hj) y hys hy.1 hyj
      · exact hy' hys
    obtain ⟨s, h₁, h₂⟩ := Qcqs.exists_section_glue₂ F (V₁ := W i) (V₂ := V) (W := ⊤) le_top le_top
      hcovV (sectionsOn.toΓ F (W i) (t i)) 0 (Subsingleton.elim _ _)
    refine ⟨(sectionsOn.toΓ F ⊤).symm s, (sectionsOn.toΓ F (W i)).injective ?_, fun j hj =>
      (sectionsOn.toΓ F (W j)).injective ?_⟩
    · rw [sectionsOn.toΓ_res, AddEquiv.apply_symm_apply]
      exact h₁
    · rw [sectionsOn.toΓ_res, AddEquiv.apply_symm_apply, map_zero]
      have e := congrArg (F.presheaf.map (homOfLE (hWV j hj)).op) h₂
      rw [map_zero, ← ConcreteCategory.comp_apply, ← Functor.map_comp] at e
      exact e
  choose s h₁ h₂ using key
  refine ⟨∑ i, s i, funext fun j => ?_⟩
  rw [LinearMap.pi_apply, map_sum, Finset.sum_eq_single j (fun i _ hi => h₂ i j hi.symm) (by simp),
    h₁]

/- English proof (translation)
Introduce `X F _ R _ _ ι _ W hcov hdisj`. Rewrite using `[(LinearEquiv.ofBijective _ (sectionsOn_res_pi_bijective_of_separating F R W hcov hdisj)).length_eq, Module.length_pi_of_fintype]`.
-/
theorem length_sectionsOn_top_eq_sum_of_separating :
    ∀ {X : Scheme.{0}} (F : X.Modules) [IsFiniteQC F] (R : Type) [CommRing R]
      [Algebra R Γ(X, ⊤)] {ι : Type} [Fintype ι] (W : ι → X.Opens),
      support F ⊆ ⋃ i, (W i : Set X) → (∀ i j, i ≠ j → ∀ x ∈ support F, x ∈ W i → x ∉ W j) →
      Module.length R (sectionsOn F ⊤) = ∑ i, Module.length R (sectionsOn F (W i)) := by
  intro X F _ R _ _ ι _ W hcov hdisj
  rw [(LinearEquiv.ofBijective _
    (sectionsOn_res_pi_bijective_of_separating F R W hcov hdisj)).length_eq,
    Module.length_pi_of_fintype]

end GlobalTheory
