import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.CechCobGlue

/- English proof (translation)
Express the relevant statement in the definitionally equal form `((X.presheaf.map (homOfLE h₁).op ≫ X.presheaf.map (homOfLE h₂).op).hom) a = _`. Rewrite using `[← Functor.map_comp]`. Both sides reduce to the same expression.
-/
theorem resG_comp {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (a : Γ(X, U)) :
    resG X h₂ (resG X h₁ a) = resG X (h₂.trans h₁) a := by
  change ((X.presheaf.map (homOfLE h₁).op ≫ X.presheaf.map (homOfLE h₂).op).hom) a = _
  rw [← Functor.map_comp]
  rfl

/- English proof (translation)
Introduce `Y J W κ σ hcov E hE h' hh'`. Establish `hcovi : ∀ i, W i ≤ ⨆ k, (W i ⊓ W (σ k))`. Introduce `i x hx`. Establish `hx' : x ∈ (⨆ k, W (σ k))` using `by rw [hcov]; trivial`. Take `⟨k, hk⟩` from `TopologicalSpace.Opens.mem_iSup.1 hx'`.

Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx, hk⟩`. Set `f : ∀ i k, Γ(Y, W i ⊓ W (σ k))` to `fun i k => E i (σ k) + resG Y inf_le_right (h' k)`. Establish `hf : ∀ i k k', resG Y (inf_le_left : (W i ⊓ W (σ k)) ⊓ (W i ⊓ W (σ k')) ≤ W i ⊓ W (σ k)) (f i k) = resG Y (inf_le_right : (W i ⊓ W (σ k)) ⊓ (W i ⊓ W (σ k')) ≤ W i ⊓ W (σ k')) (f i k')`. Introduce `i k k'`. Establish `hPT : (W i ⊓ W (σ k)) ⊓ (W i ⊓ W (σ k')) ≤ W i ⊓ W (σ k) ⊓ W (σ k')` using `le_inf inf_le_left (inf_le_right.trans inf_le_right)`.

Establish `e1` using `congrArg (resG Y hPT) (hE i (σ k) (σ k'))`. Establish `e2` using `congrArg (resG Y (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) : (W i ⊓ W (σ k)) ⊓ (W i ⊓ W (σ k')) ≤ W (σ k) ⊓ W (σ k'))) (hh' k k')`. Simplify using `only [map_add, map_sub, resG_comp] at e1 e2`. Simplify using `only [f, map_add, resG_comp]`. Take the linear combination `e1 - e2`.

Establish `hg : ∀ i, ∃ s : Γ(Y, W i), ∀ k, resG Y (inf_le_left : W i ⊓ W (σ k) ≤ W i) s = f i k`. Introduce `i`. Take `⟨s, hs, -⟩` from `Y.sheaf.existsUnique_gluing' (fun k => W i ⊓ W (σ k)) (W i) (fun k => homOfLE (inf_le_left : W i ⊓ W (σ k) ≤ W i)) (hcovi i) (fun k => f i k) (fun k k' => hf i k k')`. Conclude with `⟨s, hs⟩`. Use `choose h hh using hg`.

Use `⟨h, fun i i' => ?_⟩` and prove the remaining obligations. Establish `hcov2 : W i ⊓ W i' ≤ ⨆ k, (W i ⊓ W i' ⊓ W (σ k))`. Introduce `x hx`. Establish `hx' : x ∈ (⨆ k, W (σ k))` using `by rw [hcov]; trivial`. Take `⟨k, hk⟩` from `TopologicalSpace.Opens.mem_iSup.1 hx'`.

Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx, hk⟩`. Apply `Y.sheaf.eq_of_locally_eq' (fun k => W i ⊓ W i' ⊓ W (σ k)) (W i ⊓ W i') (fun k => homOfLE (inf_le_left : W i ⊓ W i' ⊓ W (σ k) ≤ W i ⊓ W i')) hcov2` to reduce the goal to its premises. Introduce `k`. Use `show resG Y inf_le_left (E i i') = resG Y inf_le_left (resG Y inf_le_left (h i) - resG Y inf_le_right (h i'))`. Establish `A` using `congrArg (resG Y (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W (σ k) ≤ W i ⊓ W (σ k))) (hh i k)`.

Establish `B` using `congrArg (resG Y (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W (σ k) ≤ W i' ⊓ W (σ k))) (hh i' k)`. Establish `C` using `hE i i' (σ k)`. Simplify using `only [f, map_add, resG_comp] at A B`. Simplify using `only [map_sub, resG_comp]`. Take the linear combination `C - A + B`.
-/
theorem cocycle_coboundary_of_subcover : ∀ (Y : Scheme.{0}) (J : Type) (W : J → Y.Opens) (κ : Type) (σ : κ → J), ⨆ k, W (σ k) = ⊤ → ∀ (E : ∀ i i' : J, Γ(Y, W i ⊓ W i')), (∀ i i' i'', resG Y (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (E i i') + resG Y (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (E i' i'') = resG Y (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (E i i'')) → ∀ (h' : ∀ k, Γ(Y, W (σ k))), (∀ k k', E (σ k) (σ k') = resG Y inf_le_left (h' k) - resG Y inf_le_right (h' k')) → ∃ h : ∀ i, Γ(Y, W i), ∀ i i', E i i' = resG Y inf_le_left (h i) - resG Y inf_le_right (h i') := by
  intro Y J W κ σ hcov E hE h' hh'
  have hcovi : ∀ i, W i ≤ ⨆ k, (W i ⊓ W (σ k)) := by
    intro i x hx
    have hx' : x ∈ (⨆ k, W (σ k)) := by rw [hcov]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx'
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx, hk⟩
  let f : ∀ i k, Γ(Y, W i ⊓ W (σ k)) := fun i k => E i (σ k) + resG Y inf_le_right (h' k)
  have hf : ∀ i k k', resG Y (inf_le_left : (W i ⊓ W (σ k)) ⊓ (W i ⊓ W (σ k')) ≤ W i ⊓ W (σ k)) (f i k)
      = resG Y (inf_le_right : (W i ⊓ W (σ k)) ⊓ (W i ⊓ W (σ k')) ≤ W i ⊓ W (σ k')) (f i k') := by
    intro i k k'
    have hPT : (W i ⊓ W (σ k)) ⊓ (W i ⊓ W (σ k')) ≤ W i ⊓ W (σ k) ⊓ W (σ k') :=
      le_inf inf_le_left (inf_le_right.trans inf_le_right)
    have e1 := congrArg (resG Y hPT) (hE i (σ k) (σ k'))
    have e2 := congrArg (resG Y (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
      (W i ⊓ W (σ k)) ⊓ (W i ⊓ W (σ k')) ≤ W (σ k) ⊓ W (σ k'))) (hh' k k')
    simp only [map_add, map_sub, resG_comp] at e1 e2
    simp only [f, map_add, resG_comp]
    linear_combination e1 - e2
  have hg : ∀ i, ∃ s : Γ(Y, W i), ∀ k, resG Y (inf_le_left : W i ⊓ W (σ k) ≤ W i) s = f i k := by
    intro i
    obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' (fun k => W i ⊓ W (σ k)) (W i)
      (fun k => homOfLE (inf_le_left : W i ⊓ W (σ k) ≤ W i)) (hcovi i) (fun k => f i k)
      (fun k k' => hf i k k')
    exact ⟨s, hs⟩
  choose h hh using hg
  refine ⟨h, fun i i' => ?_⟩
  have hcov2 : W i ⊓ W i' ≤ ⨆ k, (W i ⊓ W i' ⊓ W (σ k)) := by
    intro x hx
    have hx' : x ∈ (⨆ k, W (σ k)) := by rw [hcov]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx'
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx, hk⟩
  apply Y.sheaf.eq_of_locally_eq' (fun k => W i ⊓ W i' ⊓ W (σ k)) (W i ⊓ W i')
    (fun k => homOfLE (inf_le_left : W i ⊓ W i' ⊓ W (σ k) ≤ W i ⊓ W i')) hcov2
  intro k
  show resG Y inf_le_left (E i i') = resG Y inf_le_left (resG Y inf_le_left (h i) - resG Y inf_le_right (h i'))
  have A := congrArg (resG Y (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
    W i ⊓ W i' ⊓ W (σ k) ≤ W i ⊓ W (σ k))) (hh i k)
  have B := congrArg (resG Y (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
    W i ⊓ W i' ⊓ W (σ k) ≤ W i' ⊓ W (σ k))) (hh i' k)
  have C := hE i i' (σ k)
  simp only [f, map_add, resG_comp] at A B
  simp only [map_sub, resG_comp]
  linear_combination C - A + B

end GlobalTheory.CechCobGlue
