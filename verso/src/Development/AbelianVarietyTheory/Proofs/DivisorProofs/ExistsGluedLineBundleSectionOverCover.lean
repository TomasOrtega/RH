import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocSecZero
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.ThBdl

/- English proof (translation)
Simplify using `only [resG]`. Rewrite using `[← CommRingCat.comp_apply, ← Functor.map_comp]`. Both sides reduce to the same expression.
-/
theorem resG_resG_glue {X : Scheme.{0}} {A B C : X.Opens} (h : B ≤ A) (h' : C ≤ B) (f : Γ(X, A)) :
    resG X h' (resG X h f) = resG X (h'.trans h) f := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/- English proof (translation)
Introduce `S G L V κ N s hN hV hs hc`. Establish `hmem : ∀ x : G.left, G.hom.base x ∈ V → ∃ k, G.hom.base x ∈ N k`. Introduce `x hx`. Establish `: G.hom.base x ∈ (⨆ k, N k)` using `by rw [hV]; exact hx`. Conclude with `TopologicalSpace.Opens.mem_iSup.1 this`.

Establish `hcov : ∀ i, L.U i ⊓ G.hom ⁻¹ᵁ V ≤ ⨆ k, (L.U i ⊓ G.hom ⁻¹ᵁ N k)`. Introduce `i x hx`. Take `⟨k, hk⟩` from `hmem x hx.2`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx.1, hk⟩`. Establish `hWV : ∀ i k, L.U i ⊓ G.hom ⁻¹ᵁ N k ≤ L.U i ⊓ G.hom ⁻¹ᵁ V` using `fun i k _ hx => ⟨hx.1, hN k hx.2⟩`.

Establish `hglue : ∀ i, ∃! t : Γ(G.left, L.U i ⊓ G.hom ⁻¹ᵁ V), ∀ k, resG _ (hWV i k) t = s k i`. Introduce `i`. Use `G.left.sheaf.existsUnique_gluing' (fun k => L.U i ⊓ G.hom ⁻¹ᵁ N k) (L.U i ⊓ G.hom ⁻¹ᵁ V) (fun k => homOfLE (hWV i k)) (hcov i) (fun k => s k i) ?_` and prove the remaining obligations. Introduce `k k'`. Establish `hle : (L.U i ⊓ G.hom ⁻¹ᵁ N k) ⊓ (L.U i ⊓ G.hom ⁻¹ᵁ N k') ≤ L.U i ⊓ G.hom ⁻¹ᵁ (N k ⊓ N k')` using `fun _ hx => ⟨hx.1.1, hx.1.2, hx.2.2⟩`.

Establish `e` using `congrArg (resG _ hle) (hc k k' i)`. Conclude with `(resG_resG_glue _ _ _).symm.trans (e.trans (resG_resG_glue _ _ _))`. Use `choose s' hs' _ using hglue`. Use `⟨s', ?_, fun k i => hs' i k⟩` and prove the remaining obligations. Introduce `i j`.

Establish `hTV : ∀ k, L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ N k ≤ L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ V` using `fun k _ hx => ⟨hx.1, hN k hx.2⟩`. Use `G.left.sheaf.eq_of_locally_eq' (fun k => L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ N k) (L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ V) (fun k => homOfLE (hTV k)) ?_ _ _ ?_` and prove the remaining obligations. Introduce `x hx`. Take `⟨k, hk⟩` from `hmem x hx.2`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx.1, hk⟩`.

Introduce `k`. Establish `hi1 : L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ N k ≤ L.U i ⊓ G.hom ⁻¹ᵁ N k` using `fun _ hx => ⟨hx.1.1, hx.2⟩`. Establish `hj1 : L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ N k ≤ L.U j ⊓ G.hom ⁻¹ᵁ N k` using `fun _ hx => ⟨hx.1.2, hx.2⟩`. Establish `e1 : resG _ (hi1.trans (hWV i k)) (s' i) = resG _ hi1 (s k i)`. Rewrite using `[← hs' i k, resG_resG_glue]`.

Establish `e2 : resG _ (hj1.trans (hWV j k)) (s' j) = resG _ hj1 (s k j)`. Rewrite using `[← hs' j k, resG_resG_glue]`. Express the relevant statement in the definitionally equal form `resG _ (hTV k) (resG _ _ (s' i)) = resG _ (hTV k) (resG _ _ (L.g i j : Γ(G.left, L.U i ⊓ L.U j)) * resG _ _ (s' j))`. Rewrite using `[map_mul]`. Use `((resG_resG_glue _ _ _).trans e1).trans ((hs k i j).trans ?_)` and prove the remaining obligations.

Use `congr 1`. Conclude with `(resG_resG_glue _ _ _).symm`. Conclude with `((resG_resG_glue _ _ _).trans e2).symm`.
-/
theorem locSec_glue : ∀ (S : Scheme.{0}) (G : Over S) (L : LB G.left) (V : S.Opens) (κ : Type) (N : κ → S.Opens)
    (s : ∀ k, LocSec G L (N k)) (hN : ∀ k, N k ≤ V), (⨆ k, N k) = V → (∀ k, IsLocSec (s k)) →
    (∀ k k' i, resG _ (fun _ hx => ⟨hx.1, hx.2.1⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N k ⊓ N k') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N k) (s k i) =
      resG _ (fun _ hx => ⟨hx.1, hx.2.2⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N k ⊓ N k') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N k') (s k' i)) →
    ∃ s' : LocSec G L V, IsLocSec s' ∧ ∀ k i,
      resG _ (fun _ hx => ⟨hx.1, hN k hx.2⟩ : L.U i ⊓ G.hom ⁻¹ᵁ N k ≤ L.U i ⊓ G.hom ⁻¹ᵁ V) (s' i) = s k i := by
  intro S G L V κ N s hN hV hs hc
  have hmem : ∀ x : G.left, G.hom.base x ∈ V → ∃ k, G.hom.base x ∈ N k := by
    intro x hx
    have : G.hom.base x ∈ (⨆ k, N k) := by rw [hV]; exact hx
    exact TopologicalSpace.Opens.mem_iSup.1 this
  have hcov : ∀ i, L.U i ⊓ G.hom ⁻¹ᵁ V ≤ ⨆ k, (L.U i ⊓ G.hom ⁻¹ᵁ N k) := by
    intro i x hx
    obtain ⟨k, hk⟩ := hmem x hx.2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx.1, hk⟩
  have hWV : ∀ i k, L.U i ⊓ G.hom ⁻¹ᵁ N k ≤ L.U i ⊓ G.hom ⁻¹ᵁ V := fun i k _ hx => ⟨hx.1, hN k hx.2⟩
  have hglue : ∀ i, ∃! t : Γ(G.left, L.U i ⊓ G.hom ⁻¹ᵁ V), ∀ k, resG _ (hWV i k) t = s k i := by
    intro i
    refine G.left.sheaf.existsUnique_gluing' (fun k => L.U i ⊓ G.hom ⁻¹ᵁ N k) (L.U i ⊓ G.hom ⁻¹ᵁ V)
      (fun k => homOfLE (hWV i k)) (hcov i) (fun k => s k i) ?_
    intro k k'
    have hle : (L.U i ⊓ G.hom ⁻¹ᵁ N k) ⊓ (L.U i ⊓ G.hom ⁻¹ᵁ N k') ≤ L.U i ⊓ G.hom ⁻¹ᵁ (N k ⊓ N k') :=
      fun _ hx => ⟨hx.1.1, hx.1.2, hx.2.2⟩
    have e := congrArg (resG _ hle) (hc k k' i)
    exact (resG_resG_glue _ _ _).symm.trans (e.trans (resG_resG_glue _ _ _))
  choose s' hs' _ using hglue
  refine ⟨s', ?_, fun k i => hs' i k⟩
  intro i j
  have hTV : ∀ k, L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ N k ≤ L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ V := fun k _ hx => ⟨hx.1, hN k hx.2⟩
  refine G.left.sheaf.eq_of_locally_eq' (fun k => L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ N k) (L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ V)
    (fun k => homOfLE (hTV k)) ?_ _ _ ?_
  · intro x hx
    obtain ⟨k, hk⟩ := hmem x hx.2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx.1, hk⟩
  · intro k
    have hi1 : L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ N k ≤ L.U i ⊓ G.hom ⁻¹ᵁ N k := fun _ hx => ⟨hx.1.1, hx.2⟩
    have hj1 : L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ N k ≤ L.U j ⊓ G.hom ⁻¹ᵁ N k := fun _ hx => ⟨hx.1.2, hx.2⟩
    have e1 : resG _ (hi1.trans (hWV i k)) (s' i) = resG _ hi1 (s k i) := by
      rw [← hs' i k, resG_resG_glue]
    have e2 : resG _ (hj1.trans (hWV j k)) (s' j) = resG _ hj1 (s k j) := by
      rw [← hs' j k, resG_resG_glue]
    change resG _ (hTV k) (resG _ _ (s' i)) =
      resG _ (hTV k) (resG _ _ (L.g i j : Γ(G.left, L.U i ⊓ L.U j)) * resG _ _ (s' j))
    rw [map_mul]
    refine ((resG_resG_glue _ _ _).trans e1).trans ((hs k i j).trans ?_)
    congr 1
    · exact (resG_resG_glue _ _ _).symm
    · exact ((resG_resG_glue _ _ _).trans e2).symm

end GlobalTheory.UMin.ThBdl
