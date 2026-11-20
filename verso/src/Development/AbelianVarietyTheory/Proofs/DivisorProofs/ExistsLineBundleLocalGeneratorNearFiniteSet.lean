import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsPatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionFamilyZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLocalSectionFamilyUnitAtPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLocalSectionFamilyUnitAtFinitePointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalUnitGeneratorOfLineBundleLocalSectionStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Pinch.Semiloc

/- English proof (translation)
Introduce `X L hL W hW`. Establish `h : ∀ x : W, ∃ (f : Γ(X, W)) (i : L.ι), X.basicOpen f ≤ L.U i ∧ (x : X) ∈ X.basicOpen f`. Introduce `x`. Take `⟨i, hi⟩` from `ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hL (x : X)`. Take `⟨f, hf, hxf⟩` from `hW.exists_basicOpen_le (V := L.U i) ⟨x, hi⟩ x.2`.

Conclude with `⟨f, i, hf, hxf⟩`. Use `choose f i hf hx using h`. Take `⟨s, hs⟩` from `hW.isCompact.elim_finite_subcover (fun x : W => (X.basicOpen (f x) : Set X)) (fun x => (X.basicOpen (f x)).isOpen) (fun x hxW => Set.mem_iUnion.2 ⟨⟨x, hxW⟩, hx ⟨x, hxW⟩⟩)`. Use `⟨s, inferInstance, fun j => f j, fun j => i j, fun j => hf j, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨j, hj, hxj⟩` from `Set.mem_iUnion₂.1 (hs hx)`.

Conclude with `⟨⟨j, hj⟩, hxj⟩`.
-/
theorem exists_basicOpen_cover : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (W : X.Opens), IsAffineOpen W → ∃ (J : Type) (_ : Fintype J) (f : J → Γ(X, W)) (k : J → L.ι), (∀ j, X.basicOpen (f j) ≤ L.U (k j)) ∧ ∀ x ∈ W, ∃ j, x ∈ X.basicOpen (f j) := by
  intro X L hL W hW
  classical
  have h : ∀ x : W, ∃ (f : Γ(X, W)) (i : L.ι), X.basicOpen f ≤ L.U i ∧ (x : X) ∈ X.basicOpen f := by
    intro x
    obtain ⟨i, hi⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hL (x : X)
    obtain ⟨f, hf, hxf⟩ := hW.exists_basicOpen_le (V := L.U i) ⟨x, hi⟩ x.2
    exact ⟨f, i, hf, hxf⟩
  choose f i hf hx using h
  obtain ⟨s, hs⟩ := hW.isCompact.elim_finite_subcover (fun x : W => (X.basicOpen (f x) : Set X))
    (fun x => (X.basicOpen (f x)).isOpen) (fun x hxW => Set.mem_iUnion.2 ⟨⟨x, hxW⟩, hx ⟨x, hxW⟩⟩)
  refine ⟨s, inferInstance, fun j => f j, fun j => i j, fun j => hf j, fun x hx => ?_⟩
  obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.1 (hs hx)
  exact ⟨⟨j, hj⟩, hxj⟩

/- English proof (translation)
Introduce `X W hW F hF hFW hsp`. Establish `hb : ∀ x ∈ F, ∀ y ∈ F, y ≠ x → ∃ b : Γ(X, W), x ∈ X.basicOpen b ∧ y ∉ X.basicOpen b`. Introduce `x hx y hy hne`. Establish `hn : ¬ y ⤳ x` using `fun h => hne (hsp x hx y hy h)`. Rewrite `hn` using `[specializes_iff_forall_open]`.

Use `push Not at hn`. Take `⟨O, hO, hxO, hyO⟩` from `hn`. Take `⟨b, hbO, hxb⟩` from `hW.exists_basicOpen_le (V := ⟨O, hO⟩) ⟨x, hxO⟩ (hFW hx)`. Conclude with `⟨b, hxb, fun h => hyO (hbO h)⟩`. Use `choose! b hb1 hb2 using hb`.

Use `⟨fun x => ∏ y ∈ hF.toFinset.erase x, b x y, fun x hx => ?_, fun x hx y hy hne h => ?_⟩` and prove the remaining obligations. Use `Finset.prod_induction _ (fun c => x ∈ X.basicOpen c) (fun c d hc hd => ?_) ?_ (fun y hy => ?_)` and prove the remaining obligations. Rewrite using `[Scheme.basicOpen_mul]`. Conclude with `⟨hc, hd⟩`. Rewrite using `[Scheme.basicOpen_of_isUnit _ isUnit_one]`.

Conclude with `hFW hx`. Take `⟨hyx, hyF⟩` from `Finset.mem_erase.1 hy`. Conclude with `hb1 x hx y (hF.mem_toFinset.1 hyF) hyx`. Establish `hmem : y ∈ hF.toFinset.erase x` using `Finset.mem_erase.2 ⟨hne, hF.mem_toFinset.2 hy⟩ dsimp only at h`. Rewrite `h` using `[← Finset.mul_prod_erase _ _ hmem, Scheme.basicOpen_mul]`.

Conclude with `hb2 x hx y hy hne h.1`.
-/
theorem exists_separating : ∀ (X : Scheme.{0}) (W : X.Opens), IsAffineOpen W → ∀ (F : Set X), F.Finite → F ⊆ W → (∀ x ∈ F, ∀ y ∈ F, y ⤳ x → y = x) → ∃ a : X → Γ(X, W), (∀ x ∈ F, x ∈ X.basicOpen (a x)) ∧ ∀ x ∈ F, ∀ y ∈ F, y ≠ x → y ∉ X.basicOpen (a x) := by
  intro X W hW F hF hFW hsp
  classical
  have hb : ∀ x ∈ F, ∀ y ∈ F, y ≠ x → ∃ b : Γ(X, W), x ∈ X.basicOpen b ∧ y ∉ X.basicOpen b := by
    intro x hx y hy hne
    have hn : ¬ y ⤳ x := fun h => hne (hsp x hx y hy h)
    rw [specializes_iff_forall_open] at hn
    push Not at hn
    obtain ⟨O, hO, hxO, hyO⟩ := hn
    obtain ⟨b, hbO, hxb⟩ := hW.exists_basicOpen_le (V := ⟨O, hO⟩) ⟨x, hxO⟩ (hFW hx)
    exact ⟨b, hxb, fun h => hyO (hbO h)⟩
  choose! b hb1 hb2 using hb
  refine ⟨fun x => ∏ y ∈ hF.toFinset.erase x, b x y, fun x hx => ?_, fun x hx y hy hne h => ?_⟩
  · refine Finset.prod_induction _ (fun c => x ∈ X.basicOpen c) (fun c d hc hd => ?_) ?_ (fun y hy => ?_)
    · rw [Scheme.basicOpen_mul]; exact ⟨hc, hd⟩
    · rw [Scheme.basicOpen_of_isUnit _ isUnit_one]; exact hFW hx
    · obtain ⟨hyx, hyF⟩ := Finset.mem_erase.1 hy
      exact hb1 x hx y (hF.mem_toFinset.1 hyF) hyx
  · have hmem : y ∈ hF.toFinset.erase x := Finset.mem_erase.2 ⟨hne, hF.mem_toFinset.2 hy⟩
    dsimp only at h
    rw [← Finset.mul_prod_erase _ _ hmem, Scheme.basicOpen_mul] at h
    exact hb2 x hx y hy hne h.1

/- English proof (translation)
Introduce `X L hL W hW F hF hFW`. Take `⟨J, _, f, k, hk, hcov⟩` from `exists_basicOpen_cover X L hL W hW`. Use `set F' : Set X := {x | x ∈ F ∧ ∀ y ∈ F, x ⤳ y → y = x} with hF'`. Establish `hF'F : F' ⊆ F` using `fun x hx => hx.1`. Establish `hF'fin : F'.Finite` using `hF.subset hF'F`.

Establish `hup : ∀ x ∈ F, ∃ x' ∈ F', x ⤳ x'`. Introduce `x hx`. Take `⟨i, hi⟩` from `Set.Finite.exists_minimalFor (fun y : X => closure ({y} : Set X)) {y | y ∈ F ∧ x ⤳ y} (hF.subset fun y hy => hy.1) ⟨x, hx, specializes_rfl⟩`. Use `⟨i, ⟨hi.1.1, fun y hy hiy => ?_⟩, hi.1.2⟩` and prove the remaining obligations. Establish `h1 : closure ({y} : Set X) ⊆ closure {i}` using `specializes_iff_closure_subset.1 hiy`.

Establish `h2` using `hi.2 ⟨hy, hi.1.2.trans hiy⟩ h1`. Conclude with `((specializes_iff_closure_subset.2 h2).antisymm hiy).eq`. Take `⟨a, ha, ha'⟩` from `exists_separating X W hW F' hF'fin (hF'F.trans hFW) (fun x hx y hy hyx => (hy.2 x hx.1 hyx).symm)`. Establish `hE : ∀ x : X, ∃ e : ∀ j, Γ(X, X.basicOpen (f j)), x ∈ W → GlobalTheory.Pinch.IsSecFam L (fun j => X.basicOpen (f j)) k hk e ∧ ∀ j (h : x ∈ X.basicOpen (f j)), IsUnit ((X.presheaf.germ (X.basicOpen (f j)) x h).hom (e j))`. Introduce `x`.

Distinguish the cases in `hx : x ∈ W`. Take `⟨e, he⟩` from `GlobalTheory.T.exists_lineBundleLocalSectionFamily_unit_at_point X L hL W hW J f k hk x hx`. Conclude with `⟨e, fun _ => he⟩`. Conclude with `⟨fun _ => 0, fun h => absurd h hx⟩`. Use `choose E hE using hE`.

Take `⟨e, he, heu⟩` from `GlobalTheory.T.lineBundleLocalSectionFamily_unit_at_finite_points X L W J (fun j => X.basicOpen (f j)) (fun j => X.basicOpen_le (f j)) k hk F' hF'fin a ha ha' E (fun x hx => (hE x (hFW (hF'F hx))).1) (fun x hx => (hE x (hFW (hF'F hx))).2)`. Take `⟨V, u, hV, hgen⟩` from `GlobalTheory.T.exists_localUnitGenerator_of_lineBundleLocalSectionFamily X L hL J (fun j => X.basicOpen (f j)) k hk e he`. Use `⟨V, u, fun x hx => ?_, hgen⟩` and prove the remaining obligations. Take `⟨x', hx', hxx'⟩` from `hup x hx`. Take `⟨j, hj⟩` from `hcov x' (hFW (hF'F hx'))`.

Conclude with `hxx'.mem_open V.isOpen (hV j x' hj (heu x' hx' j hj))`.
-/
theorem exists_locGen_near_finite : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (W : X.Opens), IsAffineOpen W → ∀ F : Set X, F.Finite → F ⊆ W → ∃ (V : X.Opens) (a : ∀ k, Γ(X, V ⊓ L.U k)ˣ), F ⊆ V ∧ GlobalTheory.Pinch.LocGen L V a := by
  intro X L hL W hW F hF hFW
  classical
  obtain ⟨J, _, f, k, hk, hcov⟩ := exists_basicOpen_cover X L hL W hW
  set F' : Set X := {x | x ∈ F ∧ ∀ y ∈ F, x ⤳ y → y = x} with hF'
  have hF'F : F' ⊆ F := fun x hx => hx.1
  have hF'fin : F'.Finite := hF.subset hF'F
  have hup : ∀ x ∈ F, ∃ x' ∈ F', x ⤳ x' := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.Finite.exists_minimalFor (fun y : X => closure ({y} : Set X)) {y | y ∈ F ∧ x ⤳ y}
      (hF.subset fun y hy => hy.1) ⟨x, hx, specializes_rfl⟩
    refine ⟨i, ⟨hi.1.1, fun y hy hiy => ?_⟩, hi.1.2⟩
    have h1 : closure ({y} : Set X) ⊆ closure {i} := specializes_iff_closure_subset.1 hiy
    have h2 := hi.2 ⟨hy, hi.1.2.trans hiy⟩ h1
    exact ((specializes_iff_closure_subset.2 h2).antisymm hiy).eq
  obtain ⟨a, ha, ha'⟩ := exists_separating X W hW F' hF'fin (hF'F.trans hFW)
    (fun x hx y hy hyx => (hy.2 x hx.1 hyx).symm)
  have hE : ∀ x : X, ∃ e : ∀ j, Γ(X, X.basicOpen (f j)), x ∈ W →
      GlobalTheory.Pinch.IsSecFam L (fun j => X.basicOpen (f j)) k hk e ∧
        ∀ j (h : x ∈ X.basicOpen (f j)), IsUnit ((X.presheaf.germ (X.basicOpen (f j)) x h).hom (e j)) := by
    intro x
    by_cases hx : x ∈ W
    · obtain ⟨e, he⟩ := GlobalTheory.T.exists_lineBundleLocalSectionFamily_unit_at_point X L hL W hW J f k hk x hx
      exact ⟨e, fun _ => he⟩
    · exact ⟨fun _ => 0, fun h => absurd h hx⟩
  choose E hE using hE
  obtain ⟨e, he, heu⟩ := GlobalTheory.T.lineBundleLocalSectionFamily_unit_at_finite_points X L W J (fun j => X.basicOpen (f j)) (fun j => X.basicOpen_le (f j)) k hk F'
    hF'fin a ha ha' E (fun x hx => (hE x (hFW (hF'F hx))).1) (fun x hx => (hE x (hFW (hF'F hx))).2)
  obtain ⟨V, u, hV, hgen⟩ := GlobalTheory.T.exists_localUnitGenerator_of_lineBundleLocalSectionFamily X L hL J (fun j => X.basicOpen (f j)) k hk e he
  refine ⟨V, u, fun x hx => ?_, hgen⟩
  obtain ⟨x', hx', hxx'⟩ := hup x hx
  obtain ⟨j, hj⟩ := hcov x' (hFW (hF'F hx'))
  exact hxx'.mem_open V.isOpen (hV j x' hj (heu x' hx' j hj))

end GlobalTheory.Pinch.Semiloc
