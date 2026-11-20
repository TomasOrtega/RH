import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOpenNonzeroLocusOfUniversallyClosed
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.TupleGlue

/- English proof (translation)
Rewrite using `[← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]`. Both sides reduce to the same expression.
-/
private theorem rr {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(X, U)) :
    resG X h₂ (resG X h₁ s) = resG X (h₂.trans h₁) s := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

variable {X : Scheme.{0}} {N : X.Opens} {J : Type}

/- English proof (translation)
Establish `hu : IsUnit (resG X (X.basicOpen_le s) s)` using `X.toRingedSpace.isUnit_res_basicOpen s`. Use `hu.map (resG X h)` as an intermediate fact. Rewrite `this` using `[rr]`. Then use the resulting hypothesis.
-/
private theorem isUnit_res (s : Γ(X, N)) {W : X.Opens} (h : W ≤ X.basicOpen s) :
    IsUnit (resG X (h.trans (X.basicOpen_le s)) s) := by
  have hu : IsUnit (resG X (X.basicOpen_le s) s) := X.toRingedSpace.isUnit_res_basicOpen s
  have := hu.map (resG X h)
  rwa [rr] at this

/- English proof (translation)
Use `X.sheaf.eq_of_locally_eq' (fun i => X.basicOpen (v i)) N (fun i => homOfLE (X.basicOpen_le _)) hv a b fun i => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `resG X (X.basicOpen_le (v i)) a = resG X (X.basicOpen_le (v i)) b`. Apply `(isUnit_res (v i) le_rfl).mul_right_cancel` to reduce the goal to its premises. Use `congrArg (resG X (X.basicOpen_le (v i))) (h i)` as an intermediate fact. Rewrite `this` using `[map_mul, map_mul]`. Then use the resulting hypothesis.
-/
theorem eq_of_mul_eq (v : J → Γ(X, N)) (hv : N ≤ ⨆ i, X.basicOpen (v i)) {a b : Γ(X, N)}
    (h : ∀ i, a * v i = b * v i) : a = b := by
  refine X.sheaf.eq_of_locally_eq' (fun i => X.basicOpen (v i)) N
    (fun i => homOfLE (X.basicOpen_le _)) hv a b fun i => ?_
  change resG X (X.basicOpen_le (v i)) a = resG X (X.basicOpen_le (v i)) b
  apply (isUnit_res (v i) le_rfl).mul_right_cancel
  have := congrArg (resG X (X.basicOpen_le (v i))) (h i)
  rwa [map_mul, map_mul] at this

/- English proof (translation)
Establish `hq : ∀ i, ∃ q : Γ(X, X.basicOpen (v i)), resG X (X.basicOpen_le (v i)) (u i) = q * resG X (X.basicOpen_le (v i)) (v i)` using `fun i => ⟨resG X (X.basicOpen_le (v i)) (u i) * ↑(isUnit_res (v i) le_rfl).unit⁻¹, by`. Rewrite using `[_root_.mul_assoc, IsUnit.val_inv_mul, _root_.mul_one]⟩`. Use `choose q hq using hq`. Establish `hcomp : TopCat.Presheaf.IsCompatible X.sheaf.1 (fun i => X.basicOpen (v i)) q`. Introduce `i j`.

Express the relevant statement in the definitionally equal form `resG X (inf_le_left : X.basicOpen (v i) ⊓ X.basicOpen (v j) ≤ _) (q i) = resG X (inf_le_right : X.basicOpen (v i) ⊓ X.basicOpen (v j) ≤ _) (q j)`. Establish `e1` using `congrArg (resG X (inf_le_left : X.basicOpen (v i) ⊓ X.basicOpen (v j) ≤ _)) (hq i)`. Establish `e2` using `congrArg (resG X (inf_le_right : X.basicOpen (v i) ⊓ X.basicOpen (v j) ≤ _)) (hq j)`. Rewrite `e1`, `e2` using `[map_mul, rr, rr]`. Establish `e3` using `congrArg (resG X ((inf_le_left : X.basicOpen (v i) ⊓ X.basicOpen (v j) ≤ _).trans (X.basicOpen_le (v i)))) (h i j)`.

Rewrite `e3` using `[map_mul, map_mul, e1, e2]`. Establish `ui` using `isUnit_res (v i) (inf_le_left : X.basicOpen (v i) ⊓ X.basicOpen (v j) ≤ _)`. Establish `uj` using `isUnit_res (v j) (inf_le_right : X.basicOpen (v i) ⊓ X.basicOpen (v j) ≤ _)`. Apply `(ui.mul uj).mul_right_cancel` to reduce the goal to its premises. Take the linear combination `e3`.

Take `⟨r₀, hr, -⟩` from `X.sheaf.existsUnique_gluing' (fun i => X.basicOpen (v i)) N (fun i => homOfLE (X.basicOpen_le _)) hv q hcomp`. Set `r : Γ(X, N)` to `r₀`. Use `⟨r, fun j => ?_⟩` and prove the remaining obligations. Use `X.sheaf.eq_of_locally_eq' (fun i => X.basicOpen (v i)) N (fun i => homOfLE (X.basicOpen_le _)) hv (u j) (r * v j) fun i => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `resG X (X.basicOpen_le (v i)) (u j) = resG X (X.basicOpen_le (v i)) (r * v j)`.

Establish `hri : resG X (X.basicOpen_le (v i)) r = q i` using `hr i`. Rewrite using `[map_mul, hri]`. Apply `(isUnit_res (v i) le_rfl).mul_right_cancel` to reduce the goal to its premises. Establish `e3` using `congrArg (resG X (X.basicOpen_le (v i))) (h i j)`. Rewrite `e3` using `[map_mul, map_mul, hq i]`.

Take the linear combination `-e3`.
-/
theorem exists_mul (u v : J → Γ(X, N)) (hv : N ≤ ⨆ i, X.basicOpen (v i))
    (h : ∀ i j, u i * v j = u j * v i) : ∃ r : Γ(X, N), ∀ j, u j = r * v j := by
  have hq : ∀ i, ∃ q : Γ(X, X.basicOpen (v i)), resG X (X.basicOpen_le (v i)) (u i) =
      q * resG X (X.basicOpen_le (v i)) (v i) := fun i =>
    ⟨resG X (X.basicOpen_le (v i)) (u i) * ↑(isUnit_res (v i) le_rfl).unit⁻¹, by
      rw [_root_.mul_assoc, IsUnit.val_inv_mul, _root_.mul_one]⟩
  choose q hq using hq
  have hcomp : TopCat.Presheaf.IsCompatible X.sheaf.1 (fun i => X.basicOpen (v i)) q := by
    intro i j
    change resG X (inf_le_left : X.basicOpen (v i) ⊓ X.basicOpen (v j) ≤ _) (q i) =
      resG X (inf_le_right : X.basicOpen (v i) ⊓ X.basicOpen (v j) ≤ _) (q j)
    have e1 := congrArg (resG X (inf_le_left : X.basicOpen (v i) ⊓ X.basicOpen (v j) ≤ _)) (hq i)
    have e2 := congrArg (resG X (inf_le_right : X.basicOpen (v i) ⊓ X.basicOpen (v j) ≤ _)) (hq j)
    rw [map_mul, rr, rr] at e1 e2
    have e3 := congrArg (resG X ((inf_le_left : X.basicOpen (v i) ⊓ X.basicOpen (v j) ≤ _).trans
      (X.basicOpen_le (v i)))) (h i j)
    rw [map_mul, map_mul, e1, e2] at e3
    have ui := isUnit_res (v i) (inf_le_left : X.basicOpen (v i) ⊓ X.basicOpen (v j) ≤ _)
    have uj := isUnit_res (v j) (inf_le_right : X.basicOpen (v i) ⊓ X.basicOpen (v j) ≤ _)
    apply (ui.mul uj).mul_right_cancel
    linear_combination e3
  obtain ⟨r₀, hr, -⟩ := X.sheaf.existsUnique_gluing' (fun i => X.basicOpen (v i)) N
    (fun i => homOfLE (X.basicOpen_le _)) hv q hcomp
  let r : Γ(X, N) := r₀
  refine ⟨r, fun j => ?_⟩
  refine X.sheaf.eq_of_locally_eq' (fun i => X.basicOpen (v i)) N
    (fun i => homOfLE (X.basicOpen_le _)) hv (u j) (r * v j) fun i => ?_
  change resG X (X.basicOpen_le (v i)) (u j) = resG X (X.basicOpen_le (v i)) (r * v j)
  have hri : resG X (X.basicOpen_le (v i)) r = q i := hr i
  rw [map_mul, hri]
  apply (isUnit_res (v i) le_rfl).mul_right_cancel
  have e3 := congrArg (resG X (X.basicOpen_le (v i))) (h i j)
  rw [map_mul, map_mul, hq i] at e3
  linear_combination -e3

/- English proof (translation)
Take `⟨r, hr⟩` from `exists_mul u v hv h`. Take `⟨r', hr'⟩` from `exists_mul v u hu fun i j => by linear_combination h j i`. Establish `h1 : r * r' = 1` using `eq_of_mul_eq u hu fun i => by`. Rewrite using `[_root_.mul_assoc, ← hr', ← hr, _root_.one_mul]`. Conclude with `⟨⟨r, r', h1, by rw [_root_.mul_comm, h1]⟩, hr⟩`.
-/
theorem exists_unit_mul (u v : J → Γ(X, N)) (hu : N ≤ ⨆ i, X.basicOpen (u i))
    (hv : N ≤ ⨆ i, X.basicOpen (v i))
    (h : ∀ i j, u i * v j = u j * v i) : ∃ r : Γ(X, N)ˣ, ∀ j, u j = r * v j := by
  obtain ⟨r, hr⟩ := exists_mul u v hv h
  obtain ⟨r', hr'⟩ := exists_mul v u hu fun i j => by linear_combination h j i
  have h1 : r * r' = 1 := eq_of_mul_eq u hu fun i => by
    rw [_root_.mul_assoc, ← hr', ← hr, _root_.one_mul]
  exact ⟨⟨r, r', h1, by rw [_root_.mul_comm, h1]⟩, hr⟩

/- English proof (translation)
Introduce `x hx`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 (hv (e hx))`. Use `TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩` and prove the remaining obligations. Use `erw [Scheme.basicOpen_res]`. Conclude with `⟨hx, hi⟩`.
-/
private theorem cover_res {U : X.Opens} (e : N ≤ U) (v : J → Γ(X, U))
    (hv : U ≤ ⨆ i, X.basicOpen (v i)) : N ≤ ⨆ i, X.basicOpen (resG X e (v i)) := by
  intro x hx
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hv (e hx))
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩
  erw [Scheme.basicOpen_res]
  exact ⟨hx, hi⟩

/- English proof (translation)
Introduce `X A J V t hV h`. Use `choose g hg using fun a a' => exists_unit_mul (fun i => resG X (inf_le_left : V a ⊓ V a' ≤ V a) (t a i)) (fun i => resG X (inf_le_right : V a ⊓ V a' ≤ V a') (t a' i)) (cover_res _ _ (hV a)) (cover_res _ _ (hV a')) (h a a')`. Conclude with `⟨g, fun i => ⟨fun a => t a i, fun a a' => hg a a' i⟩, fun _ _ => rfl⟩`.
-/
theorem exists_sections : ∀ (X : Scheme.{0}) (A J : Type) (V : A → X.Opens) (t : ∀ a, J → Γ(X, V a)), (∀ a, V a ≤ ⨆ i, X.basicOpen (t a i)) → (∀ a a' i j, resG X (inf_le_left : V a ⊓ V a' ≤ V a) (t a i) * resG X (inf_le_right : V a ⊓ V a' ≤ V a') (t a' j) = resG X (inf_le_left : V a ⊓ V a' ≤ V a) (t a j) * resG X (inf_le_right : V a ⊓ V a' ≤ V a') (t a' i)) → ∃ (g : ∀ a a', Γ(X, V a ⊓ V a')ˣ) (T : J → LB.Sec (⟨A, V, g⟩ : LB X)), ∀ i a, (T i).f a = t a i := by
  intro X A J V t hV h
  choose g hg using fun a a' => exists_unit_mul
    (fun i => resG X (inf_le_left : V a ⊓ V a' ≤ V a) (t a i))
    (fun i => resG X (inf_le_right : V a ⊓ V a' ≤ V a') (t a' i))
    (cover_res _ _ (hV a)) (cover_res _ _ (hV a')) (h a a')
  exact ⟨g, fun i => ⟨fun a => t a i, fun a a' => hg a a' i⟩, fun _ _ => rfl⟩

end GlobalTheory.TupleGlue
