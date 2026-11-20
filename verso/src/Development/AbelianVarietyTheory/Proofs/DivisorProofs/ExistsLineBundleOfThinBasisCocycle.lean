import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueTransitionUnitsCocycleThinBasisStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThinGlue

variable {X : Scheme.{0}}

/- English proof (translation)
Use `ext`. Simplify using `only [res, Units.coe_map, MonoidHom.coe_coe]`. Rewrite using `[← CommRingCat.comp_apply, ← Functor.map_comp]`. Both sides reduce to the same expression.
-/
theorem res_res {U W W' : X.Opens} (h : W ≤ U) (h' : W' ≤ W) (x : Γ(X, U)ˣ) :
    res h' (res h x) = res (h'.trans h) x := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/- English proof (translation)
Use `choose W' hW hp hxy using h`. Use `ext`. Use `TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun p : W => W' p.1 p.2) W (fun p => homOfLE (hW p.1 p.2)) ?_ _ _ ?_` and prove the remaining obligations. Introduce `p hpW`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨⟨p, hpW⟩, hp _ hpW⟩`.

Introduce `p`. Use `congrArg Units.val (hxy p.1 p.2)` as an intermediate fact. Conclude with `this`.
-/
theorem units_eq_of_local {W : X.Opens} (x y : Γ(X, W)ˣ)
    (h : ∀ p ∈ W, ∃ (W' : X.Opens) (hW : W' ≤ W), p ∈ W' ∧ res hW x = res hW y) : x = y := by
  choose W' hW hp hxy using h
  ext
  refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun p : W => W' p.1 p.2) W (fun p => homOfLE (hW p.1 p.2)) ?_ _ _ ?_
  · intro p hpW
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨p, hpW⟩, hp _ hpW⟩
  · intro p
    have := congrArg Units.val (hxy p.1 p.2)
    exact this

end GlobalTheory.ThinGlue

namespace GlobalTheory.ThinGlue

/- English proof (translation)
Introduce `X C _ V hV _ u hB hC`. Establish `hE` using `fun T₁ T₂ => GlobalTheory.T.existsUnique_transition_units_cocycle_thin_basis X C V hV u hB hC T₁ T₂`. Use `choose g hg using fun T₁ T₂ => (hE T₁ T₂).exists`. Establish `key : ∀ (T₁ T₂ S : C) (a : T₁ ⟶ S) (b : T₂ ⟶ S) (h : V S ≤ V T₁ ⊓ V T₂), res h (g T₁ T₂) * u T₁ S a = u T₂ S b` using `fun T₁ T₂ S a b _ => hg T₁ T₂ S a b`. Establish `bas2 : ∀ (i j : C) (W : X.Opens) (hW : W ≤ V i ⊓ V j) (x y : Γ(X, W)ˣ), (∀ (S : C) (_ : i ⟶ S) (_ : j ⟶ S) (hS : V S ≤ W), res hS x = res hS y) → x = y`.

Introduce `i j W hW x y h`. Use `units_eq_of_local x y fun p hp => ?_` and prove the remaining obligations. Take `⟨S, ⟨a⟩, ⟨b⟩, hpS, hSW⟩` from `hB.2 i j p W hp (hW hp).1 (hW hp).2`. Conclude with `⟨V S, hSW, hpS, h S a b hSW⟩`. Establish `bas3 : ∀ (i j k : C) (W : X.Opens) (hW : W ≤ V i ⊓ V j ⊓ V k) (x y : Γ(X, W)ˣ), (∀ (S : C) (_ : i ⟶ S) (_ : j ⟶ S) (_ : k ⟶ S) (hS : V S ≤ W), res hS x = res hS y) → x = y`.

Introduce `i j k W hW x y h`. Use `units_eq_of_local x y fun p hp => ?_` and prove the remaining obligations. Take `⟨S₀, ⟨a⟩, ⟨b⟩, hpS₀, hS₀W⟩` from `hB.2 i j p W hp (hW hp).1.1 (hW hp).1.2`. Take `⟨S, ⟨c⟩, ⟨d⟩, hpS, hSW⟩` from `hB.2 S₀ k p W hp hpS₀ (hW hp).2`. Conclude with `⟨V S, hSW, hpS, h S (a ≫ c) (b ≫ c) d hSW⟩`.

Establish `gself : ∀ T, g T T = 1` using `fun T => (hE T T).unique (hg T T) (fun S a b => by rw [Subsingleton.elim a b, map_one, _root_.one_mul])`. Set `L : LB X` to `⟨C, V, g⟩`. Use `⟨L, ⟨?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Use `eq_top_iff.2 fun p _ => ?_` and prove the remaining obligations. Take `⟨t, hp, _⟩` from `hB.1 p ⊤ trivial`.

Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨t, hp⟩`. Introduce `T show res _ (g T T) = 1`. Rewrite using `[gself, map_one]`. Introduce `i j k`. Use `bas3 i j k _ le_rfl _ _ fun S a b c hS => ?_` and prove the remaining obligations.

Use `show res hS (res _ (g i j) * res _ (g j k)) = res hS (res _ (g i k))`. Simplify using `only [map_mul, res_res]`. Establish `e1` using `key i j S a b (hS.trans inf_le_left)`. Establish `e2` using `key j k S b c (hS.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right))`. Establish `e3` using `key i k S a c (hS.trans (le_inf (inf_le_left.trans inf_le_left) inf_le_right))`.

Apply `mul_right_cancel (b := u i S a)` to reduce the goal to its premises. Rewrite using `[e3, mul_comm (res _ (g i j)), _root_.mul_assoc, e1, e2]`. Use `⟨fun T m => res (le_of_eq (inf_comm _ _)) (g m T), fun T => ?_, ?_⟩` and prove the remaining obligations. Introduce `m m'`. Use `bas3 T m m' _ le_rfl _ _ fun S a b c hS => ?_` and prove the remaining obligations.

Use `show res hS (res _ (res _ (g m T))) = res hS (res _ (g m m') * res _ (res _ (g m' T)))`. Simplify using `only [map_mul, res_res]`. Establish `e1` using `key m T S b a (hS.trans (le_inf (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_left)))`. Establish `e2` using `key m m' S b c (hS.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right))`. Establish `e3` using `key m' T S c a (hS.trans (le_inf inf_le_right (inf_le_left.trans inf_le_left)))`.

Apply `mul_right_cancel (b := u m S b)` to reduce the goal to its premises. Rewrite using `[e1, mul_comm (res _ (g m m')), _root_.mul_assoc, e2, e3]`. Introduce `T T' a m`. Use `bas2 T' m _ le_rfl _ _ fun S c d hS => ?_` and prove the remaining obligations. Use `show res hS (res _ (res _ (g m T))) = res hS (res _ (u T T' a) * res _ (g m T'))`.

Simplify using `only [map_mul, res_res]`. Establish `e1` using `key m T S d (a ≫ c) (hS.trans (le_inf inf_le_right ((inf_le_left.trans (hV a)))))`. Establish `e2` using `key m T' S d c (hS.trans (le_inf inf_le_right inf_le_left))`. Establish `e3` using `hC a c`. Apply `mul_right_cancel (b := u m S d)` to reduce the goal to its premises.

Rewrite using `[e1, _root_.mul_assoc, e2, e3]`.
-/
theorem exists_lb_frame : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens)
    (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) [Quiver.IsThin C] (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ),
    IsBas V → IsCoc V hV u → ∃ L : LB X, L.IsLB ∧ IsFrame L V hV u := by
  intro X C _ V hV _ u hB hC
  have hE := fun T₁ T₂ => GlobalTheory.T.existsUnique_transition_units_cocycle_thin_basis X C V hV u hB hC T₁ T₂
  choose g hg using fun T₁ T₂ => (hE T₁ T₂).exists
  have key : ∀ (T₁ T₂ S : C) (a : T₁ ⟶ S) (b : T₂ ⟶ S) (h : V S ≤ V T₁ ⊓ V T₂),
      res h (g T₁ T₂) * u T₁ S a = u T₂ S b := fun T₁ T₂ S a b _ => hg T₁ T₂ S a b
  have bas2 : ∀ (i j : C) (W : X.Opens) (hW : W ≤ V i ⊓ V j) (x y : Γ(X, W)ˣ),
      (∀ (S : C) (_ : i ⟶ S) (_ : j ⟶ S) (hS : V S ≤ W), res hS x = res hS y) → x = y := by
    intro i j W hW x y h
    refine units_eq_of_local x y fun p hp => ?_
    obtain ⟨S, ⟨a⟩, ⟨b⟩, hpS, hSW⟩ := hB.2 i j p W hp (hW hp).1 (hW hp).2
    exact ⟨V S, hSW, hpS, h S a b hSW⟩
  have bas3 : ∀ (i j k : C) (W : X.Opens) (hW : W ≤ V i ⊓ V j ⊓ V k) (x y : Γ(X, W)ˣ),
      (∀ (S : C) (_ : i ⟶ S) (_ : j ⟶ S) (_ : k ⟶ S) (hS : V S ≤ W), res hS x = res hS y) → x = y := by
    intro i j k W hW x y h
    refine units_eq_of_local x y fun p hp => ?_
    obtain ⟨S₀, ⟨a⟩, ⟨b⟩, hpS₀, hS₀W⟩ := hB.2 i j p W hp (hW hp).1.1 (hW hp).1.2
    obtain ⟨S, ⟨c⟩, ⟨d⟩, hpS, hSW⟩ := hB.2 S₀ k p W hp hpS₀ (hW hp).2
    exact ⟨V S, hSW, hpS, h S (a ≫ c) (b ≫ c) d hSW⟩
  have gself : ∀ T, g T T = 1 := fun T =>
    (hE T T).unique (hg T T) (fun S a b => by rw [Subsingleton.elim a b, map_one, _root_.one_mul])
  let L : LB X := ⟨C, V, g⟩
  refine ⟨L, ⟨?_, ?_, ?_⟩, ?_⟩
  · refine eq_top_iff.2 fun p _ => ?_
    obtain ⟨t, hp, _⟩ := hB.1 p ⊤ trivial
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨t, hp⟩
  · intro T
    show res _ (g T T) = 1
    rw [gself, map_one]
  · intro i j k
    refine bas3 i j k _ le_rfl _ _ fun S a b c hS => ?_
    show res hS (res _ (g i j) * res _ (g j k)) = res hS (res _ (g i k))
    simp only [map_mul, res_res]
    have e1 := key i j S a b (hS.trans inf_le_left)
    have e2 := key j k S b c (hS.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right))
    have e3 := key i k S a c (hS.trans (le_inf (inf_le_left.trans inf_le_left) inf_le_right))
    apply mul_right_cancel (b := u i S a)
    rw [e3, mul_comm (res _ (g i j)), _root_.mul_assoc, e1, e2]
  · refine ⟨fun T m => res (le_of_eq (inf_comm _ _)) (g m T), fun T => ?_, ?_⟩
    · intro m m'
      refine bas3 T m m' _ le_rfl _ _ fun S a b c hS => ?_
      show res hS (res _ (res _ (g m T))) = res hS (res _ (g m m') * res _ (res _ (g m' T)))
      simp only [map_mul, res_res]
      have e1 := key m T S b a (hS.trans (le_inf (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_left)))
      have e2 := key m m' S b c (hS.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right))
      have e3 := key m' T S c a (hS.trans (le_inf inf_le_right (inf_le_left.trans inf_le_left)))
      apply mul_right_cancel (b := u m S b)
      rw [e1, mul_comm (res _ (g m m')), _root_.mul_assoc, e2, e3]
    · intro T T' a m
      refine bas2 T' m _ le_rfl _ _ fun S c d hS => ?_
      show res hS (res _ (res _ (g m T))) = res hS (res _ (u T T' a) * res _ (g m T'))
      simp only [map_mul, res_res]
      have e1 := key m T S d (a ≫ c) (hS.trans (le_inf inf_le_right ((inf_le_left.trans (hV a)))))
      have e2 := key m T' S d c (hS.trans (le_inf inf_le_right inf_le_left))
      have e3 := hC a c
      apply mul_right_cancel (b := u m S d)
      rw [e1, _root_.mul_assoc, e2, e3]

end GlobalTheory.ThinGlue
