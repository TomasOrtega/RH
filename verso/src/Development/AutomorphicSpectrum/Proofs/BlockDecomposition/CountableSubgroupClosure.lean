import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape
open MeasureTheory Filter Topology
open scoped ENNReal
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.LatCount

/- English proof (translation)
Establish `ht : (s ∪ s⁻¹).Countable` using `hs.union (by simpa using hs.image (·⁻¹))`. Use `haveI : Countable ↥(s ∪ s⁻¹) := ht.to_subtype`. Use `haveI : Countable (FreeMonoid ↥(s ∪ s⁻¹)) := inferInstanceAs (Countable (List ↥(s ∪ s⁻¹)))`. Establish `h : ((Subgroup.closure s : Subgroup G) : Set G) = Set.range (FreeMonoid.lift ((↑) : ↥(s ∪ s⁻¹) → G))`. Establish `h1 : ((Subgroup.closure s : Subgroup G) : Set G) = ((Submonoid.closure (s ∪ s⁻¹) : Submonoid G) : Set G)`.

Rewrite using `[← Subgroup.closure_toSubmonoid]`. Both sides reduce to the same expression. Rewrite using `[h1, Submonoid.closure_eq_mrange]`. Both sides reduce to the same expression. Rewrite using `[h]`.

Conclude with `Set.countable_range _`.
-/
theorem countable_subgroupClosure {G : Type*} [Group G] (s : Set G) (hs : s.Countable) :
    ((Subgroup.closure s : Subgroup G) : Set G).Countable := by
  have ht : (s ∪ s⁻¹).Countable := hs.union (by simpa using hs.image (·⁻¹))
  haveI : Countable ↥(s ∪ s⁻¹) := ht.to_subtype
  haveI : Countable (FreeMonoid ↥(s ∪ s⁻¹)) :=
    inferInstanceAs (Countable (List ↥(s ∪ s⁻¹)))
  have h : ((Subgroup.closure s : Subgroup G) : Set G)
      = Set.range (FreeMonoid.lift ((↑) : ↥(s ∪ s⁻¹) → G)) := by
    have h1 : ((Subgroup.closure s : Subgroup G) : Set G)
        = ((Submonoid.closure (s ∪ s⁻¹) : Submonoid G) : Set G) := by
      rw [← Subgroup.closure_toSubmonoid]; rfl
    rw [h1, Submonoid.closure_eq_mrange]; rfl
  rw [h]
  exact Set.countable_range _

/- English proof (translation)
Use `haveI : Countable K := GroundTheory.Global.countable_numberField K`. Use `haveI : Countable (Matrix (Fin n) (Fin n) K) := inferInstanceAs (Countable (Fin n → Fin n → K))`. Use `haveI : Countable (GL (Fin n) K) := Units.val_injective.countable`. Establish `h1 : (Set.range (AdelicGLn.diagonal K n)).Countable` using `Set.countable_range _`. Establish `h2 : ((Subgroup.zpowers (PositivityTheory.Rg.Rs.An.tor K fun _ : Fin n => (1 : ℝ)) : Subgroup (AdelicGLn.AdelicGL K n)) : Set (AdelicGLn.AdelicGL K n)).Countable`.

Rewrite using `[Subgroup.coe_zpowers]`. Conclude with `Set.countable_range _`. Establish `h3` using `countable_subgroupClosure ((Set.range (AdelicGLn.diagonal K n)) ∪ ((Subgroup.zpowers (PositivityTheory.Rg.Rs.An.tor K fun _ : Fin n => (1 : ℝ)) : Subgroup (AdelicGLn.AdelicGL K n)) : Set (AdelicGLn.AdelicGL K n))) (h1.union h2)`. Establish `h4 : PositivityTheory.Rg.Rs.An.lat K n = Subgroup.closure ((Set.range (AdelicGLn.diagonal K n)) ∪ ((Subgroup.zpowers (PositivityTheory.Rg.Rs.An.tor K fun _ : Fin n => (1 : ℝ)) : Subgroup (AdelicGLn.AdelicGL K n)) : Set (AdelicGLn.AdelicGL K n)))`. Unfold `PositivityTheory.Rg.Rs.An.lat`.

Rewrite using `[Subgroup.closure_union, Subgroup.closure_eq, ← MonoidHom.coe_range, Subgroup.closure_eq]`. Rewrite using `[h4]`. Conclude with `h3.to_subtype`.
-/
theorem countable_lat (K : Type) [Field K] [NumberField K] (n : ℕ) :
    Countable (PositivityTheory.Rg.Rs.An.lat K n) := by
  haveI : Countable K := GroundTheory.Global.countable_numberField K
  haveI : Countable (Matrix (Fin n) (Fin n) K) :=
    inferInstanceAs (Countable (Fin n → Fin n → K))
  haveI : Countable (GL (Fin n) K) := Units.val_injective.countable
  have h1 : (Set.range (AdelicGLn.diagonal K n)).Countable := Set.countable_range _
  have h2 : ((Subgroup.zpowers (PositivityTheory.Rg.Rs.An.tor K fun _ : Fin n => (1 : ℝ)) :
      Subgroup (AdelicGLn.AdelicGL K n)) : Set (AdelicGLn.AdelicGL K n)).Countable := by
    rw [Subgroup.coe_zpowers]
    exact Set.countable_range _
  have h3 := countable_subgroupClosure
    ((Set.range (AdelicGLn.diagonal K n)) ∪
      ((Subgroup.zpowers (PositivityTheory.Rg.Rs.An.tor K fun _ : Fin n => (1 : ℝ)) :
      Subgroup (AdelicGLn.AdelicGL K n)) : Set (AdelicGLn.AdelicGL K n))) (h1.union h2)
  have h4 : PositivityTheory.Rg.Rs.An.lat K n = Subgroup.closure
      ((Set.range (AdelicGLn.diagonal K n)) ∪
        ((Subgroup.zpowers (PositivityTheory.Rg.Rs.An.tor K fun _ : Fin n => (1 : ℝ)) :
        Subgroup (AdelicGLn.AdelicGL K n)) : Set (AdelicGLn.AdelicGL K n))) := by
    unfold PositivityTheory.Rg.Rs.An.lat
    rw [Subgroup.closure_union, Subgroup.closure_eq, ← MonoidHom.coe_range, Subgroup.closure_eq]
  rw [h4]
  exact h3.to_subtype

end GlobalTheory.CompanionTheory.LatCount
