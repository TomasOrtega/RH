import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFunctionUnitAtPointOfFibreQuotientStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.Cartier.Descent

/- English proof (translation)
Take `⟨a, ha, rfl⟩` from `h`. Conclude with `⟨q.stalkMap x a, ha.map _, (functionFieldMap_algebraMap q x a).symm⟩`.
-/
theorem unitAt_functionFieldMap {X W : Scheme.{0}} [IsIntegral X] [IsIntegral W] (q : X ⟶ W)
    [IsDominant q] (x : X) {f : W.functionField} (h : UnitAt (q x) f) :
    UnitAt x (functionFieldMap q f) := by
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨q.stalkMap x a, ha.map _, (functionFieldMap_algebraMap q x a).symm⟩

/- English proof (translation)
Introduce `X W _ _ Γ _ _ ρ q _ hq D h`. Use `choose b hb using h`. Establish `: IsIntegralHom q` using `hq.isIntegralHom`. Establish `hcl : IsClosedMap q` using `q.isClosedMap`. Establish `hloc : ∀ y : W, ∃ U : W.Opens, y ∈ U ∧ ∃ f, ∀ y' ∈ U, germOf y' (b y') = germOf y' f`.

Introduce `y`. Set `O : Set X` to `{x | D.IsEqn x (Units.map (functionFieldMap q).toMonoidHom (b y))}`. Establish `hO : IsOpen O` using `isOpen_iff_forall_mem_open.2 fun x hx => by`. Take `⟨U, hU, hU'⟩` from `CartierDiv.IsEqn.exists_nhds hx`. Conclude with `⟨U, fun z hz => hU' z hz, U.isOpen, hU⟩`.

Establish `hZ : IsClosed (q '' Oᶜ)` using `hcl _ hO.isClosed_compl`. Use `⟨⟨(q '' Oᶜ)ᶜ, hZ.isOpen_compl⟩, ?_, b y, fun y' hy' => ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨x, hx, hxy⟩`. Conclude with `hx (hb y x hxy)`. Use `(germOf_eq_iff.2 ?_).symm` and prove the remaining obligations.

Use `GlobalTheory.T.rationalFunctionUnitAtPoint_of_fibre_quotient X W Γ ρ q hq y' _ fun x hx => ?_` and prove the remaining obligations. Establish `h1 : x ∈ O`. Assume the negation of the conclusion as `hn`. Conclude with `hy' ⟨x, hn, hx⟩`. Establish `h2` using `(h1 : D.IsEqn x _).iff_unitAt.1 (hb y' x hx)`.

Simplify `h2` using `only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, map_div₀]`. Set `E : CartierDiv W` to `show cartierGroup W from ⟨fun y => germOf y (b y), hloc⟩`. Use `⟨E, fun y b' hE x hx => ?_⟩` and prove the remaining obligations. Establish `hu : UnitAt y ((b' : W.functionField) / b y)` using `germOf_eq_iff.1 hE`. Substitute `hx` using the available equality.

Use `(hb (q x) x rfl).iff_unitAt.2 ?_` and prove the remaining obligations. Use `unitAt_functionFieldMap q x hu` as an intermediate fact. Simplify `this` using `only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, map_div₀]`.
-/
theorem exists_cartierDiv_descent : ∀ (X W : Scheme.{0}) [IsIntegral X] [IsIntegral W] (Γ : Type) [Group Γ] [Finite Γ]
    (ρ : Γ →* Aut X) (q : X ⟶ W) [IsDominant q], IsAffineQuotient ρ q → ∀ (D : CartierDiv X),
    (∀ y : W, ∃ b : W.functionFieldˣ, ∀ x, q x = y → D.IsEqn x (Units.map (functionFieldMap q).toMonoidHom b)) →
    ∃ E : CartierDiv W, ∀ y b, E.IsEqn y b → ∀ x, q x = y → D.IsEqn x (Units.map (functionFieldMap q).toMonoidHom b) := by
  intro X W _ _ Γ _ _ ρ q _ hq D h
  choose b hb using h
  have : IsIntegralHom q := hq.isIntegralHom
  have hcl : IsClosedMap q := q.isClosedMap

  have hloc : ∀ y : W, ∃ U : W.Opens, y ∈ U ∧ ∃ f, ∀ y' ∈ U, germOf y' (b y') = germOf y' f := by
    intro y
    let O : Set X := {x | D.IsEqn x (Units.map (functionFieldMap q).toMonoidHom (b y))}
    have hO : IsOpen O := isOpen_iff_forall_mem_open.2 fun x hx => by
      obtain ⟨U, hU, hU'⟩ := CartierDiv.IsEqn.exists_nhds hx
      exact ⟨U, fun z hz => hU' z hz, U.isOpen, hU⟩
    have hZ : IsClosed (q '' Oᶜ) := hcl _ hO.isClosed_compl
    refine ⟨⟨(q '' Oᶜ)ᶜ, hZ.isOpen_compl⟩, ?_, b y, fun y' hy' => ?_⟩
    · rintro ⟨x, hx, hxy⟩
      exact hx (hb y x hxy)
    · refine (germOf_eq_iff.2 ?_).symm
      refine GlobalTheory.T.rationalFunctionUnitAtPoint_of_fibre_quotient X W Γ ρ q hq y' _ fun x hx => ?_
      have h1 : x ∈ O := by
        by_contra hn
        exact hy' ⟨x, hn, hx⟩
      have h2 := (h1 : D.IsEqn x _).iff_unitAt.1 (hb y' x hx)
      simpa only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, map_div₀] using h2
  let E : CartierDiv W := show cartierGroup W from ⟨fun y => germOf y (b y), hloc⟩
  refine ⟨E, fun y b' hE x hx => ?_⟩
  have hu : UnitAt y ((b' : W.functionField) / b y) := germOf_eq_iff.1 hE
  subst hx
  refine (hb (q x) x rfl).iff_unitAt.2 ?_
  have := unitAt_functionFieldMap q x hu
  simpa only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, map_div₀] using this

end GlobalTheory.Cartier.Descent
