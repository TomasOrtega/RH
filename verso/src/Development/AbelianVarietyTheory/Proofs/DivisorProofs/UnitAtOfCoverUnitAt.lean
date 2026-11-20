import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometricOfSameNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodReductionExtendsRegular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormShiftRationalMultipleLog
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsZeroOfInvOfNotRegularNormal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverFunctionFieldMapEqStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm

namespace GlobalTheory.Mean4O.Cover

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

/- English proof (translation)
Take `⟨U, hb, hU⟩` from `hf.exists_nhds`. Conclude with `hU a (h.mem_open U.isOpen hb)`.
-/
theorem unitAt_of_specializes {X : Scheme.{0}} [IsIntegral X] {a b : X} (h : a ⤳ b)
    {f : X.functionField} (hf : UnitAt b f) : UnitAt a f := by
  obtain ⟨U, hb, hU⟩ := hf.exists_nhds
  exact hU a (h.mem_open U.isOpen hb)

/- English proof (translation)
Take `⟨hη, e⟩` from `GlobalTheory.T.cover_function_field_map_eq V`. Take `⟨U, hx, s, rfl⟩` from `hr.exists_fnOf`. Establish `hy : z ∈ V.π ⁻¹ᵁ U` using `hx`. Rewrite `hu` using `[e, SmallSec.fnMap_fnOf V.π hη _ (gen_mem hy), unitAt_fnOf_iff hy, ← Scheme.preimage_basicOpen]`. Conclude with `(unitAt_fnOf_iff hx _ s).2 hu`.
-/
theorem unitAt_of_unitAt_φ (V : Cover Y) {z : V.G} {f : Y.Fn} (hr : RegAt (V.π z) f)
    (hu : UnitAt z (V.φ f)) : UnitAt (V.π z) f := by
  obtain ⟨hη, e⟩ := GlobalTheory.T.cover_function_field_map_eq V
  obtain ⟨U, hx, s, rfl⟩ := hr.exists_fnOf
  have hy : z ∈ V.π ⁻¹ᵁ U := hx
  rw [e, SmallSec.fnMap_fnOf V.π hη _ (gen_mem hy), unitAt_fnOf_iff hy, ← Scheme.preimage_basicOpen] at hu
  exact (unitAt_fnOf_iff hx _ s).2 hu

/- English proof (translation)
Assume the negation of the conclusion as `hn`. Use `Var.isNormalScheme Y` as an intermediate fact. Take `⟨z, hzx, hz⟩` from `GlobalTheory.T.exists_zero_of_inv_of_not_regular_normal Y.X (GlobalTheory.IsNormalScheme.pred _) x u hn`. Take `⟨z', rfl⟩` from `V.π.surjective z`. Take `⟨x', hzx', rfl⟩` from `V.π.isClosedMap.specializingMap hzx`.

Establish `hu : UnitAt z' (V.φ u⁻¹)`. Rewrite using `[map_inv₀]`. Conclude with `(unitAt_of_specializes hzx' (h x' rfl)).inv`. Conclude with `(zeroAt_iff.1 hz).2 (unitAt_of_unitAt_φ V (zeroAt_iff.1 hz).1 hu)`.
-/
theorem regAt_of_unitAt_φ (V : Cover Y) {u : Y.Fn} {x : Y.X}
    (h : ∀ x' : V.G, V.π x' = x → UnitAt x' (V.φ u)) : RegAt x u := by
  by_contra hn
  have := Var.isNormalScheme Y
  obtain ⟨z, hzx, hz⟩ := GlobalTheory.T.exists_zero_of_inv_of_not_regular_normal Y.X (GlobalTheory.IsNormalScheme.pred _) x u hn
  obtain ⟨z', rfl⟩ := V.π.surjective z
  obtain ⟨x', hzx', rfl⟩ := V.π.isClosedMap.specializingMap hzx
  have hu : UnitAt z' (V.φ u⁻¹) := by
    rw [map_inv₀]
    exact (unitAt_of_specializes hzx' (h x' rfl)).inv
  exact (zeroAt_iff.1 hz).2 (unitAt_of_unitAt_φ V (zeroAt_iff.1 hz).1 hu)

end GlobalTheory.Mean4O.Cover

namespace GlobalTheory

/- English proof (translation)
Introduce `F _ _ Y V g x h`. Take `⟨x', hx'⟩` from `V.π.surjective x`. Establish `hg : g ≠ 0`. Introduce and unpack `rfl`. Conclude with `(h x' hx').ne_zero (map_zero _)`.

Use `(unitAt_iff hg).2 ⟨V.regAt_of_unitAt_φ h, V.regAt_of_unitAt_φ fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[map_inv₀]`. Conclude with `(h y hy).inv`.
-/
theorem unitAt_of_unitAt_φ_cover : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : GlobalTheory.Mean4O.Cover Y) (g : Y.Fn) (x : Y.X),
    (∀ x' : V.G, V.π x' = x → UnitAt x' (V.φ g)) → UnitAt x g := by
  intro F _ _ Y V g x h
  obtain ⟨x', hx'⟩ := V.π.surjective x
  have hg : g ≠ 0 := by
    rintro rfl
    exact (h x' hx').ne_zero (map_zero _)
  refine (unitAt_iff hg).2 ⟨V.regAt_of_unitAt_φ h, V.regAt_of_unitAt_φ fun y hy => ?_⟩
  rw [map_inv₀]
  exact (h y hy).inv

end GlobalTheory
