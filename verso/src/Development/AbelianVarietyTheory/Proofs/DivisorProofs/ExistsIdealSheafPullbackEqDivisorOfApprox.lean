import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffectiveCartierIdealSheafLeOfClosedPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMapIdealSheafOfForallDivLocalEquationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalEquationMemComapMapIdealSheafNearPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpreadRegularDivLocalEquationsProperFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratesOfCloseLocalEquationClassicalPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChevalleyCorrectionOverProperFibreStatement

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

namespace GlobalTheory.Poinc

/- English proof (translation)
Introduce `o Ω _ _ _ _ M₁ M π hπ hprop hn₁ hn U D hU hUD hyp`. Use `⟨D.idealSheaf.map π, le_antisymm (Scheme.IdealSheafData.comap_map_le _ _) ?_⟩` and prove the remaining obligations. Use `haveI : QuasiCompact M.s := M.qc`. Use `haveI : CompactSpace M.Z := QuasiCompact.compactSpace_of_compactSpace M.s`. Apply `GlobalTheory.T.effectiveCartier_idealSheaf_le_of_closedPoints M.Z D` to reduce the goal to its premises.

Introduce `x hx`. Establish `hz : IsClosed ({π x} : Set M₁.Z)`. Use `π.isClosedMap _ hx` as an intermediate fact. Simplify `this` using `[Set.image_singleton]`. Take `⟨p, hp, y₀, hcen, hF⟩` from `hyp (π x) hz x rfl hx`.

Take `⟨i, hi⟩` from `D.exists_mem x`. Establish `hEq : EqAt M D x (valF M.pt (D.U i) (D.f i))` using `⟨i, hi, rfl⟩`. Take `⟨k, hk⟩` from `GlobalTheory.T.generates_of_close_localEquation_classicalPoint o Ω M₁ M π hπ U D hUD x p y₀ hcen _ hEq`. Take `⟨e, he⟩` from `GlobalTheory.T.exists_chevalley_correction_over_proper_fibre o Ω M₁ M π hπ hprop hn₁ hn U D hU hUD (π x) hz k`. Take `⟨F, hFm, h1, h2⟩` from `hF e`.

Take `⟨G, b, hFGb, hfib, hb⟩` from `he ⟨F, hFm⟩ h2`. Establish `hGf : (G : Ω) / valF M.pt (D.U i) (D.f i) ∈ M.O x` using `hfib x rfl _ hEq`. Establish `hnorm : ‖M.val (gPt p ≫ y₀) ((G : Ω) + b)‖ = ‖M.val (gPt p ≫ y₀) (valF M.pt (D.U i) (D.f i))‖`. Rewrite using `[← hFGb]`. Conclude with `h1 _ hEq`.

Take `⟨hG0, hfG⟩` from `hk G b hnorm hb hGf`. Take `⟨V, g, hzV, hg, hV⟩` from `GlobalTheory.T.spread_regular_div_localEquations_proper_fibre o Ω M₁ M π hπ hprop D (π x) G G.2 hfib`. Establish `hgI` using `GlobalTheory.T.mem_map_idealSheaf_of_forall_div_localEquation o Ω M₁ M π hπ hprop D V g (by rw [hg]; exact hV)`. Take `⟨W, h, hxW, hW⟩` from `GlobalTheory.T.localEquation_mem_comap_map_idealSheaf_near_point o Ω M₁ M π hπ D V g x i hzV hi hgI (by rw [hg]; exact hG0) (by rw [hg]; exact hfG)`. Conclude with `⟨W, i, h, hxW, hW⟩`.
-/
theorem exists_idealSheaf_comap_eq_of_approx : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M₁ M : RatModel o Ω) (π : M.Z ⟶ M₁.Z), M₁.IsHom M (AlgHom.id o Ω) π → IsProper π → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₁.Z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (U : M.Z.Opens) (D : EffCartierData M.Z), (U : Set M.Z).Nonempty → (∀ x ∈ D.idealSheaf.support, x ∉ U) → (∀ (z : M₁.Z), IsClosed ({z} : Set M₁.Z) → ∀ x : M.Z, π x = z → IsClosed ({x} : Set M.Z) → ∃ (p : ℕ) (_ : Fact p.Prime) (y₀ : Sp (OO p) ⟶ M.Z), M.Cen U x y₀ ∧ ∀ e : ℕ, ∃ F ∈ M₁.O z, (∀ f, EqAt M D x f → ‖M.val (gPt p ≫ y₀) F‖ = ‖M.val (gPt p ≫ y₀) f‖) ∧ ∀ (q : ℕ) [Fact q.Prime] (y : Sp (OO q) ⟶ M.Z), π (y (cPt q)) = z → Set.range (gPt q ≫ y) ⊆ U → ∀ f, EqAt M D (y (cPt q)) f → ‖M.val (gPt q ≫ y) F‖ ≤ ‖M.val (gPt q ≫ y) f‖ ∨ ∃ h, NonUnitAt M₁ z h ∧ ‖M.val (gPt q ≫ y) F‖ ≤ ‖M.val (gPt q ≫ y) h‖ ^ e) → ∃ J : M₁.Z.IdealSheafData, J.comap π = D.idealSheaf := by
  intro o Ω _ _ _ _ M₁ M π hπ hprop hn₁ hn U D hU hUD hyp
  refine ⟨D.idealSheaf.map π, le_antisymm (Scheme.IdealSheafData.comap_map_le _ _) ?_⟩
  haveI : QuasiCompact M.s := M.qc
  haveI : CompactSpace M.Z := QuasiCompact.compactSpace_of_compactSpace M.s
  apply GlobalTheory.T.effectiveCartier_idealSheaf_le_of_closedPoints M.Z D
  intro x hx
  have hz : IsClosed ({π x} : Set M₁.Z) := by
    have := π.isClosedMap _ hx
    simpa [Set.image_singleton] using this
  obtain ⟨p, hp, y₀, hcen, hF⟩ := hyp (π x) hz x rfl hx
  obtain ⟨i, hi⟩ := D.exists_mem x
  have hEq : EqAt M D x (valF M.pt (D.U i) (D.f i)) := ⟨i, hi, rfl⟩
  obtain ⟨k, hk⟩ := GlobalTheory.T.generates_of_close_localEquation_classicalPoint o Ω M₁ M π hπ U D hUD x p y₀ hcen _ hEq
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_chevalley_correction_over_proper_fibre o Ω M₁ M π hπ hprop hn₁ hn U D hU hUD (π x) hz k
  obtain ⟨F, hFm, h1, h2⟩ := hF e
  obtain ⟨G, b, hFGb, hfib, hb⟩ := he ⟨F, hFm⟩ h2
  have hGf : (G : Ω) / valF M.pt (D.U i) (D.f i) ∈ M.O x := hfib x rfl _ hEq
  have hnorm : ‖M.val (gPt p ≫ y₀) ((G : Ω) + b)‖ = ‖M.val (gPt p ≫ y₀) (valF M.pt (D.U i) (D.f i))‖ := by
    rw [← hFGb]; exact h1 _ hEq
  obtain ⟨hG0, hfG⟩ := hk G b hnorm hb hGf
  obtain ⟨V, g, hzV, hg, hV⟩ := GlobalTheory.T.spread_regular_div_localEquations_proper_fibre o Ω M₁ M π hπ hprop D (π x) G G.2 hfib
  have hgI := GlobalTheory.T.mem_map_idealSheaf_of_forall_div_localEquation o Ω M₁ M π hπ hprop D V g (by rw [hg]; exact hV)
  obtain ⟨W, h, hxW, hW⟩ := GlobalTheory.T.localEquation_mem_comap_map_idealSheaf_near_point o Ω M₁ M π hπ D V g x i hzV hi hgI (by rw [hg]; exact hG0) (by rw [hg]; exact hfG)
  exact ⟨W, i, h, hxW, hW⟩

end GlobalTheory.Poinc
