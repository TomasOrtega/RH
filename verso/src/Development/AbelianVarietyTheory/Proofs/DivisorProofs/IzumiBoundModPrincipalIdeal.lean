import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeSpanSupPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IInfIzumiSmallValueIdealMapLeSpanStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

namespace GlobalTheory.Izumi

/- English proof (translation)
Introduce `o Ω _ _ _ _ M hn U hU x hx f hf hf0`. Use `haveI : IsDedekindDomain o := ArithBase.ded Ω`. Use `haveI : IsNoetherianRing (M.O x) := M.isNoetherianRing_O x`. Establish `hB` using `GlobalTheory.T.iInf_izumiSmallValueIdeal_map_le_span o Ω M hn U hU x hx f hf hf0`. Use `choose C hC using exists_le_span_sup_pow (M.O x) (smallIdeal M U x f) ⟨f, hf⟩ (smallIdeal_antitone U x f) (self_mem_smallIdeal U hf) hB`.

Use `⟨C, fun e F hF => ?_⟩` and prove the remaining obligations. Establish `hmem : F ∈ Ideal.span {(⟨f, hf⟩ : M.O x)} ⊔ maximalIdeal (M.O x) ^ e` using `hC e (mem_smallIdeal.2 hF)`. Take `⟨u, hu, b, hb, rfl⟩` from `Submodule.mem_sup.1 hmem`. Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.1 hu`. Establish `hm : Ideal.span {c : M.O x | ¬ IsUnit c} = maximalIdeal (M.O x)` using `Ideal.span_eq (maximalIdeal (M.O x))`.

Use `⟨a, b, rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[hm]`. Conclude with `hb`.
-/
theorem small_mod_principal : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (U : M.Z.Opens), (U : Set M.Z).Nonempty → ∀ (x : M.Z), IsClosed ({x} : Set M.Z) → ∀ f ∈ M.O x, f ≠ 0 → ∃ C : ℕ → ℕ, ∀ (e : ℕ) (F : M.O x), (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U x y → ‖M.val (gPt p ≫ y) F‖ ≤ ‖M.val (gPt p ≫ y) f‖ ∨ ∃ h, NonUnitAt M x h ∧ ‖M.val (gPt p ≫ y) F‖ ≤ ‖M.val (gPt p ≫ y) h‖ ^ C e) → ∃ a b : M.O x, (F : Ω) = a * f + b ∧ b ∈ Ideal.span {c : M.O x | ¬ IsUnit c} ^ e := by
  intro o Ω _ _ _ _ M hn U hU x hx f hf hf0
  haveI : IsDedekindDomain o := ArithBase.ded Ω
  haveI : IsNoetherianRing (M.O x) := M.isNoetherianRing_O x
  have hB := GlobalTheory.T.iInf_izumiSmallValueIdeal_map_le_span o Ω M hn U hU x hx f hf hf0
  choose C hC using exists_le_span_sup_pow (M.O x) (smallIdeal M U x f) ⟨f, hf⟩
    (smallIdeal_antitone U x f) (self_mem_smallIdeal U hf) hB
  refine ⟨C, fun e F hF => ?_⟩
  have hmem : F ∈ Ideal.span {(⟨f, hf⟩ : M.O x)} ⊔ maximalIdeal (M.O x) ^ e := hC e (mem_smallIdeal.2 hF)
  obtain ⟨u, hu, b, hb, rfl⟩ := Submodule.mem_sup.1 hmem
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hu
  have hm : Ideal.span {c : M.O x | ¬ IsUnit c} = maximalIdeal (M.O x) := Ideal.span_eq (maximalIdeal (M.O x))
  refine ⟨a, b, rfl, ?_⟩
  rw [hm]
  exact hb

end GlobalTheory.Izumi
