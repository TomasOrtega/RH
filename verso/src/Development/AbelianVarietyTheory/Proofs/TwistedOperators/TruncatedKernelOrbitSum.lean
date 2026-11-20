import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

noncomputable section

namespace GlobalTheory.TruncKerConst

variable {D : D7} {V : HSp D}

/- English proof (translation)
Use `eq_bot_iff.2 fun g hg => ?_` and prove the remaining obligations. Establish `ht : 𝔉.X (Fin.last 𝔉.k) = ⊥`. Establish `e : (Fin.last 𝔉.k) = 0` using `Fin.ext (by simp [h])`. Rewrite using `[e, 𝔉.zero]`. Establish `h2` using `(IsoFlag.mem_unip.1 hg).2`.

Express the relevant statement in the definitionally equal form `g ∈ trivOn _ V _ (𝔉.X (Fin.last 𝔉.k)) (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V (𝔉.X (Fin.last 𝔉.k))) at h2`. Rewrite `h2` using `[ht, perp_bot, trivOn_bot_top]`. Conclude with `h2`.
-/
theorem NA_eq_bot_of_k_eq_zero (𝔉 : IsoFlag V) (h : 𝔉.k = 0) : NA 𝔉 = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  have ht : 𝔉.X (Fin.last 𝔉.k) = ⊥ := by
    have e : (Fin.last 𝔉.k) = 0 := Fin.ext (by simp [h])
    rw [e, 𝔉.zero]
  have h2 := (IsoFlag.mem_unip.1 hg).2
  change g ∈ trivOn _ V _ (𝔉.X (Fin.last 𝔉.k)) (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V (𝔉.X (Fin.last 𝔉.k))) at h2
  rw [ht, perp_bot, trivOn_bot_top] at h2
  exact h2

/- English proof (translation)
Use `eq_top_iff.2 fun γ _ => IsoFlag.mem_parRat.2 fun i x hx => ?_` and prove the remaining obligations. Establish `hi : i = 0` using `Fin.ext (by have := i.2; simp; omega)`. Rewrite `hx`, the goal using `[hi, 𝔉.zero]`. Rewrite `hx`, the goal using `[Submodule.mem_bot]`. Rewrite using `[hx, map_zero]`.
-/
theorem parRat_eq_top_of_k_eq_zero (𝔉 : IsoFlag V) (h : 𝔉.k = 0) : 𝔉.parRat D.sp.cm = ⊤ := by
  refine eq_top_iff.2 fun γ _ => IsoFlag.mem_parRat.2 fun i x hx => ?_
  have hi : i = 0 := Fin.ext (by have := i.2; simp; omega)
  rw [hi, 𝔉.zero] at hx ⊢
  rw [Submodule.mem_bot] at hx ⊢
  rw [hx, map_zero]

/- English proof (translation)
Establish `hb` using `NA_eq_bot_of_k_eq_zero 𝔉 h`. Establish `h1' : ∀ g ∈ NA 𝔉, g = 1` using `fun g hg => Subgroup.mem_bot.1 (hb ▸ hg)`. Use `haveI : Subsingleton (NA 𝔉) := ⟨fun a b => Subtype.ext ((h1' _ a.2).trans (h1' _ b.2).symm)⟩`. Use `letI : Unique (NA 𝔉) := { default := 1, uniq := fun _ => Subsingleton.elim _ _ }`. Establish `h1 : (Measure.haar : Measure (NA 𝔉)) univ = 1`.

Rewrite using `[Measure.haar, ← (Classical.arbitrary (TopologicalSpace.PositiveCompacts (NA 𝔉))).nonempty.eq_univ]`. Conclude with `Measure.haarMeasure_self`. Establish `h2 : quotMeasure (NQ 𝔉) Measure.haar univ = 1`. Rewrite using `[quotMeasure, Measure.map_apply GlobalTheory.AutomorphicL2Unitary.measurable_mk MeasurableSet.univ, Set.preimage_univ, Measure.restrict_apply_univ, Set.Nonempty.eq_univ (s := GlobalTheory.AutomorphicL2Unitary.stdDom (NQ 𝔉)) ⟨_, GlobalTheory.AutomorphicL2Unitary.sec_mem (GlobalThe …`. Rewrite using `[integral_unique, unipMeas, Measure.real, Measure.smul_apply, h2, h1]`.

Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem integral_unipMeas_of_k_eq_zero (𝔉 : IsoFlag V) (h : 𝔉.k = 0) (φ : GA D V → ℂ) :
    ∫ n : NA 𝔉, φ n ∂unipMeas 𝔉 = φ 1 := by
  have hb := NA_eq_bot_of_k_eq_zero 𝔉 h
  have h1' : ∀ g ∈ NA 𝔉, g = 1 := fun g hg => Subgroup.mem_bot.1 (hb ▸ hg)
  haveI : Subsingleton (NA 𝔉) := ⟨fun a b => Subtype.ext ((h1' _ a.2).trans (h1' _ b.2).symm)⟩
  letI : Unique (NA 𝔉) := { default := 1, uniq := fun _ => Subsingleton.elim _ _ }
  have h1 : (Measure.haar : Measure (NA 𝔉)) univ = 1 := by
    rw [Measure.haar, ← (Classical.arbitrary (TopologicalSpace.PositiveCompacts (NA 𝔉))).nonempty.eq_univ]
    exact Measure.haarMeasure_self
  have h2 : quotMeasure (NQ 𝔉) Measure.haar univ = 1 := by
    rw [quotMeasure, Measure.map_apply GlobalTheory.AutomorphicL2Unitary.measurable_mk MeasurableSet.univ, Set.preimage_univ,
      Measure.restrict_apply_univ,
      Set.Nonempty.eq_univ (s := GlobalTheory.AutomorphicL2Unitary.stdDom (NQ 𝔉)) ⟨_, GlobalTheory.AutomorphicL2Unitary.sec_mem (GlobalTheory.AutomorphicL2Unitary.mk (NQ 𝔉) 1)⟩, h1]
  rw [integral_unique, unipMeas, Measure.real, Measure.smul_apply, h2, h1]
  simp
  rfl

def conjEquiv (𝔬 : Set (GF V)) (h𝔬 : ∀ δ ∈ 𝔬, ∀ g, g * δ * g⁻¹ ∈ 𝔬) (g : GF V) : 𝔬 ≃ 𝔬 where
  toFun δ := ⟨g * δ * g⁻¹, h𝔬 _ δ.2 g⟩
  invFun δ := ⟨g⁻¹ * δ * g⁻¹⁻¹, h𝔬 _ δ.2 g⁻¹⟩
  left_inv δ := Subtype.ext (by simp [mul_assoc])
  right_inv δ := Subtype.ext (by simp [mul_assoc])

end GlobalTheory.TruncKerConst

open GlobalTheory.TruncKerConst in

/- English proof (translation)
Introduce `D V Φ K f hf 𝔬 h𝔬 Tr x`. Rewrite using `[kT, Finset.sum_eq_single (∅ : Finset (Fin (wittIndex V)))]`. Establish `hk : (Φ.stdFlag (∅ : Finset (Fin (wittIndex V)))).k = 0` using `rfl`. Use `haveI : Subsingleton (GlobalTheory.AutomorphicL2Unitary.Quot ((Φ.stdFlag ∅).parRat D.sp.cm)) := ⟨fun a b => by`. Proceed by induction on `a using Quotient.inductionOn`.

Proceed by induction on `b using Quotient.inductionOn`. Conclude with `Quotient.sound (QuotientGroup.rightRel_apply.2 (by rw [parRat_eq_top_of_k_eq_zero _ hk]; trivial))⟩`. Use `set ξ₀ : GlobalTheory.AutomorphicL2Unitary.Quot ((Φ.stdFlag ∅).parRat D.sp.cm) := GlobalTheory.AutomorphicL2Unitary.mk _ 1`. Rewrite using `[tsum_eq_single ξ₀ (fun b hb => absurd (Subsingleton.elim b ξ₀) hb)]`. Establish `hτ : tauHat (stdPar (∅ : Finset (Fin (wittIndex V)))) ∅ (H0 Φ K (rat V ξ₀.out * x) - Tr) = 1`.

Simplify using `[tauHat, stdPar]`. Rewrite using `[hτ, Finset.card_empty, pow_zero, one_mul, Complex.ofReal_one, one_mul, kerP]`. Use `set g := ξ₀.out`. Establish `hl : Φ.levi D.sp.cm (AF D.host.F) (stdPar (∅ : Finset (Fin (wittIndex V)))) = ⊤`. Simplify using `[WittFrame.levi, stdPar]`.

Set `e : 𝔬 ≃ {δ : GF V // δ ∈ 𝔬 ∧ rat V δ ∈ Φ.levi D.sp.cm (AF D.host.F) (stdPar (∅ : Finset (Fin (wittIndex V))))}` to `(conjEquiv 𝔬 h𝔬 g).trans { toFun := fun δ => ⟨δ.1, δ.2, by rw [hl]; trivial⟩ invFun := fun δ => ⟨δ.1, δ.2.1⟩ left_inv := fun _ => rfl right_inv := fun _ => rfl }`. Rewrite using `[← e.tsum_eq]`. Use `tsum_congr fun δ => ?_` and prove the remaining obligations. Use `(integral_unipMeas_of_k_eq_zero (φ := fun n => f (((rat V) g * x)⁻¹ * rat V (e δ).1 * n * ((rat V) g * x))) _ hk).trans ?_` and prove the remaining obligations. Establish `hδ : ((e δ).1 : GF V) = g * δ.1 * g⁻¹` using `rfl`.

Simplify using `only [hδ, OneMemClass.coe_one, map_mul, map_inv, mul_inv_rev, mul_one]`. Use `congr 1`. Use `group`. Introduce `J _ hJ`. Establish `hp : (Φ.stdFlag J).Proper` using `by show 0 < J.card`.

Conclude with `Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hJ)`. Establish `h0 : ∀ y : GA D V, kerP Φ J 𝔬 f y y = 0` using `fun y => by`. Rewrite using `[kerP]`. Use `(tsum_congr fun δ => ?_).trans tsum_zero` and prove the remaining obligations. Rewrite using `[unipMeas, integral_smul_measure, ((hf _ hp) Measure.haar (y⁻¹ * rat V δ) y).2, smul_zero]`.

Simplify using `[h0]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem GlobalTheory.TruncKer.kT_eq_of_unipIntegralsVanish : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (K : Subgroup (GA D V)) (f : GA D V → ℂ), (∀ 𝔉 : IsoFlag V, 𝔉.Proper → GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.UnipIntegralsVanish 𝔉 f) → ∀ 𝔬 : Set (GF V), (∀ δ ∈ 𝔬, ∀ g, g * δ * g⁻¹ ∈ 𝔬) → ∀ Tr x, kT Φ K 𝔬 f Tr x = ∑' δ : 𝔬, f (x⁻¹ * rat V δ * x) := by
  intro D V Φ K f hf 𝔬 h𝔬 Tr x
  classical
  rw [kT, Finset.sum_eq_single (∅ : Finset (Fin (wittIndex V)))]
  ·
    have hk : (Φ.stdFlag (∅ : Finset (Fin (wittIndex V)))).k = 0 := rfl
    haveI : Subsingleton (GlobalTheory.AutomorphicL2Unitary.Quot ((Φ.stdFlag ∅).parRat D.sp.cm)) := ⟨fun a b => by
      induction a using Quotient.inductionOn
      induction b using Quotient.inductionOn
      exact Quotient.sound (QuotientGroup.rightRel_apply.2 (by rw [parRat_eq_top_of_k_eq_zero _ hk]; trivial))⟩
    set ξ₀ : GlobalTheory.AutomorphicL2Unitary.Quot ((Φ.stdFlag ∅).parRat D.sp.cm) := GlobalTheory.AutomorphicL2Unitary.mk _ 1
    rw [tsum_eq_single ξ₀ (fun b hb => absurd (Subsingleton.elim b ξ₀) hb)]
    have hτ : tauHat (stdPar (∅ : Finset (Fin (wittIndex V)))) ∅ (H0 Φ K (rat V ξ₀.out * x) - Tr) = 1 := by
      simp [tauHat, stdPar]
    rw [hτ, Finset.card_empty, pow_zero, one_mul, Complex.ofReal_one, one_mul, kerP]
    set g := ξ₀.out
    have hl : Φ.levi D.sp.cm (AF D.host.F) (stdPar (∅ : Finset (Fin (wittIndex V)))) = ⊤ := by
      simp [WittFrame.levi, stdPar]
    let e : 𝔬 ≃ {δ : GF V // δ ∈ 𝔬 ∧ rat V δ ∈ Φ.levi D.sp.cm (AF D.host.F) (stdPar (∅ : Finset (Fin (wittIndex V))))} :=
      (conjEquiv 𝔬 h𝔬 g).trans
        { toFun := fun δ => ⟨δ.1, δ.2, by rw [hl]; trivial⟩
          invFun := fun δ => ⟨δ.1, δ.2.1⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    rw [← e.tsum_eq]
    refine tsum_congr fun δ => ?_
    refine (integral_unipMeas_of_k_eq_zero (φ := fun n => f (((rat V) g * x)⁻¹ * rat V (e δ).1 * n * ((rat V) g * x))) _ hk).trans ?_
    have hδ : ((e δ).1 : GF V) = g * δ.1 * g⁻¹ := rfl
    simp only [hδ, OneMemClass.coe_one, map_mul, map_inv, mul_inv_rev, mul_one]
    congr 1
    group
  ·
    intro J _ hJ
    have hp : (Φ.stdFlag J).Proper := by
      show 0 < J.card
      exact Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hJ)
    have h0 : ∀ y : GA D V, kerP Φ J 𝔬 f y y = 0 := fun y => by
      rw [kerP]
      refine (tsum_congr fun δ => ?_).trans tsum_zero
      rw [unipMeas, integral_smul_measure, ((hf _ hp) Measure.haar (y⁻¹ * rat V δ) y).2, smul_zero]
    simp [h0]
  · intro h; exact absurd (Finset.mem_univ _) h
