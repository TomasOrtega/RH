import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsCuspFunOnePlane
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingZeroMeanNormalizedSubgroupStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ENNReal

noncomputable section
namespace GlobalTheory.TowerCT

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `D V r C hC κ 𝓝 hκ h𝓝`. Establish `hint : IntegrableOn (fun _ : NI V C => (1 : ℂ)) 𝓝 κ`. Establish `key : ∀ N : Subgroup (GA D V), N = GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) (GlobalTheory.AutFunCompare.colSpan V C) → ∀ Q : Subgroup (GA D V), Q = GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.ratPts D.sp.cm V → ∀ …`. Introduce and unpack `N rfl Q rfl μ 𝓕 hμ h𝓕`. Conclude with `GlobalTheory.AutFunCompare.integrableOn_constTerm D.sp.cm V _ ((GlobalTheory.AutFunCompare.isIsoFrame_iff V C).1 hC).2 (fun _ => 1) continuous_const (fun _ _ _ => rfl) μ hμ 𝓕 h𝓕 1`.

Conclude with `key _ (GlobalTheory.AutFunCompare.NI_eq V C) _ (GlobalTheory.AutFunCompare.GQ_eq V) κ 𝓝 hκ h𝓝`. Break down `(integrableOn_const_iff (C := (1 : ℂ))).1 hint with h | h` into its components or cases. Conclude with `absurd h (by simp)`. Conclude with `h.ne`.
-/
theorem vol : ∀ (D : D7) (V : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C →
    ∀ (κ : Measure (NI V C)) (𝓝 : Set (NI V C)), κ.IsHaarMeasure → IsFundamentalDomain (NIQ V C) 𝓝 κ → κ 𝓝 ≠ ⊤ := by
  intro D V r C hC κ 𝓝 hκ h𝓝
  have hint : IntegrableOn (fun _ : NI V C => (1 : ℂ)) 𝓝 κ := by
    have key : ∀ N : Subgroup (GA D V),
        N = GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) (GlobalTheory.AutFunCompare.colSpan V C) →
        ∀ Q : Subgroup (GA D V), Q = GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.ratPts D.sp.cm V →
        ∀ (μ : Measure N) (𝓕 : Set N), μ.IsHaarMeasure → IsFundamentalDomain (Q.subgroupOf N) 𝓕 μ →
          IntegrableOn (fun _ : N => (1 : ℂ)) 𝓕 μ := by
      rintro N rfl Q rfl μ 𝓕 hμ h𝓕
      exact GlobalTheory.AutFunCompare.integrableOn_constTerm D.sp.cm V _ ((GlobalTheory.AutFunCompare.isIsoFrame_iff V C).1 hC).2
        (fun _ => 1) continuous_const (fun _ _ _ => rfl) μ hμ 𝓕 h𝓕 1
    exact key _ (GlobalTheory.AutFunCompare.NI_eq V C) _ (GlobalTheory.AutFunCompare.GQ_eq V) κ 𝓝 hκ h𝓝
  rcases (integrableOn_const_iff (C := (1 : ℂ))).1 hint with h | h
  · exact absurd h (by simp)
  · exact h.ne

/- English proof (translation)
Introduce `D W s L hL ν hν F hF hcusp Γ hle hnorm hin K hKm hKn hKγ 𝓖 h𝓖 hint`. Take `⟨b1, b2, b3, b4, b5, b6, b7⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W`. Establish `hcl` using `GlobalTheory.CuspDecay.Model.isClosed_NI W hL`. Establish `: LocallyCompactSpace (NI W L)` using `hcl.locallyCompactSpace`. Establish `hQ : Countable (GQ W)` using `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig W.gram`.

Set `i : NIQ W L → GQ W` to `fun x => ⟨x.1.1, x.2⟩`. Establish `hi : Function.Injective i` using `fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z : GQ W => z.1) h))`. Establish `: DiscreteTopology (NIQ W L)` using `DiscreteTopology.of_continuous_injective (f := i) ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) hi`. Establish `: Countable (NIQ W L)` using `hi.countable`. Establish `: SecondCountableTopology (NI W L)` using `TopologicalSpace.Subtype.secondCountableTopology _`.

Set `κ : Measure (NI W L)` to `Measure.haar`. Take `⟨𝓝, h𝓝⟩` from `GlobalTheory.FundDomDiscrete.exists_isFundamentalDomain (NIQ W L) κ`. Establish `hκ : κ.IsHaarMeasure` using `inferInstance`. Establish `hΓ : Countable Γ` using `(Subgroup.inclusion_injective hle).countable`. Establish `e : Γ.subgroupOf (NI W L) = NIQ W L`.

Use extensionality with `n`. Conclude with `⟨fun h => hle h, fun h => hin _ n.2 h⟩`. Establish `h𝓝' : IsFundamentalDomain (Γ.subgroupOf (NI W L)) 𝓝 κ`. Rewrite using `[e]`. Conclude with `h𝓝`.

Conclude with `GlobalTheory.T.unfolding_zero_mean_normalized_subgroup (GA D W) ν Γ (NI W L) hΓ hcl hnorm κ 𝓝 hκ h𝓝' (vol D W s L hL κ 𝓝 hκ h𝓝) K F hKm hF.2.1.measurable hKn hKγ (fun γ hγ h => hF.1 γ (hle hγ) h) (fun h => hcusp s L hL κ 𝓝 hκ h𝓝 h) 𝓖 h𝓖 hint`.
-/
theorem cusp : ∀ (D : D7) (W : HSp D) (s : ℕ) (L : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W L →
    ∀ (ν : Measure (GA D W)), ν.IsHaarMeasure → ∀ F : GA D W → ℂ, GlobalTheory.Grow.RapidDec W F → IsCuspFun W F →
    ∀ Γ : Subgroup (GA D W), Γ ≤ GQ W → (∀ γ ∈ Γ, ∀ n ∈ NI W L, γ * n * γ⁻¹ ∈ NI W L) →
    (∀ n ∈ NI W L, n ∈ GQ W → n ∈ Γ) → ∀ K : GA D W → ℂ, Measurable K → (∀ n ∈ NI W L, ∀ h, K (n * h) = K h) →
    (∀ γ ∈ Γ, ∀ h, K (γ * h) = K h) → ∀ 𝓖 : Set (GA D W), IsFundamentalDomain Γ 𝓖 ν →
    IntegrableOn (fun h => K h * F h) 𝓖 ν → ∫ h in 𝓖, K h * F h ∂ν = 0 := by
  intro D W s L hL ν hν F hF hcusp Γ hle hnorm hin K hKm hKn hKγ 𝓖 h𝓖 hint
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have hcl := GlobalTheory.CuspDecay.Model.isClosed_NI W hL
  have : LocallyCompactSpace (NI W L) := hcl.locallyCompactSpace
  have hQ : Countable (GQ W) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig W.gram
  let i : NIQ W L → GQ W := fun x => ⟨x.1.1, x.2⟩
  have hi : Function.Injective i := fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z : GQ W => z.1) h))
  have : DiscreteTopology (NIQ W L) := DiscreteTopology.of_continuous_injective (f := i)
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) hi
  have : Countable (NIQ W L) := hi.countable
  have : SecondCountableTopology (NI W L) := TopologicalSpace.Subtype.secondCountableTopology _
  let κ : Measure (NI W L) := Measure.haar
  obtain ⟨𝓝, h𝓝⟩ := GlobalTheory.FundDomDiscrete.exists_isFundamentalDomain (NIQ W L) κ
  have hκ : κ.IsHaarMeasure := inferInstance
  have hΓ : Countable Γ := (Subgroup.inclusion_injective hle).countable
  have e : Γ.subgroupOf (NI W L) = NIQ W L := by
    ext n
    exact ⟨fun h => hle h, fun h => hin _ n.2 h⟩
  have h𝓝' : IsFundamentalDomain (Γ.subgroupOf (NI W L)) 𝓝 κ := by
    rw [e]
    exact h𝓝
  exact GlobalTheory.T.unfolding_zero_mean_normalized_subgroup (GA D W) ν Γ (NI W L) hΓ hcl hnorm κ 𝓝 hκ h𝓝' (vol D W s L hL κ 𝓝 hκ h𝓝) K F hKm
    hF.2.1.measurable hKn hKγ (fun γ hγ h => hF.1 γ (hle hγ) h) (fun h => hcusp s L hL κ 𝓝 hκ h𝓝 h) 𝓖 h𝓖 hint

/- English proof (translation)
Set `U : Submodule K (Fin a → K)` to `Submodule.span K (Set.range y.transpose)`. Set `s` to `Module.finrank K U`. Set `bs : Module.Basis (Fin s) K U` to `Module.finBasisOfFinrankEq K U rfl`. Establish `hcol : ∀ j, y.transpose j ∈ U` using `fun j => Submodule.subset_span ⟨j, rfl⟩`. Set `L : Matrix (Fin a) (Fin s) K` to `Matrix.of fun i k => (bs k : Fin a → K) i`.

Set `m : Matrix (Fin s) (Fin b) K` to `Matrix.of fun k j => bs.repr ⟨y.transpose j, hcol j⟩ k`. Establish `hym : y = L * m`. Use extensionality with `i j`. Establish `h` using `bs.sum_repr ⟨y.transpose j, hcol j⟩`. Establish `h2` using `congrArg (fun u : U => (u : Fin a → K) i) h`.

Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2`. Simplify using `only [Matrix.mul_apply, L, m, Matrix.of_apply]`. Rewrite using `[show y i j = y.transpose j i from rfl, ← h2]`. Conclude with `Finset.sum_congr rfl fun k _ => mul_comm _ _`. Establish `hLi : LinearIndependent K L.transpose`.

Establish `: LinearIndependent K fun k => (bs k : Fin a → K)` using `bs.linearIndependent.map' U.subtype (Submodule.ker_subtype U)`. Conclude with `this`. Establish `hrk : y.rank = s`. Rewrite using `[Matrix.rank_eq_finrank_span_cols]`. Both sides reduce to the same expression.

Establish `hs : 0 < s`. Use `Nat.pos_of_ne_zero fun h => hy ?_` and prove the remaining obligations. Establish `hU : U = ⊥` using `Submodule.finrank_eq_zero.1 h`. Use extensionality with `i j`. Use `hcol j` as an intermediate fact.

Rewrite `this` using `[hU, Submodule.mem_bot]`. Conclude with `congrFun this i`. Establish `hle : s ≤ m.rank`. Combine the equalities or inequalities in the displayed calculation. Establish `hm : m.rank = s` using `le_antisymm ((Matrix.rank_le_height m)) hle`.

Establish `hsurj : Function.Surjective m.mulVecLin`. Rewrite using `[← LinearMap.range_eq_top]`. Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Establish `: Module.finrank K (LinearMap.range m.mulVecLin) = s` using `hm`. Simplify using `using this`.

Take `⟨g, hg⟩` from `m.mulVecLin.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hsurj)`. Use `⟨s, L, m, LinearMap.toMatrix' g, hs, hLi, hm, ?_, hym⟩` and prove the remaining obligations. Establish `: Matrix.toLin' (m * LinearMap.toMatrix' g) = LinearMap.id`. Rewrite using `[Matrix.toLin'_mul, Matrix.toLin'_toMatrix']`. Conclude with `hg`.

Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Rewrite using `[this, Matrix.toLin'_one]`.
-/
theorem rankFacGen {K : Type} [Field K] {a b : ℕ} (y : Matrix (Fin a) (Fin b) K) (hy : y ≠ 0) :
    ∃ (s : ℕ) (L : Matrix (Fin a) (Fin s) K) (m : Matrix (Fin s) (Fin b) K) (m' : Matrix (Fin b) (Fin s) K),
      0 < s ∧ LinearIndependent K L.transpose ∧ m.rank = s ∧ m * m' = 1 ∧ y = L * m := by
  classical
  let U : Submodule K (Fin a → K) := Submodule.span K (Set.range y.transpose)
  let s := Module.finrank K U
  let bs : Module.Basis (Fin s) K U := Module.finBasisOfFinrankEq K U rfl
  have hcol : ∀ j, y.transpose j ∈ U := fun j => Submodule.subset_span ⟨j, rfl⟩
  let L : Matrix (Fin a) (Fin s) K := Matrix.of fun i k => (bs k : Fin a → K) i
  let m : Matrix (Fin s) (Fin b) K := Matrix.of fun k j => bs.repr ⟨y.transpose j, hcol j⟩ k
  have hym : y = L * m := by
    ext i j
    have h := bs.sum_repr ⟨y.transpose j, hcol j⟩
    have h2 := congrArg (fun u : U => (u : Fin a → K) i) h
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2
    simp only [Matrix.mul_apply, L, m, Matrix.of_apply]
    rw [show y i j = y.transpose j i from rfl, ← h2]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hLi : LinearIndependent K L.transpose := by
    have : LinearIndependent K fun k => (bs k : Fin a → K) := bs.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
    exact this
  have hrk : y.rank = s := by
    rw [Matrix.rank_eq_finrank_span_cols]
    rfl
  have hs : 0 < s := by
    refine Nat.pos_of_ne_zero fun h => hy ?_
    have hU : U = ⊥ := Submodule.finrank_eq_zero.1 h
    ext i j
    have := hcol j
    rw [hU, Submodule.mem_bot] at this
    exact congrFun this i
  have hle : s ≤ m.rank := by
    calc s = y.rank := hrk.symm
      _ = (L * m).rank := by rw [← hym]
      _ ≤ m.rank := Matrix.rank_mul_le_right _ _
  have hm : m.rank = s := le_antisymm ((Matrix.rank_le_height m)) hle
  have hsurj : Function.Surjective m.mulVecLin := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    have : Module.finrank K (LinearMap.range m.mulVecLin) = s := hm
    simpa using this
  obtain ⟨g, hg⟩ := m.mulVecLin.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hsurj)
  refine ⟨s, L, m, LinearMap.toMatrix' g, hs, hLi, hm, ?_, hym⟩
  have : Matrix.toLin' (m * LinearMap.toMatrix' g) = LinearMap.id := by
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
    exact hg
  apply Matrix.toLin'.injective
  rw [this, Matrix.toLin'_one]

/- English proof (translation)
Introduce `D W r y hy hiso`. Take `⟨s, L, m, m', hs, hL, hm, hmm, e⟩` from `rankFacGen y hy`. Use `⟨s, L, m, m', ⟨hs, hL, ?_⟩, hm, hmm, e⟩` and prove the remaining obligations. Establish `hLy : L = y * m'` using `by rw [e, Matrix.mul_assoc, hmm, Matrix.mul_one]`. Establish `hc : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) L = adj D m' * adj D y`.

Rewrite using `[hLy]`. Simplify using `only [adj, Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]`. Rewrite using `[hc]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hLy]`.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = 0 := by rw [hiso, Matrix.mul_zero, Matrix.zero_mul]`.
-/
theorem rankFac : ∀ (D : D7) (W : HSp D) (r : ℕ) (y : Matrix (Fin W.rank) (Fin r) D.host.E), y ≠ 0 →
    adj D y * W.gram * y = 0 → ∃ (s : ℕ) (L : Matrix (Fin W.rank) (Fin s) D.host.E) (m : Matrix (Fin s) (Fin r) D.host.E)
      (m' : Matrix (Fin r) (Fin s) D.host.E), IsIsoFrame W L ∧ m.rank = s ∧ m * m' = 1 ∧ y = L * m := by
  intro D W r y hy hiso
  obtain ⟨s, L, m, m', hs, hL, hm, hmm, e⟩ := rankFacGen y hy
  refine ⟨s, L, m, m', ⟨hs, hL, ?_⟩, hm, hmm, e⟩
  have hLy : L = y * m' := by rw [e, Matrix.mul_assoc, hmm, Matrix.mul_one]
  have hc : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) L = adj D m' * adj D y := by
    rw [hLy]
    simp only [adj, Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]
  rw [hc]
  calc adj D m' * adj D y * W.gram * L = adj D m' * (adj D y * W.gram * y) * m' := by
        rw [hLy]
        simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hiso, Matrix.mul_zero, Matrix.zero_mul]

/- English proof (translation)
Use `set P := (κ.restrict 𝓝).prod (ν.restrict 𝓕) with hP`. Set `G : Y → N × H → ℂ` to `fun y p => T y p.1 p.2 * F p.2`. Establish `hGm : ∀ y, Measurable (G y)` using `fun y => (hT y).mul (hF.comp measurable_snd)`. Establish `hGe : ∀ y, Measurable fun p => ‖G y p‖ₑ` using `fun y => (hGm y).enorm`. Establish `hlin : ∫⁻ p, ∑' y, ‖G y p‖ₑ ∂P ≠ ⊤`.

Rewrite using `[hP, lintegral_prod _ (Measurable.ennreal_tsum hGe).aemeasurable]`. Use `hb using 6 with n _ h` and compare the differences between its conclusion and the goal. Simplify using `only [G, enorm_mul]`. Rewrite using `[ENNReal.tsum_mul_right]`. Establish `hsum : ∑' y, ∫⁻ p, ‖G y p‖ₑ ∂P ≠ ⊤`.

Rewrite using `[← lintegral_tsum fun y => (hGe y).aemeasurable]` and apply the resulting hypothesis. Establish `hfin : ∀ y, ∫⁻ p, ‖G y p‖ₑ ∂P ≠ ⊤` using `fun y => ENNReal.ne_top_of_tsum_ne_top hsum y`. Establish `hGi : ∀ y, Integrable (G y) P` using `fun y => ⟨(hGm y).aestronglyMeasurable, lt_top_iff_ne_top.2 (hfin y)⟩`. Establish `hsp : ∀ p : N × H, HasSum (fun y => G y p) (Θ p.1 p.2 * F p.2)` using `fun p => (hs p.1 p.2).mul_right _`. Establish `hΘm : Measurable fun p : N × H => Θ p.1 p.2 * F p.2` using `measurable_of_tendsto_metrizable' Filter.atTop (f := fun (s : Finset Y) p => ∑ y ∈ s, G y p) (fun s => Finset.measurable_sum _ fun y _ => hGm y) (tendsto_pi_nhds.2 hsp)`.

Establish `hle : ∀ p : N × H, ‖Θ p.1 p.2 * F p.2‖ₑ ≤ ∑' y, ‖G y p‖ₑ` using `fun p => le_of_tendsto' ((continuous_enorm.tendsto _).comp (hsp p)) fun s => (enorm_sum_le s _).trans (ENNReal.sum_le_tsum s)`. Establish `hΘi : Integrable (fun p : N × H => Θ p.1 p.2 * F p.2) P` using `⟨hΘm.aestronglyMeasurable, ((lintegral_mono hle).trans_lt (lt_top_iff_ne_top.2 hlin))⟩`. Establish `hnorm : Summable fun y => ∫ p, ‖G y p‖ ∂P`. Establish `e : ∀ y, ∫ p, ‖G y p‖ ∂P = (∫⁻ p, ‖G y p‖ₑ ∂P).toReal` using `fun y => by`. Rewrite using `[integral_norm_eq_lintegral_enorm (hGm y).aestronglyMeasurable]`.

Simplify using `only [e]`. Conclude with `ENNReal.summable_toReal hsum`. Establish `hS` using `hasSum_integral_of_summable_integral_norm hGi hnorm`. Establish `eT : (fun p => ∑' y, G y p) = fun p : N × H => Θ p.1 p.2 * F p.2` using `funext fun p => (hsp p).tsum_eq`. Rewrite `hS` using `[eT, hP, integral_prod _ (by rw [← hP]; exact hΘi)]`.

Use `⟨hΘi.integral_prod_left, ?_, ?_⟩` and prove the remaining obligations. Use `ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum fun y => ?_)` and prove the remaining obligations. Rewrite using `[hP, lintegral_prod_symm _ (hGe y).aemeasurable]`. Use `lintegral_mono fun h => ?_` and prove the remaining obligations. Simplify using `only [G, enorm_mul]`.

Rewrite using `[lintegral_mul_const _ ((hT y).of_uncurry_right.enorm)]`. Conclude with `mul_le_mul' (enorm_integral_le_lintegral_enorm _) le_rfl`. Establish `e : (fun y => ∫ h in 𝓕, (∫ n in 𝓝, T y n h ∂κ) * F h ∂ν) = fun y => ∫ p, G y p ∂(κ.restrict 𝓝).prod (ν.restrict 𝓕)` using `funext fun y => by`. Rewrite using `[integral_prod_symm _ (by rw [← hP]; exact hGi y)]`. Use `integral_congr_ae (.of_forall fun h => ?_)` and prove the remaining obligations.

Simplify using `only [G]`. Rewrite using `[integral_mul_const]`. Rewrite using `[e]`. Conclude with `hS`.
-/
theorem fub {N H Y : Type} [MeasurableSpace N] [MeasurableSpace H] [Countable Y]
    (κ : Measure N) (ν : Measure H) [SFinite κ] [SFinite ν] (𝓝 : Set N) (𝓕 : Set H)
    (T : Y → N → H → ℂ) (hT : ∀ y, Measurable (Function.uncurry (T y))) (Θ : N → H → ℂ)
    (F : H → ℂ) (hF : Measurable F) (hs : ∀ n h, HasSum (fun y => T y n h) (Θ n h))
    (hb : ∫⁻ n in 𝓝, ∫⁻ h in 𝓕, (∑' y, ‖T y n h‖ₑ) * ‖F h‖ₑ ∂ν ∂κ ≠ ⊤) :
    IntegrableOn (fun n => ∫ h in 𝓕, Θ n h * F h ∂ν) 𝓝 κ ∧
    (∑' y, ∫⁻ h in 𝓕, ‖(∫ n in 𝓝, T y n h ∂κ) * F h‖ₑ ∂ν) ≠ ⊤ ∧
    HasSum (fun y => ∫ h in 𝓕, (∫ n in 𝓝, T y n h ∂κ) * F h ∂ν)
      (∫ n in 𝓝, ∫ h in 𝓕, Θ n h * F h ∂ν ∂κ) := by
  set P := (κ.restrict 𝓝).prod (ν.restrict 𝓕) with hP
  let G : Y → N × H → ℂ := fun y p => T y p.1 p.2 * F p.2
  have hGm : ∀ y, Measurable (G y) := fun y => (hT y).mul (hF.comp measurable_snd)
  have hGe : ∀ y, Measurable fun p => ‖G y p‖ₑ := fun y => (hGm y).enorm
  have hlin : ∫⁻ p, ∑' y, ‖G y p‖ₑ ∂P ≠ ⊤ := by
    rw [hP, lintegral_prod _ (Measurable.ennreal_tsum hGe).aemeasurable]
    convert hb using 6 with n _ h
    simp only [G, enorm_mul]
    rw [ENNReal.tsum_mul_right]
  have hsum : ∑' y, ∫⁻ p, ‖G y p‖ₑ ∂P ≠ ⊤ := by
    rwa [← lintegral_tsum fun y => (hGe y).aemeasurable]
  have hfin : ∀ y, ∫⁻ p, ‖G y p‖ₑ ∂P ≠ ⊤ := fun y => ENNReal.ne_top_of_tsum_ne_top hsum y
  have hGi : ∀ y, Integrable (G y) P := fun y =>
    ⟨(hGm y).aestronglyMeasurable, lt_top_iff_ne_top.2 (hfin y)⟩
  have hsp : ∀ p : N × H, HasSum (fun y => G y p) (Θ p.1 p.2 * F p.2) := fun p => (hs p.1 p.2).mul_right _
  have hΘm : Measurable fun p : N × H => Θ p.1 p.2 * F p.2 :=
    measurable_of_tendsto_metrizable' Filter.atTop (f := fun (s : Finset Y) p => ∑ y ∈ s, G y p)
      (fun s => Finset.measurable_sum _ fun y _ => hGm y) (tendsto_pi_nhds.2 hsp)
  have hle : ∀ p : N × H, ‖Θ p.1 p.2 * F p.2‖ₑ ≤ ∑' y, ‖G y p‖ₑ := fun p =>
    le_of_tendsto' ((continuous_enorm.tendsto _).comp (hsp p)) fun s =>
      (enorm_sum_le s _).trans (ENNReal.sum_le_tsum s)
  have hΘi : Integrable (fun p : N × H => Θ p.1 p.2 * F p.2) P :=
    ⟨hΘm.aestronglyMeasurable, ((lintegral_mono hle).trans_lt (lt_top_iff_ne_top.2 hlin))⟩
  have hnorm : Summable fun y => ∫ p, ‖G y p‖ ∂P := by
    have e : ∀ y, ∫ p, ‖G y p‖ ∂P = (∫⁻ p, ‖G y p‖ₑ ∂P).toReal := fun y => by
      rw [integral_norm_eq_lintegral_enorm (hGm y).aestronglyMeasurable]
    simp only [e]
    exact ENNReal.summable_toReal hsum
  have hS := hasSum_integral_of_summable_integral_norm hGi hnorm
  have eT : (fun p => ∑' y, G y p) = fun p : N × H => Θ p.1 p.2 * F p.2 := funext fun p => (hsp p).tsum_eq
  rw [eT, hP, integral_prod _ (by rw [← hP]; exact hΘi)] at hS
  refine ⟨hΘi.integral_prod_left, ?_, ?_⟩
  · refine ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum fun y => ?_)
    rw [hP, lintegral_prod_symm _ (hGe y).aemeasurable]
    refine lintegral_mono fun h => ?_
    simp only [G, enorm_mul]
    rw [lintegral_mul_const _ ((hT y).of_uncurry_right.enorm)]
    exact mul_le_mul' (enorm_integral_le_lintegral_enorm _) le_rfl
  · have e : (fun y => ∫ h in 𝓕, (∫ n in 𝓝, T y n h ∂κ) * F h ∂ν) =
        fun y => ∫ p, G y p ∂(κ.restrict 𝓝).prod (ν.restrict 𝓕) := funext fun y => by
      rw [integral_prod_symm _ (by rw [← hP]; exact hGi y)]
      refine integral_congr_ae (.of_forall fun h => ?_)
      simp only [G]
      rw [integral_mul_const]
    rw [e]
    exact hS

end GlobalTheory.TowerCT

end
