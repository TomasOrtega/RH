import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodingerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableThetaSumOfSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingOfProjectionSupportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalizingWeightEqualOffPlaceMassesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharDotMulMemAdelicSchwartzSpaceStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.FibreLocality

/- English proof (translation)
The claim follows from `GlobalTheory.T.vanishing_of_projection_support`.
-/
theorem lp : ∀ {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure] (P : X →+ X), Continuous P →
    (∀ x, P (P x) = P x) → ∀ (Φ Ψ : X → ℂ), Continuous Φ → Continuous Ψ → ∀ K : Set X, IsCompact K →
    (∀ x, Φ x ≠ 0 → P x ∈ K) → ∀ y : X, (∀ z, P z = z → Φ (y + z) = 0) →
    (∀ O : Set X, IsOpen O → y ∈ O → ∃ h : X → ENNReal, Measurable h ∧ (∀ x, h x ≤ 1) ∧
      (∀ x z, P z = z → h (x + z) = h x) ∧ (∀ x, h x ≠ 0 → x + (P y - P x) ∈ O) ∧
      (∃ O' : Set X, IsOpen O' ∧ y ∈ O' ∧ ∀ x ∈ O', Ψ x ≠ 0 → 1 / 2 ≤ h x) ∧
      ∫⁻ x, h x * ‖Ψ x‖ₑ ^ 2 ∂μ = ∫⁻ x, h x * ‖Φ x‖ₑ ^ 2 ∂μ) → Ψ y = 0 := GlobalTheory.T.vanishing_of_projection_support

/- English proof (translation)
The claim follows from `GlobalTheory.T.exists_localizingWeight_equal_offPlaceMasses`.
-/
theorem lw : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → (∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1) →
    ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ Ψ ∈ GlobalTheory.WeilM.schA F κ,
    (∀ (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ), (∀ b ∈ s, GlobalTheory.LatVac.liftV v 1 • b = 0) →
      ∫⁻ x, ‖(∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * Ψ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖(∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * Φ x‖ₑ ^ 2 ∂μ) →
    ∀ (y : κ → AF F) (O : Set (κ → AF F)), IsOpen O → y ∈ O →
    ∃ h : (κ → AF F) → ENNReal, @Measurable _ _ (borel _) _ h ∧ (∀ x, h x ≤ 1) ∧
      (∀ x z, GlobalTheory.LatVac.liftV v 1 • z = z → h (x + z) = h x) ∧
      (∀ x, h x ≠ 0 → x + (GlobalTheory.LatVac.liftV v 1 • y - GlobalTheory.LatVac.liftV v 1 • x) ∈ O) ∧
      (∃ O' : Set (κ → AF F), IsOpen O' ∧ y ∈ O' ∧ ∀ x ∈ O', Ψ x ≠ 0 → 1 / 2 ≤ h x) ∧
      ∫⁻ x, h x * ‖Ψ x‖ₑ ^ 2 ∂μ = ∫⁻ x, h x * ‖Φ x‖ₑ ^ 2 ∂μ := GlobalTheory.T.exists_localizingWeight_equal_offPlaceMasses

/- English proof (translation)
The claim follows from `GlobalTheory.T.addCharDotMul_mem_adelicSchwartzSpace`.
-/
theorem lc : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ b : κ → AF F, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
    (fun x => ψ (x ⬝ᵥ b) * Φ x) ∈ GlobalTheory.WeilM.schA F κ := GlobalTheory.T.addCharDotMul_mem_adelicSchwartzSpace

open scoped Classical in
/- English proof (translation)
Use `set e := GlobalTheory.LatVac.liftV v (1 : Fv F v) with he_def`. Set `ι : FiniteAdeleRing (𝓞 F) F → AF F` to `fun a => (0, a)`. Establish `hι : Continuous ι` using `continuous_const.prodMk continuous_id`. Set `Θ : (κ → FiniteAdeleRing (𝓞 F) F) → (κ → AF F)` to `fun z => e • fun i => ι (z i)`. Establish `hΘ : Continuous Θ`.

Use `(continuous_const_smul e).comp (continuous_pi fun i => ?_)` and prove the remaining obligations. Conclude with `hι.comp (continuous_apply i)`. Establish `he1 : e.1 = 0` using `rfl`. Use `⟨Θ '' tsupport g, hg.2.isCompact.image hΘ, fun x hx => ⟨fun i => (x i).2, ?_, ?_⟩⟩` and prove the remaining obligations. Use `subset_tsupport _ ?_` and prove the remaining obligations.

Introduce `h0`. Apply `hx` to reduce the goal to its premises. Simplify using `only [GlobalTheory.WeilM.pureA]`. Rewrite using `[h0, mul_zero]`. Use function extensionality and compare the values at `i show e * ι (x i).2 = e * x i`.

Use `Prod.ext ?_ rfl` and prove the remaining obligations. Use `show e.1 * 0 = e.1 * (x i).1`. Rewrite using `[he1, zero_mul, zero_mul]`.
-/
theorem ls_pure {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ K : Set (κ → AF F), IsCompact K ∧ ∀ x, GlobalTheory.WeilM.pureA F f g x ≠ 0 → GlobalTheory.LatVac.liftV v 1 • x ∈ K := by
  set e := GlobalTheory.LatVac.liftV v (1 : Fv F v) with he_def
  let ι : FiniteAdeleRing (𝓞 F) F → AF F := fun a => (0, a)
  have hι : Continuous ι := continuous_const.prodMk continuous_id
  let Θ : (κ → FiniteAdeleRing (𝓞 F) F) → (κ → AF F) := fun z => e • fun i => ι (z i)
  have hΘ : Continuous Θ := by
    refine (continuous_const_smul e).comp (continuous_pi fun i => ?_)
    exact hι.comp (continuous_apply i)
  have he1 : e.1 = 0 := rfl
  refine ⟨Θ '' tsupport g, hg.2.isCompact.image hΘ, fun x hx => ⟨fun i => (x i).2, ?_, ?_⟩⟩
  · refine subset_tsupport _ ?_
    intro h0
    apply hx
    simp only [GlobalTheory.WeilM.pureA]
    rw [h0, mul_zero]
  · funext i
    show e * ι (x i).2 = e * x i
    refine Prod.ext ?_ rfl
    show e.1 * 0 = e.1 * (x i).1
    rw [he1, zero_mul, zero_mul]

/- English proof (translation)
Introduce `F _ _ κ _ v Φ hΦ`. Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem Φ h`. Take `⟨f, g, hg, rfl⟩` from `h`. Conclude with `ls_pure v f g hg`.

Consider the case `zero => exact ⟨∅, isCompact_empty, fun x hx => (hx rfl).elim⟩`. Consider the case `add Φ₁ Φ₂ _ _ h1 h2`. Take `⟨K₁, hK₁, h₁⟩` from `h1`. Take `⟨K₂, hK₂, h₂⟩` from `h2`. Use `⟨K₁ ∪ K₂, hK₁.union hK₂, fun x hx => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hx1 : Φ₁ x = 0`. Conclude with `Or.inr (h₂ x fun hx2 => hx (by simp [hx1, hx2]))`. Conclude with `Or.inl (h₁ x hx1)`. Consider the case `smul c Φ _ h`. Take `⟨K, hK, hs⟩` from `h`.

Conclude with `⟨K, hK, fun x hx => hs x fun h0 => hx (by simp [h0])⟩`.
-/
theorem ls : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F),
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∃ K : Set (κ → AF F), IsCompact K ∧ ∀ x, Φ x ≠ 0 → GlobalTheory.LatVac.liftV v 1 • x ∈ K := by
  intro F _ _ κ _ v Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact ls_pure v f g hg
  | zero => exact ⟨∅, isCompact_empty, fun x hx => (hx rfl).elim⟩
  | add Φ₁ Φ₂ _ _ h1 h2 =>
    obtain ⟨K₁, hK₁, h₁⟩ := h1
    obtain ⟨K₂, hK₂, h₂⟩ := h2
    refine ⟨K₁ ∪ K₂, hK₁.union hK₂, fun x hx => ?_⟩
    by_cases hx1 : Φ₁ x = 0
    · exact Or.inr (h₂ x fun hx2 => hx (by simp [hx1, hx2]))
    · exact Or.inl (h₁ x hx1)
  | smul c Φ _ h =>
    obtain ⟨K, hK, hs⟩ := h
    exact ⟨K, hK, fun x hx => hs x fun h0 => hx (by simp [h0])⟩

/- English proof (translation)
Establish `h` using `GlobalTheory.LatVac.at_liftV v (1 : Fv F v) (GlobalTheory.LatVac.liftV v 1 - 1) (by rw [map_sub, GlobalTheory.LatVac.evFin_liftV, map_one, sub_self])`. Rewrite `h` using `[smul_eq_mul, sub_mul, one_mul, sub_eq_zero]`. Conclude with `h`.
-/
theorem liftV_mul_self {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) :
    GlobalTheory.LatVac.liftV v (1 : Fv F v) * GlobalTheory.LatVac.liftV v 1 = GlobalTheory.LatVac.liftV v 1 := by
  have h := GlobalTheory.LatVac.at_liftV v (1 : Fv F v) (GlobalTheory.LatVac.liftV v 1 - 1)
    (by rw [map_sub, GlobalTheory.LatVac.evFin_liftV, map_one, sub_self])
  rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h
  exact h

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1` using `h (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, GlobalTheory.LatVac.evFin_liftV, map_one, sub_self])`. Rewrite `h1` using `[sub_smul, one_smul, sub_eq_zero]`. Conclude with `h1.symm`.

Introduce `h u hu`. Rewrite using `[← h, smul_smul]`. Use `GlobalTheory.LatVac.at_liftV v (1 : Fv F v) u hu` as an intermediate fact. Rewrite `this` using `[smul_eq_mul]`. Rewrite using `[this, zero_smul]`.
-/
theorem at_iff {F : Type} [Field F] [NumberField F] {κ : Type} (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (z : κ → AF F) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z ↔ GlobalTheory.LatVac.liftV v 1 • z = z := by
  constructor
  · intro h
    have h1 := h (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, GlobalTheory.LatVac.evFin_liftV, map_one, sub_self])
    rw [sub_smul, one_smul, sub_eq_zero] at h1
    exact h1.symm
  · intro h u hu
    rw [← h, smul_smul]
    have := GlobalTheory.LatVac.at_liftV v (1 : Fv F v) u hu
    rw [smul_eq_mul] at this
    rw [this, zero_smul]

/- English proof (translation)
Introduce `F _ _ κ _ v ψ T hstd hnt hpres hiso hcomm Φ hΦ y hy`. Use `letI : MeasurableSpace (κ → AF F) := borel _`. Use `haveI : BorelSpace (κ → AF F) := ⟨rfl⟩`. Use `set e := GlobalTheory.LatVac.liftV v (1 : Fv F v) with he_def`. Establish `he0 : evFin F v (1 - e) = 0` using `by rw [map_sub, he_def, GlobalTheory.LatVac.evFin_liftV, map_one, sub_self]`.

Set `P : (κ → AF F) →+ (κ → AF F)` to `DistribMulAction.toAddMonoidHom _ e`. Establish `hPc : Continuous P` using `continuous_const_smul e`. Establish `hPP : ∀ x, P (P x) = P x` using `fun x => by show e • e • x = e • x`. Rewrite using `[smul_smul, he_def, liftV_mul_self]`. Establish `hTΦ` using `hpres Φ hΦ`.

Take `⟨K, hK, hKs⟩` from `ls v Φ hΦ`. Set `μ : Measure (κ → AF F)` to `Measure.addHaar`. Use `lp μ P hPc hPP Φ (T Φ) (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hΦ) (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hTΦ) K hK hKs y (fun z hz => hy z ((at_iff v z).2 hz)) ?_` and prove the remaining obligations. Introduce `O hO hyO`. Establish `htrig : ∀ (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ), (∀ b ∈ s, e • b = 0) → ∫⁻ x, ‖(∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * T Φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖(∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * Φ x‖ₑ ^ 2 ∂μ`.

Introduce `s c hs`. Establish `hchar : ∀ b ∈ s, ∀ Ψ ∈ schA F κ, T (fun x => ψ (x ⬝ᵥ b) * Ψ x) = fun x => ψ (x ⬝ᵥ b) * T Ψ x`. Introduce `b hb Ψ hΨ`. Establish `h1` using `hcomm (1 - e) he0 0 b Ψ hΨ`. Establish `hb' : (1 - e) • b = b` using `by rw [sub_smul, one_smul, hs b hb, sub_zero]`.

Establish `hs0 : ∀ Ψ' : (κ → AF F) → ℂ, schr ψ ((1 - e) • (0 : κ → AF F), (1 - e) • b) Ψ' = fun x => ψ (x ⬝ᵥ b) * Ψ' x`. Introduce `Ψ'`. Use function extensionality and compare the values at `x`. Simplify using `[schr, hb']`. Rewrite `h1` using `[hs0, hs0]`.

Conclude with `h1`. Establish `hsum : ∀ G : (κ → AF F) → ℂ, (fun x => (∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * G x) = ∑ b ∈ s, c b • (fun x => ψ (x ⬝ᵥ b) * G x)`. Introduce `G`. Use function extensionality and compare the values at `x`. Simplify using `[Finset.sum_mul, mul_assoc]`.

Establish `hmem : (fun x => (∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * Φ x) ∈ schA F κ`. Rewrite using `[hsum]`. Conclude with `Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (lc ψ hstd b Φ hΦ)`. Establish `hT : T (fun x => (∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * Φ x) = fun x => (∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * T Φ x`. Rewrite using `[hsum, hsum, map_sum]`.

Use `Finset.sum_congr rfl fun b hb => ?_` and prove the remaining obligations. Rewrite using `[map_smul, hchar b hb Φ hΦ]`. Use `hiso μ inferInstance _ hmem` as an intermediate fact. Rewrite `this` using `[hT]`. Conclude with `this`.

Conclude with `lw v ψ hstd hnt μ inferInstance Φ hΦ (T Φ) hTΦ htrig y O hO hyO`.
-/
theorem eq_zero_of_vanish_fibre : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (ψ : AddChar (AF F) ℂ) (T : Module.End ℂ ((κ → AF F) → ℂ)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → (∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1) →
    (∀ Φ ∈ GlobalTheory.WeilM.schA F κ, T Φ ∈ GlobalTheory.WeilM.schA F κ) →
    (∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∫⁻ y, ‖T Φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖Φ y‖ₑ ^ 2 ∂μ) →
    (∀ u : AF F, evFin F v u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
      T (GlobalTheory.WeilM.schr ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr ψ (u • p, u • q) (T Φ)) →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ y : κ → AF F, (∀ z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → Φ (y + z) = 0) → T Φ y = 0 := by
  intro F _ _ κ _ v ψ T hstd hnt hpres hiso hcomm Φ hΦ y hy
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  set e := GlobalTheory.LatVac.liftV v (1 : Fv F v) with he_def
  have he0 : evFin F v (1 - e) = 0 := by rw [map_sub, he_def, GlobalTheory.LatVac.evFin_liftV, map_one, sub_self]
  let P : (κ → AF F) →+ (κ → AF F) := DistribMulAction.toAddMonoidHom _ e
  have hPc : Continuous P := continuous_const_smul e
  have hPP : ∀ x, P (P x) = P x := fun x => by
    show e • e • x = e • x
    rw [smul_smul, he_def, liftV_mul_self]
  have hTΦ := hpres Φ hΦ
  obtain ⟨K, hK, hKs⟩ := ls v Φ hΦ
  let μ : Measure (κ → AF F) := Measure.addHaar
  refine lp μ P hPc hPP Φ (T Φ) (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hΦ)
    (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hTΦ) K hK hKs y
    (fun z hz => hy z ((at_iff v z).2 hz)) ?_
  intro O hO hyO
  have htrig : ∀ (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ), (∀ b ∈ s, e • b = 0) →
      ∫⁻ x, ‖(∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * T Φ x‖ₑ ^ 2 ∂μ =
        ∫⁻ x, ‖(∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * Φ x‖ₑ ^ 2 ∂μ := by
    intro s c hs
    have hchar : ∀ b ∈ s, ∀ Ψ ∈ schA F κ,
        T (fun x => ψ (x ⬝ᵥ b) * Ψ x) = fun x => ψ (x ⬝ᵥ b) * T Ψ x := by
      intro b hb Ψ hΨ
      have h1 := hcomm (1 - e) he0 0 b Ψ hΨ
      have hb' : (1 - e) • b = b := by rw [sub_smul, one_smul, hs b hb, sub_zero]
      have hs0 : ∀ Ψ' : (κ → AF F) → ℂ,
          schr ψ ((1 - e) • (0 : κ → AF F), (1 - e) • b) Ψ' = fun x => ψ (x ⬝ᵥ b) * Ψ' x := by
        intro Ψ'; funext x; simp [schr, hb']
      rw [hs0, hs0] at h1
      exact h1
    have hsum : ∀ G : (κ → AF F) → ℂ, (fun x => (∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * G x) =
        ∑ b ∈ s, c b • (fun x => ψ (x ⬝ᵥ b) * G x) := by
      intro G; funext x; simp [Finset.sum_mul, mul_assoc]
    have hmem : (fun x => (∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * Φ x) ∈ schA F κ := by
      rw [hsum]
      exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (lc ψ hstd b Φ hΦ)
    have hT : T (fun x => (∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * Φ x) =
        fun x => (∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * T Φ x := by
      rw [hsum, hsum, map_sum]
      refine Finset.sum_congr rfl fun b hb => ?_
      rw [map_smul, hchar b hb Φ hΦ]
    have := hiso μ inferInstance _ hmem
    rw [hT] at this
    exact this
  exact lw v ψ hstd hnt μ inferInstance Φ hΦ (T Φ) hTΦ htrig y O hO hyO

end GlobalTheory.FibreLocality
