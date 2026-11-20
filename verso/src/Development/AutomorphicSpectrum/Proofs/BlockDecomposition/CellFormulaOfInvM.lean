import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.CellAbs

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.RswCell

open PositivityTheory.Rg.Rsw.Cell

variable {G : Type} [Group G] [TopologicalSpace G]

/- English proof (translation)
Take `⟨k, hk⟩` from `QuotientGroup.mk_out_eq_mul P g`. Use `⟨(k : G)⁻¹, P.inv_mem k.2, ?_⟩` and prove the remaining obligations. Establish `: Quotient.out (QuotientGroup.mk g : G ⧸ P) = g * k` using `hk`. Simplify using `[rp, this]`.
-/
lemma rp_mk (P : Subgroup G) (g : G) : ∃ p ∈ P, rp (QuotientGroup.mk g : G ⧸ P) = p * g⁻¹ := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul P g
  refine ⟨(k : G)⁻¹, P.inv_mem k.2, ?_⟩
  have : Quotient.out (QuotientGroup.mk g : G ⧸ P) = g * k := hk
  simp [rp, this]

/- English proof (translation)
Take `⟨p, hp, e⟩` from `rp_mk P (x⁻¹ * Quotient.out q)`. Use `⟨p, hp, ?_⟩` and prove the remaining obligations. Establish `hq : (QuotientGroup.mk (x⁻¹ * Quotient.out q) : G ⧸ P) = x⁻¹ • q` using `by conv_rhs => rw [← QuotientGroup.out_eq' q]`. Both sides reduce to the same expression. Rewrite using `[← hq, e]`.

Simplify using `[rp]`.
-/
lemma rp_smul (P : Subgroup G) (x : G) (q : G ⧸ P) : ∃ p ∈ P, rp (x⁻¹ • q) = p * (rp q * x) := by
  obtain ⟨p, hp, e⟩ := rp_mk P (x⁻¹ * Quotient.out q)
  refine ⟨p, hp, ?_⟩
  have hq : (QuotientGroup.mk (x⁻¹ * Quotient.out q) : G ⧸ P) = x⁻¹ • q := by
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [← hq, e]
  simp [rp]

/- English proof (translation)
Take `⟨p, hp, e⟩` from `rp_mk P g`. Rewrite using `[e]`. Use `⟨fun H => ?_, hl p hp _⟩` and prove the remaining obligations. Simplify using `using hl p⁻¹ (P.inv_mem hp) _ H`.
-/
lemma rp_mk_mem_iff {P : Subgroup G} {Ω : Set G} (hl : ∀ p ∈ P, ∀ x ∈ Ω, p * x ∈ Ω) (g : G) :
    rp (QuotientGroup.mk g : G ⧸ P) ∈ Ω ↔ g⁻¹ ∈ Ω := by
  obtain ⟨p, hp, e⟩ := rp_mk P g
  rw [e]
  refine ⟨fun H => ?_, hl p hp _⟩
  simpa using hl p⁻¹ (P.inv_mem hp) _ H

def coord {N : Type} [Zero N] {P : Subgroup G} (Ω : Set G) (τ : G → N) (q : G ⧸ P) : N :=
  open Classical in if rp q ∈ Ω then τ (rp q) else 0

/- English proof (translation)
Simplify using `[coord, hq]`.
-/
lemma coord_of_mem {N : Type} [Zero N] {P : Subgroup G} {Ω : Set G} {τ : G → N} {q : G ⧸ P}
    (hq : rp q ∈ Ω) : coord Ω τ q = τ (rp q) := by
  simp [coord, hq]

/- English proof (translation)
Establish `hl' : ∀ p ∈ P, ∀ x ∈ Ω, p * x ∈ Ω` using `fun p hp x hx => (hl p hp x hx).1`. Rewrite using `[← (QuotientGroup.isOpenQuotientMap_mk (N := P)).isQuotientMap.isOpen_preimage]`. Establish `: (QuotientGroup.mk : G → G ⧸ P) ⁻¹' {q : G ⧸ P | rp q ∈ Ω ∧ τ (rp q) ∈ U} = (fun g : G => g⁻¹) ⁻¹' (Ω ∩ τ ⁻¹' U)`. Use extensionality with `g`. Simplify using `only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_inter_iff]`.

Rewrite using `[rp_mk_mem_iff hl' g]`. Take `⟨p, hp, e⟩` from `rp_mk P g`. Use `and_congr_right fun hg => ?_` and prove the remaining obligations. Rewrite using `[e, (hl p hp _ hg).2]`. Rewrite using `[this]`.

Conclude with `(hτ.isOpen_inter_preimage hΩ hU).preimage continuous_inv`.
-/
lemma isOpen_bar [IsTopologicalGroup G] {N : Type} [TopologicalSpace N] {P : Subgroup G} {Ω : Set G}
    {τ : G → N} (hΩ : IsOpen Ω) (hl : ∀ p ∈ P, ∀ x ∈ Ω, p * x ∈ Ω ∧ τ (p * x) = τ x)
    (hτ : ContinuousOn τ Ω) {U : Set N} (hU : IsOpen U) :
    IsOpen {q : G ⧸ P | rp q ∈ Ω ∧ τ (rp q) ∈ U} := by
  have hl' : ∀ p ∈ P, ∀ x ∈ Ω, p * x ∈ Ω := fun p hp x hx => (hl p hp x hx).1
  rw [← (QuotientGroup.isOpenQuotientMap_mk (N := P)).isQuotientMap.isOpen_preimage]
  have : (QuotientGroup.mk : G → G ⧸ P) ⁻¹' {q : G ⧸ P | rp q ∈ Ω ∧ τ (rp q) ∈ U}
      = (fun g : G => g⁻¹) ⁻¹' (Ω ∩ τ ⁻¹' U) := by
    ext g
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_inter_iff]
    rw [rp_mk_mem_iff hl' g]
    obtain ⟨p, hp, e⟩ := rp_mk P g
    refine and_congr_right fun hg => ?_
    rw [e, (hl p hp _ hg).2]
  rw [this]
  exact (hτ.isOpen_inter_preimage hΩ hU).preimage continuous_inv

/- English proof (translation)
Use `measurable_of_isOpen fun U hU => ?_` and prove the remaining obligations. Establish `hA` using `(isOpen_bar (P := P) hΩ hl hτ hU).measurableSet`. Establish `hB : MeasurableSet {q : G ⧸ P | rp q ∈ Ω}`. Use `(isOpen_bar (P := P) hΩ hl hτ (isOpen_univ (X := N))).measurableSet` as an intermediate fact. Simplify using `using this`.

Distinguish the cases in `h0 : (0 : N) ∈ U`. Establish `: (coord Ω τ : G ⧸ P → N) ⁻¹' U = {q : G ⧸ P | rp q ∈ Ω ∧ τ (rp q) ∈ U} ∪ {q : G ⧸ P | rp q ∈ Ω}ᶜ`. Use extensionality with `q`. Apply the tactic sequence `by_cases hq : rp q ∈ Ω <;> simp [coord, hq, h0]`. Rewrite using `[this]`.

Conclude with `hA.union hB.compl`. Establish `: (coord Ω τ : G ⧸ P → N) ⁻¹' U = {q : G ⧸ P | rp q ∈ Ω ∧ τ (rp q) ∈ U}`. Use extensionality with `q`. Apply the tactic sequence `by_cases hq : rp q ∈ Ω <;> simp [coord, hq, h0]`. Rewrite using `[this]`.

Conclude with `hA`.
-/
lemma measurable_coord [IsTopologicalGroup G] {N : Type} [AddCommGroup N] [TopologicalSpace N]
    [MeasurableSpace N] [BorelSpace N] {P : Subgroup G} [MeasurableSpace (G ⧸ P)] [BorelSpace (G ⧸ P)]
    {Ω : Set G} {τ : G → N} (hΩ : IsOpen Ω) (hl : ∀ p ∈ P, ∀ x ∈ Ω, p * x ∈ Ω ∧ τ (p * x) = τ x)
    (hτ : ContinuousOn τ Ω) : Measurable (coord Ω τ : G ⧸ P → N) := by
  refine measurable_of_isOpen fun U hU => ?_
  have hA := (isOpen_bar (P := P) hΩ hl hτ hU).measurableSet
  have hB : MeasurableSet {q : G ⧸ P | rp q ∈ Ω} := by
    have := (isOpen_bar (P := P) hΩ hl hτ (isOpen_univ (X := N))).measurableSet
    simpa using this
  by_cases h0 : (0 : N) ∈ U
  · have : (coord Ω τ : G ⧸ P → N) ⁻¹' U = {q : G ⧸ P | rp q ∈ Ω ∧ τ (rp q) ∈ U} ∪ {q : G ⧸ P | rp q ∈ Ω}ᶜ := by
      ext q
      by_cases hq : rp q ∈ Ω <;> simp [coord, hq, h0]
    rw [this]
    exact hA.union hB.compl
  · have : (coord Ω τ : G ⧸ P → N) ⁻¹' U = {q : G ⧸ P | rp q ∈ Ω ∧ τ (rp q) ∈ U} := by
      ext q
      by_cases hq : rp q ∈ Ω <;> simp [coord, hq, h0]
    rw [this]
    exact hA

/- English proof (translation)
Introduce `G _ _ _ _ _ _ P _ _ h mu hs ν hν N _ _ _ _ _ _ _ _ lam _ Ω τ w nb hc hInv hh hnull`. Use `haveI : IsFiniteMeasure ν := hν.1`. Establish `ρc : Continuous fun y => h (w * nb y)` using `hs.cont.comp (continuous_const.mul hc.nbCont)`. Establish `ρpos : ∀ y, 0 < h (w * nb y)` using `fun y => hs.pos _`. Set `D : N → ℝ≥0` to `fun y => (1 / h (w * nb y)).toNNReal`.

Establish `Dc : Continuous D` using `continuous_real_toNNReal.comp (continuous_const.div ρc fun y => (ρpos y).ne')`. Establish `Dm : Measurable D` using `Dc.measurable`. Set `T : G ⧸ P → N` to `coord Ω τ`. Establish `Tm : Measurable T` using `measurable_coord hc.isOpen hc.left hc.cont`. Set `lam' : Measure N` to `(ν.map T).withDensity fun y => (D y : ℝ≥0∞)`.

Establish `hlin : ∀ φ : N → ℝ≥0∞, Measurable φ → ∫⁻ y, φ y ∂lam' = ∫⁻ q, (D (T q) : ℝ≥0∞) * φ (T q) ∂ν`. Introduce `φ hφ`. Establish `h1 : Measurable fun y => (D y : ℝ≥0∞)` using `Dm.coe_nnreal_ennreal`. Rewrite using `[lintegral_withDensity_eq_lintegral_mul _ h1 hφ, lintegral_map (h1.mul hφ) Tm]`. Both sides reduce to the same expression.

Establish `hae : ∀ᵐ q ∂ν, rp q ∈ Ω`. Rewrite using `[ae_iff]`. Conclude with `hnull`. Establish `hshift : ∀ (a : N) (φ : N → ℝ≥0∞), Measurable φ → ∫⁻ q, (D (T q) : ℝ≥0∞) * φ (a + T q) ∂ν = ∫⁻ q, (D (T q) : ℝ≥0∞) * φ (T q) ∂ν`. Introduce `a φ hφ`.

Establish `hF : Measurable fun q => (D (T q) : ℝ≥0∞) * φ (T q)` using `((Dm.comp Tm).coe_nnreal_ennreal).mul (hφ.comp Tm)`. Rewrite using `[← (hI G P h mu hs ν hν (nb a) (hInv a)).2 _ hF]`. Use `lintegral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hae] with q hq`. Take `⟨p, hp, e⟩` from `rp_smul P (nb a) q`.

Establish `hr` using `hc.right a _ hq`. Establish `hl` using `hc.left p hp _ hr.1`. Establish `hmem : rp ((nb a)⁻¹ • q) ∈ Ω` using `e ▸ hl.1`. Establish `e1 : T ((nb a)⁻¹ • q) = τ (rp q) + a`. Express the relevant statement in the definitionally equal form `coord Ω τ _ = _`.

Rewrite using `[coord_of_mem hmem, e, hl.2, hr.2]`. Establish `e0 : T q = τ (rp q)` using `coord_of_mem hq`. Rewrite using `[e1, e0, add_comm a]`. Establish `hq1` using `hh a _ hq`. Use `set y := τ (rp q)`.

Establish `p1` using `ρpos y`. Establish `p2` using `ρpos (y + a)`. Establish `p3` using `hs.pos (rp q)`. Establish `hD : (D y : ℝ≥0∞) = (D (y + a) : ℝ≥0∞) * ENNReal.ofReal (h (rp q * nb a) / h (rp q))`. Express the relevant statement in the definitionally equal form `ENNReal.ofReal _ = ENNReal.ofReal _ * _`.

Rewrite using `[← ENNReal.ofReal_mul (by positivity)]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hD]`.

Expand and normalize the polynomial expressions, which then agree. Use `haveI hinv : lam'.IsAddLeftInvariant := by`. Use `⟨fun a => Measure.ext fun S hS => ?_⟩` and prove the remaining obligations. Rewrite using `[Measure.map_apply (measurable_const_add a) hS]`. Establish `hS' : MeasurableSet ((fun y => a + y) ⁻¹' S)` using `measurable_const_add a hS`.

Establish `hi : Measurable (S.indicator (1 : N → ℝ≥0∞))` using `measurable_one.indicator hS`. Establish `hi' : ((fun y => a + y) ⁻¹' S).indicator (1 : N → ℝ≥0∞) = fun y => S.indicator (1 : N → ℝ≥0∞) (a + y)`. Use extensionality with `y`. Distinguish the cases in `hy : a + y ∈ S`. Rewrite using `[Set.indicator_of_mem (show y ∈ (fun y => a + y) ⁻¹' S from hy), Set.indicator_of_mem hy]`.

Both sides reduce to the same expression. Rewrite using `[Set.indicator_of_notMem (show y ∉ (fun y => a + y) ⁻¹' S from hy), Set.indicator_of_notMem hy]`. Establish `hi2 : Measurable fun y => S.indicator (1 : N → ℝ≥0∞) (a + y)` using `hi.comp (measurable_const_add a)`. Rewrite using `[← lintegral_indicator_one hS', ← lintegral_indicator_one hS, hi', hlin _ hi2, hlin _ hi]`. Conclude with `hshift a _ hi`.

Use `haveI : IsLocallyFiniteMeasure lam' := IsLocallyFiniteMeasure.withDensity_coe Dc`. Establish `e` using `Measure.isAddLeftInvariant_eq_smul lam' lam`. Use `⟨Measure.addHaarScalarFactor lam' lam, fun f hf hoc => ?_⟩` and prove the remaining obligations. Rewrite using `[← e]`. Establish `gc : Continuous fun y => f (w * nb y)` using `hf.1.comp (continuous_const.mul hc.nbCont)`.

Establish `ψc : Continuous fun y => D y • f (w * nb y)` using `Dc.smul gc`. Establish `hcomp : (fun q => D (T q) • f (w * nb (T q))) =ᵐ[ν] fun q => f (rp q) / h (rp q)` using `by filter_upwards [hae] with q hq`. Establish `e0 : T q = τ (rp q)` using `coord_of_mem hq`. Rewrite using `[e0]`. Establish `h1` using `hoc _ hq`.

Use `set y := τ (rp q)`. Establish `p1` using `ρpos y`. Establish `p3` using `hs.pos (rp q)`. Establish `hDy : ((D y : ℝ≥0) : ℝ) = 1 / h (w * nb y)` using `Real.coe_toNNReal _ (by positivity)`. Establish `c1 : (h (w * nb y) : ℂ) ≠ 0` using `by exact_mod_cast p1.ne'`.

Establish `c3 : (h (rp q) : ℂ) ≠ 0` using `by exact_mod_cast p3.ne'`. Rewrite using `[NNReal.smul_def, Complex.real_smul, hDy]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Take the linear combination `-h1`.

Take `⟨hint, hmu⟩` from `hν.2 f hf`. Prove the components needed by the constructor for the conclusion. Use `(integrable_withDensity_iff_integrable_smul Dm).2 ?_` and prove the remaining obligations. Use `(integrable_map_measure ψc.aestronglyMeasurable Tm.aemeasurable).2 ?_` and prove the remaining obligations. Conclude with `hint.congr hcomp.symm`.

Rewrite using `[hmu]`. Express the relevant statement in the definitionally equal form `_ = ∫ y, f (w * nb y) ∂((ν.map T).withDensity fun y => (D y : ℝ≥0∞))`. Rewrite using `[integral_withDensity_eq_integral_smul Dm, integral_map Tm.aemeasurable ψc.aestronglyMeasurable]`. Conclude with `(integral_congr_ae hcomp).symm`.
-/
theorem cellFormula_of_invM (hI : InvM) : CellFormula := by
  intro G _ _ _ _ _ _ P _ _ h mu hs ν hν N _ _ _ _ _ _ _ _ lam _ Ω τ w nb hc hInv hh hnull
  haveI : IsFiniteMeasure ν := hν.1
  have ρc : Continuous fun y => h (w * nb y) := hs.cont.comp (continuous_const.mul hc.nbCont)
  have ρpos : ∀ y, 0 < h (w * nb y) := fun y => hs.pos _
  let D : N → ℝ≥0 := fun y => (1 / h (w * nb y)).toNNReal
  have Dc : Continuous D :=
    continuous_real_toNNReal.comp (continuous_const.div ρc fun y => (ρpos y).ne')
  have Dm : Measurable D := Dc.measurable
  let T : G ⧸ P → N := coord Ω τ
  have Tm : Measurable T := measurable_coord hc.isOpen hc.left hc.cont
  let lam' : Measure N := (ν.map T).withDensity fun y => (D y : ℝ≥0∞)
  have hlin : ∀ φ : N → ℝ≥0∞, Measurable φ →
      ∫⁻ y, φ y ∂lam' = ∫⁻ q, (D (T q) : ℝ≥0∞) * φ (T q) ∂ν := by
    intro φ hφ
    have h1 : Measurable fun y => (D y : ℝ≥0∞) := Dm.coe_nnreal_ennreal
    rw [lintegral_withDensity_eq_lintegral_mul _ h1 hφ, lintegral_map (h1.mul hφ) Tm]
    rfl
  have hae : ∀ᵐ q ∂ν, rp q ∈ Ω := by
    rw [ae_iff]
    exact hnull
  have hshift : ∀ (a : N) (φ : N → ℝ≥0∞), Measurable φ →
      ∫⁻ q, (D (T q) : ℝ≥0∞) * φ (a + T q) ∂ν = ∫⁻ q, (D (T q) : ℝ≥0∞) * φ (T q) ∂ν := by
    intro a φ hφ
    have hF : Measurable fun q => (D (T q) : ℝ≥0∞) * φ (T q) :=
      ((Dm.comp Tm).coe_nnreal_ennreal).mul (hφ.comp Tm)
    rw [← (hI G P h mu hs ν hν (nb a) (hInv a)).2 _ hF]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with q hq
    obtain ⟨p, hp, e⟩ := rp_smul P (nb a) q
    have hr := hc.right a _ hq
    have hl := hc.left p hp _ hr.1
    have hmem : rp ((nb a)⁻¹ • q) ∈ Ω := e ▸ hl.1
    have e1 : T ((nb a)⁻¹ • q) = τ (rp q) + a := by
      change coord Ω τ _ = _
      rw [coord_of_mem hmem, e, hl.2, hr.2]
    have e0 : T q = τ (rp q) := coord_of_mem hq
    rw [e1, e0, add_comm a]
    have hq1 := hh a _ hq
    set y := τ (rp q)
    have p1 := ρpos y
    have p2 := ρpos (y + a)
    have p3 := hs.pos (rp q)
    have hD : (D y : ℝ≥0∞) = (D (y + a) : ℝ≥0∞) * ENNReal.ofReal (h (rp q * nb a) / h (rp q)) := by
      change ENNReal.ofReal _ = ENNReal.ofReal _ * _
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
      linarith
    rw [hD]
    ring
  haveI hinv : lam'.IsAddLeftInvariant := by
    refine ⟨fun a => Measure.ext fun S hS => ?_⟩
    rw [Measure.map_apply (measurable_const_add a) hS]
    have hS' : MeasurableSet ((fun y => a + y) ⁻¹' S) := measurable_const_add a hS
    have hi : Measurable (S.indicator (1 : N → ℝ≥0∞)) := measurable_one.indicator hS
    have hi' : ((fun y => a + y) ⁻¹' S).indicator (1 : N → ℝ≥0∞)
        = fun y => S.indicator (1 : N → ℝ≥0∞) (a + y) := by
      ext y
      by_cases hy : a + y ∈ S
      · rw [Set.indicator_of_mem (show y ∈ (fun y => a + y) ⁻¹' S from hy), Set.indicator_of_mem hy]
        rfl
      · rw [Set.indicator_of_notMem (show y ∉ (fun y => a + y) ⁻¹' S from hy),
          Set.indicator_of_notMem hy]
    have hi2 : Measurable fun y => S.indicator (1 : N → ℝ≥0∞) (a + y) :=
      hi.comp (measurable_const_add a)
    rw [← lintegral_indicator_one hS', ← lintegral_indicator_one hS, hi', hlin _ hi2, hlin _ hi]
    exact hshift a _ hi
  haveI : IsLocallyFiniteMeasure lam' := IsLocallyFiniteMeasure.withDensity_coe Dc
  have e := Measure.isAddLeftInvariant_eq_smul lam' lam
  refine ⟨Measure.addHaarScalarFactor lam' lam, fun f hf hoc => ?_⟩
  rw [← e]
  have gc : Continuous fun y => f (w * nb y) := hf.1.comp (continuous_const.mul hc.nbCont)
  have ψc : Continuous fun y => D y • f (w * nb y) := Dc.smul gc
  have hcomp : (fun q => D (T q) • f (w * nb (T q))) =ᵐ[ν] fun q => f (rp q) / h (rp q) := by
    filter_upwards [hae] with q hq
    have e0 : T q = τ (rp q) := coord_of_mem hq
    rw [e0]
    have h1 := hoc _ hq
    set y := τ (rp q)
    have p1 := ρpos y
    have p3 := hs.pos (rp q)
    have hDy : ((D y : ℝ≥0) : ℝ) = 1 / h (w * nb y) := Real.coe_toNNReal _ (by positivity)
    have c1 : (h (w * nb y) : ℂ) ≠ 0 := by exact_mod_cast p1.ne'
    have c3 : (h (rp q) : ℂ) ≠ 0 := by exact_mod_cast p3.ne'
    rw [NNReal.smul_def, Complex.real_smul, hDy]
    push_cast
    field_simp
    linear_combination -h1
  obtain ⟨hint, hmu⟩ := hν.2 f hf
  constructor
  · refine (integrable_withDensity_iff_integrable_smul Dm).2 ?_
    refine (integrable_map_measure ψc.aestronglyMeasurable Tm.aemeasurable).2 ?_
    exact hint.congr hcomp.symm
  · rw [hmu]
    change _ = ∫ y, f (w * nb y) ∂((ν.map T).withDensity fun y => (D y : ℝ≥0∞))
    rw [integral_withDensity_eq_integral_smul Dm, integral_map Tm.aemeasurable ψc.aestronglyMeasurable]
    exact (integral_congr_ae hcomp).symm

end GlobalTheory.CompanionTheory.RswCell
