import Mathlib
import Development.WeilBound.CoreStatements.ThetaDilations.BoundedA
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RealQuadraticFormLemma
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SchurFunctionSmoothRightInvariant

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Core0

section Theta

open GlobalTheory.CompanionTheory.SW.CoefTheta

/- English proof (translation)
Introduce `F _ _ _ _ ι _ _ M B ρ P hQ Ω _ Pr gf gi hC a ha β N hN hNβ hint D hD`. Use `haveI : Countable F := countable_field`. Take `⟨hTR, -, -, -, hρ, -, -⟩` from `id hQ`. Take `⟨hprob, -, -, hOrth, -⟩` from `id hC`. Take `⟨-, -, hT2, hOc, hOo, -, hmem, -, -, -⟩` from `GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F`.

Take `⟨-, -, -, hfd⟩` from `GlobalTheory.T.lattice_fundamental_domain_volume F hTR ρ hρ N hN`. Take `⟨hvol, horth⟩` from `hfd D hD`. Establish `hsb : SB (indL a : (ι → A F) → ℂ)` using `sb_indL hT2 hOc hOo ha`. Take `⟨C, hCb⟩` from `GlobalTheory.T.weighted_theta_average_le_of_countData F ι M B ρ P hQ Ω Pr gf gi hC (indL a) hsb 1 1 one_pos one_pos`. Take `⟨hmeas, hbound⟩` from `hCb (fun _ => Complex.I) (by simp) (by simp)`.

Use `set s : (ι → F) → Ω → ℂ := fun z ω => thTerm B ρ P (gf ω) (gi ω) (indL a) (fun _ => Complex.I) z with hs`. Establish `hm : ∀ z, Measurable (s z)` using `hmeas`. Establish `hwt : wt M (fun _ : InfinitePlace F => Complex.I) = 1` using `by simp [wt]`. Establish `hnz : ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0}, ‖s x.1 ω‖ₑ ∂Pr ≠ ∞`. Rewrite `hbound` using `[hwt, ENNReal.ofReal_one, one_mul]`.

Conclude with `ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound`. Establish `hfin : ∫⁻ ω, ∑' z, ‖s z ω‖ₑ ∂Pr ≠ ∞`. Establish `hle : ∀ ω, ∑' z, ‖s z ω‖ₑ ≤ 1 + ∑' x : {x : ι → F // x ≠ 0}, ‖s x.1 ω‖ₑ`. Introduce `ω`. Rewrite using `[ENNReal.tsum_eq_add_tsum_ite 0]`.

Use `add_le_add (thTerm_zero_le B ρ P (gf ω) (gi ω) a) (le_of_eq ?_)` and prove the remaining obligations. Use `tsum_subtype {x : ι → F | x ≠ 0} (fun z => ‖s z ω‖ₑ)` as an intermediate fact. Use `Eq.trans ?_ this.symm` and prove the remaining obligations. Use `tsum_congr fun z => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases h : z = 0 <;> simp [h]`.

Use `ne_top_of_le_ne_top ?_ (lintegral_mono hle)` and prove the remaining obligations. Rewrite using `[lintegral_add_left measurable_const]`. Simplify using `only [lintegral_const, measure_univ, mul_one]`. Conclude with `ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, hnz⟩`. Establish `hpos : ∀ z ω, s z ω = ((‖s z ω‖ : ℝ) : ℂ)` using `fun z ω => thTerm_nonneg B ρ P (gf ω) (gi ω) a z`.

Use `set Sel : Set (ι → F) := {z | qf (1 / 2 : F) B z = β} with hSel`. Use `haveI : IsFiniteMeasure ((volume : Measure (InfinitePlace F → ℝ)).restrict D) := ⟨by rw [Measure.restrict_apply_univ, hvol]; exact ENNReal.ofReal_lt_top⟩`. Establish `hv : Continuous fun x : InfinitePlace F → ℝ => Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ))`. Repeatedly rewrite using `[ph_neg]`. Conclude with `ph_continuous ρ _`.

Establish `hvn : ∀ x : InfinitePlace F → ℝ, ‖Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ))‖ = 1`. Introduce `x`. Rewrite using `[ph_neg, ph_norm]`. Establish `hres` using `fourier_series hm hfin (μ := (volume : Measure (InfinitePlace F → ℝ)).restrict D) (u := fun z => ph ρ (qf (1 / 2 : F) B z)) (fun z => ph_continuous ρ _) (fun z x => ph_norm ρ _ x) hv hvn Sel ((volume D).toReal : ℂ) (by`. Introduce `z hz`.

Establish `hz' : qf (1 / 2 : F) B z = β` using `hz`. Establish `: ∀ x : InfinitePlace F → ℝ, ph ρ (qf (1 / 2 : F) B z) x * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) = 1`. Introduce `x`. Rewrite using `[ph_neg, ph_mul, hz', add_neg_cancel, ph_zero]`. Repeatedly rewrite using `[this]`.

Simplify using `[setIntegral_const, Measure.real])`. Use the proof step `(by`. Introduce `z hz`. Distinguish the cases in `hall : ∀ ω, s z ω = 0`. Conclude with `Or.inr hall`.

Use `left`. Use `push_neg at hall`. Take `⟨ω, hω⟩` from `hall`. Take `⟨r, hr⟩` from `integral_of_ne_zero (hOrth ω) hint hmem hω`. Take `⟨r₀, hr₀⟩` from `hNβ`.

Establish `hne : qf (1 / 2 : F) B z + -β ≠ 0` using `fun h => hz (add_neg_eq_zero.mp h)`. Use `horth _ hne ⟨r - r₀, by` as an intermediate fact. Establish `hsub : ((r - r₀ : 𝓞 F) : F) = (r : F) - (r₀ : F)` using `map_sub (algebraMap (𝓞 F) F) r r₀`. Rewrite using `[hsub, hr, hr₀]`. Use the proof step `ring⟩`.

Establish `hx : ∀ x : InfinitePlace F → ℝ, ph ρ (qf (1 / 2 : F) B z) x * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) = ph ρ (qf (1 / 2 : F) B z + -β) x`. Introduce `x`. Rewrite using `[ph_neg, ph_mul]`. Repeatedly rewrite using `[hx]`. Conclude with `this)`.

Establish `hth : ∀ (x : InfinitePlace F → ℝ) (ω : Ω), theta B ρ P (gf ω) (gi ω) (indL a) (fun w => (x w : ℂ) + Complex.I) = ∑' z, ph ρ (qf (1 / 2 : F) B z) x * s z ω` using `fun x ω => tsum_congr fun z => thTerm_shift P (hOrth ω) _ x z`. Establish `hI : ∫⁻ ω, ∑' x : {x : ι → F // qf (1 / 2 : F) B x = β}, ‖s x.1 ω‖ₑ ∂Pr ≠ ∞` using `ne_top_of_le_ne_top hfin (lintegral_mono fun ω => ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective fun z => ‖s z ω‖ₑ)`. Use `⟨_, (ENNReal.coe_toNNReal hI).symm, ?_, ?_⟩` and prove the remaining obligations. Repeatedly rewrite using `[hth]`. Conclude with `hres.1`.

Repeatedly rewrite using `[hth]`. Rewrite using `[hres.2, sum_selected hm hfin hpos Sel]`. Both sides reduce to the same expression.
-/
theorem fourier_coefficient_any : ∀ (F : Type) [Field F] [NumberField F], ∀ [MeasurableSpace (A F)] [BorelSpace (A F)], ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) (gf : Ω → Matrix ι ι (A F)) (gi : Ω → InfinitePlace F → Matrix ι ι ℝ), CountData M B ρ Pr gf gi → ∀ a : ℕ, 0 < a → ∀ β : F, ∀ N : ℕ, 0 < N → (∃ r : 𝓞 F, (r : F) = (N : F) * β) → (∀ y : ι → A F, (∀ i, (a : A F) * y i ∈ Oh F) → (N : A F) * qf (hf F) (Bf B) y ∈ Oh F) → ∀ D : Set (InfinitePlace F → ℝ), IsAddFundamentalDomain (latR ρ N) D volume → ∃ I : ℝ≥0, ∫⁻ ω, ∑' x : {x : ι → F // qf (1 / 2 : F) B x = β}, ‖thTerm B ρ P (gf ω) (gi ω) (indL a) (fun _ => Complex.I) x.1‖ₑ ∂Pr = (I : ℝ≥0∞) ∧ IntegrableOn (fun x : InfinitePlace F → ℝ => (∫ ω, theta B ρ P (gf ω) (gi ω) (indL a) (fun w => (x w : ℂ) + Complex.I) ∂Pr) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ))) D volume ∧ ∫ x in D, (∫ ω, theta B ρ P (gf ω) (gi ω) (indL a) (fun w => (x w : ℂ) + Complex.I) ∂Pr) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) = ((volume D).toReal : ℂ) * ((I : ℝ) : ℂ) := by
  intro F _ _ _ _ ι _ _ M B ρ P hQ Ω _ Pr gf gi hC a ha β N hN hNβ hint D hD
  haveI : Countable F := countable_field
  obtain ⟨hTR, -, -, -, hρ, -, -⟩ := id hQ
  obtain ⟨hprob, -, -, hOrth, -⟩ := id hC
  obtain ⟨-, -, hT2, hOc, hOo, -, hmem, -, -, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  obtain ⟨-, -, -, hfd⟩ := GlobalTheory.T.lattice_fundamental_domain_volume F hTR ρ hρ N hN
  obtain ⟨hvol, horth⟩ := hfd D hD
  have hsb : SB (indL a : (ι → A F) → ℂ) := sb_indL hT2 hOc hOo ha
  obtain ⟨C, hCb⟩ := GlobalTheory.T.weighted_theta_average_le_of_countData F ι M B ρ P hQ Ω Pr gf gi hC (indL a) hsb 1 1 one_pos one_pos
  obtain ⟨hmeas, hbound⟩ := hCb (fun _ => Complex.I) (by simp) (by simp)
  set s : (ι → F) → Ω → ℂ :=
    fun z ω => thTerm B ρ P (gf ω) (gi ω) (indL a) (fun _ => Complex.I) z with hs
  have hm : ∀ z, Measurable (s z) := hmeas
  have hwt : wt M (fun _ : InfinitePlace F => Complex.I) = 1 := by simp [wt]
  have hnz : ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0}, ‖s x.1 ω‖ₑ ∂Pr ≠ ∞ := by
    rw [hwt, ENNReal.ofReal_one, one_mul] at hbound
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  have hfin : ∫⁻ ω, ∑' z, ‖s z ω‖ₑ ∂Pr ≠ ∞ := by
    have hle : ∀ ω, ∑' z, ‖s z ω‖ₑ ≤ 1 + ∑' x : {x : ι → F // x ≠ 0}, ‖s x.1 ω‖ₑ := by
      intro ω
      rw [ENNReal.tsum_eq_add_tsum_ite 0]
      refine add_le_add (thTerm_zero_le B ρ P (gf ω) (gi ω) a) (le_of_eq ?_)
      have := tsum_subtype {x : ι → F | x ≠ 0} (fun z => ‖s z ω‖ₑ)
      refine Eq.trans ?_ this.symm
      refine tsum_congr fun z => ?_
      by_cases h : z = 0 <;> simp [h]
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hle)
    rw [lintegral_add_left measurable_const]
    simp only [lintegral_const, measure_univ, mul_one]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, hnz⟩
  have hpos : ∀ z ω, s z ω = ((‖s z ω‖ : ℝ) : ℂ) := fun z ω => thTerm_nonneg B ρ P (gf ω) (gi ω) a z
  set Sel : Set (ι → F) := {z | qf (1 / 2 : F) B z = β} with hSel
  haveI : IsFiniteMeasure ((volume : Measure (InfinitePlace F → ℝ)).restrict D) :=
    ⟨by rw [Measure.restrict_apply_univ, hvol]; exact ENNReal.ofReal_lt_top⟩
  have hv : Continuous fun x : InfinitePlace F → ℝ =>
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) := by
    simp_rw [ph_neg]
    exact ph_continuous ρ _
  have hvn : ∀ x : InfinitePlace F → ℝ,
      ‖Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ))‖ = 1 := by
    intro x
    rw [ph_neg, ph_norm]
  have hres := fourier_series hm hfin (μ := (volume : Measure (InfinitePlace F → ℝ)).restrict D)
    (u := fun z => ph ρ (qf (1 / 2 : F) B z)) (fun z => ph_continuous ρ _) (fun z x => ph_norm ρ _ x)
    hv hvn Sel ((volume D).toReal : ℂ)
    (by
      intro z hz
      have hz' : qf (1 / 2 : F) B z = β := hz
      have : ∀ x : InfinitePlace F → ℝ, ph ρ (qf (1 / 2 : F) B z) x *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) = 1 := by
        intro x
        rw [ph_neg, ph_mul, hz', add_neg_cancel, ph_zero]
      simp_rw [this]
      simp [setIntegral_const, Measure.real])
    (by
      intro z hz
      by_cases hall : ∀ ω, s z ω = 0
      · exact Or.inr hall
      left
      push_neg at hall
      obtain ⟨ω, hω⟩ := hall
      obtain ⟨r, hr⟩ := integral_of_ne_zero (hOrth ω) hint hmem hω
      obtain ⟨r₀, hr₀⟩ := hNβ
      have hne : qf (1 / 2 : F) B z + -β ≠ 0 := fun h => hz (add_neg_eq_zero.mp h)
      have := horth _ hne ⟨r - r₀, by
        have hsub : ((r - r₀ : 𝓞 F) : F) = (r : F) - (r₀ : F) := map_sub (algebraMap (𝓞 F) F) r r₀
        rw [hsub, hr, hr₀]
        ring⟩
      have hx : ∀ x : InfinitePlace F → ℝ, ph ρ (qf (1 / 2 : F) B z) x *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) =
          ph ρ (qf (1 / 2 : F) B z + -β) x := by
        intro x
        rw [ph_neg, ph_mul]
      simp_rw [hx]
      exact this)
  have hth : ∀ (x : InfinitePlace F → ℝ) (ω : Ω),
      theta B ρ P (gf ω) (gi ω) (indL a) (fun w => (x w : ℂ) + Complex.I) =
        ∑' z, ph ρ (qf (1 / 2 : F) B z) x * s z ω := fun x ω =>
    tsum_congr fun z => thTerm_shift P (hOrth ω) _ x z
  have hI : ∫⁻ ω, ∑' x : {x : ι → F // qf (1 / 2 : F) B x = β}, ‖s x.1 ω‖ₑ ∂Pr ≠ ∞ :=
    ne_top_of_le_ne_top hfin (lintegral_mono fun ω =>
      ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective fun z => ‖s z ω‖ₑ)
  refine ⟨_, (ENNReal.coe_toNNReal hI).symm, ?_, ?_⟩
  · simp_rw [hth]
    exact hres.1
  · simp_rw [hth]
    rw [hres.2, sum_selected hm hfin hpos Sel]
    rfl

end Theta

section Eis

open GlobalTheory.CompanionTheory.SW.CoefEis

/- English proof (translation)
Introduce `F _ _ _ _ lf hlf h1 ψ hψ ι _ _ M B ρ P hQ hM φ hφ hΦ hc β N hN hNβ hper D hD`. Take `⟨hTR, -, -, -, hρ, -, -⟩` from `id hQ`. Establish `hcount : Countable F` using `(Module.finBasis ℚ F).equivFun.toEquiv.injective.countable`. Take `⟨-, hLcount, hLmem, hLD⟩` from `GlobalTheory.T.lattice_fundamental_domain_volume F hTR ρ hρ N hN`. Take `⟨hvol, -⟩` from `hLD D hD`.

Take `⟨-, -, -, -, hOopen, -, hOint, -, -, hWopen⟩` from `GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F`. Take `⟨-, hψ'⟩` from `GlobalTheory.T.standard_adelic_character F`. Take `⟨hψ1, hψO, -⟩` from `hψ' ψ hψ`. Take `⟨C, hC⟩` from `GlobalTheory.T.summable_norm_eiTerm_and_wt_mul_tsum_le F lf hlf h1 ψ hψ ι M B ρ P hQ hM φ hφ 1 one_pos`. Use `haveI := hLcount`.

Use `haveI : lf.IsAddHaarMeasure := hlf`. Use `set Φ := fstar ψ (hf F) (Bf B) (muF B lf) φ with hΦdef`. Use `set c : (InfinitePlace F → ℝ) → ℂ := fun x => cG B ρ P (fun w => (x w : ℂ) + Complex.I) with hcdef`. Use `set e : (InfinitePlace F → ℝ) → ℂ := fun x => Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) with hedef`. Set `j : F →+ (InfinitePlace F → ℝ)` to `{ toFun := fun b w => ρ w b map_zero' := by ext w; simp map_add' := fun a b => by ext w; simp }`.

Establish `hj : ∀ b w, j b w = ρ w b` using `fun _ _ => rfl`. Establish `hjinj : Function.Injective j`. Introduce `a b hab`. Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Conclude with `(ρ w).injective (congrFun hab w)`.

Use `set al : F →+* A F := algebraMap F (A F) with hal`. Establish `hecont : Continuous e`. Simplify using `only [hedef]`. Use `fun_prop`. Establish `henorm : ∀ x, ‖e x‖ = 1`.

Introduce `x`. Simplify using `only [hedef]`. Establish `: -(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ) = ((-(2 * Real.pi * ∑ w, ρ w β * x w) : ℝ) : ℂ) * Complex.I` using `by push_cast; ring`. Rewrite using `[this, Complex.norm_exp_ofReal_mul_I]`. Establish `headd : ∀ x y, e (x + y) = e x * e y`.

Introduce `x y`. Simplify using `only [hedef, ← Complex.exp_add]`. Use `congr 1`. Simplify using `only [Pi.add_apply, mul_add, Finset.sum_add_distrib]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hechar : ∀ b : F, e (-(j b)) = ψ (-(al β) * al b)`. Introduce `b`. Establish `h2 : -(al β) * al b = al (-(β * b))` using `by simp [hal]`. Rewrite using `[h2, hψ.2]`.

Simplify using `only [hedef]`. Use `congr 1`. Establish `h3 : (∑ w, ρ w β * (-(j b)) w) = -((Algebra.trace ℚ F (β * b) : ℚ) : ℝ)`. Rewrite using `[← sum_places_eq_trace F hTR ρ hρ (β * b), ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations.

Simplify using `[hj]`. Rewrite using `[h3, map_neg]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Set `H : AddSubgroup F` to `(latR ρ N).comap j`.

Establish `hHmem : ∀ b, b ∈ H ↔ ∃ r : 𝓞 F, b = (N : F) * (r : F)`. Introduce `b`. Rewrite using `[AddSubgroup.mem_comap, hLmem]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, hr⟩`.

Use `⟨r, hjinj ?_⟩` and prove the remaining obligations. Rewrite using `[hr]`. Both sides reduce to the same expression. Introduce and unpack `⟨r, rfl⟩`. Conclude with `⟨r, rfl⟩`.

Establish `hNal : ∀ n : ℕ, al (n : F) = (n : A F)` using `fun n => map_natCast _ n`. Establish `hOr : ∀ r : 𝓞 F, al (r : F) ∈ Oh F` using `fun r => (hOint _).2 ⟨r, rfl⟩`. Establish `heLat : ∀ l ∈ latR ρ N, e l = 1`. Introduce `l hl`. Take `⟨r, rfl⟩` from `(hLmem l).1 hl`.

Take `⟨r0, hr0⟩` from `hNβ`. Establish `h4 : (fun w => ρ w ((N : F) * (r : F))) = -(j (-((N : F) * (r : F))))`. Use extensionality with `w`. Simplify using `[hj]`. Rewrite using `[h4, hechar]`.

Establish `h5 : -(al β) * al (-((N : F) * (r : F))) = al ((r0 * r : 𝓞 F) : F)`. Rewrite using `[← map_neg, ← map_mul]`. Use `congr 1`. Rewrite using `[show ((r0 * r : 𝓞 F) : F) = (r0 : F) * (r : F) from map_mul (algebraMap (𝓞 F) F) r0 r, hr0]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h5]`. Conclude with `hψO _ (hOr _)`. Establish `hap : ∀ b, ∀ h ∈ H, Φ (al (b + h)) = Φ (al b)`. Introduce `b h hh`. Take `⟨r, rfl⟩` from `(hHmem h).1 hh`.

Establish `: al (b + (N : F) * (r : F)) = al b + (N : A F) * al (r : F)`. Rewrite using `[map_add, map_mul, hNal]`. Rewrite using `[this]`. Conclude with `hper _ (hOr r) _`. Establish `hterm : ∀ (x : InfinitePlace F → ℝ) (b : F), eiTerm ψ lf B ρ P φ (fun w => (x w : ℂ) + Complex.I) b = Φ (al b) * c (x + j b)`.

Introduce `x b`. Simplify using `only [eiTerm, hcdef]`. Use `congr 2`. Use function extensionality and compare the values at `w`. Simplify using `only [Pi.add_apply, hj]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hbd : ∀ x : InfinitePlace F → ℝ, Summable (fun b => ‖Φ (al b) * c (x + j b)‖) ∧ ∑' b, ‖Φ (al b) * c (x + j b)‖ ≤ C`. Introduce `x`. Establish `h6` using `hC (fun w => (x w : ℂ) + Complex.I) (fun w => by simp)`.

Simplify using `only [hterm] at h6`. Establish `h7 : wt M (fun w => (x w : ℂ) + Complex.I) = 1` using `by simp [wt]`. Rewrite `h6` using `[h7, one_mul]`. Conclude with `h6`. Establish `hDfin : volume D ≠ ⊤` using `by rw [hvol]; exact ENNReal.ofReal_ne_top`.

Use `haveI : IsFiniteMeasure (volume.restrict D) := ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hDfin⟩`. Use `set T : F → (InfinitePlace F → ℝ) → ℂ := fun b x => Φ (al b) * c (x + j b) * e x with hT`. Establish `hTnorm : ∀ b x, ‖T b x‖ = ‖Φ (al b) * c (x + j b)‖`. Introduce `b x`. Simplify using `only [hT, norm_mul, henorm, mul_one]`.

Establish `hTmeas : ∀ b, AEStronglyMeasurable (T b) (volume.restrict D)`. Introduce `b`. Establish `h8 : AEStronglyMeasurable (fun x => c (x + j b)) volume` using `(hc.comp_add_right (j b)).aestronglyMeasurable`. Conclude with `((h8.const_mul _).mul hecont.aestronglyMeasurable).restrict`. Take `⟨hInt, hSum, hEq⟩` from `tsum_integral_swap F (InfinitePlace F → ℝ) (volume.restrict D) T C hTmeas (fun x => by simpa only [hTnorm] using (hbd x).1) (fun x => by simpa only [hTnorm] using (hbd x).2)`.

Establish `heInt : Integrable e (volume.restrict D)` using `Integrable.of_bound hecont.aestronglyMeasurable 1 (ae_of_all _ fun x => (henorm x).le)`. Establish `Heisenberg₂ : ∀ x : InfinitePlace F → ℝ, eis ψ lf B ρ P φ (fun w => (x w : ℂ) + Complex.I) * e x = φ 0 * e x + ∑' b, T b x`. Introduce `x`. Simplify using `only [eis, add_mul, hT, hterm, tsum_mul_right]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Establish `: (fun x : InfinitePlace F → ℝ => eis ψ lf B ρ P φ (fun w => (x w : ℂ) + Complex.I) * e x) = fun x => φ 0 * e x + ∑' b, T b x` using `funext Heisenberg₂`. Rewrite using `[IntegrableOn, this]`. Conclude with `(heInt.const_mul _).add hInt`. Express the relevant statement in the definitionally equal form `∫ x in D, eis ψ lf B ρ P φ (fun w => (x w : ℂ) + Complex.I) * e x = φ 0 * (∫ x in D, e x) + ((N : ℂ) ^ Module.finrank ℚ F * ∫ y, Φ y * ψ (-(al β) * y) ∂lf) * ∫ x, c x * e x set Ch : ℂ := ∫ x, c x * e x with hCh`. Simplify using `only [Heisenberg₂]`.

Rewrite using `[integral_add (heInt.const_mul _) hInt, integral_const_mul, hEq, tsum_cosets F H _ hSum]`. Use `congr 1`. Set `eH : H ≃ latR ρ N` to `Equiv.ofBijective (fun h => ⟨j h, h.2⟩) (by`. Prove the components needed by the constructor for the conclusion. Introduce `a b hab`.

Conclude with `Subtype.ext (hjinj (congrArg Subtype.val hab))`. Introduce and unpack `⟨l, hl⟩`. Take `⟨r, rfl⟩` from `(hLmem l).1 hl`. Conclude with `⟨⟨(N : F) * (r : F), (hHmem _).2 ⟨r, rfl⟩⟩, rfl⟩)`. Establish `hcoset : ∀ q : F ⧸ H, ∑' h : H, ∫ x in D, T (q.out + (h : F)) x = Φ (al q.out) * e (-(j q.out)) * Ch`.

Introduce `q`. Establish `h10 : ∀ h : H, ∫ x in D, T (q.out + (h : F)) x = Φ (al q.out) * ∫ x in D, c (x + (j q.out + ((eH h : latR ρ N) : InfinitePlace F → ℝ))) * e x`. Introduce `h`. Rewrite using `[← integral_const_mul]`. Use `integral_congr_ae (ae_of_all _ fun x => ?_)` and prove the remaining obligations.

Simplify using `only [hT]`. Rewrite using `[hap _ _ h.2, map_add j, mul_assoc]`. Both sides reduce to the same expression. Simplify using `only [h10]`. Rewrite using `[tsum_mul_left, eH.tsum_eq (fun l : latR ρ N => ∫ x in D, c (x + (j q.out + (l : InfinitePlace F → ℝ))) * e x), unfold_char (InfinitePlace F) (latR ρ N) D hD c e hc hecont henorm headd heLat (j q.out)]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hcoset]`. Rewrite using `[tsum_mul_right]`. Use `congr 1`. Use `set W : Set (A F) := {x : A F | ∃ z ∈ Oh F, x = (N : A F) * z} with hW`.

Take `⟨hcov, hdis⟩` from `cosets_of_multiples F N hN H hHmem`. Use `set G : A F → ℂ := fun y => Φ y * ψ (-(al β) * y) with hG`. Establish `hGint : Integrable G lf`. Use `hΦ.mono ?_ (ae_of_all _ fun y => ?_)` and prove the remaining obligations. Use `hΦ.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable ?_)` and prove the remaining obligations.

Conclude with `hψ.1.comp (by fun_prop)`. Simplify using `only [hG, norm_mul, hψ1, mul_one, le_refl]`. Establish `hGper : ∀ y, ∀ w ∈ W, G (y + w) = G y`. Introduce and unpack `y w ⟨z, hz, rfl⟩`. Take `⟨r0, hr0⟩` from `hNβ`.

Establish `h11 : -(al β) * (y + (N : A F) * z) = -(al β) * y + al (-(r0 : F)) * z`. Rewrite using `[hr0, ← hNal]`. Simplify using `only [map_neg, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `h12 : al (-(r0 : F)) * z ∈ Oh F`.

Rewrite using `[show -(r0 : F) = ((-r0 : 𝓞 F) : F) from (map_neg (algebraMap (𝓞 F) F) r0).symm]`. Conclude with `Oh_mul_mem F _ _ (hOr _) hz`. Simplify using `only [hG]`. Rewrite using `[hper z hz y, h11, AddChar.map_add_eq_mul, hψO _ h12, mul_one]`. Use `haveI : Countable (F ⧸ H) := Function.Surjective.countable (f := fun b : F => (b : F ⧸ H)) (fun q => ⟨q.out, QuotientAddGroup.out_eq' q⟩)`.

Establish `hsum` using `hasSum_integral_cosets (A F) (F ⧸ H) lf (fun q => al q.out) W (hWopen N hN) hcov hdis G hGint hGper`. Establish `h13 : ∀ q : F ⧸ H, G (al q.out) = Φ (al q.out) * e (-(j q.out))`. Introduce `q`. Simplify using `only [hG, hechar]`. Establish `h14` using `hsum.tsum_eq`.

Simplify using `only [h13] at h14`. Rewrite `h14` using `[tsum_mul_left]`. Rewrite using `[← h14, ← mul_assoc]`. Establish `h15` using `mass_multiples F lf hlf h1 N hN`. Establish `h16 : (((N : ℂ) ^ Module.finrank ℚ F) * (((lf W).toReal : ℝ) : ℂ)) = 1`.

Rewrite using `[mul_comm]`. Conclude with `h15` after adjusting the coercions. Rewrite using `[h16, one_mul]`.
-/
theorem fourier_coeff_eis_any : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → 3 ≤ M → ∀ φ : (ι → A F) → ℂ, SB φ → Integrable (fstar ψ (hf F) (Bf B) (muF B lf) φ) lf → Integrable (fun x : InfinitePlace F → ℝ => cG B ρ P (fun w => (x w : ℂ) + Complex.I)) → ∀ β : F, ∀ N : ℕ, 0 < N → (∃ r : 𝓞 F, (r : F) = (N : F) * β) → (∀ x ∈ Oh F, ∀ y : A F, fstar ψ (hf F) (Bf B) (muF B lf) φ (y + (N : A F) * x) = fstar ψ (hf F) (Bf B) (muF B lf) φ y) → ∀ D : Set (InfinitePlace F → ℝ), IsAddFundamentalDomain (latR ρ N) D volume → IntegrableOn (fun x : InfinitePlace F → ℝ => eis ψ lf B ρ P φ (fun w => (x w : ℂ) + Complex.I) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ))) D volume ∧ ∫ x in D, eis ψ lf B ρ P φ (fun w => (x w : ℂ) + Complex.I) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) = φ 0 * (∫ x in D, Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ))) + ((N : ℂ) ^ Module.finrank ℚ F * ∫ y, fstar ψ (hf F) (Bf B) (muF B lf) φ y * ψ (-(algebraMap F (A F) β) * y) ∂lf) * ∫ x : InfinitePlace F → ℝ, cG B ρ P (fun w => (x w : ℂ) + Complex.I) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) := by
  intro F _ _ _ _ lf hlf h1 ψ hψ ι _ _ M B ρ P hQ hM φ hφ hΦ hc β N hN hNβ hper D hD
  obtain ⟨hTR, -, -, -, hρ, -, -⟩ := id hQ
  have hcount : Countable F := (Module.finBasis ℚ F).equivFun.toEquiv.injective.countable
  obtain ⟨-, hLcount, hLmem, hLD⟩ := GlobalTheory.T.lattice_fundamental_domain_volume F hTR ρ hρ N hN
  obtain ⟨hvol, -⟩ := hLD D hD
  obtain ⟨-, -, -, -, hOopen, -, hOint, -, -, hWopen⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  obtain ⟨-, hψ'⟩ := GlobalTheory.T.standard_adelic_character F
  obtain ⟨hψ1, hψO, -⟩ := hψ' ψ hψ
  obtain ⟨C, hC⟩ := GlobalTheory.T.summable_norm_eiTerm_and_wt_mul_tsum_le F lf hlf h1 ψ hψ ι M B ρ P hQ hM φ hφ 1 one_pos
  haveI := hLcount
  haveI : lf.IsAddHaarMeasure := hlf

  set Φ := fstar ψ (hf F) (Bf B) (muF B lf) φ with hΦdef
  set c : (InfinitePlace F → ℝ) → ℂ := fun x => cG B ρ P (fun w => (x w : ℂ) + Complex.I) with hcdef
  set e : (InfinitePlace F → ℝ) → ℂ := fun x =>
    Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) with hedef
  let j : F →+ (InfinitePlace F → ℝ) :=
    { toFun := fun b w => ρ w b
      map_zero' := by ext w; simp
      map_add' := fun a b => by ext w; simp }
  have hj : ∀ b w, j b w = ρ w b := fun _ _ => rfl
  have hjinj : Function.Injective j := by
    intro a b hab
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    exact (ρ w).injective (congrFun hab w)
  set al : F →+* A F := algebraMap F (A F) with hal

  have hecont : Continuous e := by
    simp only [hedef]
    fun_prop
  have henorm : ∀ x, ‖e x‖ = 1 := by
    intro x
    simp only [hedef]
    have : -(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)
        = ((-(2 * Real.pi * ∑ w, ρ w β * x w) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  have headd : ∀ x y, e (x + y) = e x * e y := by
    intro x y
    simp only [hedef, ← Complex.exp_add]
    congr 1
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    push_cast
    ring
  have hechar : ∀ b : F, e (-(j b)) = ψ (-(al β) * al b) := by
    intro b
    have h2 : -(al β) * al b = al (-(β * b)) := by simp [hal]
    rw [h2, hψ.2]
    simp only [hedef]
    congr 1
    have h3 : (∑ w, ρ w β * (-(j b)) w) = -((Algebra.trace ℚ F (β * b) : ℚ) : ℝ) := by
      rw [← sum_places_eq_trace F hTR ρ hρ (β * b), ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp [hj]
    rw [h3, map_neg]
    push_cast
    ring

  let H : AddSubgroup F := (latR ρ N).comap j
  have hHmem : ∀ b, b ∈ H ↔ ∃ r : 𝓞 F, b = (N : F) * (r : F) := by
    intro b
    rw [AddSubgroup.mem_comap, hLmem]
    constructor
    · rintro ⟨r, hr⟩
      refine ⟨r, hjinj ?_⟩
      rw [hr]
      rfl
    · rintro ⟨r, rfl⟩
      exact ⟨r, rfl⟩
  have hNal : ∀ n : ℕ, al (n : F) = (n : A F) := fun n => map_natCast _ n

  have hOr : ∀ r : 𝓞 F, al (r : F) ∈ Oh F := fun r => (hOint _).2 ⟨r, rfl⟩
  have heLat : ∀ l ∈ latR ρ N, e l = 1 := by
    intro l hl
    obtain ⟨r, rfl⟩ := (hLmem l).1 hl
    obtain ⟨r0, hr0⟩ := hNβ
    have h4 : (fun w => ρ w ((N : F) * (r : F))) = -(j (-((N : F) * (r : F)))) := by
      ext w
      simp [hj]
    rw [h4, hechar]
    have h5 : -(al β) * al (-((N : F) * (r : F))) = al ((r0 * r : 𝓞 F) : F) := by
      rw [← map_neg, ← map_mul]
      congr 1
      rw [show ((r0 * r : 𝓞 F) : F) = (r0 : F) * (r : F) from map_mul (algebraMap (𝓞 F) F) r0 r, hr0]
      ring
    rw [h5]
    exact hψO _ (hOr _)
  have hap : ∀ b, ∀ h ∈ H, Φ (al (b + h)) = Φ (al b) := by
    intro b h hh
    obtain ⟨r, rfl⟩ := (hHmem h).1 hh
    have : al (b + (N : F) * (r : F)) = al b + (N : A F) * al (r : F) := by
      rw [map_add, map_mul, hNal]
    rw [this]
    exact hper _ (hOr r) _
  have hterm : ∀ (x : InfinitePlace F → ℝ) (b : F),
      eiTerm ψ lf B ρ P φ (fun w => (x w : ℂ) + Complex.I) b = Φ (al b) * c (x + j b) := by
    intro x b
    simp only [eiTerm, hcdef]
    congr 2
    funext w
    simp only [Pi.add_apply, hj]
    push_cast
    ring
  have hbd : ∀ x : InfinitePlace F → ℝ, Summable (fun b => ‖Φ (al b) * c (x + j b)‖) ∧
      ∑' b, ‖Φ (al b) * c (x + j b)‖ ≤ C := by
    intro x
    have h6 := hC (fun w => (x w : ℂ) + Complex.I) (fun w => by simp)
    simp only [hterm] at h6
    have h7 : wt M (fun w => (x w : ℂ) + Complex.I) = 1 := by simp [wt]
    rw [h7, one_mul] at h6
    exact h6
  have hDfin : volume D ≠ ⊤ := by rw [hvol]; exact ENNReal.ofReal_ne_top
  haveI : IsFiniteMeasure (volume.restrict D) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hDfin⟩
  set T : F → (InfinitePlace F → ℝ) → ℂ := fun b x => Φ (al b) * c (x + j b) * e x with hT
  have hTnorm : ∀ b x, ‖T b x‖ = ‖Φ (al b) * c (x + j b)‖ := by
    intro b x
    simp only [hT, norm_mul, henorm, mul_one]
  have hTmeas : ∀ b, AEStronglyMeasurable (T b) (volume.restrict D) := by
    intro b
    have h8 : AEStronglyMeasurable (fun x => c (x + j b)) volume :=
      (hc.comp_add_right (j b)).aestronglyMeasurable
    exact ((h8.const_mul _).mul hecont.aestronglyMeasurable).restrict
  obtain ⟨hInt, hSum, hEq⟩ := tsum_integral_swap F (InfinitePlace F → ℝ) (volume.restrict D) T C hTmeas
    (fun x => by simpa only [hTnorm] using (hbd x).1)
    (fun x => by simpa only [hTnorm] using (hbd x).2)
  have heInt : Integrable e (volume.restrict D) :=
    Integrable.of_bound hecont.aestronglyMeasurable 1 (ae_of_all _ fun x => (henorm x).le)
  have Heisenberg₂ : ∀ x : InfinitePlace F → ℝ,
      eis ψ lf B ρ P φ (fun w => (x w : ℂ) + Complex.I) * e x = φ 0 * e x + ∑' b, T b x := by
    intro x
    simp only [eis, add_mul, hT, hterm, tsum_mul_right]
  refine ⟨?_, ?_⟩
  · have : (fun x : InfinitePlace F → ℝ => eis ψ lf B ρ P φ (fun w => (x w : ℂ) + Complex.I) * e x)
        = fun x => φ 0 * e x + ∑' b, T b x := funext Heisenberg₂
    rw [IntegrableOn, this]
    exact (heInt.const_mul _).add hInt
  · change ∫ x in D, eis ψ lf B ρ P φ (fun w => (x w : ℂ) + Complex.I) * e x =
      φ 0 * (∫ x in D, e x) + ((N : ℂ) ^ Module.finrank ℚ F * ∫ y, Φ y * ψ (-(al β) * y) ∂lf) * ∫ x, c x * e x
    set Ch : ℂ := ∫ x, c x * e x with hCh
    simp only [Heisenberg₂]
    rw [integral_add (heInt.const_mul _) hInt, integral_const_mul, hEq, tsum_cosets F H _ hSum]
    congr 1

    let eH : H ≃ latR ρ N := Equiv.ofBijective (fun h => ⟨j h, h.2⟩) (by
      constructor
      · intro a b hab
        exact Subtype.ext (hjinj (congrArg Subtype.val hab))
      · rintro ⟨l, hl⟩
        obtain ⟨r, rfl⟩ := (hLmem l).1 hl
        exact ⟨⟨(N : F) * (r : F), (hHmem _).2 ⟨r, rfl⟩⟩, rfl⟩)
    have hcoset : ∀ q : F ⧸ H, ∑' h : H, ∫ x in D, T (q.out + (h : F)) x =
        Φ (al q.out) * e (-(j q.out)) * Ch := by
      intro q
      have h10 : ∀ h : H, ∫ x in D, T (q.out + (h : F)) x =
          Φ (al q.out) * ∫ x in D, c (x + (j q.out + ((eH h : latR ρ N) : InfinitePlace F → ℝ))) * e x := by
        intro h
        rw [← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [hT]
        rw [hap _ _ h.2, map_add j, mul_assoc]
        rfl
      simp only [h10]
      rw [tsum_mul_left, eH.tsum_eq (fun l : latR ρ N =>
        ∫ x in D, c (x + (j q.out + (l : InfinitePlace F → ℝ))) * e x),
        unfold_char (InfinitePlace F) (latR ρ N) D hD c e hc hecont henorm headd heLat (j q.out)]
      ring
    simp only [hcoset]
    rw [tsum_mul_right]
    congr 1

    set W : Set (A F) := {x : A F | ∃ z ∈ Oh F, x = (N : A F) * z} with hW
    obtain ⟨hcov, hdis⟩ := cosets_of_multiples F N hN H hHmem
    set G : A F → ℂ := fun y => Φ y * ψ (-(al β) * y) with hG
    have hGint : Integrable G lf := by
      refine hΦ.mono ?_ (ae_of_all _ fun y => ?_)
      · refine hΦ.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable ?_)
        exact hψ.1.comp (by fun_prop)
      · simp only [hG, norm_mul, hψ1, mul_one, le_refl]
    have hGper : ∀ y, ∀ w ∈ W, G (y + w) = G y := by
      rintro y w ⟨z, hz, rfl⟩
      obtain ⟨r0, hr0⟩ := hNβ
      have h11 : -(al β) * (y + (N : A F) * z) = -(al β) * y + al (-(r0 : F)) * z := by
        rw [hr0, ← hNal]
        simp only [map_neg, map_mul]
        ring
      have h12 : al (-(r0 : F)) * z ∈ Oh F := by
        rw [show -(r0 : F) = ((-r0 : 𝓞 F) : F) from (map_neg (algebraMap (𝓞 F) F) r0).symm]
        exact Oh_mul_mem F _ _ (hOr _) hz
      simp only [hG]
      rw [hper z hz y, h11, AddChar.map_add_eq_mul, hψO _ h12, mul_one]
    haveI : Countable (F ⧸ H) := Function.Surjective.countable (f := fun b : F => (b : F ⧸ H))
      (fun q => ⟨q.out, QuotientAddGroup.out_eq' q⟩)
    have hsum := hasSum_integral_cosets (A F) (F ⧸ H) lf (fun q => al q.out) W (hWopen N hN) hcov hdis G hGint hGper
    have h13 : ∀ q : F ⧸ H, G (al q.out) = Φ (al q.out) * e (-(j q.out)) := by
      intro q
      simp only [hG, hechar]
    have h14 := hsum.tsum_eq
    simp only [h13] at h14
    rw [tsum_mul_left] at h14
    rw [← h14, ← mul_assoc]
    have h15 := mass_multiples F lf hlf h1 N hN
    have h16 : (((N : ℂ) ^ Module.finrank ℚ F) * (((lf W).toReal : ℝ) : ℂ)) = 1 := by
      rw [mul_comm]
      exact_mod_cast h15
    rw [h16, one_mul]

end Eis

/- English proof (translation)
Establish `a1` using `tsum_subtype {x | p x} f`. Establish `a2` using `tsum_subtype {x | x ≠ z ∧ p x} f`. Express the relevant statement in the definitionally equal form `∑' x : ({x | p x} : Set α), f x.1 = f z + ∑' x : ({x | x ≠ z ∧ p x} : Set α), f x.1`. Rewrite using `[a1, a2, ENNReal.tsum_eq_add_tsum_ite z, Set.indicator_of_mem (show z ∈ {x | p x} from hz)]`. Use `congr 1`.

Use `tsum_congr fun x => ?_` and prove the remaining obligations. Distinguish the cases in `h : x = z`. Simplify using `[h]`. Apply the tactic sequence `by_cases hp : p x <;> simp [h, hp, Set.indicator]`.
-/
lemma tsum_split {α : Type} (f : α → ℝ≥0∞) (p : α → Prop) (z : α) (hz : p z) :
    ∑' x : {x // p x}, f x.1 = f z + ∑' x : {x // x ≠ z ∧ p x}, f x.1 := by
  classical
  have a1 := tsum_subtype {x | p x} f
  have a2 := tsum_subtype {x | x ≠ z ∧ p x} f
  change ∑' x : ({x | p x} : Set α), f x.1 = f z + ∑' x : ({x | x ≠ z ∧ p x} : Set α), f x.1
  rw [a1, a2, ENNReal.tsum_eq_add_tsum_ite z, Set.indicator_of_mem (show z ∈ {x | p x} from hz)]
  congr 1
  refine tsum_congr fun x => ?_
  by_cases h : x = z
  · simp [h]
  · by_cases hp : p x <;> simp [h, hp, Set.indicator]

/- English proof (translation)
Establish `hz : (gf *ᵥ fun j => algebraMap F (A F) ((0 : ι → F) j)) = 0`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct]`. Establish `hg : gauss B ρ P (fun _ => Complex.I) (fun w => gi w *ᵥ fun j => ρ w ((0 : ι → F) j)) = 1`. Establish `: ∀ w, (gi w *ᵥ fun j => ρ w ((0 : ι → F) j)) = 0`.

Introduce `w`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct]`. Simplify using `only [gauss, this]`. Simplify using the standard rewrite rules.

Establish `hm : (0 : ι → A F) ∈ {x : ι → A F | ∀ i, (a : A F) * x i ∈ Oh F}` using `fun i v => by`. Simplify using `only [Pi.zero_apply, mul_zero]`. Conclude with `zero_mem _`. Unfold `thTerm`. Rewrite using `[hz, hg, mul_one]`.

Simplify using `only [indL, Set.indicator_of_mem hm]`.
-/
lemma thTerm_zero {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (gf : Matrix ι ι (A F)) (gi : InfinitePlace F → Matrix ι ι ℝ) (a : ℕ) :
    thTerm B ρ P gf gi (indL a) (fun _ => Complex.I) 0 = 1 := by
  have hz : (gf *ᵥ fun j => algebraMap F (A F) ((0 : ι → F) j)) = 0 := by
    funext i
    simp [Matrix.mulVec, dotProduct]
  have hg : gauss B ρ P (fun _ => Complex.I) (fun w => gi w *ᵥ fun j => ρ w ((0 : ι → F) j)) = 1 := by
    have : ∀ w, (gi w *ᵥ fun j => ρ w ((0 : ι → F) j)) = 0 := by
      intro w
      funext i
      simp [Matrix.mulVec, dotProduct]
    simp only [gauss, this]
    simp
  have hm : (0 : ι → A F) ∈ {x : ι → A F | ∀ i, (a : A F) * x i ∈ Oh F} := fun i v => by
    simp only [Pi.zero_apply, mul_zero]
    exact zero_mem _
  unfold thTerm
  rw [hz, hg, mul_one]
  simp only [indL, Set.indicator_of_mem hm]

/- English proof (translation)
Introduce `F _ _ hF ι _ _ M hc hM B hB hdet ρ hρ P hP hPP _ _ lf hlf h1 Ω _ Pr _ gi gf m1 m2 o1 o2 hcnt`. Establish `hQ : QSetup M B ρ P` using `⟨hF, hc, hB, hdet, hρ, hP, hPP⟩`. Establish `hC : CountData M B ρ Pr gf gi` using `⟨inferInstance, m1, m2, fun ω => ⟨o2 ω, o1 ω⟩, hcnt⟩`. Take `⟨ψ, hψ⟩` from `(GlobalTheory.T.standard_adelic_character F).1`. Take `⟨C, hb⟩` from `PositivityTheory.PlacePermOperatorBicommutantSpan.bounded_a F lf hlf h1 ψ hψ ι M B ρ P hQ hM Ω Pr gf gi hC`.

Use `choose! Df d1 d2 d3 d4 d5 using GlobalTheory.T.schur_function_whittaker_equivariant F lf hlf h1 ψ hψ ι M B ρ P hQ hM`. Take `⟨Di, i1, i2, i3, i4, i5⟩` from `GlobalTheory.T.quadratic_level_set_density F ι M B ρ P hQ hM`. Use `⟨C, Df, Di, fun a ha => ⟨d1 a ha, d2 a ha, d3 a ha⟩, ⟨i1, i2, i3⟩, fun a ha => ?_⟩` and prove the remaining obligations. Take `⟨-, -, -, -, -, -, hint, -, hK, -⟩` from `GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F`. Establish `hs` using `PositivityTheory.PlacePermOperatorBicommutantSpan.sb_indL (F := F) (ι := ι) ha`.

Take `⟨N₁, p1, n1⟩` from `GlobalTheory.T.weil_operator_integral_invariance F lf hlf h1 ψ hψ ι M B ρ P hQ _ hs`. Establish `hq : Continuous (qf (hf F) (Bf B) : (ι → A F) → A F)` using `by unfold qf; fun_prop`. Take `⟨N₂, p2, n2⟩` from `hK _ ((hs.2.isCompact.image hq).insert (algebraMap F (A F) 0))`. Establish `hN : 0 < N₁ * N₂` using `Nat.mul_pos p1 p2`. Establish `hβN : ∃ r : 𝓞 F, (r : F) = ((N₁ * N₂ : ℕ) : F) * 0` using `⟨0, by simp⟩`.

Take `⟨⟨D, hD⟩, -, -, hvol⟩` from `GlobalTheory.T.lattice_fundamental_domain_volume F hF ρ hρ _ hN`. Take `⟨I, e1, j1, e2⟩` from `fourier_coefficient_any F ι M B ρ P hQ Ω Pr gf gi hC a ha 0 _ hN hβN (fun y hy => by`. Rewrite using `[Nat.cast_mul, mul_assoc]`. Use `PositivityTheory.PlacePermOperatorBicommutantSpan.oh_mul (PositivityTheory.PlacePermOperatorBicommutantSpan.oh_nat N₁) (n2 _ (Set.mem_insert_of_mem _ ⟨y, subset_tsupport _ ?_, rfl⟩))` and prove the remaining obligations. Rewrite using `[Function.mem_support, indL, Set.indicator_of_mem (s := {x : ι → A F | ∀ i, (a : A F) * x i ∈ Oh F}) hy]`.

Conclude with `one_ne_zero) D hD`. Take `⟨j2, e3⟩` from `fourier_coeff_eis_any F lf hlf h1 ψ hψ ι M B ρ P hQ hM _ hs (d4 a ha) i4 0 _ hN hβN (fun x hx y => by`. Rewrite using `[Nat.cast_mul, mul_assoc]`. Conclude with `(n1 _ (PositivityTheory.PlacePermOperatorBicommutantSpan.oh_mul (PositivityTheory.PlacePermOperatorBicommutantSpan.oh_nat N₂) hx)).2 y) D hD`. Use `haveI : IsProbabilityMeasure Pr := hC.1`.

Establish `hsplit : ∀ ω, ∑' x : {x : ι → F // qf (1 / 2 : F) B x = 0}, ‖thTerm B ρ P (gf ω) (gi ω) (indL a) (fun _ => Complex.I) x.1‖ₑ = 1 + ∑' x : {x : ι → F // x ≠ 0 ∧ qf (1 / 2 : F) B x = 0}, ‖thTerm B ρ P (gf ω) (gi ω) (indL a) (fun _ => Complex.I) x.1‖ₑ` using `fun ω => by`. Rewrite using `[tsum_split (fun x => ‖thTerm B ρ P (gf ω) (gi ω) (indL a) (fun _ => Complex.I) x‖ₑ) (fun x => qf (1 / 2 : F) B x = 0) 0 (by simp [qf]), thTerm_zero]`. Simplify using the standard rewrite rules. Establish `e1' : 1 + ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0 ∧ qf (1 / 2 : F) B x = 0}, ‖thTerm B ρ P (gf ω) (gi ω) (indL a) (fun _ => Complex.I) x.1‖ₑ ∂Pr = (I : ℝ≥0∞)`. Rewrite using `[← e1]`.

Repeatedly rewrite using `[hsplit]`. Rewrite using `[lintegral_add_left measurable_const]`. Simplify using the standard rewrite rules. Establish `hJtop : ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0 ∧ qf (1 / 2 : F) B x = 0}, ‖thTerm B ρ P (gf ω) (gi ω) (indL a) (fun _ => Complex.I) x.1‖ₑ ∂Pr ≠ ∞`. Introduce `h`.

Rewrite `e1'` using `[h]`. Simplify using `at e1'`. Take `⟨J, hJ⟩ : ∃ J : ℝ≥0, ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0 ∧ qf (1 / 2 : F) B x = 0}, ‖thTerm B ρ P (gf ω) (gi ω) (indL a) (fun _ => Complex.I) x.1‖ₑ ∂Pr = (J : ℝ≥0∞)` from `⟨_, (ENNReal.coe_toNNReal hJtop).symm⟩`. Establish `hIJ : (I : ℝ) = 1 + (J : ℝ)`. Rewrite `e1'` using `[hJ]`.

Establish `: (1 + J : ℝ≥0) = I` using `by exact_mod_cast e1'`. Rewrite using `[← this]`. Use `push_cast`. Both sides reduce to the same expression. Use `⟨J, Eq.trans (lintegral_congr fun ω => tsum_congr fun x => ?_) hJ, ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hx : ∀ i, (a : A F) * (gf ω *ᵥ fun j => algebraMap F (A F) (x.1 j)) i ∈ Oh F`. Rewrite using `[Set.indicator_of_mem (by exact hx), thTerm, indL, Set.indicator_of_mem (s := {x : ι → A F | ∀ i, (a : A F) * x i ∈ Oh F}) hx, one_mul, ← ofReal_norm, gauss, Complex.norm_exp]`. Use `congr 2`. Simplify using `[Finset.mul_sum]`. Rewrite using `[Set.indicator_of_notMem (by exact hx), thTerm, indL, Set.indicator_of_notMem (s := {x : ι → A F | ∀ i, (a : A F) * x i ∈ Oh F}) hx, zero_mul, enorm_zero]`.

Establish `hk : 0 < kap F` using `inv_pos.2 (Real.sqrt_pos.2 (abs_pos.2 (by exact_mod_cast discr_ne_zero F)))`. Establish `hsq : 0 < Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)|` using `Real.sqrt_pos.2 (abs_pos.2 (by exact_mod_cast Algebra.norm_ne_zero_iff.2 hdet))`. Use `set v : ℝ := ((N₁ * N₂ : ℕ) : ℝ) ^ Module.finrank ℚ F * (kap F)⁻¹ with hv`. Establish `hv0 : 0 < v` using `by positivity`. Establish `hvD : volume.real D = v` using `by rw [Measure.real, (hvol D hD).1, ENNReal.toReal_ofReal hv0.le]`.

Establish `hph : ∀ x : InfinitePlace F → ℝ, Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w (0 : F) * x w : ℝ) : ℂ)) = 1` using `fun x => by simp`. Establish `hind : indL (F` using `F) (ι := ι) a 0 = 1 := by`. Establish `hm : (0 : ι → A F) ∈ {x : ι → A F | ∀ i, (a : A F) * x i ∈ Oh F}` using `fun i v => by`. Simplify using `only [Pi.zero_apply, mul_zero]`. Conclude with `zero_mem _`.

Simplify using `only [indL, Set.indicator_of_mem hm]`. Establish `h2` using `norm_setIntegral_le_of_norm_le_const (μ := volume) (s := D) (f := fun x : InfinitePlace F → ℝ => (∫ ω, theta B ρ P (gf ω) (gi ω) (indL a) (fun w => (x w : ℂ) + Complex.I) ∂Pr) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w (0 : F) * x w : ℝ) : ℂ)) - eis ψ lf B ρ P ( …`. Rewrite using `[hph, mul_one, mul_one]`. Conclude with `(hb a ha x).2`. Establish `hi0 : (fun w => ρ w (0 : F)) = fun _ => (0 : ℝ)`.

Use function extensionality and compare the values at `w`. Conclude with `map_zero _`. Establish `hz0 : algebraMap F (A F) 0 = 0` using `map_zero _`. Establish `hD1 : ∫ x in D, Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w (0 : F) * x w : ℝ) : ℂ)) = (v : ℂ)`. Repeatedly rewrite using `[hph]`.

Simplify using `[setIntegral_const, hvD]`. Rewrite `h2` using `[integral_sub j1 j2, e2, e3, hD1, hind, d5 a ha, i5, hvD, show (volume D).toReal = v from hvD, hi0, hz0]`. Establish `e4 : ((v : ℝ) : ℂ) * ((I : ℝ) : ℂ) - (1 * ((v : ℝ) : ℂ) + ((N₁ * N₂ : ℕ) : ℂ) ^ Module.finrank ℚ F * ((kap F ^ (2 * M - 2) * (Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)|)⁻¹ * Df a 0 : ℝ) : ℂ) * ((Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| * Di (fun _ => 0) : ℝ) : ℂ)) = ((v * ( …`. Rewrite using `[hIJ, ← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one, ← Complex.ofReal_mul, ← Complex.ofReal_add, ← Complex.ofReal_sub, show 2 * M - 1 = 2 * M - 2 + 1 by omega, pow_succ, hv]`. Use `congr 1`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite `h2` using `[e4, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hv0, mul_comm v]`. Conclude with `le_of_mul_le_mul_right h2 hv0`.
-/
theorem core_zero : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ), Fintype.card ι = 2 * M → 3 ≤ M → ∀ (B : Matrix ι ι F), B.IsSymm → B.det ≠ 0 → ∀ (ρ : InfinitePlace F → (F →+* ℝ)), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → ∀ (Pm : InfinitePlace F → Matrix ι ι ℝ), (∀ w, (Pm w).PosDef) → (∀ w, Pm w * (B.map (ρ w))⁻¹ * Pm w = B.map (ρ w)) → ∀ [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] (lf : Measure (FiniteAdeleRing (𝓞 F) F)), lf.IsAddHaarMeasure → lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 → ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (ginf : Ω → InfinitePlace F → Matrix ι ι ℝ) (gf : Ω → Matrix ι ι (FiniteAdeleRing (𝓞 F) F)), (∀ w i j, Measurable fun ω => ginf ω w i j) → (∀ i j, Measurable fun ω => gf ω i j) → (∀ ω w, (ginf ω w)ᵀ * B.map (ρ w) * ginf ω w = B.map (ρ w)) → (∀ ω, (gf ω)ᵀ * B.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) * gf ω = B.map (algebraMap F (FiniteAdeleRing (𝓞 F) F))) → (∀ N : ℕ, 0 < N → ∃ C : ℝ, ∀ R : ℝ, 0 < R → ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0}, Set.indicator {x : ι → F | (∀ i v, ((N : FiniteAdeleRing (𝓞 F) F) * (gf ω *ᵥ fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x j)) i) v ∈ v.adicCompletionIntegers F) ∧ ∀ w, ‖ginf ω w *ᵥ fun j => ρ w (x j)‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) x.1 ∂Pr ≤ ENNReal.ofReal (C * (R ^ (Module.finrank ℚ F * M) + R ^ (2 * Module.finrank ℚ F * M)))) → ∃ (C : ℝ) (Df : ℕ → FiniteAdeleRing (𝓞 F) F → ℝ) (Dinf : (InfinitePlace F → ℝ) → ℝ), (∀ a : ℕ, 0 < a → Continuous (Df a) ∧ (∀ y, 0 ≤ Df a y) ∧ ∀ U : Set (FiniteAdeleRing (𝓞 F) F), MeasurableSet U → (Measure.pi fun _ : ι => lf) {x | (∀ i v, ((a : FiniteAdeleRing (𝓞 F) F) * x i) v ∈ v.adicCompletionIntegers F) ∧ algebraMap F (FiniteAdeleRing (𝓞 F) F) (1 / 2) * (x ⬝ᵥ (B.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) *ᵥ x)) ∈ U} = ∫⁻ y in U, ENNReal.ofReal (Df a y) ∂lf) ∧ (Continuous Dinf ∧ (∀ y, 0 ≤ Dinf y) ∧ ∀ U : Set (InfinitePlace F → ℝ), MeasurableSet U → ∫⁻ x in {x : InfinitePlace F → ι → ℝ | (fun w => (1 / 2 : ℝ) * (x w ⬝ᵥ (B.map (ρ w) *ᵥ x w))) ∈ U}, ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (Pm w *ᵥ x w))) = ∫⁻ y in U, ENNReal.ofReal (Dinf y)) ∧ ∀ a : ℕ, 0 < a → ∃ I : ℝ≥0, ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0 ∧ (1 / 2 : F) * (x ⬝ᵥ (B *ᵥ x)) = 0}, Set.indicator {x : ι → F | ∀ i v, ((a : FiniteAdeleRing (𝓞 F) F) * (gf ω *ᵥ fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x j)) i) v ∈ v.adicCompletionIntegers F} (fun x => ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, (ginf ω w *ᵥ fun j => ρ w (x j)) ⬝ᵥ (Pm w *ᵥ (ginf ω w *ᵥ fun j => ρ w (x j)))))) x.1 ∂Pr = (I : ℝ≥0∞) ∧ |(I : ℝ) - (Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (2 * M - 1) * Df a 0 * Dinf (fun _ => 0)| ≤ C * (a : ℝ) ^ (Module.finrank ℚ F * M) := by
  intro F _ _ hF ι _ _ M hc hM B hB hdet ρ hρ P hP hPP _ _ lf hlf h1 Ω _ Pr _ gi gf m1 m2 o1 o2 hcnt
  have hQ : QSetup M B ρ P := ⟨hF, hc, hB, hdet, hρ, hP, hPP⟩
  have hC : CountData M B ρ Pr gf gi := ⟨inferInstance, m1, m2, fun ω => ⟨o2 ω, o1 ω⟩, hcnt⟩
  obtain ⟨ψ, hψ⟩ := (GlobalTheory.T.standard_adelic_character F).1
  obtain ⟨C, hb⟩ := PositivityTheory.PlacePermOperatorBicommutantSpan.bounded_a F lf hlf h1 ψ hψ ι M B ρ P hQ hM Ω Pr gf gi hC
  choose! Df d1 d2 d3 d4 d5 using GlobalTheory.T.schur_function_whittaker_equivariant F lf hlf h1 ψ hψ ι M B ρ P hQ hM
  obtain ⟨Di, i1, i2, i3, i4, i5⟩ := GlobalTheory.T.quadratic_level_set_density F ι M B ρ P hQ hM
  refine ⟨C, Df, Di, fun a ha => ⟨d1 a ha, d2 a ha, d3 a ha⟩, ⟨i1, i2, i3⟩, fun a ha => ?_⟩
  obtain ⟨-, -, -, -, -, -, hint, -, hK, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  have hs := PositivityTheory.PlacePermOperatorBicommutantSpan.sb_indL (F := F) (ι := ι) ha
  obtain ⟨N₁, p1, n1⟩ := GlobalTheory.T.weil_operator_integral_invariance F lf hlf h1 ψ hψ ι M B ρ P hQ _ hs
  have hq : Continuous (qf (hf F) (Bf B) : (ι → A F) → A F) := by unfold qf; fun_prop
  obtain ⟨N₂, p2, n2⟩ := hK _ ((hs.2.isCompact.image hq).insert (algebraMap F (A F) 0))
  have hN : 0 < N₁ * N₂ := Nat.mul_pos p1 p2
  have hβN : ∃ r : 𝓞 F, (r : F) = ((N₁ * N₂ : ℕ) : F) * 0 := ⟨0, by simp⟩
  obtain ⟨⟨D, hD⟩, -, -, hvol⟩ := GlobalTheory.T.lattice_fundamental_domain_volume F hF ρ hρ _ hN
  obtain ⟨I, e1, j1, e2⟩ := fourier_coefficient_any F ι M B ρ P hQ Ω Pr gf gi hC a ha 0 _ hN hβN (fun y hy => by
    rw [Nat.cast_mul, mul_assoc]
    refine PositivityTheory.PlacePermOperatorBicommutantSpan.oh_mul (PositivityTheory.PlacePermOperatorBicommutantSpan.oh_nat N₁) (n2 _ (Set.mem_insert_of_mem _ ⟨y, subset_tsupport _ ?_, rfl⟩))
    rw [Function.mem_support, indL, Set.indicator_of_mem (s := {x : ι → A F | ∀ i, (a : A F) * x i ∈ Oh F}) hy]
    exact one_ne_zero) D hD
  obtain ⟨j2, e3⟩ := fourier_coeff_eis_any F lf hlf h1 ψ hψ ι M B ρ P hQ hM _ hs (d4 a ha) i4 0 _ hN hβN
    (fun x hx y => by
      rw [Nat.cast_mul, mul_assoc]
      exact (n1 _ (PositivityTheory.PlacePermOperatorBicommutantSpan.oh_mul (PositivityTheory.PlacePermOperatorBicommutantSpan.oh_nat N₂) hx)).2 y) D hD
  haveI : IsProbabilityMeasure Pr := hC.1

  have hsplit : ∀ ω, ∑' x : {x : ι → F // qf (1 / 2 : F) B x = 0},
      ‖thTerm B ρ P (gf ω) (gi ω) (indL a) (fun _ => Complex.I) x.1‖ₑ =
      1 + ∑' x : {x : ι → F // x ≠ 0 ∧ qf (1 / 2 : F) B x = 0},
        ‖thTerm B ρ P (gf ω) (gi ω) (indL a) (fun _ => Complex.I) x.1‖ₑ := fun ω => by
    rw [tsum_split (fun x => ‖thTerm B ρ P (gf ω) (gi ω) (indL a) (fun _ => Complex.I) x‖ₑ)
      (fun x => qf (1 / 2 : F) B x = 0) 0 (by simp [qf]), thTerm_zero]
    simp
  have e1' : 1 + ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0 ∧ qf (1 / 2 : F) B x = 0},
      ‖thTerm B ρ P (gf ω) (gi ω) (indL a) (fun _ => Complex.I) x.1‖ₑ ∂Pr = (I : ℝ≥0∞) := by
    rw [← e1]
    simp_rw [hsplit]
    rw [lintegral_add_left measurable_const]
    simp
  have hJtop : ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0 ∧ qf (1 / 2 : F) B x = 0},
      ‖thTerm B ρ P (gf ω) (gi ω) (indL a) (fun _ => Complex.I) x.1‖ₑ ∂Pr ≠ ∞ := by
    intro h
    rw [h] at e1'
    simp at e1'
  obtain ⟨J, hJ⟩ : ∃ J : ℝ≥0, ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0 ∧ qf (1 / 2 : F) B x = 0},
      ‖thTerm B ρ P (gf ω) (gi ω) (indL a) (fun _ => Complex.I) x.1‖ₑ ∂Pr = (J : ℝ≥0∞) :=
    ⟨_, (ENNReal.coe_toNNReal hJtop).symm⟩
  have hIJ : (I : ℝ) = 1 + (J : ℝ) := by
    rw [hJ] at e1'
    have : (1 + J : ℝ≥0) = I := by exact_mod_cast e1'
    rw [← this]
    push_cast
    rfl
  refine ⟨J, Eq.trans (lintegral_congr fun ω => tsum_congr fun x => ?_) hJ, ?_⟩
  · by_cases hx : ∀ i, (a : A F) * (gf ω *ᵥ fun j => algebraMap F (A F) (x.1 j)) i ∈ Oh F
    · rw [Set.indicator_of_mem (by exact hx), thTerm, indL,
        Set.indicator_of_mem (s := {x : ι → A F | ∀ i, (a : A F) * x i ∈ Oh F}) hx, one_mul, ← ofReal_norm, gauss,
        Complex.norm_exp]
      congr 2
      simp [Finset.mul_sum]
    · rw [Set.indicator_of_notMem (by exact hx), thTerm, indL,
        Set.indicator_of_notMem (s := {x : ι → A F | ∀ i, (a : A F) * x i ∈ Oh F}) hx, zero_mul, enorm_zero]
  · have hk : 0 < kap F := inv_pos.2 (Real.sqrt_pos.2 (abs_pos.2 (by exact_mod_cast discr_ne_zero F)))
    have hsq : 0 < Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| :=
      Real.sqrt_pos.2 (abs_pos.2 (by exact_mod_cast Algebra.norm_ne_zero_iff.2 hdet))
    set v : ℝ := ((N₁ * N₂ : ℕ) : ℝ) ^ Module.finrank ℚ F * (kap F)⁻¹ with hv
    have hv0 : 0 < v := by positivity
    have hvD : volume.real D = v := by rw [Measure.real, (hvol D hD).1, ENNReal.toReal_ofReal hv0.le]
    have hph : ∀ x : InfinitePlace F → ℝ,
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w (0 : F) * x w : ℝ) : ℂ)) = 1 := fun x => by simp
    have hind : indL (F := F) (ι := ι) a 0 = 1 := by
      have hm : (0 : ι → A F) ∈ {x : ι → A F | ∀ i, (a : A F) * x i ∈ Oh F} := fun i v => by
        simp only [Pi.zero_apply, mul_zero]
        exact zero_mem _
      simp only [indL, Set.indicator_of_mem hm]
    have h2 := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := D)
      (f := fun x : InfinitePlace F → ℝ => (∫ ω, theta B ρ P (gf ω) (gi ω) (indL a) (fun w => (x w : ℂ) + Complex.I) ∂Pr) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w (0 : F) * x w : ℝ) : ℂ)) -
        eis ψ lf B ρ P (indL a) (fun w => (x w : ℂ) + Complex.I) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w (0 : F) * x w : ℝ) : ℂ)))
      (C := C * (a : ℝ) ^ (Module.finrank ℚ F * M)) (by rw [(hvol D hD).1]; exact ENNReal.ofReal_lt_top) fun x _ => by
        rw [hph, mul_one, mul_one]
        exact (hb a ha x).2
    have hi0 : (fun w => ρ w (0 : F)) = fun _ => (0 : ℝ) := by
      funext w
      exact map_zero _
    have hz0 : algebraMap F (A F) 0 = 0 := map_zero _
    have hD1 : ∫ x in D, Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w (0 : F) * x w : ℝ) : ℂ)) = (v : ℂ) := by
      simp_rw [hph]
      simp [setIntegral_const, hvD]
    rw [integral_sub j1 j2, e2, e3, hD1, hind, d5 a ha, i5, hvD, show (volume D).toReal = v from hvD, hi0, hz0] at h2
    have e4 : ((v : ℝ) : ℂ) * ((I : ℝ) : ℂ) - (1 * ((v : ℝ) : ℂ) + ((N₁ * N₂ : ℕ) : ℂ) ^ Module.finrank ℚ F *
        ((kap F ^ (2 * M - 2) * (Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)|)⁻¹ * Df a 0 : ℝ) : ℂ) *
        ((Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| * Di (fun _ => 0) : ℝ) : ℂ)) =
        ((v * ((J : ℝ) - kap F ^ (2 * M - 1) * Df a 0 * Di fun _ => 0) : ℝ) : ℂ) := by
      rw [hIJ, ← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
        ← Complex.ofReal_mul, ← Complex.ofReal_one, ← Complex.ofReal_mul, ← Complex.ofReal_add,
        ← Complex.ofReal_sub, show 2 * M - 1 = 2 * M - 2 + 1 by omega, pow_succ, hv]
      congr 1
      field_simp
      ring
    rw [e4, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hv0, mul_comm v] at h2
    exact le_of_mul_le_mul_right h2 hv0

end GlobalTheory.CompanionTheory.SW.Core0
