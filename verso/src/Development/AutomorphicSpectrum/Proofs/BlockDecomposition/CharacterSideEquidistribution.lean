import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThPr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurablePureAdelicFunctionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModuleRayEqPowDegreeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSeriesVanishesLargeModuleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSeriesUniformBoundCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanCutoffContinuousCompactSupportStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitePlaceCutoffContinuousCompactSupportStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PureFunctionEnlargeFiniteSetStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PureFunctionTranslateRayUnitsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PureFunctionThetaSeriesInvarianceStatement

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open GroundTheory.Global PositivityTheory.Rg.Base1
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.BasePsi

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Establish `h1 : ∀ᶠ v in cofinite, (a : AF F).2 v ∈ v.adicCompletionIntegers F` using `(a : AF F).2.2`. Establish `h2 : ∀ᶠ v in cofinite, ((a⁻¹ : (AF F)ˣ) : AF F).2 v ∈ v.adicCompletionIntegers F` using `((a⁻¹ : (AF F)ˣ) : AF F).2.2`. Establish `h3` using `h1.and h2`. Rewrite `h3` using `[eventually_cofinite]`. Use `⟨S ∪ h3.toFinset, Finset.subset_union_left, fun v hv => ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hc`. Conclude with `hv (Finset.mem_union_right _ (h3.mem_toFinset.2 hc))`.
-/
theorem exists_strictHenselian_absolutely_closed_local_ring (a : (AF F)ˣ) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), S ⊆ T ∧ ∀ v, v ∉ T → (a : AF F).2 v ∈ v.adicCompletionIntegers F ∧
      ((a⁻¹ : (AF F)ˣ) : AF F).2 v ∈ v.adicCompletionIntegers F := by
  have h1 : ∀ᶠ v in cofinite, (a : AF F).2 v ∈ v.adicCompletionIntegers F := (a : AF F).2.2
  have h2 : ∀ᶠ v in cofinite, ((a⁻¹ : (AF F)ˣ) : AF F).2 v ∈ v.adicCompletionIntegers F :=
    ((a⁻¹ : (AF F)ˣ) : AF F).2.2
  have h3 := h1.and h2
  rw [eventually_cofinite] at h3
  refine ⟨S ∪ h3.toFinset, Finset.subset_union_left, fun v hv => ?_⟩
  by_contra hc
  exact hv (Finset.mem_union_right _ (h3.mem_toFinset.2 hc))

/- English proof (translation)
Take `⟨T, hST, hT⟩` from `exists_strictHenselian_absolutely_closed_local_ring a S`. Establish `hφ` using `GlobalTheory.T.archimedean_cutoff_continuous_compact_support F G a hG hGc`. Establish `hψ` using `GlobalTheory.T.finite_place_cutoff_continuous_compact_support F S g a hgS`. Establish `h` using `hE F hF θ hθ li lam hli hlam Unit T (phiA G a) (fun v => psiA S g a v) hφ.1 hφ.2 (fun v _ => hψ v)`. Rewrite `h` using `[GlobalTheory.T.pure_function_enlarge_finite_set F li lam hli hlam S T G g a hST hT]`.

Simplify using `only [Fintype.card_unit, mul_one] at h`. Use `set d := Module.finrank ℚ F with hd`. Establish `hdpos : d ≠ 0` using `(Module.finrank_pos (R := ℚ) (M := F)).ne'`. Set `P : F → Prop` to `fun x => ∀ v, v ∉ T → algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F`. Set `q : ℝ → F → ℝ` to `fun δ x => phiA G a (fun _ => θ δ * algebraMap F (Ainf F) x) * ∏ v ∈ T, psiA S g a v (fun _ => algebraMap F (Fv F v) x)`.

Establish `hq0 : ∀ δ x, 0 ≤ q δ x` using `fun δ x => mul_nonneg (hG0 _) (Finset.prod_nonneg fun v _ => by`. Unfold `psiA`. Use `split_ifs`. Use `exacts [hg0 _ _, zero_le_one, le_rfl])`. Set `H : ℝ → F → ℝ` to `fun δ x => if P x then q δ x else 0`.

Establish `hH0 : ∀ δ x, 0 ≤ H δ x` using `fun δ x => by`. Simplify using `only [H]`. Use `split_ifs`. Use `exacts [hq0 δ x, le_rfl]`. Establish `hsum : ∀ δ : ℝ, (∑' x : {x : Unit → F // ∀ v, v ∉ T → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F}, phiA G a (fun i => θ δ * algebraMap F (Ainf F) (x.1 i)) * ∏ v ∈ T, psiA S g a v fun i => algebraMap F (Fv F v) (x.1 i)) = ∑' x : F, H δ x`.

Introduce `δ`. Set `e : {x : Unit → F // ∀ v, v ∉ T → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F} ≃ {x : F // P x}` to `(Equiv.funUnique Unit F).subtypeEquiv (fun x => by`. Simplify using `only [P, Equiv.funUnique_apply]`. Conclude with `⟨fun hx v hv => hx v hv _, fun hx v hv i => by`. Establish `: i = default` using `Subsingleton.elim _ _`.

Rewrite using `[this]`. Conclude with `hx v hv⟩)`. Establish `e1` using `e.tsum_eq (fun x : {x : F // P x} => q δ x.1)`. Establish `e2 : (∑' x : F, H δ x) = ∑' x : {x : F // P x}, q δ x.1`. Use `tsum_subtype {x : F | P x} (q δ)` as an intermediate fact.

Rewrite using `[show (∑' x : {x : F // P x}, q δ x.1) = ∑' x : ({x : F | P x} : Set F), q δ x.1 from rfl, this]`. Use `tsum_congr fun x => ?_` and prove the remaining obligations. Simplify using `only [H, Set.indicator, Set.mem_setOf_eq]`. Rewrite using `[e2, ← e1]`. Use `tsum_congr fun x => ?_` and prove the remaining obligations.

Simplify using `only [q]`. Establish `c1 : (fun i => θ δ * algebraMap F (Ainf F) (x.1 i)) = fun _ => θ δ * algebraMap F (Ainf F) ((e x).1)`. Use function extensionality and compare the values at `i`. Establish `: i = default` using `Subsingleton.elim _ _`. Rewrite using `[this]`.

Both sides reduce to the same expression. Establish `c2 : ∀ v, (fun i => algebraMap F (Fv F v) (x.1 i)) = fun _ => algebraMap F (Fv F v) ((e x).1)`. Introduce `v`. Use function extensionality and compare the values at `i`. Establish `: i = default` using `Subsingleton.elim _ _`.

Rewrite using `[this]`. Both sides reduce to the same expression. Rewrite using `[c1]`. Conclude with `congrArg _ (Finset.prod_congr rfl fun v _ => by rw [c2 v])`. Establish `hz : ∀ δ : ℝ, H δ 0 = H 1 0` using `fun δ => by`.

Simplify using `[H, q]`. Establish `hth : ∀ δ : ℝ, 0 < δ → ENNReal.ofReal (∑' x : F, H δ x) = ENNReal.ofReal (H 1 0) + th (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) (a * r δ)`. Introduce `δ hδ`. Establish `hfin : (Function.support (H δ)).Finite`. Use `(GlobalTheory.T.pure_function_theta_series_invariance F hF θ hθ S T G g a hG hGc hgS hST hT δ hδ).subset fun x hx => ?_` and prove the remaining obligations.

Simplify using `only [Function.mem_support, H] at hx`. Distinguish the cases in `hP : P x`. Rewrite `hx` using `[if_pos hP]`. Conclude with `⟨hP, hx⟩`. Rewrite `hx` using `[if_neg hP]`.

Conclude with `absurd rfl hx`. Rewrite using `[ENNReal.ofReal_tsum_of_nonneg (hH0 δ) (summable_of_finite_support hfin), ENNReal.tsum_eq_add_tsum_ite (0 : F), hz δ]`. Use `congr 1`. Unfold `th`. Establish `e1` using `(unitsEquivNeZero (G₀ := F)).tsum_eq (fun x : {x : F // x ≠ 0} => ENNReal.ofReal (H δ x.1))`.

Establish `e2` using `tsum_subtype {x : F | x ≠ 0} (fun x => ENNReal.ofReal (H δ x))`. Establish `e3 : (∑' x : F, if x = 0 then (0 : ℝ≥0∞) else ENNReal.ofReal (H δ x)) = ∑' x : {x : F // x ≠ 0}, ENNReal.ofReal (H δ x.1)`. Rewrite using `[show (∑' x : {x : F // x ≠ 0}, ENNReal.ofReal (H δ x.1)) = ∑' x : ({x : F | x ≠ 0} : Set F), ENNReal.ofReal (H δ x.1) from rfl, e2]`. Use `tsum_congr fun x => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases hx : x = 0 <;> simp [hx, Set.indicator]`.

Rewrite using `[e3, ← e1]`. Use `tsum_congr fun t => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.T.pure_function_translate_ray_units F θ r hr S T G g a hST hT δ hδ t]`. Simplify using `only [H, P, q, unitsEquivNeZero_apply_coe]`. Apply the tactic sequence `split_ifs <;> simp`.

Use `set z := ENNReal.ofReal (H 1 0) with hzdef`. Establish `hzt : z ≠ ⊤` using `ENNReal.ofReal_ne_top`. Establish `hpow : Tendsto (fun δ : ℝ => ENNReal.ofReal (δ ^ d)) (𝓝[>] 0) (𝓝 0)`. Establish `c : Continuous fun δ : ℝ => ENNReal.ofReal (δ ^ d)` using `ENNReal.continuous_ofReal.comp (continuous_pow d)`. Use `(c.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))` as an intermediate fact.

Simplify `this` using `[hdpos]`. Establish `h1` using `(ENNReal.tendsto_ofReal h)`. Establish `h2 : Tendsto (fun δ : ℝ => ENNReal.ofReal (δ ^ d) * z) (𝓝[>] 0) (𝓝 0)`. Simplify using `using ENNReal.Tendsto.mul_const hpow (Or.inr hzt)`. Establish `h3` using `ENNReal.Tendsto.sub h1 h2 (Or.inr ENNReal.zero_ne_top)`.

Rewrite `h3` using `[tsub_zero]`. Use `h3.congr' ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with δ hδ`. Establish `hδ' : (0 : ℝ) < δ` using `hδ`. Establish `hne : ENNReal.ofReal (δ ^ d) * z ≠ ⊤` using `ENNReal.mul_ne_top ENNReal.ofReal_ne_top hzt`.

Rewrite using `[hsum δ, ENNReal.ofReal_mul (by positivity), hth δ hδ', mul_add]`. Conclude with `ENNReal.add_sub_cancel_left hne`.
-/
theorem limit (hE : PositivityTheory.Rg.Mass.Equi) (hF : IsTotallyReal F) (θ : ℝ →+* Ainf F) (hθ : Continuous θ) (r : ℝ → (AF F)ˣ)
    (hr : IsRay θ r) (li : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)) (hli : IsStdInf li)
    (hlam : ∀ v, IsStdV v (lam v)) (S : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (hG : Continuous G) (hGc : HasCompactSupport G)
    (hG0 : ∀ y, 0 ≤ G y) (hg0 : ∀ v y, 0 ≤ g v y) (hgS : ∀ v ∈ S, Continuous (g v) ∧ HasCompactSupport (g v))
    (a : (AF F)ˣ) :
    Tendsto (fun δ : ℝ => ENNReal.ofReal (δ ^ Module.finrank ℚ F) * th (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) (a * r δ))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal ((md a)⁻¹ * ((∫ y, G y ∂li) * ∏ v ∈ S, ∫ s, g v s ∂(lam v))))) := by
  obtain ⟨T, hST, hT⟩ := exists_strictHenselian_absolutely_closed_local_ring a S
  have hφ := GlobalTheory.T.archimedean_cutoff_continuous_compact_support F G a hG hGc
  have hψ := GlobalTheory.T.finite_place_cutoff_continuous_compact_support F S g a hgS
  have h := hE F hF θ hθ li lam hli hlam Unit T (phiA G a) (fun v => psiA S g a v) hφ.1 hφ.2 (fun v _ => hψ v)
  rw [GlobalTheory.T.pure_function_enlarge_finite_set F li lam hli hlam S T G g a hST hT] at h
  simp only [Fintype.card_unit, mul_one] at h
  set d := Module.finrank ℚ F with hd
  have hdpos : d ≠ 0 := (Module.finrank_pos (R := ℚ) (M := F)).ne'

  let P : F → Prop := fun x => ∀ v, v ∉ T → algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F
  let q : ℝ → F → ℝ := fun δ x => phiA G a (fun _ => θ δ * algebraMap F (Ainf F) x) *
    ∏ v ∈ T, psiA S g a v (fun _ => algebraMap F (Fv F v) x)
  have hq0 : ∀ δ x, 0 ≤ q δ x := fun δ x => mul_nonneg (hG0 _) (Finset.prod_nonneg fun v _ => by
    unfold psiA
    split_ifs
    exacts [hg0 _ _, zero_le_one, le_rfl])
  let H : ℝ → F → ℝ := fun δ x => if P x then q δ x else 0
  have hH0 : ∀ δ x, 0 ≤ H δ x := fun δ x => by
    simp only [H]
    split_ifs
    exacts [hq0 δ x, le_rfl]
  have hsum : ∀ δ : ℝ, (∑' x : {x : Unit → F // ∀ v, v ∉ T → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F},
      phiA G a (fun i => θ δ * algebraMap F (Ainf F) (x.1 i)) * ∏ v ∈ T, psiA S g a v fun i => algebraMap F (Fv F v) (x.1 i)) =
      ∑' x : F, H δ x := by
    intro δ
    let e : {x : Unit → F // ∀ v, v ∉ T → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F} ≃ {x : F // P x} :=
      (Equiv.funUnique Unit F).subtypeEquiv (fun x => by
        simp only [P, Equiv.funUnique_apply]
        exact ⟨fun hx v hv => hx v hv _, fun hx v hv i => by
          have : i = default := Subsingleton.elim _ _
          rw [this]
          exact hx v hv⟩)
    have e1 := e.tsum_eq (fun x : {x : F // P x} => q δ x.1)
    have e2 : (∑' x : F, H δ x) = ∑' x : {x : F // P x}, q δ x.1 := by
      have := tsum_subtype {x : F | P x} (q δ)
      rw [show (∑' x : {x : F // P x}, q δ x.1) = ∑' x : ({x : F | P x} : Set F), q δ x.1 from rfl, this]
      refine tsum_congr fun x => ?_
      simp only [H, Set.indicator, Set.mem_setOf_eq]
    rw [e2, ← e1]
    refine tsum_congr fun x => ?_
    simp only [q]
    have c1 : (fun i => θ δ * algebraMap F (Ainf F) (x.1 i)) = fun _ => θ δ * algebraMap F (Ainf F) ((e x).1) := by
      funext i
      have : i = default := Subsingleton.elim _ _
      rw [this]
      rfl
    have c2 : ∀ v, (fun i => algebraMap F (Fv F v) (x.1 i)) = fun _ => algebraMap F (Fv F v) ((e x).1) := by
      intro v
      funext i
      have : i = default := Subsingleton.elim _ _
      rw [this]
      rfl
    rw [c1]
    exact congrArg _ (Finset.prod_congr rfl fun v _ => by rw [c2 v])
  have hz : ∀ δ : ℝ, H δ 0 = H 1 0 := fun δ => by
    simp [H, q]
  have hth : ∀ δ : ℝ, 0 < δ → ENNReal.ofReal (∑' x : F, H δ x) =
      ENNReal.ofReal (H 1 0) + th (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) (a * r δ) := by
    intro δ hδ
    have hfin : (Function.support (H δ)).Finite := by
      refine (GlobalTheory.T.pure_function_theta_series_invariance F hF θ hθ S T G g a hG hGc hgS hST hT δ hδ).subset fun x hx => ?_
      simp only [Function.mem_support, H] at hx
      by_cases hP : P x
      · rw [if_pos hP] at hx
        exact ⟨hP, hx⟩
      · rw [if_neg hP] at hx
        exact absurd rfl hx
    rw [ENNReal.ofReal_tsum_of_nonneg (hH0 δ) (summable_of_finite_support hfin),
      ENNReal.tsum_eq_add_tsum_ite (0 : F), hz δ]
    congr 1
    unfold th
    have e1 := (unitsEquivNeZero (G₀ := F)).tsum_eq (fun x : {x : F // x ≠ 0} => ENNReal.ofReal (H δ x.1))
    have e2 := tsum_subtype {x : F | x ≠ 0} (fun x => ENNReal.ofReal (H δ x))
    have e3 : (∑' x : F, if x = 0 then (0 : ℝ≥0∞) else ENNReal.ofReal (H δ x)) =
        ∑' x : {x : F // x ≠ 0}, ENNReal.ofReal (H δ x.1) := by
      rw [show (∑' x : {x : F // x ≠ 0}, ENNReal.ofReal (H δ x.1)) =
        ∑' x : ({x : F | x ≠ 0} : Set F), ENNReal.ofReal (H δ x.1) from rfl, e2]
      refine tsum_congr fun x => ?_
      by_cases hx : x = 0 <;> simp [hx, Set.indicator]
    rw [e3, ← e1]
    refine tsum_congr fun t => ?_
    rw [GlobalTheory.T.pure_function_translate_ray_units F θ r hr S T G g a hST hT δ hδ t]
    simp only [H, P, q, unitsEquivNeZero_apply_coe]
    split_ifs <;> simp
  set z := ENNReal.ofReal (H 1 0) with hzdef
  have hzt : z ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpow : Tendsto (fun δ : ℝ => ENNReal.ofReal (δ ^ d)) (𝓝[>] 0) (𝓝 0) := by
    have c : Continuous fun δ : ℝ => ENNReal.ofReal (δ ^ d) := ENNReal.continuous_ofReal.comp (continuous_pow d)
    have := (c.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa [hdpos] using this
  have h1 := (ENNReal.tendsto_ofReal h)
  have h2 : Tendsto (fun δ : ℝ => ENNReal.ofReal (δ ^ d) * z) (𝓝[>] 0) (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const hpow (Or.inr hzt)
  have h3 := ENNReal.Tendsto.sub h1 h2 (Or.inr ENNReal.zero_ne_top)
  rw [tsub_zero] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ' : (0 : ℝ) < δ := hδ
  have hne : ENNReal.ofReal (δ ^ d) * z ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hzt
  rw [hsum δ, ENNReal.ofReal_mul (by positivity), hth δ hδ', mul_add]
  exact ENNReal.add_sub_cancel_left hne

/- English proof (translation)
Introduce `hE F _ _ hF θ hθ r hr li lam hli hlam S G g hG hGc hG0 hg0 hgS`. Use `⟨GlobalTheory.T.measurable_pure_adelic_function F S G g hG fun v hv => (hgS v hv).1, ?_⟩` and prove the remaining obligations. Take `⟨D, hD, hD1, hDk⟩` from `IdeleGroup.exists_isCompact_normOneSubgroup F`. Take `⟨C, hC⟩` from `GlobalTheory.T.theta_series_uniform_bound_compact F hF θ hθ r hr S G g hG hGc hgS D hD`. Use `set d := Module.finrank ℚ F with hd`.

Establish `hdpos : d ≠ 0` using `(Module.finrank_pos (R := ℚ) (M := F)).ne'`. Establish `hmd : ∀ (a : (AF F)ˣ) (δ : ℝ), 0 < δ → ENNReal.ofReal (md (a * r δ)) = ENNReal.ofReal (md a) * ENNReal.ofReal (δ ^ d)`. Introduce `a δ hδ`. Rewrite using `[md_mul, GlobalTheory.T.module_ray_eq_pow_degree F hF θ r hr δ hδ, ENNReal.ofReal_mul (md_pos a).le]`. Use `⟨⟨C, fun a => ?_⟩, GlobalTheory.T.theta_series_vanishes_large_module F S G g hGc fun v hv => (hgS v hv).2, fun a ha => absurd (Subgroup.mem_top a) ha, fun a _ => ?_⟩` and prove the remaining obligations.

Use `set δ : ℝ := md a ^ ((d : ℝ)⁻¹) with hδdef`. Establish `hδ : 0 < δ` using `Real.rpow_pos_of_pos (md_pos a) _`. Establish `hδd : δ ^ d = md a` using `Real.rpow_inv_natCast_pow (md_pos a).le hdpos`. Use `set x : (AF F)ˣ := a * (r δ)⁻¹ with hx`. Establish `hxr : x * r δ = a` using `by simp [hx]`.

Establish `hx1 : md x = 1`. Establish `h1` using `md_mul x (r δ)`. Rewrite `h1` using `[hxr, GlobalTheory.T.module_ray_eq_pow_degree F hF θ r hr δ hδ, hδd]`. Use `md_pos a` as an intermediate fact. Clear denominators, using `at h1` for the nonvanishing conditions.

Use polynomial arithmetic with `[h1]`. Establish `hxn : x ∈ IdeleGroup.normOneSubgroup F`. Rewrite using `[IdeleGroup.normOneSubgroup, MonoidHom.mem_ker]`. Conclude with `Subtype.ext hx1`. Take `⟨k, hk⟩` from `hDk x hxn`.

Establish `hk' : pr k * x ∈ D` using `hk`. Establish `e : th (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) a = th (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) ((pr k * x) * r δ)`. Rewrite using `[mul_assoc, hxr, th_pr]`. Rewrite using `[e, ← hδd]`. Conclude with `hC _ hk' δ hδ`.

Establish `hl` using `limit hE hF θ hθ r hr li lam hli hlam S G g hG hGc hG0 hg0 hgS a`. Establish `hm` using `ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (md a)) hl (Or.inr ENNReal.ofReal_ne_top)`. Rewrite `hm` using `[← ENNReal.ofReal_mul (md_pos a).le, ← mul_assoc, mul_inv_cancel₀ (md_pos a).ne', one_mul]`. Use `hm.congr' ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with δ hδ`.

Rewrite using `[hmd a δ hδ, mul_assoc]`.
-/
theorem psiSide_of_equi : PositivityTheory.Rg.Mass.Equi → PsiSide := by
  intro hE F _ _ hF θ hθ r hr li lam hli hlam S G g hG hGc hG0 hg0 hgS
  refine ⟨GlobalTheory.T.measurable_pure_adelic_function F S G g hG fun v hv => (hgS v hv).1, ?_⟩
  obtain ⟨D, hD, hD1, hDk⟩ := IdeleGroup.exists_isCompact_normOneSubgroup F
  obtain ⟨C, hC⟩ := GlobalTheory.T.theta_series_uniform_bound_compact F hF θ hθ r hr S G g hG hGc hgS D hD
  set d := Module.finrank ℚ F with hd
  have hdpos : d ≠ 0 := (Module.finrank_pos (R := ℚ) (M := F)).ne'
  have hmd : ∀ (a : (AF F)ˣ) (δ : ℝ), 0 < δ → ENNReal.ofReal (md (a * r δ)) = ENNReal.ofReal (md a) * ENNReal.ofReal (δ ^ d) := by
    intro a δ hδ
    rw [md_mul, GlobalTheory.T.module_ray_eq_pow_degree F hF θ r hr δ hδ, ENNReal.ofReal_mul (md_pos a).le]
  refine ⟨⟨C, fun a => ?_⟩, GlobalTheory.T.theta_series_vanishes_large_module F S G g hGc fun v hv => (hgS v hv).2, fun a ha => absurd (Subgroup.mem_top a) ha, fun a _ => ?_⟩
  · set δ : ℝ := md a ^ ((d : ℝ)⁻¹) with hδdef
    have hδ : 0 < δ := Real.rpow_pos_of_pos (md_pos a) _
    have hδd : δ ^ d = md a := Real.rpow_inv_natCast_pow (md_pos a).le hdpos
    set x : (AF F)ˣ := a * (r δ)⁻¹ with hx
    have hxr : x * r δ = a := by simp [hx]
    have hx1 : md x = 1 := by
      have h1 := md_mul x (r δ)
      rw [hxr, GlobalTheory.T.module_ray_eq_pow_degree F hF θ r hr δ hδ, hδd] at h1
      have := md_pos a
      field_simp at h1
      nlinarith [h1]
    have hxn : x ∈ IdeleGroup.normOneSubgroup F := by
      rw [IdeleGroup.normOneSubgroup, MonoidHom.mem_ker]
      exact Subtype.ext hx1
    obtain ⟨k, hk⟩ := hDk x hxn
    have hk' : pr k * x ∈ D := hk
    have e : th (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) a =
        th (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) ((pr k * x) * r δ) := by
      rw [mul_assoc, hxr, th_pr]
    rw [e, ← hδd]
    exact hC _ hk' δ hδ
  · have hl := limit hE hF θ hθ r hr li lam hli hlam S G g hG hGc hG0 hg0 hgS a
    have hm := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (md a)) hl (Or.inr ENNReal.ofReal_ne_top)
    rw [← ENNReal.ofReal_mul (md_pos a).le, ← mul_assoc, mul_inv_cancel₀ (md_pos a).ne', one_mul] at hm
    refine hm.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    rw [hmd a δ hδ, mul_assoc]

end GlobalTheory.CompanionTheory.BasePsi

end
