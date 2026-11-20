import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.TaylorExpansionLocalCoordinates
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open Filter Asymptotics

namespace GlobalTheory.LeadJets

noncomputable section

/- English proof (translation)
Simplify using `[multiLt, Finset.Nat.mem_antidiagonalTuple]`.
-/
theorem mem_multiLt {n a : ℕ} {α : Fin n → ℕ} : α ∈ multiLt n a ↔ ∑ k, α k < a := by
  simp [multiLt, Finset.Nat.mem_antidiagonalTuple]

def leadVal {n δ : ℕ} (s : Fin n → ℂ) (w : ℂ) (t : Fin δ → ℂ) (T a0 : ℕ)
    (cc : (Fin n → ℕ) → Fin δ → ℂ) : ℂ :=
  ∑ α ∈ multiLt n a0, ∑ k, cc α k * (∏ q, s q ^ α q) * w ^ (T - ∑ q, α q) * t k

/- English proof (translation)
Establish `hfil : (multiLt n a0).filter (fun α => ∑ q, α q = a) = Finset.Nat.antidiagonalTuple n a`. Use extensionality with `α`. Simplify using `only [Finset.mem_filter, mem_multiLt, Finset.Nat.mem_antidiagonalTuple]`. Use linear arithmetic over natural numbers and integers. Unfold `leadVal`.

Simplify using `only [add_mul, Finset.sum_add_distrib]`. Use `congr 1`. Rewrite using `[← hfil, Finset.sum_filter]`. Use `Finset.sum_congr rfl fun α hα => ?_` and prove the remaining obligations. Establish `hlt` using `mem_multiLt.1 hα`.

Distinguish the cases in `h : ∑ q, α q = a`. Simplify using `only [if_pos h]`. Establish `hm : (∏ q, s q ^ α q) = (∏ k, (s k / w) ^ α k) * w ^ (∑ q, α q)`. Rewrite using `[← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun k _ => by rw [← mul_pow, div_mul_cancel₀ _ hw]`.

Establish `hT : w ^ (∑ q, α q) * w ^ (T - ∑ q, α q) = w ^ T`. Rewrite using `[← pow_add]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Finset.mul_sum, Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hm]`. Take the linear combination `(dd α k * (∏ q, (s q / w) ^ α q) * t k) * hT`. Simplify using `[h]`.
-/
theorem leadVal_add {n δ : ℕ} (s : Fin n → ℂ) (w : ℂ) (t : Fin δ → ℂ) {T a0 a : ℕ}
    (ha : a < a0) (ha0 : a0 ≤ T + 1) (cc dd : (Fin n → ℕ) → Fin δ → ℂ) (hw : w ≠ 0) :
    leadVal s w t T a0 (fun α k => cc α k + if ∑ q, α q = a then dd α k else 0) =
      leadVal s w t T a0 cc + ∑ α ∈ Finset.Nat.antidiagonalTuple n a,
        (w ^ T * ∑ k, dd α k * t k) * ∏ k, (s k / w) ^ α k := by
  classical
  have hfil : (multiLt n a0).filter (fun α => ∑ q, α q = a) =
      Finset.Nat.antidiagonalTuple n a := by
    ext α
    simp only [Finset.mem_filter, mem_multiLt, Finset.Nat.mem_antidiagonalTuple]
    omega
  unfold leadVal
  simp only [add_mul, Finset.sum_add_distrib]
  congr 1
  rw [← hfil, Finset.sum_filter]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hlt := mem_multiLt.1 hα
  by_cases h : ∑ q, α q = a
  · simp only [if_pos h]
    have hm : (∏ q, s q ^ α q) = (∏ k, (s k / w) ^ α k) * w ^ (∑ q, α q) := by
      rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => by rw [← mul_pow, div_mul_cancel₀ _ hw]
    have hT : w ^ (∑ q, α q) * w ^ (T - ∑ q, α q) = w ^ T := by
      rw [← pow_add]; congr 1; omega
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hm]
    linear_combination (dd α k * (∏ q, (s q / w) ^ α q) * t k) * hT
  · simp [h]

/- English proof (translation)
Unfold `leadVal`. Use `DifferentiableOn.fun_sum fun α _ => DifferentiableOn.fun_sum fun k _ => ?_` and prove the remaining obligations. Use `(((differentiableOn_const _).mul ?_).mul (hw.pow _)).mul (ht k)` and prove the remaining obligations. Use `Finset.induction_on (motive := fun F : Finset (Fin n) => DifferentiableOn ℂ (fun z => ∏ q ∈ F, s z q ^ α q) U) Finset.univ ?_ fun q F hq ih => ?_` and prove the remaining obligations. Simplify using `using differentiableOn_const (1 : ℂ)`.

Simplify using `only [Finset.prod_insert hq]`. Conclude with `((hs q).fun_pow _).mul ih`.
-/
theorem leadVal_diffOn {n δ : ℕ} {U : Set (V n)} {s : V n → Fin n → ℂ} {w : V n → ℂ}
    {t : V n → Fin δ → ℂ} (hs : ∀ k, DifferentiableOn ℂ (fun z => s z k) U)
    (hw : DifferentiableOn ℂ w U) (ht : ∀ k, DifferentiableOn ℂ (fun z => t z k) U)
    (T a0 : ℕ) (cc : (Fin n → ℕ) → Fin δ → ℂ) :
    DifferentiableOn ℂ (fun z => leadVal (s z) (w z) (t z) T a0 cc) U := by
  unfold leadVal
  refine DifferentiableOn.fun_sum fun α _ => DifferentiableOn.fun_sum fun k _ => ?_
  refine (((differentiableOn_const _).mul ?_).mul (hw.pow _)).mul (ht k)
  refine Finset.induction_on (motive := fun F : Finset (Fin n) =>
    DifferentiableOn ℂ (fun z => ∏ q ∈ F, s z q ^ α q) U) Finset.univ ?_ fun q F hq ih => ?_
  · simpa using differentiableOn_const (1 : ℂ)
  · simp only [Finset.prod_insert hq]
    exact ((hs q).fun_pow _).mul ih

section Step

variable {n δ m : ℕ} {U : Fin m → Set (V n)} {f w : Fin m → V n → ℂ}
  {s : Fin m → V n → Fin n → ℂ} {t : Fin m → V n → Fin δ → ℂ}

/- English proof (translation)
Use `set ζ : Fin m → V n → V n := fun j z => (WithLp.toLp 2 fun k => s j z k / w j z : V n) with hζdef`. Establish `loc : ∀ j, ∃ U' : Set (V n), IsOpen U' ∧ (0 : V n) ∈ U' ∧ U' ⊆ U j ∧ (∀ v ∈ U', w j v ≠ 0) ∧ DifferentiableOn ℂ (ζ j) U' ∧ ζ j 0 = 0`. Introduce `j`. Use `⟨U j ∩ w j ⁻¹' {0}ᶜ, (hw j).continuousOn.isOpen_inter_preimage (hU j) isOpen_compl_singleton, ⟨h0 j, hw0 j⟩, Set.inter_subset_left, fun v hv => hv.2, ?_, ?_⟩` and prove the remaining obligations. Use `differentiableOn_euclidean.2 fun k => ?_` and prove the remaining obligations.

Establish `hdiv : DifferentiableOn ℂ (fun v => s j v k * (w j v)⁻¹) (U j ∩ w j ⁻¹' {0}ᶜ)` using `((hs j k).mono Set.inter_subset_left).mul (((hw j).mono Set.inter_subset_left).inv fun v hv => hv.2)`. Conclude with `hdiv.congr fun v _ => by simp [hζdef, div_eq_mul_inv]`. Use extensionality with `k`. Simplify using `[hζdef, hs0]`. Establish `hb : ∀ j, ∃ b : (Fin n → ℕ) → ℂ, (fun v => (f j v - leadVal (s j v) (w j v) (t j v) T a0 cc) - ∑ α ∈ Finset.Nat.antidiagonalTuple n a, b α * ∏ k, ζ j v k ^ α k) =O[𝓝 0] fun v => ‖v‖ ^ (a + 1)`.

Introduce `j`. Take `⟨U', hUo, hxU, hUt, -, hζ, hζ0⟩` from `loc j`. Take `⟨b, hb⟩` from `taylor_expansion_local_coordinates (a := a) (fun v => f j v - leadVal (s j v) (w j v) (t j v) T a0 cc) (ζ j) U' 0 hUo hxU (((hf j).sub (leadVal_diffOn (hs j) (hw j) (ht j) T a0 cc)).mono hUt) hζ hζ0 (hcoord j) (by simpa only [sub_zero] using hcc j)`. Conclude with `⟨b, by simpa only [sub_zero] using hb⟩`. Use `choose bb hbb using hb`.

Use `choose dd hdd using fun α => hsurj (fun j => bb j α / w j 0 ^ T)`. Use `⟨fun α k => cc α k + if ∑ q, α q = a then dd α k else 0, fun j => ?_⟩` and prove the remaining obligations. Take `⟨U', hUo, hxU, hUt, hUw, hζ, hζ0⟩` from `loc j`. Establish `hxt : U j ∈ 𝓝 (0 : V n)` using `(hU j).mem_nhds (h0 j)`. Establish `hζO : (fun v => ζ j v) =O[𝓝 0] fun v => v`.

Use `(hζ.differentiableAt (hUo.mem_nhds hxU)).hasFDerivAt.isBigO_sub` as an intermediate fact. Simplify `this` using `only [hζ0, sub_zero]`. Establish `hQ : ∀ α ∈ Finset.Nat.antidiagonalTuple n a, (fun v => ∏ k, ζ j v k ^ α k) =O[𝓝 0] fun v => ‖v‖ ^ a`. Introduce `α hα`. Establish `hsum` using `Finset.Nat.mem_antidiagonalTuple.1 hα`.

Use `(IsBigO.of_bound 1 (Eventually.of_forall fun v => ?_)).trans (hζO.norm_norm.pow a)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.prod_pow_eq_pow_sum, hsum, one_mul, norm_pow, norm_norm]`. Establish `hφ : ∀ α, (fun v => bb j α - w j v ^ T * ∑ k, dd α k * t j v k) =O[𝓝 0] fun v => ‖v‖ ^ 1`. Introduce `α`.

Establish `hd : DifferentiableAt ℂ (fun v => bb j α - w j v ^ T * ∑ k, dd α k * t j v k) 0`. Use `(differentiableAt_const _).sub ((((hw j).differentiableAt hxt).pow T).mul ?_)` and prove the remaining obligations. Conclude with `DifferentiableAt.fun_sum fun k _ => ((ht j k).differentiableAt hxt).const_mul _`. Establish `h00 : bb j α - w j 0 ^ T * ∑ k, dd α k * t j 0 k = 0`. Rewrite using `[hdd α j, mul_div_cancel₀ _ (pow_ne_zero _ (hw0 j)), sub_self]`.

Use `hd.hasFDerivAt.isBigO_sub` as an intermediate fact. Rewrite `this` using `[h00]`. Simplify using `only [sub_zero] at this`. Conclude with `(this.trans (isBigO_refl _ _).norm_right).congr_right fun v => (pow_one _).symm`. Establish `h2 : (fun v => ∑ α ∈ Finset.Nat.antidiagonalTuple n a, (bb j α - w j v ^ T * ∑ k, dd α k * t j v k) * ∏ k, ζ j v k ^ α k) =O[𝓝 0] fun v => ‖v‖ ^ (a + 1)`.

Establish `hterm : ∀ α ∈ Finset.Nat.antidiagonalTuple n a, (fun v => (bb j α - w j v ^ T * ∑ k, dd α k * t j v k) * ∏ k, ζ j v k ^ α k) =O[𝓝 0] fun v => ‖v‖ ^ (a + 1)` using `fun α hα => ((hφ α).mul (hQ α hα)).congr_right fun v => by ring`. Conclude with `(IsBigO.sum hterm).congr_left fun v => Finset.sum_apply _ _ _`. Use `((hbb j).add h2).congr' ?_ EventuallyEq.rfl` and prove the remaining obligations. Use `filter_upwards [hUo.mem_nhds hxU] with v hv`. Use `beta_reduce`.

Rewrite using `[leadVal_add _ _ _ ha ha0 cc dd (hUw v hv)]`. Simplify using `only [hζdef, PiLp.toLp_apply, sub_mul, Finset.sum_sub_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem step {T a0 a : ℕ} (ha : a < a0) (ha0 : a0 ≤ T + 1)
    (hU : ∀ j, IsOpen (U j)) (h0 : ∀ j, (0 : V n) ∈ U j)
    (hf : ∀ j, DifferentiableOn ℂ (f j) (U j)) (hw : ∀ j, DifferentiableOn ℂ (w j) (U j))
    (hs : ∀ j k, DifferentiableOn ℂ (fun z => s j z k) (U j))
    (ht : ∀ j k, DifferentiableOn ℂ (fun z => t j z k) (U j))
    (hw0 : ∀ j, w j 0 ≠ 0) (hs0 : ∀ j k, s j 0 k = 0)
    (hcoord : ∀ j, (fderiv ℂ (fun z : V n => (WithLp.toLp 2 fun k => s j z k / w j z : V n)) 0).det ≠ 0)
    (hsurj : ∀ v : Fin m → ℂ, ∃ c : Fin δ → ℂ, ∀ j, ∑ k, c k * t j 0 k = v j)
    (cc : (Fin n → ℕ) → Fin δ → ℂ)
    (hcc : ∀ j, (fun z => f j z - leadVal (s j z) (w j z) (t j z) T a0 cc) =O[𝓝 0] fun z => ‖z‖ ^ a) :
    ∃ cc' : (Fin n → ℕ) → Fin δ → ℂ, ∀ j,
      (fun z => f j z - leadVal (s j z) (w j z) (t j z) T a0 cc') =O[𝓝 0] fun z => ‖z‖ ^ (a + 1) := by
  classical
  set ζ : Fin m → V n → V n := fun j z => (WithLp.toLp 2 fun k => s j z k / w j z : V n) with hζdef
  have loc : ∀ j, ∃ U' : Set (V n), IsOpen U' ∧ (0 : V n) ∈ U' ∧ U' ⊆ U j ∧
      (∀ v ∈ U', w j v ≠ 0) ∧ DifferentiableOn ℂ (ζ j) U' ∧ ζ j 0 = 0 := by
    intro j
    refine ⟨U j ∩ w j ⁻¹' {0}ᶜ, (hw j).continuousOn.isOpen_inter_preimage (hU j)
      isOpen_compl_singleton, ⟨h0 j, hw0 j⟩, Set.inter_subset_left, fun v hv => hv.2, ?_, ?_⟩
    · refine differentiableOn_euclidean.2 fun k => ?_
      have hdiv : DifferentiableOn ℂ (fun v => s j v k * (w j v)⁻¹) (U j ∩ w j ⁻¹' {0}ᶜ) :=
        ((hs j k).mono Set.inter_subset_left).mul
          (((hw j).mono Set.inter_subset_left).inv fun v hv => hv.2)
      exact hdiv.congr fun v _ => by simp [hζdef, div_eq_mul_inv]
    · ext k
      simp [hζdef, hs0]
  have hb : ∀ j, ∃ b : (Fin n → ℕ) → ℂ,
      (fun v => (f j v - leadVal (s j v) (w j v) (t j v) T a0 cc) -
        ∑ α ∈ Finset.Nat.antidiagonalTuple n a, b α * ∏ k, ζ j v k ^ α k)
        =O[𝓝 0] fun v => ‖v‖ ^ (a + 1) := by
    intro j
    obtain ⟨U', hUo, hxU, hUt, -, hζ, hζ0⟩ := loc j
    obtain ⟨b, hb⟩ := taylor_expansion_local_coordinates (a := a)
      (fun v => f j v - leadVal (s j v) (w j v) (t j v) T a0 cc) (ζ j) U' 0 hUo hxU
      (((hf j).sub (leadVal_diffOn (hs j) (hw j) (ht j) T a0 cc)).mono hUt) hζ hζ0 (hcoord j)
      (by simpa only [sub_zero] using hcc j)
    exact ⟨b, by simpa only [sub_zero] using hb⟩
  choose bb hbb using hb
  choose dd hdd using fun α => hsurj (fun j => bb j α / w j 0 ^ T)
  refine ⟨fun α k => cc α k + if ∑ q, α q = a then dd α k else 0, fun j => ?_⟩
  obtain ⟨U', hUo, hxU, hUt, hUw, hζ, hζ0⟩ := loc j
  have hxt : U j ∈ 𝓝 (0 : V n) := (hU j).mem_nhds (h0 j)
  have hζO : (fun v => ζ j v) =O[𝓝 0] fun v => v := by
    have := (hζ.differentiableAt (hUo.mem_nhds hxU)).hasFDerivAt.isBigO_sub
    simpa only [hζ0, sub_zero] using this
  have hQ : ∀ α ∈ Finset.Nat.antidiagonalTuple n a,
      (fun v => ∏ k, ζ j v k ^ α k) =O[𝓝 0] fun v => ‖v‖ ^ a := by
    intro α hα
    have hsum := Finset.Nat.mem_antidiagonalTuple.1 hα
    refine (IsBigO.of_bound 1 (Eventually.of_forall fun v => ?_)).trans (hζO.norm_norm.pow a)
    calc ‖∏ k, ζ j v k ^ α k‖
        = ∏ k, ‖ζ j v k‖ ^ α k := by simp only [norm_prod, norm_pow]
      _ ≤ ∏ k, ‖ζ j v‖ ^ α k :=
          Finset.prod_le_prod (fun k _ => by positivity)
            (fun k _ => pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le _ _) _)
      _ = 1 * ‖‖ζ j v‖ ^ a‖ := by
          rw [Finset.prod_pow_eq_pow_sum, hsum, one_mul, norm_pow, norm_norm]
  have hφ : ∀ α, (fun v => bb j α - w j v ^ T * ∑ k, dd α k * t j v k)
        =O[𝓝 0] fun v => ‖v‖ ^ 1 := by
    intro α
    have hd : DifferentiableAt ℂ (fun v => bb j α - w j v ^ T * ∑ k, dd α k * t j v k) 0 := by
      refine (differentiableAt_const _).sub ((((hw j).differentiableAt hxt).pow T).mul ?_)
      exact DifferentiableAt.fun_sum fun k _ => ((ht j k).differentiableAt hxt).const_mul _
    have h00 : bb j α - w j 0 ^ T * ∑ k, dd α k * t j 0 k = 0 := by
      rw [hdd α j, mul_div_cancel₀ _ (pow_ne_zero _ (hw0 j)), sub_self]
    have := hd.hasFDerivAt.isBigO_sub
    rw [h00] at this
    simp only [sub_zero] at this
    exact (this.trans (isBigO_refl _ _).norm_right).congr_right fun v => (pow_one _).symm
  have h2 : (fun v => ∑ α ∈ Finset.Nat.antidiagonalTuple n a,
      (bb j α - w j v ^ T * ∑ k, dd α k * t j v k) * ∏ k, ζ j v k ^ α k)
      =O[𝓝 0] fun v => ‖v‖ ^ (a + 1) := by
    have hterm : ∀ α ∈ Finset.Nat.antidiagonalTuple n a,
        (fun v => (bb j α - w j v ^ T * ∑ k, dd α k * t j v k) * ∏ k, ζ j v k ^ α k)
        =O[𝓝 0] fun v => ‖v‖ ^ (a + 1) :=
      fun α hα => ((hφ α).mul (hQ α hα)).congr_right fun v => by ring
    exact (IsBigO.sum hterm).congr_left fun v => Finset.sum_apply _ _ _
  refine ((hbb j).add h2).congr' ?_ EventuallyEq.rfl
  filter_upwards [hUo.mem_nhds hxU] with v hv
  beta_reduce
  rw [leadVal_add _ _ _ ha ha0 cc dd (hUw v hv)]
  simp only [hζdef, PiLp.toLp_apply, sub_mul, Finset.sum_sub_distrib]
  ring

/- English proof (translation)
Establish `key : ∀ a ≤ a0, ∃ cc : (Fin n → ℕ) → Fin δ → ℂ, ∀ j, (fun z => f j z - leadVal (s j z) (w j z) (t j z) T a0 cc) =O[𝓝 0] fun z => ‖z‖ ^ a`. Introduce `a`. Proceed by induction on `a with`. Consider the case `zero`. Introduce `_`.

Use `⟨0, fun j => ?_⟩` and prove the remaining obligations. Establish `hc` using `(((hf j).sub (leadVal_diffOn (hs j) (hw j) (ht j) T a0 0)).differentiableAt ((hU j).mem_nhds (h0 j))).continuousAt`. Conclude with `(hc.tendsto.isBigO_one ℝ).congr_right fun v => (pow_zero _).symm`. Consider the case `succ a ih`. Introduce `ha`.

Take `⟨cc, hcc⟩` from `ih (by omega)`. Conclude with `step (by omega) ha0 hU h0 hf hw hs ht hw0 hs0 hcoord hsurj cc hcc`. Conclude with `key a0 le_rfl`.
-/
theorem jets {T a0 : ℕ} (ha0 : a0 ≤ T + 1)
    (hU : ∀ j, IsOpen (U j)) (h0 : ∀ j, (0 : V n) ∈ U j)
    (hf : ∀ j, DifferentiableOn ℂ (f j) (U j)) (hw : ∀ j, DifferentiableOn ℂ (w j) (U j))
    (hs : ∀ j k, DifferentiableOn ℂ (fun z => s j z k) (U j))
    (ht : ∀ j k, DifferentiableOn ℂ (fun z => t j z k) (U j))
    (hw0 : ∀ j, w j 0 ≠ 0) (hs0 : ∀ j k, s j 0 k = 0)
    (hcoord : ∀ j, (fderiv ℂ (fun z : V n => (WithLp.toLp 2 fun k => s j z k / w j z : V n)) 0).det ≠ 0)
    (hsurj : ∀ v : Fin m → ℂ, ∃ c : Fin δ → ℂ, ∀ j, ∑ k, c k * t j 0 k = v j) :
    ∃ cc : (Fin n → ℕ) → Fin δ → ℂ, ∀ j,
      (fun z => f j z - leadVal (s j z) (w j z) (t j z) T a0 cc) =O[𝓝 0] fun z => ‖z‖ ^ a0 := by
  have key : ∀ a ≤ a0, ∃ cc : (Fin n → ℕ) → Fin δ → ℂ, ∀ j,
      (fun z => f j z - leadVal (s j z) (w j z) (t j z) T a0 cc) =O[𝓝 0] fun z => ‖z‖ ^ a := by
    intro a
    induction a with
    | zero =>
      intro _
      refine ⟨0, fun j => ?_⟩
      have hc := (((hf j).sub (leadVal_diffOn (hs j) (hw j) (ht j) T a0 0)).differentiableAt
        ((hU j).mem_nhds (h0 j))).continuousAt
      exact (hc.tendsto.isBigO_one ℝ).congr_right fun v => (pow_zero _).symm
    | succ a ih =>
      intro ha
      obtain ⟨cc, hcc⟩ := ih (by omega)
      exact step (by omega) ha0 hU h0 hf hw hs ht hw0 hs0 hcoord hsurj cc hcc
  exact key a0 le_rfl

end Step

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Use extensionality with `a b`. Distinguish the cases in `h1 : b < a`. Simplify using `[mat, nmat, h1, h1.ne']`. Both sides reduce to the same expression. Simplify using `[mat, nmat, h1, Matrix.one_apply]`.
-/
theorem mat_nmat_zero {r : ℕ} (X : Data E r) (τ : X.Ψ) : mat (nmat X 0) τ = 1 := by
  ext a b
  by_cases h1 : b < a
  · simp [mat, nmat, h1, h1.ne']
    rfl
  · simp [mat, nmat, h1, Matrix.one_apply]

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Use `show (mat x0 τ * mat (nmat X 0) τ : Matrix (Fin r) (Fin r) ℂ) = x0 τ`. Rewrite using `[mat_nmat_zero, Matrix.mul_one]`. Both sides reduce to the same expression.
-/
theorem cpt_zero {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) : cpt X x0 0 = x0 := by
  funext τ
  show (mat x0 τ * mat (nmat X 0) τ : Matrix (Fin r) (Fin r) ℂ) = x0 τ
  rw [mat_nmat_zero, Matrix.mul_one]
  rfl

/- English proof (translation)
The claim follows from `cpt_zero X x0`.
-/
theorem rmul_nmat_zero {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) : rmul x0 (nmat X 0) = x0 :=
  cpt_zero X x0

/- English proof (translation)
Introduce `τ`. Use `⟨by rw [mat_nmat_zero, Matrix.det_one]; exact one_ne_zero, fun a c h => ?_⟩` and prove the remaining obligations. Use `congrFun (congrFun (mat_nmat_zero X τ) a) c` as an intermediate fact. Rewrite `this` using `[Matrix.one_apply_ne h.ne']`. Conclude with `this`.
-/
theorem nmat_zero_mem_Bor {r : ℕ} (X : Data E r) : nmat X 0 ∈ Bor X.Ψ r := by
  intro τ
  refine ⟨by rw [mat_nmat_zero, Matrix.det_one]; exact one_ne_zero, fun a c h => ?_⟩
  have := congrFun (congrFun (mat_nmat_zero X τ) a) c
  rw [Matrix.one_apply_ne h.ne'] at this
  exact this

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Use `show (((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ : Matrix (Fin r) (Fin r) ℂ) = x τ`. Rewrite using `[Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]`. Both sides reduce to the same expression.
-/
theorem lact_one {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) : lact (1 : GL (Fin r) E) x = x := by
  funext τ
  show (((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ : Matrix (Fin r) (Fin r) ℂ) = x τ
  rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  rfl

/- English proof (translation)
Introduce `r X Xa Fl G T a δ ha t ht hb f hf`. Establish `hs0 : ∀ j k, Fl.s k (Fl.xs j) = 0` using `fun j => (Fl.S_eq _ (Fl.xs_mem j)).2 ⟨j, 1, one_mem _, nmat X 0, nmat_zero_mem_Bor X, by`. Rewrite using `[rmul_nmat_zero, lact_one]⟩`. Conclude with `jets (U := fun j => OmF X (Fl.xs j)) (f := fun j z => f (cpt X (Fl.xs j) z)) (w := fun j z => Fl.w0 (cpt X (Fl.xs j) z)) (s := fun j z k => Fl.s k (cpt X (Fl.xs j) z)) (t := fun j z k => t k (cpt X (Fl.xs j) z)) ha (fun j => OntoB.isOpen_OmF X _) (fun j => by show cpt X (Fl.xs j) …`. Rewrite using `[cpt_zero]`.

Conclude with `Fl.xs_mem j)`. Use the proof step `(fun j => OntoB.hol_comp X _ hf.1)`. Use the proof step `(fun j => OntoB.hol_comp X _ Fl.weightForm_vanishes.1.1.1.1)`. Use the proof step `(fun j k => OntoB.hol_comp X _ (Fl.s_van k).1.1.1.1)`. Use the proof step `(fun j k => OntoB.hol_comp X _ (ht k).1)`.

Use the proof step `(fun j => by simpa only [cpt_zero] using Fl.w0_ne j)`. Use the proof step `(fun j k => by simpa only [cpt_zero] using hs0 j k)`. Use the proof step `Fl.coord`. Use the proof step `(fun v => by simpa only [cpt_zero] using hb.1 v)`.
-/
theorem main : ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (T a δ : ℕ), a ≤ T + 1 →
    ∀ (t : Fin δ → Frame X.Ψ r → ℂ), (∀ k, X.IsSec G (t k)) → IsValBasisM X Fl.xs t →
    ∀ f, X.IsSec (G + T • Xa.L) f →
    ∃ cc : (Fin (nd X) → ℕ) → Fin δ → ℂ, ∀ j,
      (fun z : V (nd X) => f (cpt X (Fl.xs j) z) - leadM X Fl.s Fl.w0 t T a cc (cpt X (Fl.xs j) z))
        =O[𝓝 0] fun z => ‖z‖ ^ a := by
  intro r X Xa Fl G T a δ ha t ht hb f hf
  have hs0 : ∀ j k, Fl.s k (Fl.xs j) = 0 := fun j =>
    (Fl.S_eq _ (Fl.xs_mem j)).2 ⟨j, 1, one_mem _, nmat X 0, nmat_zero_mem_Bor X, by
      rw [rmul_nmat_zero, lact_one]⟩
  exact jets (U := fun j => OmF X (Fl.xs j)) (f := fun j z => f (cpt X (Fl.xs j) z))
    (w := fun j z => Fl.w0 (cpt X (Fl.xs j) z)) (s := fun j z k => Fl.s k (cpt X (Fl.xs j) z))
    (t := fun j z k => t k (cpt X (Fl.xs j) z)) ha
    (fun j => OntoB.isOpen_OmF X _)
    (fun j => by
      show cpt X (Fl.xs j) 0 ∈ X.dom
      rw [cpt_zero]; exact Fl.xs_mem j)
    (fun j => OntoB.hol_comp X _ hf.1)
    (fun j => OntoB.hol_comp X _ Fl.weightForm_vanishes.1.1.1.1)
    (fun j k => OntoB.hol_comp X _ (Fl.s_van k).1.1.1.1)
    (fun j k => OntoB.hol_comp X _ (ht k).1)
    (fun j => by simpa only [cpt_zero] using Fl.w0_ne j)
    (fun j k => by simpa only [cpt_zero] using hs0 j k)
    Fl.coord
    (fun v => by simpa only [cpt_zero] using hb.1 v)

end

end GlobalTheory.LeadJets
