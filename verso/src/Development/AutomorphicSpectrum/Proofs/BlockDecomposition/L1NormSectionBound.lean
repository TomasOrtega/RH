import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageDerivativeL1Bound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelUniqueness

noncomputable section

open MeasureTheory Matrix Topology Filter
open scoped ContDiff InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.ApproxK

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveK
open GlobalTheory.CompanionTheory.KerUniq

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace msK

variable {n : ℕ}

local instance : BorelSpace (UK n) := ⟨rfl⟩
local instance : CompactSpace (UK n) := GlobalTheory.compactSpace_unitaryGroup (Fin n) ℂ
local instance : SecondCountableTopology (Mat n) :=
  inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
local instance : LocallyCompactSpace (Mat n) :=
  inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
local instance : ProperSpace (Mat n) :=
  inferInstanceAs (ProperSpace (Fin n → Fin n → ℂ))
local instance : SecondCountableTopology (G n) :=
  have : SecondCountableTopology (Mat n)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  Units.isEmbedding_embedProduct.secondCountableTopology
local instance : LocallyCompactSpace (G n) := inferInstanceAs (LocallyCompactSpace (Mat n)ˣ)
local instance : SecondCountableTopology (UK n) :=
  (Topology.IsEmbedding.subtypeVal (p := fun x => x ∈ unitaryGroup (Fin n) ℂ)).secondCountableTopology
local instance : (nu n).IsHaarMeasure := by unfold nu; infer_instance
local instance : IsFiniteMeasure (nu n) := CompactSpace.isFiniteMeasure
local instance : (nu n).IsMulRightInvariant :=
  ⟨fun g => GlobalTheory.CompactRight.map_mul_right_eq_of_mem_compact (nu n) ⊤
    (by simpa using isCompact_univ) g (Subgroup.mem_top g)⟩

def nsq (A : Mat n) : ℝ := (Matrix.trace (Aᴴ * A)).re

/- English proof (translation)
Simplify using `only [nsq, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.star_def, Complex.conj_mul']`. Use `norm_cast`.
-/
theorem nsq_eq (A : Mat n) : nsq A = ∑ a, ∑ b, ‖A a b‖ ^ 2 := by
  simp only [nsq, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  norm_cast

/- English proof (translation)
Establish `h : (k.1)ᴴ * k.1 = 1` using `Unitary.star_mul_self_of_mem k.2`. Unfold `nsq`. Rewrite using `[Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (k.1)ᴴ, h, Matrix.one_mul]`.
-/
theorem nsq_mul_left (k : UK n) (A : Mat n) : nsq (k.1 * A) = nsq A := by
  have h : (k.1)ᴴ * k.1 = 1 := Unitary.star_mul_self_of_mem k.2
  unfold nsq
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (k.1)ᴴ, h, Matrix.one_mul]

/- English proof (translation)
Establish `h : k.1 * (k.1)ᴴ = 1` using `Unitary.mul_star_self_of_mem k.2`. Unfold `nsq`. Rewrite using `[Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, h, Matrix.mul_one]`.
-/
theorem nsq_mul_right (k : UK n) (A : Mat n) : nsq (A * k.1) = nsq A := by
  have h : k.1 * (k.1)ᴴ = 1 := Unitary.mul_star_self_of_mem k.2
  unfold nsq
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, h, Matrix.mul_one]

def frob (y : Mat n) : ℝ := nsq (y - 1)

/- English proof (translation)
Establish `h1 : k.1 * (k.1)ᴴ = 1` using `Unitary.mul_star_self_of_mem k.2`. Establish `h2 : (k.1)ᴴ * k.1 = 1` using `Unitary.star_mul_self_of_mem k.2`. Establish `e1 : k.1 * z - 1 = k.1 * (z - (k.1)ᴴ)` using `by rw [Matrix.mul_sub, h1]`. Establish `e2 : z * k.1 - 1 = (z - (k.1)ᴴ) * k.1` using `by rw [Matrix.sub_mul, h2]`. Unfold `frob`.

Rewrite using `[e1, e2, nsq_mul_left, nsq_mul_right]`.
-/
theorem frob_swap (k : UK n) (z : Mat n) : frob (k.1 * z) = frob (z * k.1) := by
  have h1 : k.1 * (k.1)ᴴ = 1 := Unitary.mul_star_self_of_mem k.2
  have h2 : (k.1)ᴴ * k.1 = 1 := Unitary.star_mul_self_of_mem k.2
  have e1 : k.1 * z - 1 = k.1 * (z - (k.1)ᴴ) := by rw [Matrix.mul_sub, h1]
  have e2 : z * k.1 - 1 = (z - (k.1)ᴴ) * k.1 := by rw [Matrix.sub_mul, h2]
  unfold frob
  rw [e1, e2, nsq_mul_left, nsq_mul_right]

/- English proof (translation)
Simplify using `[frob, nsq]`.
-/
theorem frob_one : frob (1 : Mat n) = 0 := by simp [frob, nsq]

/- English proof (translation)
Establish `: (frob : Mat n → ℝ) = fun y => ∑ a, ∑ b, ‖(y - 1) a b‖ ^ 2`. Use function extensionality and compare the values at `y`. Conclude with `nsq_eq _`. Rewrite using `[this]`. Use `ContDiff.sum fun a _ => ContDiff.sum fun b _ => ?_` and prove the remaining obligations.

Establish `h : ContDiff ℝ ∞ fun y : Mat n => (y - 1) a b` using `contDiff_pi.1 (contDiff_pi.1 (contDiff_id.sub contDiff_const) a) b`. Conclude with `(contDiff_norm_sq ℝ).comp h`.
-/
theorem contDiff_frob : ContDiff ℝ ∞ (frob : Mat n → ℝ) := by
  have : (frob : Mat n → ℝ) = fun y => ∑ a, ∑ b, ‖(y - 1) a b‖ ^ 2 := by
    funext y; exact nsq_eq _
  rw [this]
  refine ContDiff.sum fun a _ => ContDiff.sum fun b _ => ?_
  have h : ContDiff ℝ ∞ fun y : Mat n => (y - 1) a b :=
    contDiff_pi.1 (contDiff_pi.1 (contDiff_id.sub contDiff_const) a) b
  exact (contDiff_norm_sq ℝ).comp h

/- English proof (translation)
Rewrite using `[frob, nsq_eq]`. Use `le_trans ?_ (Finset.single_le_sum (f := fun a => ∑ b, ‖(y - 1) a b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ a))` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := fun b => ‖(y - 1) a b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ b)`.
-/
theorem entry_sq_le (y : Mat n) (a b : Fin n) : ‖(y - 1) a b‖ ^ 2 ≤ frob y := by
  rw [frob, nsq_eq]
  refine le_trans ?_ (Finset.single_le_sum (f := fun a => ∑ b, ‖(y - 1) a b‖ ^ 2)
    (fun _ _ => by positivity) (Finset.mem_univ a))
  exact Finset.single_le_sum (f := fun b => ‖(y - 1) a b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ b)

/- English proof (translation)
The claim follows from `(Matrix.norm_le_iff (Real.sqrt_nonneg _)).2 fun a b => Real.le_sqrt_of_sq_le (entry_sq_le y a b)`.
-/
theorem norm_sub_one_le (y : Mat n) : ‖y - 1‖ ≤ Real.sqrt (frob y) :=
  (Matrix.norm_le_iff (Real.sqrt_nonneg _)).2 fun a b =>
    Real.le_sqrt_of_sq_le (entry_sq_le y a b)

/- English proof (translation)
Take `⟨r, hr, hb⟩` from `Metric.mem_nhds_iff.1 hU`. Use `⟨r ^ 2, by positivity, fun y hy => hb ?_⟩` and prove the remaining obligations. Rewrite using `[Metric.mem_ball, dist_eq_norm]`. Use `(norm_sub_one_le y).trans_lt ?_` and prove the remaining obligations. Conclude with `(Real.sqrt_lt' hr).2 hy`.
-/
theorem exists_frob_lt {U : Set (Mat n)} (hU : U ∈ 𝓝 (1 : Mat n)) : ∃ ε > 0, ∀ y, frob y < ε → y ∈ U := by
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.1 hU
  refine ⟨r ^ 2, by positivity, fun y hy => hb ?_⟩
  rw [Metric.mem_ball, dist_eq_norm]
  refine (norm_sub_one_le y).trans_lt ?_
  exact (Real.sqrt_lt' hr).2 hy

/- English proof (translation)
Use `Metric.isCompact_of_isClosed_isBounded (isClosed_le contDiff_frob.continuous continuous_const) ?_` and prove the remaining obligations. Use `(Metric.isBounded_closedBall (x := (1 : Mat n)) (r := Real.sqrt r)).subset fun y hy => ?_` and prove the remaining obligations. Rewrite using `[Metric.mem_closedBall, dist_eq_norm]`. Conclude with `(norm_sub_one_le y).trans (Real.sqrt_le_sqrt hy)`.
-/
theorem isCompact_frob_le (r : ℝ) : IsCompact {y : Mat n | frob y ≤ r} := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_le contDiff_frob.continuous continuous_const) ?_
  refine (Metric.isBounded_closedBall (x := (1 : Mat n)) (r := Real.sqrt r)).subset fun y hy => ?_
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact (norm_sub_one_le y).trans (Real.sqrt_le_sqrt hy)

def bp (δ : ℝ) (j : ℕ) (y : Mat n) : ℝ := Real.smoothTransition (1 - (j + 1) * frob y / δ)

/- English proof (translation)
Use `Real.smoothTransition.contDiff.comp ?_` and prove the remaining obligations. Conclude with `contDiff_const.sub ((contDiff_const.mul contDiff_frob).div_const δ)`.
-/
theorem contDiff_bp (δ : ℝ) (j : ℕ) : ContDiff ℝ ∞ (bp δ j : Mat n → ℝ) := by
  refine Real.smoothTransition.contDiff.comp ?_
  exact contDiff_const.sub ((contDiff_const.mul contDiff_frob).div_const δ)

/- English proof (translation)
The claim follows from `Real.smoothTransition.nonneg _`.
-/
theorem bp_nonneg (δ : ℝ) (j : ℕ) (y : Mat n) : 0 ≤ bp δ j y := Real.smoothTransition.nonneg _

/- English proof (translation)
Simplify using `only [bp, frob_swap]`.
-/
theorem bp_swap (δ : ℝ) (j : ℕ) (k : UK n) (z : Mat n) : bp δ j (k.1 * z) = bp δ j (z * k.1) := by
  simp only [bp, frob_swap]

/- English proof (translation)
Simplify using `[bp, frob_one]`.
-/
theorem bp_one (δ : ℝ) (j : ℕ) : bp δ j (1 : Mat n) = 1 := by
  simp [bp, frob_one]

/- English proof (translation)
Use `Real.smoothTransition.zero_of_nonpos ?_` and prove the remaining obligations. Establish `hj : (0 : ℝ) < j + 1` using `by positivity`. Rewrite `hy` using `[div_le_iff₀ hj]`. Rewrite using `[sub_nonpos, one_le_div hδ]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem bp_eq_zero {δ : ℝ} (hδ : 0 < δ) (j : ℕ) {y : Mat n} (hy : δ / (j + 1) ≤ frob y) : bp δ j y = 0 := by
  refine Real.smoothTransition.zero_of_nonpos ?_
  have hj : (0 : ℝ) < j + 1 := by positivity
  rw [div_le_iff₀ hj] at hy
  rw [sub_nonpos, one_le_div hδ]
  linarith

/- English proof (translation)
Use `closure_minimal (fun y hy => ?_) (isClosed_le contDiff_frob.continuous continuous_const)` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Conclude with `hy (bp_eq_zero hδ j (le_of_lt (not_le.1 h)))`.
-/
theorem tsupport_bp {δ : ℝ} (hδ : 0 < δ) (j : ℕ) : tsupport (bp δ j : Mat n → ℝ) ⊆ {y | frob y ≤ δ / (j + 1)} := by
  refine closure_minimal (fun y hy => ?_) (isClosed_le contDiff_frob.continuous continuous_const)
  by_contra h
  exact hy (bp_eq_zero hδ j (le_of_lt (not_le.1 h)))

/- English proof (translation)
The claim follows from `(isCompact_frob_le _).of_isClosed_subset (isClosed_tsupport _) (tsupport_bp hδ j)`.
-/
theorem hasCompactSupport_bp {δ : ℝ} (hδ : 0 < δ) (j : ℕ) : HasCompactSupport (bp δ j : Mat n → ℝ) :=
  (isCompact_frob_le _).of_isClosed_subset (isClosed_tsupport _) (tsupport_bp hδ j)

section Avg

variable {E : KMod n} {β : Mat n → ℝ}

/- English proof (translation)
Unfold `sec`. Establish `h : ∫ κ : UK n, β (k.1 * y * κ.1) • E.ρ κ v ∂nu n = ∫ κ : UK n, (fun κ' : UK n => β (y * κ'.1) • E.ρ (κ' * k⁻¹) v) (κ * k) ∂nu n`. Use `integral_congr_ae (Eventually.of_forall fun κ => ?_)` and prove the remaining obligations. Establish `e : k.1 * y * κ.1 = k.1 * (y * κ.1)` using `Matrix.mul_assoc _ _ _`. Establish `e2 : y * (κ * k).1 = y * κ.1 * k.1` using `(Matrix.mul_assoc _ _ _).symm`.

Simplify using `only [e, e2, hb, mul_inv_cancel_right]`. Rewrite using `[h, integral_mul_right_eq_self (fun κ' : UK n => β (y * κ'.1) • E.ρ (κ' * k⁻¹) v) k]`. Simplify using `[map_mul]`.
-/
theorem sec_left (hb : ∀ (k : UK n) (z : Mat n), β (k.1 * z) = β (z * k.1)) (v : E.V) (k : UK n) (y : Mat n) :
    sec E β v (k.1 * y) = sec E β (E.ρ k⁻¹ v) y := by
  unfold sec
  have h : ∫ κ : UK n, β (k.1 * y * κ.1) • E.ρ κ v ∂nu n =
      ∫ κ : UK n, (fun κ' : UK n => β (y * κ'.1) • E.ρ (κ' * k⁻¹) v) (κ * k) ∂nu n := by
    refine integral_congr_ae (Eventually.of_forall fun κ => ?_)
    have e : k.1 * y * κ.1 = k.1 * (y * κ.1) := Matrix.mul_assoc _ _ _
    have e2 : y * (κ * k).1 = y * κ.1 * k.1 := (Matrix.mul_assoc _ _ _).symm
    simp only [e, e2, hb, mul_inv_cancel_right]
  rw [h, integral_mul_right_eq_self (fun κ' : UK n => β (y * κ'.1) • E.ρ (κ' * k⁻¹) v) k]
  simp [map_mul]

def secL (hβ : Continuous β) : E.V →ₗ[ℂ] (Mat n → E.V) where
  toFun := sec E β
  map_add' v w := by
    funext y
    simp only [sec, map_add, smul_add, Pi.add_apply]
    exact integral_add (integrable_avg hβ y _ (continuous_orbit E v)) (integrable_avg hβ y _ (continuous_orbit E w))
  map_smul' c v := by
    funext y
    simp only [sec, map_smul, RingHom.id_apply, Pi.smul_apply]
    rw [← integral_smul]
    exact integral_congr_ae (Eventually.of_forall fun κ => smul_comm _ _ _)

/- English proof (translation)
Establish `hcont : Continuous (Function.uncurry fun (y : G n) (κ : UK n) => h (y * emb κ) • a y κ)` using `(hh.comp (continuous_fst.mul (continuous_emb.comp continuous_snd))).smul ha`. Establish `hint : Integrable (Function.uncurry fun (y : G n) (κ : UK n) => h (y * emb κ) • a y κ) (μ.prod (nu n))`. Use `hcont.integrable_of_hasCompactSupport ?_` and prove the remaining obligations. Establish `hm : Continuous fun p : G n × UK n => (p.1 * (emb p.2)⁻¹, p.2)` using `(continuous_fst.mul ((continuous_emb.comp continuous_snd).inv)).prodMk continuous_snd`. Use `HasCompactSupport.intro ((hc.isCompact.prod isCompact_univ).image hm) fun p hp => ?_` and prove the remaining obligations.

Assume the negation of the conclusion as `hne`. Use `hp ⟨(p.1 * emb p.2, p.2), ⟨subset_tsupport _ ?_, Set.mem_univ _⟩, ?_⟩` and prove the remaining obligations. Introduce `h0`. Conclude with `hne (by simp [Function.uncurry, h0])`. Simplify using the standard rewrite rules.

Use `⟨hint.integral_prod_left, ?_⟩` and prove the remaining obligations. Rewrite using `[integral_integral_swap hint]`. Use `integral_congr_ae (Eventually.of_forall fun κ => ?_)` and prove the remaining obligations. Use `integral_mul_emb μ (fun y => h y • a (y * (emb κ)⁻¹) κ) κ` as an intermediate fact. Simplify using `using this`.
-/
theorem fub {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {_ : MeasurableSpace (G n)} [BorelSpace (G n)]
    (μ : Measure (G n)) [μ.IsHaarMeasure] {h : G n → ℝ} (hh : Continuous h) (hc : HasCompactSupport h)
    {a : G n → UK n → W} (ha : Continuous (Function.uncurry a)) :
    Integrable (fun y => ∫ κ : UK n, h (y * emb κ) • a y κ ∂nu n) μ ∧
    ∫ y, ∫ κ : UK n, h (y * emb κ) • a y κ ∂nu n ∂μ = ∫ κ : UK n, ∫ y, h y • a (y * (emb κ)⁻¹) κ ∂μ ∂nu n := by
  have hcont : Continuous (Function.uncurry fun (y : G n) (κ : UK n) => h (y * emb κ) • a y κ) :=
    (hh.comp (continuous_fst.mul (continuous_emb.comp continuous_snd))).smul ha
  have hint : Integrable (Function.uncurry fun (y : G n) (κ : UK n) => h (y * emb κ) • a y κ) (μ.prod (nu n)) := by
    refine hcont.integrable_of_hasCompactSupport ?_
    have hm : Continuous fun p : G n × UK n => (p.1 * (emb p.2)⁻¹, p.2) :=
      (continuous_fst.mul ((continuous_emb.comp continuous_snd).inv)).prodMk continuous_snd
    refine HasCompactSupport.intro ((hc.isCompact.prod isCompact_univ).image hm) fun p hp => ?_
    by_contra hne
    refine hp ⟨(p.1 * emb p.2, p.2), ⟨subset_tsupport _ ?_, Set.mem_univ _⟩, ?_⟩
    · intro h0
      exact hne (by simp [Function.uncurry, h0])
    · simp
  refine ⟨hint.integral_prod_left, ?_⟩
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun κ => ?_)
  have := integral_mul_emb μ (fun y => h y • a (y * (emb κ)⁻¹) κ) κ
  simpa using this

/- English proof (translation)
Establish `hh : Continuous fun y : G n => β y.val` using `hβ.comp Units.continuous_val`. Establish `hch : HasCompactSupport fun y : G n => β y.val`. Use `HasCompactSupport.intro (isCompact_preimage_val hc.isCompact hs) fun y hy => ?_` and prove the remaining obligations. Conclude with `image_eq_zero_of_notMem_tsupport hy`. Take `⟨hI, hF⟩` from `fub μ hh hch (a := fun _ _ => ‖v‖) continuous_const`.

Establish `hb : ∀ y : G n, ‖sec E β v y.val‖ ≤ ∫ κ : UK n, β (y * emb κ).val • ‖v‖ ∂nu n`. Introduce `y`. Use `norm_integral_le_of_norm_le ?_ (Eventually.of_forall fun κ => ?_)` and prove the remaining obligations. Conclude with `((hβ.comp (continuous_const.matrix_mul continuous_subtype_val)).smul continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)`. Rewrite using `[norm_smul, E.iso, Real.norm_of_nonneg (h0 _)]`.

Both sides reduce to the same expression. Unfold `l1`. Use `(integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _) hI (Eventually.of_forall hb)).trans_eq ?_` and prove the remaining obligations. Rewrite using `[hF]`. Simplify using `only [integral_smul_const, integral_const, smul_eq_mul, integral_mul_const]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem l1_norm_section_bound {_ : MeasurableSpace (G n)} [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (hβ : Continuous β) (hc : HasCompactSupport β) (hs : tsupport β ⊆ GLs n) (h0 : ∀ y, 0 ≤ β y) (v : E.V) :
    l1 μ (sec E β v) ≤ (nu n).real Set.univ * (∫ y : G n, β y.val ∂μ) * ‖v‖ := by
  have hh : Continuous fun y : G n => β y.val := hβ.comp Units.continuous_val
  have hch : HasCompactSupport fun y : G n => β y.val := by
    refine HasCompactSupport.intro (isCompact_preimage_val hc.isCompact hs) fun y hy => ?_
    exact image_eq_zero_of_notMem_tsupport hy
  obtain ⟨hI, hF⟩ := fub μ hh hch (a := fun _ _ => ‖v‖) continuous_const
  have hb : ∀ y : G n, ‖sec E β v y.val‖ ≤ ∫ κ : UK n, β (y * emb κ).val • ‖v‖ ∂nu n := by
    intro y
    refine norm_integral_le_of_norm_le ?_ (Eventually.of_forall fun κ => ?_)
    · exact ((hβ.comp (continuous_const.matrix_mul continuous_subtype_val)).smul
        continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    · rw [norm_smul, E.iso, Real.norm_of_nonneg (h0 _)]
      rfl
  unfold l1
  refine (integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _) hI
    (Eventually.of_forall hb)).trans_eq ?_
  rw [hF]
  simp only [integral_smul_const, integral_const, smul_eq_mul, integral_mul_const]
  ring

/- English proof (translation)
Unfold `sec`. Rewrite using `[← inner_conj_symm, ← integral_inner (integrable_avg hβ y _ (continuous_orbit E v)), ← integral_conj]`. Use `integral_congr_ae (Eventually.of_forall fun κ => ?_)` and prove the remaining obligations. Simplify using `only [inner_conj_symm]`. Rewrite using `[← Complex.coe_smul, inner_smul_left]`.

Simplify using the standard rewrite rules.
-/
theorem inner_sec (hβ : Continuous β) (v w : E.V) (y : Mat n) :
    ⟪sec E β v y, w⟫_ℂ = ∫ κ : UK n, β (y * κ.1) • ⟪E.ρ κ v, w⟫_ℂ ∂nu n := by
  unfold sec
  rw [← inner_conj_symm, ← integral_inner (integrable_avg hβ y _ (continuous_orbit E v)), ← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun κ => ?_)
  simp only [inner_conj_symm]
  rw [← Complex.coe_smul, inner_smul_left]
  simp

/- English proof (translation)
The claim follows from `(LinearIsometry.mk (E.ρ κ : E.V →ₗ[ℂ] E.V) (E.iso κ)).inner_map_map v w`.
-/
theorem inner_rho (κ : UK n) (v w : E.V) : ⟪E.ρ κ v, E.ρ κ w⟫_ℂ = ⟪v, w⟫_ℂ :=
  (LinearIsometry.mk (E.ρ κ : E.V →ₗ[ℂ] E.V) (E.iso κ)).inner_map_map v w

/- English proof (translation)
Establish `hh : Continuous fun y : G n => β y.val` using `hβ.comp Units.continuous_val`. Establish `hch : HasCompactSupport fun y : G n => β y.val`. Use `HasCompactSupport.intro (isCompact_preimage_val hc.isCompact hs) fun y hy => ?_` and prove the remaining obligations. Conclude with `image_eq_zero_of_notMem_tsupport hy`. Establish `hfc : Continuous fun y : G n => f y.val` using `hf.1.continuousOn.comp_continuous Units.continuous_val val_mem`.

Establish `ha : Continuous (Function.uncurry fun (y : G n) (κ : UK n) => ⟪E.ρ κ v, f y.val⟫_ℂ)` using `((continuous_orbit E v).comp continuous_snd).inner (hfc.comp continuous_fst)`. Take `⟨-, hF⟩` from `fub μ hh hch ha`. Unfold `ip`. Repeatedly rewrite using `[inner_sec hβ]`. Use `hF.trans ?_` and prove the remaining obligations.

Establish `e : ∀ (κ : UK n) (y : G n), ⟪E.ρ κ v, f (y * (emb κ)⁻¹).val⟫_ℂ = ⟪v, f y.val⟫_ℂ`. Introduce `κ y`. Establish `e1 : (y * (emb κ)⁻¹).val = y.val * (κ⁻¹ : UK n).1`. Rewrite using `[← map_inv]`. Both sides reduce to the same expression.

Rewrite using `[e1, hf.2 _ (val_mem y), inv_inv, inner_rho]`. Simplify using `only [e, integral_const, Measure.real]`.
-/
theorem ip_sec {_ : MeasurableSpace (G n)} [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (hβ : Continuous β) (hc : HasCompactSupport β) (hs : tsupport β ⊆ GLs n) (v : E.V) {f : Mat n → E.V} (hf : f ∈ CE E) :
    ip μ (sec E β v) f = (nu n).real Set.univ • ∫ y : G n, β y.val • ⟪v, f y.val⟫_ℂ ∂μ := by
  have hh : Continuous fun y : G n => β y.val := hβ.comp Units.continuous_val
  have hch : HasCompactSupport fun y : G n => β y.val := by
    refine HasCompactSupport.intro (isCompact_preimage_val hc.isCompact hs) fun y hy => ?_
    exact image_eq_zero_of_notMem_tsupport hy
  have hfc : Continuous fun y : G n => f y.val :=
    hf.1.continuousOn.comp_continuous Units.continuous_val val_mem
  have ha : Continuous (Function.uncurry fun (y : G n) (κ : UK n) => ⟪E.ρ κ v, f y.val⟫_ℂ) :=
    ((continuous_orbit E v).comp continuous_snd).inner (hfc.comp continuous_fst)
  obtain ⟨-, hF⟩ := fub μ hh hch ha
  unfold ip
  simp_rw [inner_sec hβ]
  refine hF.trans ?_
  have e : ∀ (κ : UK n) (y : G n), ⟪E.ρ κ v, f (y * (emb κ)⁻¹).val⟫_ℂ = ⟪v, f y.val⟫_ℂ := by
    intro κ y
    have e1 : (y * (emb κ)⁻¹).val = y.val * (κ⁻¹ : UK n).1 := by
      rw [← map_inv]; rfl
    rw [e1, hf.2 _ (val_mem y), inv_inv, inner_rho]
  simp only [e, integral_const, Measure.real]

/- English proof (translation)
Establish `hgc : Continuous fun y : G n => g y.val` using `hg.comp_continuous Units.continuous_val val_mem`. Establish `hg1 : ContinuousAt g 1` using `hg.continuousAt (isOpen_GLs.mem_nhds (by simp [GLs]))`. Rewrite using `[Metric.tendsto_nhds]`. Introduce `ε hε`. Establish `hV : {m : Mat n | dist (g m) (g 1) < ε / 2} ∈ 𝓝 (1 : Mat n)` using `hg1.eventually (Metric.ball_mem_nhds _ (half_pos hε))`.

Use `filter_upwards [hU _ hV] with j hj`. Establish `hi : ∀ c : ℂ, Integrable (fun y : G n => w j y • c) μ` using `fun c => ((hwc j).smul continuous_const).integrable_of_hasCompactSupport ((hws j).smul_right)`. Establish `hi2 : Integrable (fun y : G n => w j y • g y.val) μ` using `((hwc j).smul hgc).integrable_of_hasCompactSupport ((hws j).smul_right)`. Establish `hiw : Integrable (w j) μ` using `(hwc j).integrable_of_hasCompactSupport (hws j)`. Establish `e : (∫ y : G n, w j y • g y.val ∂μ) - g 1 = ∫ y : G n, w j y • (g y.val - g 1) ∂μ`.

Simplify using `only [smul_sub]`. Rewrite using `[integral_sub hi2 (hi _), integral_smul_const, h1, one_smul]`. Rewrite using `[dist_eq_norm, e]`. Use `lt_of_le_of_lt (norm_integral_le_of_norm_le (g := fun y => w j y * (ε / 2)) (hiw.mul_const _) (Eventually.of_forall fun y => ?_)) ?_` and prove the remaining obligations. Rewrite using `[norm_smul, Real.norm_of_nonneg (hw0 j y)]`.

Distinguish the cases in `hy : y.val ∈ {m : Mat n | dist (g m) (g 1) < ε / 2}`. Use `mul_le_mul_of_nonneg_left ?_ (hw0 j y)` and prove the remaining obligations. Rewrite using `[← dist_eq_norm]`. Conclude with `le_of_lt hy`. Simplify using `[hj y hy]`.

Rewrite using `[integral_mul_const, h1]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem peak {_ : MeasurableSpace (G n)} [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (w : ℕ → G n → ℝ) (hwc : ∀ j, Continuous (w j)) (hws : ∀ j, HasCompactSupport (w j)) (hw0 : ∀ j y, 0 ≤ w j y)
    (h1 : ∀ j, ∫ y, w j y ∂μ = 1)
    (hU : ∀ U ∈ 𝓝 (1 : Mat n), ∀ᶠ j in atTop, ∀ y : G n, y.val ∉ U → w j y = 0)
    (g : Mat n → ℂ) (hg : ContinuousOn g (GLs n)) :
    Tendsto (fun j => ∫ y : G n, w j y • g y.val ∂μ) atTop (𝓝 (g 1)) := by
  have hgc : Continuous fun y : G n => g y.val := hg.comp_continuous Units.continuous_val val_mem
  have hg1 : ContinuousAt g 1 := hg.continuousAt (isOpen_GLs.mem_nhds (by simp [GLs]))
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hV : {m : Mat n | dist (g m) (g 1) < ε / 2} ∈ 𝓝 (1 : Mat n) :=
    hg1.eventually (Metric.ball_mem_nhds _ (half_pos hε))
  filter_upwards [hU _ hV] with j hj
  have hi : ∀ c : ℂ, Integrable (fun y : G n => w j y • c) μ := fun c =>
    ((hwc j).smul continuous_const).integrable_of_hasCompactSupport ((hws j).smul_right)
  have hi2 : Integrable (fun y : G n => w j y • g y.val) μ :=
    ((hwc j).smul hgc).integrable_of_hasCompactSupport ((hws j).smul_right)
  have hiw : Integrable (w j) μ := (hwc j).integrable_of_hasCompactSupport (hws j)
  have e : (∫ y : G n, w j y • g y.val ∂μ) - g 1 = ∫ y : G n, w j y • (g y.val - g 1) ∂μ := by
    simp only [smul_sub]
    rw [integral_sub hi2 (hi _), integral_smul_const, h1, one_smul]
  rw [dist_eq_norm, e]
  refine lt_of_le_of_lt (norm_integral_le_of_norm_le (g := fun y => w j y * (ε / 2)) (hiw.mul_const _)
    (Eventually.of_forall fun y => ?_)) ?_
  · rw [norm_smul, Real.norm_of_nonneg (hw0 j y)]
    by_cases hy : y.val ∈ {m : Mat n | dist (g m) (g 1) < ε / 2}
    · refine mul_le_mul_of_nonneg_left ?_ (hw0 j y)
      rw [← dist_eq_norm]
      exact le_of_lt hy
    · simp [hj y hy]
  · rw [integral_mul_const, h1]
    linarith

end Avg

/- English proof (translation)
Introduce `hL _ n _ _ μ _ E`. Establish `hLn` using `hL n`. Establish `hlgK : ∀ y ∈ GLs n, ∀ k : UK n, lg (y * k.1) = lg y`. Introduce `y hy k`. Use `hLn.2.2.1 y hy 1 k` as an intermediate fact.

Simplify using `using this`. Establish `hmulG : ∀ y ∈ GLs n, ∀ k : UK n, y * k.1 ∈ GLs n`. Introduce `y hy k`. Establish `hk : (k.1).det ≠ 0`. Use `(Matrix.isUnits_det_units (Unitary.toUnits k))` as an intermediate fact.

Conclude with `this.ne_zero`. Simplify using `only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at hy ⊢`. Conclude with `mul_ne_zero hy hk`. Establish `h1G : (1 : Mat n) ∈ GLs n` using `by simp [GLs]`. Establish `hnb : GLs n ∩ {y | lg y < lg (1 : Mat n) + 1} ∈ 𝓝 (1 : Mat n)`.

Establish `hc : ContinuousAt (lg : Mat n → ℝ) 1` using `continuousOn_lg.continuousAt (isOpen_GLs.mem_nhds h1G)`. Conclude with `Filter.inter_mem (isOpen_GLs.mem_nhds h1G) (hc.eventually (gt_mem_nhds (lt_add_one _)))`. Take `⟨ε, hε, hεU⟩` from `exists_frob_lt hnb`. Use `set δ := ε / 2 with hδdef`. Establish `hδ : 0 < δ` using `half_pos hε`.

Establish `hsmall : ∀ (j : ℕ) (y : Mat n), frob y ≤ δ / (j + 1) → y ∈ GLs n ∩ {y | lg y < lg (1 : Mat n) + 1}`. Introduce `j y hy`. Use `hεU y (lt_of_le_of_lt hy ?_)` and prove the remaining obligations. Establish `hj : (1 : ℝ) ≤ j + 1`. Establish `: (0 : ℝ) ≤ j` using `Nat.cast_nonneg j`.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `lt_of_le_of_lt (div_le_self hδ.le hj) (half_lt_self hε)`. Establish `hsG : ∀ j, tsupport (bp δ j : Mat n → ℝ) ⊆ GLs n` using `fun j y hy => (hsmall j y (tsupport_bp hδ j hy)).1`. Use `set c : ℝ := (nu n).real Set.univ with hcdef`. Establish `hcpos : 0 < c`.

Rewrite using `[hcdef, Measure.real, ENNReal.toReal_pos_iff]`. Conclude with `⟨isOpen_univ.measure_pos _ Set.univ_nonempty, measure_lt_top _ _⟩`. Establish `hbc : ∀ j, Continuous fun y : G n => bp δ j y.val` using `fun j => (contDiff_bp δ j).continuous.comp Units.continuous_val`. Establish `hbs : ∀ j, HasCompactSupport fun y : G n => bp δ j y.val` using `fun j => by`. Use `HasCompactSupport.intro (isCompact_preimage_val (hasCompactSupport_bp hδ j).isCompact (hsG j)) fun y hy => ?_` and prove the remaining obligations.

Conclude with `image_eq_zero_of_notMem_tsupport hy`. Use `set I : ℕ → ℝ := fun j => ∫ y : G n, bp δ j y.val ∂μ with hIdef`. Establish `hIpos : ∀ j, 0 < I j` using `fun j => (hbc j).integral_pos_of_hasCompactSupport_nonneg_nonzero (x := (1 : G n)) (hbs j) (fun y => bp_nonneg δ j _) (by simp [bp_one])`. Use `set β : ℕ → Mat n → ℝ := fun j y => (c * I j)⁻¹ * bp δ j y with hβdef`. Establish `hβs : ∀ j, ContDiff ℝ ∞ (β j)` using `fun j => contDiff_const.mul (contDiff_bp δ j)`.

Establish `hβc : ∀ j, Continuous (β j)` using `fun j => (hβs j).continuous`. Establish `hβ0 : ∀ j y, 0 ≤ β j y` using `fun j y => mul_nonneg (inv_nonneg.2 (mul_pos hcpos (hIpos j)).le) (bp_nonneg δ j y)`. Establish `hβsupp : ∀ j, tsupport (β j) ⊆ tsupport (bp δ j : Mat n → ℝ)` using `fun j => closure_mono (Function.support_const_smul_subset ((c * I j)⁻¹) (bp δ j : Mat n → ℝ))`. Establish `hβcs : ∀ j, HasCompactSupport (β j)` using `fun j => IsCompact.of_isClosed_subset (hasCompactSupport_bp hδ j) (isClosed_tsupport _) (hβsupp j)`. Establish `hβG : ∀ j, tsupport (β j) ⊆ GLs n` using `fun j => (hβsupp j).trans (hsG j)`.

Establish `hβint : ∀ j, ∫ y : G n, β j y.val ∂μ = c⁻¹`. Introduce `j`. Simplify using `only [hβdef]`. Rewrite using `[integral_const_mul]`. Use `(hIpos j).ne'` as an intermediate fact.

Establish `hc'` using `hcpos.ne'`. Express the relevant statement in the definitionally equal form `(c * I j)⁻¹ * I j = c⁻¹`. Clear the denominators using the available nonvanishing facts. Establish `hbsw : ∀ j (k : UK n) (z : Mat n), β j (k.1 * z) = β j (z * k.1)` using `fun j k z => by`. Simplify using `only [hβdef, bp_swap]`.

Use `⟨fun j => secL (hβc j), ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `j v show sec E (β j) v ∈ CE E`. Conclude with `⟨(contDiff_sec (hβs j)).contDiffOn, fun g _ κ => sec_mul (hβc j) g κ⟩`. Use `⟨lg (1 : Mat n) + 1, fun j v y hy hlt => ?_⟩ show sec E (β j) v y = 0` and prove the remaining obligations. Use `sec_eq_zero (U := GLs n ∩ {y | lg y < lg (1 : Mat n) + 1}) ?_ ?_ ?_` and prove the remaining obligations.

Introduce `z hz k`. Use `⟨hmulG z hz.1 k, ?_⟩` and prove the remaining obligations. Use `show lg (z * k.1) < _`. Rewrite using `[hlgK z hz.1 k]`. Conclude with `hz.2`.

Introduce `z hz`. Conclude with `hsmall j z (tsupport_bp hδ j (hβsupp j hz))`. Introduce `hyU`. Conclude with `absurd hyU.2 (not_lt.2 hlt.le)`. Use `⟨1, fun j v => ?_⟩ show l1 μ (sec E (β j) v) ≤ 1 * ‖v‖` and prove the remaining obligations.

Use `(l1_norm_section_bound μ (hβc j) (hβcs j) (hβG j) (hβ0 j) v).trans_eq ?_` and prove the remaining obligations. Rewrite using `[hβint, mul_inv_cancel₀ hcpos.ne']`. Introduce `j v k y _`. Conclude with `sec_left (hbsw j) v k y`. Introduce `v f hf _`.

Establish `hw` using `peak μ (fun j y => c * β j y.val) (fun j => continuous_const.mul ((hβc j).comp Units.continuous_val)) (fun j => by`. Use `HasCompactSupport.mul_left (f := fun _ : G n => c) (f' := fun y : G n => β j y.val) ?_` and prove the remaining obligations. Use `HasCompactSupport.intro (isCompact_preimage_val (hβcs j) (hβG j)) fun y hy => ?_` and prove the remaining obligations. Conclude with `image_eq_zero_of_notMem_tsupport hy)`. Use the proof step `(fun j y => mul_nonneg hcpos.le (hβ0 j _))`.

Use the proof step `(fun j => by rw [integral_const_mul, hβint, mul_inv_cancel₀ hcpos.ne'])`. Use the proof step `(by`. Introduce `U hU`. Take `⟨ε', hε', hU'⟩` from `exists_frob_lt hU`. Take `⟨N, hN⟩` from `exists_nat_gt (δ / ε')`.

Use `filter_upwards [eventually_ge_atTop N] with j hj y hy`. Establish `hfr : ε' ≤ frob y.val` using `not_lt.1 fun h => hy (hU' _ h)`. Establish `hNj : (N : ℝ) ≤ j` using `by exact_mod_cast hj`. Establish `hle : δ / ((j : ℝ) + 1) ≤ ε'`. Rewrite using `[div_le_iff₀ (by positivity)]`.

Rewrite `hN` using `[div_lt_iff₀ hε']`. Use the polynomial consequences of the given equalities and inequalities. Simplify using `only [hβdef, bp_eq_zero hδ j (hle.trans hfr), mul_zero])`. Use the proof step `(fun m => ⟪v, f m⟫_ℂ) (continuousOn_const.inner hf.1.continuousOn)`. Use `hw.congr fun j => ?_` and prove the remaining obligations.

Use `show _ = ip μ (sec E (β j) v) f`. Rewrite using `[ip_sec μ (hβc j) (hβcs j) (hβG j) v hf, ← integral_smul]`. Use `integral_congr_ae (Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Conclude with `mul_smul _ _ _`.
-/
theorem main : LgFacts → Unimod → ApproxId := by
  intro hL _ n _ _ μ _ E
  have hLn := hL n
  have hlgK : ∀ y ∈ GLs n, ∀ k : UK n, lg (y * k.1) = lg y := by
    intro y hy k
    have := hLn.2.2.1 y hy 1 k
    simpa using this
  have hmulG : ∀ y ∈ GLs n, ∀ k : UK n, y * k.1 ∈ GLs n := by
    intro y hy k
    have hk : (k.1).det ≠ 0 := by
      have := (Matrix.isUnits_det_units (Unitary.toUnits k))
      exact this.ne_zero
    simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at hy ⊢
    exact mul_ne_zero hy hk
  have h1G : (1 : Mat n) ∈ GLs n := by simp [GLs]

  have hnb : GLs n ∩ {y | lg y < lg (1 : Mat n) + 1} ∈ 𝓝 (1 : Mat n) := by
    have hc : ContinuousAt (lg : Mat n → ℝ) 1 := continuousOn_lg.continuousAt (isOpen_GLs.mem_nhds h1G)
    exact Filter.inter_mem (isOpen_GLs.mem_nhds h1G) (hc.eventually (gt_mem_nhds (lt_add_one _)))
  obtain ⟨ε, hε, hεU⟩ := exists_frob_lt hnb
  set δ := ε / 2 with hδdef
  have hδ : 0 < δ := half_pos hε
  have hsmall : ∀ (j : ℕ) (y : Mat n), frob y ≤ δ / (j + 1) → y ∈ GLs n ∩ {y | lg y < lg (1 : Mat n) + 1} := by
    intro j y hy
    refine hεU y (lt_of_le_of_lt hy ?_)
    have hj : (1 : ℝ) ≤ j + 1 := by
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      linarith
    exact lt_of_le_of_lt (div_le_self hδ.le hj) (half_lt_self hε)
  have hsG : ∀ j, tsupport (bp δ j : Mat n → ℝ) ⊆ GLs n := fun j y hy =>
    (hsmall j y (tsupport_bp hδ j hy)).1

  set c : ℝ := (nu n).real Set.univ with hcdef
  have hcpos : 0 < c := by
    rw [hcdef, Measure.real, ENNReal.toReal_pos_iff]
    exact ⟨isOpen_univ.measure_pos _ Set.univ_nonempty, measure_lt_top _ _⟩
  have hbc : ∀ j, Continuous fun y : G n => bp δ j y.val := fun j =>
    (contDiff_bp δ j).continuous.comp Units.continuous_val
  have hbs : ∀ j, HasCompactSupport fun y : G n => bp δ j y.val := fun j => by
    refine HasCompactSupport.intro (isCompact_preimage_val (hasCompactSupport_bp hδ j).isCompact (hsG j))
      fun y hy => ?_
    exact image_eq_zero_of_notMem_tsupport hy
  set I : ℕ → ℝ := fun j => ∫ y : G n, bp δ j y.val ∂μ with hIdef
  have hIpos : ∀ j, 0 < I j := fun j =>
    (hbc j).integral_pos_of_hasCompactSupport_nonneg_nonzero (x := (1 : G n)) (hbs j)
      (fun y => bp_nonneg δ j _) (by simp [bp_one])

  set β : ℕ → Mat n → ℝ := fun j y => (c * I j)⁻¹ * bp δ j y with hβdef
  have hβs : ∀ j, ContDiff ℝ ∞ (β j) := fun j => contDiff_const.mul (contDiff_bp δ j)
  have hβc : ∀ j, Continuous (β j) := fun j => (hβs j).continuous
  have hβ0 : ∀ j y, 0 ≤ β j y := fun j y =>
    mul_nonneg (inv_nonneg.2 (mul_pos hcpos (hIpos j)).le) (bp_nonneg δ j y)
  have hβsupp : ∀ j, tsupport (β j) ⊆ tsupport (bp δ j : Mat n → ℝ) := fun j =>
    closure_mono (Function.support_const_smul_subset ((c * I j)⁻¹) (bp δ j : Mat n → ℝ))
  have hβcs : ∀ j, HasCompactSupport (β j) := fun j =>
    IsCompact.of_isClosed_subset (hasCompactSupport_bp hδ j) (isClosed_tsupport _) (hβsupp j)
  have hβG : ∀ j, tsupport (β j) ⊆ GLs n := fun j => (hβsupp j).trans (hsG j)
  have hβint : ∀ j, ∫ y : G n, β j y.val ∂μ = c⁻¹ := by
    intro j
    simp only [hβdef]
    rw [integral_const_mul]
    have := (hIpos j).ne'
    have hc' := hcpos.ne'
    change (c * I j)⁻¹ * I j = c⁻¹
    field_simp
  have hbsw : ∀ j (k : UK n) (z : Mat n), β j (k.1 * z) = β j (z * k.1) := fun j k z => by
    simp only [hβdef, bp_swap]
  refine ⟨fun j => secL (hβc j), ?_, ?_, ?_, ?_, ?_⟩
  · intro j v
    show sec E (β j) v ∈ CE E
    exact ⟨(contDiff_sec (hβs j)).contDiffOn, fun g _ κ => sec_mul (hβc j) g κ⟩
  · refine ⟨lg (1 : Mat n) + 1, fun j v y hy hlt => ?_⟩
    show sec E (β j) v y = 0
    refine sec_eq_zero (U := GLs n ∩ {y | lg y < lg (1 : Mat n) + 1}) ?_ ?_ ?_
    · intro z hz k
      refine ⟨hmulG z hz.1 k, ?_⟩
      show lg (z * k.1) < _
      rw [hlgK z hz.1 k]
      exact hz.2
    · intro z hz
      exact hsmall j z (tsupport_bp hδ j (hβsupp j hz))
    · intro hyU
      exact absurd hyU.2 (not_lt.2 hlt.le)
  · refine ⟨1, fun j v => ?_⟩
    show l1 μ (sec E (β j) v) ≤ 1 * ‖v‖
    refine (l1_norm_section_bound μ (hβc j) (hβcs j) (hβG j) (hβ0 j) v).trans_eq ?_
    rw [hβint, mul_inv_cancel₀ hcpos.ne']
  · intro j v k y _
    exact sec_left (hbsw j) v k y
  · intro v f hf _
    have hw := peak μ (fun j y => c * β j y.val)
      (fun j => continuous_const.mul ((hβc j).comp Units.continuous_val))
      (fun j => by
        refine HasCompactSupport.mul_left (f := fun _ : G n => c) (f' := fun y : G n => β j y.val) ?_
        refine HasCompactSupport.intro (isCompact_preimage_val (hβcs j) (hβG j)) fun y hy => ?_
        exact image_eq_zero_of_notMem_tsupport hy)
      (fun j y => mul_nonneg hcpos.le (hβ0 j _))
      (fun j => by rw [integral_const_mul, hβint, mul_inv_cancel₀ hcpos.ne'])
      (by
        intro U hU
        obtain ⟨ε', hε', hU'⟩ := exists_frob_lt hU
        obtain ⟨N, hN⟩ := exists_nat_gt (δ / ε')
        filter_upwards [eventually_ge_atTop N] with j hj y hy
        have hfr : ε' ≤ frob y.val := not_lt.1 fun h => hy (hU' _ h)
        have hNj : (N : ℝ) ≤ j := by exact_mod_cast hj
        have hle : δ / ((j : ℝ) + 1) ≤ ε' := by
          rw [div_le_iff₀ (by positivity)]
          rw [div_lt_iff₀ hε'] at hN
          nlinarith
        simp only [hβdef, bp_eq_zero hδ j (hle.trans hfr), mul_zero])
      (fun m => ⟪v, f m⟫_ℂ) (continuousOn_const.inner hf.1.continuousOn)
    refine hw.congr fun j => ?_
    show _ = ip μ (sec E (β j) v) f
    rw [ip_sec μ (hβc j) (hβcs j) (hβG j) v hf, ← integral_smul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    exact mul_smul _ _ _

end GlobalTheory.CompanionTheory.ApproxK
