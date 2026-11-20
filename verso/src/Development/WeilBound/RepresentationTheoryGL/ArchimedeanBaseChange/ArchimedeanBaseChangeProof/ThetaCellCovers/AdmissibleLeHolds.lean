import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.ThetaBasic
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SquareIntegrableCovers.SetLIntegralLeOfCover
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CuspRep.CuspidalL2GL PositivityTheory.Rg.BcB.D1
open GroundTheory.Automorphic.Reduction
open scoped ENNReal Pointwise

namespace PositivityTheory.Rg.BcB.E1

/- English proof (translation)
Introduce `n t₀ x ht h i j hij`. Establish `key : ∀ k : ℕ, ∀ hk : i.1 + k < n, x ⟨i.1 + k, hk⟩ ≤ x i + k * t₀`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro hk`.

Simplify using the standard rewrite rules. Consider the case `succ k ih`. Introduce `hk`. Establish `h1` using `h (i.1 + k + 1)`. Unfold `An.sr at h1`.

Rewrite `h1` using `[dif_pos ⟨by omega, by omega⟩]`. Establish `h2` using `ih (by omega)`. Establish `e : (⟨i.1 + k + 1 - 1, by omega⟩ : Fin n) = ⟨i.1 + k, by omega⟩` using `Fin.ext (by simp)`. Rewrite `h1` using `[e]`. Use `push_cast`.

Establish `e2 : x ⟨i.1 + (k + 1), hk⟩ = x ⟨i.1 + k + 1, by omega⟩` using `rfl`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hij' : i.1 ≤ j.1` using `hij`. Establish `h3` using `key (j.1 - i.1) (by omega)`. Establish `e : (⟨i.1 + (j.1 - i.1), by omega⟩ : Fin n) = j` using `Fin.ext (by simp only; omega)`.

Rewrite `h3` using `[e]`. Establish `h4 : ((j.1 - i.1 : ℕ) : ℝ) ≤ n` using `by exact_mod_cast (by omega : j.1 - i.1 ≤ n)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem admissible_le_holds : AdmLe := by
  intro n t₀ x ht h i j hij
  have key : ∀ k : ℕ, ∀ hk : i.1 + k < n, x ⟨i.1 + k, hk⟩ ≤ x i + k * t₀ := by
    intro k
    induction k with
    | zero => intro hk; simp
    | succ k ih =>
      intro hk
      have h1 := h (i.1 + k + 1)
      unfold An.sr at h1
      rw [dif_pos ⟨by omega, by omega⟩] at h1
      have h2 := ih (by omega)
      have e : (⟨i.1 + k + 1 - 1, by omega⟩ : Fin n) = ⟨i.1 + k, by omega⟩ := Fin.ext (by simp)
      rw [e] at h1
      push_cast
      have e2 : x ⟨i.1 + (k + 1), hk⟩ = x ⟨i.1 + k + 1, by omega⟩ := rfl
      linarith
  have hij' : i.1 ≤ j.1 := hij
  have h3 := key (j.1 - i.1) (by omega)
  have e : (⟨i.1 + (j.1 - i.1), by omega⟩ : Fin n) = j := Fin.ext (by simp only; omega)
  rw [e] at h3
  have h4 : ((j.1 - i.1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : j.1 - i.1 ≤ n)
  nlinarith

/- English proof (translation)
Introduce `E _ _ _ n`. Take `⟨ω, hω, hωB, t, ht, hsieg⟩` from `exists_siegelSet (K := E) n`. Use `⟨ω, max 0 (-Real.log t), ⟨hω, hωB⟩, le_max_left _ _, fun g => ?_⟩` and prove the remaining obligations. Take `⟨γ, b, hb, _, ⟨r, hr, hratio, rfl⟩, k, hk, hg⟩` from `hsieg g`. Establish `ha : diagUnits n (fun i => posIdele (K` using `E) (r i) (hr i)) = An.tor E fun i => Real.log (r i) := by`.

Unfold `An.tor`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `JSqIntGlue.posIdele_congr (Real.exp_log (hr i)).symm _ _`. Use `⟨γ, b, hb, fun i => Real.log (r i), fun r' => ?_, k, hk, ha ▸ hg⟩` and prove the remaining obligations.

Unfold `An.sr`. Use `split_ifs with h`. Establish `h1` using `hratio ⟨r' - 1, by omega⟩ ⟨r', h.2⟩ (by simp only; omega)`. Establish `h2` using `Real.log_le_log (mul_pos ht (hr _)) h1`. Rewrite `h2` using `[Real.log_mul ht.ne' (hr _).ne']`.

Use `le_max_right 0 (-Real.log t)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `le_max_left 0 (-Real.log t)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cover_holds : Cover := by
  intro E _ _ _ n
  obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := exists_siegelSet (K := E) n
  refine ⟨ω, max 0 (-Real.log t), ⟨hω, hωB⟩, le_max_left _ _, fun g => ?_⟩
  obtain ⟨γ, b, hb, _, ⟨r, hr, hratio, rfl⟩, k, hk, hg⟩ := hsieg g
  have ha : diagUnits n (fun i => posIdele (K := E) (r i) (hr i)) = An.tor E fun i => Real.log (r i) := by
    unfold An.tor
    congr 1
    funext i
    exact JSqIntGlue.posIdele_congr (Real.exp_log (hr i)).symm _ _
  refine ⟨γ, b, hb, fun i => Real.log (r i), fun r' => ?_, k, hk, ha ▸ hg⟩
  unfold An.sr
  split_ifs with h
  · have h1 := hratio ⟨r' - 1, by omega⟩ ⟨r', h.2⟩ (by simp only; omega)
    have h2 := Real.log_le_log (mul_pos ht (hr _)) h1
    rw [Real.log_mul ht.ne' (hr _).ne'] at h2
    have := le_max_right 0 (-Real.log t)
    linarith
  · have := le_max_left 0 (-Real.log t); linarith

/- English proof (translation)
Introduce `E _ _ _ n`. Take `⟨ω, t₀, hω, ht, hc⟩` from `h1 E n`. Take `⟨ω', hω', hj⟩` from `h2 E n ω t₀ hω ht`. Use `⟨(fun p : (Fin n → ℝ) × GA E n × GA E n => An.tor E p.1 * p.2.1 * p.2.2) '' (Metric.closedBall 0 1 ×ˢ ω' ×ˢ (maxCompact (K := E) (n := n) : Set _)), ?_, fun g => ?_⟩` and prove the remaining obligations. Conclude with `((isCompact_closedBall _ _).prod (hω'.prod isCompact_maxCompact)).image (((JSqIntGlue.continuous_tor.comp continuous_fst).mul continuous_snd.fst).mul continuous_snd.snd)`.

Take `⟨γ, b, hb, x, hx, k, hk, e⟩` from `hc g`. Use `⟨γ, fun i => ⌊x i⌋, _, ⟨(fun i => Int.fract (x i), _, k), ⟨?_, hj b hb x hx, hk⟩, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]`. Introduce `i`. Rewrite using `[Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]`.

Conclude with `(Int.fract_lt_one _).le`. Establish `e2 : (An.tor E x : GA E n) = An.tor E (fun i => (⌊x i⌋ : ℝ)) * An.tor E (fun i => Int.fract (x i))`. Rewrite using `[← JSqIntGlue.tor_add]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Conclude with `(Int.floor_add_fract _).symm`. Rewrite using `[e]`. Simplify using `only [← mul_assoc]`. Rewrite using `[← e2, mul_inv_cancel, one_mul]`.
-/
theorem cellCover_of (h1 : Cover) (h2 : ConjCpt) : CellCover := by
  intro E _ _ _ n
  obtain ⟨ω, t₀, hω, ht, hc⟩ := h1 E n
  obtain ⟨ω', hω', hj⟩ := h2 E n ω t₀ hω ht
  refine ⟨(fun p : (Fin n → ℝ) × GA E n × GA E n => An.tor E p.1 * p.2.1 * p.2.2) ''
    (Metric.closedBall 0 1 ×ˢ ω' ×ˢ (maxCompact (K := E) (n := n) : Set _)), ?_, fun g => ?_⟩
  · exact ((isCompact_closedBall _ _).prod (hω'.prod isCompact_maxCompact)).image
      (((JSqIntGlue.continuous_tor.comp continuous_fst).mul continuous_snd.fst).mul continuous_snd.snd)
  · obtain ⟨γ, b, hb, x, hx, k, hk, e⟩ := hc g
    refine ⟨γ, fun i => ⌊x i⌋, _, ⟨(fun i => Int.fract (x i), _, k), ⟨?_, hj b hb x hx, hk⟩, rfl⟩, ?_⟩
    · rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      rw [Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
      exact (Int.fract_lt_one _).le
    · have e2 : (An.tor E x : GA E n) = An.tor E (fun i => (⌊x i⌋ : ℝ)) * An.tor E (fun i => Int.fract (x i)) := by
        rw [← JSqIntGlue.tor_add]
        congr 1
        funext i
        exact (Int.floor_add_fract _).symm
      rw [e]
      simp only [← mul_assoc]
      rw [← e2, mul_inv_cancel, one_mul]

/- English proof (translation)
The claim follows from `DiscreteTopology.of_continuous_injective (β := latticeGL E n) (f := Subgroup.inclusion le_sup_left) (continuous_subtype_val.subtype_mk _) (Subgroup.inclusion_injective _)`.
-/
theorem discrete_range (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) :
    DiscreteTopology (ratGL E n).range :=
  DiscreteTopology.of_continuous_injective (β := latticeGL E n) (f := Subgroup.inclusion le_sup_left)
    (continuous_subtype_val.subtype_mk _) (Subgroup.inclusion_injective _)

/- English proof (translation)
Introduce `E _ _ _ n _ _ μ`. Use `discrete_range E n` as an intermediate fact. Conclude with `⟨_, GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom _ μ⟩`.
-/
theorem domEx_holds : DomEx := by
  intro E _ _ _ n _ _ μ
  have := discrete_range E n
  exact ⟨_, GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom _ μ⟩

/- English proof (translation)
Introduce `E _ _ _ n`. Establish `hi : Function.Injective (ratGL E n)` using `fun a b h => Units.ext <| Matrix.ext fun i j => AdeleRing.algebraMap_injective (𝓞 E) E (congrArg (fun g : GA E n => g.val i j) h)`. Use `discrete_range E n` as an intermediate fact. Use `⟨hi, (MonoidHom.ofInjective hi).injective.countable, fun C hC => ?_⟩` and prove the remaining obligations. Conclude with `(GlobalTheory.AutomorphicL2Unitary.finite_mem_compact (Γ := (ratGL E n).range) hC).preimage (f := MonoidHom.ofInjective hi) (MonoidHom.ofInjective hi).injective.injOn`.
-/
theorem ratProper_holds : RatProper := by
  intro E _ _ _ n
  have hi : Function.Injective (ratGL E n) := fun a b h => Units.ext <| Matrix.ext fun i j =>
    AdeleRing.algebraMap_injective (𝓞 E) E (congrArg (fun g : GA E n => g.val i j) h)
  have := discrete_range E n
  refine ⟨hi, (MonoidHom.ofInjective hi).injective.countable, fun C hC => ?_⟩
  exact (GlobalTheory.AutomorphicL2Unitary.finite_mem_compact (Γ := (ratGL E n).range) hC).preimage
    (f := MonoidHom.ofInjective hi) (MonoidHom.ofInjective hi).injective.injOn

/- English proof (translation)
Use `eq_top_iff.2 fun v _ => ⟨(g⁻¹).val *ᵥ v, trivial, ?_⟩` and prove the remaining obligations. Simplify using `[Matrix.mulVec_mulVec]`.
-/
theorem img_top {K : Type} [Field K] {n : ℕ} (g : GL (Fin n) K) : img g ⊤ = ⊤ := by
  refine eq_top_iff.2 fun v _ => ⟨(g⁻¹).val *ᵥ v, trivial, ?_⟩
  simp [Matrix.mulVec_mulVec]

/- English proof (translation)
Unfold `img`. Rewrite using `[← Submodule.map_comp, ← Matrix.toLin'_mul, Units.mul_inv, Matrix.toLin'_one, Submodule.map_id]`.
-/
theorem img_img_inv {K : Type} [Field K] {n : ℕ} (g : GL (Fin n) K) (W : Submodule K (Fin n → K)) :
    img g (img g⁻¹ W) = W := by
  unfold img
  rw [← Submodule.map_comp, ← Matrix.toLin'_mul, Units.mul_inv, Matrix.toLin'_one, Submodule.map_id]

/- English proof (translation)
Use `le_antisymm (Submodule.finrank_map_le _ _) ?_` and prove the remaining obligations. Use `conv_lhs => rw [← img_img_inv g⁻¹ W, inv_inv]`. Conclude with `Submodule.finrank_map_le _ _`.
-/
theorem finrank_img {K : Type} [Field K] {n : ℕ} (g : GL (Fin n) K) (W : Submodule K (Fin n → K)) :
    Module.finrank K (img g W) = Module.finrank K W := by
  refine le_antisymm (Submodule.finrank_map_le _ _) ?_
  conv_lhs => rw [← img_img_inv g⁻¹ W, inv_inv]
  exact Submodule.finrank_map_le _ _

/- English proof (translation)
Introduce `E _ _ _ n Ω₀ hΩ`. Take `⟨C, hC⟩` from `h E n Ω₀ hΩ`. Use `⟨(n + 1) * (1 + |C|), by positivity, fun x o ho σ hσ h1 h2 => ?_⟩` and prove the remaining obligations. Take `⟨a1, a2⟩` from `hC x o ho`. Establish `hd : (1 : ℝ) ≤ Module.finrank ℚ E` using `by exact_mod_cast Module.finrank_pos`.

Establish `hc` using `le_abs_self C`. Establish `hc0` using `abs_nonneg C`. Establish `b1 : ∀ i, x i ≤ σ + |C|` using `fun i => by`. Use `h1 _ (finrank_span_singleton (v := (Pi.single i 1 : Fin n → E)) (by simp))` as an intermediate fact. Use `(abs_le.1 (a1 i)).1` as an intermediate fact.

Assume the negation of the conclusion as `hn`. Use the polynomial consequences of the given equalities and inequalities. Establish `b2 : -(σ + |C|) ≤ ∑ i, x i`. Use `(abs_le.1 a2).2` as an intermediate fact. Assume the negation of the conclusion as `hn`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hn : (0 : ℝ) ≤ n` using `Nat.cast_nonneg n`. Rewrite using `[pi_norm_le_iff_of_nonneg (by positivity)]`. Introduce `i`. Establish `b3 : ∑ j, (σ + |C| - x j) = n * (σ + |C|) - ∑ j, x j` using `by simp [Finset.sum_sub_distrib, mul_add]`.

Establish `b4` using `Finset.single_le_sum (f := fun j => σ + |C| - x j) (fun j _ => sub_nonneg.2 (b1 j)) (Finset.mem_univ i)`. Establish `b5 : (n + 1) * (σ + |C|) ≤ (n + 1) * (1 + |C|) * (1 + σ)`. Rewrite using `[mul_assoc]; exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)`. Rewrite using `[Real.norm_eq_abs, abs_le]`. Apply the tactic sequence `constructor <;> nlinarith [b1 i]`.
-/
theorem cutBox_of (h : DegCell) : CutBox := by
  intro E _ _ _ n Ω₀ hΩ
  obtain ⟨C, hC⟩ := h E n Ω₀ hΩ
  refine ⟨(n + 1) * (1 + |C|), by positivity, fun x o ho σ hσ h1 h2 => ?_⟩
  obtain ⟨a1, a2⟩ := hC x o ho
  have hd : (1 : ℝ) ≤ Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  have hc := le_abs_self C
  have hc0 := abs_nonneg C
  have b1 : ∀ i, x i ≤ σ + |C| := fun i => by
    have := h1 _ (finrank_span_singleton (v := (Pi.single i 1 : Fin n → E)) (by simp))
    have := (abs_le.1 (a1 i)).1
    by_contra hn
    nlinarith
  have b2 : -(σ + |C|) ≤ ∑ i, x i := by
    have := (abs_le.1 a2).2
    by_contra hn
    nlinarith
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  have b3 : ∑ j, (σ + |C| - x j) = n * (σ + |C|) - ∑ j, x j := by simp [Finset.sum_sub_distrib, mul_add]
  have b4 := Finset.single_le_sum (f := fun j => σ + |C| - x j) (fun j _ => sub_nonneg.2 (b1 j)) (Finset.mem_univ i)
  have b5 : (n + 1) * (σ + |C|) ≤ (n + 1) * (1 + |C|) * (1 + σ) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith [b1 i]

/- English proof (translation)
Introduce `E _ _ _ n`. Take `⟨Ω₀, hΩ, hc⟩` from `h2 E n`. Take `⟨C, hC0, hC⟩` from `h3 E n Ω₀ hΩ`. Take `⟨C', hC0', hC'⟩` from `h5 E n Ω₀ hΩ`. Use `⟨C' * (1 + C * (2 * n + 1)), by positivity, fun τ hτ g hg => ?_⟩` and prove the remaining obligations.

Take `⟨γ, m, o, ho, e⟩` from `hc g`. Establish `hn : (0 : ℝ) ≤ n` using `Nat.cast_nonneg n`. Establish `a` using `hC (fun i => (m i : ℝ)) o ho ((2 * n + 1) * τ) (by positivity) (fun W hW => by`. Rewrite using `[← e, ← img_img_inv γ W, h1]`. Use `(hg.1 _).trans ?_` and prove the remaining obligations.

Rewrite using `[finrank_img, hW, prof]`. Use `push_cast`. Use the proof step `nlinarith) (by`. Rewrite using `[← e, ← img_top γ, h1]`. Use polynomial arithmetic with `[hg.2])`.

Rewrite using `[← (h4 E n).1 γ g, e]`. Use `(hC' _ o ho).2.trans ?_` and prove the remaining obligations. Rewrite using `[mul_assoc]`. Use `mul_le_mul_of_nonneg_left ?_ hC0'` and prove the remaining obligations. Establish `: 0 ≤ C * n` using `by positivity`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem cutRed_of (h1 : DegRat) (h2 : CellCover) (h3 : CutBox) (h4 : RedBasic) (h5 : RedCell) : CutRed := by
  intro E _ _ _ n
  obtain ⟨Ω₀, hΩ, hc⟩ := h2 E n
  obtain ⟨C, hC0, hC⟩ := h3 E n Ω₀ hΩ
  obtain ⟨C', hC0', hC'⟩ := h5 E n Ω₀ hΩ
  refine ⟨C' * (1 + C * (2 * n + 1)), by positivity, fun τ hτ g hg => ?_⟩
  obtain ⟨γ, m, o, ho, e⟩ := hc g
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have a := hC (fun i => (m i : ℝ)) o ho ((2 * n + 1) * τ) (by positivity) (fun W hW => by
    rw [← e, ← img_img_inv γ W, h1]
    refine (hg.1 _).trans ?_
    rw [finrank_img, hW, prof]
    push_cast
    nlinarith) (by
    rw [← e, ← img_top γ, h1]
    nlinarith [hg.2])
  rw [← (h4 E n).1 γ g, e]
  refine (hC' _ o ho).2.trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hC0'
  have : 0 ≤ C * n := by positivity
  nlinarith

/- English proof (translation)
Introduce `E _ _ _ n`. Establish `h0 : ∀ A : Matrix (Fin n) (Fin n) (Ad E), 0 ≤ logSizeM A` using `fun A => add_nonneg (Finset.sum_nonneg fun _ _ => Real.posLog_nonneg) (finsum_nonneg fun _ => Real.posLog_nonneg)`. Establish `h0' : ∀ g : GA E n, 0 ≤ logSize g` using `fun g => add_nonneg (h0 _) (h0 _)`. Use `⟨fun γ g => ?_, fun g => ⟨le_ciInf fun _ => h0' _, ?_⟩, ?_⟩` and prove the remaining obligations. Unfold `red`.

Rewrite using `[← (Equiv.mulRight γ).iInf_comp (g := fun δ => logSize (ratGL E n δ * g))]`. Simplify using `[mul_assoc]`. Use `(ciInf_le ⟨0, ?_⟩ 1).trans (by simp)` and prove the remaining obligations. Introduce and unpack `_ ⟨γ, rfl⟩`. Conclude with `h0' _`.

Use `(h1 E n).2.1` as an intermediate fact. Conclude with `Measurable.iInf fun γ => ((h2 E n).comp (continuous_const.mul continuous_id)).measurable`.
-/
theorem redBasic_of (h1 : RatProper) (h2 : SizeCont) : RedBasic := by
  intro E _ _ _ n
  have h0 : ∀ A : Matrix (Fin n) (Fin n) (Ad E), 0 ≤ logSizeM A := fun A =>
    add_nonneg (Finset.sum_nonneg fun _ _ => Real.posLog_nonneg) (finsum_nonneg fun _ => Real.posLog_nonneg)
  have h0' : ∀ g : GA E n, 0 ≤ logSize g := fun g => add_nonneg (h0 _) (h0 _)
  refine ⟨fun γ g => ?_, fun g => ⟨le_ciInf fun _ => h0' _, ?_⟩, ?_⟩
  · unfold red
    rw [← (Equiv.mulRight γ).iInf_comp (g := fun δ => logSize (ratGL E n δ * g))]
    simp [mul_assoc]
  · refine (ciInf_le ⟨0, ?_⟩ 1).trans (by simp)
    rintro _ ⟨γ, rfl⟩
    exact h0' _
  · have := (h1 E n).2.1
    exact Measurable.iInf fun γ => ((h2 E n).comp (continuous_const.mul continuous_id)).measurable

/- English proof (translation)
Introduce `E _ _ _ n`. Use `⟨Units.continuous_iff.2 ⟨?_, ?_⟩, fun g => ?_, fun γ => ?_⟩` and prove the remaining obligations. Conclude with `(Units.continuous_coe_inv.matrix_map GlobalTheory.ThetaPull.continuous_conjAd).matrix_transpose`. Conclude with `(Units.continuous_val.matrix_map GlobalTheory.ThetaPull.continuous_conjAd).matrix_transpose`. Conclude with `Units.ext (Matrix.ext fun i j => GlobalTheory.ThetaPull.conjAd_conjAd _)`.

Conclude with `Units.ext (Matrix.ext fun i j => conjAd_algebraMap _)`.
-/
theorem thetaBasic_holds : ThetaBasic := by
  intro E _ _ _ n
  refine ⟨Units.continuous_iff.2 ⟨?_, ?_⟩, fun g => ?_, fun γ => ?_⟩
  · exact (Units.continuous_coe_inv.matrix_map GlobalTheory.ThetaPull.continuous_conjAd).matrix_transpose
  · exact (Units.continuous_val.matrix_map GlobalTheory.ThetaPull.continuous_conjAd).matrix_transpose
  · exact Units.ext (Matrix.ext fun i j => GlobalTheory.ThetaPull.conjAd_conjAd _)
  · exact Units.ext (Matrix.ext fun i j => conjAd_algebraMap _)

end PositivityTheory.Rg.BcB.E1

end
