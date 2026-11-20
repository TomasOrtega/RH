import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FirstMin

/- English proof (translation)
Establish `hb : BddBelow (Set.range f)` using `⟨0, by rintro _ ⟨s, rfl⟩; exact hf s⟩`. Establish `key : sInf (Set.range f) / c ≤ sInf (Set.range h)`. Apply `le_csInf (Set.range_nonempty h)` to reduce the goal to its premises. Introduce and unpack `_ ⟨s, rfl⟩`. Rewrite using `[div_le_iff₀' hc]`.

Conclude with `(csInf_le hb ⟨s, rfl⟩).trans (hle s)`. Rewrite `key` using `[div_le_iff₀' hc]`. Then use the resulting hypothesis.
-/
theorem sInf_range_le_mul {S : Type} [Nonempty S] (f h : S → ℝ) (hf : ∀ s, 0 ≤ f s) (c : ℝ) (hc : 0 < c)
    (hle : ∀ s, f s ≤ c * h s) : sInf (Set.range f) ≤ c * sInf (Set.range h) := by
  have hb : BddBelow (Set.range f) := ⟨0, by rintro _ ⟨s, rfl⟩; exact hf s⟩
  have key : sInf (Set.range f) / c ≤ sInf (Set.range h) := by
    apply le_csInf (Set.range_nonempty h)
    rintro _ ⟨s, rfl⟩
    rw [div_le_iff₀' hc]
    exact (csInf_le hb ⟨s, rfl⟩).trans (hle s)
  rwa [div_le_iff₀' hc] at key

/- English proof (translation)
Establish `hK : IsCompact (Metric.sphere (0 : ι → ℝ) 1)` using `isCompact_sphere _ _`. Establish `hQ0 : Continuous fun p : X × (ι → ℝ) => Q x₀ p.2` using `hQ.comp (continuous_const.prodMk continuous_snd)`. Establish `hev : ∀ᶠ x in 𝓝 x₀, ∀ a ∈ Metric.sphere (0 : ι → ℝ) 1, (1 - δ) ^ 2 * Q x₀ a < Q x a ∧ Q x a < (1 + δ) ^ 2 * Q x₀ a`. Apply `hK.eventually_forall_of_forall_eventually` to reduce the goal to its premises. Introduce `a ha`.

Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Simplify using `at ha`. Establish `hp` using `hpos x₀ a ha0`. Establish `hl : (1 - δ) ^ 2 < 1` using `by nlinarith`.

Establish `hu : 1 < (1 + δ) ^ 2` using `by nlinarith`. Establish `h1 : (1 - δ) ^ 2 * Q x₀ a < Q x₀ a` using `by nlinarith`. Establish `h2 : Q x₀ a < (1 + δ) ^ 2 * Q x₀ a` using `by nlinarith`. Conclude with `((isOpen_lt (continuous_const.mul hQ0) hQ).inter (isOpen_lt hQ (continuous_const.mul hQ0))).mem_nhds ⟨h1, h2⟩`. Use `filter_upwards [hev] with x hx a ha`.

Establish `hn : 0 < ‖a‖` using `norm_pos_iff.mpr ha`. Establish `hu : ‖a‖⁻¹ • a ∈ Metric.sphere (0 : ι → ℝ) 1`. Rewrite using `[mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']`. Establish `hau : a = ‖a‖ • (‖a‖⁻¹ • a)`. Rewrite using `[smul_smul, mul_inv_cancel₀ hn.ne', one_smul]`.

Take `⟨h1, h2⟩` from `hx _ hu`. Establish `hn2 : 0 < ‖a‖ ^ 2` using `by positivity`. Rewrite using `[hau, hhom x, hhom x₀]`. Generalize the expression as in `‖a‖⁻¹ • a = u at h1 h2`. Prove the components needed by the constructor for the conclusion.

Use polynomial arithmetic with `[mul_lt_mul_of_pos_left h1 hn2]`. Use polynomial arithmetic with `[mul_lt_mul_of_pos_left h2 hn2]`.
-/
theorem eventually_form_comparison {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (Q : X → (ι → ℝ) → ℝ) (hQ : Continuous fun p : X × (ι → ℝ) => Q p.1 p.2)
    (hhom : ∀ x (r : ℝ) a, Q x (r • a) = r ^ 2 * Q x a)
    (hpos : ∀ x a, a ≠ 0 → 0 < Q x a) (x₀ : X) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∀ᶠ x in 𝓝 x₀, ∀ a, a ≠ 0 → (1 - δ) ^ 2 * Q x₀ a ≤ Q x a ∧ Q x a ≤ (1 + δ) ^ 2 * Q x₀ a := by
  have hK : IsCompact (Metric.sphere (0 : ι → ℝ) 1) := isCompact_sphere _ _
  have hQ0 : Continuous fun p : X × (ι → ℝ) => Q x₀ p.2 :=
    hQ.comp (continuous_const.prodMk continuous_snd)
  have hev : ∀ᶠ x in 𝓝 x₀, ∀ a ∈ Metric.sphere (0 : ι → ℝ) 1,
      (1 - δ) ^ 2 * Q x₀ a < Q x a ∧ Q x a < (1 + δ) ^ 2 * Q x₀ a := by
    apply hK.eventually_forall_of_forall_eventually
    intro a ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at ha
    have hp := hpos x₀ a ha0
    have hl : (1 - δ) ^ 2 < 1 := by nlinarith
    have hu : 1 < (1 + δ) ^ 2 := by nlinarith
    have h1 : (1 - δ) ^ 2 * Q x₀ a < Q x₀ a := by nlinarith
    have h2 : Q x₀ a < (1 + δ) ^ 2 * Q x₀ a := by nlinarith
    exact ((isOpen_lt (continuous_const.mul hQ0) hQ).inter
      (isOpen_lt hQ (continuous_const.mul hQ0))).mem_nhds ⟨h1, h2⟩
  filter_upwards [hev] with x hx a ha
  have hn : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hu : ‖a‖⁻¹ • a ∈ Metric.sphere (0 : ι → ℝ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have hau : a = ‖a‖ • (‖a‖⁻¹ • a) := by
    rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  obtain ⟨h1, h2⟩ := hx _ hu
  have hn2 : 0 < ‖a‖ ^ 2 := by positivity
  rw [hau, hhom x, hhom x₀]
  generalize ‖a‖⁻¹ • a = u at h1 h2
  constructor
  · nlinarith [mul_lt_mul_of_pos_left h1 hn2]
  · nlinarith [mul_lt_mul_of_pos_left h2 hn2]

/- English proof (translation)
Break down `isEmpty_or_nonempty S with hS | hS` into its components or cases. Simplify using `only [Set.range_eq_empty]`. Conclude with `continuous_const`. Rewrite using `[continuous_iff_continuousAt]`. Introduce `x₀`.

Rewrite using `[Metric.continuousAt_iff']`. Introduce `ε hε`. Use `set m := sInf (Set.range fun s => Real.sqrt (Q x₀ (c s))) with hm`. Establish `hm0 : 0 ≤ m` using `Real.sInf_nonneg (by rintro _ ⟨s, rfl⟩; exact Real.sqrt_nonneg _)`. Choose the witnesses or unpack the hypotheses as in `⟨δ, hδ, hδ1, hδm⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ δ * m < ε := by`.

Use `⟨min (1 / 2) (ε / (2 * (m + 1))), by positivity, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(min_le_left _ _).trans_lt (by norm_num)`. Establish `h1 : min (1 / 2) (ε / (2 * (m + 1))) ≤ ε / (2 * (m + 1))` using `min_le_right _ _`. Establish `h2 : ε / (2 * (m + 1)) * m < ε`. Rewrite using `[div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]`.

Use the polynomial consequences of the given equalities and inequalities. Conclude with `(mul_le_mul_of_nonneg_right h1 hm0).trans_lt h2`. Use `filter_upwards [eventually_form_comparison Q hQ hhom hpos x₀ δ hδ hδ1] with x hx`. Establish `hlow : ∀ s, Real.sqrt (Q x₀ (c s)) ≤ (1 - δ)⁻¹ * Real.sqrt (Q x (c s))`. Introduce `s`.

Establish `h1 : 0 < 1 - δ` using `by linarith`. Rewrite using `[inv_mul_eq_div, le_div_iff₀' h1]`. Use `Real.sqrt_le_sqrt (hx _ (hc s)).1` as an intermediate fact. Rewrite `this` using `[Real.sqrt_mul (by positivity), Real.sqrt_sq h1.le]`. Then use the resulting hypothesis. Establish `hup : ∀ s, Real.sqrt (Q x (c s)) ≤ (1 + δ) * Real.sqrt (Q x₀ (c s))`.

Introduce `s`. Establish `h1 : 0 < 1 + δ` using `by linarith`. Use `Real.sqrt_le_sqrt (hx _ (hc s)).2` as an intermediate fact. Rewrite `this` using `[Real.sqrt_mul (by positivity), Real.sqrt_sq h1.le]`. Then use the resulting hypothesis. Establish `hA` using `sInf_range_le_mul _ _ (fun s => Real.sqrt_nonneg _) _ (inv_pos.mpr (by linarith : 0 < 1 - δ)) hlow`.

Establish `hB` using `sInf_range_le_mul _ _ (fun s => Real.sqrt_nonneg _) _ (by linarith : 0 < 1 + δ) hup`. Rewrite `hA`, `hB` using `[← hm]`. Use `set l := sInf (Set.range fun s => Real.sqrt (Q x (c s))) with hl`. Establish `hA' : (1 - δ) * m ≤ l`. Establish `h1 : 0 < 1 - δ` using `by linarith`.

Rewrite `hA` using `[inv_mul_eq_div, le_div_iff₀' h1]`. Conclude with `hA`. Rewrite using `[Real.dist_eq, abs_lt]`. Apply the tactic sequence `constructor <;> nlinarith`.
-/
theorem continuous_sInf_sqrt_form {X ι S : Type} [TopologicalSpace X] [Fintype ι]
    (Q : X → (ι → ℝ) → ℝ) (hQ : Continuous fun p : X × (ι → ℝ) => Q p.1 p.2)
    (hhom : ∀ x (r : ℝ) a, Q x (r • a) = r ^ 2 * Q x a)
    (hpos : ∀ x a, a ≠ 0 → 0 < Q x a) (c : S → ι → ℝ) (hc : ∀ s, c s ≠ 0) :
    Continuous fun x => sInf (Set.range fun s => Real.sqrt (Q x (c s))) := by
  rcases isEmpty_or_nonempty S with hS | hS
  · simp only [Set.range_eq_empty]
    exact continuous_const
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [Metric.continuousAt_iff']
  intro ε hε
  set m := sInf (Set.range fun s => Real.sqrt (Q x₀ (c s))) with hm
  have hm0 : 0 ≤ m := Real.sInf_nonneg (by rintro _ ⟨s, rfl⟩; exact Real.sqrt_nonneg _)
  obtain ⟨δ, hδ, hδ1, hδm⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ δ * m < ε := by
    refine ⟨min (1 / 2) (ε / (2 * (m + 1))), by positivity, ?_, ?_⟩
    · exact (min_le_left _ _).trans_lt (by norm_num)
    · have h1 : min (1 / 2) (ε / (2 * (m + 1))) ≤ ε / (2 * (m + 1)) := min_le_right _ _
      have h2 : ε / (2 * (m + 1)) * m < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
      exact (mul_le_mul_of_nonneg_right h1 hm0).trans_lt h2
  filter_upwards [eventually_form_comparison Q hQ hhom hpos x₀ δ hδ hδ1] with x hx
  have hlow : ∀ s, Real.sqrt (Q x₀ (c s)) ≤ (1 - δ)⁻¹ * Real.sqrt (Q x (c s)) := by
    intro s
    have h1 : 0 < 1 - δ := by linarith
    rw [inv_mul_eq_div, le_div_iff₀' h1]
    have := Real.sqrt_le_sqrt (hx _ (hc s)).1
    rwa [Real.sqrt_mul (by positivity), Real.sqrt_sq h1.le] at this
  have hup : ∀ s, Real.sqrt (Q x (c s)) ≤ (1 + δ) * Real.sqrt (Q x₀ (c s)) := by
    intro s
    have h1 : 0 < 1 + δ := by linarith
    have := Real.sqrt_le_sqrt (hx _ (hc s)).2
    rwa [Real.sqrt_mul (by positivity), Real.sqrt_sq h1.le] at this
  have hA := sInf_range_le_mul _ _ (fun s => Real.sqrt_nonneg _) _
    (inv_pos.mpr (by linarith : 0 < 1 - δ)) hlow
  have hB := sInf_range_le_mul _ _ (fun s => Real.sqrt_nonneg _) _ (by linarith : 0 < 1 + δ) hup
  rw [← hm] at hA hB
  set l := sInf (Set.range fun s => Real.sqrt (Q x (c s))) with hl
  have hA' : (1 - δ) * m ≤ l := by
    have h1 : 0 < 1 - δ := by linarith
    rw [inv_mul_eq_div, le_div_iff₀' h1] at hA
    exact hA
  rw [Real.dist_eq, abs_lt]
  constructor <;> nlinarith

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

/- English proof (translation)
Establish `hspan : Submodule.span ℝ (Set.range R.P) = ⊤` using `(GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit R).2.1`. Establish `htop : ⊤ ≤ Submodule.span ℝ (Set.range fun i => R.P (b i))`. Rewrite using `[← hspan, Submodule.span_le]`. Introduce and unpack `_ ⟨v, rfl⟩`. Rewrite using `[← b.sum_repr v, map_sum]`.

Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, ← Int.cast_smul_eq_zsmul ℝ]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Use `linearIndependent_of_top_le_span_of_card_eq_finrank htop ?_` and prove the remaining obligations. Establish `h1 : Fintype.card ι = 2 * g`.

Rewrite using `[← R.rank, Module.finrank_eq_card_basis b]`. Establish `h2 : Module.finrank ℝ (Fin g → ℂ) = 2 * g`. Simplify using `[Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]`. Rewrite using `[h1, h2]`.
-/
theorem linearIndependent_periods (R : RiemLat E g Λ) {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ Λ) :
    LinearIndependent ℝ fun i => R.P (b i) := by
  have hspan : Submodule.span ℝ (Set.range R.P) = ⊤ := (GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit R).2.1
  have htop : ⊤ ≤ Submodule.span ℝ (Set.range fun i => R.P (b i)) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    rw [← b.sum_repr v, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℝ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine linearIndependent_of_top_le_span_of_card_eq_finrank htop ?_
  have h1 : Fintype.card ι = 2 * g := by
    rw [← R.rank, Module.finrank_eq_card_basis b]
  have h2 : Module.finrank ℝ (Fin g → ℂ) = 2 * g := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]
  rw [h1, h2]

def comb (R : RiemLat E g Λ) {ι : Type} [Fintype ι] (b : ι → Λ) (a : ι → ℝ) : Fin g → ℂ :=
  ∑ i, ((a i : ℝ) : ℂ) • R.P (b i)

/- English proof (translation)
Use `conv_rhs => rw [← b.sum_repr v, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, ← Int.cast_smul_eq_zsmul ℂ]`. Simplify using the standard rewrite rules.
-/
theorem comb_repr (R : RiemLat E g Λ) {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ Λ) (v : Λ) :
    comb R b (fun i => ((b.repr v i : ℤ) : ℝ)) = R.P v := by
  conv_rhs => rw [← b.sum_repr v, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℂ]
  simp

/- English proof (translation)
Introduce `h0`. Apply `ha` to reduce the goal to its premises. Establish `hli` using `linearIndependent_periods R b`. Establish `h1 : ∑ i, a i • R.P (b i) = 0`. Rewrite using `[← h0]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use extensionality with `j`. Simplify using the standard rewrite rules. Use function extensionality and compare the values at `i`. Conclude with `Fintype.linearIndependent_iff.mp hli a h1 i`.
-/
theorem comb_ne_zero (R : RiemLat E g Λ) {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ Λ) (a : ι → ℝ)
    (ha : a ≠ 0) : comb R b a ≠ 0 := by
  intro h0
  apply ha
  have hli := linearIndependent_periods R b
  have h1 : ∑ i, a i • R.P (b i) = 0 := by
    rw [← h0]
    refine Finset.sum_congr rfl fun i _ => ?_
    ext j
    simp
  funext i
  exact Fintype.linearIndependent_iff.mp hli a h1 i

end GlobalTheory.CompanionTheory.Ar.Cusp.FirstMin

open GlobalTheory.CompanionTheory.Ar.Cusp.FirstMin in

/- English proof (translation)
Introduce `E _ _ _ g Λ _ _ X _ R hP hH`. Break down `isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩` into its components or cases. Conclude with `continuous_of_const fun x => hX.elim x`. Use `haveI := (R x₀).free`. Use `haveI := (R x₀).fin`.

Set `b` to `Module.Free.chooseBasis ℤ Λ`. Set `Q : X → (Module.Free.ChooseBasisIndex ℤ Λ → ℝ) → ℝ` to `fun x a => ((R x).ip (comb (R x) b a) (comb (R x) b a)).re`. Establish `hL : Continuous fun p : X × (Module.Free.ChooseBasisIndex ℤ Λ → ℝ) => comb (R p.1) b p.2`. Unfold `comb`. Use `continuous_finset_sum _ fun i _ => ?_` and prove the remaining obligations.

Conclude with `(Complex.continuous_ofReal.comp ((continuous_apply i).comp continuous_snd)).smul ((hP (b i)).comp continuous_fst)`. Establish `hQ : Continuous fun p : X × (Module.Free.ChooseBasisIndex ℤ Λ → ℝ) => Q p.1 p.2`. Use `Complex.continuous_re.comp ?_` and prove the remaining obligations. Conclude with `hL.dotProduct ((hH.comp continuous_fst).matrix_mulVec hL.star)`. Establish `hhom : ∀ x (r : ℝ) a, Q x (r • a) = r ^ 2 * Q x a`.

Introduce `x r a`. Establish `hc : comb (R x) b (r • a) = (r : ℂ) • comb (R x) b a`. Unfold `comb`. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[smul_smul]`. Simplify using the standard rewrite rules. Simplify using `only [Q, RiemLat.ip, hc, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]`. Simplify using `[pow_two, mul_assoc]`. Establish `hpos : ∀ x a, a ≠ 0 → 0 < Q x a` using `fun x a ha => (R x).pos _ (comb_ne_zero (R x) b a ha)`.

Establish `hmain` using `continuous_sInf_sqrt_form Q hQ hhom hpos (fun (s : {v : Λ // v ≠ 0}) i => ((b.repr s.1 i : ℤ) : ℝ)) (by`. Introduce `s h0`. Apply `s.2` to reduce the goal to its premises. Apply `b.repr.injective` to reduce the goal to its premises. Use extensionality with `i`.

Use `congrFun h0 i` as an intermediate fact. Simplify using `using this)`. Use `hmain using 2 with x` and compare the differences between its conclusion and the goal. Unfold `RiemLat.lam1`. Use `congr 1`.

Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv, rfl⟩`. Use `⟨⟨v, hv⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [Q, comb_repr, RiemLat.normSq]`.

Introduce and unpack `⟨⟨v, hv⟩, rfl⟩`. Use `⟨v, hv, ?_⟩` and prove the remaining obligations. Simplify using `only [Q, comb_repr, RiemLat.normSq]`.
-/
theorem GlobalTheory.CompanionTheory.Ar.Cusp.continuous_first_minimum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (X : Type) [TopologicalSpace X] (R : X → RiemLat E g Λ), (∀ v, Continuous fun x => (R x).P v) → (Continuous fun x => (R x).Hm) → Continuous fun x => (R x).lam1 := by
  intro E _ _ _ g Λ _ _ X _ R hP hH
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · exact continuous_of_const fun x => hX.elim x
  haveI := (R x₀).free
  haveI := (R x₀).fin
  let b := Module.Free.chooseBasis ℤ Λ
  let Q : X → (Module.Free.ChooseBasisIndex ℤ Λ → ℝ) → ℝ := fun x a =>
    ((R x).ip (comb (R x) b a) (comb (R x) b a)).re
  have hL : Continuous fun p : X × (Module.Free.ChooseBasisIndex ℤ Λ → ℝ) => comb (R p.1) b p.2 := by
    unfold comb
    refine continuous_finset_sum _ fun i _ => ?_
    exact (Complex.continuous_ofReal.comp ((continuous_apply i).comp continuous_snd)).smul
      ((hP (b i)).comp continuous_fst)
  have hQ : Continuous fun p : X × (Module.Free.ChooseBasisIndex ℤ Λ → ℝ) => Q p.1 p.2 := by
    refine Complex.continuous_re.comp ?_
    exact hL.dotProduct ((hH.comp continuous_fst).matrix_mulVec hL.star)
  have hhom : ∀ x (r : ℝ) a, Q x (r • a) = r ^ 2 * Q x a := by
    intro x r a
    have hc : comb (R x) b (r • a) = (r : ℂ) • comb (R x) b a := by
      unfold comb
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul]
      simp
    simp only [Q, RiemLat.ip, hc, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
    simp [pow_two, mul_assoc]
  have hpos : ∀ x a, a ≠ 0 → 0 < Q x a := fun x a ha => (R x).pos _ (comb_ne_zero (R x) b a ha)
  have hmain := continuous_sInf_sqrt_form Q hQ hhom hpos
    (fun (s : {v : Λ // v ≠ 0}) i => ((b.repr s.1 i : ℤ) : ℝ)) (by
      intro s h0
      apply s.2
      apply b.repr.injective
      ext i
      have := congrFun h0 i
      simpa using this)
  convert hmain using 2 with x
  unfold RiemLat.lam1
  congr 1
  ext y
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨⟨v, hv⟩, ?_⟩
    simp only [Q, comb_repr, RiemLat.normSq]
  · rintro ⟨⟨v, hv⟩, rfl⟩
    refine ⟨v, hv, ?_⟩
    simp only [Q, comb_repr, RiemLat.normSq]
