import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoAF

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.ZetaAlongK

open PositivityTheory.RgEis PositivityTheory.RgEis.MG GroundTheory.Global GroundTheory.Automorphic

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Establish `h1 : SecondCountableTopology (Matrix ι ι 𝔸[k])` using `inferInstanceAs (SecondCountableTopology (ι → ι → 𝔸[k]))`. Establish `h2 : SecondCountableTopology (Matrix ι ι 𝔸[k])ᵐᵒᵖ` using `(MulOpposite.opHomeomorph (M := Matrix ι ι 𝔸[k])).symm.isEmbedding.secondCountableTopology`. Establish `h3 : SecondCountableTopology (GL ι 𝔸[k])` using `(Units.isEmbedding_embedProduct (M := Matrix ι ι 𝔸[k])).secondCountableTopology`. Use `infer_instance`.
-/
theorem firstCountable_gl : FirstCountableTopology (GL ι 𝔸[k]) := by
  have h1 : SecondCountableTopology (Matrix ι ι 𝔸[k]) :=
    inferInstanceAs (SecondCountableTopology (ι → ι → 𝔸[k]))
  have h2 : SecondCountableTopology (Matrix ι ι 𝔸[k])ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix ι ι 𝔸[k])).symm.isEmbedding.secondCountableTopology
  have h3 : SecondCountableTopology (GL ι 𝔸[k]) :=
    (Units.isEmbedding_embedProduct (M := Matrix ι ι 𝔸[k])).secondCountableTopology
  infer_instance

/- English proof (translation)
Establish `hT : ∀ x : IdeleGroup k, 0 < (IdeleGroup.ideleModule k x : ℝ)` using `fun x ↦ (IdeleGroup.ideleModule k x).2`. Use `set G : ℂ → IdeleGroup k → ℂ := fun s x ↦ F x * (χ.toIdele x : ℂ) * ((IdeleGroup.ideleModule k x : ℝ) : ℂ) ^ s with hG`. Use `set G' : ℂ → IdeleGroup k → ℂ := fun s x ↦ G s x * Complex.log (IdeleGroup.ideleModule k x : ℝ) with hG'`. Use `set bound : IdeleGroup k → ℝ := fun x ↦ (f₁ x + f₂ x) / δ with hbound`. Establish `hbound_int : Integrable bound (ideleMeasure k)` using `(i₁.add i₂).div_const δ`.

Establish `hcont' : Continuous (G' s₀)` using `(continuous_zetaIntegrand hFc χ s₀).mul ((Complex.continuous_ofReal.comp continuous_ideleModule_val).clog fun x ↦ Complex.ofReal_mem_slitPlane.2 (hT x))`. Establish `hint₀ : Integrable (G s₀) (ideleMeasure k)`. Use `i₀.mono' (continuous_zetaIntegrand hFc χ s₀).aestronglyMeasurable (Eventually.of_forall fun x ↦ ?_)` and prove the remaining obligations. Simplify using `only [hG]`. Rewrite using `[norm_zetaIntegrand]`.

Conclude with `b₀ x`. Establish `hle : ∀ x, ∀ s ∈ Metric.ball s₀ δ, ‖G' s x‖ ≤ bound x`. Introduce `x s hs`. Establish `hre : |s.re - s₀.re| < δ`. Use `(Complex.abs_re_le_norm (s - s₀)).trans_lt (mem_ball_iff_norm.1 hs)` as an intermediate fact.

Rewrite `this` using `[Complex.sub_re]`. Then use the resulting hypothesis. Establish `hnorm : ‖G' s x‖ = ‖F x‖ * ((IdeleGroup.ideleModule k x : ℝ) ^ s.re * |Real.log (IdeleGroup.ideleModule k x : ℝ)|)`. Simplify using `only [hG', hG]`. Rewrite using `[norm_mul, norm_zetaIntegrand, ← Complex.ofReal_log (hT x).le, Complex.norm_real, Real.norm_eq_abs, mul_assoc]`. Rewrite using `[hnorm]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hdiff : ∀ x, ∀ s ∈ Metric.ball s₀ δ, HasDerivAt (fun s ↦ G s x) (G' s x) s`. Introduce `x s _`. Establish `h` using `((Complex.hasStrictDerivAt_const_cpow (y := s) (Or.inl (Complex.ofReal_ne_zero.2 (hT x).ne'))).hasDerivAt).const_mul (F x * (χ.toIdele x : ℂ))`. Use `h.congr_deriv ?_` and prove the remaining obligations.

Simplify using `only [hG', hG]`. Expand and normalize the polynomial expressions, which then agree. Establish `key` using `hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ideleMeasure k) (F := G) (F' := G') (x₀ := s₀) (bound := bound) (Metric.ball_mem_nhds s₀ hδ) (Eventually.of_forall fun s ↦ (continuous_zetaIntegrand hFc χ s).aestronglyMeasurable) hint₀ hcont'.aestronglyMeasurable (Eventually …`. Conclude with `key.2.differentiableAt`.
-/
theorem differentiableAt_globalZeta_of_majorant {F : 𝔸[k] → ℂ} (hFc : Continuous F)
    (χ : HeckeCharacter k) {s₀ : ℂ} {δ : ℝ} (hδ : 0 < δ) {f₀ f₁ f₂ : IdeleGroup k → ℝ}
    (i₀ : Integrable f₀ (ideleMeasure k)) (i₁ : Integrable f₁ (ideleMeasure k))
    (i₂ : Integrable f₂ (ideleMeasure k))
    (b₀ : ∀ t : IdeleGroup k, ‖F t‖ * (IdeleGroup.ideleModule k t : ℝ) ^ s₀.re ≤ f₀ t)
    (b₁ : ∀ t : IdeleGroup k, ‖F t‖ * (IdeleGroup.ideleModule k t : ℝ) ^ (s₀.re - 2 * δ) ≤ f₁ t)
    (b₂ : ∀ t : IdeleGroup k, ‖F t‖ * (IdeleGroup.ideleModule k t : ℝ) ^ (s₀.re + 2 * δ) ≤ f₂ t) :
    DifferentiableAt ℂ (globalZeta F χ) s₀ := by
  have hT : ∀ x : IdeleGroup k, 0 < (IdeleGroup.ideleModule k x : ℝ) :=
    fun x ↦ (IdeleGroup.ideleModule k x).2
  set G : ℂ → IdeleGroup k → ℂ := fun s x ↦
    F x * (χ.toIdele x : ℂ) * ((IdeleGroup.ideleModule k x : ℝ) : ℂ) ^ s with hG
  set G' : ℂ → IdeleGroup k → ℂ :=
    fun s x ↦ G s x * Complex.log (IdeleGroup.ideleModule k x : ℝ) with hG'
  set bound : IdeleGroup k → ℝ := fun x ↦ (f₁ x + f₂ x) / δ with hbound
  have hbound_int : Integrable bound (ideleMeasure k) := (i₁.add i₂).div_const δ
  have hcont' : Continuous (G' s₀) :=
    (continuous_zetaIntegrand hFc χ s₀).mul
      ((Complex.continuous_ofReal.comp continuous_ideleModule_val).clog
        fun x ↦ Complex.ofReal_mem_slitPlane.2 (hT x))
  have hint₀ : Integrable (G s₀) (ideleMeasure k) := by
    refine i₀.mono' (continuous_zetaIntegrand hFc χ s₀).aestronglyMeasurable
      (Eventually.of_forall fun x ↦ ?_)
    simp only [hG]
    rw [norm_zetaIntegrand]
    exact b₀ x
  have hle : ∀ x, ∀ s ∈ Metric.ball s₀ δ, ‖G' s x‖ ≤ bound x := by
    intro x s hs
    have hre : |s.re - s₀.re| < δ := by
      have := (Complex.abs_re_le_norm (s - s₀)).trans_lt (mem_ball_iff_norm.1 hs)
      rwa [Complex.sub_re] at this
    have hnorm : ‖G' s x‖ = ‖F x‖ * ((IdeleGroup.ideleModule k x : ℝ) ^ s.re *
        |Real.log (IdeleGroup.ideleModule k x : ℝ)|) := by
      simp only [hG', hG]
      rw [norm_mul, norm_zetaIntegrand, ← Complex.ofReal_log (hT x).le, Complex.norm_real,
        Real.norm_eq_abs, mul_assoc]
    rw [hnorm]
    calc ‖F x‖ * ((IdeleGroup.ideleModule k x : ℝ) ^ s.re * |Real.log (IdeleGroup.ideleModule k x : ℝ)|)
        ≤ ‖F x‖ * (((IdeleGroup.ideleModule k x : ℝ) ^ (s₀.re - 2 * δ) +
            (IdeleGroup.ideleModule k x : ℝ) ^ (s₀.re + 2 * δ)) / δ) :=
          mul_le_mul_of_nonneg_left (rpow_mul_abs_log_le (hT x) hδ hre) (norm_nonneg _)
      _ = (‖F x‖ * (IdeleGroup.ideleModule k x : ℝ) ^ (s₀.re - 2 * δ) +
            ‖F x‖ * (IdeleGroup.ideleModule k x : ℝ) ^ (s₀.re + 2 * δ)) / δ := by ring
      _ ≤ bound x := div_le_div_of_nonneg_right (add_le_add (b₁ x) (b₂ x)) hδ.le
  have hdiff : ∀ x, ∀ s ∈ Metric.ball s₀ δ, HasDerivAt (fun s ↦ G s x) (G' s x) s := by
    intro x s _
    have h := ((Complex.hasStrictDerivAt_const_cpow (y := s)
      (Or.inl (Complex.ofReal_ne_zero.2 (hT x).ne'))).hasDerivAt).const_mul
        (F x * (χ.toIdele x : ℂ))
    refine h.congr_deriv ?_
    simp only [hG', hG]
    ring
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ideleMeasure k) (F := G)
    (F' := G') (x₀ := s₀) (bound := bound) (Metric.ball_mem_nhds s₀ hδ)
    (Eventually.of_forall fun s ↦ (continuous_zetaIntegrand hFc χ s).aestronglyMeasurable)
    hint₀ hcont'.aestronglyMeasurable
    (Eventually.of_forall fun x s hs ↦ hle x s hs) hbound_int
    (Eventually.of_forall fun x s hs ↦ hdiff x s hs)
  exact key.2.differentiableAt

def col (m : GL ι 𝔸[k]) (i : ι) : ι → 𝔸[k] := (m : Matrix ι ι 𝔸[k]) *ᵥ Pi.single i 1

/- English proof (translation)
The claim follows from `(Units.continuous_val (M := Matrix ι ι 𝔸[k])).matrix_mulVec continuous_const`.
-/
theorem continuous_col (i : ι) : Continuous fun m : GL ι 𝔸[k] => col m i :=
  (Units.continuous_val (M := Matrix ι ι 𝔸[k])).matrix_mulVec continuous_const

/- English proof (translation)
The claim follows from `hΨ.comp (continuous_id.smul continuous_const)`.
-/
theorem continuous_line {Ψ : (ι → 𝔸[k]) → ℂ} (hΨ : Continuous Ψ) (x : ι → 𝔸[k]) :
    Continuous fun t : 𝔸[k] => Ψ (t • x) :=
  hΨ.comp (continuous_id.smul continuous_const)

def Maj (Ψ : (ι → 𝔸[k]) → ℂ) (i : ι) (C : Set (GL ι 𝔸[k])) : Prop :=
  ∀ a b : ℝ, 1 < a → ∃ f : IdeleGroup k → ℝ, Integrable f (ideleMeasure k) ∧
    ∀ x : ℝ, a ≤ x → x ≤ b → ∀ m ∈ C, ∀ t : IdeleGroup k,
      ‖Ψ ((t : 𝔸[k]) • col m i)‖ * (IdeleGroup.ideleModule k t : ℝ) ^ x ≤ f t

/- English proof (translation)
Introduce `s₀ hs₀`. Establish `hs₀' : 1 < s₀.re` using `hs₀`. Use `set δ := (s₀.re - 1) / 4 with hδdef`. Establish `hδ : 0 < δ` using `by rw [hδdef]; linarith`. Take `⟨f₀, i₀, b₀⟩` from `h s₀.re s₀.re hs₀'`.

Take `⟨f₁, i₁, b₁⟩` from `h (s₀.re - 2 * δ) (s₀.re - 2 * δ) (by rw [hδdef]; linarith)`. Take `⟨f₂, i₂, b₂⟩` from `h (s₀.re + 2 * δ) (s₀.re + 2 * δ) (by linarith)`. Conclude with `(differentiableAt_globalZeta_of_majorant (F := fun t => Ψ (t • col m i)) (continuous_line hΨ _) ω hδ i₀ i₁ i₂ (fun t => b₀ _ le_rfl le_rfl m hm t) (fun t => b₁ _ le_rfl le_rfl m hm t) (fun t => b₂ _ le_rfl le_rfl m hm t)).differentiableWithinAt`.
-/
theorem differentiableOn_lineZeta {Ψ : (ι → 𝔸[k]) → ℂ} (hΨ : Continuous Ψ) (ω : HeckeCharacter k)
    {i : ι} {C : Set (GL ι 𝔸[k])} (h : Maj Ψ i C) {m : GL ι 𝔸[k]} (hm : m ∈ C) :
    DifferentiableOn ℂ (fun s => lineZeta Ψ ω s (col m i)) {s | 1 < s.re} := by
  intro s₀ hs₀
  have hs₀' : 1 < s₀.re := hs₀
  set δ := (s₀.re - 1) / 4 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  obtain ⟨f₀, i₀, b₀⟩ := h s₀.re s₀.re hs₀'
  obtain ⟨f₁, i₁, b₁⟩ := h (s₀.re - 2 * δ) (s₀.re - 2 * δ) (by rw [hδdef]; linarith)
  obtain ⟨f₂, i₂, b₂⟩ := h (s₀.re + 2 * δ) (s₀.re + 2 * δ) (by linarith)
  exact (differentiableAt_globalZeta_of_majorant (F := fun t => Ψ (t • col m i))
    (continuous_line hΨ _) ω hδ i₀ i₁ i₂ (fun t => b₀ _ le_rfl le_rfl m hm t)
    (fun t => b₁ _ le_rfl le_rfl m hm t) (fun t => b₂ _ le_rfl le_rfl m hm t)).differentiableWithinAt

/- English proof (translation)
Use `norm_integral_le_of_norm_le hf (Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Rewrite using `[norm_zetaIntegrand (fun a => Ψ (a • col m i)) ω s t]`. Conclude with `h _ h1 h2 m hm t`.
-/
theorem norm_lineZeta_le {Ψ : (ι → 𝔸[k]) → ℂ} (ω : HeckeCharacter k)
    {i : ι} {C : Set (GL ι 𝔸[k])} {f : IdeleGroup k → ℝ} {a b : ℝ} (hf : Integrable f (ideleMeasure k))
    (h : ∀ x : ℝ, a ≤ x → x ≤ b → ∀ m ∈ C, ∀ t : IdeleGroup k,
      ‖Ψ ((t : 𝔸[k]) • col m i)‖ * (IdeleGroup.ideleModule k t : ℝ) ^ x ≤ f t)
    {s : ℂ} (h1 : a ≤ s.re) (h2 : s.re ≤ b) {m : GL ι 𝔸[k]} (hm : m ∈ C) :
    ‖lineZeta Ψ ω s (col m i)‖ ≤ ∫ t, f t ∂ideleMeasure k := by
  refine norm_integral_le_of_norm_le hf (Eventually.of_forall fun t => ?_)
  rw [norm_zetaIntegrand (fun a => Ψ (a • col m i)) ω s t]
  exact h _ h1 h2 m hm t

def ig (Ψ : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (i : ι) (y : ℂ × GL ι 𝔸[k]) (t : IdeleGroup k) : ℂ :=
  Ψ ((t : 𝔸[k]) • col y.2 i) * (ω.toIdele t : ℂ) * ((IdeleGroup.ideleModule k t : ℝ) : ℂ) ^ y.1

/- English proof (translation)
The claim follows from `norm_zetaIntegrand (fun a => Ψ (a • col y.2 i)) ω y.1 t`.
-/
theorem norm_ig (Ψ : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (i : ι) (y : ℂ × GL ι 𝔸[k]) (t : IdeleGroup k) :
    ‖ig Ψ ω i y t‖ = ‖Ψ ((t : 𝔸[k]) • col y.2 i)‖ * (IdeleGroup.ideleModule k t : ℝ) ^ y.1.re :=
  norm_zetaIntegrand (fun a => Ψ (a • col y.2 i)) ω y.1 t

/- English proof (translation)
The claim follows from `continuous_zetaIntegrand (continuous_line hΨ (col y.2 i)) ω y.1`.
-/
theorem continuous_ig {Ψ : (ι → 𝔸[k]) → ℂ} (hΨ : Continuous Ψ) (ω : HeckeCharacter k) (i : ι)
    (y : ℂ × GL ι 𝔸[k]) : Continuous (ig Ψ ω i y) :=
  continuous_zetaIntegrand (continuous_line hΨ (col y.2 i)) ω y.1

/- English proof (translation)
Establish `c1 : Continuous fun y : ℂ × GL ι 𝔸[k] => Ψ ((t : 𝔸[k]) • col y.2 i)` using `hΨ.comp ((continuous_const : Continuous fun _ : ℂ × GL ι 𝔸[k] => (t : 𝔸[k])).smul ((continuous_col i).comp continuous_snd))`. Use `(c1.mul continuous_const).mul ?_` and prove the remaining obligations. Conclude with `continuous_fst.const_cpow (Or.inl (Complex.ofReal_ne_zero.2 (IdeleGroup.ideleModule k t).2.ne'))`.
-/
theorem continuous_ig_param {Ψ : (ι → 𝔸[k]) → ℂ} (hΨ : Continuous Ψ) (ω : HeckeCharacter k) (i : ι)
    (t : IdeleGroup k) : Continuous fun y : ℂ × GL ι 𝔸[k] => ig Ψ ω i y t := by
  have c1 : Continuous fun y : ℂ × GL ι 𝔸[k] => Ψ ((t : 𝔸[k]) • col y.2 i) :=
    hΨ.comp ((continuous_const : Continuous fun _ : ℂ × GL ι 𝔸[k] => (t : 𝔸[k])).smul
      ((continuous_col i).comp continuous_snd))
  refine (c1.mul continuous_const).mul ?_
  exact continuous_fst.const_cpow (Or.inl (Complex.ofReal_ne_zero.2 (IdeleGroup.ideleModule k t).2.ne'))

/- English proof (translation)
Establish `hc : Continuous fun y : ℂ × GL ι 𝔸[k] => y.1.re` using `Complex.continuous_re.comp continuous_fst`. Establish `e1 : ∀ᶠ y : ℂ × GL ι 𝔸[k] in 𝓝 (s₀, m₀), a < y.1.re` using `hc.continuousAt.eventually (lt_mem_nhds ha)`. Establish `e2 : ∀ᶠ y : ℂ × GL ι 𝔸[k] in 𝓝 (s₀, m₀), y.1.re < b` using `hc.continuousAt.eventually (gt_mem_nhds hb)`. Use `filter_upwards [nhdsWithin_le_nhds e1, nhdsWithin_le_nhds e2, self_mem_nhdsWithin] with y y1 y2 y3`. Conclude with `⟨y1.le, y2.le, y3.2⟩`.
-/
theorem eventually_near {C : Set (GL ι 𝔸[k])} {s₀ : ℂ} {m₀ : GL ι 𝔸[k]} {a b : ℝ} (ha : a < s₀.re)
    (hb : s₀.re < b) : ∀ᶠ y : ℂ × GL ι 𝔸[k] in 𝓝[{s | 1 < s.re} ×ˢ C] (s₀, m₀),
      a ≤ y.1.re ∧ y.1.re ≤ b ∧ y.2 ∈ C := by
  have hc : Continuous fun y : ℂ × GL ι 𝔸[k] => y.1.re := Complex.continuous_re.comp continuous_fst
  have e1 : ∀ᶠ y : ℂ × GL ι 𝔸[k] in 𝓝 (s₀, m₀), a < y.1.re :=
    hc.continuousAt.eventually (lt_mem_nhds ha)
  have e2 : ∀ᶠ y : ℂ × GL ι 𝔸[k] in 𝓝 (s₀, m₀), y.1.re < b :=
    hc.continuousAt.eventually (gt_mem_nhds hb)
  filter_upwards [nhdsWithin_le_nhds e1, nhdsWithin_le_nhds e2, self_mem_nhdsWithin] with y y1 y2 y3
  exact ⟨y1.le, y2.le, y3.2⟩

/- English proof (translation)
Use `firstCountable_gl (k := k) (ι := ι)` as an intermediate fact. Introduce and unpack `⟨s₀, m₀⟩ ⟨hs₀, hm₀⟩`. Establish `hs₀' : 1 < s₀.re` using `hs₀`. Take `⟨f, hf, hb⟩` from `h ((1 + s₀.re) / 2) (s₀.re + 1) (by linarith)`. Establish `hnear` using `eventually_near (C := C) (m₀ := m₀) (s₀ := s₀) (a := (1 + s₀.re) / 2) (b := s₀.re + 1) (by linarith) (by linarith)`.

Use `continuousWithinAt_of_dominated (bound := f) ?_ ?_ hf ?_` and prove the remaining obligations. Conclude with `Eventually.of_forall fun y => (continuous_ig hΨ ω i y).aestronglyMeasurable`. Use `filter_upwards [hnear] with y hy`. Use `Eventually.of_forall fun t => ?_` and prove the remaining obligations. Rewrite using `[norm_ig]`.

Conclude with `hb _ hy.1 hy.2.1 _ hy.2.2 t`. Conclude with `Eventually.of_forall fun t => (continuous_ig_param hΨ ω i t).continuousWithinAt`.
-/
theorem continuousOn_ig {Ψ : (ι → 𝔸[k]) → ℂ} (hΨ : Continuous Ψ) (ω : HeckeCharacter k)
    {i : ι} {C : Set (GL ι 𝔸[k])} (h : Maj Ψ i C) :
    ContinuousOn (fun y : ℂ × GL ι 𝔸[k] => ∫ t, ig Ψ ω i y t ∂ideleMeasure k)
      ({s | 1 < s.re} ×ˢ C) := by
  have := firstCountable_gl (k := k) (ι := ι)
  rintro ⟨s₀, m₀⟩ ⟨hs₀, hm₀⟩
  have hs₀' : 1 < s₀.re := hs₀
  obtain ⟨f, hf, hb⟩ := h ((1 + s₀.re) / 2) (s₀.re + 1) (by linarith)
  have hnear := eventually_near (C := C) (m₀ := m₀) (s₀ := s₀) (a := (1 + s₀.re) / 2) (b := s₀.re + 1)
    (by linarith) (by linarith)
  refine continuousWithinAt_of_dominated (bound := f) ?_ ?_ hf ?_
  · exact Eventually.of_forall fun y => (continuous_ig hΨ ω i y).aestronglyMeasurable
  · filter_upwards [hnear] with y hy
    refine Eventually.of_forall fun t => ?_
    rw [norm_ig]
    exact hb _ hy.1 hy.2.1 _ hy.2.2 t
  · exact Eventually.of_forall fun t => (continuous_ig_param hΨ ω i t).continuousWithinAt

/- English proof (translation)
The claim follows from `continuousOn_ig hΨ ω h`.
-/
theorem continuousOn_lineZeta {Ψ : (ι → 𝔸[k]) → ℂ} (hΨ : Continuous Ψ) (ω : HeckeCharacter k)
    {i : ι} {C : Set (GL ι 𝔸[k])} (h : Maj Ψ i C) :
    ContinuousOn (fun y : ℂ × GL ι 𝔸[k] => lineZeta Ψ ω y.1 (col y.2 i))
      ({s | 1 < s.re} ×ˢ C) :=
  continuousOn_ig hΨ ω h

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem zt_eq {G : Type} [Group G] (π : G →* GL ι 𝔸[k]) (d : ι → IdeleGroup k) (i : ι)
    (Ψ : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (s : ℂ) (g : G) :
    zt π d i Ψ ω s g = lineZeta Ψ ω s (col (kap π d g)⁻¹ i) := rfl

/- English proof (translation)
Introduce `hE G _ _ _ _ K hK k _ _ ι _ _ π Γ P i ω d c η hS Ψ hΨ`. Establish `hΨc : Continuous Ψ` using `GJMatrix.continuous_of_mem_schwartzBruhatPi hΨ`. Establish `hcont : Continuous fun g : G => (kap π d g)⁻¹` using `((continuous_const.mul hS.cont).mul continuous_const).inv`. Establish `hC : IsCompact ((fun g : G => (kap π d g)⁻¹) '' (K : Set G))` using `hK.image hcont`. Establish `hM : Maj Ψ i ((fun g : G => (kap π d g)⁻¹) '' (K : Set G))` using `fun a b ha => (hE k ι Ψ hΨ).1 i a b _ ha hC`.

Establish `hmem : ∀ κ : K, (kap π d κ)⁻¹ ∈ (fun g : G => (kap π d g)⁻¹) '' (K : Set G)` using `fun κ => ⟨κ, κ.2, rfl⟩`. Use `⟨fun κ => differentiableOn_lineZeta hΨc ω hM (hmem κ), ?_, ?_⟩` and prove the remaining obligations. Establish `hmap : Continuous fun y : ℂ × K => (y.1, (kap π d (y.2 : G))⁻¹)` using `continuous_fst.prodMk (hcont.comp (continuous_subtype_val.comp continuous_snd))`. Establish `hS' : Set.MapsTo (fun y : ℂ × K => (y.1, (kap π d (y.2 : G))⁻¹)) ({s : ℂ | 1 < s.re} ×ˢ Set.univ) ({s : ℂ | 1 < s.re} ×ˢ ((fun g : G => (kap π d g)⁻¹) '' (K : Set G)))` using `fun y hy => ⟨hy.1, hmem y.2⟩`. Establish `h2` using `ContinuousOn.comp (continuousOn_lineZeta hΨc ω hM) hmap.continuousOn hS'`.

Conclude with `h2.congr fun y _ => zt_eq π d i Ψ ω y.1 y.2`. Introduce `a b ha`. Take `⟨f, hf, hb⟩` from `(hE k ι Ψ hΨ).1 i a b _ ha hC`. Conclude with `⟨∫ t, f t ∂ideleMeasure k, fun s h1 h2 κ => norm_lineZeta_le ω hf hb h1 h2 (hmem κ)⟩`.
-/
theorem zetaK : EpConv → ZetaK := by
  intro hE G _ _ _ _ K hK k _ _ ι _ _ π Γ P i ω d c η hS Ψ hΨ
  have hΨc : Continuous Ψ := GJMatrix.continuous_of_mem_schwartzBruhatPi hΨ
  have hcont : Continuous fun g : G => (kap π d g)⁻¹ :=
    ((continuous_const.mul hS.cont).mul continuous_const).inv
  have hC : IsCompact ((fun g : G => (kap π d g)⁻¹) '' (K : Set G)) := hK.image hcont
  have hM : Maj Ψ i ((fun g : G => (kap π d g)⁻¹) '' (K : Set G)) :=
    fun a b ha => (hE k ι Ψ hΨ).1 i a b _ ha hC
  have hmem : ∀ κ : K, (kap π d κ)⁻¹ ∈ (fun g : G => (kap π d g)⁻¹) '' (K : Set G) :=
    fun κ => ⟨κ, κ.2, rfl⟩
  refine ⟨fun κ => differentiableOn_lineZeta hΨc ω hM (hmem κ), ?_, ?_⟩
  · have hmap : Continuous fun y : ℂ × K => (y.1, (kap π d (y.2 : G))⁻¹) :=
      continuous_fst.prodMk (hcont.comp (continuous_subtype_val.comp continuous_snd))
    have hS' : Set.MapsTo (fun y : ℂ × K => (y.1, (kap π d (y.2 : G))⁻¹))
        ({s : ℂ | 1 < s.re} ×ˢ Set.univ)
        ({s : ℂ | 1 < s.re} ×ˢ ((fun g : G => (kap π d g)⁻¹) '' (K : Set G))) :=
      fun y hy => ⟨hy.1, hmem y.2⟩
    have h2 := ContinuousOn.comp (continuousOn_lineZeta hΨc ω hM) hmap.continuousOn hS'
    exact h2.congr fun y _ => zt_eq π d i Ψ ω y.1 y.2
  · intro a b ha
    obtain ⟨f, hf, hb⟩ := (hE k ι Ψ hΨ).1 i a b _ ha hC
    exact ⟨∫ t, f t ∂ideleMeasure k, fun s h1 h2 κ => norm_lineZeta_le ω hf hb h1 h2 (hmem κ)⟩

end GlobalTheory.CompanionTheory.ZetaAlongK
