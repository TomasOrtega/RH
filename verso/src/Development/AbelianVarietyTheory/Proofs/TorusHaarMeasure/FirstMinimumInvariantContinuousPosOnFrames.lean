import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MajLactRmul
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.EventuallyComparable
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsIntMulIntegral
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.RmulOneFrame
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPos

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.ClosedDiscontinuity

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Take `⟨c, C, hc, hb⟩` from `_root_.GlobalTheory.MajorantContinuity.compact_bounds X (isCompact_singleton (x := x)) (by simpa using hx)`. Establish `hev` using `(_root_.GlobalTheory.MajorantContinuity.majorant_continuity (E := E)).1 r X x hx 1 one_pos`. Use `⟨_, hev, c / 2, 2 * C, by positivity, fun y hy => ⟨hy.1, fun τ w => ?_⟩⟩` and prove the remaining obligations. Take `⟨h1, h2⟩` from `hy.2 τ w`. Take `⟨h3, h4⟩` from `hb x rfl τ w`.

Apply the tactic sequence `constructor <;> nlinarith`.
-/
private lemma exists_nhds_maj_two_sided_norm_sq_bound {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (hx : x ∈ X.dom) :
    ∃ U ∈ nhds x, ∃ c C : ℝ, 0 < c ∧ ∀ y ∈ U, y ∈ X.dom ∧
      ∀ (τ : X.Ψ) (w : Fin r → ℂ), c * ‖w‖ ^ 2 ≤ X.maj y τ w ∧ X.maj y τ w ≤ C * ‖w‖ ^ 2 := by
  obtain ⟨c, C, hc, hb⟩ :=
    _root_.GlobalTheory.MajorantContinuity.compact_bounds X (isCompact_singleton (x := x)) (by simpa using hx)
  have hev := (_root_.GlobalTheory.MajorantContinuity.majorant_continuity (E := E)).1 r X x hx 1 one_pos
  refine ⟨_, hev, c / 2, 2 * C, by positivity, fun y hy => ⟨hy.1, fun τ w => ?_⟩⟩
  obtain ⟨h1, h2⟩ := hy.2 τ w
  obtain ⟨h3, h4⟩ := hb x rfl τ w
  constructor <;> nlinarith

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 E) x`. Use `⟨b, nonZeroDivisors.ne_zero hb, ?_⟩` and prove the remaining obligations. Establish `hb' : (b : E) ≠ 0`. Simplify using `using nonZeroDivisors.ne_zero hb`. Establish `: (b : E) * (algebraMap (𝓞 E) E a / algebraMap (𝓞 E) E b) = a`.

Simplify using `[mul_div_cancel₀ _ hb']`. Rewrite using `[this]`. Conclude with `RingOfIntegers.isIntegral_coe a`.
-/
private lemma exists_integral_denominator (x : E) :
    ∃ b : 𝓞 E, b ≠ 0 ∧ IsIntegral ℤ ((b : E) * x) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  refine ⟨b, nonZeroDivisors.ne_zero hb, ?_⟩
  have hb' : (b : E) ≠ 0 := by
    simpa using nonZeroDivisors.ne_zero hb
  have : (b : E) * (algebraMap (𝓞 E) E a / algebraMap (𝓞 E) E b) = a := by
    simp [mul_div_cancel₀ _ hb']
  rw [this]
  exact RingOfIntegers.isIntegral_coe a

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Take `⟨S, hS⟩` from `X.Λ_fg`. Use `choose d hd0 hd using fun x : E => exists_integral_denominator x`. Set `T : Finset E` to `S.biUnion fun s => Finset.univ.image s`. Use `⟨∏ t ∈ T, d t, Finset.prod_ne_zero_iff.2 (fun t _ => hd0 t), fun v hv => ?_⟩` and prove the remaining obligations. Rewrite `hv` using `[← hS]`.

Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem s hs`. Introduce `i`. Establish `ht : s i ∈ T` using `Finset.mem_biUnion.2 ⟨s, hs, Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩`. Rewrite using `[← Finset.mul_prod_erase T d ht]`.

Use `push_cast`. Rewrite using `[mul_comm (d (s i) : E), mul_assoc]`. Establish `h1` using `(RingOfIntegers.isIntegral_coe (∏ t ∈ T.erase (s i), d t)).mul (hd (s i))`. Simplify using `using h1`. Consider the case `zero => intro i`.

Simplify using `using isIntegral_zero`. Consider the case `add u w _ _ hu hw => intro i`. Simplify `(hu i).add (hw i)` using `[mul_add]`. Consider the case `smul a u _ hu`. Introduce `i`.

Establish `: ((∏ t ∈ T, d t : 𝓞 E) : E) * (a • u) i = (a : E) * (((∏ t ∈ T, d t : 𝓞 E) : E) * u i)`. Simplify using `[Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `(RingOfIntegers.isIntegral_coe a).mul (hu i)`.
-/
private lemma exists_common_denominator_lattice {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) :
    ∃ y : 𝓞 E, y ≠ 0 ∧ ∀ v ∈ X.Λ, ∀ i, IsIntegral ℤ ((y : E) * v i) := by
  classical
  obtain ⟨S, hS⟩ := X.Λ_fg
  choose d hd0 hd using fun x : E => exists_integral_denominator x
  let T : Finset E := S.biUnion fun s => Finset.univ.image s
  refine ⟨∏ t ∈ T, d t, Finset.prod_ne_zero_iff.2 (fun t _ => hd0 t), fun v hv => ?_⟩
  rw [← hS] at hv
  induction hv using Submodule.span_induction with
  | mem s hs =>
    intro i
    have ht : s i ∈ T :=
      Finset.mem_biUnion.2 ⟨s, hs, Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩
    rw [← Finset.mul_prod_erase T d ht]
    push_cast
    rw [mul_comm (d (s i) : E), mul_assoc]
    have h1 := (RingOfIntegers.isIntegral_coe (∏ t ∈ T.erase (s i), d t)).mul (hd (s i))
    simpa using h1
  | zero => intro i; simpa using isIntegral_zero
  | add u w _ _ hu hw => intro i; simpa [mul_add] using (hu i).add (hw i)
  | smul a u _ hu =>
    intro i
    have : ((∏ t ∈ T, d t : 𝓞 E) : E) * (a • u) i =
        (a : E) * (((∏ t ∈ T, d t : 𝓞 E) : E) * u i) := by
      simp [Algebra.smul_def]; ring
    rw [this]
    exact (RingOfIntegers.isIntegral_coe a).mul (hu i)

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Establish `hy' : (y : E) ≠ 0` using `by simpa using hy`. Use `((Embeddings.finite_of_norm_le E ℂ ((∑ ψ : E →+* ℂ, ‖ψ (y : E)‖) * R)).image (fun b => b / (y : E))).subset ?_` and prove the remaining obligations. Introduce `a ⟨ha, hR⟩`. Use `⟨(y : E) * a, ⟨ha, fun φ => ?_⟩, by simp [hy']⟩` and prove the remaining obligations. Establish `hφ : ‖φ a‖ ≤ R`.

Break down `hΨ φ with h | h` into its components or cases. Conclude with `hR φ h`. Simplify using `using hR _ h`. Rewrite using `[map_mul, norm_mul]`. Conclude with `mul_le_mul (Finset.single_le_sum (f := fun ψ : E →+* ℂ => ‖ψ (y : E)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ φ)) hφ (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)`.
-/
private lemma finite_denominator_norm_le (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ∨ ComplexEmbedding.conjugate τ ∈ Ψ)
    (y : 𝓞 E) (hy : y ≠ 0) (R : ℝ) :
    {a : E | IsIntegral ℤ ((y : E) * a) ∧ ∀ τ ∈ Ψ, ‖τ a‖ ≤ R}.Finite := by
  have hy' : (y : E) ≠ 0 := by simpa using hy
  refine ((Embeddings.finite_of_norm_le E ℂ ((∑ ψ : E →+* ℂ, ‖ψ (y : E)‖) * R)).image
    (fun b => b / (y : E))).subset ?_
  intro a ⟨ha, hR⟩
  refine ⟨(y : E) * a, ⟨ha, fun φ => ?_⟩, by simp [hy']⟩
  have hφ : ‖φ a‖ ≤ R := by
    rcases hΨ φ with h | h
    · exact hR φ h
    · simpa using hR _ h
  rw [map_mul, norm_mul]
  exact mul_le_mul (Finset.single_le_sum (f := fun ψ : E →+* ℂ => ‖ψ (y : E)‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ φ)) hφ (norm_nonneg _)
    (Finset.sum_nonneg fun _ _ => norm_nonneg _)

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Distinguish the cases in `h : τ ∈ X.Ψ`. Conclude with `Or.inl h`. Use `right`. Rewrite using `[X.cmType]`. Simplify `h` using `[ComplexEmbedding.conjugate, star_star]`.
-/
private lemma mem_Ψ_or_conjugate_mem {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (τ : E →+* ℂ) :
    τ ∈ X.Ψ ∨ ComplexEmbedding.conjugate τ ∈ X.Ψ := by
  by_cases h : τ ∈ X.Ψ
  · exact Or.inl h
  · right
    rw [X.cmType]
    simpa [ComplexEmbedding.conjugate, star_star] using h

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Take `⟨y, hy0, hy⟩` from `exists_common_denominator_lattice X`. Use `(Set.Finite.pi (t := fun _ : Fin r => {a : E | IsIntegral ℤ ((y : E) * a) ∧ ∀ τ ∈ X.Ψ, ‖τ a‖ ≤ R}) (fun _ => finite_denominator_norm_le X.Ψ (mem_Ψ_or_conjugate_mem X) y hy0 R)).subset ?_` and prove the remaining obligations. Introduce `v ⟨hv, hR⟩ i _`. Use `⟨hy v hv i, fun τ hτ => ?_⟩` and prove the remaining obligations. Use `hR ⟨τ, hτ⟩` as an intermediate fact.

Conclude with `le_trans (by simpa [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb] using norm_le_pi_norm (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v) i) this`.
-/
private lemma finite_lattice_norm_emb_le {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (R : ℝ) :
    {v : Fin r → E | v ∈ X.Λ ∧ ∀ τ : X.Ψ, ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) v‖ ≤ R}.Finite := by
  obtain ⟨y, hy0, hy⟩ := exists_common_denominator_lattice X
  refine (Set.Finite.pi (t := fun _ : Fin r => {a : E | IsIntegral ℤ ((y : E) * a) ∧
      ∀ τ ∈ X.Ψ, ‖τ a‖ ≤ R})
    (fun _ => finite_denominator_norm_le X.Ψ (mem_Ψ_or_conjugate_mem X) y hy0 R)).subset ?_
  intro v ⟨hv, hR⟩ i _
  refine ⟨hy v hv i, fun τ hτ => ?_⟩
  have := hR ⟨τ, hτ⟩
  exact le_trans (by simpa [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb] using norm_le_pi_norm (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v) i) this

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Establish `htop : Submodule.span E (S : Set (Fin r → E)) = ⊤`. Rewrite using `[eq_top_iff, ← hspan, Submodule.span_le]`. Introduce `v hv`. Rewrite `hv` using `[← hS]`. Conclude with `Submodule.span_le_restrictScalars (𝓞 E) E _ hv`.

Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Conclude with `LinearMap.ext_on htop (fun s hs => by simpa using h s hs)`.
-/
private lemma matrix_eq_of_mulVec_eq_on_span_generators {r : ℕ} {Λ : Submodule (𝓞 E) (Fin r → E)}
    {S : Finset (Fin r → E)} (hS : Submodule.span (𝓞 E) ↑S = Λ)
    (hspan : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) {g g' : Matrix (Fin r) (Fin r) E}
    (h : ∀ s ∈ S, g.mulVec s = g'.mulVec s) : g = g' := by
  have htop : Submodule.span E (S : Set (Fin r → E)) = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    intro v hv
    rw [← hS] at hv
    exact Submodule.span_le_restrictScalars (𝓞 E) E _ hv
  apply Matrix.toLin'.injective
  exact LinearMap.ext_on htop (fun s hs => by simpa using h s hs)

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Rewrite using `[← Real.sqrt_sq ha, ← Real.sqrt_sq hb, ← Real.sqrt_mul hk]`. Conclude with `Real.sqrt_le_sqrt h`.
-/
private lemma le_sqrt_mul_of_sq_le_mul_sq {a b k : ℝ} (hk : 0 ≤ k) (hb : 0 ≤ b) (ha : 0 ≤ a)
    (h : a ^ 2 ≤ k * b ^ 2) : a ≤ Real.sqrt k * b := by
  rw [← Real.sqrt_sq ha, ← Real.sqrt_sq hb, ← Real.sqrt_mul hk]
  exact Real.sqrt_le_sqrt h

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Use extensionality with `i`. Simplify using `[_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb, Matrix.mulVec, dotProduct, map_sum, map_mul]`.
-/
private lemma emb_mulVec_torus_haar_measure {r : ℕ} (τ : E →+* ℂ) (g : Matrix (Fin r) (Fin r) E) (v : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ (g.mulVec v) = (g.map τ).mulVec (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v) := by
  ext i
  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb, Matrix.mulVec, dotProduct, map_sum, map_mul]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Unfold `_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.PropDisc`. Introduce `x hx x' hx'`. Take `⟨U, hU, c, C, hc, hUb⟩` from `exists_nhds_maj_two_sided_norm_sq_bound X hx`. Take `⟨U', hU', c', C', hc', hUb'⟩` from `exists_nhds_maj_two_sided_norm_sq_bound X hx'`. Use `⟨U, hU, U', hU', ?_⟩` and prove the remaining obligations.

Take `⟨S, hS⟩` from `X.Λ_fg`. Establish `hSΛ : ∀ s ∈ S, s ∈ X.Λ` using `fun s hs => hS ▸ Submodule.subset_span hs`. Use `set K := Real.sqrt (|C| / c')`. Use `set R := K * ∑ s ∈ S, ∑ τ : X.Ψ, ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) s‖`. Establish `hF` using `finite_lattice_norm_emb_le X R`.

Establish `hpi : (Set.pi Set.univ (fun _ : S => {v : Fin r → E | v ∈ X.Λ ∧ ∀ τ : X.Ψ, ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) v‖ ≤ R})).Finite` using `Set.Finite.pi (fun _ => hF)`. Use `(hpi.preimage (f := fun γ : GL (Fin r) E => fun s : S => (γ : Matrix (Fin r) (Fin r) E).mulVec s.1) ?_).subset ?_` and prove the remaining obligations. Introduce `γ _ γ' _ h`. Apply `Units.ext` to reduce the goal to its premises. Conclude with `matrix_eq_of_mulVec_eq_on_span_generators hS X.Λ_span (fun s hs => congrFun h ⟨s, hs⟩)`.

Introduce and unpack `γ ⟨hγ, u, hu, u', hu', b, hb, he⟩ s _`. Establish `hs` using `X.Γ_stab γ hγ`. Take `⟨hud, hUu⟩` from `hUb u hu`. Take `⟨hud', hUu'⟩` from `hUb' u' hu'`. Use `⟨(hs.2 s).1 (hSΛ s s.2), fun τ => ?_⟩` and prove the remaining obligations.

Establish `hmaj : ∀ w, X.maj u' τ (((γ : Matrix (Fin r) (Fin r) E).map (τ : E →+* ℂ)).mulVec w) = X.maj u τ w` using `fun w => by`. Rewrite using `[← _root_.GlobalTheory.MajInv.maj_rmul X hud' hb, ← he, _root_.GlobalTheory.MajInv.maj_lact X hs]`. Establish `hbound : ∀ w, ‖((γ : Matrix (Fin r) (Fin r) E).map (τ : E →+* ℂ)).mulVec w‖ ≤ K * ‖w‖` using `fun w => by`. Apply `le_sqrt_mul_of_sq_le_mul_sq (by positivity) (norm_nonneg _) (norm_nonneg _)` to reduce the goal to its premises. Establish `h1` using `(hUu' τ (((γ : Matrix (Fin r) (Fin r) E).map (τ : E →+* ℂ)).mulVec w)).1`.

Establish `h2` using `(hUu τ w).2`. Rewrite `h1` using `[hmaj]`. Establish `h3 : C * ‖w‖ ^ 2 ≤ |C| * ‖w‖ ^ 2` using `mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)`. Rewrite using `[div_mul_eq_mul_div, le_div_iff₀ hc']`. Use the polynomial consequences of the given equalities and inequalities.

Rewrite using `[emb_mulVec_torus_haar_measure]`. Use `le_trans (hbound _) (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))` and prove the remaining obligations. Use `le_trans ?_ (Finset.single_le_sum (f := fun s => ∑ τ : X.Ψ, ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) s‖) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) s.2)` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := fun τ : X.Ψ => ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) (s : Fin r → E)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ τ)`.
-/
private lemma propDisc_arithmetic_group_frames (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.PropDisc X := by
  classical
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.PropDisc
  intro x hx x' hx'
  obtain ⟨U, hU, c, C, hc, hUb⟩ := exists_nhds_maj_two_sided_norm_sq_bound X hx
  obtain ⟨U', hU', c', C', hc', hUb'⟩ := exists_nhds_maj_two_sided_norm_sq_bound X hx'
  refine ⟨U, hU, U', hU', ?_⟩
  obtain ⟨S, hS⟩ := X.Λ_fg
  have hSΛ : ∀ s ∈ S, s ∈ X.Λ := fun s hs => hS ▸ Submodule.subset_span hs
  set K := Real.sqrt (|C| / c')
  set R := K * ∑ s ∈ S, ∑ τ : X.Ψ, ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) s‖
  have hF := finite_lattice_norm_emb_le X R
  have hpi : (Set.pi Set.univ (fun _ : S =>
      {v : Fin r → E | v ∈ X.Λ ∧ ∀ τ : X.Ψ, ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) v‖ ≤ R})).Finite :=
    Set.Finite.pi (fun _ => hF)
  refine (hpi.preimage
    (f := fun γ : GL (Fin r) E => fun s : S => (γ : Matrix (Fin r) (Fin r) E).mulVec s.1)
    ?_).subset ?_
  · intro γ _ γ' _ h
    apply Units.ext
    exact matrix_eq_of_mulVec_eq_on_span_generators hS X.Λ_span (fun s hs => congrFun h ⟨s, hs⟩)
  · rintro γ ⟨hγ, u, hu, u', hu', b, hb, he⟩ s _
    have hs := X.Γ_stab γ hγ
    obtain ⟨hud, hUu⟩ := hUb u hu
    obtain ⟨hud', hUu'⟩ := hUb' u' hu'
    refine ⟨(hs.2 s).1 (hSΛ s s.2), fun τ => ?_⟩
    have hmaj : ∀ w, X.maj u' τ (((γ : Matrix (Fin r) (Fin r) E).map (τ : E →+* ℂ)).mulVec w) =
        X.maj u τ w := fun w => by
      rw [← _root_.GlobalTheory.MajInv.maj_rmul X hud' hb, ← he,
        _root_.GlobalTheory.MajInv.maj_lact X hs]
    have hbound : ∀ w, ‖((γ : Matrix (Fin r) (Fin r) E).map (τ : E →+* ℂ)).mulVec w‖ ≤
        K * ‖w‖ := fun w => by
      apply le_sqrt_mul_of_sq_le_mul_sq (by positivity) (norm_nonneg _) (norm_nonneg _)
      have h1 := (hUu' τ (((γ : Matrix (Fin r) (Fin r) E).map (τ : E →+* ℂ)).mulVec w)).1
      have h2 := (hUu τ w).2
      rw [hmaj] at h1
      have h3 : C * ‖w‖ ^ 2 ≤ |C| * ‖w‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      rw [div_mul_eq_mul_div, le_div_iff₀ hc']
      nlinarith
    rw [emb_mulVec_torus_haar_measure]
    refine le_trans (hbound _) (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun s => ∑ τ : X.Ψ, ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) s‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) s.2)
    exact Finset.single_le_sum
      (f := fun τ : X.Ψ => ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) (s : Fin r → E)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ τ)

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

/- English proof (translation)
Introduce `r X` and use `propDisc_arithmetic_group_frames r X`.
-/
theorem _root_.GlobalTheory.ClosedDiscontinuity.propDisc_closed :
    ∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r), _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.PropDisc X :=
  fun r X => propDisc_arithmetic_group_frames r X

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Establish `hs` using `X.Γ_stab γ hγ`. Take `⟨-, hmaj⟩` from `_root_.GlobalTheory.maj_lact_rmul r X γ hs x hx b hb`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.la1 _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.firstMinimumSq`. Apply `congrArg Real.sqrt` to reduce the goal to its premises. Apply `congrArg sInf` to reduce the goal to its premises.

Use extensionality with `t`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv, hv0, rfl⟩`. Use `⟨(↑γ⁻¹ : Matrix (Fin r) (Fin r) E).mulVec v, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hs.2]`.

Simplify `hv` using `[Matrix.mulVec_mulVec]`. Introduce `h`. Apply `hv0` to reduce the goal to its premises. Use `congrArg (fun w => (↑γ : Matrix (Fin r) (Fin r) E).mulVec w) h` as an intermediate fact. Simplify `this` using `[Matrix.mulVec_mulVec]`.

Use `Finset.sum_congr rfl (fun τ _ => ?_)` and prove the remaining obligations. Rewrite using `[← hmaj τ, ← emb_mulVec_torus_haar_measure]`. Simplify using `[Matrix.mulVec_mulVec]`. Introduce and unpack `⟨v, hv, hv0, rfl⟩`. Use `⟨(↑γ : Matrix (Fin r) (Fin r) E).mulVec v, (hs.2 v).1 hv, ?_, ?_⟩` and prove the remaining obligations.

Introduce `h`. Apply `hv0` to reduce the goal to its premises. Use `congrArg (fun w => (↑γ⁻¹ : Matrix (Fin r) (Fin r) E).mulVec w) h` as an intermediate fact. Simplify `this` using `[Matrix.mulVec_mulVec]`. Use `Finset.sum_congr rfl (fun τ _ => ?_)` and prove the remaining obligations.

Rewrite using `[← hmaj τ, ← emb_mulVec_torus_haar_measure]`.
-/
private lemma la1_lact_rmul_eq {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom) {b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r) :
    X.la1 (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b)) = X.la1 x := by
  have hs := X.Γ_stab γ hγ
  obtain ⟨-, hmaj⟩ := _root_.GlobalTheory.maj_lact_rmul r X γ hs x hx b hb
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.la1 _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.firstMinimumSq
  apply congrArg Real.sqrt
  apply congrArg sInf
  ext t
  constructor
  · rintro ⟨v, hv, hv0, rfl⟩
    refine ⟨(↑γ⁻¹ : Matrix (Fin r) (Fin r) E).mulVec v, ?_, ?_, ?_⟩
    · rw [hs.2]; simpa [Matrix.mulVec_mulVec] using hv
    · intro h; apply hv0
      have := congrArg (fun w => (↑γ : Matrix (Fin r) (Fin r) E).mulVec w) h
      simpa [Matrix.mulVec_mulVec] using this
    · refine Finset.sum_congr rfl (fun τ _ => ?_)
      rw [← hmaj τ, ← emb_mulVec_torus_haar_measure]
      simp [Matrix.mulVec_mulVec]
  · rintro ⟨v, hv, hv0, rfl⟩
    refine ⟨(↑γ : Matrix (Fin r) (Fin r) E).mulVec v, (hs.2 v).1 hv, ?_, ?_⟩
    · intro h; apply hv0
      have := congrArg (fun w => (↑γ⁻¹ : Matrix (Fin r) (Fin r) E).mulVec w) h
      simpa [Matrix.mulVec_mulVec] using this
    · refine Finset.sum_congr rfl (fun τ _ => ?_)
      rw [← hmaj τ, ← emb_mulVec_torus_haar_measure]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Use function extensionality and compare the values at `x`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.la1`. Both sides reduce to the same expression.
-/
private lemma la1_eq_sqrt_la1sq {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) :
    X.la1 = fun x => Real.sqrt (X.firstMinimumSq x) := by
  funext x
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.la1
  rfl

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Establish `ha : e * y ≤ e * ((1 + e) * L)` using `mul_le_mul_of_nonneg_left h2 he.le`. Establish `hb : e * ((1 + e) * L) ≤ 2 * e * L`. Establish `: 0 ≤ e * L` using `mul_nonneg he.le hL`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[abs_lt]`.

Apply the tactic sequence `constructor <;> nlinarith`.
-/
private lemma abs_sub_lt_of_ratio_bounds {L y e ε : ℝ} (hL : 0 ≤ L) (he : 0 < e) (he1 : e ≤ 1)
    (heL : 2 * e * L < ε) (h1 : L ≤ (1 + e) * y) (h2 : y ≤ (1 + e) * L) : |y - L| < ε := by
  have ha : e * y ≤ e * ((1 + e) * L) := mul_le_mul_of_nonneg_left h2 he.le
  have hb : e * ((1 + e) * L) ≤ 2 * e * L := by
    have : 0 ≤ e * L := mul_nonneg he.le hL
    nlinarith
  rw [abs_lt]
  constructor <;> nlinarith

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Introduce `x hx`. Rewrite using `[ContinuousWithinAt, Metric.tendsto_nhds]`. Introduce `ε hε`. Establish `hL0 : 0 ≤ X.firstMinimumSq x` using `_root_.ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds.minimumSq_nonneg X hx`. Choose the witnesses or unpack the hypotheses as in `⟨e, he0, he1, heL⟩ : ∃ e : ℝ, 0 < e ∧ e ≤ 1 ∧ 2 * e * X.firstMinimumSq x < ε := by`.

Use `⟨min 1 (ε / (4 * (X.firstMinimumSq x + 1))), by positivity, min_le_left _ _, ?_⟩` and prove the remaining obligations. Establish `hm : min 1 (ε / (4 * (X.firstMinimumSq x + 1))) ≤ ε / (4 * (X.firstMinimumSq x + 1))` using `min_le_right _ _`. Establish `h4 : ε / (4 * (X.firstMinimumSq x + 1)) * (X.firstMinimumSq x + 1) = ε / 4`. Clear the denominators using the available nonvanishing facts. Establish `: min 1 (ε / (4 * (X.firstMinimumSq x + 1))) * X.firstMinimumSq x ≤ ε / 4`.

Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hev` using `(_root_.GlobalTheory.MajorantContinuity.majorant_continuity (E := E)).1 r X x hx e he0`. Use `filter_upwards [nhdsWithin_le_nhds hev] with y hyy`. Take `⟨hy, hxy⟩` from `hyy`.

Establish `hb` using `_root_.ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds.minimumSq_two_sided_bounds X hx hy (k1 := 1 / (1 + e)) (k2 := 1 + e) (by positivity) (by positivity) (fun τ w => by`. Use `(hxy τ w).1` as an intermediate fact. Rewrite using `[div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]`. Use the proof step `linarith)`. Use the proof step `(fun τ w => (hxy τ w).2)`.

Take `⟨h1, h2⟩` from `hb`. Rewrite `h1` using `[div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]`. Rewrite using `[Real.dist_eq]`. Conclude with `abs_sub_lt_of_ratio_bounds hL0 he0 he1 heL (by linarith) h2`.
-/
private lemma continuousOn_la1sq_dom {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) : ContinuousOn X.firstMinimumSq X.dom := by
  intro x hx
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro ε hε
  have hL0 : 0 ≤ X.firstMinimumSq x := _root_.ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds.minimumSq_nonneg X hx
  obtain ⟨e, he0, he1, heL⟩ : ∃ e : ℝ, 0 < e ∧ e ≤ 1 ∧ 2 * e * X.firstMinimumSq x < ε := by
    refine ⟨min 1 (ε / (4 * (X.firstMinimumSq x + 1))), by positivity, min_le_left _ _, ?_⟩
    have hm : min 1 (ε / (4 * (X.firstMinimumSq x + 1))) ≤ ε / (4 * (X.firstMinimumSq x + 1)) := min_le_right _ _
    have h4 : ε / (4 * (X.firstMinimumSq x + 1)) * (X.firstMinimumSq x + 1) = ε / 4 := by
      field_simp
    have : min 1 (ε / (4 * (X.firstMinimumSq x + 1))) * X.firstMinimumSq x ≤ ε / 4 := by
      calc _ ≤ ε / (4 * (X.firstMinimumSq x + 1)) * X.firstMinimumSq x := mul_le_mul_of_nonneg_right hm hL0
        _ ≤ ε / (4 * (X.firstMinimumSq x + 1)) * (X.firstMinimumSq x + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = ε / 4 := h4
    linarith
  have hev := (_root_.GlobalTheory.MajorantContinuity.majorant_continuity (E := E)).1 r X x hx e he0
  filter_upwards [nhdsWithin_le_nhds hev] with y hyy
  obtain ⟨hy, hxy⟩ := hyy
  have hb := _root_.ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds.minimumSq_two_sided_bounds X hx hy (k1 := 1 / (1 + e)) (k2 := 1 + e) (by positivity) (by positivity)
    (fun τ w => by
      have := (hxy τ w).1
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
      linarith)
    (fun τ w => (hxy τ w).2)
  obtain ⟨h1, h2⟩ := hb
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)] at h1
  rw [Real.dist_eq]
  exact abs_sub_lt_of_ratio_bounds hL0 he0 he1 heL (by linarith) h2

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Break down `s.eq_empty_or_nonempty with rfl | hne` into its components or cases. Conclude with `⟨1, one_pos, by simp⟩`. Take `⟨v0, hv0, hmin⟩` from `Set.exists_min_image s f hs hne`. Conclude with `⟨f v0, hpos v0 hv0, hmin⟩`.
-/
private lemma exists_pos_lower_bound_of_finite {α : Type} {s : Set α} (hs : s.Finite)
    (f : α → ℝ) (hpos : ∀ v ∈ s, 0 < f v) : ∃ δ : ℝ, 0 < δ ∧ ∀ v ∈ s, δ ≤ f v := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  · obtain ⟨v0, hv0, hmin⟩ := Set.exists_min_image s f hs hne
    exact ⟨f v0, hpos v0 hv0, hmin⟩

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Take `⟨c0, C0, hc0, hb⟩` from `_root_.GlobalTheory.MajorantContinuity.compact_bounds X (isCompact_singleton (x := x)) (by simpa using hx)`. Take `⟨σ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Choose the witnesses or unpack the hypotheses as in `⟨τ0, hτ0⟩ : ∃ τ0 : E →+* ℂ, τ0 ∈ X.Ψ := by`. Break down `mem_Ψ_or_conjugate_mem X σ with h | h` into its components or cases. Conclude with `⟨σ, h⟩`.

Conclude with `⟨_, h⟩`. Establish `hne : (Finset.univ : Finset X.Ψ).Nonempty` using `⟨⟨τ0, hτ0⟩, Finset.mem_univ _⟩`. Use `set m := Finset.univ.inf' hne X.c`. Establish `hm : 0 < m` using `(Finset.lt_inf'_iff hne).2 (fun τ _ => _root_.ReciprocityTheory.ChartRestriction.G.FD.TwoSidedBoostBounds.c_pos X τ)`. Set `f : (Fin r → E) → ℝ` to `fun v => ∑ τ : X.Ψ, X.c τ * X.maj x τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) v)`.

Establish `hterm : ∀ v (τ : X.Ψ), 0 ≤ X.c τ * X.maj x τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) v)` using `fun v τ => mul_nonneg (_root_.ReciprocityTheory.ChartRestriction.G.FD.TwoSidedBoostBounds.c_pos X τ).le (_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.maj_nonneg X hx τ _)`. Establish `hfpos : ∀ v, v ≠ 0 → 0 < f v`. Introduce `v hv`. Establish `hemb : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ0 v ≠ 0`. Introduce `h`.

Apply `hv` to reduce the goal to its premises. Use extensionality with `i`. Use `congrFun h i` as an intermediate fact. Simplify `this` using `[_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb]`. Establish `h1 : 0 < X.c ⟨τ0, hτ0⟩ * X.maj x ⟨τ0, hτ0⟩ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ0 v)` using `mul_pos (_root_.ReciprocityTheory.ChartRestriction.G.FD.TwoSidedBoostBounds.c_pos X _) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.maj_pos X hx _ hemb)`.

Conclude with `lt_of_lt_of_le h1 (Finset.single_le_sum (f := fun τ : X.Ψ => X.c τ * X.maj x τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) v)) (fun τ _ => hterm v τ) (Finset.mem_univ _))`. Take `⟨δ, hδ, hδf⟩` from `exists_pos_lower_bound_of_finite ((finite_lattice_norm_emb_le X 1).inter_of_left {v | v ≠ 0}) f (fun v hv => hfpos v hv.2)`. Establish `hlow : ∀ v ∈ X.Λ, v ≠ 0 → min δ (m * c0) ≤ f v`. Introduce `v hvΛ hv0`. Distinguish the cases in `hsmall : ∀ τ : X.Ψ, ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) v‖ ≤ 1`.

Conclude with `le_trans (min_le_left _ _) (hδf v ⟨⟨hvΛ, hsmall⟩, hv0⟩)`. Use `push_neg at hsmall`. Take `⟨τ, hτ⟩` from `hsmall`. Use `le_trans (min_le_right _ _) ?_` and prove the remaining obligations. Establish `h1 : m * c0 ≤ X.c τ * X.maj x τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) v)`.

Establish `hmτ : m ≤ X.c τ` using `Finset.inf'_le _ (Finset.mem_univ τ)`. Establish `h2` using `(hb x rfl τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) v)).1`. Establish `h3 : c0 ≤ c0 * ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) v‖ ^ 2`. Establish `: 1 ≤ ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) v‖ ^ 2` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities.

Combine the equalities or inequalities in the displayed calculation. Conclude with `le_trans h1 (Finset.single_le_sum (f := fun τ : X.Ψ => X.c τ * X.maj x τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) v)) (fun τ _ => hterm v τ) (Finset.mem_univ _))`. Choose the witnesses or unpack the hypotheses as in `⟨v0, hv0Λ, hv00⟩ : ∃ v ∈ X.Λ, v ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Establish `hbot : (X.Λ : Set (Fin r → E)) ⊆ {0}` using `fun v hv => hcon v hv`. Use `X.Λ_span` as an intermediate fact. Rewrite `this` using `[eq_top_iff]`. Establish `h1` using `this (Submodule.mem_top (x := fun _ : Fin r => (1 : E)))`. Establish `h2 : Submodule.span E (X.Λ : Set (Fin r → E)) ≤ ⊥`.

Rewrite using `[Submodule.span_le]`. Introduce `v hv`. Simplify using `using hbot hv`. Establish `h3` using `h2 h1`. Rewrite `h3` using `[Submodule.mem_bot]`.

Conclude with `one_ne_zero (congrFun h3 ⟨0, hr⟩)`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.firstMinimumSq`. Use `lt_of_lt_of_le (lt_min hδ (mul_pos hm hc0)) (le_csInf ⟨f v0, v0, hv0Λ, hv00, rfl⟩ ?_)` and prove the remaining obligations. Introduce and unpack `t ⟨v, hv, hv0, rfl⟩`. Conclude with `hlow v hv hv0`.
-/
private lemma la1sq_pos_of_mem_dom {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (hr : 0 < r) {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (hx : x ∈ X.dom) : 0 < X.firstMinimumSq x := by
  classical
  obtain ⟨c0, C0, hc0, hb⟩ :=
    _root_.GlobalTheory.MajorantContinuity.compact_bounds X (isCompact_singleton (x := x)) (by simpa using hx)
  obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain ⟨τ0, hτ0⟩ : ∃ τ0 : E →+* ℂ, τ0 ∈ X.Ψ := by
    rcases mem_Ψ_or_conjugate_mem X σ with h | h
    · exact ⟨σ, h⟩
    · exact ⟨_, h⟩
  have hne : (Finset.univ : Finset X.Ψ).Nonempty := ⟨⟨τ0, hτ0⟩, Finset.mem_univ _⟩
  set m := Finset.univ.inf' hne X.c
  have hm : 0 < m := (Finset.lt_inf'_iff hne).2 (fun τ _ => _root_.ReciprocityTheory.ChartRestriction.G.FD.TwoSidedBoostBounds.c_pos X τ)
  let f : (Fin r → E) → ℝ := fun v => ∑ τ : X.Ψ, X.c τ * X.maj x τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) v)
  have hterm : ∀ v (τ : X.Ψ), 0 ≤ X.c τ * X.maj x τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) v) :=
    fun v τ => mul_nonneg (_root_.ReciprocityTheory.ChartRestriction.G.FD.TwoSidedBoostBounds.c_pos X τ).le (_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.maj_nonneg X hx τ _)
  have hfpos : ∀ v, v ≠ 0 → 0 < f v := by
    intro v hv
    have hemb : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ0 v ≠ 0 := by
      intro h; apply hv; ext i
      have := congrFun h i
      simpa [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb] using this
    have h1 : 0 < X.c ⟨τ0, hτ0⟩ * X.maj x ⟨τ0, hτ0⟩ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ0 v) :=
      mul_pos (_root_.ReciprocityTheory.ChartRestriction.G.FD.TwoSidedBoostBounds.c_pos X _) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.maj_pos X hx _ hemb)
    exact lt_of_lt_of_le h1 (Finset.single_le_sum (f := fun τ : X.Ψ =>
      X.c τ * X.maj x τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) v)) (fun τ _ => hterm v τ)
      (Finset.mem_univ _))
  obtain ⟨δ, hδ, hδf⟩ := exists_pos_lower_bound_of_finite
    ((finite_lattice_norm_emb_le X 1).inter_of_left {v | v ≠ 0}) f (fun v hv => hfpos v hv.2)
  have hlow : ∀ v ∈ X.Λ, v ≠ 0 → min δ (m * c0) ≤ f v := by
    intro v hvΛ hv0
    by_cases hsmall : ∀ τ : X.Ψ, ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) v‖ ≤ 1
    · exact le_trans (min_le_left _ _) (hδf v ⟨⟨hvΛ, hsmall⟩, hv0⟩)
    · push_neg at hsmall
      obtain ⟨τ, hτ⟩ := hsmall
      refine le_trans (min_le_right _ _) ?_
      have h1 : m * c0 ≤ X.c τ * X.maj x τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) v) := by
        have hmτ : m ≤ X.c τ := Finset.inf'_le _ (Finset.mem_univ τ)
        have h2 := (hb x rfl τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) v)).1
        have h3 : c0 ≤ c0 * ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) v‖ ^ 2 := by
          have : 1 ≤ ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) v‖ ^ 2 := by nlinarith
          nlinarith
        calc m * c0 ≤ X.c τ * c0 := mul_le_mul_of_nonneg_right hmτ hc0.le
          _ ≤ X.c τ * X.maj x τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) v) :=
            mul_le_mul_of_nonneg_left (by linarith) (_root_.ReciprocityTheory.ChartRestriction.G.FD.TwoSidedBoostBounds.c_pos X τ).le
      exact le_trans h1 (Finset.single_le_sum (f := fun τ : X.Ψ =>
        X.c τ * X.maj x τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (τ : E →+* ℂ) v)) (fun τ _ => hterm v τ)
        (Finset.mem_univ _))
  obtain ⟨v0, hv0Λ, hv00⟩ : ∃ v ∈ X.Λ, v ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hbot : (X.Λ : Set (Fin r → E)) ⊆ {0} := fun v hv => hcon v hv
    have := X.Λ_span
    rw [eq_top_iff] at this
    have h1 := this (Submodule.mem_top (x := fun _ : Fin r => (1 : E)))
    have h2 : Submodule.span E (X.Λ : Set (Fin r → E)) ≤ ⊥ := by
      rw [Submodule.span_le]; intro v hv; simpa using hbot hv
    have h3 := h2 h1
    rw [Submodule.mem_bot] at h3
    exact one_ne_zero (congrFun h3 ⟨0, hr⟩)
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.firstMinimumSq
  refine lt_of_lt_of_le (lt_min hδ (mul_pos hm hc0)) (le_csInf ⟨f v0, v0, hv0Λ, hv00, rfl⟩ ?_)
  rintro t ⟨v, hv, hv0, rfl⟩
  exact hlow v hv hv0

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

/- English proof (translation)
Unfold `_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.LineBundleFirstBoundGlobalGeneration`. Introduce `r X hr`. Use `⟨fun γ hγ x hx b hb => la1_lact_rmul_eq X hγ hx hb, ?_, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[la1_eq_sqrt_la1sq]`. Conclude with `Real.continuous_sqrt.comp_continuousOn (continuousOn_la1sq_dom X)`.

Rewrite using `[la1_eq_sqrt_la1sq]`. Conclude with `Real.sqrt_pos.2 (la1sq_pos_of_mem_dom X hr hx)`.
-/
theorem _root_.GlobalTheory.ClosedDiscontinuity.firstMinimum_invariant_continuous_pos_on_frames : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.LineBundleFirstBoundGlobalGeneration (E := E) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.LineBundleFirstBoundGlobalGeneration
  intro r X hr
  refine ⟨fun γ hγ x hx b hb => la1_lact_rmul_eq X hγ hx hb, ?_, fun x hx => ?_⟩
  · rw [la1_eq_sqrt_la1sq]
    exact Real.continuous_sqrt.comp_continuousOn (continuousOn_la1sq_dom X)
  · rw [la1_eq_sqrt_la1sq]
    exact Real.sqrt_pos.2 (la1sq_pos_of_mem_dom X hr hx)

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

/- English proof (translation)
Assemble the required witnesses or components as `⟨_root_.GlobalTheory.ClosedDiscontinuity.propDisc_closed, _root_.GlobalTheory.ClosedDiscontinuity.firstMinimum_invariant_continuous_pos_on_frames⟩`.
-/
theorem _root_.GlobalTheory.ClosedDiscontinuity.propDisc_and_la1GG :
    (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r), _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.PropDisc X) ∧ (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.LineBundleFirstBoundGlobalGeneration (E := E)) :=
  ⟨_root_.GlobalTheory.ClosedDiscontinuity.propDisc_closed, _root_.GlobalTheory.ClosedDiscontinuity.firstMinimum_invariant_continuous_pos_on_frames⟩

end GlobalTheory.ClosedDiscontinuity
