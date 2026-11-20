import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TransvectionPeriodicity

namespace ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra

open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma pnorm_eq (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.pnorm la P x = ‖P x‖ * X.nfac la x := rfl

/- English proof (translation)
The claim follows from `Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _`.
-/
lemma nfac_nonneg (la : Wt X.Ψ r) (x : Frame X.Ψ r) : 0 ≤ X.nfac la x :=
  Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _

/- English proof (translation)
Rewrite using `[pnorm_eq]`. Conclude with `mul_nonneg (norm_nonneg _) (nfac_nonneg X la x)`.
-/
lemma pnorm_nonneg (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : 0 ≤ X.pnorm la P x := by
  rw [pnorm_eq]
  exact mul_nonneg (norm_nonneg _) (nfac_nonneg X la x)

/- English proof (translation)
Introduce `h`. Establish `h1` using `(hx τ).2 i`. Rewrite `h1` using `[h, Complex.zero_re, mul_zero]`. Conclude with `lt_irrefl _ h1`.
-/
lemma dmin_ne {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (i : Fin (r + 1)) : dmin X.Gm x τ i ≠ 0 := by
  intro h
  have h1 := (hx τ).2 i
  rw [h, Complex.zero_re, mul_zero] at h1
  exact lt_irrefl _ h1

/- English proof (translation)
The claim follows from `norm_pos_iff.mpr (div_ne_zero (dmin_ne X hx τ _) (dmin_ne X hx τ _))`.
-/
lemma ratio_pos {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (i : Fin r) :
    0 < ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ :=
  norm_pos_iff.mpr (div_ne_zero (dmin_ne X hx τ _) (dmin_ne X hx τ _))

/- English proof (translation)
The claim follows from `Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (ratio_pos X hx τ i) _`.
-/
lemma nfac_pos {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la : Wt X.Ψ r) : 0 < X.nfac la x :=
  Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (ratio_pos X hx τ i) _

/- English proof (translation)
Unfold `Data.nfac`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← Real.rpow_add (ratio_pos X hx τ i)]`. Use `congr 1`. Simplify using `only [Pi.add_apply, Int.cast_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma nfac_add {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la la' : Wt X.Ψ r) :
    X.nfac (la + la') x = X.nfac la x * X.nfac la' x := by
  unfold Data.nfac
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Real.rpow_add (ratio_pos X hx τ i)]
  congr 1
  simp only [Pi.add_apply, Int.cast_add]
  ring

/- English proof (translation)
Simplify using `only [hermC, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma hermC_sub_smul_sub_smul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v w : Fin r → ℂ) (α β : ℂ) :
    hermC τ G (u - α • w) (v - β • w) = hermC τ G u v - starRingEnd ℂ β * hermC τ G u w -
      α * hermC τ G w v + α * starRingEnd ℂ β * hermC τ G w w := by
  simp only [hermC, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/- English proof (translation)
Establish `h` using `congrArg τ.1 hξ`. Rewrite `h` using `[map_zero]`. Rewrite using `[← h]`. Simplify using `only [hermC, herm, map_sum, map_mul]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Rewrite using `[cc, NumberField.IsCMField.complexEmbedding_complexConj (K := E)]`.
-/
private lemma hermC_emb_self_eq_zero_of_herm_self_eq_zero {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (τ : X.Ψ) :
    hermC τ.1 X.Gm (fun k => τ.1 (ξ k)) (fun k => τ.1 (ξ k)) = 0 := by
  have h := congrArg τ.1 hξ
  rw [map_zero] at h
  rw [← h]
  simp only [hermC, herm, map_sum, map_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [cc, NumberField.IsCMField.complexEmbedding_complexConj (K := E)]

/- English proof (translation)
Simplify using `only [hermC, map_sum, map_mul, Complex.conj_conj]`. Use `conv_lhs => rw [Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Establish `hG : τ.1 (X.Gm b a) = starRingEnd ℂ (τ.1 (X.Gm a b))`. Rewrite using `[← X.Gm_herm a b, cc, NumberField.IsCMField.complexEmbedding_complexConj (K := E)]`.

Rewrite using `[hG]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma hermC_eq_conj_hermC_swap' (τ : X.Ψ) (u v : Fin r → ℂ) :
    hermC τ.1 X.Gm u v = starRingEnd ℂ (hermC τ.1 X.Gm v u) := by
  simp only [hermC, map_sum, map_mul, Complex.conj_conj]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have hG : τ.1 (X.Gm b a) = starRingEnd ℂ (τ.1 (X.Gm a b)) := by
    rw [← X.Gm_herm a b, cc, NumberField.IsCMField.complexEmbedding_complexConj (K := E)]
  rw [hG]
  ring

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `only [col, Data.flowMat, Matrix.mul_apply, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, hermC, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]`. Use `congr 1`. Use `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma col_flowMat_mul (ξ : Fin r → E) (τ : X.Ψ) (s : ℂ) (M : Matrix (Fin r) (Fin r) ℂ)
    (a : Fin r) :
    col (X.flowMat ξ τ s * M) a = col M a -
      (I * X.c τ * s * hermC τ.1 X.Gm (col M a) (fun k => τ.1 (ξ k))) • (fun k => τ.1 (ξ k)) := by
  funext k
  simp only [col, Data.flowMat, Matrix.mul_apply, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, hermC, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun m _ => ?_
  ring

/- English proof (translation)
Establish `key : ∀ (M : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r), hermC τ.1 X.Gm (col (X.flowMat ξ τ (p τ) * M) a) (col (X.flowMat ξ τ (p τ) * M) b) = hermC τ.1 X.Gm (col M a) (col M b)`. Introduce `M a b`. Rewrite using `[col_flowMat_mul, col_flowMat_mul, hermC_sub_smul_sub_smul, hermC_emb_self_eq_zero_of_herm_self_eq_zero X hξ τ, hermC_eq_conj_hermC_swap' X τ (fun k => τ.1 (ξ k)) (col M b)]`. Simplify using `only [map_mul, Complex.conj_I, Complex.conj_ofReal]`. Expand and normalize the polynomial expressions, which then agree.

Unfold `dmin`. Use `congr 1`. Use extensionality with `a b`. Conclude with `key (mat x τ) a b`.
-/
lemma dmin_flow_real {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (p : X.Ψ → ℝ) (x : Frame X.Ψ r) (τ : X.Ψ)
    (i : Fin (r + 1)) : dmin X.Gm (X.flow ξ (cR X p) x) τ i = dmin X.Gm x τ i := by
  have key : ∀ (M : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r),
      hermC τ.1 X.Gm (col (X.flowMat ξ τ (p τ) * M) a) (col (X.flowMat ξ τ (p τ) * M) b) =
      hermC τ.1 X.Gm (col M a) (col M b) := by
    intro M a b
    rw [col_flowMat_mul, col_flowMat_mul, hermC_sub_smul_sub_smul, hermC_emb_self_eq_zero_of_herm_self_eq_zero X hξ τ,
      hermC_eq_conj_hermC_swap' X τ (fun k => τ.1 (ξ k)) (col M b)]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  unfold dmin
  congr 1
  ext a b
  exact key (mat x τ) a b

/- English proof (translation)
Unfold `Data.nfac`. Simplify using `only [dmin_flow_real X hξ]`.
-/
lemma nfac_flow_real {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (p : X.Ψ → ℝ) (la : Wt X.Ψ r)
    (x : Frame X.Ψ r) : X.nfac la (X.flow ξ (cR X p) x) = X.nfac la x := by
  unfold Data.nfac
  simp only [dmin_flow_real X hξ]

/- English proof (translation)
Take `⟨C, hC⟩` from `hP.2`. Establish `hsub : ∀ N : Matrix (Fin r) (Fin r) ℂ, N.submatrix (Fin.castLE (Nat.le_of_lt_succ (Fin.last r).isLt)) (Fin.castLE (Nat.le_of_lt_succ (Fin.last r).isLt)) = N`. Introduce `N`. Use extensionality with `a b`. Both sides reduce to the same expression.

Establish `hflow_dom : ∀ s : X.Ψ → ℝ, X.flow ξ (fun τ => (s τ : ℂ)) x ∈ X.dom`. Introduce `s τ`. Establish `hd : ∀ i, dmin X.Gm (X.flow ξ (fun τ => (s τ : ℂ)) x) τ i = dmin X.Gm x τ i` using `fun i => dmin_flow_real X hξ s x τ i`. Use `⟨?_, fun i => by rw [hd i]; exact (hx τ).2 i⟩` and prove the remaining obligations. Introduce `hdet`.

Establish `hlast : dmin X.Gm (X.flow ξ (fun τ => (s τ : ℂ)) x) τ (Fin.last r) ≠ 0`. Rewrite using `[hd]`. Conclude with `dmin_ne X hx τ _`. Apply `hlast` to reduce the goal to its premises. Unfold `dmin lminor`.

Rewrite using `[hsub]`. Establish `hg : gram τ.1 X.Gm (mat (X.flow ξ (fun τ => (s τ : ℂ)) x) τ) = (mat (X.flow ξ (fun τ => (s τ : ℂ)) x) τ).transpose * (X.Gm.map τ.1) * (mat (X.flow ξ (fun τ => (s τ : ℂ)) x) τ).map (starRingEnd ℂ)`. Use extensionality with `a b`. Simplify using `only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.

Rewrite using `[hg, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdet, zero_mul, zero_mul]`. Establish `hcont_flow : Continuous fun s : X.Ψ → ℝ => X.flow ξ (fun τ => (s τ : ℂ)) x`. Apply `continuous_pi` to reduce the goal to its premises. Introduce `τ`. Use `show Continuous fun s : X.Ψ → ℝ => (X.flowMat ξ τ (s τ : ℂ) * mat x τ : Matrix (Fin r) (Fin r) ℂ)`.

Use `Continuous.matrix_mul ?_ continuous_const` and prove the remaining obligations. Apply `continuous_pi` to reduce the goal to its premises. Introduce `a`. Apply `continuous_pi` to reduce the goal to its premises. Introduce `b`.

Use `show Continuous fun s : X.Ψ → ℝ => X.flowMat ξ τ (s τ : ℂ) a b`. Simplify using `only [Data.flowMat, Matrix.of_apply]`. Use `fun_prop`. Establish `hcont : Continuous fun s : X.Ψ → ℝ => P (X.flow ξ (fun τ => (s τ : ℂ)) x) * cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * s τ)` using `(hP.1.1.continuousOn.comp_continuous hcont_flow hflow_dom).mul (by fun_prop)`. Establish `hexp1 : ∀ s : X.Ψ → ℝ, ‖cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * s τ)‖ = 1`.

Introduce `s`. Establish `h2 : -(4 * (Real.pi : ℂ) * I) * ∑ τ, (ν τ : ℂ) * (s τ : ℂ) = ((-(4 * Real.pi * ∑ τ, ν τ * s τ) : ℝ) : ℂ) * I`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2, Complex.norm_exp_ofReal_mul_I]`.

Use `haveI : Fact (volume D < ⊤) := ⟨hD⟩`. Use `Integrable.mono' (integrable_const (C / X.nfac la x)) hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun s => ?_)` and prove the remaining obligations. Use `show ‖P (X.flow ξ (fun τ => (s τ : ℂ)) x) * cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * s τ)‖ ≤ C / X.nfac la x`. Rewrite using `[norm_mul, hexp1 s, mul_one]`. Establish `hnf : X.nfac la (X.flow ξ (fun τ => (s τ : ℂ)) x) = X.nfac la x` using `nfac_flow_real X hξ s la x`.

Establish `h1` using `hC _ (hflow_dom s)`. Rewrite `h1` using `[pnorm_eq, hnf]`. Conclude with `(le_div_iff₀ (nfac_pos X hx la)).mpr h1`.
-/
lemma integrableOn_fj {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : X.IsBddSec la P) {ξ : Fin r → E}
    (hξ : herm X.Gm ξ ξ = 0) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ν : X.Ψ → ℝ) {D : Set (X.Ψ → ℝ)}
    (hD : volume D < ⊤) :
    IntegrableOn (fun s : X.Ψ → ℝ => P (X.flow ξ (fun τ => (s τ : ℂ)) x) *
      cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * s τ)) D := by
  obtain ⟨C, hC⟩ := hP.2
  have hsub : ∀ N : Matrix (Fin r) (Fin r) ℂ,
      N.submatrix (Fin.castLE (Nat.le_of_lt_succ (Fin.last r).isLt))
        (Fin.castLE (Nat.le_of_lt_succ (Fin.last r).isLt)) = N := by
    intro N
    ext a b
    rfl

  have hflow_dom : ∀ s : X.Ψ → ℝ, X.flow ξ (fun τ => (s τ : ℂ)) x ∈ X.dom := by
    intro s τ
    have hd : ∀ i, dmin X.Gm (X.flow ξ (fun τ => (s τ : ℂ)) x) τ i = dmin X.Gm x τ i :=
      fun i => dmin_flow_real X hξ s x τ i
    refine ⟨?_, fun i => by rw [hd i]; exact (hx τ).2 i⟩
    intro hdet
    have hlast : dmin X.Gm (X.flow ξ (fun τ => (s τ : ℂ)) x) τ (Fin.last r) ≠ 0 := by
      rw [hd]
      exact dmin_ne X hx τ _
    apply hlast
    unfold dmin lminor
    rw [hsub]
    have hg : gram τ.1 X.Gm (mat (X.flow ξ (fun τ => (s τ : ℂ)) x) τ) =
        (mat (X.flow ξ (fun τ => (s τ : ℂ)) x) τ).transpose * (X.Gm.map τ.1) *
          (mat (X.flow ξ (fun τ => (s τ : ℂ)) x) τ).map (starRingEnd ℂ) := by
      ext a b
      simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
        Matrix.map_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
    rw [hg, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdet, zero_mul, zero_mul]

  have hcont_flow : Continuous fun s : X.Ψ → ℝ => X.flow ξ (fun τ => (s τ : ℂ)) x := by
    apply continuous_pi
    intro τ
    show Continuous fun s : X.Ψ → ℝ =>
      (X.flowMat ξ τ (s τ : ℂ) * mat x τ : Matrix (Fin r) (Fin r) ℂ)
    refine Continuous.matrix_mul ?_ continuous_const
    apply continuous_pi
    intro a
    apply continuous_pi
    intro b
    show Continuous fun s : X.Ψ → ℝ => X.flowMat ξ τ (s τ : ℂ) a b
    simp only [Data.flowMat, Matrix.of_apply]
    fun_prop
  have hcont : Continuous fun s : X.Ψ → ℝ => P (X.flow ξ (fun τ => (s τ : ℂ)) x) *
      cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * s τ) :=
    (hP.1.1.continuousOn.comp_continuous hcont_flow hflow_dom).mul (by fun_prop)
  have hexp1 : ∀ s : X.Ψ → ℝ, ‖cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * s τ)‖ = 1 := by
    intro s
    have h2 : -(4 * (Real.pi : ℂ) * I) * ∑ τ, (ν τ : ℂ) * (s τ : ℂ) =
        ((-(4 * Real.pi * ∑ τ, ν τ * s τ) : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [h2, Complex.norm_exp_ofReal_mul_I]
  haveI : Fact (volume D < ⊤) := ⟨hD⟩
  refine Integrable.mono' (integrable_const (C / X.nfac la x)) hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun s => ?_)
  show ‖P (X.flow ξ (fun τ => (s τ : ℂ)) x) * cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * s τ)‖ ≤
    C / X.nfac la x
  rw [norm_mul, hexp1 s, mul_one]
  have hnf : X.nfac la (X.flow ξ (fun τ => (s τ : ℂ)) x) = X.nfac la x := nfac_flow_real X hξ s la x
  have h1 := hC _ (hflow_dom s)
  rw [pnorm_eq, hnf] at h1
  exact (le_div_iff₀ (nfac_pos X hx la)).mpr h1

/- English proof (translation)
Unfold `Data.fj`. Use `split_ifs with h1 h2`. Establish `hP'` using `integrableOn_fj X hP hξ.2.1 hx ν h2.choose_spec.2.2.2`. Establish `hQ'` using `integrableOn_fj X hQ hξ.2.1 hx ν h2.choose_spec.2.2.2`. Simplify using `only [Pi.add_apply, add_mul]`.

Rewrite using `[MeasureTheory.integral_add hP' hQ', mul_add]`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
lemma fj_add {la : Wt X.Ψ r} {P Q : Frame X.Ψ r → ℂ} (hP : X.IsBddSec la P) (hQ : X.IsBddSec la Q)
    {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ν : X.Ψ → ℝ) :
    X.fj la ξ ν (P + Q) x = X.fj la ξ ν P x + X.fj la ξ ν Q x := by
  unfold Data.fj
  split_ifs with h1 h2
  · have hP' := integrableOn_fj X hP hξ.2.1 hx ν h2.choose_spec.2.2.2
    have hQ' := integrableOn_fj X hQ hξ.2.1 hx ν h2.choose_spec.2.2.2
    simp only [Pi.add_apply, add_mul]
    rw [MeasureTheory.integral_add hP' hQ', mul_add]
  · simp
  · simp

/- English proof (translation)
Unfold `Data.fj`. Use `split_ifs`. Simplify using `only [Pi.smul_apply, smul_eq_mul, mul_assoc, MeasureTheory.integral_const_mul]`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
lemma fj_smul (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (x : Frame X.Ψ r) (ν : X.Ψ → ℝ)
    (a : ℂ) : X.fj la ξ ν (a • P) x = a * X.fj la ξ ν P x := by
  unfold Data.fj
  split_ifs
  · simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, MeasureTheory.integral_const_mul]
    ring
  · simp
  · simp

/- English proof (translation)
Unfold `Data.fj`. Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma fj_zero (la : Wt X.Ψ r) (ξ : Fin r → E) (x : Frame X.Ψ r) (ν : X.Ψ → ℝ) :
    X.fj la ξ ν 0 x = 0 := by
  unfold Data.fj
  split_ifs <;> simp

/- English proof (translation)
Use `⟨⟨?_, fun x _ b _ => by simp, fun γ _ x _ => by simp⟩, 0, fun x _ => by simp [pnorm_eq]⟩` and prove the remaining obligations. Conclude with `differentiableOn_const 0`.
-/
lemma bdd_zero (la : Wt X.Ψ r) : X.IsBddSec la 0 := by
  refine ⟨⟨?_, fun x _ b _ => by simp, fun γ _ x _ => by simp⟩, 0, fun x _ => by simp [pnorm_eq]⟩
  exact differentiableOn_const 0

/- English proof (translation)
Take `⟨C1, hC1⟩` from `hP.2`. Take `⟨C2, hC2⟩` from `hQ.2`. Use `⟨⟨hP.1.1.add hQ.1.1, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩, C1 + C2, fun x hx => ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.add_apply, hP.1.2.1 x hx b hb, hQ.1.2.1 x hx b hb, mul_add]`. Simplify using `only [Pi.add_apply, hP.1.2.2 γ hγ x hx, hQ.1.2.2 γ hγ x hx, mul_add]`.

Establish `h1` using `hC1 x hx`. Establish `h2` using `hC2 x hx`. Rewrite `h1`, `h2`, the goal using `[pnorm_eq]`. Establish `hn` using `nfac_nonneg X la x`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma bdd_add {la : Wt X.Ψ r} {P Q : Frame X.Ψ r → ℂ} (hP : X.IsBddSec la P) (hQ : X.IsBddSec la Q) :
    X.IsBddSec la (P + Q) := by
  obtain ⟨C1, hC1⟩ := hP.2
  obtain ⟨C2, hC2⟩ := hQ.2
  refine ⟨⟨hP.1.1.add hQ.1.1, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩, C1 + C2, fun x hx => ?_⟩
  · simp only [Pi.add_apply, hP.1.2.1 x hx b hb, hQ.1.2.1 x hx b hb, mul_add]
  · simp only [Pi.add_apply, hP.1.2.2 γ hγ x hx, hQ.1.2.2 γ hγ x hx, mul_add]
  · have h1 := hC1 x hx
    have h2 := hC2 x hx
    rw [pnorm_eq] at h1 h2 ⊢
    have hn := nfac_nonneg X la x
    calc ‖(P + Q) x‖ * X.nfac la x ≤ (‖P x‖ + ‖Q x‖) * X.nfac la x :=
          mul_le_mul_of_nonneg_right (norm_add_le _ _) hn
      _ = ‖P x‖ * X.nfac la x + ‖Q x‖ * X.nfac la x := add_mul _ _ _
      _ ≤ C1 + C2 := add_le_add h1 h2

/- English proof (translation)
Take `⟨C, hC⟩` from `hP.2`. Use `⟨⟨hP.1.1.const_smul a, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩, ‖a‖ * C, fun x hx => ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, smul_eq_mul, hP.1.2.1 x hx b hb]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Pi.smul_apply, smul_eq_mul, hP.1.2.2 γ hγ x hx]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h1` using `hC x hx`. Rewrite `h1`, the goal using `[pnorm_eq]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_left h1 (norm_nonneg a)`.
-/
lemma bdd_smul {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (a : ℂ) (hP : X.IsBddSec la P) :
    X.IsBddSec la (a • P) := by
  obtain ⟨C, hC⟩ := hP.2
  refine ⟨⟨hP.1.1.const_smul a, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩, ‖a‖ * C, fun x hx => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, hP.1.2.1 x hx b hb]
    ring
  · simp only [Pi.smul_apply, smul_eq_mul, hP.1.2.2 γ hγ x hx]
    ring
  · have h1 := hC x hx
    rw [pnorm_eq] at h1 ⊢
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left h1 (norm_nonneg a)

/- English proof (translation)
Unfold `bchar`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Establish `hdet` using `(hb τ).1`. Establish `htri : (mat b τ).BlockTriangular id`. Introduce `a c h`. Conclude with `(hb τ).2 a c h`. Rewrite `hdet` using `[Matrix.det_of_upperTriangular htri]`.

Establish `hi : b τ i i ≠ 0` using `(Finset.prod_ne_zero_iff.mp hdet) i (Finset.mem_univ i)`. Rewrite using `[Pi.add_apply, Pi.add_apply, zpow_add₀ hi]`.
-/
lemma bchar_add {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (la la' : Wt X.Ψ r) :
    bchar (la + la') b = bchar la b * bchar la' b := by
  unfold bchar
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hdet := (hb τ).1
  have htri : (mat b τ).BlockTriangular id := by
    intro a c h
    exact (hb τ).2 a c h
  rw [Matrix.det_of_upperTriangular htri] at hdet
  have hi : b τ i i ≠ 0 := (Finset.prod_ne_zero_iff.mp hdet) i (Finset.mem_univ i)
  rw [Pi.add_apply, Pi.add_apply, zpow_add₀ hi]

/- English proof (translation)
Take `⟨C1, hC1⟩` from `hP.2`. Take `⟨C2, hC2⟩` from `hQ.2`. Use `⟨⟨hP.1.1.mul hQ.1.1, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩, C1 * C2, fun x hx => ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.mul_apply, hP.1.2.1 x hx b hb, hQ.1.2.1 x hx b hb, bchar_add X hb]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [Pi.mul_apply, hP.1.2.2 γ hγ x hx, hQ.1.2.2 γ hγ x hx, X.χ_add la la' γ hγ]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1` using `hC1 x hx`. Establish `h2` using `hC2 x hx`. Establish `hQn` using `pnorm_nonneg X la' Q x`.

Establish `hPn` using `pnorm_nonneg X la P x`. Establish `heq : X.pnorm (la + la') (P * Q) x = X.pnorm la P x * X.pnorm la' Q x`. Rewrite using `[pnorm_eq, pnorm_eq, pnorm_eq, nfac_add X hx, Pi.mul_apply, norm_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[heq]`.

Conclude with `mul_le_mul h1 h2 hQn (hPn.trans h1)`.
-/
lemma bdd_mul {la la' : Wt X.Ψ r} {P Q : Frame X.Ψ r → ℂ} (hP : X.IsBddSec la P) (hQ : X.IsBddSec la' Q) :
    X.IsBddSec (la + la') (P * Q) := by
  obtain ⟨C1, hC1⟩ := hP.2
  obtain ⟨C2, hC2⟩ := hQ.2
  refine ⟨⟨hP.1.1.mul hQ.1.1, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩, C1 * C2, fun x hx => ?_⟩
  · simp only [Pi.mul_apply, hP.1.2.1 x hx b hb, hQ.1.2.1 x hx b hb, bchar_add X hb]
    ring
  · simp only [Pi.mul_apply, hP.1.2.2 γ hγ x hx, hQ.1.2.2 γ hγ x hx, X.χ_add la la' γ hγ]
    ring
  · have h1 := hC1 x hx
    have h2 := hC2 x hx
    have hQn := pnorm_nonneg X la' Q x
    have hPn := pnorm_nonneg X la P x
    have heq : X.pnorm (la + la') (P * Q) x = X.pnorm la P x * X.pnorm la' Q x := by
      rw [pnorm_eq, pnorm_eq, pnorm_eq, nfac_add X hx, Pi.mul_apply, norm_mul]
      ring
    rw [heq]
    exact mul_le_mul h1 h2 hQn (hPn.trans h1)

/- English proof (translation)
Take `⟨C, hC⟩` from `hP.2`. Use `⟨C, 0, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[neg_zero, Real.rpow_zero, mul_one]`. Conclude with `hC x hx`.
-/
lemma mod_of_bdd {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : X.IsBddSec la P) : X.IsModerate la P := by
  obtain ⟨C, hC⟩ := hP.2
  refine ⟨C, 0, fun x hx => ?_⟩
  rw [neg_zero, Real.rpow_zero, mul_one]
  exact hC x hx

/- English proof (translation)
Take `⟨C, A, hCA⟩` from `mod_of_bdd X hP`. Conclude with `(h3d r X la P C A hP.1 hCA).1 ξ hξ ν x hx h`.
-/
lemma sign_of_bdd (h3d : ModerateCoefficientPositivity (E := E)) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ}
    (hP : X.IsBddSec la P) {ξ : Fin r → E} (hξ : X.IsIso ξ) (ν : X.Ψ → ℝ) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (h : X.fj la ξ ν P x ≠ 0) : ∀ τ, 0 ≤ ν τ := by
  obtain ⟨C, A, hCA⟩ := mod_of_bdd X hP
  exact (h3d r X la P C A hP.1 hCA).1 ξ hξ ν x hx h

/- English proof (translation)
Establish `hs` using `h3e r X la la' P Q hP.1 hQ.1 (mod_of_bdd X hP) (mod_of_bdd X hQ) ξ hξ x hx ν`. Establish `hz : (fun ν' : X.Ψ → ℝ => X.fj la ξ ν' P x * X.fj la' ξ (ν - ν') Q x) = 0`. Use function extensionality and compare the values at `ν'`. Distinguish the cases in `h1 : X.fj la ξ ν' P x = 0`. Simplify using `[h1]`.

Distinguish the cases in `h2 : X.fj la' ξ (ν - ν') Q x = 0`. Simplify using `[h2]`. It suffices to derive a contradiction. Apply `h1` to reduce the goal to its premises. Apply `hvan ν' (sign_of_bdd X h3d hP hξ ν' hx h1)` to reduce the goal to its premises.

Introduce `τ`. Establish `h3` using `sign_of_bdd X h3d hQ hξ (ν - ν') hx h2 τ`. Simplify using `using h3`. Rewrite `hs` using `[hz]`. Conclude with `hs.unique hasSum_zero`.
-/
lemma fj_mul_zero (h3d : ModerateCoefficientPositivity (E := E)) (h3e : CoefficientConvolution (E := E)) {la la' : Wt X.Ψ r}
    {P Q : Frame X.Ψ r → ℂ} (hP : X.IsBddSec la P) (hQ : X.IsBddSec la' Q) {ξ : Fin r → E}
    (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ν : X.Ψ → ℝ)
    (hvan : ∀ ν' : X.Ψ → ℝ, (∀ τ, 0 ≤ ν' τ) → (∀ τ, 0 ≤ ν τ - ν' τ) → X.fj la ξ ν' P x = 0) :
    X.fj (la + la') ξ ν (P * Q) x = 0 := by
  have hs := h3e r X la la' P Q hP.1 hQ.1 (mod_of_bdd X hP) (mod_of_bdd X hQ) ξ hξ x hx ν
  have hz : (fun ν' : X.Ψ → ℝ => X.fj la ξ ν' P x * X.fj la' ξ (ν - ν') Q x) = 0 := by
    funext ν'
    by_cases h1 : X.fj la ξ ν' P x = 0
    · simp [h1]
    by_cases h2 : X.fj la' ξ (ν - ν') Q x = 0
    · simp [h2]
    exfalso
    apply h1
    apply hvan ν' (sign_of_bdd X h3d hP hξ ν' hx h1)
    intro τ
    have h3 := sign_of_bdd X h3d hQ hξ (ν - ν') hx h2 τ
    simpa using h3
  rw [hz] at hs
  exact hs.unique hasSum_zero

/- English proof (translation)
Introduce `r X la la' c`. Establish `hSSmul : ∀ P ∈ X.SS la, ∀ Q, X.IsBddSec la' Q → P * Q ∈ X.SS (la + la')`. Introduce `P hP Q hQ`. Use `⟨bdd_mul X hP.1 hQ, fun ξ hξ x hx => ?_⟩` and prove the remaining obligations. Use `fj_mul_zero X h3d h3e hP.1 hQ hξ hx 0 fun ν' h0 h1 => ?_` and prove the remaining obligations.

Establish `hν' : ν' = 0`. Use function extensionality and compare the values at `τ`. Establish `h2` using `h1 τ`. Simplify using `only [Pi.zero_apply] at h2 ⊢`. Combine the linear relations using `[h0 τ]`.

Rewrite using `[hν']`. Conclude with `hP.2 ξ hξ x hx`. Use `⟨⟨⟨bdd_zero X la, fun ξ _ x _ => fj_zero X la ξ x 0⟩, ?_, ?_⟩, hSSmul, ⟨?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `P hP Q hQ`. Use `⟨bdd_add X hP.1 hQ.1, fun ξ hξ x hx => ?_⟩` and prove the remaining obligations.

Rewrite using `[fj_add X hP.1 hQ.1 hξ hx, hP.2 ξ hξ x hx, hQ.2 ξ hξ x hx, add_zero]`. Introduce `a P hP`. Use `⟨bdd_smul X a hP.1, fun ξ hξ x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[fj_smul, hP.2 ξ hξ x hx, mul_zero]`. Conclude with `⟨⟨bdd_zero X la, fun ξ _ x _ => fj_zero X la ξ x 0⟩, fun ξ _ ν _ x _ => fj_zero X la ξ x ν⟩`.

Introduce `P hP Q hQ`. Use `⟨⟨bdd_add X hP.1.1 hQ.1.1, fun ξ hξ x hx => ?_⟩, fun ξ hξ ν hν x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[fj_add X hP.1.1 hQ.1.1 hξ hx, hP.1.2 ξ hξ x hx, hQ.1.2 ξ hξ x hx, add_zero]`. Rewrite using `[fj_add X hP.1.1 hQ.1.1 hξ hx, hP.2 ξ hξ ν hν x hx, hQ.2 ξ hξ ν hν x hx, add_zero]`. Introduce `a P hP`.

Use `⟨⟨bdd_smul X a hP.1.1, fun ξ hξ x hx => ?_⟩, fun ξ hξ ν hν x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[fj_smul, hP.1.2 ξ hξ x hx, mul_zero]`. Rewrite using `[fj_smul, hP.2 ξ hξ ν hν x hx, mul_zero]`. Introduce `P hP Q hQ`. Use `⟨hSSmul P hP.1 Q hQ, fun ξ hξ ν hν x hx => ?_⟩` and prove the remaining obligations.

Use `fj_mul_zero X h3d h3e hP.1.1 hQ hξ hx ν fun ν' h0 h1 => ?_` and prove the remaining obligations. Use `hP.2 ξ hξ ν' ?_ x hx` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem siegelSpaceAlgebra_of (h3d : ModerateCoefficientPositivity (E := E)) (h3e : CoefficientConvolution (E := E)) : SiegelSpaceAlgebra (E := E) := by
  intro r X la la' c
  have hSSmul : ∀ P ∈ X.SS la, ∀ Q, X.IsBddSec la' Q → P * Q ∈ X.SS (la + la') := by
    intro P hP Q hQ
    refine ⟨bdd_mul X hP.1 hQ, fun ξ hξ x hx => ?_⟩
    refine fj_mul_zero X h3d h3e hP.1 hQ hξ hx 0 fun ν' h0 h1 => ?_
    have hν' : ν' = 0 := by
      funext τ
      have h2 := h1 τ
      simp only [Pi.zero_apply] at h2 ⊢
      linarith [h0 τ]
    rw [hν']
    exact hP.2 ξ hξ x hx
  refine ⟨⟨⟨bdd_zero X la, fun ξ _ x _ => fj_zero X la ξ x 0⟩, ?_, ?_⟩, hSSmul, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro P hP Q hQ
    refine ⟨bdd_add X hP.1 hQ.1, fun ξ hξ x hx => ?_⟩
    rw [fj_add X hP.1 hQ.1 hξ hx, hP.2 ξ hξ x hx, hQ.2 ξ hξ x hx, add_zero]
  · intro a P hP
    refine ⟨bdd_smul X a hP.1, fun ξ hξ x hx => ?_⟩
    rw [fj_smul, hP.2 ξ hξ x hx, mul_zero]
  · exact ⟨⟨bdd_zero X la, fun ξ _ x _ => fj_zero X la ξ x 0⟩, fun ξ _ ν _ x _ => fj_zero X la ξ x ν⟩
  · intro P hP Q hQ
    refine ⟨⟨bdd_add X hP.1.1 hQ.1.1, fun ξ hξ x hx => ?_⟩, fun ξ hξ ν hν x hx => ?_⟩
    · rw [fj_add X hP.1.1 hQ.1.1 hξ hx, hP.1.2 ξ hξ x hx, hQ.1.2 ξ hξ x hx, add_zero]
    · rw [fj_add X hP.1.1 hQ.1.1 hξ hx, hP.2 ξ hξ ν hν x hx, hQ.2 ξ hξ ν hν x hx, add_zero]
  · intro a P hP
    refine ⟨⟨bdd_smul X a hP.1.1, fun ξ hξ x hx => ?_⟩, fun ξ hξ ν hν x hx => ?_⟩
    · rw [fj_smul, hP.1.2 ξ hξ x hx, mul_zero]
    · rw [fj_smul, hP.2 ξ hξ ν hν x hx, mul_zero]
  · intro P hP Q hQ
    refine ⟨hSSmul P hP.1 Q hQ, fun ξ hξ ν hν x hx => ?_⟩
    refine fj_mul_zero X h3d h3e hP.1.1 hQ hξ hx ν fun ν' h0 h1 => ?_
    refine hP.2 ξ hξ ν' ?_ x hx
    calc ∑ τ, ν' τ ≤ ∑ τ, ν τ := Finset.sum_le_sum fun τ _ => by linarith [h1 τ]
      _ ≤ c := hν

end

end ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra
