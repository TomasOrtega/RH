import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.RhGradStatementPfB

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.RgE

open Matrix Topology Filter
open scoped ComplexOrder Matrix ContDiff
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD ReciprocityTheory.ChartRestriction.G.AR.Up.RgC

variable {f p q : ℕ}

/- English proof (translation)
Establish `hZ : ∀ a b, ContDiff ℝ ∞ (fun v : V (nD f p q) => Zof v k a b)`. Introduce `a b`. Unfold `Zof`. Simplify using `only [Matrix.of_apply]`. Conclude with `((EuclideanSpace.proj (𝕜 := ℂ) (finProdFinEquiv (k, finProdFinEquiv (a, b)))).contDiff).restrict_scalars ℝ`.

Establish `hM : ∀ a b, ContDiff ℝ ∞ (fun v : V (nD f p q) => (1 - Zof v k * (Zof v k)ᴴ : Matrix (Fin p) (Fin p) ℂ) a b)`. Introduce `a b`. Simplify using `only [Matrix.sub_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]`. Conclude with `contDiff_const.sub (ContDiff.sum fun c _ => (hZ a c).mul (Complex.conjCLE.contDiff.comp (hZ b c)))`. Establish `hdet : ContDiff ℝ ∞ (fun v : V (nD f p q) => (1 - Zof v k * (Zof v k)ᴴ).det)`.

Simplify using `only [Matrix.det_apply']`. Conclude with `ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => hM (σ i) i)`. Unfold `dk`. Conclude with `Complex.reCLM.contDiff.comp hdet`.
-/
theorem dkV_contDiff (k : Fin f) :
    ContDiff ℝ ∞ (fun v : V (nD f p q) => dk v k) := by
  have hZ : ∀ a b, ContDiff ℝ ∞ (fun v : V (nD f p q) => Zof v k a b) := by
    intro a b
    unfold Zof
    simp only [Matrix.of_apply]
    exact ((EuclideanSpace.proj (𝕜 := ℂ)
      (finProdFinEquiv (k, finProdFinEquiv (a, b)))).contDiff).restrict_scalars ℝ
  have hM : ∀ a b, ContDiff ℝ ∞ (fun v : V (nD f p q) =>
      (1 - Zof v k * (Zof v k)ᴴ : Matrix (Fin p) (Fin p) ℂ) a b) := by
    intro a b
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    exact contDiff_const.sub (ContDiff.sum fun c _ => (hZ a c).mul (Complex.conjCLE.contDiff.comp (hZ b c)))
  have hdet : ContDiff ℝ ∞ (fun v : V (nD f p q) => (1 - Zof v k * (Zof v k)ᴴ).det) := by
    simp only [Matrix.det_apply']
    exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => hM (σ i) i)
  unfold dk
  exact Complex.reCLM.contDiff.comp hdet

/- English proof (translation)
Use function extensionality and compare the values at `y`. Establish `h : (fun y => (((g y - K : ℝ)) : ℂ)) = fun y => ((g y : ℝ) : ℂ) - (K : ℂ)`. Use function extensionality and compare the values at `z`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h, fderiv_sub_const]`.
-/
private lemma fderiv_ofReal_sub_const {n : ℕ} (g : V n → ℝ) (K : ℝ) :
    fderiv ℝ (fun y => (((g y - K : ℝ)) : ℂ)) = fderiv ℝ (fun y => ((g y : ℝ) : ℂ)) := by
  funext y
  have h : (fun y => (((g y - K : ℝ)) : ℂ)) = fun y => ((g y : ℝ) : ℂ) - (K : ℂ) := by
    funext z
    push_cast
    ring
  rw [h, fderiv_sub_const]

/- English proof (translation)
Unfold `wd`. Rewrite using `[fderiv_ofReal_sub_const]`.
-/
private lemma wd_ofReal_sub_const {n : ℕ} (g : V n → ℝ) (K : ℝ) (j : Fin n) (y : V n) :
    wd n j (fun y => (((g y - K : ℝ)) : ℂ)) y = wd n j (fun y => ((g y : ℝ) : ℂ)) y := by
  unfold wd
  rw [fderiv_ofReal_sub_const]

/- English proof (translation)
Establish `h : ∀ k, wdb n k (fun y => (((g y - K : ℝ)) : ℂ)) = wdb n k (fun y => ((g y : ℝ) : ℂ))`. Introduce `k`. Use function extensionality and compare the values at `z`. Unfold `wdb`. Rewrite using `[fderiv_ofReal_sub_const]`.

Unfold `leviV`. Simplify using `only [h]`.
-/
private lemma leviV_ofReal_sub_const {n : ℕ} (g : V n → ℝ) (K : ℝ) (y : V n) (ξ : Fin n → ℂ) :
    leviV n (fun y => (((g y - K : ℝ)) : ℂ)) y ξ = leviV n (fun y => ((g y : ℝ) : ℂ)) y ξ := by
  have h : ∀ k, wdb n k (fun y => (((g y - K : ℝ)) : ℂ)) = wdb n k (fun y => ((g y : ℝ) : ℂ)) := by
    intro k
    funext z
    unfold wdb
    rw [fderiv_ofReal_sub_const]
  unfold leviV
  simp only [h]

/- English proof (translation)
Establish `hf0 : (f : ℝ) ≠ 0` using `by exact_mod_cast hf.ne'`. Establish `hfR : (0 : ℝ) < (f : ℝ)` using `by exact_mod_cast hf`. Establish `hmR : (0 : ℝ) < ((min p q : ℕ) : ℝ)` using `by exact_mod_cast hm`. Establish `hm0 : ((min p q : ℕ) : ℝ) ≠ 0` using `hmR.ne'`. Establish `hC_eq : (((f * min p q : ℕ)) : ℝ) = (f : ℝ) * ((min p q : ℕ) : ℝ)` using `by push_cast; ring`.

Establish `hCpos : (0 : ℝ) < ((f * min p q : ℕ) : ℝ)` using `by rw [hC_eq]; positivity`. Use `haveI : Nonempty (Fin f) := ⟨⟨0, hf⟩⟩`. Use `choose Q hQc hQL hQ0 hQle using fun k : Fin f => RgD.block hm hv0 k`. Establish `hdk : ∀ v ∈ Dset f p q, ∀ k, 0 < dk v k`. Introduce `v hv k`.

Establish `hv' : ∀ k, (1 - Zof v k * (Zof v k)ᴴ).PosDef` using `hv`. Establish `h` using `(hv' k).det_pos`. Conclude with `(Complex.pos_iff.mp h).1`. Establish `hkey : ∀ v ∈ Dset f p q, 0 < ∑ k, Q k v ∧ -((f * min p q : ℕ) : ℝ) * Real.log (∑ k, Q k v) ≤ rh v - (rh v0 + ((f * min p q : ℕ) : ℝ) * Real.log ((f * min p q : ℕ) : ℝ))`. Introduce `v hv`.

Establish `ht : ∀ k, 0 < Q k v / ((min p q : ℕ) : ℝ)`. Introduce `k`. Establish `h1` using `hQle k v hv`. Establish `ha : 0 < dk v k ^ (((min p q : ℕ) : ℝ)⁻¹)` using `Real.rpow_pos_of_pos (hdk v hv k) _`. Establish `ha0 : 0 < dk v0 k ^ (((min p q : ℕ) : ℝ)⁻¹)` using `Real.rpow_pos_of_pos (hdk v0 hv0 k) _`.

Assume the negation of the conclusion as `hneg`. Use `push_neg at hneg`. Establish `h2 : dk v0 k ^ (((min p q : ℕ) : ℝ)⁻¹) * (Q k v / ((min p q : ℕ) : ℝ)) ≤ 0` using `mul_nonpos_of_nonneg_of_nonpos ha0.le hneg`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlog : ∀ k, Real.log (dk v k) ≤ Real.log (dk v0 k) + ((min p q : ℕ) : ℝ) * Real.log (Q k v / ((min p q : ℕ) : ℝ))`.

Introduce `k`. Establish `h1` using `hQle k v hv`. Establish `ha : 0 < dk v k ^ (((min p q : ℕ) : ℝ)⁻¹)` using `Real.rpow_pos_of_pos (hdk v hv k) _`. Establish `h2` using `Real.log_le_log ha h1`. Rewrite `h2` using `[Real.log_mul (Real.rpow_pos_of_pos (hdk v0 hv0 k) _).ne' (ht k).ne', Real.log_rpow (hdk v hv k), Real.log_rpow (hdk v0 hv0 k)]`.

Establish `h3` using `mul_le_mul_of_nonneg_left h2 hmR.le`. Establish `hmm : ((min p q : ℕ) : ℝ) * ((min p q : ℕ) : ℝ)⁻¹ = 1` using `mul_inv_cancel₀ hm0`. Rewrite `h3` using `[mul_add, ← mul_assoc, ← mul_assoc, hmm]`. Simplify `h3` using `only [one_mul]`. Establish `hQpos : ∀ k, 0 < Q k v` using `fun k => (div_pos_iff_of_pos_right hmR).mp (ht k)`.

Establish `hSpos : 0 < ∑ k, Q k v` using `Finset.sum_pos (fun k _ => hQpos k) Finset.univ_nonempty`. Use `⟨hSpos, ?_⟩` and prove the remaining obligations. Establish `hJ : ∑ k, (f : ℝ)⁻¹ • Real.log (Q k v / ((min p q : ℕ) : ℝ)) ≤ Real.log (∑ k, (f : ℝ)⁻¹ • (Q k v / ((min p q : ℕ) : ℝ)))` using `(strictConcaveOn_log_Ioi.concaveOn).le_map_sum (fun _ _ => inv_nonneg.mpr hfR.le) (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Conclude with `mul_inv_cancel₀ hf0)`. Use the proof step `(fun k _ => ht k)`.

Establish `hS : ∑ k, (f : ℝ)⁻¹ • (Q k v / ((min p q : ℕ) : ℝ)) = (∑ k, Q k v) / ((f * min p q : ℕ) : ℝ)`. Rewrite using `[Finset.sum_div]`. Use `Finset.sum_congr rfl (fun k _ => ?_)` and prove the remaining obligations. Rewrite using `[smul_eq_mul, hC_eq]`. Clear the denominators using the available nonvanishing facts.

Establish `hL : ∑ k, (f : ℝ)⁻¹ • Real.log (Q k v / ((min p q : ℕ) : ℝ)) = (f : ℝ)⁻¹ * ∑ k, Real.log (Q k v / ((min p q : ℕ) : ℝ))`. Simplify using `only [smul_eq_mul, Finset.mul_sum]`. Rewrite `hJ` using `[hS, hL, Real.log_div hSpos.ne' hCpos.ne']`. Establish `hsum : ∑ k, Real.log (dk v k) ≤ ∑ k, Real.log (dk v0 k) + ((min p q : ℕ) : ℝ) * ∑ k, Real.log (Q k v / ((min p q : ℕ) : ℝ))`. Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib]`.

Conclude with `Finset.sum_le_sum fun k _ => hlog k`. Establish `hmX : ((min p q : ℕ) : ℝ) * ∑ k, Real.log (Q k v / ((min p q : ℕ) : ℝ)) = ((f * min p q : ℕ) : ℝ) * ((f : ℝ)⁻¹ * ∑ k, Real.log (Q k v / ((min p q : ℕ) : ℝ)))`. Rewrite using `[hC_eq]`. Clear the denominators using the available nonvanishing facts. Establish `hCJ : ((f * min p q : ℕ) : ℝ) * ((f : ℝ)⁻¹ * ∑ k, Real.log (Q k v / ((min p q : ℕ) : ℝ))) ≤ ((f * min p q : ℕ) : ℝ) * Real.log (∑ k, Q k v) - ((f * min p q : ℕ) : ℝ) * Real.log ((f * min p q : ℕ) : ℝ)`.

Rewrite using `[← mul_sub]`. Conclude with `mul_le_mul_of_nonneg_left hJ hCpos.le`. Establish `hrv : rh v = -∑ k, Real.log (dk v k)` using `rfl`. Establish `hrv0 : rh v0 = -∑ k, Real.log (dk v0 k)` using `rfl`. Rewrite using `[hrv, hrv0]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hle : ∀ᶠ v in 𝓝 v0, -((f * min p q : ℕ) : ℝ) * Real.log (∑ k, Q k v) ≤ rh v - (rh v0 + ((f * min p q : ℕ) : ℝ) * Real.log ((f * min p q : ℕ) : ℝ))` using `by filter_upwards [(isOpen_Dset f p q).mem_nhds hv0] with v hv using (hkey v hv).2`. Establish `h2c : ∀ {g : V (nD f p q) → ℝ}, ContDiff ℝ ∞ g → ContDiffAt ℝ 2 g v0` using `fun hg => by`. Simplify using `using (contDiff_infty.mp hg 2).contDiffAt`. Establish `hrhc : ContDiffAt ℝ 2 (fun v : V (nD f p q) => rh v - (rh v0 + ((f * min p q : ℕ) : ℝ) * Real.log ((f * min p q : ℕ) : ℝ))) v0`.

Establish `h1 : ContDiffAt ℝ 2 (fun v : V (nD f p q) => -∑ k, Real.log (dk v k)) v0`. Use `ContDiffAt.neg (ContDiffAt.sum fun k _ => ?_)` and prove the remaining obligations. Conclude with `(h2c (dkV_contDiff k)).log (hdk v0 hv0 k).ne'`. Conclude with `h1.sub contDiffAt_const`. Establish `hΨc : ContDiffAt ℝ 2 (fun v : V (nD f p q) => ∑ k, Q k v) v0` using `ContDiffAt.sum fun k _ => h2c (hQc k)`.

Establish `hLev : (leviV (nD f p q) (fun y => ((∑ k, Q k y : ℝ) : ℂ)) v0 ξ).re ≤ 0`. Rewrite using `[leviV_ofReal_sum (fun k => h2c (hQc k)) ξ, Complex.re_sum]`. Conclude with `Finset.sum_nonpos fun k _ => hQL k ξ`. Establish `hSv0 : ∑ k, Q k v0 = ((f * min p q : ℕ) : ℝ)`. Simplify using `only [hQ0, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`.

Rewrite using `[hC_eq]`. Establish `heq : rh v0 - (rh v0 + ((f * min p q : ℕ) : ℝ) * Real.log ((f * min p q : ℕ) : ℝ)) = -((f * min p q : ℕ) : ℝ) * Real.log (∑ k, Q k v0)`. Rewrite using `[hSv0]`. Expand and normalize the polynomial expressions, which then agree. Establish `hmain` using `RgA.grad_le_of_minorant (fun v : V (nD f p q) => rh v - (rh v0 + ((f * min p q : ℕ) : ℝ) * Real.log ((f * min p q : ℕ) : ℝ))) (fun v : V (nD f p q) => ∑ k, Q k v) v0 ((f * min p q : ℕ) : ℝ) hCpos (hkey v0 hv0).1 hrhc hΨc ξ hLev hle heq`.

Simplify using `only [wd_ofReal_sub_const (fun w : V (nD f p q) => rh w), leviV_ofReal_sub_const (fun w : V (nD f p q) => rh w)] at hmain`. Conclude with `hmain`.
-/
theorem rhGrad_main (hf : 0 < f) (hm : 0 < min p q) (v0 : V (nD f p q)) (hv0 : v0 ∈ Dset f p q)
    (ξ : Fin (nD f p q) → ℂ) :
    Complex.normSq (∑ j, wd (nD f p q) j (fun w => ((rh w : ℝ) : ℂ)) v0 * ξ j) ≤
      ((f * min p q : ℕ) : ℝ) * (leviV (nD f p q) (fun w => ((rh w : ℝ) : ℂ)) v0 ξ).re := by
  classical
  have hf0 : (f : ℝ) ≠ 0 := by exact_mod_cast hf.ne'
  have hfR : (0 : ℝ) < (f : ℝ) := by exact_mod_cast hf
  have hmR : (0 : ℝ) < ((min p q : ℕ) : ℝ) := by exact_mod_cast hm
  have hm0 : ((min p q : ℕ) : ℝ) ≠ 0 := hmR.ne'
  have hC_eq : (((f * min p q : ℕ)) : ℝ) = (f : ℝ) * ((min p q : ℕ) : ℝ) := by push_cast; ring
  have hCpos : (0 : ℝ) < ((f * min p q : ℕ) : ℝ) := by rw [hC_eq]; positivity
  haveI : Nonempty (Fin f) := ⟨⟨0, hf⟩⟩
  choose Q hQc hQL hQ0 hQle using fun k : Fin f => RgD.block hm hv0 k
  have hdk : ∀ v ∈ Dset f p q, ∀ k, 0 < dk v k := by
    intro v hv k
    have hv' : ∀ k, (1 - Zof v k * (Zof v k)ᴴ).PosDef := hv
    have h := (hv' k).det_pos
    exact (Complex.pos_iff.mp h).1
  have hkey : ∀ v ∈ Dset f p q, 0 < ∑ k, Q k v ∧
      -((f * min p q : ℕ) : ℝ) * Real.log (∑ k, Q k v) ≤
        rh v - (rh v0 + ((f * min p q : ℕ) : ℝ) * Real.log ((f * min p q : ℕ) : ℝ)) := by
    intro v hv
    have ht : ∀ k, 0 < Q k v / ((min p q : ℕ) : ℝ) := by
      intro k
      have h1 := hQle k v hv
      have ha : 0 < dk v k ^ (((min p q : ℕ) : ℝ)⁻¹) := Real.rpow_pos_of_pos (hdk v hv k) _
      have ha0 : 0 < dk v0 k ^ (((min p q : ℕ) : ℝ)⁻¹) := Real.rpow_pos_of_pos (hdk v0 hv0 k) _
      by_contra hneg
      push_neg at hneg
      have h2 : dk v0 k ^ (((min p q : ℕ) : ℝ)⁻¹) * (Q k v / ((min p q : ℕ) : ℝ)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos ha0.le hneg
      linarith
    have hlog : ∀ k, Real.log (dk v k) ≤
        Real.log (dk v0 k) + ((min p q : ℕ) : ℝ) * Real.log (Q k v / ((min p q : ℕ) : ℝ)) := by
      intro k
      have h1 := hQle k v hv
      have ha : 0 < dk v k ^ (((min p q : ℕ) : ℝ)⁻¹) := Real.rpow_pos_of_pos (hdk v hv k) _
      have h2 := Real.log_le_log ha h1
      rw [Real.log_mul (Real.rpow_pos_of_pos (hdk v0 hv0 k) _).ne' (ht k).ne',
        Real.log_rpow (hdk v hv k), Real.log_rpow (hdk v0 hv0 k)] at h2
      have h3 := mul_le_mul_of_nonneg_left h2 hmR.le
      have hmm : ((min p q : ℕ) : ℝ) * ((min p q : ℕ) : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hm0
      rw [mul_add, ← mul_assoc, ← mul_assoc, hmm] at h3
      simpa only [one_mul] using h3
    have hQpos : ∀ k, 0 < Q k v := fun k => (div_pos_iff_of_pos_right hmR).mp (ht k)
    have hSpos : 0 < ∑ k, Q k v := Finset.sum_pos (fun k _ => hQpos k) Finset.univ_nonempty
    refine ⟨hSpos, ?_⟩
    have hJ : ∑ k, (f : ℝ)⁻¹ • Real.log (Q k v / ((min p q : ℕ) : ℝ)) ≤
        Real.log (∑ k, (f : ℝ)⁻¹ • (Q k v / ((min p q : ℕ) : ℝ))) :=
      (strictConcaveOn_log_Ioi.concaveOn).le_map_sum (fun _ _ => inv_nonneg.mpr hfR.le)
        (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            exact mul_inv_cancel₀ hf0)
        (fun k _ => ht k)
    have hS : ∑ k, (f : ℝ)⁻¹ • (Q k v / ((min p q : ℕ) : ℝ)) =
        (∑ k, Q k v) / ((f * min p q : ℕ) : ℝ) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [smul_eq_mul, hC_eq]
      field_simp
    have hL : ∑ k, (f : ℝ)⁻¹ • Real.log (Q k v / ((min p q : ℕ) : ℝ)) =
        (f : ℝ)⁻¹ * ∑ k, Real.log (Q k v / ((min p q : ℕ) : ℝ)) := by
      simp only [smul_eq_mul, Finset.mul_sum]
    rw [hS, hL, Real.log_div hSpos.ne' hCpos.ne'] at hJ
    have hsum : ∑ k, Real.log (dk v k) ≤ ∑ k, Real.log (dk v0 k) +
        ((min p q : ℕ) : ℝ) * ∑ k, Real.log (Q k v / ((min p q : ℕ) : ℝ)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun k _ => hlog k
    have hmX : ((min p q : ℕ) : ℝ) * ∑ k, Real.log (Q k v / ((min p q : ℕ) : ℝ)) =
        ((f * min p q : ℕ) : ℝ) * ((f : ℝ)⁻¹ * ∑ k, Real.log (Q k v / ((min p q : ℕ) : ℝ))) := by
      rw [hC_eq]
      field_simp
    have hCJ : ((f * min p q : ℕ) : ℝ) * ((f : ℝ)⁻¹ * ∑ k, Real.log (Q k v / ((min p q : ℕ) : ℝ))) ≤
        ((f * min p q : ℕ) : ℝ) * Real.log (∑ k, Q k v) -
          ((f * min p q : ℕ) : ℝ) * Real.log ((f * min p q : ℕ) : ℝ) := by
      rw [← mul_sub]
      exact mul_le_mul_of_nonneg_left hJ hCpos.le
    have hrv : rh v = -∑ k, Real.log (dk v k) := rfl
    have hrv0 : rh v0 = -∑ k, Real.log (dk v0 k) := rfl
    rw [hrv, hrv0]
    linarith
  have hle : ∀ᶠ v in 𝓝 v0, -((f * min p q : ℕ) : ℝ) * Real.log (∑ k, Q k v) ≤
      rh v - (rh v0 + ((f * min p q : ℕ) : ℝ) * Real.log ((f * min p q : ℕ) : ℝ)) := by
    filter_upwards [(isOpen_Dset f p q).mem_nhds hv0] with v hv using (hkey v hv).2
  have h2c : ∀ {g : V (nD f p q) → ℝ}, ContDiff ℝ ∞ g → ContDiffAt ℝ 2 g v0 := fun hg => by
    simpa using (contDiff_infty.mp hg 2).contDiffAt
  have hrhc : ContDiffAt ℝ 2 (fun v : V (nD f p q) =>
      rh v - (rh v0 + ((f * min p q : ℕ) : ℝ) * Real.log ((f * min p q : ℕ) : ℝ))) v0 := by
    have h1 : ContDiffAt ℝ 2 (fun v : V (nD f p q) => -∑ k, Real.log (dk v k)) v0 := by
      refine ContDiffAt.neg (ContDiffAt.sum fun k _ => ?_)
      exact (h2c (dkV_contDiff k)).log (hdk v0 hv0 k).ne'
    exact h1.sub contDiffAt_const
  have hΨc : ContDiffAt ℝ 2 (fun v : V (nD f p q) => ∑ k, Q k v) v0 :=
    ContDiffAt.sum fun k _ => h2c (hQc k)
  have hLev : (leviV (nD f p q) (fun y => ((∑ k, Q k y : ℝ) : ℂ)) v0 ξ).re ≤ 0 := by
    rw [leviV_ofReal_sum (fun k => h2c (hQc k)) ξ,
      Complex.re_sum]
    exact Finset.sum_nonpos fun k _ => hQL k ξ
  have hSv0 : ∑ k, Q k v0 = ((f * min p q : ℕ) : ℝ) := by
    simp only [hQ0, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hC_eq]
  have heq : rh v0 - (rh v0 + ((f * min p q : ℕ) : ℝ) * Real.log ((f * min p q : ℕ) : ℝ)) =
      -((f * min p q : ℕ) : ℝ) * Real.log (∑ k, Q k v0) := by
    rw [hSv0]
    ring
  have hmain := RgA.grad_le_of_minorant
    (fun v : V (nD f p q) =>
      rh v - (rh v0 + ((f * min p q : ℕ) : ℝ) * Real.log ((f * min p q : ℕ) : ℝ)))
    (fun v : V (nD f p q) => ∑ k, Q k v) v0 ((f * min p q : ℕ) : ℝ) hCpos
    (hkey v0 hv0).1 hrhc hΨc ξ hLev hle heq
  simp only [wd_ofReal_sub_const (fun w : V (nD f p q) => rh w), leviV_ofReal_sub_const (fun w : V (nD f p q) => rh w)]
    at hmain
  exact hmain

end ReciprocityTheory.ChartRestriction.G.AR.Up.RgE

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up.RgE

/- English proof (translation)
Introduce `f p q v hv ξ`. Distinguish the cases in `h : 0 < f ∧ 0 < min p q`. Conclude with `rhGrad_main h.1 h.2 v hv ξ`. Establish `hn : nD f p q = 0`. Simplify using `only [nD]`.

Break down `Nat.eq_zero_or_pos f with hf | hf` into its components or cases. Simplify using `[hf]`. Establish `hm : ¬ 0 < min p q` using `fun hm => h ⟨hf, hm⟩`. Break down `Nat.min_eq_zero_iff.mp (Nat.eq_zero_of_not_pos hm) with hp | hq` into its components or cases. Simplify using `[hp]`.

Simplify using `[hq]`. Use `haveI : IsEmpty (Fin (nD f p q)) := by rw [hn]; infer_instance`. Simplify using `[leviV]`.
-/
theorem RhGradStatement_holds : RhGradStatement := by
  intro f p q v hv ξ
  by_cases h : 0 < f ∧ 0 < min p q
  · exact rhGrad_main h.1 h.2 v hv ξ
  · have hn : nD f p q = 0 := by
      simp only [nD]
      rcases Nat.eq_zero_or_pos f with hf | hf
      · simp [hf]
      · have hm : ¬ 0 < min p q := fun hm => h ⟨hf, hm⟩
        rcases Nat.min_eq_zero_iff.mp (Nat.eq_zero_of_not_pos hm) with hp | hq
        · simp [hp]
        · simp [hq]
    haveI : IsEmpty (Fin (nD f p q)) := by rw [hn]; infer_instance
    simp [leviV]

end ReciprocityTheory.ChartRestriction.G.AR.Up
