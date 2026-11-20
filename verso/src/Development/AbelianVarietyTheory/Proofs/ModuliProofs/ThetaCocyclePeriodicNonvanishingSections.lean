import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SetIntegralFderivEqZeroOfLatticePeriodic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CauchyRiemannIffDifferentiableOnComplex
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PeriodicCechCocycleSmoothCoboundaryStatement
open Complex Matrix
open scoped ContDiff BigOperators Real
open Filter Topology

namespace GlobalTheory.PeriodSymm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

noncomputable def dbar (f : E → ℂ) (u : E) (z : E) : ℂ :=
  fderiv ℝ f z u + I * fderiv ℝ f z (I • u)

/- English proof (translation)
Rewrite using `[dbar, dbar, h.fderiv_eq (𝕜 := ℝ)]`.
-/
theorem dbar_congr {f f' : E → ℂ} {z : E} (h : f =ᶠ[𝓝 z] f') (u : E) :
    dbar f u z = dbar f' u z := by
  rw [dbar, dbar, h.fderiv_eq (𝕜 := ℝ)]

/- English proof (translation)
Rewrite using `[dbar, h.fderiv_restrictScalars ℝ]`. Simplify using `only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]`. Take the linear combination `(fderiv ℂ f z u) * I_sq`.
-/
theorem dbar_holo {f : E → ℂ} {z : E} (h : DifferentiableAt ℂ f z) (u : E) :
    dbar f u z = 0 := by
  rw [dbar, h.fderiv_restrictScalars ℝ]
  simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
  linear_combination (fderiv ℂ f z u) * I_sq

/- English proof (translation)
Establish `H : HasFDerivAt (fun x => f x + f' x) (fderiv ℝ f z + fderiv ℝ f' z) z` using `h.hasFDerivAt.add h'.hasFDerivAt`. Rewrite using `[dbar, dbar, dbar, H.fderiv]`. Simplify using `only [ContinuousLinearMap.add_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dbar_add {f f' : E → ℂ} {z : E} (h : DifferentiableAt ℝ f z) (h' : DifferentiableAt ℝ f' z)
    (u : E) : dbar (fun x => f x + f' x) u z = dbar f u z + dbar f' u z := by
  have H : HasFDerivAt (fun x => f x + f' x) (fderiv ℝ f z + fderiv ℝ f' z) z :=
    h.hasFDerivAt.add h'.hasFDerivAt
  rw [dbar, dbar, dbar, H.fderiv]
  simp only [ContinuousLinearMap.add_apply]
  ring

/- English proof (translation)
Establish `H : HasFDerivAt (fun x => f x - f' x) (fderiv ℝ f z - fderiv ℝ f' z) z` using `h.hasFDerivAt.sub h'.hasFDerivAt`. Rewrite using `[dbar, dbar, dbar, H.fderiv]`. Simplify using `only [ContinuousLinearMap.sub_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dbar_sub {f f' : E → ℂ} {z : E} (h : DifferentiableAt ℝ f z) (h' : DifferentiableAt ℝ f' z)
    (u : E) : dbar (fun x => f x - f' x) u z = dbar f u z - dbar f' u z := by
  have H : HasFDerivAt (fun x => f x - f' x) (fderiv ℝ f z - fderiv ℝ f' z) z :=
    h.hasFDerivAt.sub h'.hasFDerivAt
  rw [dbar, dbar, dbar, H.fderiv]
  simp only [ContinuousLinearMap.sub_apply]
  ring

/- English proof (translation)
Establish `H : HasFDerivAt (fun x => f x * f' x) (f z • fderiv ℝ f' z + f' z • fderiv ℝ f z) z` using `h.hasFDerivAt.mul h'.hasFDerivAt`. Rewrite using `[dbar, dbar, dbar, H.fderiv]`. Simplify using `only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dbar_mul {f f' : E → ℂ} {z : E} (h : DifferentiableAt ℝ f z) (h' : DifferentiableAt ℝ f' z)
    (u : E) : dbar (fun x => f x * f' x) u z = dbar f u z * f' z + f z * dbar f' u z := by
  have H : HasFDerivAt (fun x => f x * f' x) (f z • fderiv ℝ f' z + f' z • fderiv ℝ f z) z :=
    h.hasFDerivAt.mul h'.hasFDerivAt
  rw [dbar, dbar, dbar, H.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Conclude with `HasFDerivAt.fun_sum h`.
-/
private lemma hasFDerivAt_finset_sum {ι : Type*} (s : Finset ι) {A : ι → E → ℂ}
    {A' : ι → E →L[ℝ] ℂ} {x : E} (h : ∀ i ∈ s, HasFDerivAt (A i) (A' i) x) :
    HasFDerivAt (fun y => ∑ i ∈ s, A i y) (∑ i ∈ s, A' i) x := by
  exact HasFDerivAt.fun_sum h

/- English proof (translation)
Establish `H` using `hasFDerivAt_finset_sum s (fun i hi => (h i hi).hasFDerivAt)`. Rewrite using `[dbar, H.fderiv, ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply, Finset.mul_sum, ← Finset.sum_add_distrib]`. Both sides reduce to the same expression.
-/
theorem dbar_sum {ι : Type*} (s : Finset ι) {f : ι → E → ℂ} {z : E}
    (h : ∀ i ∈ s, DifferentiableAt ℝ (f i) z) (u : E) :
    dbar (fun x => ∑ i ∈ s, f i x) u z = ∑ i ∈ s, dbar (f i) u z := by
  have H := hasFDerivAt_finset_sum s (fun i hi => (h i hi).hasFDerivAt)
  rw [dbar, H.fderiv, ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  rfl

/- English proof (translation)
Simplify using `only [dbar, ContinuousLinearMap.fderiv, hφ]`. Take the linear combination `(-φ u) * I_sq`.
-/
theorem dbar_anti (φ : E →L[ℝ] ℂ) (hφ : ∀ u, φ (I • u) = -I * φ u) (u z : E) :
    dbar φ u z = 2 * φ u := by
  simp only [dbar, ContinuousLinearMap.fderiv, hφ]
  linear_combination (-φ u) * I_sq

/- English proof (translation)
Simplify using `only [dbar, fderiv_comp_add_right]`.
-/
theorem dbar_translate (f : E → ℂ) (u z l : E) :
    dbar (fun x => f (x + l)) u z = dbar f u (z + l) := by
  simp only [dbar, fderiv_comp_add_right]

/- English proof (translation)
Establish `h1 : ContDiffAt ℝ 1 (fderiv ℝ f) z` using `h.fderiv_right (by norm_num)`. Conclude with `(h1.clm_apply contDiffAt_const).add (contDiffAt_const.mul (h1.clm_apply contDiffAt_const))`.
-/
theorem dbar_contDiffAt {f : E → ℂ} {z : E} (h : ContDiffAt ℝ 2 f z) (u : E) :
    ContDiffAt ℝ 1 (dbar f u) z := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) z := h.fderiv_right (by norm_num)
  exact (h1.clm_apply contDiffAt_const).add (contDiffAt_const.mul (h1.clm_apply contDiffAt_const))

/- English proof (translation)
Rewrite using `[fderiv_clm_apply hD (differentiableAt_const u)]`. Simplify using the standard rewrite rules.
-/
private lemma fderiv_apply_lemma {f : E → ℂ} {z : E}
    (hD : DifferentiableAt ℝ (fderiv ℝ f) z) (u w : E) :
    fderiv ℝ (fun x => fderiv ℝ f x u) z w = fderiv ℝ (fderiv ℝ f) z w u := by
  rw [fderiv_clm_apply hD (differentiableAt_const u)]
  simp

/- English proof (translation)
Establish `h1 : ContDiffAt ℝ 1 (fderiv ℝ f) z` using `h.fderiv_right (by norm_num)`. Establish `hD : DifferentiableAt ℝ (fderiv ℝ f) z` using `h1.differentiableAt (by norm_num)`. Establish `hs` using `h.isSymmSndFDerivAt (by simp)`. Establish `e : ∀ a w : E, fderiv ℝ (dbar f a) z w = fderiv ℝ (fderiv ℝ f) z w a + I * fderiv ℝ (fderiv ℝ f) z w (I • a)`. Introduce `a w`.

Establish `d1 : DifferentiableAt ℝ (fun x => fderiv ℝ f x a) z` using `hD.clm_apply (differentiableAt_const _)`. Establish `d2 : DifferentiableAt ℝ (fun x => fderiv ℝ f x (I • a)) z` using `hD.clm_apply (differentiableAt_const _)`. Establish `H : HasFDerivAt (dbar f a) (fderiv ℝ (fun x => fderiv ℝ f x a) z + I • fderiv ℝ (fun x => fderiv ℝ f x (I • a)) z) z` using `d1.hasFDerivAt.add (d2.hasFDerivAt.const_mul I)`. Rewrite using `[H.fderiv, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, fderiv_apply_lemma hD, fderiv_apply_lemma hD]`. Rewrite using `[dbar, dbar, e, e, e, e, hs v u, hs v (I • u), hs (I • v) u, hs (I • v) (I • u)]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem dbar_symm {f : E → ℂ} {z : E} (h : ContDiffAt ℝ 2 f z) (u v : E) :
    dbar (dbar f u) v z = dbar (dbar f v) u z := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) z := h.fderiv_right (by norm_num)
  have hD : DifferentiableAt ℝ (fderiv ℝ f) z := h1.differentiableAt (by norm_num)
  have hs := h.isSymmSndFDerivAt (by simp)
  have e : ∀ a w : E, fderiv ℝ (dbar f a) z w
      = fderiv ℝ (fderiv ℝ f) z w a + I * fderiv ℝ (fderiv ℝ f) z w (I • a) := by
    intro a w
    have d1 : DifferentiableAt ℝ (fun x => fderiv ℝ f x a) z :=
      hD.clm_apply (differentiableAt_const _)
    have d2 : DifferentiableAt ℝ (fun x => fderiv ℝ f x (I • a)) z :=
      hD.clm_apply (differentiableAt_const _)
    have H : HasFDerivAt (dbar f a) (fderiv ℝ (fun x => fderiv ℝ f x a) z
        + I • fderiv ℝ (fun x => fderiv ℝ f x (I • a)) z) z :=
      d1.hasFDerivAt.add (d2.hasFDerivAt.const_mul I)
    rw [H.fderiv, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      fderiv_apply_lemma hD, fderiv_apply_lemma hD]
  rw [dbar, dbar, e, e, e, e, hs v u, hs v (I • u), hs (I • v) u, hs (I • v) (I • u)]
  ring

/- English proof (translation)
Establish `H : HasFDerivAt (fun x => c * f x) (c • fderiv ℝ f z) z` using `h.hasFDerivAt.const_mul c`. Rewrite using `[dbar, dbar, H.fderiv]`. Simplify using `only [ContinuousLinearMap.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma dbar_const_mul {f : E → ℂ} {z : E} (c : ℂ) (h : DifferentiableAt ℝ f z)
    (u : E) : dbar (fun x => c * f x) u z = c * dbar f u z := by
  have H : HasFDerivAt (fun x => c * f x) (c • fderiv ℝ f z) z := h.hasFDerivAt.const_mul c
  rw [dbar, dbar, H.fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Use `(contDiffOn_infty.1 hf 2).contDiffAt (hs.mem_nhds hx)` as an intermediate fact. Conclude with `this` after adjusting the coercions.
-/
private lemma contDiffAt_two_of_contDiffOn_infty_of_isOpen {s : Set E} {f : E → ℂ} {x : E} (hf : ContDiffOn ℝ ∞ f s)
    (hs : IsOpen s) (hx : x ∈ s) : ContDiffAt ℝ 2 f x := by
  have := (contDiffOn_infty.1 hf 2).contDiffAt (hs.mem_nhds hx)
  exact_mod_cast this

/- English proof (translation)
Conclude with `ContDiffOn.sum h`.
-/
private lemma contDiffOn_infty_finset_sum {ι : Type*} (s : Finset ι) {A : ι → E → ℂ} {t : Set E}
    (h : ∀ i ∈ s, ContDiffOn ℝ ∞ (A i) t) : ContDiffOn ℝ ∞ (fun y => ∑ i ∈ s, A i y) t := by
  exact ContDiffOn.sum h

/- English proof (translation)
Conclude with `ContDiffAt.sum h`.
-/
private lemma contDiffAt_one_finset_sum {ι : Type*} (s : Finset ι) {A : ι → E → ℂ} {x : E}
    (h : ∀ i ∈ s, ContDiffAt ℝ 1 (A i) x) : ContDiffAt ℝ 1 (fun y => ∑ i ∈ s, A i y) x := by
  exact ContDiffAt.sum h

/- English proof (translation)
Establish `hpS : ∀ i m, ContDiffOn ℝ ∞ (p i m) (U i)` using `fun i m => ((GlobalTheory.cauchyRiemann_iff_differentiableOn_complex g (U i) (p i m) (hU i)).2 (hp i m)).1`. Establish `hkS : ∀ i j, ContDiffOn ℝ ∞ (k i j) (U i ∩ U j)` using `fun i j => ((GlobalTheory.cauchyRiemann_iff_differentiableOn_complex g _ (k i j) ((hU i).inter (hU j))).2 (hk i j)).1`. Take `⟨G, hG⟩ : ∃ G : ι → ι → (Fin g → ℂ) → ℂ, ∀ i j z, G i j z = k i j z - ∑ m, θ m z * (p i m z - p j m z)` from `⟨_, fun _ _ _ => rfl⟩`. Establish `hGs : ∀ i j, ContDiffOn ℝ ∞ (G i j) (U i ∩ U j)`. Introduce `i j`.

Use `ContDiffOn.congr ?_ (fun z _ => hG i j z)` and prove the remaining obligations. Establish `hs : ContDiffOn ℝ ∞ (fun z => ∑ m, θ m z * (p i m z - p j m z)) (U i ∩ U j)` using `contDiffOn_infty_finset_sum (A := fun m z => θ m z * (p i m z - p j m z)) Finset.univ fun m _ => by`. Conclude with `(θ m).contDiff.contDiffOn.mul (((hpS i m).mono Set.inter_subset_left).sub ((hpS j m).mono Set.inter_subset_right))`. Conclude with `(hkS i j).sub hs`. Establish `hGper : ∀ i j (l : Λ), ∀ z ∈ U i ∩ U j, G i j (z + l) = G i j z`.

Introduce `i j l z hz`. Establish `hi : ∀ m, p i m (z + l) = p i m z - h m l` using `fun m => hper i m l z hz.1`. Establish `hj : ∀ m, p j m (z + l) = p j m z - h m l` using `fun m => hper j m l z hz.2`. Rewrite using `[hG, hG, hkp i j l z hz]`. Simplify using `only [hi, hj, map_add, sub_sub_sub_cancel_right, add_mul, Finset.sum_add_distrib, mul_sub, Finset.sum_sub_distrib]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hGc : ∀ i j n, ∀ z ∈ U i ∩ U j ∩ U n, G i j z + G j n z = G i n z`. Introduce `i j n z hz`. Rewrite using `[hG, hG, hG, ← hkc i j n z hz]`. Simplify using `only [mul_sub, Finset.sum_sub_distrib]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨b, hb, hbG⟩` from `GlobalTheory.T.exists_periodic_smooth_coboundary_of_cech_cocycle g Λ hd hsp ι U G hU hinv hcov hGs hGper hGc`. Establish `hbA : ∀ i, ∀ x ∈ U i, ContDiffAt ℝ 2 (b i) x` using `fun i x hx => contDiffAt_two_of_contDiffOn_infty_of_isOpen (hb i).1 (hU i) hx`. Establish `hbD : ∀ i, ∀ x ∈ U i, DifferentiableAt ℝ (b i) x` using `fun i x hx => (hbA i x hx).differentiableAt (by norm_num)`. Establish `hpD : ∀ i m, ∀ x ∈ U i, DifferentiableAt ℂ (p i m) x` using `fun i m x hx => (hp i m).differentiableAt ((hU i).mem_nhds hx)`.

Take `⟨W, hW⟩ : ∃ W : ι → (Fin g → ℂ) → (Fin g → ℂ) → ℂ, ∀ i u, W i u = fun y => (∑ m, (2 * θ m u) * (p i m y + h m y)) - dbar (b i) u y` from `⟨fun i u y => (∑ m, (2 * θ m u) * (p i m y + h m y)) - dbar (b i) u y, fun _ _ => rfl⟩`. Establish `hPH : ∀ i m, ∀ x ∈ U i, DifferentiableAt ℝ (fun y => p i m y + h m y) x` using `fun i m x hx => ((hpD i m x hx).restrictScalars ℝ).add (h m).differentiableAt`. Establish `hTD : ∀ i u m, ∀ x ∈ U i, DifferentiableAt ℝ (fun y => 2 * θ m u * (p i m y + h m y)) x` using `fun i u m x hx => (hPH i m x hx).const_mul _`. Establish `hSD : ∀ i u, ∀ x ∈ U i, DifferentiableAt ℝ (fun y => ∑ m, (2 * θ m u) * (p i m y + h m y)) x` using `fun i u x hx => (hasFDerivAt_finset_sum (A := fun m y => 2 * θ m u * (p i m y + h m y)) Finset.univ fun m _ => (hTD i u m x hx).hasFDerivAt).differentiableAt`. Establish `hWA : ∀ i u, ∀ x ∈ U i, ContDiffAt ℝ 1 (W i u) x`.

Introduce `i u x hx`. Establish `h1 : ContDiffAt ℝ 1 (fun y => ∑ m, (2 * θ m u) * (p i m y + h m y)) x` using `contDiffAt_one_finset_sum (A := fun m y => 2 * θ m u * (p i m y + h m y)) Finset.univ fun m _ => by`. Conclude with `contDiffAt_const.mul (((contDiffAt_two_of_contDiffOn_infty_of_isOpen (hpS i m) (hU i) hx).of_le (by norm_num)).add (h m).contDiff.contDiffAt)`. Establish `h2` using `dbar_contDiffAt (hbA i x hx) u`. Rewrite using `[hW]`.

Conclude with `h1.sub h2`. Establish `hWeq : ∀ i j u, ∀ x ∈ U i ∩ U j, W i u x = W j u x`. Introduce `i j u x hx`. Establish `hO : U i ∩ U j ∈ 𝓝 x` using `((hU i).inter (hU j)).mem_nhds hx`. Establish `hev : b j =ᶠ[𝓝 x] fun y => b i y + (k i j y - ∑ m, θ m y * (p i m y - p j m y))` using `by filter_upwards [hO] with y hy`.

Establish `e` using `hbG i j y hy`. Rewrite `e` using `[hG]`. Take the linear combination `-e`. Establish `hkD : DifferentiableAt ℂ (k i j) x` using `(hk i j).differentiableAt hO`. Establish `hdD : ∀ m, DifferentiableAt ℂ (fun y => p i m y - p j m y) x` using `fun m => (hpD i m x hx.1).sub (hpD j m x hx.2)`.

Establish `hmD : ∀ m, DifferentiableAt ℝ (fun y => θ m y * (p i m y - p j m y)) x` using `fun m => (θ m).differentiableAt.mul ((hdD m).restrictScalars ℝ)`. Establish `hterm : ∀ m, dbar (fun y => θ m y * (p i m y - p j m y)) u x = 2 * θ m u * (p i m x - p j m x)`. Introduce `m`. Rewrite using `[dbar_mul (θ m).differentiableAt ((hdD m).restrictScalars ℝ), dbar_anti (θ m) (hθ m), dbar_holo (hdD m)]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hsumD : DifferentiableAt ℝ (fun y => ∑ m, θ m y * (p i m y - p j m y)) x` using `(hasFDerivAt_finset_sum (A := fun m y => θ m y * (p i m y - p j m y)) Finset.univ fun m _ => (hmD m).hasFDerivAt).differentiableAt`. Establish `hbj : dbar (b j) u x = dbar (b i) u x + (0 - ∑ m, 2 * θ m u * (p i m x - p j m x))`. Establish `hk2 : DifferentiableAt ℝ (fun y => k i j y - ∑ m, θ m y * (p i m y - p j m y)) x` using `(hkD.restrictScalars ℝ).sub hsumD`. Rewrite using `[dbar_congr hev, dbar_add (hbD i x hx.1) hk2, dbar_sub (hkD.restrictScalars ℝ) hsumD, dbar_holo hkD, dbar_sum (f := fun m y => θ m y * (p i m y - p j m y)) Finset.univ fun m _ => hmD m]`. Simplify using `only [hterm]`.

Simplify using `only [hW]`. Rewrite using `[hbj]`. Simplify using `only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]`. Expand and normalize the polynomial expressions, which then agree. Establish `hWper : ∀ i u (l : Λ), ∀ x ∈ U i, W i u (x + l) = W i u x`.

Introduce `i u l x hx`. Establish `hev : (fun y => b i (y + l)) =ᶠ[𝓝 x] b i` using `by filter_upwards [(hU i).mem_nhds hx] with y hy using (hb i).2 l y hy`. Establish `hd : dbar (b i) u (x + l) = dbar (b i) u x`. Rewrite using `[← dbar_translate, dbar_congr hev]`. Establish `hi : ∀ m, p i m (x + l) = p i m x - h m l` using `fun m => hper i m l x hx`.

Simplify using `only [hW, hd, hi, map_add]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun m _ => by ring`. Establish `hWd : ∀ i a c, ∀ x ∈ U i, dbar (W i a) c x = ∑ m, (2 * θ m a) * (2 * h m c) - dbar (dbar (b i) a) c x`. Introduce `i a c x hx`.

Establish `hbd1 : DifferentiableAt ℝ (dbar (b i) a) x` using `(dbar_contDiffAt (hbA i x hx) a).differentiableAt (by norm_num)`. Rewrite using `[hW, dbar_sub (hSD i a x hx) hbd1, dbar_sum (f := fun m y => 2 * θ m a * (p i m y + h m y)) Finset.univ fun m _ => hTD i a m x hx]`. Use `congr 1`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[dbar_const_mul _ (hPH i m x hx), dbar_add ((hpD i m x hx).restrictScalars ℝ) (h m).differentiableAt, dbar_holo (hpD i m x hx), dbar_anti (h m) (hh m)]`.

Expand and normalize the polynomial expressions, which then agree. Use `choose ch hch using hcov`. Take `⟨P, hP⟩ : ∃ P : (Fin g → ℂ) → (Fin g → ℂ) → ℂ, ∀ a z, P a z = W (ch z) a z` from `⟨_, fun _ _ => rfl⟩`. Establish `hPloc : ∀ a i, ∀ x ∈ U i, P a =ᶠ[𝓝 x] W i a`. Introduce `a i x hx`.

Use `filter_upwards [(hU i).mem_nhds hx] with y hy`. Rewrite using `[hP]`. Conclude with `hWeq _ _ a y ⟨hch y, hy⟩`. Establish `hPper : ∀ a (l : Λ) z, P a (z + l) = P a z`. Introduce `a l z`.

Rewrite using `[hP, hP, hWeq (ch (z + l)) (ch z) a (z + l) ⟨hch _, hinv _ l z (hch z)⟩, hWper _ a l z (hch z)]`. Establish `hPC : ∀ a, ContDiff ℝ 1 (P a)`. Introduce `a`. Rewrite using `[contDiff_iff_contDiffAt]`. Introduce `z`.

Conclude with `(hWA (ch z) a z (hch z)).congr_of_eventuallyEq (hPloc a (ch z) z (hch z))`. Establish `s1 : ∀ a c, ∑ m, (2 * θ m a) * (2 * h m c) = 4 * ∑ m, θ m a * h m c`. Introduce `a c`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun _ _ => by ring`.

Establish `hconst : ∀ z, ∑ n : Fin 4, ![(1 : ℂ), I, -1, -I] n * fderiv ℝ (![P u, P u, P v, P v] n) z (![v, I • v, u, I • u] n) = 4 * (∑ m, θ m u * h m v - ∑ m, θ m v * h m u)`. Introduce `z`. Use `Eq.trans (b := dbar (P u) v z - dbar (P v) u z) ?_ ?_` and prove the remaining obligations. Simplify using `[Fin.sum_univ_four, dbar]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[dbar_congr (hPloc u _ z (hch z)), dbar_congr (hPloc v _ z (hch z)), hWd _ u v z (hch z), hWd _ v u z (hch z), dbar_symm (hbA _ z (hch z)) u v, s1, s1]`. Expand and normalize the polynomial expressions, which then agree. Apply the tactic sequence `have h0 := GlobalTheory.const_eq_zero_of_sum_fderiv_periodic g Λ hd hsp 4 ![P u, P u, P v, P v] ![1, I, -1, -I] ![v, I • v, u, I • u] _ (fun n => ⟨by fin_cases n <;> simp [hPC], fun l z => by fin_cases n <;> simp [hPper]⟩) hconst`. Establish `h4 : (4 : ℂ) ≠ 0` using `by norm_num`. Conclude with `sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left h4)`.
-/
theorem symm_of_cocycle (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (hd : DiscreteTopology Λ)
    (hsp : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) (ι : Type) (U : ι → Set (Fin g → ℂ))
    (p : ι → Fin g → (Fin g → ℂ) → ℂ) (k : ι → ι → (Fin g → ℂ) → ℂ)
    (θ h : Fin g → (Fin g → ℂ) →L[ℝ] ℂ)
    (hθ : ∀ m u, θ m (I • u) = -I * θ m u) (hh : ∀ m u, h m (I • u) = -I * h m u)
    (hU : ∀ i, IsOpen (U i)) (hinv : ∀ i (l : Λ) z, z ∈ U i → z + l ∈ U i)
    (hcov : ∀ z, ∃ i, z ∈ U i) (hp : ∀ i m, DifferentiableOn ℂ (p i m) (U i))
    (hper : ∀ i m (l : Λ), ∀ z ∈ U i, p i m (z + l) = p i m z - h m l)
    (hk : ∀ i j, DifferentiableOn ℂ (k i j) (U i ∩ U j))
    (hkc : ∀ i j m, ∀ z ∈ U i ∩ U j ∩ U m, k i j z + k j m z = k i m z)
    (hkp : ∀ i j (l : Λ), ∀ z ∈ U i ∩ U j,
      k i j (z + l) = k i j z + (∑ m, θ m l * p i m z - ∑ m, θ m l * p j m z))
    (u v : Fin g → ℂ) : ∑ m, θ m u * h m v = ∑ m, θ m v * h m u := by
  classical
  have hpS : ∀ i m, ContDiffOn ℝ ∞ (p i m) (U i) := fun i m =>
    ((GlobalTheory.cauchyRiemann_iff_differentiableOn_complex g (U i) (p i m) (hU i)).2 (hp i m)).1
  have hkS : ∀ i j, ContDiffOn ℝ ∞ (k i j) (U i ∩ U j) := fun i j =>
    ((GlobalTheory.cauchyRiemann_iff_differentiableOn_complex g _ (k i j) ((hU i).inter (hU j))).2
      (hk i j)).1

  obtain ⟨G, hG⟩ : ∃ G : ι → ι → (Fin g → ℂ) → ℂ, ∀ i j z,
      G i j z = k i j z - ∑ m, θ m z * (p i m z - p j m z) := ⟨_, fun _ _ _ => rfl⟩
  have hGs : ∀ i j, ContDiffOn ℝ ∞ (G i j) (U i ∩ U j) := by
    intro i j
    refine ContDiffOn.congr ?_ (fun z _ => hG i j z)
    have hs : ContDiffOn ℝ ∞ (fun z => ∑ m, θ m z * (p i m z - p j m z)) (U i ∩ U j) :=
      contDiffOn_infty_finset_sum (A := fun m z => θ m z * (p i m z - p j m z)) Finset.univ fun m _ => by
        exact (θ m).contDiff.contDiffOn.mul
          (((hpS i m).mono Set.inter_subset_left).sub ((hpS j m).mono Set.inter_subset_right))
    exact (hkS i j).sub hs
  have hGper : ∀ i j (l : Λ), ∀ z ∈ U i ∩ U j, G i j (z + l) = G i j z := by
    intro i j l z hz
    have hi : ∀ m, p i m (z + l) = p i m z - h m l := fun m => hper i m l z hz.1
    have hj : ∀ m, p j m (z + l) = p j m z - h m l := fun m => hper j m l z hz.2
    rw [hG, hG, hkp i j l z hz]
    simp only [hi, hj, map_add, sub_sub_sub_cancel_right, add_mul, Finset.sum_add_distrib, mul_sub,
      Finset.sum_sub_distrib]
    ring
  have hGc : ∀ i j n, ∀ z ∈ U i ∩ U j ∩ U n, G i j z + G j n z = G i n z := by
    intro i j n z hz
    rw [hG, hG, hG, ← hkc i j n z hz]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  obtain ⟨b, hb, hbG⟩ := GlobalTheory.T.exists_periodic_smooth_coboundary_of_cech_cocycle g Λ hd hsp ι U G hU hinv hcov hGs hGper hGc
  have hbA : ∀ i, ∀ x ∈ U i, ContDiffAt ℝ 2 (b i) x := fun i x hx =>
    contDiffAt_two_of_contDiffOn_infty_of_isOpen (hb i).1 (hU i) hx
  have hbD : ∀ i, ∀ x ∈ U i, DifferentiableAt ℝ (b i) x := fun i x hx =>
    (hbA i x hx).differentiableAt (by norm_num)
  have hpD : ∀ i m, ∀ x ∈ U i, DifferentiableAt ℂ (p i m) x := fun i m x hx =>
    (hp i m).differentiableAt ((hU i).mem_nhds hx)

  obtain ⟨W, hW⟩ : ∃ W : ι → (Fin g → ℂ) → (Fin g → ℂ) → ℂ, ∀ i u,
      W i u = fun y => (∑ m, (2 * θ m u) * (p i m y + h m y)) - dbar (b i) u y :=
    ⟨fun i u y => (∑ m, (2 * θ m u) * (p i m y + h m y)) - dbar (b i) u y, fun _ _ => rfl⟩
  have hPH : ∀ i m, ∀ x ∈ U i, DifferentiableAt ℝ (fun y => p i m y + h m y) x := fun i m x hx =>
    ((hpD i m x hx).restrictScalars ℝ).add (h m).differentiableAt
  have hTD : ∀ i u m, ∀ x ∈ U i,
      DifferentiableAt ℝ (fun y => 2 * θ m u * (p i m y + h m y)) x := fun i u m x hx =>
    (hPH i m x hx).const_mul _
  have hSD : ∀ i u, ∀ x ∈ U i,
      DifferentiableAt ℝ (fun y => ∑ m, (2 * θ m u) * (p i m y + h m y)) x := fun i u x hx =>
    (hasFDerivAt_finset_sum (A := fun m y => 2 * θ m u * (p i m y + h m y)) Finset.univ
      fun m _ => (hTD i u m x hx).hasFDerivAt).differentiableAt
  have hWA : ∀ i u, ∀ x ∈ U i, ContDiffAt ℝ 1 (W i u) x := by
    intro i u x hx
    have h1 : ContDiffAt ℝ 1 (fun y => ∑ m, (2 * θ m u) * (p i m y + h m y)) x :=
      contDiffAt_one_finset_sum (A := fun m y => 2 * θ m u * (p i m y + h m y)) Finset.univ fun m _ => by
        exact contDiffAt_const.mul
          (((contDiffAt_two_of_contDiffOn_infty_of_isOpen (hpS i m) (hU i) hx).of_le (by norm_num)).add
            (h m).contDiff.contDiffAt)
    have h2 := dbar_contDiffAt (hbA i x hx) u
    rw [hW]
    exact h1.sub h2
  have hWeq : ∀ i j u, ∀ x ∈ U i ∩ U j, W i u x = W j u x := by
    intro i j u x hx
    have hO : U i ∩ U j ∈ 𝓝 x := ((hU i).inter (hU j)).mem_nhds hx
    have hev : b j =ᶠ[𝓝 x] fun y => b i y + (k i j y - ∑ m, θ m y * (p i m y - p j m y)) := by
      filter_upwards [hO] with y hy
      have e := hbG i j y hy
      rw [hG] at e
      linear_combination -e
    have hkD : DifferentiableAt ℂ (k i j) x := (hk i j).differentiableAt hO
    have hdD : ∀ m, DifferentiableAt ℂ (fun y => p i m y - p j m y) x := fun m =>
      (hpD i m x hx.1).sub (hpD j m x hx.2)
    have hmD : ∀ m, DifferentiableAt ℝ (fun y => θ m y * (p i m y - p j m y)) x := fun m =>
      (θ m).differentiableAt.mul ((hdD m).restrictScalars ℝ)
    have hterm : ∀ m, dbar (fun y => θ m y * (p i m y - p j m y)) u x
        = 2 * θ m u * (p i m x - p j m x) := by
      intro m
      rw [dbar_mul (θ m).differentiableAt ((hdD m).restrictScalars ℝ), dbar_anti (θ m) (hθ m),
        dbar_holo (hdD m)]
      ring
    have hsumD : DifferentiableAt ℝ (fun y => ∑ m, θ m y * (p i m y - p j m y)) x :=
      (hasFDerivAt_finset_sum (A := fun m y => θ m y * (p i m y - p j m y)) Finset.univ
        fun m _ => (hmD m).hasFDerivAt).differentiableAt
    have hbj : dbar (b j) u x
        = dbar (b i) u x + (0 - ∑ m, 2 * θ m u * (p i m x - p j m x)) := by
      have hk2 : DifferentiableAt ℝ (fun y => k i j y - ∑ m, θ m y * (p i m y - p j m y)) x :=
        (hkD.restrictScalars ℝ).sub hsumD
      rw [dbar_congr hev, dbar_add (hbD i x hx.1) hk2,
        dbar_sub (hkD.restrictScalars ℝ) hsumD, dbar_holo hkD,
        dbar_sum (f := fun m y => θ m y * (p i m y - p j m y)) Finset.univ fun m _ => hmD m]
      simp only [hterm]
    simp only [hW]
    rw [hbj]
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  have hWper : ∀ i u (l : Λ), ∀ x ∈ U i, W i u (x + l) = W i u x := by
    intro i u l x hx
    have hev : (fun y => b i (y + l)) =ᶠ[𝓝 x] b i := by
      filter_upwards [(hU i).mem_nhds hx] with y hy using (hb i).2 l y hy
    have hd : dbar (b i) u (x + l) = dbar (b i) u x := by
      rw [← dbar_translate, dbar_congr hev]
    have hi : ∀ m, p i m (x + l) = p i m x - h m l := fun m => hper i m l x hx
    simp only [hW, hd, hi, map_add]
    congr 1
    exact Finset.sum_congr rfl fun m _ => by ring
  have hWd : ∀ i a c, ∀ x ∈ U i,
      dbar (W i a) c x = ∑ m, (2 * θ m a) * (2 * h m c) - dbar (dbar (b i) a) c x := by
    intro i a c x hx
    have hbd1 : DifferentiableAt ℝ (dbar (b i) a) x :=
      (dbar_contDiffAt (hbA i x hx) a).differentiableAt (by norm_num)
    rw [hW, dbar_sub (hSD i a x hx) hbd1,
      dbar_sum (f := fun m y => 2 * θ m a * (p i m y + h m y)) Finset.univ
        fun m _ => hTD i a m x hx]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [dbar_const_mul _ (hPH i m x hx),
      dbar_add ((hpD i m x hx).restrictScalars ℝ) (h m).differentiableAt, dbar_holo (hpD i m x hx),
      dbar_anti (h m) (hh m)]
    ring

  choose ch hch using hcov
  obtain ⟨P, hP⟩ : ∃ P : (Fin g → ℂ) → (Fin g → ℂ) → ℂ, ∀ a z, P a z = W (ch z) a z :=
    ⟨_, fun _ _ => rfl⟩
  have hPloc : ∀ a i, ∀ x ∈ U i, P a =ᶠ[𝓝 x] W i a := by
    intro a i x hx
    filter_upwards [(hU i).mem_nhds hx] with y hy
    rw [hP]
    exact hWeq _ _ a y ⟨hch y, hy⟩
  have hPper : ∀ a (l : Λ) z, P a (z + l) = P a z := by
    intro a l z
    rw [hP, hP, hWeq (ch (z + l)) (ch z) a (z + l) ⟨hch _, hinv _ l z (hch z)⟩,
      hWper _ a l z (hch z)]
  have hPC : ∀ a, ContDiff ℝ 1 (P a) := by
    intro a
    rw [contDiff_iff_contDiffAt]
    intro z
    exact (hWA (ch z) a z (hch z)).congr_of_eventuallyEq (hPloc a (ch z) z (hch z))
  have s1 : ∀ a c, ∑ m, (2 * θ m a) * (2 * h m c) = 4 * ∑ m, θ m a * h m c := by
    intro a c
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hconst : ∀ z, ∑ n : Fin 4, ![(1 : ℂ), I, -1, -I] n
      * fderiv ℝ (![P u, P u, P v, P v] n) z (![v, I • v, u, I • u] n)
      = 4 * (∑ m, θ m u * h m v - ∑ m, θ m v * h m u) := by
    intro z
    refine Eq.trans (b := dbar (P u) v z - dbar (P v) u z) ?_ ?_
    · simp [Fin.sum_univ_four, dbar]
      ring
    rw [dbar_congr (hPloc u _ z (hch z)), dbar_congr (hPloc v _ z (hch z)),
      hWd _ u v z (hch z), hWd _ v u z (hch z), dbar_symm (hbA _ z (hch z)) u v, s1, s1]
    ring
  have h0 := GlobalTheory.const_eq_zero_of_sum_fderiv_periodic g Λ hd hsp 4 ![P u, P u, P v, P v]
    ![1, I, -1, -I] ![v, I • v, u, I • u] _
    (fun n => ⟨by fin_cases n <;> simp [hPC], fun l z => by fin_cases n <;> simp [hPper]⟩) hconst
  have h4 : (4 : ℂ) ≠ 0 := by norm_num
  exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left h4)

noncomputable def antiRow {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (m : Fin g) :
    (Fin g → ℂ) →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => M.mulVec (star z) m
      map_add' := fun x y => by simp [star_add, Matrix.mulVec_add]
      map_smul' := fun r x => by
        simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm] }

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem antiRow_apply {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (m : Fin g) (z : Fin g → ℂ) :
    antiRow M m z = M.mulVec (star z) m := rfl

/- English proof (translation)
Rewrite using `[antiRow_apply, antiRow_apply, star_smul, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]`. Simplify using `[Complex.star_def]`.
-/
theorem antiRow_I {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (m : Fin g) (z : Fin g → ℂ) :
    antiRow M m (I • z) = -I * antiRow M m z := by
  rw [antiRow_apply, antiRow_apply, star_smul, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  simp [Complex.star_def]

/- English proof (translation)
Establish `hv : v = ∑ m, v m • (Pi.single m 1 : Fin g → ℂ)`. Use extensionality with `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Use `conv_lhs => rw [hv]`. Simplify using `[map_sum, map_smul, smul_eq_mul]`.
-/
theorem clm_eq_sum {g : ℕ} (L : (Fin g → ℂ) →L[ℂ] ℂ) (v : Fin g → ℂ) :
    L v = ∑ m, v m * L (Pi.single m 1) := by
  have hv : v = ∑ m, v m • (Pi.single m 1 : Fin g → ℂ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp [map_sum, map_smul, smul_eq_mul]

/- English proof (translation)
Establish `hz' : z + l ∈ U` using `hinv z hz`. Establish `ha1 : a (z + l) ≠ 0` using `ha0 _ hz'`. Set `L : (Fin g → ℂ) →L[ℂ] ℂ` to `LinearMap.toContinuousLinearMap { toFun := fun x => x ⬝ᵥ w map_add' := fun x y => add_dotProduct x y w map_smul' := fun c x => smul_dotProduct c x w }`. Establish `hL : ∀ x, L x = x ⬝ᵥ w` using `fun x => rfl`. Establish `hE : HasFDerivAt (fun x => e * cexp (π * (x ⬝ᵥ w))) (e • (cexp (π * (z ⬝ᵥ w)) • ((π : ℂ) • L))) z`.

Establish `h0 : HasFDerivAt (fun x => (π : ℂ) * L x) ((π : ℂ) • L) z` using `L.hasFDerivAt.const_mul _`. Conclude with `h0.cexp.const_mul e`. Establish `hA0 : HasFDerivAt a (fderiv ℂ a (z + l)) (z + l)` using `(ha.differentiableAt (hU.mem_nhds hz')).hasFDerivAt`. Establish `hA : HasFDerivAt (fun x => a (x + l)) (fderiv ℂ a (z + l)) z`. Establish `h3` using `hA0.comp z ((hasFDerivAt_id z).add_const l)`.

Simplify using `only [ContinuousLinearMap.comp_id] at h3`. Conclude with `h3`. Establish `hev : a =ᶠ[𝓝 z] fun x => e * cexp (π * (x ⬝ᵥ w)) * a (x + l)` using `by filter_upwards [hU.mem_nhds hz] with x hx using hf x hx`. Establish `hP : HasFDerivAt (fun x => e * cexp (π * (x ⬝ᵥ w)) * a (x + l)) ((e * cexp (π * (z ⬝ᵥ w))) • fderiv ℂ a (z + l) + a (z + l) • (e • (cexp (π * (z ⬝ᵥ w)) • ((π : ℂ) • L)))) z` using `hE.mul hA`. Establish `hD` using `(hP.congr_of_eventuallyEq hev).fderiv`.

Establish `hD' : fderiv ℂ a z (Pi.single m 1) = e * cexp (π * (z ⬝ᵥ w)) * fderiv ℂ a (z + l) (Pi.single m 1) + a (z + l) * (e * (cexp (π * (z ⬝ᵥ w)) * (π * w m)))`. Rewrite using `[hD]`. Simplify using `[hL]`. Establish `hEz : e * cexp (π * (z ⬝ᵥ w)) ≠ 0`. Introduce `h0`.

Conclude with `ha0 z hz (by rw [hf z hz, h0, zero_mul])`. Establish `he : e ≠ 0` using `left_ne_zero_of_mul hEz`. Establish `hX : cexp (π * (z ⬝ᵥ w)) ≠ 0` using `Complex.exp_ne_zero _`. Rewrite using `[hD', hf z hz]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem logDeriv_translate {g : ℕ} {U : Set (Fin g → ℂ)} (hU : IsOpen U) {a : (Fin g → ℂ) → ℂ}
    (ha : DifferentiableOn ℂ a U) (ha0 : ∀ z ∈ U, a z ≠ 0) (l w : Fin g → ℂ) (e : ℂ)
    (hinv : ∀ z ∈ U, z + l ∈ U)
    (hf : ∀ z ∈ U, a z = e * cexp (π * (z ⬝ᵥ w)) * a (z + l)) (m : Fin g) {z : Fin g → ℂ}
    (hz : z ∈ U) :
    fderiv ℂ a (z + l) (Pi.single m 1) / a (z + l)
      = fderiv ℂ a z (Pi.single m 1) / a z - π * w m := by
  have hz' : z + l ∈ U := hinv z hz
  have ha1 : a (z + l) ≠ 0 := ha0 _ hz'
  let L : (Fin g → ℂ) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap
    { toFun := fun x => x ⬝ᵥ w
      map_add' := fun x y => add_dotProduct x y w
      map_smul' := fun c x => smul_dotProduct c x w }
  have hL : ∀ x, L x = x ⬝ᵥ w := fun x => rfl
  have hE : HasFDerivAt (fun x => e * cexp (π * (x ⬝ᵥ w)))
      (e • (cexp (π * (z ⬝ᵥ w)) • ((π : ℂ) • L))) z := by
    have h0 : HasFDerivAt (fun x => (π : ℂ) * L x) ((π : ℂ) • L) z := L.hasFDerivAt.const_mul _
    exact h0.cexp.const_mul e
  have hA0 : HasFDerivAt a (fderiv ℂ a (z + l)) (z + l) :=
    (ha.differentiableAt (hU.mem_nhds hz')).hasFDerivAt
  have hA : HasFDerivAt (fun x => a (x + l)) (fderiv ℂ a (z + l)) z := by
    have h3 := hA0.comp z ((hasFDerivAt_id z).add_const l)
    simp only [ContinuousLinearMap.comp_id] at h3
    exact h3
  have hev : a =ᶠ[𝓝 z] fun x => e * cexp (π * (x ⬝ᵥ w)) * a (x + l) := by
    filter_upwards [hU.mem_nhds hz] with x hx using hf x hx
  have hP : HasFDerivAt (fun x => e * cexp (π * (x ⬝ᵥ w)) * a (x + l))
      ((e * cexp (π * (z ⬝ᵥ w))) • fderiv ℂ a (z + l)
        + a (z + l) • (e • (cexp (π * (z ⬝ᵥ w)) • ((π : ℂ) • L)))) z := hE.mul hA
  have hD := (hP.congr_of_eventuallyEq hev).fderiv
  have hD' : fderiv ℂ a z (Pi.single m 1)
      = e * cexp (π * (z ⬝ᵥ w)) * fderiv ℂ a (z + l) (Pi.single m 1)
        + a (z + l) * (e * (cexp (π * (z ⬝ᵥ w)) * (π * w m))) := by
    rw [hD]
    simp [hL]
  have hEz : e * cexp (π * (z ⬝ᵥ w)) ≠ 0 := by
    intro h0
    exact ha0 z hz (by rw [hf z hz, h0, zero_mul])
  have he : e ≠ 0 := left_ne_zero_of_mul hEz
  have hX : cexp (π * (z ⬝ᵥ w)) ≠ 0 := Complex.exp_ne_zero _
  rw [hD', hf z hz]
  field_simp
  ring

/- English proof (translation)
Introduce `g Λ hd hsp Hm Θ ι U a k e hU hinv hcov ha hf hk hkc hkp z w`. Establish `key : ∑ m, antiRow Θ m z * ((Real.pi) • antiRow Hm m) w = ∑ m, antiRow Θ m w * ((Real.pi) • antiRow Hm m) z`. Use `symm_of_cocycle g Λ hd hsp ι U (fun i m x => fderiv ℂ (a i) x (Pi.single m 1) / a i x) k (fun m => antiRow Θ m) (fun m => (Real.pi) • antiRow Hm m) (fun m u => antiRow_I Θ m u) ?_ hU hinv hcov ?_ ?_ hk hkc ?_ z w` and prove the remaining obligations. Introduce `m u`. Simplify using `only [ContinuousLinearMap.smul_apply, antiRow_I, Complex.real_smul]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `i m`. Establish `h1 : DifferentiableOn ℂ (fun x => fderiv ℂ (a i) x (Pi.single m 1)) (U i)` using `((GlobalTheory.cauchyRiemann_iff_differentiableOn_complex g (U i) (a i) (hU i)).2 (ha i).1).2 _`. Establish `h2 : DifferentiableOn ℂ (fun x => (a i x)⁻¹) (U i)` using `(ha i).1.inv (ha i).2`. Conclude with `(h1.mul h2).congr fun x _ => div_eq_mul_inv _ _`.

Introduce `i m l x hx`. Simplify using `only [ContinuousLinearMap.smul_apply, antiRow_apply, Complex.real_smul]`. Conclude with `logDeriv_translate (hU i) (ha i).1 (ha i).2 (l : Fin g → ℂ) _ (e l) (fun y hy => hinv i l y hy) (fun y hy => hf i l y hy) m hx`. Introduce `i j l x hx`. Rewrite using `[hkp i j l x hx, clm_eq_sum (fderiv ℂ (a i) x), clm_eq_sum (fderiv ℂ (a j) x), Finset.sum_div, Finset.sum_div]`.

Simplify using `only [antiRow_apply, mul_div_assoc]`. Establish `e1 : ∀ x y : Fin g → ℂ, ∑ m, antiRow Θ m x * ((Real.pi) • antiRow Hm m) y = Real.pi * (Θ.mulVec (star x) ⬝ᵥ Hm.mulVec (star y))`. Introduce `x y`. Simplify using `only [ContinuousLinearMap.smul_apply, antiRow_apply, Complex.real_smul, dotProduct, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun _ _ => by ring`.

Establish `hπ : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Rewrite `key` using `[e1, e1]`. Conclude with `mul_left_cancel₀ hπ key`.
-/
theorem period_symm : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (Hm Θ : Matrix (Fin g) (Fin g) ℂ) (ι : Type) (U : ι → Set (Fin g → ℂ)) (a : ι → (Fin g → ℂ) → ℂ) (k : ι → ι → (Fin g → ℂ) → ℂ) (e : Λ → ℂ), (∀ i, IsOpen (U i)) → (∀ i (l : Λ) z, z ∈ U i → z + l ∈ U i) → (∀ z, ∃ i, z ∈ U i) → (∀ i, DifferentiableOn ℂ (a i) (U i) ∧ ∀ z ∈ U i, a i z ≠ 0) → (∀ i (l : Λ), ∀ z ∈ U i, a i z = e l * cexp (π * (z ⬝ᵥ Hm.mulVec (star (l : (Fin g → ℂ))))) * a i (z + l)) → (∀ i j, DifferentiableOn ℂ (k i j) (U i ∩ U j)) → (∀ i j m, ∀ z ∈ U i ∩ U j ∩ U m, k i j z + k j m z = k i m z) → (∀ i j (l : Λ), ∀ z ∈ U i ∩ U j, k i j (z + l) = k i j z + (fderiv ℂ (a i) z (Θ.mulVec (star (l : (Fin g → ℂ)))) / a i z - fderiv ℂ (a j) z (Θ.mulVec (star (l : (Fin g → ℂ)))) / a j z)) → ∀ z w, Θ.mulVec (star z) ⬝ᵥ Hm.mulVec (star w) = Θ.mulVec (star w) ⬝ᵥ Hm.mulVec (star z) := by
  intro g Λ hd hsp Hm Θ ι U a k e hU hinv hcov ha hf hk hkc hkp z w
  have key : ∑ m, antiRow Θ m z * ((Real.pi) • antiRow Hm m) w
      = ∑ m, antiRow Θ m w * ((Real.pi) • antiRow Hm m) z := by
    refine symm_of_cocycle g Λ hd hsp ι U (fun i m x => fderiv ℂ (a i) x (Pi.single m 1) / a i x)
      k (fun m => antiRow Θ m) (fun m => (Real.pi) • antiRow Hm m) (fun m u => antiRow_I Θ m u)
      ?_ hU hinv hcov ?_ ?_ hk hkc ?_ z w
    · intro m u
      simp only [ContinuousLinearMap.smul_apply, antiRow_I, Complex.real_smul]
      ring
    · intro i m
      have h1 : DifferentiableOn ℂ (fun x => fderiv ℂ (a i) x (Pi.single m 1)) (U i) :=
        ((GlobalTheory.cauchyRiemann_iff_differentiableOn_complex g (U i) (a i) (hU i)).2 (ha i).1).2 _
      have h2 : DifferentiableOn ℂ (fun x => (a i x)⁻¹) (U i) := (ha i).1.inv (ha i).2
      exact (h1.mul h2).congr fun x _ => div_eq_mul_inv _ _
    · intro i m l x hx
      simp only [ContinuousLinearMap.smul_apply, antiRow_apply, Complex.real_smul]
      exact logDeriv_translate (hU i) (ha i).1 (ha i).2 (l : Fin g → ℂ) _ (e l)
        (fun y hy => hinv i l y hy) (fun y hy => hf i l y hy) m hx
    · intro i j l x hx
      rw [hkp i j l x hx, clm_eq_sum (fderiv ℂ (a i) x), clm_eq_sum (fderiv ℂ (a j) x),
        Finset.sum_div, Finset.sum_div]
      simp only [antiRow_apply, mul_div_assoc]
  have e1 : ∀ x y : Fin g → ℂ, ∑ m, antiRow Θ m x * ((Real.pi) • antiRow Hm m) y
      = Real.pi * (Θ.mulVec (star x) ⬝ᵥ Hm.mulVec (star y)) := by
    intro x y
    simp only [ContinuousLinearMap.smul_apply, antiRow_apply, Complex.real_smul, dotProduct,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [e1, e1] at key
  exact mul_left_cancel₀ hπ key

end GlobalTheory.PeriodSymm
