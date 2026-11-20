import Formalism.HermitianCurvature.LatticeHerglotzBound
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MiddleThirdEstimate

open Filter Topology Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.MeanBoundsLimits

open Classical

open Formalism.FourierDecayAlt.crystallineComparison

section Mean

variable {Λ : Type} [AddCommGroup Λ] {LIM : (Λ → ℂ) → ℂ}

/- English proof (translation)
Assemble the required witnesses or components as `⟨‖c‖, fun _ => le_rfl⟩`.
-/
theorem bdd_const (c : ℂ) : Bdd (fun _ : Λ => c) := ⟨‖c‖, fun _ => le_rfl⟩

/- English proof (translation)
Establish `e : (fun _ : Λ => c) = c • (fun _ : Λ => (1 : ℂ))` using `by funext; simp`. Rewrite using `[e, hM.2.1 c _ (bdd_const 1), hM.2.2.2.1, mul_one]`.
-/
theorem lim_const (hM : IsMean LIM) (c : ℂ) : LIM (fun _ : Λ => c) = c := by
  have e : (fun _ : Λ => c) = c • (fun _ : Λ => (1 : ℂ)) := by funext; simp
  rw [e, hM.2.1 c _ (bdd_const 1), hM.2.2.2.1, mul_one]

/- English proof (translation)
Establish `hqb : Bdd q` using `⟨B, hq⟩`. Establish `hre : ∀ x, |(q x).re| ≤ B` using `fun x => (Complex.abs_re_le_norm _).trans (hq x)`. Establish `h1` using `hM.2.2.1 (q + fun _ => (B : ℂ)) (Bdd_add hqb) (fun x => by`. Simplify using `only [Pi.add_apply, Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, hr x, add_zero]`. Conclude with `⟨by linarith [(abs_le.mp (hre x)).1], trivial⟩)`.

Rewrite `h1` using `[hM.1 _ _ hqb (bdd_const _), lim_const hM]`. Establish `hneg : Bdd ((-1 : ℂ) • q)` using `⟨B, fun x => by simpa using hq x⟩`. Establish `h2` using `hM.2.2.1 ((fun _ => (B : ℂ)) + (-1 : ℂ) • q) (bdd_const_add hneg) (fun x => by`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, hr x]`. Evaluate the numerical expressions.

Combine the linear relations using `[(abs_le.mp (hre x)).2])`. Rewrite `h2` using `[hM.1 _ _ (bdd_const _) hneg, lim_const hM, hM.2.1 _ _ hqb]`. Simplify using `only [Complex.add_im, Complex.ofReal_im, Complex.add_re, Complex.ofReal_re] at h1 h2`. Prove the components needed by the constructor for the conclusion. Combine the linear relations using `[h1.2]`.

Simplify using `at h2`. Combine the linear relations using `[h2.1]`. Use `where Bdd_add {g : Λ → ℂ} (hg : Bdd g) : Bdd (g + fun _ => (B : ℂ)) := Formalism.FourierDecayAlt.P.E2.bdd_add' hg (bdd_const _) bdd_const_add {g : Λ → ℂ} (hg : Bdd g) : Bdd ((fun _ => (B : ℂ)) + g) := Formalism.FourierDecayAlt.P.E2.bdd_add' (bdd_const _) hg`.
-/
theorem lim_real (hM : IsMean LIM) (q : Λ → ℂ) (B : ℝ) (hq : ∀ x, ‖q x‖ ≤ B)
    (hr : ∀ x, (q x).im = 0) : (LIM q).im = 0 ∧ (LIM q).re ≤ B := by
  have hqb : Bdd q := ⟨B, hq⟩
  have hre : ∀ x, |(q x).re| ≤ B := fun x => (Complex.abs_re_le_norm _).trans (hq x)
  have h1 := hM.2.2.1 (q + fun _ => (B : ℂ)) (Bdd_add hqb) (fun x => by
    simp only [Pi.add_apply, Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im,
      hr x, add_zero]
    exact ⟨by linarith [(abs_le.mp (hre x)).1], trivial⟩)
  rw [hM.1 _ _ hqb (bdd_const _), lim_const hM] at h1
  have hneg : Bdd ((-1 : ℂ) • q) := ⟨B, fun x => by simpa using hq x⟩
  have h2 := hM.2.2.1 ((fun _ => (B : ℂ)) + (-1 : ℂ) • q) (bdd_const_add hneg) (fun x => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.add_re, Complex.ofReal_re,
      Complex.add_im, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, hr x]
    norm_num
    linarith [(abs_le.mp (hre x)).2])
  rw [hM.1 _ _ (bdd_const _) hneg, lim_const hM, hM.2.1 _ _ hqb] at h2
  simp only [Complex.add_im, Complex.ofReal_im, Complex.add_re, Complex.ofReal_re] at h1 h2
  constructor
  · linarith [h1.2]
  · simp at h2; linarith [h2.1]
where
  Bdd_add {g : Λ → ℂ} (hg : Bdd g) : Bdd (g + fun _ => (B : ℂ)) :=
    Formalism.FourierDecayAlt.P.E2.bdd_add' hg (bdd_const _)
  bdd_const_add {g : Λ → ℂ} (hg : Bdd g) : Bdd ((fun _ => (B : ℂ)) + g) :=
    Formalism.FourierDecayAlt.P.E2.bdd_add' (bdd_const _) hg

/- English proof (translation)
Introduce `Λ _ LIM g B hM hg`. Establish `hB : 0 ≤ B` using `(norm_nonneg _).trans (hg 0)`. Use `set z := LIM g with hz`. Distinguish the cases in `z0 : z = 0`. Rewrite using `[z0, norm_zero]`.

Conclude with `hB`. Establish `hn : (‖z‖ : ℂ) ≠ 0` using `by exact_mod_cast norm_ne_zero_iff.mpr z0`. Use `set u : ℂ := starRingEnd ℂ z / ‖z‖ with hu`. Establish `hu1 : ‖u‖ = 1`. Rewrite using `[hu, norm_div, Complex.norm_conj, Complex.norm_real, norm_norm, div_self]`.

Conclude with `norm_ne_zero_iff.mpr z0`. Establish `hgb : Bdd g` using `⟨B, hg⟩`. Use `set h := u • g with hh`. Establish `hhb : ∀ x, ‖h x‖ ≤ B` using `fun x => by`. Simplify using `only [hh, Pi.smul_apply, smul_eq_mul, norm_mul, hu1, one_mul]`.

Conclude with `hg x`. Establish `hLh : LIM h = ‖z‖`. Rewrite using `[hh, hM.2.1 u g hgb, ← hz, hu, div_mul_eq_mul_div, Complex.conj_mul', pow_two, mul_div_assoc, div_self hn, mul_one]`. Use `set hr : Λ → ℂ := fun x => ((h x).re : ℂ)`. Use `set hi : Λ → ℂ := fun x => ((h x).im : ℂ)`.

Establish `hrb : ∀ x, ‖hr x‖ ≤ B` using `fun x => by`. Simplify using `only [hr, Complex.norm_real, Real.norm_eq_abs]`. Conclude with `(Complex.abs_re_le_norm _).trans (hhb x)`. Establish `hib : ∀ x, ‖hi x‖ ≤ B` using `fun x => by`. Simplify using `only [hi, Complex.norm_real, Real.norm_eq_abs]`.

Conclude with `(Complex.abs_im_le_norm _).trans (hhb x)`. Establish `hsplit : h = hr + Complex.I • hi`. Use function extensionality and compare the values at `x`. Simplify using `only [hr, hi, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[mul_comm Complex.I]`.

Conclude with `(Complex.re_add_im (h x)).symm`. Establish `hL` using `congrArg LIM hsplit`. Rewrite `hL` using `[hM.1 _ _ ⟨B, hrb⟩ (Formalism.FourierDecayAlt.P.E2.bdd_smul' _ ⟨B, hib⟩), hM.2.1 _ _ ⟨B, hib⟩, hLh]`. Establish `R` using `lim_real hM hr B hrb (fun x => by simp [hr])`. Establish `I` using `lim_real hM hi B hib (fun x => by simp [hi])`.

Use `congrArg Complex.re hL` as an intermediate fact. Simplify using `only [Complex.ofReal_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, I.1, zero_sub, neg_zero, add_zero] at this`. Combine the linear relations using `[R.2]`.
-/
theorem meanBound_ok : MeanBound := by
  intro Λ _ LIM g B hM hg
  have hB : 0 ≤ B := (norm_nonneg _).trans (hg 0)
  set z := LIM g with hz
  by_cases z0 : z = 0
  · rw [z0, norm_zero]; exact hB
  have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr z0
  set u : ℂ := starRingEnd ℂ z / ‖z‖ with hu
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_div, Complex.norm_conj, Complex.norm_real, norm_norm, div_self]
    exact norm_ne_zero_iff.mpr z0
  have hgb : Bdd g := ⟨B, hg⟩
  set h := u • g with hh
  have hhb : ∀ x, ‖h x‖ ≤ B := fun x => by
    simp only [hh, Pi.smul_apply, smul_eq_mul, norm_mul, hu1, one_mul]; exact hg x
  have hLh : LIM h = ‖z‖ := by
    rw [hh, hM.2.1 u g hgb, ← hz, hu, div_mul_eq_mul_div, Complex.conj_mul', pow_two,
      mul_div_assoc, div_self hn, mul_one]
  set hr : Λ → ℂ := fun x => ((h x).re : ℂ)
  set hi : Λ → ℂ := fun x => ((h x).im : ℂ)
  have hrb : ∀ x, ‖hr x‖ ≤ B := fun x => by
    simp only [hr, Complex.norm_real, Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans (hhb x)
  have hib : ∀ x, ‖hi x‖ ≤ B := fun x => by
    simp only [hi, Complex.norm_real, Real.norm_eq_abs]
    exact (Complex.abs_im_le_norm _).trans (hhb x)
  have hsplit : h = hr + Complex.I • hi := by
    funext x; simp only [hr, hi, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm Complex.I]; exact (Complex.re_add_im (h x)).symm
  have hL := congrArg LIM hsplit
  rw [hM.1 _ _ ⟨B, hrb⟩ (Formalism.FourierDecayAlt.P.E2.bdd_smul' _ ⟨B, hib⟩), hM.2.1 _ _ ⟨B, hib⟩, hLh] at hL
  have R := lim_real hM hr B hrb (fun x => by simp [hr])
  have I := lim_real hM hi B hib (fun x => by simp [hi])
  have := congrArg Complex.re hL
  simp only [Complex.ofReal_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, I.1, zero_sub, neg_zero, add_zero] at this
  linarith [R.2]

end Mean

/- English proof (translation)
Assemble the required witnesses or components as `⟨B * B, fun x => (norm_inner_le_norm _ _).trans (mul_le_mul (hp _) (hq _) (norm_nonneg _) ((norm_nonneg _).trans (hp x)))⟩`.
-/
theorem bdd_inner {f : ℕ} {Λ : AddSubgroup (V f)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (p q : V f → H) (B : ℝ) (hp : ∀ x, ‖p x‖ ≤ B) (hq : ∀ x, ‖q x‖ ≤ B)
    (σ : V f) : Bdd (fun x : Λ => inner ℂ (p x) (q ((x : V f) + σ))) :=
  ⟨B * B, fun x => (norm_inner_le_norm _ _).trans
    (mul_le_mul (hp _) (hq _) (norm_nonneg _) ((norm_nonneg _).trans (hp x)))⟩

/- English proof (translation)
Establish `hD : Bdd (fun x : Λ => F x - L)`. Take `⟨b, hb⟩` from `hF`. Conclude with `⟨b + ‖L‖, fun x => (norm_sub_le _ _).trans (by linarith [hb x])⟩`. Establish `h0 : LIM (fun x : Λ => F x - L) = 0`. Apply `hM.2 _ hD` to reduce the goal to its premises.

Use `(ht.comp (tendsto_comap (f := fun x : Λ => (x : V f)))).sub_const L` as an intermediate fact. Simplify `this` using `[Function.comp_def]`. Establish `e : (fun x : Λ => F x) = (fun x : Λ => F x - L) + (fun _ => L)` using `by funext; simp`. Rewrite using `[e, hM.1.1 _ _ hD (bdd_const L), h0, lim_const hM.1, zero_add]`.
-/
theorem lim_of_tendsto {f : ℕ} {Λ : AddSubgroup (V f)} {LIM : (Λ → ℂ) → ℂ}
    (hM : IsMeanInf Λ LIM) (F : V f → ℂ) (L : ℂ) (hF : Bdd (fun x : Λ => F x))
    (ht : Tendsto F (atInfAll f) (𝓝 L)) : LIM (fun x : Λ => F x) = L := by
  have hD : Bdd (fun x : Λ => F x - L) := by
    obtain ⟨b, hb⟩ := hF
    exact ⟨b + ‖L‖, fun x => (norm_sub_le _ _).trans (by linarith [hb x])⟩
  have h0 : LIM (fun x : Λ => F x - L) = 0 := by
    apply hM.2 _ hD
    have := (ht.comp (tendsto_comap (f := fun x : Λ => (x : V f)))).sub_const L
    simpa [Function.comp_def] using this
  have e : (fun x : Λ => F x) = (fun x : Λ => F x - L) + (fun _ => L) := by funext; simp
  rw [e, hM.1.1 _ _ hD (bdd_const L), h0, lim_const hM.1, zero_add]

/- English proof (translation)
Introduce `f Λ LIM H _ _ a r Nh B hM hb haa har hra`. Establish `hpa : ∀ x, ‖a x‖ ≤ B` using `fun x => (hb x).1`. Establish `hpr : ∀ x, ‖r x‖ ≤ B` using `fun x => (hb x).2`. Prove the components needed by the constructor for the conclusion. Introduce `σ hσ`.

Establish `e : (fun x : Λ => inner ℂ (a x + r x) (a ((x : V f) + σ) + r ((x : V f) + σ))) = (fun x : Λ => inner ℂ (a x) (a ((x : V f) + σ))) + (fun x : Λ => inner ℂ (a x) (r ((x : V f) + σ))) + ((fun x : Λ => inner ℂ (r x) (a ((x : V f) + σ))) + (fun x : Λ => inner ℂ (r x) (r ((x : V f) + σ …`. Use function extensionality and compare the values at `x`. Simplify using `only [Pi.add_apply, inner_add_left, inner_add_right]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, hM.1.1 _ _ (Formalism.FourierDecayAlt.P.E2.bdd_add' (bdd_inner a a B hpa hpa σ) (bdd_inner a r B hpa hpr σ)) (Formalism.FourierDecayAlt.P.E2.bdd_add' (bdd_inner r a B hpr hpa σ) (bdd_inner r r B hpr hpr σ)), hM.1.1 _ _ (bdd_inner a a B hpa hpa σ) (bdd_inner a r B hpa hpr σ), …`.

Expand and normalize the polynomial expressions, which then agree. Introduce `S c hS`. Establish `hS' : ∀ σ ∈ S, σ ∈ Λ` using `hS`. Establish `hpd` using `Formalism.FourierDecayAlt.P.mean_matrix_posDef Λ H LIM hM.1.1 hM.1.2.1 (fun g hg hpos => (hM.1.2.2.1 g hg hpos).1) hM.1.2.2.2.2 (fun x => r x) B (fun x => hpr x) (S.subtype (fun x => x ∈ Λ)) (fun σ => c σ)`. Establish `eq : (∑ σ ∈ S, ∑ σ' ∈ S, (LIM fun x : Λ => inner ℂ (r x) (r ((x : V f) + (σ - σ')))) * c σ * starRingEnd ℂ (c σ')) = ∑ σ ∈ S.subtype (fun x => x ∈ Λ), ∑ σ' ∈ S.subtype (fun x => x ∈ Λ), (LIM fun x : Λ => inner ℂ (r x) (r ((x + (σ - σ') : Λ) : V f))) * c σ * starRingEnd ℂ (c σ')`.

Rewrite using `[← Finset.sum_subtype_of_mem (p := fun x => x ∈ Λ) _ hS']`. Use `Finset.sum_congr rfl (fun σ _ => ?_)` and prove the remaining obligations. Rewrite using `[← Finset.sum_subtype_of_mem (p := fun x => x ∈ Λ) _ hS']`. Use `Finset.sum_congr rfl (fun σ' _ => ?_)` and prove the remaining obligations. Simplify using `only [AddSubgroup.coe_add, AddSubgroup.coe_sub]`.

Use `beta_reduce`. Rewrite using `[eq]`. Conclude with `hpd`.
-/
theorem meanSplit_ok : MeanSplit := by
  intro f Λ LIM H _ _ a r Nh B hM hb haa har hra
  have hpa : ∀ x, ‖a x‖ ≤ B := fun x => (hb x).1
  have hpr : ∀ x, ‖r x‖ ≤ B := fun x => (hb x).2
  constructor
  · intro σ hσ
    have e : (fun x : Λ => inner ℂ (a x + r x) (a ((x : V f) + σ) + r ((x : V f) + σ))) =
        (fun x : Λ => inner ℂ (a x) (a ((x : V f) + σ))) +
        (fun x : Λ => inner ℂ (a x) (r ((x : V f) + σ))) +
        ((fun x : Λ => inner ℂ (r x) (a ((x : V f) + σ))) +
         (fun x : Λ => inner ℂ (r x) (r ((x : V f) + σ)))) := by
      funext x; simp only [Pi.add_apply, inner_add_left, inner_add_right]; ring
    rw [e, hM.1.1 _ _ (Formalism.FourierDecayAlt.P.E2.bdd_add' (bdd_inner a a B hpa hpa σ) (bdd_inner a r B hpa hpr σ))
        (Formalism.FourierDecayAlt.P.E2.bdd_add' (bdd_inner r a B hpr hpa σ) (bdd_inner r r B hpr hpr σ)),
      hM.1.1 _ _ (bdd_inner a a B hpa hpa σ) (bdd_inner a r B hpa hpr σ),
      hM.1.1 _ _ (bdd_inner r a B hpr hpa σ) (bdd_inner r r B hpr hpr σ),
      lim_of_tendsto hM (fun x => inner ℂ (a x) (a (x + σ))) (Nh σ) (bdd_inner a a B hpa hpa σ)
        (haa σ hσ),
      lim_of_tendsto hM (fun x => inner ℂ (a x) (r (x + σ))) 0 (bdd_inner a r B hpa hpr σ)
        (har σ hσ),
      lim_of_tendsto hM (fun x => inner ℂ (r x) (a (x + σ))) 0 (bdd_inner r a B hpr hpa σ)
        (hra σ hσ)]
    ring
  · intro S c hS
    have hS' : ∀ σ ∈ S, σ ∈ Λ := hS
    have hpd := Formalism.FourierDecayAlt.P.mean_matrix_posDef Λ H LIM hM.1.1 hM.1.2.1
      (fun g hg hpos => (hM.1.2.2.1 g hg hpos).1) hM.1.2.2.2.2 (fun x => r x) B (fun x => hpr x)
      (S.subtype (fun x => x ∈ Λ)) (fun σ => c σ)
    have eq : (∑ σ ∈ S, ∑ σ' ∈ S, (LIM fun x : Λ => inner ℂ (r x) (r ((x : V f) + (σ - σ')))) *
        c σ * starRingEnd ℂ (c σ')) =
        ∑ σ ∈ S.subtype (fun x => x ∈ Λ), ∑ σ' ∈ S.subtype (fun x => x ∈ Λ),
          (LIM fun x : Λ => inner ℂ (r x) (r ((x + (σ - σ') : Λ) : V f))) * c σ *
            starRingEnd ℂ (c σ') := by
      rw [← Finset.sum_subtype_of_mem (p := fun x => x ∈ Λ) _ hS']
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      rw [← Finset.sum_subtype_of_mem (p := fun x => x ∈ Λ) _ hS']
      refine Finset.sum_congr rfl (fun σ' _ => ?_)
      simp only [AddSubgroup.coe_add, AddSubgroup.coe_sub]
    beta_reduce
    rw [eq]
    exact hpd

end Formalism.FourierDecayAlt.P.MeanBoundsLimits

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.MeanBoundsLimits.meanBound_ok`.
-/
theorem Formalism.FourierDecayAlt.P.mean_bound_estimate : Formalism.FourierDecayAlt.crystallineComparison.MeanBound := Formalism.FourierDecayAlt.P.MeanBoundsLimits.meanBound_ok
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.MeanBoundsLimits.meanSplit_ok`.
-/
theorem Formalism.FourierDecayAlt.P.mean_split_identity : Formalism.FourierDecayAlt.crystallineComparison.MeanSplit := Formalism.FourierDecayAlt.P.MeanBoundsLimits.meanSplit_ok
