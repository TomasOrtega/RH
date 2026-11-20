import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointHeight
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import ReciprocityTheory.SemistableReduction.SJCoreA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFirstCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurePreservingPolarGaussianProbabilityComplexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianRadialLawProbabilityLogIntegrableMeanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianFirstCoordsMeasurePreservingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockSphereProbZeroSetEqZeroStatement

noncomputable section

namespace GlobalTheory.SphereMeanDrop

open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights

/- English proof (translation)
Establish `hp` using `GlobalTheory.T.measurePreserving_polar_gaussianProbabilityComplexSpace n hn`. Use `haveI := (GlobalTheory.T.gaussianRadialLawProbability_log_integrable_mean n hn).1`. Use `haveI : IsProbabilityMeasure (sphereProb n) := isProbabilityMeasure_sphereProb hn`. Rewrite using `[← hp.map_eq]`. Conclude with `Measure.isProbabilityMeasure_map hp.measurable.aemeasurable`.
-/
theorem isProbabilityMeasure_gaussProb {n : ℕ} (hn : 0 < n) : IsProbabilityMeasure (gaussProb n) := by
  have hp := GlobalTheory.T.measurePreserving_polar_gaussianProbabilityComplexSpace n hn
  haveI := (GlobalTheory.T.gaussianRadialLawProbability_log_integrable_mean n hn).1
  haveI : IsProbabilityMeasure (sphereProb n) := isProbabilityMeasure_sphereProb hn
  rw [← hp.map_eq]
  exact Measure.isProbabilityMeasure_map hp.measurable.aemeasurable

/- English proof (translation)
Use `conv_lhs => rw [g.as_sum]`. Use `conv_rhs => rw [g.as_sum]`. Rewrite using `[map_sum, map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun s hs => ?_` and prove the remaining obligations. Rewrite using `[eval_monomial, eval_monomial]`.

Establish `h1 : (s.prod fun p e => (r p.1 * x p) ^ e) = (s.prod fun p e => r p.1 ^ e) * s.prod fun p e => x p ^ e`. Rewrite using `[← Finsupp.prod_mul]`. Use `congr 1`. Use function extensionality and compare the values at `p e`. Rewrite using `[mul_pow]`.

Establish `h2 : (s.prod fun p e => r p.1 ^ e) = ∏ b, r b ^ a b`. Rewrite using `[Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type]`. Use `Finset.prod_congr rfl fun b _ => ?_` and prove the remaining obligations. Use `show ∏ y, r b ^ s (b, y) = _`. Rewrite using `[Finset.prod_pow_eq_pow_sum, hm s hs b]`.

Rewrite using `[h1, h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eval_blockScale {B n : ℕ} (a : Fin B → ℕ) (g : MvPolynomial (Fin B × Fin n) ℂ)
    (hm : IsMultiHomogeneous a g) (r : Fin B → ℂ) (x : Fin B × Fin n → ℂ) :
    eval (fun p => r p.1 * x p) g = (∏ b, r b ^ a b) * eval x g := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [eval_monomial, eval_monomial]
  have h1 : (s.prod fun p e => (r p.1 * x p) ^ e) =
      (s.prod fun p e => r p.1 ^ e) * s.prod fun p e => x p ^ e := by
    rw [← Finsupp.prod_mul]
    congr 1
    funext p e
    rw [mul_pow]
  have h2 : (s.prod fun p e => r p.1 ^ e) = ∏ b, r b ^ a b := by
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun b _ => ?_
    show ∏ y, r b ^ s (b, y) = _
    rw [Finset.prod_pow_eq_pow_sum, hm s hs b]
  rw [h1, h2]
  ring

/- English proof (translation)
Unfold `GlobalTheory.ChowHt.linSubst`. Establish `hfun : (fun p : Fin B × Fin N => ∑ k : Fin n, C ((Matrix.of fun (j : Fin N) (k : Fin n) => if (j : ℕ) = (k : ℕ) then (1 : ℂ) else 0) p.2 k) * X (p.1, k)) = fun p => X (p.1, Fin.castLE h p.2)`. Use function extensionality and compare the values at `p`. Rewrite using `[Fintype.sum_eq_single (Fin.castLE h p.2)]`. Simplify using the standard rewrite rules.

Introduce `k hk`. Establish `hne : (p.2 : ℕ) ≠ (k : ℕ)` using `fun he => hk (Fin.ext (by rw [Fin.coe_castLE]; exact he.symm))`. Simplify using `[Matrix.of_apply, hne]`. Rewrite using `[hfun]`. Establish `hal : (aeval fun p : Fin B × Fin N => (X (p.1, Fin.castLE h p.2) : MvPolynomial (Fin B × Fin n) ℂ)) = rename (fun p : Fin B × Fin N => (p.1, Fin.castLE h p.2))` using `MvPolynomial.algHom_ext fun p => by simp`.

Rewrite using `[hal]`.
-/
theorem linSubst_incl {B N n : ℕ} (h : N ≤ n) (f : MvPolynomial (Fin B × Fin N) ℂ) :
    GlobalTheory.ChowHt.linSubst (Matrix.of fun (j : Fin N) (k : Fin n) =>
                 if (j : ℕ) = (k : ℕ) then (1 : ℂ) else 0) f =
      rename (fun p : Fin B × Fin N => (p.1, Fin.castLE h p.2)) f := by
  unfold GlobalTheory.ChowHt.linSubst
  have hfun : (fun p : Fin B × Fin N => ∑ k : Fin n, C ((Matrix.of fun (j : Fin N) (k : Fin n) =>
      if (j : ℕ) = (k : ℕ) then (1 : ℂ) else 0) p.2 k) * X (p.1, k)) =
      fun p => X (p.1, Fin.castLE h p.2) := by
    funext p
    rw [Fintype.sum_eq_single (Fin.castLE h p.2)]
    · simp
    · intro k hk
      have hne : (p.2 : ℕ) ≠ (k : ℕ) := fun he => hk (Fin.ext (by rw [Fin.coe_castLE]; exact he.symm))
      simp [Matrix.of_apply, hne]
  rw [hfun]
  have hal : (aeval fun p : Fin B × Fin N => (X (p.1, Fin.castLE h p.2) : MvPolynomial (Fin B × Fin n) ℂ)) =
      rename (fun p : Fin B × Fin N => (p.1, Fin.castLE h p.2)) :=
    MvPolynomial.algHom_ext fun p => by simp
  rw [hal]

/- English proof (translation)
Establish `he : Function.Injective (fun p : Fin B × Fin N => (p.1, Fin.castLE h p.2))`. Introduce `p q hpq`. Simplify using `only [Prod.mk.injEq] at hpq`. Conclude with `Prod.ext hpq.1 (Fin.castLE_injective h hpq.2)`. Introduce `s hs b`.

Rewrite `hs` using `[support_rename_of_injective he, Finset.mem_image]`. Take `⟨t, ht, rfl⟩` from `hs`. Rewrite using `[← hm t ht b]`. Set `emb : Fin N ↪ Fin n` to `⟨Fin.castLE h, Fin.castLE_injective h⟩`. Establish `hsub : (Finset.univ.map emb) ⊆ Finset.univ` using `Finset.subset_univ _`.

Rewrite using `[← Finset.sum_subset hsub ?_]`. Rewrite using `[Finset.sum_map]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Conclude with `Finsupp.mapDomain_apply he t (b, j)`. Introduce `j _ hj`.

Apply `Finsupp.mapDomain_notin_range` to reduce the goal to its premises. Introduce and unpack `⟨q, hq⟩`. Apply `hj` to reduce the goal to its premises. Simplify using `only [Prod.mk.injEq] at hq`. Rewrite using `[Finset.mem_map]`.

Conclude with `⟨q.2, Finset.mem_univ _, hq.2⟩`.
-/
theorem isMultiHomogeneous_rename_castLE {B N n : ℕ} (h : N ≤ n) (a : Fin B → ℕ)
    (f : MvPolynomial (Fin B × Fin N) ℂ) (hm : IsMultiHomogeneous a f) :
    IsMultiHomogeneous a (rename (fun p : Fin B × Fin N => (p.1, Fin.castLE h p.2)) f) := by
  have he : Function.Injective (fun p : Fin B × Fin N => (p.1, Fin.castLE h p.2)) := by
    intro p q hpq
    simp only [Prod.mk.injEq] at hpq
    exact Prod.ext hpq.1 (Fin.castLE_injective h hpq.2)
  intro s hs b
  rw [support_rename_of_injective he, Finset.mem_image] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  rw [← hm t ht b]
  let emb : Fin N ↪ Fin n := ⟨Fin.castLE h, Fin.castLE_injective h⟩
  have hsub : (Finset.univ.map emb) ⊆ Finset.univ := Finset.subset_univ _
  rw [← Finset.sum_subset hsub ?_]
  · rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact Finsupp.mapDomain_apply he t (b, j)
  · intro j _ hj
    apply Finsupp.mapDomain_notin_range
    rintro ⟨q, hq⟩
    apply hj
    simp only [Prod.mk.injEq] at hq
    rw [Finset.mem_map]
    exact ⟨q.2, Finset.mem_univ _, hq.2⟩

/- English proof (translation)
Take `⟨hρ, hlogi, hlog⟩` from `GlobalTheory.T.gaussianRadialLawProbability_log_integrable_mean n hn`. Use `haveI := hρ`. Use `haveI : IsProbabilityMeasure (sphereProb n) := isProbabilityMeasure_sphereProb hn`. Use `haveI : IsProbabilityMeasure (gaussProb n) := isProbabilityMeasure_gaussProb hn`. Establish `hΦm : Measurable fun x : Fin B → EuclideanSpace ℂ (Fin n) => Real.log ‖eval (fun p => WithLp.ofLp (x p.1) p.2) g‖` using `Real.measurable_log.comp (Continuous.measurable (continuous_norm.comp ((continuous_eval g).comp (by fun_prop))))`.

Establish `hpol : MeasurePreserving (fun q : (Fin B → UnitSphereC n) × (Fin B → Ioi (0:ℝ)) => fun b => ((q.2 b : ℝ)) • ((q.1 b : EuclideanSpace ℂ (Fin n)))) ((Measure.pi fun _ : Fin B => sphereProb n).prod (Measure.pi fun _ : Fin B => radProb n)) (Measure.pi fun _ : Fin B => gaussProb n)`. Establish `h1` using `measurePreserving_pi (fun _ : Fin B => (sphereProb n).prod (radProb n)) (fun _ => gaussProb n) (fun _ => GlobalTheory.T.measurePreserving_polar_gaussianProbabilityComplexSpace n hn)`. Establish `h2` using `MeasurePreserving.symm _ (measurePreserving_arrowProdEquivProdArrow (UnitSphereC n) (Ioi (0:ℝ)) (Fin B) (fun _ => sphereProb n) (fun _ => radProb n))`. Conclude with `h1.comp h2`. Establish `hpt : ∀ q : (Fin B → UnitSphereC n) × (Fin B → Ioi (0:ℝ)), eval (blockPoint q.1) g ≠ 0 → Real.log ‖eval (fun p => WithLp.ofLp (((q.2 p.1 : ℝ)) • ((q.1 p.1 : EuclideanSpace ℂ (Fin n)))) p.2) g‖ = Real.log ‖eval (blockPoint q.1) g‖ + ∑ b, (δ : ℝ) * Real.log (q.2 b : ℝ)`.

Introduce `q hq`. Establish `hr : ∀ b, (0:ℝ) < q.2 b` using `fun b => (q.2 b).2`. Establish `hfun : (fun p : Fin B × Fin n => WithLp.ofLp (((q.2 p.1 : ℝ)) • ((q.1 p.1 : EuclideanSpace ℂ (Fin n)))) p.2) = fun p => ((q.2 p.1 : ℝ) : ℂ) * blockPoint q.1 p`. Use function extensionality and compare the values at `p`. Simplify using `[blockPoint, spherePoint, Complex.real_smul]`.

Establish `hprod : ‖∏ b, (((q.2 b : ℝ) : ℂ)) ^ δ‖ = ∏ b, ((q.2 b : ℝ)) ^ δ`. Rewrite using `[norm_prod]`. Use `Finset.prod_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hr b)]`. Establish `hs` using `eval_blockScale (fun _ => δ) g hm (fun b => ((q.2 b : ℝ) : ℂ)) (blockPoint q.1)`.

Rewrite using `[hfun, hs, norm_mul, hprod, Real.log_mul (Finset.prod_ne_zero_iff.2 fun b _ => pow_ne_zero _ (hr b).ne') (norm_ne_zero_iff.2 hq), Real.log_prod (fun b _ => pow_ne_zero _ (hr b).ne')]`. Simplify using `only [Real.log_pow]`. Expand and normalize the polynomial expressions, which then agree. Establish `hnull` using `GlobalTheory.T.blockSphereProb_zeroSet_eq_zero_of_ne_zero B n _ g hn hg hm`. Establish `hae : ∀ᵐ q ∂((Measure.pi fun _ : Fin B => sphereProb n).prod (Measure.pi fun _ : Fin B => radProb n)), Real.log ‖eval (fun p => WithLp.ofLp (((q.2 p.1 : ℝ)) • ((q.1 p.1 : EuclideanSpace ℂ (Fin n)))) p.2) g‖ = Real.log ‖eval (blockPoint q.1) g‖ + ∑ b, (δ : ℝ) * Real.log (q.2 b : ℝ …`.

Establish `h0 : ((Measure.pi fun _ : Fin B => sphereProb n).prod (Measure.pi fun _ : Fin B => radProb n)) {q | eval (blockPoint q.1) g = 0} = 0`. Establish `hs : {q : (Fin B → UnitSphereC n) × (Fin B → Ioi (0:ℝ)) | eval (blockPoint q.1) g = 0} = {z | eval (blockPoint z) g = 0} ×ˢ univ`. Use extensionality with `q`. Simplify using the standard rewrite rules. Rewrite using `[hs, Measure.prod_prod]`.

Establish `: (Measure.pi fun _ : Fin B => sphereProb n) {z | eval (blockPoint z) g = 0} = 0` using `hnull`. Rewrite using `[this, zero_mul]`. Use `filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with q hq using hpt q hq`. Establish `hA : Integrable (fun z : Fin B → UnitSphereC n => Real.log ‖eval (blockPoint z) g‖) (Measure.pi fun _ : Fin B => sphereProb n)` using `ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable B n _ g hg hm`. Establish `hRi : ∀ b : Fin B, Integrable (fun r : Fin B → Ioi (0:ℝ) => Real.log (r b : ℝ)) (Measure.pi fun _ => radProb n)`.

Introduce `b`. Establish `he` using `measurePreserving_eval (fun _ : Fin B => radProb n) b`. Conclude with `(he.integrable_comp hlogi.aestronglyMeasurable).2 hlogi`. Establish `hRint : ∀ b : Fin B, ∫ r, Real.log ((r : Fin B → Ioi (0:ℝ)) b : ℝ) ∂(Measure.pi fun _ => radProb n) = radK (2 * n - 1) / radJ (2 * n - 1)`. Introduce `b`.

Establish `he` using `measurePreserving_eval (fun _ : Fin B => radProb n) b`. Establish `hm' : AEStronglyMeasurable (fun r : Ioi (0:ℝ) => Real.log (r : ℝ)) (Measure.map (Function.eval b) (Measure.pi fun _ : Fin B => radProb n))` using `(Real.measurable_log.comp measurable_subtype_coe).aestronglyMeasurable`. Use `integral_map he.measurable.aemeasurable hm'` as an intermediate fact. Rewrite `this` using `[he.map_eq]`. Rewrite using `[← hlog, this]`.

Establish `hAi : Integrable (fun q : (Fin B → UnitSphereC n) × (Fin B → Ioi (0:ℝ)) => Real.log ‖eval (blockPoint q.1) g‖) ((Measure.pi fun _ : Fin B => sphereProb n).prod (Measure.pi fun _ : Fin B => radProb n))` using `hA.comp_fst _`. Establish `hRsum : Integrable (fun r : Fin B → Ioi (0:ℝ) => ∑ b, (δ : ℝ) * Real.log (r b : ℝ)) (Measure.pi fun _ => radProb n)` using `integrable_finset_sum _ fun b _ => (hRi b).const_mul _`. Establish `hRi' : Integrable (fun q : (Fin B → UnitSphereC n) × (Fin B → Ioi (0:ℝ)) => ∑ b, (δ : ℝ) * Real.log (q.2 b : ℝ)) ((Measure.pi fun _ : Fin B => sphereProb n).prod (Measure.pi fun _ : Fin B => radProb n))` using `hRsum.comp_snd _`. Establish `hcomp` using `(hAi.add hRi').congr (hae.mono fun q h => h.symm)`. Use `⟨(hpol.integrable_comp hΦm.aestronglyMeasurable).1 hcomp, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hpol.map_eq, integral_map hpol.measurable.aemeasurable hΦm.aestronglyMeasurable, integral_congr_ae hae, integral_add hAi hRi', integral_fun_fst (fun z : Fin B → UnitSphereC n => Real.log ‖eval (blockPoint z) g‖), integral_fun_snd (fun r : Fin B → Ioi (0:ℝ) => ∑ b, (δ : ℝ) * Re …`. Simplify using `only [probReal_univ, one_smul, integral_const_mul, hRint, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Rewrite using `[blockSphereMean, blockSphereProb]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gauss_blockMean {B n : ℕ} (hn : 0 < n) (δ : ℕ) (g : MvPolynomial (Fin B × Fin n) ℂ)
    (hg : g ≠ 0) (hm : IsMultiHomogeneous (fun _ => δ) g) :
    Integrable (fun x : Fin B → EuclideanSpace ℂ (Fin n) =>
        Real.log ‖eval (fun p => WithLp.ofLp (x p.1) p.2) g‖) (Measure.pi fun _ => gaussProb n) ∧
    ∫ x, Real.log ‖eval (fun p => WithLp.ofLp (x p.1) p.2) g‖ ∂(Measure.pi fun _ => gaussProb n) =
      blockSphereMean B n g + (B : ℝ) * δ * (radK (2 * n - 1) / radJ (2 * n - 1)) := by
  obtain ⟨hρ, hlogi, hlog⟩ := GlobalTheory.T.gaussianRadialLawProbability_log_integrable_mean n hn
  haveI := hρ
  haveI : IsProbabilityMeasure (sphereProb n) := isProbabilityMeasure_sphereProb hn
  haveI : IsProbabilityMeasure (gaussProb n) := isProbabilityMeasure_gaussProb hn
  have hΦm : Measurable fun x : Fin B → EuclideanSpace ℂ (Fin n) =>
      Real.log ‖eval (fun p => WithLp.ofLp (x p.1) p.2) g‖ :=
    Real.measurable_log.comp (Continuous.measurable
      (continuous_norm.comp ((continuous_eval g).comp (by fun_prop))))

  have hpol : MeasurePreserving
      (fun q : (Fin B → UnitSphereC n) × (Fin B → Ioi (0:ℝ)) =>
        fun b => ((q.2 b : ℝ)) • ((q.1 b : EuclideanSpace ℂ (Fin n))))
      ((Measure.pi fun _ : Fin B => sphereProb n).prod (Measure.pi fun _ : Fin B => radProb n))
      (Measure.pi fun _ : Fin B => gaussProb n) := by
    have h1 := measurePreserving_pi (fun _ : Fin B => (sphereProb n).prod (radProb n))
      (fun _ => gaussProb n) (fun _ => GlobalTheory.T.measurePreserving_polar_gaussianProbabilityComplexSpace n hn)
    have h2 := MeasurePreserving.symm _ (measurePreserving_arrowProdEquivProdArrow (UnitSphereC n)
      (Ioi (0:ℝ)) (Fin B) (fun _ => sphereProb n) (fun _ => radProb n))
    exact h1.comp h2

  have hpt : ∀ q : (Fin B → UnitSphereC n) × (Fin B → Ioi (0:ℝ)), eval (blockPoint q.1) g ≠ 0 →
      Real.log ‖eval (fun p => WithLp.ofLp (((q.2 p.1 : ℝ)) • ((q.1 p.1 : EuclideanSpace ℂ (Fin n)))) p.2) g‖ =
        Real.log ‖eval (blockPoint q.1) g‖ + ∑ b, (δ : ℝ) * Real.log (q.2 b : ℝ) := by
    intro q hq
    have hr : ∀ b, (0:ℝ) < q.2 b := fun b => (q.2 b).2
    have hfun : (fun p : Fin B × Fin n =>
        WithLp.ofLp (((q.2 p.1 : ℝ)) • ((q.1 p.1 : EuclideanSpace ℂ (Fin n)))) p.2) =
        fun p => ((q.2 p.1 : ℝ) : ℂ) * blockPoint q.1 p := by
      funext p
      simp [blockPoint, spherePoint, Complex.real_smul]
    have hprod : ‖∏ b, (((q.2 b : ℝ) : ℂ)) ^ δ‖ = ∏ b, ((q.2 b : ℝ)) ^ δ := by
      rw [norm_prod]
      refine Finset.prod_congr rfl fun b _ => ?_
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hr b)]
    have hs := eval_blockScale (fun _ => δ) g hm (fun b => ((q.2 b : ℝ) : ℂ)) (blockPoint q.1)
    rw [hfun, hs, norm_mul, hprod,
      Real.log_mul (Finset.prod_ne_zero_iff.2 fun b _ => pow_ne_zero _ (hr b).ne')
        (norm_ne_zero_iff.2 hq),
      Real.log_prod (fun b _ => pow_ne_zero _ (hr b).ne')]
    simp only [Real.log_pow]
    ring
  have hnull := GlobalTheory.T.blockSphereProb_zeroSet_eq_zero_of_ne_zero B n _ g hn hg hm
  have hae : ∀ᵐ q ∂((Measure.pi fun _ : Fin B => sphereProb n).prod (Measure.pi fun _ : Fin B => radProb n)),
      Real.log ‖eval (fun p => WithLp.ofLp (((q.2 p.1 : ℝ)) • ((q.1 p.1 : EuclideanSpace ℂ (Fin n)))) p.2) g‖ =
        Real.log ‖eval (blockPoint q.1) g‖ + ∑ b, (δ : ℝ) * Real.log (q.2 b : ℝ) := by
    have h0 : ((Measure.pi fun _ : Fin B => sphereProb n).prod (Measure.pi fun _ : Fin B => radProb n))
        {q | eval (blockPoint q.1) g = 0} = 0 := by
      have hs : {q : (Fin B → UnitSphereC n) × (Fin B → Ioi (0:ℝ)) | eval (blockPoint q.1) g = 0} =
          {z | eval (blockPoint z) g = 0} ×ˢ univ := by
        ext q; simp
      rw [hs, Measure.prod_prod]
      have : (Measure.pi fun _ : Fin B => sphereProb n) {z | eval (blockPoint z) g = 0} = 0 := hnull
      rw [this, zero_mul]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with q hq using hpt q hq

  have hA : Integrable (fun z : Fin B → UnitSphereC n => Real.log ‖eval (blockPoint z) g‖)
      (Measure.pi fun _ : Fin B => sphereProb n) :=
    ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable B n _ g hg hm
  have hRi : ∀ b : Fin B, Integrable (fun r : Fin B → Ioi (0:ℝ) => Real.log (r b : ℝ))
      (Measure.pi fun _ => radProb n) := by
    intro b
    have he := measurePreserving_eval (fun _ : Fin B => radProb n) b
    exact (he.integrable_comp hlogi.aestronglyMeasurable).2 hlogi
  have hRint : ∀ b : Fin B, ∫ r, Real.log ((r : Fin B → Ioi (0:ℝ)) b : ℝ)
      ∂(Measure.pi fun _ => radProb n) = radK (2 * n - 1) / radJ (2 * n - 1) := by
    intro b
    have he := measurePreserving_eval (fun _ : Fin B => radProb n) b
    have hm' : AEStronglyMeasurable (fun r : Ioi (0:ℝ) => Real.log (r : ℝ))
        (Measure.map (Function.eval b) (Measure.pi fun _ : Fin B => radProb n)) :=
      (Real.measurable_log.comp measurable_subtype_coe).aestronglyMeasurable
    have := integral_map he.measurable.aemeasurable hm'
    rw [he.map_eq] at this
    rw [← hlog, this]
  have hAi : Integrable (fun q : (Fin B → UnitSphereC n) × (Fin B → Ioi (0:ℝ)) =>
      Real.log ‖eval (blockPoint q.1) g‖)
      ((Measure.pi fun _ : Fin B => sphereProb n).prod (Measure.pi fun _ : Fin B => radProb n)) :=
    hA.comp_fst _
  have hRsum : Integrable (fun r : Fin B → Ioi (0:ℝ) => ∑ b, (δ : ℝ) * Real.log (r b : ℝ))
      (Measure.pi fun _ => radProb n) :=
    integrable_finset_sum _ fun b _ => (hRi b).const_mul _
  have hRi' : Integrable (fun q : (Fin B → UnitSphereC n) × (Fin B → Ioi (0:ℝ)) =>
      ∑ b, (δ : ℝ) * Real.log (q.2 b : ℝ))
      ((Measure.pi fun _ : Fin B => sphereProb n).prod (Measure.pi fun _ : Fin B => radProb n)) :=
    hRsum.comp_snd _
  have hcomp := (hAi.add hRi').congr (hae.mono fun q h => h.symm)
  refine ⟨(hpol.integrable_comp hΦm.aestronglyMeasurable).1 hcomp, ?_⟩
  rw [← hpol.map_eq, integral_map hpol.measurable.aemeasurable hΦm.aestronglyMeasurable,
    integral_congr_ae hae, integral_add hAi hRi',
    integral_fun_fst (fun z : Fin B → UnitSphereC n => Real.log ‖eval (blockPoint z) g‖),
    integral_fun_snd (fun r : Fin B → Ioi (0:ℝ) => ∑ b, (δ : ℝ) * Real.log (r b : ℝ)),
    integral_finset_sum _ fun b _ => (hRi b).const_mul _]
  simp only [probReal_univ, one_smul, integral_const_mul, hRint, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [blockSphereMean, blockSphereProb]
  ring

/- English proof (translation)
Take `⟨a, rfl⟩ : ∃ a, N = a + 1` from `⟨N - 1, by omega⟩`. Take `⟨b, rfl⟩ : ∃ b, n = b + 1` from `⟨n - 1, by omega⟩`. Establish `e1 : 2 * (a + 1) - 1 = 2 * a + 1` using `by omega`. Establish `e2 : 2 * (b + 1) - 1 = 2 * b + 1` using `by omega`. Rewrite using `[e1, e2, radRatio_odd, radRatio_odd]`.

Simplify using `only [Nat.add_sub_cancel]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem radRatio_sub {N n : ℕ} (hN : 0 < N) (hn : 0 < n) :
    radK (2 * N - 1) / radJ (2 * N - 1) - radK (2 * n - 1) / radJ (2 * n - 1) =
      ((harmonic (N - 1) : ℝ) - (harmonic (n - 1) : ℝ)) / 2 := by
  obtain ⟨a, rfl⟩ : ∃ a, N = a + 1 := ⟨N - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, n = b + 1 := ⟨n - 1, by omega⟩
  have e1 : 2 * (a + 1) - 1 = 2 * a + 1 := by omega
  have e2 : 2 * (b + 1) - 1 = 2 * b + 1 := by omega
  rw [e1, e2, radRatio_odd, radRatio_odd]
  simp only [Nat.add_sub_cancel]
  ring

/- English proof (translation)
Establish `hn : 0 < n` using `lt_of_lt_of_le hN hNn`. Rewrite using `[linSubst_incl hNn]`. Use `set e : Fin B × Fin N → Fin B × Fin n := fun p => (p.1, Fin.castLE hNn p.2) with he`. Establish `heinj : Function.Injective e`. Introduce `p q hpq`.

Simplify using `only [he, Prod.mk.injEq] at hpq`. Conclude with `Prod.ext hpq.1 (Fin.castLE_injective hNn hpq.2)`. Use `set g := rename e f with hgdef`. Establish `hg : g ≠ 0` using `fun h0 => hf (rename_injective e heinj (by rw [← hgdef, h0, map_zero]))`. Establish `hgm : IsMultiHomogeneous (fun _ => δ) g` using `isMultiHomogeneous_rename_castLE hNn _ f hm`.

Establish `hIn` using `(gauss_blockMean hn δ g hg hgm).2`. Establish `hIN` using `(gauss_blockMean hN δ f hf hm).2`. Use `haveI : IsProbabilityMeasure (gaussProb N) := isProbabilityMeasure_gaussProb hN`. Establish `hproj : MeasurePreserving (fun (x : Fin B → EuclideanSpace ℂ (Fin n)) b => firstCoords hNn (x b)) (Measure.pi fun _ => gaussProb n) (Measure.pi fun _ => gaussProb N)` using `measurePreserving_pi _ _ fun _ => GlobalTheory.T.gaussian_first_coords_measure_preserving N n hNn`. Establish `hev : ∀ x : Fin B → EuclideanSpace ℂ (Fin n), eval (fun p => WithLp.ofLp (x p.1) p.2) g = eval (fun p => WithLp.ofLp (firstCoords hNn (x p.1)) p.2) f`.

Introduce `x`. Rewrite using `[hgdef, eval_rename]`. Both sides reduce to the same expression. Establish `hmeas : Measurable fun y : Fin B → EuclideanSpace ℂ (Fin N) => Real.log ‖eval (fun p => WithLp.ofLp (y p.1) p.2) f‖`. Use `Real.measurable_log.comp (Continuous.measurable ?_)` and prove the remaining obligations.

Conclude with `continuous_norm.comp ((continuous_eval f).comp (by fun_prop))`. Establish `hchange : ∫ x, Real.log ‖eval (fun p => WithLp.ofLp (x p.1) p.2) g‖ ∂(Measure.pi fun _ => gaussProb n) = ∫ y, Real.log ‖eval (fun p => WithLp.ofLp (y p.1) p.2) f‖ ∂(Measure.pi fun _ => gaussProb N)`. Repeatedly rewrite using `[hev]`. Rewrite using `[← hproj.map_eq, integral_map hproj.measurable.aemeasurable hmeas.aestronglyMeasurable]`. Rewrite `hIn` using `[hchange, hIN]`.

Establish `hr` using `radRatio_sub hN hn`. Take the linear combination `hIn.symm + (B : ℝ) * δ * hr`.
-/
theorem blockSphereMean_incl (B N n δ : ℕ) (f : MvPolynomial (Fin B × Fin N) ℂ) (hN : 0 < N)
    (hNn : N ≤ n) (hf : f ≠ 0) (hm : IsMultiHomogeneous (fun _ => δ) f) :
    blockSphereMean B n (GlobalTheory.ChowHt.linSubst (Matrix.of fun (j : Fin N) (k : Fin n) =>
        if (j : ℕ) = (k : ℕ) then (1 : ℂ) else 0) f) =
      blockSphereMean B N f + (B : ℝ) * δ * ((harmonic (N - 1) : ℝ) - (harmonic (n - 1) : ℝ)) / 2 := by
  have hn : 0 < n := lt_of_lt_of_le hN hNn
  rw [linSubst_incl hNn]
  set e : Fin B × Fin N → Fin B × Fin n := fun p => (p.1, Fin.castLE hNn p.2) with he
  have heinj : Function.Injective e := by
    intro p q hpq
    simp only [he, Prod.mk.injEq] at hpq
    exact Prod.ext hpq.1 (Fin.castLE_injective hNn hpq.2)
  set g := rename e f with hgdef
  have hg : g ≠ 0 := fun h0 => hf (rename_injective e heinj (by rw [← hgdef, h0, map_zero]))
  have hgm : IsMultiHomogeneous (fun _ => δ) g := isMultiHomogeneous_rename_castLE hNn _ f hm
  have hIn := (gauss_blockMean hn δ g hg hgm).2
  have hIN := (gauss_blockMean hN δ f hf hm).2
  haveI : IsProbabilityMeasure (gaussProb N) := isProbabilityMeasure_gaussProb hN
  have hproj : MeasurePreserving (fun (x : Fin B → EuclideanSpace ℂ (Fin n)) b => firstCoords hNn (x b))
      (Measure.pi fun _ => gaussProb n) (Measure.pi fun _ => gaussProb N) :=
    measurePreserving_pi _ _ fun _ => GlobalTheory.T.gaussian_first_coords_measure_preserving N n hNn
  have hev : ∀ x : Fin B → EuclideanSpace ℂ (Fin n),
      eval (fun p => WithLp.ofLp (x p.1) p.2) g =
        eval (fun p => WithLp.ofLp (firstCoords hNn (x p.1)) p.2) f := by
    intro x
    rw [hgdef, eval_rename]
    rfl
  have hmeas : Measurable fun y : Fin B → EuclideanSpace ℂ (Fin N) =>
      Real.log ‖eval (fun p => WithLp.ofLp (y p.1) p.2) f‖ := by
    refine Real.measurable_log.comp (Continuous.measurable ?_)
    exact continuous_norm.comp ((continuous_eval f).comp (by fun_prop))
  have hchange : ∫ x, Real.log ‖eval (fun p => WithLp.ofLp (x p.1) p.2) g‖
        ∂(Measure.pi fun _ => gaussProb n) =
      ∫ y, Real.log ‖eval (fun p => WithLp.ofLp (y p.1) p.2) f‖
        ∂(Measure.pi fun _ => gaussProb N) := by
    simp_rw [hev]
    rw [← hproj.map_eq, integral_map hproj.measurable.aemeasurable hmeas.aestronglyMeasurable]
  rw [hchange, hIN] at hIn
  have hr := radRatio_sub hN hn
  linear_combination hIn.symm + (B : ℝ) * δ * hr

end GlobalTheory.SphereMeanDrop
