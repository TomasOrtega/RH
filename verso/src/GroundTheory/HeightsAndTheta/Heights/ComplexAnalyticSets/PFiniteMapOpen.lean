import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteMapOpen
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology

noncomputable section

namespace FiniteMapOpen

abbrev evalYT {d : ℕ} (F : Polynomial (MvPolynomial (Fin d) ℂ)) (y : Fin d → ℂ) (t : ℂ) : ℂ :=
  (F.map (MvPolynomial.eval y)).eval t

/- English proof (translation)
Establish `: (fun y => evalYT F y t) = fun y => ∑ k ∈ Finset.range (F.natDegree + 1), MvPolynomial.eval y (F.coeff k) * t ^ k`. Use function extensionality and compare the values at `y`. Rewrite using `[evalYT, Polynomial.eval_map, Polynomial.eval₂_eq_sum_range]`. Rewrite using `[this]`. Conclude with `continuous_finsetSum _ fun k _ => (MvPolynomial.continuous_eval _).mul continuous_const`.
-/
theorem continuous_evalYT {d : ℕ} (F : Polynomial (MvPolynomial (Fin d) ℂ)) (t : ℂ) :
    Continuous fun y => evalYT F y t := by
  have : (fun y => evalYT F y t) =
      fun y => ∑ k ∈ Finset.range (F.natDegree + 1), MvPolynomial.eval y (F.coeff k) * t ^ k := by
    funext y
    rw [evalYT, Polynomial.eval_map, Polynomial.eval₂_eq_sum_range]
  rw [this]
  exact continuous_finsetSum _ fun k _ => (MvPolynomial.continuous_eval _).mul continuous_const

/- English proof (translation)
Take `⟨ε, hε, hball⟩` from `Metric.mem_nhds_iff.1 hV`. Establish `hcont` using `(continuous_evalYT F t₀).tendsto y₀`. Rewrite `hcont` using `[h₀]`. Establish `hsmall : ∀ᶠ y in 𝓝 y₀, ‖evalYT F y t₀‖ < ε ^ F.natDegree` using `(tendsto_norm_zero.comp hcont) (Iio_mem_nhds (pow_pos hε _))`. Use `filter_upwards [hsmall] with y hy`.

Use `set G := F.map (MvPolynomial.eval y) with hG`. Establish `hGm : G.Monic` using `hF.map _`. Establish `hGdeg : G.natDegree = F.natDegree` using `hF.natDegree_map _`. Establish `hsplit : G.Splits` using `IsAlgClosed.splits G`. Use `by_contra! hfar`.

Establish `hle : ∀ r ∈ G.roots, ε ≤ ‖t₀ - r‖`. Introduce `r hr`. Establish `hr0 : G.eval r = 0` using `(Polynomial.mem_roots hGm.ne_zero).1 hr`. Use `by_contra! hlt`. Use `hfar r (hball ?_) hr0` and prove the remaining obligations.

Rewrite using `[Metric.mem_ball, dist_comm, dist_eq_norm]`. Conclude with `hlt`. Establish `hprod : ‖G.eval t₀‖ = (G.roots.map fun r => ‖t₀ - r‖).prod`. Rewrite using `[hsplit.eval_eq_prod_roots_of_monic hGm]`. Conclude with `(G.roots.prod_hom' (NormedField.toMulRingNorm ℂ) (fun r : ℂ => t₀ - r)).symm`.

Establish `hge : ε ^ F.natDegree ≤ ‖G.eval t₀‖`. Use `Multiset.prod_map_le_prod_map₀ (fun _ => ε) (fun r => ‖t₀ - r‖) (fun _ _ => hε.le) hle` as an intermediate fact. Rewrite `this` using `[Multiset.map_const', Multiset.prod_replicate]`. Rewrite using `[hprod, ← hGdeg, hsplit.natDegree_eq_card_roots]`. Conclude with `this`.

Conclude with `absurd hy (not_lt.2 hge)`.
-/
theorem eventually_exists_root {d : ℕ} {F : Polynomial (MvPolynomial (Fin d) ℂ)} (hF : F.Monic)
    {y₀ : Fin d → ℂ} {t₀ : ℂ} (h₀ : evalYT F y₀ t₀ = 0) {V : Set ℂ} (hV : V ∈ 𝓝 t₀) :
    ∀ᶠ y in 𝓝 y₀, ∃ t ∈ V, evalYT F y t = 0 := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hV
  have hcont := (continuous_evalYT F t₀).tendsto y₀
  rw [h₀] at hcont
  have hsmall : ∀ᶠ y in 𝓝 y₀, ‖evalYT F y t₀‖ < ε ^ F.natDegree :=
    (tendsto_norm_zero.comp hcont) (Iio_mem_nhds (pow_pos hε _))
  filter_upwards [hsmall] with y hy
  set G := F.map (MvPolynomial.eval y) with hG
  have hGm : G.Monic := hF.map _
  have hGdeg : G.natDegree = F.natDegree := hF.natDegree_map _
  have hsplit : G.Splits := IsAlgClosed.splits G
  by_contra! hfar
  have hle : ∀ r ∈ G.roots, ε ≤ ‖t₀ - r‖ := by
    intro r hr
    have hr0 : G.eval r = 0 := (Polynomial.mem_roots hGm.ne_zero).1 hr
    by_contra! hlt
    refine hfar r (hball ?_) hr0
    rw [Metric.mem_ball, dist_comm, dist_eq_norm]
    exact hlt
  have hprod : ‖G.eval t₀‖ = (G.roots.map fun r => ‖t₀ - r‖).prod := by
    rw [hsplit.eval_eq_prod_roots_of_monic hGm]
    exact (G.roots.prod_hom' (NormedField.toMulRingNorm ℂ) (fun r : ℂ => t₀ - r)).symm
  have hge : ε ^ F.natDegree ≤ ‖G.eval t₀‖ := by
    have := Multiset.prod_map_le_prod_map₀ (fun _ => ε) (fun r => ‖t₀ - r‖)
      (fun _ _ => hε.le) hle
    rw [Multiset.map_const', Multiset.prod_replicate] at this
    rw [hprod, ← hGdeg, hsplit.natDegree_eq_card_roots]
    exact this
  exact absurd hy (not_lt.2 hge)

/- English proof (translation)
Establish `h1` using `Polynomial.IsRoot.norm_lt_cauchyBound hG.ne_zero ht`. Establish `h2 : Polynomial.cauchyBound G ≤ ∑ k ∈ Finset.range G.natDegree, ‖G.coeff k‖₊ + 1`. Rewrite using `[Polynomial.cauchyBound, hG.leadingCoeff, nnnorm_one, div_one]`. Use `gcongr`. Conclude with `Finset.sup_le fun k hk => Finset.single_le_sum (f := fun k => ‖G.coeff k‖₊) (fun _ _ => zero_le) hk`.

Establish `h3 : ‖t‖₊ ≤ ∑ k ∈ Finset.range G.natDegree, ‖G.coeff k‖₊ + 1` using `(h1.trans_le h2).le`. Establish `h4` using `NNReal.coe_le_coe.2 h3`. Simplify using `using h4`.
-/
theorem norm_le_of_monic_root {G : Polynomial ℂ} (hG : G.Monic) {t : ℂ} (ht : G.eval t = 0) :
    ‖t‖ ≤ ∑ k ∈ Finset.range G.natDegree, ‖G.coeff k‖ + 1 := by
  have h1 := Polynomial.IsRoot.norm_lt_cauchyBound hG.ne_zero ht
  have h2 : Polynomial.cauchyBound G ≤ ∑ k ∈ Finset.range G.natDegree, ‖G.coeff k‖₊ + 1 := by
    rw [Polynomial.cauchyBound, hG.leadingCoeff, nnnorm_one, div_one]
    gcongr
    exact Finset.sup_le fun k hk =>
      Finset.single_le_sum (f := fun k => ‖G.coeff k‖₊) (fun _ _ => zero_le) hk
  have h3 : ‖t‖₊ ≤ ∑ k ∈ Finset.range G.natDegree, ‖G.coeff k‖₊ + 1 := (h1.trans_le h2).le
  have h4 := NNReal.coe_le_coe.2 h3
  simpa using h4

variable {n d : ℕ}

def evalAt (J : Ideal (MvPolynomial (Fin n) ℂ)) {z : Fin n → ℂ} (hz : z ∈ zeroLocus J) :
    (MvPolynomial (Fin n) ℂ ⧸ J) →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ J (aeval z) fun q hq => by rw [aeval_eq_eval]; exact hz q hq

/- English proof (translation)
Simplify using `[evalAt]`.
-/
theorem evalAt_mk (J : Ideal (MvPolynomial (Fin n) ℂ)) {z : Fin n → ℂ} (hz : z ∈ zeroLocus J)
    (q : MvPolynomial (Fin n) ℂ) : evalAt J hz (Ideal.Quotient.mk J q) = eval z q := by
  simp [evalAt]

/- English proof (translation)
Apply the tactic sequence `ext a <;> simp [evalAt]`.
-/
theorem evalAt_comp_toRingHom (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ)
    {z : Fin n → ℂ} (hz : z ∈ zeroLocus J) :
    (evalAt J hz : (MvPolynomial (Fin n) ℂ ⧸ J) →+* ℂ).comp
      ((Ideal.Quotient.mkₐ ℂ J).comp (aeval p)).toRingHom = MvPolynomial.eval fun i => eval z (p i) := by
  ext a <;> simp [evalAt]

/- English proof (translation)
Establish `h` using `congrArg (evalAt J hz : (MvPolynomial (Fin n) ℂ ⧸ J) →+* ℂ) hs`. Rewrite `h` using `[map_zero, Polynomial.hom_eval₂, evalAt_comp_toRingHom]`. Rewrite using `[evalYT, Polynomial.eval_map]`. Conclude with `h`.
-/
theorem evalYT_eq_zero (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ)
    {F : Polynomial (MvPolynomial (Fin d) ℂ)} {s : MvPolynomial (Fin n) ℂ ⧸ J}
    (hs : Polynomial.eval₂ ((Ideal.Quotient.mkₐ ℂ J).comp (aeval p)).toRingHom s F = 0)
    {z : Fin n → ℂ} (hz : z ∈ zeroLocus J) :
    evalYT F (fun i => eval z (p i)) (evalAt J hz s) = 0 := by
  have h := congrArg (evalAt J hz : (MvPolynomial (Fin n) ℂ ⧸ J) →+* ℂ) hs
  rw [map_zero, Polynomial.hom_eval₂, evalAt_comp_toRingHom] at h
  rw [evalYT, Polynomial.eval_map]
  exact h

/- English proof (translation)
Use `set f := ((Ideal.Quotient.mkₐ ℂ J).comp (aeval p)).toRingHom with hf`. Set `g : Polynomial (MvPolynomial (Fin d) ℂ) →+* MvPolynomial (Fin n) ℂ ⧸ J` to `Polynomial.eval₂RingHom f (Ideal.Quotient.mk J L)`. Set `e : Polynomial (MvPolynomial (Fin d) ℂ) →+* ℂ` to `Polynomial.eval₂RingHom (MvPolynomial.eval y) t`. Establish `he : Function.Surjective e` using `fun c => ⟨Polynomial.C (MvPolynomial.C c), by simp [e]⟩`. Establish `hPmax : (RingHom.ker e).IsMaximal` using `RingHom.ker_isMaximal_of_surjective e he`.

Establish `hgC : g.comp Polynomial.C = f` using `RingHom.ext fun a => by simp [g]`. Establish `hfint : f.IsIntegral` using `RingHom.IsIntegral.of_finite hfin`. Establish `hgint : g.IsIntegral` using `RingHom.IsIntegral.tower_top Polynomial.C g (hgC ▸ hfint)`. Set `_ : Algebra (Polynomial (MvPolynomial (Fin d) ℂ)) (MvPolynomial (Fin n) ℂ ⧸ J)` to `g.toAlgebra`. Establish `: Algebra.IsIntegral (Polynomial (MvPolynomial (Fin d) ℂ)) (MvPolynomial (Fin n) ℂ ⧸ J)` using `⟨hgint⟩`.

Establish `hker : RingHom.ker (algebraMap (Polynomial (MvPolynomial (Fin d) ℂ)) (MvPolynomial (Fin n) ℂ ⧸ J)) ≤ RingHom.ker e`. Introduce `F hF`. Rewrite `hF`, the goal using `[RingHom.mem_ker]`. Take `⟨H, rfl⟩` from `hdvd F hF`. Establish `hμ : e μ = 0` using `by simpa [e, evalYT, Polynomial.eval_map] using hyt`.

Rewrite using `[map_mul, hμ, zero_mul]`. Take `⟨Q, hQ, hQP⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral (RingHom.ker e) hker`. Establish `hQ' : (Q.comap (Ideal.Quotient.mk J)).IsMaximal` using `Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective`. Take `⟨z, hz⟩` from `MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.1 hQ'`. Establish `key : ∀ q, Ideal.Quotient.mk J q ∈ Q → eval z q = 0`.

Introduce `q hq`. Establish `hq' : q ∈ Q.comap (Ideal.Quotient.mk J)` using `hq`. Rewrite `hq'` using `[hz, MvPolynomial.mem_vanishingIdeal_singleton_iff, aeval_eq_eval]`. Conclude with `hq'`. Establish `key2 : ∀ F, e F = 0 → g F ∈ Q`.

Introduce `F hF`. Establish `hF' : F ∈ Q.comap (algebraMap _ _)` using `by rw [hQP]; exact hF`. Conclude with `hF'`. Use `⟨z, fun q hq => key q ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem.2 hq]`.

Conclude with `Q.zero_mem`. Use function extensionality and compare the values at `i`. Establish `h1` using `key2 (Polynomial.C (X i - C (y i))) (by simp [e])`. Establish `h2 : g (Polynomial.C (X i - C (y i))) = Ideal.Quotient.mk J (p i - C (y i))`. Simplify using `[g, f]`.

Both sides reduce to the same expression. Rewrite `h1` using `[h2]`. Establish `h3` using `key _ h1`. Simplify `h3` using `[sub_eq_zero]`. Establish `h1` using `key2 (Polynomial.X - Polynomial.C (C t)) (by simp [e])`.

Establish `h2 : g (Polynomial.X - Polynomial.C (C t)) = Ideal.Quotient.mk J (L - C t)`. Simplify using `[g, f]`. Both sides reduce to the same expression. Rewrite `h1` using `[h2]`. Establish `h3` using `key _ h1`.

Simplify `h3` using `[sub_eq_zero]`.
-/
theorem exists_point_of_evalYT_eq_zero (J : Ideal (MvPolynomial (Fin n) ℂ))
    (p : Fin d → MvPolynomial (Fin n) ℂ) (hfin : ((Ideal.Quotient.mkₐ ℂ J).comp (aeval p)).Finite)
    (L : MvPolynomial (Fin n) ℂ) (μ : Polynomial (MvPolynomial (Fin d) ℂ))
    (hdvd : ∀ F, Polynomial.eval₂ ((Ideal.Quotient.mkₐ ℂ J).comp (aeval p)).toRingHom
      (Ideal.Quotient.mk J L) F = 0 → μ ∣ F)
    {y : Fin d → ℂ} {t : ℂ} (hyt : evalYT μ y t = 0) :
    ∃ z ∈ zeroLocus J, (fun i => eval z (p i)) = y ∧ eval z L = t := by
  classical
  set f := ((Ideal.Quotient.mkₐ ℂ J).comp (aeval p)).toRingHom with hf
  let g : Polynomial (MvPolynomial (Fin d) ℂ) →+* MvPolynomial (Fin n) ℂ ⧸ J :=
    Polynomial.eval₂RingHom f (Ideal.Quotient.mk J L)
  let e : Polynomial (MvPolynomial (Fin d) ℂ) →+* ℂ := Polynomial.eval₂RingHom (MvPolynomial.eval y) t
  have he : Function.Surjective e := fun c => ⟨Polynomial.C (MvPolynomial.C c), by simp [e]⟩
  have hPmax : (RingHom.ker e).IsMaximal := RingHom.ker_isMaximal_of_surjective e he
  have hgC : g.comp Polynomial.C = f := RingHom.ext fun a => by simp [g]
  have hfint : f.IsIntegral := RingHom.IsIntegral.of_finite hfin
  have hgint : g.IsIntegral := RingHom.IsIntegral.tower_top Polynomial.C g (hgC ▸ hfint)
  let _ : Algebra (Polynomial (MvPolynomial (Fin d) ℂ)) (MvPolynomial (Fin n) ℂ ⧸ J) := g.toAlgebra
  have : Algebra.IsIntegral (Polynomial (MvPolynomial (Fin d) ℂ)) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    ⟨hgint⟩
  have hker : RingHom.ker (algebraMap (Polynomial (MvPolynomial (Fin d) ℂ))
      (MvPolynomial (Fin n) ℂ ⧸ J)) ≤ RingHom.ker e := by
    intro F hF
    rw [RingHom.mem_ker] at hF ⊢
    obtain ⟨H, rfl⟩ := hdvd F hF
    have hμ : e μ = 0 := by simpa [e, evalYT, Polynomial.eval_map] using hyt
    rw [map_mul, hμ, zero_mul]
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (RingHom.ker e) hker
  have hQ' : (Q.comap (Ideal.Quotient.mk J)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨z, hz⟩ := MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.1 hQ'
  have key : ∀ q, Ideal.Quotient.mk J q ∈ Q → eval z q = 0 := by
    intro q hq
    have hq' : q ∈ Q.comap (Ideal.Quotient.mk J) := hq
    rw [hz, MvPolynomial.mem_vanishingIdeal_singleton_iff, aeval_eq_eval] at hq'
    exact hq'
  have key2 : ∀ F, e F = 0 → g F ∈ Q := by
    intro F hF
    have hF' : F ∈ Q.comap (algebraMap _ _) := by rw [hQP]; exact hF
    exact hF'
  refine ⟨z, fun q hq => key q ?_, ?_, ?_⟩
  · rw [Ideal.Quotient.eq_zero_iff_mem.2 hq]
    exact Q.zero_mem
  · funext i
    have h1 := key2 (Polynomial.C (X i - C (y i))) (by simp [e])
    have h2 : g (Polynomial.C (X i - C (y i))) = Ideal.Quotient.mk J (p i - C (y i)) := by
      simp [g, f]
      rfl
    rw [h2] at h1
    have h3 := key _ h1
    simpa [sub_eq_zero] using h3
  · have h1 := key2 (Polynomial.X - Polynomial.C (C t)) (by simp [e])
    have h2 : g (Polynomial.X - Polynomial.C (C t)) = Ideal.Quotient.mk J (L - C t) := by
      simp [g, f]
      rfl
    rw [h2] at h1
    have h3 := key _ h1
    simpa [sub_eq_zero] using h3

end FiniteMapOpen

set_option synthInstance.maxHeartbeats 400000 in
open FiniteMapOpen in

/- English proof (translation)
Introduce `n d J p hJ hinj hfin x hx U hU`. Use `set f := (Ideal.Quotient.mkₐ ℂ J).comp (aeval p) with hf`. Use `set φ : (Fin n → ℂ) → (Fin d → ℂ) := fun z i => eval z (p i) with hφ`. Use `set y₀ := φ x with hy₀`. Use `hJ` as an intermediate fact.

Set `_ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)` to `f.toRingHom.toAlgebra`. Establish `hint : ∀ s : MvPolynomial (Fin n) ℂ ⧸ J, IsIntegral (MvPolynomial (Fin d) ℂ) s` using `fun s => RingHom.IsIntegral.of_finite hfin s`. Use `choose g hgm hg0 using fun j : Fin n => hint (Ideal.Quotient.mk J (X j))`. Establish `hcoord : ∀ z (hz : z ∈ zeroLocus J) j, evalYT (g j) (φ z) (z j) = 0`. Introduce `z hz j`.

Use `evalYT_eq_zero J p (hg0 j) hz` as an intermediate fact. Simplify `this` using `[evalAt_mk]`. Establish `hfib : {w | w ∈ zeroLocus J ∧ φ w = y₀}.Finite`. Use `(Set.Finite.pi (t := fun j => {t : ℂ | evalYT (g j) y₀ t = 0}) fun j => ?_).subset ?_` and prove the remaining obligations. Conclude with `Polynomial.finite_setOfPred_isRoot ((hgm j).map _).ne_zero`.

Introduce and unpack `w ⟨hw, hwy⟩ j -`. Rewrite using `[← hwy]`. Conclude with `hcoord w hw j`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c : ℂ, ∀ w, w ∈ zeroLocus J ∧ φ w = y₀ → w ≠ x → ∑ j : Fin n, c ^ (j : ℕ) * w j ≠ ∑ j : Fin n, c ^ (j : ℕ) * x j := by`. Set `P : (Fin n → ℂ) → Polynomial ℂ` to `fun w => ∑ j : Fin n, Polynomial.monomial (j : ℕ) (w j - x j)`.

Establish `hP : ∀ w c, (P w).eval c = ∑ j : Fin n, c ^ (j : ℕ) * w j - ∑ j : Fin n, c ^ (j : ℕ) * x j`. Introduce `w c`. Simplify using `[P, Polynomial.eval_finsetSum, Finset.sum_sub_distrib, mul_comm]`. Establish `hP0 : ∀ w, w ≠ x → P w ≠ 0`. Introduce `w hw h0`.

Take `⟨j, hj⟩` from `Function.ne_iff.1 hw`. Establish `h1` using `congrArg (fun q => Polynomial.coeff q j) h0`. Simplify using `only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at h1`. Rewrite `h1` using `[Finset.sum_eq_single j (fun k _ hk => if_neg (fun h => hk (Fin.ext h))) (by simp)]`. Simplify using `only [if_true] at h1`.

Conclude with `hj (sub_eq_zero.1 h1)`. Establish `hbad : (⋃ w ∈ {w | (w ∈ zeroLocus J ∧ φ w = y₀) ∧ w ≠ x}, {c : ℂ | (P w).eval c = 0}).Finite` using `(hfib.subset fun w hw => hw.1).biUnion fun w hw => Polynomial.finite_setOfPred_isRoot (hP0 w hw.2)`. Take `⟨c, hc⟩` from `hbad.infinite_compl.nonempty`. Use `⟨c, fun w hw hwx h => hc ?_⟩` and prove the remaining obligations. Conclude with `Set.mem_biUnion (x := w) ⟨hw, hwx⟩ (by simp [hP, h])`.

Use `set L : MvPolynomial (Fin n) ℂ := ∑ j : Fin n, C (c ^ (j : ℕ)) * X j with hL`. Establish `hLz : ∀ z, eval z L = ∑ j : Fin n, c ^ (j : ℕ) * z j`. Introduce `z`. Simplify using `[hL]`. Use `set ℓ := Ideal.Quotient.mk J L with hℓ`.

Use `set μ := minpoly (MvPolynomial (Fin d) ℂ) ℓ with hμ`. Establish `hμm : μ.Monic` using `minpoly.monic (hint ℓ)`. Establish `: Module.IsTorsionFree (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)` using `Module.isTorsionFree_iff_algebraMap_injective.2 hinj`. Establish `hdvd : ∀ F, Polynomial.eval₂ f.toRingHom ℓ F = 0 → μ ∣ F` using `fun F hF => minpoly.isIntegrallyClosed_dvd (hint ℓ) (by rw [Polynomial.aeval_def]; exact hF)`. Establish `hμx : evalYT μ y₀ (eval x L) = 0`.

Establish `h0` using `minpoly.aeval (MvPolynomial (Fin d) ℂ) ℓ`. Rewrite `h0` using `[Polynomial.aeval_def]`. Use `evalYT_eq_zero J p (F := μ) (s := ℓ) h0 hx` as an intermediate fact. Rewrite `this` using `[hℓ, evalAt_mk]`. Conclude with `this`.

Take `⟨r, hr, hrU⟩` from `Metric.mem_nhds_iff.1 hU`. Establish `hφc : Continuous φ` using `continuous_pi fun i => MvPolynomial.continuous_eval _`. Establish `hZc : IsClosed (zeroLocus J)`. Establish `hZ : zeroLocus J = ⋂ q ∈ J, {z : Fin n → ℂ | eval z q = 0}`. Use extensionality with `z`.

Simplify using `[zeroLocus]`. Rewrite using `[hZ]`. Conclude with `isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const`. Use `set K := zeroLocus J ∩ (φ ⁻¹' Metric.closedBall y₀ 1 ∩ (Metric.ball x r)ᶜ) with hK`. Establish `hKc : IsClosed K` using `hZc.inter ((Metric.isClosed_closedBall.preimage hφc).inter Metric.isOpen_ball.isClosed_compl)`.

Set `B : (Fin d → ℂ) → ℝ` to `fun y => ∑ j, ∑ k ∈ Finset.range (g j).natDegree, ‖MvPolynomial.eval y ((g j).coeff k)‖`. Establish `hBc : Continuous B` using `continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ => (MvPolynomial.continuous_eval _).norm`. Take `⟨C0, hC0⟩` from `(isCompact_closedBall y₀ 1).exists_bound_of_continuousOn hBc.continuousOn`. Establish `hKb : Bornology.IsBounded K`. Rewrite using `[isBounded_iff_forall_norm_le]`.

Use `⟨C0 + 1, fun z hz => ?_⟩` and prove the remaining obligations. Establish `hB` using `hC0 _ hz.2.1`. Establish `hB0 : 0 ≤ B (φ z)` using `Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _`. Rewrite `hB` using `[Real.norm_eq_abs, abs_of_nonneg hB0]`. Use `(pi_norm_le_iff_of_nonneg (by linarith)).2 fun j => ?_` and prove the remaining obligations.

Establish `h1` using `norm_le_of_monic_root ((hgm j).map (MvPolynomial.eval (φ z))) (hcoord z hz.1 j)`. Rewrite `h1` using `[(hgm j).natDegree_map]`. Simplify using `only [Polynomial.coeff_map] at h1`. Establish `h2 : ∑ k ∈ Finset.range (g j).natDegree, ‖eval (φ z) ((g j).coeff k)‖ ≤ B (φ z)` using `Finset.single_le_sum (f := fun j => ∑ k ∈ Finset.range (g j).natDegree, ‖eval (φ z) ((g j).coeff k)‖) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ j)`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hKcpt : IsCompact K` using `Metric.isCompact_of_isClosed_isBounded hKc hKb`. Use `set Ψ : (Fin n → ℂ) → (Fin d → ℂ) × ℂ := fun z => (φ z, eval z L) with hΨ`. Establish `hΨc : Continuous Ψ` using `hφc.prodMk (MvPolynomial.continuous_eval L)`. Establish `hCcl : IsClosed (Ψ '' K)` using `(hKcpt.image hΨc).isClosed`. Establish `hnot : (y₀, eval x L) ∉ Ψ '' K`.

Introduce and unpack `⟨z, hzK, hz⟩`. Simplify using `only [Ψ, Prod.mk.injEq] at hz`. Establish `hzx : z ≠ x` using `fun h => hzK.2.2 (h ▸ Metric.mem_ball_self hr)`. Conclude with `hc z ⟨hzK.1, hz.1⟩ hzx (by rw [← hLz, ← hLz, hz.2])`. Take `⟨u, hu, v, hv, huv⟩` from `mem_nhds_prod_iff.1 (hCcl.isOpen_compl.mem_nhds hnot)`.

Use `filter_upwards [eventually_exists_root hμm hμx hv, hu, Metric.closedBall_mem_nhds y₀ one_pos] with y hyt hyu hyB`. Take `⟨t, htv, ht⟩` from `hyt`. Take `⟨z, hz, hzy, hzt⟩` from `exists_point_of_evalYT_eq_zero J p hfin L μ hdvd ht`. Distinguish the cases in `hzr : z ∈ Metric.ball x r`. Conclude with `⟨z, ⟨hz, hrU hzr⟩, hzy⟩`.

It suffices to derive a contradiction. Use `huv (Set.mk_mem_prod hyu htv) ⟨z, ⟨hz, ?_, hzr⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `φ z ∈ Metric.closedBall y₀ 1`. Rewrite `hyB` using `[← hzy]`. Conclude with `hyB`.

Simplify using `only [Ψ, Prod.mk.injEq]`. Conclude with `⟨hzy, hzt⟩`.
-/
theorem FiniteMapOpen.proof : FiniteMapOpen.Statement := by
  classical
  intro n d J p hJ hinj hfin x hx U hU
  set f := (Ideal.Quotient.mkₐ ℂ J).comp (aeval p) with hf
  set φ : (Fin n → ℂ) → (Fin d → ℂ) := fun z i => eval z (p i) with hφ
  set y₀ := φ x with hy₀
  have := hJ
  let _ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := f.toRingHom.toAlgebra
  have hint : ∀ s : MvPolynomial (Fin n) ℂ ⧸ J, IsIntegral (MvPolynomial (Fin d) ℂ) s :=
    fun s => RingHom.IsIntegral.of_finite hfin s

  choose g hgm hg0 using fun j : Fin n => hint (Ideal.Quotient.mk J (X j))
  have hcoord : ∀ z (hz : z ∈ zeroLocus J) j, evalYT (g j) (φ z) (z j) = 0 := by
    intro z hz j
    have := evalYT_eq_zero J p (hg0 j) hz
    simpa [evalAt_mk] using this

  have hfib : {w | w ∈ zeroLocus J ∧ φ w = y₀}.Finite := by
    refine (Set.Finite.pi (t := fun j => {t : ℂ | evalYT (g j) y₀ t = 0}) fun j => ?_).subset ?_
    · exact Polynomial.finite_setOfPred_isRoot ((hgm j).map _).ne_zero
    · rintro w ⟨hw, hwy⟩ j -
      rw [← hwy]
      exact hcoord w hw j

  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ w, w ∈ zeroLocus J ∧ φ w = y₀ → w ≠ x →
      ∑ j : Fin n, c ^ (j : ℕ) * w j ≠ ∑ j : Fin n, c ^ (j : ℕ) * x j := by
    let P : (Fin n → ℂ) → Polynomial ℂ := fun w => ∑ j : Fin n, Polynomial.monomial (j : ℕ) (w j - x j)
    have hP : ∀ w c, (P w).eval c = ∑ j : Fin n, c ^ (j : ℕ) * w j - ∑ j : Fin n, c ^ (j : ℕ) * x j := by
      intro w c
      simp [P, Polynomial.eval_finsetSum, Finset.sum_sub_distrib, mul_comm]
    have hP0 : ∀ w, w ≠ x → P w ≠ 0 := by
      intro w hw h0
      obtain ⟨j, hj⟩ := Function.ne_iff.1 hw
      have h1 := congrArg (fun q => Polynomial.coeff q j) h0
      simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at h1
      rw [Finset.sum_eq_single j (fun k _ hk => if_neg (fun h => hk (Fin.ext h))) (by simp)] at h1
      simp only [if_true] at h1
      exact hj (sub_eq_zero.1 h1)
    have hbad : (⋃ w ∈ {w | (w ∈ zeroLocus J ∧ φ w = y₀) ∧ w ≠ x},
        {c : ℂ | (P w).eval c = 0}).Finite :=
      (hfib.subset fun w hw => hw.1).biUnion fun w hw =>
        Polynomial.finite_setOfPred_isRoot (hP0 w hw.2)
    obtain ⟨c, hc⟩ := hbad.infinite_compl.nonempty
    refine ⟨c, fun w hw hwx h => hc ?_⟩
    exact Set.mem_biUnion (x := w) ⟨hw, hwx⟩ (by simp [hP, h])
  set L : MvPolynomial (Fin n) ℂ := ∑ j : Fin n, C (c ^ (j : ℕ)) * X j with hL
  have hLz : ∀ z, eval z L = ∑ j : Fin n, c ^ (j : ℕ) * z j := by
    intro z
    simp [hL]

  set ℓ := Ideal.Quotient.mk J L with hℓ
  set μ := minpoly (MvPolynomial (Fin d) ℂ) ℓ with hμ
  have hμm : μ.Monic := minpoly.monic (hint ℓ)
  have : Module.IsTorsionFree (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 hinj
  have hdvd : ∀ F, Polynomial.eval₂ f.toRingHom ℓ F = 0 → μ ∣ F := fun F hF =>
    minpoly.isIntegrallyClosed_dvd (hint ℓ) (by rw [Polynomial.aeval_def]; exact hF)
  have hμx : evalYT μ y₀ (eval x L) = 0 := by
    have h0 := minpoly.aeval (MvPolynomial (Fin d) ℂ) ℓ
    rw [Polynomial.aeval_def] at h0
    have := evalYT_eq_zero J p (F := μ) (s := ℓ) h0 hx
    rw [hℓ, evalAt_mk] at this
    exact this

  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
  have hφc : Continuous φ := continuous_pi fun i => MvPolynomial.continuous_eval _
  have hZc : IsClosed (zeroLocus J) := by
    have hZ : zeroLocus J = ⋂ q ∈ J, {z : Fin n → ℂ | eval z q = 0} := by
      ext z
      simp [zeroLocus]
    rw [hZ]
    exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const
  set K := zeroLocus J ∩ (φ ⁻¹' Metric.closedBall y₀ 1 ∩ (Metric.ball x r)ᶜ) with hK
  have hKc : IsClosed K :=
    hZc.inter ((Metric.isClosed_closedBall.preimage hφc).inter Metric.isOpen_ball.isClosed_compl)
  let B : (Fin d → ℂ) → ℝ := fun y =>
    ∑ j, ∑ k ∈ Finset.range (g j).natDegree, ‖MvPolynomial.eval y ((g j).coeff k)‖
  have hBc : Continuous B := continuous_finsetSum _ fun j _ =>
    continuous_finsetSum _ fun k _ => (MvPolynomial.continuous_eval _).norm
  obtain ⟨C0, hC0⟩ := (isCompact_closedBall y₀ 1).exists_bound_of_continuousOn hBc.continuousOn
  have hKb : Bornology.IsBounded K := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨C0 + 1, fun z hz => ?_⟩
    have hB := hC0 _ hz.2.1
    have hB0 : 0 ≤ B (φ z) := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hB0] at hB
    refine (pi_norm_le_iff_of_nonneg (by linarith)).2 fun j => ?_
    have h1 := norm_le_of_monic_root ((hgm j).map (MvPolynomial.eval (φ z))) (hcoord z hz.1 j)
    rw [(hgm j).natDegree_map] at h1
    simp only [Polynomial.coeff_map] at h1
    have h2 : ∑ k ∈ Finset.range (g j).natDegree, ‖eval (φ z) ((g j).coeff k)‖ ≤ B (φ z) :=
      Finset.single_le_sum
        (f := fun j => ∑ k ∈ Finset.range (g j).natDegree, ‖eval (φ z) ((g j).coeff k)‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    linarith
  have hKcpt : IsCompact K := Metric.isCompact_of_isClosed_isBounded hKc hKb
  set Ψ : (Fin n → ℂ) → (Fin d → ℂ) × ℂ := fun z => (φ z, eval z L) with hΨ
  have hΨc : Continuous Ψ := hφc.prodMk (MvPolynomial.continuous_eval L)
  have hCcl : IsClosed (Ψ '' K) := (hKcpt.image hΨc).isClosed
  have hnot : (y₀, eval x L) ∉ Ψ '' K := by
    rintro ⟨z, hzK, hz⟩
    simp only [Ψ, Prod.mk.injEq] at hz
    have hzx : z ≠ x := fun h => hzK.2.2 (h ▸ Metric.mem_ball_self hr)
    exact hc z ⟨hzK.1, hz.1⟩ hzx (by rw [← hLz, ← hLz, hz.2])
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 (hCcl.isOpen_compl.mem_nhds hnot)
  filter_upwards [eventually_exists_root hμm hμx hv, hu, Metric.closedBall_mem_nhds y₀ one_pos]
    with y hyt hyu hyB
  obtain ⟨t, htv, ht⟩ := hyt
  obtain ⟨z, hz, hzy, hzt⟩ := exists_point_of_evalYT_eq_zero J p hfin L μ hdvd ht
  by_cases hzr : z ∈ Metric.ball x r
  · exact ⟨z, ⟨hz, hrU hzr⟩, hzy⟩
  · exfalso
    refine huv (Set.mk_mem_prod hyu htv) ⟨z, ⟨hz, ?_, hzr⟩, ?_⟩
    · change φ z ∈ Metric.closedBall y₀ 1
      rw [← hzy] at hyB
      exact hyB
    · simp only [Ψ, Prod.mk.injEq]
      exact ⟨hzy, hzt⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
