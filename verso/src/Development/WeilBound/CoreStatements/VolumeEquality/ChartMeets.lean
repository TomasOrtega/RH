import Development.WeilBound.CoreStatements.VolumeEquality.RootBranches
import Development.WeilBound.CoreStatements.VolumeEquality.ChartMeetsAlg
import Development.WeilBound.CoreStatements.VolumeEquality.ChartMeetsPoint
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar

/- English proof (translation)
Take `⟨_, ⟨hP, _, _⟩, hhor, hdim⟩` from `h`. Use `haveI := hP`. Establish `hinj : Function.Injective (algebraMap ℤ (MRing J ⧸ P))`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`.

Establish `hmem : (MvPolynomial.C a : MRing J) ∈ P`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Establish `hc : algebraMap ℤ (MRing J ⧸ P) a = Ideal.Quotient.mk P (MvPolynomial.C a)` using `by simp`. Rewrite using `[← hc]`. Conclude with `ha`.

Establish `hc : a ∈ Ideal.comap (MvPolynomial.C : ℤ →+* MRing J) P` using `hmem`. Rewrite `hc` using `[hhor]`. Conclude with `(Submodule.mem_bot _).1 hc`. Establish `hd` using `GroundTheory.Heights₂.Heights.IntDomainDim.proof (MRing J ⧸ P) hinj`. Rewrite `hdim` using `[hd]`.

Establish `h4 : (Cardinal.toENat (Algebra.trdeg ℤ (MRing J ⧸ P)) + 1 : ℕ∞) = ((n + Fintype.card K : ℕ) : ℕ∞) + 1`. Rewrite `hdim` using `[show n + 1 + Fintype.card K = n + Fintype.card K + 1 by ring]`. Conclude with `hdim` after adjusting the coercions. Establish `h3 : Cardinal.toENat (Algebra.trdeg ℤ (MRing J ⧸ P)) = ((n + Fintype.card K : ℕ) : ℕ∞)` using `WithTop.add_right_cancel ENat.one_ne_top h4`. Conclude with `Cardinal.toENat_eq_nat.1 h3`.
-/
theorem trdeg_of_arithVar {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {P : Ideal (MRing J)} {n : ℕ}
    (h : IsArithVar P (n + 1)) : Algebra.trdeg ℤ (MRing J ⧸ P) = ((n + Fintype.card K : ℕ) : Cardinal) := by
  obtain ⟨_, ⟨hP, _, _⟩, hhor, hdim⟩ := h
  haveI := hP
  have hinj : Function.Injective (algebraMap ℤ (MRing J ⧸ P)) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have hmem : (MvPolynomial.C a : MRing J) ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      have hc : algebraMap ℤ (MRing J ⧸ P) a = Ideal.Quotient.mk P (MvPolynomial.C a) := by simp
      rw [← hc]
      exact ha
    have hc : a ∈ Ideal.comap (MvPolynomial.C : ℤ →+* MRing J) P := hmem
    rw [hhor] at hc
    exact (Submodule.mem_bot _).1 hc
  have hd := GroundTheory.Heights₂.Heights.IntDomainDim.proof (MRing J ⧸ P) hinj
  rw [hd] at hdim
  have h4 : (Cardinal.toENat (Algebra.trdeg ℤ (MRing J ⧸ P)) + 1 : ℕ∞)
      = ((n + Fintype.card K : ℕ) : ℕ∞) + 1 := by
    rw [show n + 1 + Fintype.card K = n + Fintype.card K + 1 by ring] at hdim
    exact_mod_cast hdim
  have h3 : Cardinal.toENat (Algebra.trdeg ℤ (MRing J ⧸ P)) = ((n + Fintype.card K : ℕ) : ℕ∞) :=
    WithTop.add_right_cancel ENat.one_ne_top h4
  exact Cardinal.toENat_eq_nat.1 h3

/- English proof (translation)
Introduce `X Ω _ _ ξ K _ J _ y n Bd χ U htie hspec harith hU`. Use `haveI : (mCoordIdeal y).IsPrime := harith.2.1.1`. Establish `hhom : IsMultiHomogIdeal (mCoordIdeal y)` using `harith.2.1.2.1`. Establish `hconv : ∀ (w : (k : K) × J k → ℂ) (f : MvPolynomial ((k : K) × J k) ℤ), aeval w f = MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) f)`. Introduce `w f`.

Rewrite using `[MvPolynomial.eval_map, MvPolynomial.aeval_def, algebraMap_int_eq]`. Establish `hscale : ∀ (c : K → ℂ) (w : (k : K) × J k → ℂ) (s : MvPolynomial ((k : K) × J k) ℤ) (a : K → ℕ), IsMultiHomog s a → aeval (torusSmul c w) s = (∏ k, c k ^ a k) * aeval w s`. Introduce `c w s a hs`. Rewrite using `[MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq', Finset.mul_sum]`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations.

Establish `hprod : ∏ i, (torusSmul c w i) ^ d i = (∏ k, c k ^ a k) * ∏ i, w i ^ d i`. Simplify using `only [torusSmul, mul_pow, Finset.prod_mul_distrib]`. Use `congr 1`. Rewrite using `[Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations.

Use `show ∏ j : J k, c k ^ d ⟨k, j⟩ = c k ^ a k`. Rewrite using `[Finset.prod_pow_eq_pow_sum, hs d hd k]`. Rewrite using `[hprod]`. Expand and normalize the polynomial expressions, which then agree. Establish `htor : ∀ (c : K → ℂ) (w : (k : K) × J k → ℂ), w ∈ mcPts (mCoordIdeal y) → ∀ f ∈ mCoordIdeal y, aeval (torusSmul c w) f = 0`.

Introduce `c w hw f hf`. Take `⟨S, hS, hPS⟩` from `hhom`. Establish `hf' : f ∈ Ideal.span S`. Rewrite using `[← hPS]`. Conclude with `hf`.

Use `clear hf`. Proceed by induction on `hf' using Submodule.span_induction with`. Consider the case `mem s hs`. Take `⟨a, ha⟩` from `hS s hs`. Establish `hsP : s ∈ mCoordIdeal y`.

Rewrite using `[hPS]`. Conclude with `Ideal.subset_span hs`. Rewrite using `[hscale c w s a ha, hconv, hw.2 s hsP, mul_zero]`. Consider the case `zero => simp`. Consider the case `add f₁ f₂ _ _ h₁ h₂ => rw [map_add, h₁, h₂, add_zero]`.

Consider the case `smul r f₁ _ h₁ => rw [smul_eq_mul, map_mul, h₁, mul_zero]`. Take `⟨g, hg, hgU⟩` from `SheetDecomposition.ChartForm.exists_form htie U hU`. Establish `h0b : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1` using `Metric.mem_ball_self one_pos`. Set `D` to `fderiv ℂ χ.γ 0`. Set `Γ : (Fin n → ℂ) × (K → ℂ) → (k : K) × J k → ℂ` to `fun w => torusSmul (fun k => 1 + w.2 k) (χ.γ w.1)`.

Set `L : ((Fin n → ℂ) × (K → ℂ)) →L[ℂ] ((k : K) × J k → ℂ)` to `ContinuousLinearMap.pi fun p : (k : K) × J k => (ContinuousLinearMap.proj p).comp (D.comp (ContinuousLinearMap.fst ℂ (Fin n → ℂ) (K → ℂ))) + χ.γ 0 p • (ContinuousLinearMap.proj p.1).comp (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (K → ℂ))`. Establish `hγ : HasStrictFDerivAt χ.γ D 0` using `(χ.analytic 0 h0b).hasStrictFDerivAt`. Establish `hstrict : HasStrictFDerivAt Γ L 0`. Rewrite using `[hasStrictFDerivAt_pi']`. Introduce `p`.

Establish `h1 : HasStrictFDerivAt (fun w : (Fin n → ℂ) × (K → ℂ) => (1 : ℂ) + w.2 p.1) ((ContinuousLinearMap.proj p.1).comp (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (K → ℂ))) 0`. Establish `hs : HasStrictFDerivAt (fun w : (Fin n → ℂ) × (K → ℂ) => w.2 p.1) ((ContinuousLinearMap.proj p.1).comp (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (K → ℂ))) 0` using `((ContinuousLinearMap.proj p.1).comp (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (K → ℂ))).hasStrictFDerivAt`. Conclude with `hs.const_add (1 : ℂ)`. Establish `h2 : HasStrictFDerivAt (fun w : (Fin n → ℂ) × (K → ℂ) => χ.γ w.1 p) ((ContinuousLinearMap.proj p).comp (D.comp (ContinuousLinearMap.fst ℂ (Fin n → ℂ) (K → ℂ)))) 0`. Establish `hγp : HasStrictFDerivAt (fun t : Fin n → ℂ => χ.γ t p) ((ContinuousLinearMap.proj p).comp D) (0 : Fin n → ℂ)` using `hasStrictFDerivAt_pi'.1 hγ p`.

Establish `hfst : HasStrictFDerivAt (fun w : (Fin n → ℂ) × (K → ℂ) => w.1) (ContinuousLinearMap.fst ℂ (Fin n → ℂ) (K → ℂ)) 0` using `hasStrictFDerivAt_fst`. Conclude with `hγp.comp (0 : (Fin n → ℂ) × (K → ℂ)) hfst`. Use `(h1.mul h2).congr_fderiv (ContinuousLinearMap.ext fun v => ?_)` and prove the remaining obligations. Apply the tactic sequence `simp [L] <;> ring`. Establish `hinjL : Function.Injective L`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce and unpack `⟨v, d⟩ h0`. Establish `hcomp : ∀ p : (k : K) × J k, D v p + χ.γ 0 p * d p.1 = 0`. Introduce `p`. Use `congrFun h0 p` as an intermediate fact.

Simplify `this` using `[L]`. Establish `hv : v = 0`. Use `χ.immersion 0 h0b v ⟨fun k => -d k, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `p`. Simplify using `only [torusSmul]`.

Take the linear combination `hcomp p`. Substitute `hv` using the available equality. Establish `hd : d = 0`. Use function extensionality and compare the values at `k`. Take `⟨i, hi⟩` from `(χ.mem 0 h0b).1 k`.

Use `hcomp ⟨k, i⟩` as an intermediate fact. Simplify using `only [map_zero, Pi.zero_apply, zero_add] at this`. Conclude with `(mul_eq_zero.1 this).resolve_left hi`. Rewrite using `[hd]`. Both sides reduce to the same expression.

Establish `hfin : Module.finrank ℂ ((Fin n → ℂ) × (K → ℂ)) = n + Fintype.card K` using `by simp`. Establish `htr : Algebra.trdeg ℤ (MvPolynomial ((k : K) × J k) ℤ ⧸ mCoordIdeal y) ≤ ↑(Module.finrank ℂ ((Fin n → ℂ) × (K → ℂ)))` using `(trdeg_of_arithVar harith).trans_le (le_of_eq (by rw [hfin]))`. Establish `hN : ∀ᶠ w : (Fin n → ℂ) × (K → ℂ) in 𝓝 0, w.1 ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ ∀ k, 1 + w.2 k ≠ 0`. Use `Filter.Eventually.and ?_ (Filter.eventually_all.2 fun k => ?_)` and prove the remaining obligations. Conclude with `(Metric.isOpen_ball.preimage continuous_fst).mem_nhds (by simpa using h0b)`.

Conclude with `(isOpen_ne_fun (continuous_const.add ((continuous_apply k).comp continuous_snd)) continuous_const).mem_nhds (by simp)`. Establish `hev : ∀ f ∈ mCoordIdeal y, ∀ᶠ w : (Fin n → ℂ) × (K → ℂ) in 𝓝 0, aeval (Γ w) f = 0`. Introduce `f hf`. Use `filter_upwards [hN] with w hw`. Conclude with `htor _ _ (χ.mem _ hw.1) f hf`.

Establish `hne` using `SheetDecomposition.ChartAlg.not_eventually_zero (mCoordIdeal y) htr Γ 0 L hstrict hinjL hev g hg`. Choose the witnesses or unpack the hypotheses as in `⟨w, hwN, hwg⟩ : ∃ w : (Fin n → ℂ) × (K → ℂ), (w.1 ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ ∀ k, 1 + w.2 k ≠ 0) ∧ aeval (Γ w) g ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `hne (hN.mono fun w hw => hcon w hw)`.

Establish `hmem` using `χ.mem _ hwN.1`. Take `⟨z, hsp, hco⟩` from `SheetDecomposition.ChartForm.exists_point htie (Γ w) (fun k => by`. Take `⟨i, hi⟩` from `hmem.1 k`. Conclude with `⟨i, (mul_ne_zero (hwN.2 k) hi).isUnit⟩)`. Use the proof step `(fun f hf => htor _ _ hmem f hf)`.

Establish `hcU` using `hgU z (Γ w) hsp hco hwg`. Establish `hcoord : CoordsAt ξ y z (χ.γ w.1)`. Take `⟨_, hrel⟩` from `hco`. Use `⟨fun k => ?_, fun k c' hu => ?_⟩` and prove the remaining obligations. Take `⟨i, hi⟩` from `hmem.1 k`.

Conclude with `⟨i, hi.isUnit⟩`. Establish `hu' : IsUnit (Γ w ⟨k, c'⟩)` using `(hwN.2 k).isUnit.mul hu`. Take `⟨hy, hr⟩` from `hrel k c' hu'`. Use `⟨hy, fun i => ?_⟩` and prove the remaining obligations. Take `⟨r, hval, hreq⟩` from `hr i`.

Use `⟨r, hval, ?_⟩` and prove the remaining obligations. Establish `hreq' : (1 + w.2 k) * χ.γ w.1 ⟨k, i⟩ = r * ((1 + w.2 k) * χ.γ w.1 ⟨k, c'⟩)` using `hreq`. Apply `mul_left_cancel₀ (hwN.2 k)` to reduce the goal to its premises. Take the linear combination `hreq'`. Use `⟨w.1, hwN.1, z, hcoord, ?_⟩` and prove the remaining obligations.

Introduce `x _`. Establish `hx : x = IsLocalRing.closedPoint ℂ` using `Subsingleton.elim _ _`. Rewrite using `[hx]`. Conclude with `hcU`.
-/
theorem chartMeets : ChartMeets := by
  intro X Ω _ _ ξ K _ J _ y n Bd χ U htie hspec harith hU
  haveI : (mCoordIdeal y).IsPrime := harith.2.1.1
  have hhom : IsMultiHomogIdeal (mCoordIdeal y) := harith.2.1.2.1
  have hconv : ∀ (w : (k : K) × J k → ℂ) (f : MvPolynomial ((k : K) × J k) ℤ),
      aeval w f = MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) f) := by
    intro w f
    rw [MvPolynomial.eval_map, MvPolynomial.aeval_def, algebraMap_int_eq]
  have hscale : ∀ (c : K → ℂ) (w : (k : K) × J k → ℂ) (s : MvPolynomial ((k : K) × J k) ℤ)
      (a : K → ℕ), IsMultiHomog s a → aeval (torusSmul c w) s = (∏ k, c k ^ a k) * aeval w s := by
    intro c w s a hs
    rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq',
      MvPolynomial.eval₂_eq', Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hprod : ∏ i, (torusSmul c w i) ^ d i = (∏ k, c k ^ a k) * ∏ i, w i ^ d i := by
      simp only [torusSmul, mul_pow, Finset.prod_mul_distrib]
      congr 1
      rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun k _ => ?_
      show ∏ j : J k, c k ^ d ⟨k, j⟩ = c k ^ a k
      rw [Finset.prod_pow_eq_pow_sum, hs d hd k]
    rw [hprod]
    ring
  have htor : ∀ (c : K → ℂ) (w : (k : K) × J k → ℂ), w ∈ mcPts (mCoordIdeal y) →
      ∀ f ∈ mCoordIdeal y, aeval (torusSmul c w) f = 0 := by
    intro c w hw f hf
    obtain ⟨S, hS, hPS⟩ := hhom
    have hf' : f ∈ Ideal.span S := by
      rw [← hPS]
      exact hf
    clear hf
    induction hf' using Submodule.span_induction with
    | mem s hs =>
      obtain ⟨a, ha⟩ := hS s hs
      have hsP : s ∈ mCoordIdeal y := by
        rw [hPS]
        exact Ideal.subset_span hs
      rw [hscale c w s a ha, hconv, hw.2 s hsP, mul_zero]
    | zero => simp
    | add f₁ f₂ _ _ h₁ h₂ => rw [map_add, h₁, h₂, add_zero]
    | smul r f₁ _ h₁ => rw [smul_eq_mul, map_mul, h₁, mul_zero]
  obtain ⟨g, hg, hgU⟩ := SheetDecomposition.ChartForm.exists_form htie U hU
  have h0b : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  let D := fderiv ℂ χ.γ 0
  let Γ : (Fin n → ℂ) × (K → ℂ) → (k : K) × J k → ℂ :=
    fun w => torusSmul (fun k => 1 + w.2 k) (χ.γ w.1)
  let L : ((Fin n → ℂ) × (K → ℂ)) →L[ℂ] ((k : K) × J k → ℂ) :=
    ContinuousLinearMap.pi fun p : (k : K) × J k =>
      (ContinuousLinearMap.proj p).comp (D.comp (ContinuousLinearMap.fst ℂ (Fin n → ℂ) (K → ℂ)))
      + χ.γ 0 p • (ContinuousLinearMap.proj p.1).comp (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (K → ℂ))
  have hγ : HasStrictFDerivAt χ.γ D 0 := (χ.analytic 0 h0b).hasStrictFDerivAt
  have hstrict : HasStrictFDerivAt Γ L 0 := by
    rw [hasStrictFDerivAt_pi']
    intro p
    have h1 : HasStrictFDerivAt (fun w : (Fin n → ℂ) × (K → ℂ) => (1 : ℂ) + w.2 p.1)
        ((ContinuousLinearMap.proj p.1).comp (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (K → ℂ))) 0 :=
      by
        have hs : HasStrictFDerivAt (fun w : (Fin n → ℂ) × (K → ℂ) => w.2 p.1)
            ((ContinuousLinearMap.proj p.1).comp
              (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (K → ℂ))) 0 :=
          ((ContinuousLinearMap.proj p.1).comp
            (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (K → ℂ))).hasStrictFDerivAt
        exact hs.const_add (1 : ℂ)
    have h2 : HasStrictFDerivAt (fun w : (Fin n → ℂ) × (K → ℂ) => χ.γ w.1 p)
        ((ContinuousLinearMap.proj p).comp (D.comp (ContinuousLinearMap.fst ℂ (Fin n → ℂ) (K → ℂ)))) 0 :=
      by
        have hγp : HasStrictFDerivAt (fun t : Fin n → ℂ => χ.γ t p)
            ((ContinuousLinearMap.proj p).comp D) (0 : Fin n → ℂ) := hasStrictFDerivAt_pi'.1 hγ p
        have hfst : HasStrictFDerivAt (fun w : (Fin n → ℂ) × (K → ℂ) => w.1)
            (ContinuousLinearMap.fst ℂ (Fin n → ℂ) (K → ℂ)) 0 := hasStrictFDerivAt_fst
        exact hγp.comp (0 : (Fin n → ℂ) × (K → ℂ)) hfst
    refine (h1.mul h2).congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    simp [L] <;> ring
  have hinjL : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨v, d⟩ h0
    have hcomp : ∀ p : (k : K) × J k, D v p + χ.γ 0 p * d p.1 = 0 := by
      intro p
      have := congrFun h0 p
      simpa [L] using this
    have hv : v = 0 := by
      refine χ.immersion 0 h0b v ⟨fun k => -d k, ?_⟩
      funext p
      simp only [torusSmul]
      linear_combination hcomp p
    subst hv
    have hd : d = 0 := by
      funext k
      obtain ⟨i, hi⟩ := (χ.mem 0 h0b).1 k
      have := hcomp ⟨k, i⟩
      simp only [map_zero, Pi.zero_apply, zero_add] at this
      exact (mul_eq_zero.1 this).resolve_left hi
    rw [hd]
    rfl
  have hfin : Module.finrank ℂ ((Fin n → ℂ) × (K → ℂ)) = n + Fintype.card K := by simp
  have htr : Algebra.trdeg ℤ (MvPolynomial ((k : K) × J k) ℤ ⧸ mCoordIdeal y)
      ≤ ↑(Module.finrank ℂ ((Fin n → ℂ) × (K → ℂ))) :=
    (trdeg_of_arithVar harith).trans_le (le_of_eq (by rw [hfin]))
  have hN : ∀ᶠ w : (Fin n → ℂ) × (K → ℂ) in 𝓝 0,
      w.1 ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ ∀ k, 1 + w.2 k ≠ 0 := by
    refine Filter.Eventually.and ?_ (Filter.eventually_all.2 fun k => ?_)
    · exact (Metric.isOpen_ball.preimage continuous_fst).mem_nhds (by simpa using h0b)
    · exact (isOpen_ne_fun (continuous_const.add ((continuous_apply k).comp continuous_snd))
        continuous_const).mem_nhds (by simp)
  have hev : ∀ f ∈ mCoordIdeal y, ∀ᶠ w : (Fin n → ℂ) × (K → ℂ) in 𝓝 0, aeval (Γ w) f = 0 := by
    intro f hf
    filter_upwards [hN] with w hw
    exact htor _ _ (χ.mem _ hw.1) f hf
  have hne := SheetDecomposition.ChartAlg.not_eventually_zero (mCoordIdeal y) htr Γ 0 L hstrict hinjL hev g hg
  obtain ⟨w, hwN, hwg⟩ : ∃ w : (Fin n → ℂ) × (K → ℂ),
      (w.1 ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ ∀ k, 1 + w.2 k ≠ 0) ∧ aeval (Γ w) g ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hne (hN.mono fun w hw => hcon w hw)
  have hmem := χ.mem _ hwN.1
  obtain ⟨z, hsp, hco⟩ := SheetDecomposition.ChartForm.exists_point htie (Γ w)
    (fun k => by
      obtain ⟨i, hi⟩ := hmem.1 k
      exact ⟨i, (mul_ne_zero (hwN.2 k) hi).isUnit⟩)
    (fun f hf => htor _ _ hmem f hf)
  have hcU := hgU z (Γ w) hsp hco hwg
  have hcoord : CoordsAt ξ y z (χ.γ w.1) := by
    obtain ⟨_, hrel⟩ := hco
    refine ⟨fun k => ?_, fun k c' hu => ?_⟩
    · obtain ⟨i, hi⟩ := hmem.1 k
      exact ⟨i, hi.isUnit⟩
    · have hu' : IsUnit (Γ w ⟨k, c'⟩) := (hwN.2 k).isUnit.mul hu
      obtain ⟨hy, hr⟩ := hrel k c' hu'
      refine ⟨hy, fun i => ?_⟩
      obtain ⟨r, hval, hreq⟩ := hr i
      refine ⟨r, hval, ?_⟩
      have hreq' : (1 + w.2 k) * χ.γ w.1 ⟨k, i⟩ = r * ((1 + w.2 k) * χ.γ w.1 ⟨k, c'⟩) := hreq
      apply mul_left_cancel₀ (hwN.2 k)
      linear_combination hreq'
  refine ⟨w.1, hwN.1, z, hcoord, ?_⟩
  intro x _
  have hx : x = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
  rw [hx]
  exact hcU

end SheetDecomposition
