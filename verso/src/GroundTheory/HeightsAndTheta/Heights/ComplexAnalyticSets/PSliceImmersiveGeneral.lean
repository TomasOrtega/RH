import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceImmersiveGeneral
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCriticalImageNull
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StZeroSetOpenMass
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology MeasureTheory

noncomputable section

/- English proof (translation)
Use `hJ` as an intermediate fact. Establish `hIW : J ≤ W` using `le_sup_left.trans hW.1.2`. Establish `huW : linForm u ∈ W` using `(le_sup_right.trans hW.1.2) (Ideal.mem_span_singleton_self _)`. Establish `hWprime : W.IsPrime` using `hW.1.1`. Use `set B := MvPolynomial (Fin n) ℂ ⧸ J`.

Establish `_ : Algebra.FiniteType ℂ B` using `Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ J) (Ideal.Quotient.mkₐ_surjective ℂ J)`. Use `set W' : Ideal B := W.map (Ideal.Quotient.mk J)`. Establish `hW'prime : W'.IsPrime` using `Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])`. Establish `hW'ne : W' ≠ ⊥`. Introduce `h`.

Apply `hu` to reduce the goal to its premises. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Establish `: Ideal.Quotient.mk J (linForm u) ∈ W'` using `Ideal.mem_map_of_mem _ huW`. Rewrite `this` using `[h, Ideal.mem_bot]`. Conclude with `this`.

Establish `hht : W'.height ≤ 1` using `Ideal.map_height_le_one_of_mem_minimalPrimes hW`. Establish `hquot : ringKrullDim (B ⧸ W') = ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W)` using `ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hIW)`. Establish `hform` using `GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient ℂ W'`. Establish `hdrop` using `GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le W' hW'ne`. Rewrite `hform`, `hdrop` using `[hquot]`.

Express the relevant statement in the definitionally equal form `ringKrullDim B = _ at hdim`. Rewrite `hform`, `hdrop` using `[hdim]`. Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : ∃ y : ℕ∞, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = y := by`. Consider the cases of `h : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) with`. Consider the case `bot`.

Use `ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) ℂ ⧸ W)` as an intermediate fact. Rewrite `this` using `[h]`. Conclude with `absurd this (by simp)`. Consider the case `coe y => exact ⟨y, rfl⟩`. Rewrite `hform`, `hdrop`, the goal using `[hy]`.

Establish `h1 : y + 1 ≤ ((d + 1 : ℕ) : ℕ∞)` using `by exact_mod_cast hdrop`. Establish `h2 : W'.height + y = ((d + 1 : ℕ) : ℕ∞)` using `by exact_mod_cast hform`. Establish `hyle : y ≤ d`. Establish `: y + 1 ≤ (d : ℕ∞) + 1` using `by exact_mod_cast h1`. Conclude with `(ENat.add_le_add_iff_right ENat.one_ne_top).mp this`.

Take `⟨k, rfl⟩ : ∃ k : ℕ, (k : ℕ∞) = y` from `ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top d) hyle)`. Establish `h3 : ((d + 1 : ℕ) : ℕ∞) ≤ 1 + k` using `by rw [← h2]; gcongr`. Establish `h4 : d + 1 ≤ 1 + k` using `by exact_mod_cast h3`. Establish `h5 : k ≤ d` using `by exact_mod_cast hyle`. Establish `: k = d` using `by omega`.

Substitute `this` using the available equality. Both sides reduce to the same expression.
-/
theorem dim_component_linForm {n d : ℕ} {J W : Ideal (MvPolynomial (Fin n) ℂ)} {u : Fin n → ℂ}
    (hJ : J.IsPrime) (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ))
    (hu : linForm u ∉ J) (hW : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (d : ℕ) := by
  have := hJ
  have hIW : J ≤ W := le_sup_left.trans hW.1.2
  have huW : linForm u ∈ W := (le_sup_right.trans hW.1.2) (Ideal.mem_span_singleton_self _)
  have hWprime : W.IsPrime := hW.1.1
  set B := MvPolynomial (Fin n) ℂ ⧸ J
  have _ : Algebra.FiniteType ℂ B :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ J) (Ideal.Quotient.mkₐ_surjective ℂ J)
  set W' : Ideal B := W.map (Ideal.Quotient.mk J)
  have hW'prime : W'.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hW'ne : W' ≠ ⊥ := by
    intro h
    apply hu
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have : Ideal.Quotient.mk J (linForm u) ∈ W' := Ideal.mem_map_of_mem _ huW
    rw [h, Ideal.mem_bot] at this
    exact this
  have hht : W'.height ≤ 1 := Ideal.map_height_le_one_of_mem_minimalPrimes hW
  have hquot : ringKrullDim (B ⧸ W') = ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) :=
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hIW)
  have hform := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient ℂ W'
  have hdrop := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le W' hW'ne
  rw [hquot] at hform hdrop
  change ringKrullDim B = _ at hdim
  rw [hdim] at hform hdrop
  obtain ⟨y, hy⟩ : ∃ y : ℕ∞, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = y := by
    cases h : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) with
    | bot =>
      have := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) ℂ ⧸ W)
      rw [h] at this
      exact absurd this (by simp)
    | coe y => exact ⟨y, rfl⟩
  rw [hy] at hform hdrop ⊢
  have h1 : y + 1 ≤ ((d + 1 : ℕ) : ℕ∞) := by exact_mod_cast hdrop
  have h2 : W'.height + y = ((d + 1 : ℕ) : ℕ∞) := by exact_mod_cast hform
  have hyle : y ≤ d := by
    have : y + 1 ≤ (d : ℕ∞) + 1 := by exact_mod_cast h1
    exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp this
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, (k : ℕ∞) = y :=
    ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top d) hyle)
  have h3 : ((d + 1 : ℕ) : ℕ∞) ≤ 1 + k := by rw [← h2]; gcongr
  have h4 : d + 1 ≤ 1 + k := by exact_mod_cast h3
  have h5 : k ≤ d := by exact_mod_cast hyle
  have : k = d := by omega
  subst this
  rfl

def hyperplaneEmb (d : ℕ) : (Fin d → ℂ) →L[ℂ] (Fin (d + 1) → ℂ) :=
  ContinuousLinearMap.pi
    (Fin.cons 0 fun j => ContinuousLinearMap.proj j : Fin (d + 1) → (Fin d → ℂ) →L[ℂ] ℂ)

/- English proof (translation)
Use extensionality with `i`. Apply the tactic sequence `refine Fin.cases ?_ (fun j => ?_) i <;> simp [hyperplaneEmb]`.
-/
theorem hyperplaneEmb_apply (d : ℕ) (t : Fin d → ℂ) : hyperplaneEmb d t = Fin.cons 0 t := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [hyperplaneEmb]

/- English proof (translation)
Rewrite using `[hyperplaneEmb_apply, ← hs]`. Conclude with `Fin.cons_self_tail s`.
-/
theorem hyperplaneEmb_tail {d : ℕ} {s : Fin (d + 1) → ℂ} (hs : s 0 = 0) :
    hyperplaneEmb d (Fin.tail s) = s := by
  rw [hyperplaneEmb_apply, ← hs]
  exact Fin.cons_self_tail s

def sliceMap {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin n → ℂ}
    (γ : GroundTheory.Heights₂.Heights.VarBranch J (d + 1) p) : (Fin d → ℂ) → Fin n → ℂ :=
  fun t => γ.toFun (hyperplaneEmb d t)

/- English proof (translation)
Introduce `n d J W u p m γ hJ hdim hu hW hp hN`. Take `⟨N, hN, hsl⟩` from `hN`. Establish `hWd` using `dim_component_linForm hJ hdim hu hW`. Establish `hball : ∀ b, ∀ s ∈ Metric.ball (0 : Fin (d + 1) → ℂ) (γ b).radius, Fin.tail s ∈ Metric.ball (0 : Fin d → ℂ) (γ b).radius`. Introduce `b s hs`.

Rewrite `hs`, the goal using `[ball_pi _ (γ b).radius_pos]`. Conclude with `fun j _ => hs j.succ (Set.mem_univ _)`. Establish `hmaps : ∀ b, Set.MapsTo (hyperplaneEmb d) (Metric.ball 0 (γ b).radius) (Metric.ball 0 (γ b).radius)`. Introduce `b t ht`. Rewrite `ht`, the goal using `[ball_pi _ (γ b).radius_pos]`.

Introduce `i _`. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify using `[hyperplaneEmb_apply, (γ b).radius_pos]`. Simplify `ht j (Set.mem_univ _)` using `[hyperplaneEmb_apply]`. Establish `hnull : ∀ b, μH[((2 * d : ℕ) : ℝ)] (sliceMap (γ b) '' {t | t ∈ Metric.ball 0 (γ b).radius ∧ ¬ Function.Injective (fderiv ℂ (sliceMap (γ b)) t)}) = 0` using `fun b => hcrit d n _ _ Metric.isOpen_ball ((γ b).differentiableOn.comp (hyperplaneEmb d).differentiableOn (hmaps b))`.

Use `⟨interior N, interior_mem_nhds.2 hN, ?_⟩` and prove the remaining obligations. Introduce and unpack `x ⟨hxW, hxN⟩`. Rewrite using `[mem_closure_iff]`. Introduce `o ho hxo`. Assume the negation of the conclusion as `hne`.

Rewrite `hne` using `[Set.not_nonempty_iff_eq_empty]`. Establish `hsub : GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∩ (o ∩ interior N) ⊆ ⋃ b, sliceMap (γ b) '' {t | t ∈ Metric.ball 0 (γ b).radius ∧ ¬ Function.Injective (fderiv ℂ (sliceMap (γ b)) t)}`. Introduce and unpack `y ⟨hyW, hyo, hyN⟩`. Assume the negation of the conclusion as `hy`. Simplify using `only [Set.mem_iUnion, not_exists] at hy`.

Establish `hyG : y ∈ o ∩ {x | x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∧ ∀ b, ∃ s ∈ Metric.ball 0 (γ b).radius, s 0 = 0 ∧ (γ b).toFun s = x ∧ ∀ v : Fin (d + 1) → ℂ, v 0 = 0 → fderiv ℂ (γ b).toFun s v = 0 → v = 0}`. Use `⟨hyo, hyW, fun b => ?_⟩` and prove the remaining obligations. Take `⟨s, ⟨hs, hs0⟩, hsy⟩` from `hsl b ⟨hyW, interior_subset hyN⟩`. Establish `hs0' : s 0 = 0` using `hs0`. Use `⟨s, hs, hs0', hsy, fun v hv0 hv => ?_⟩` and prove the remaining obligations.

Establish `hst` using `hyperplaneEmb_tail hs0'`. Establish `hinj : Function.Injective (fderiv ℂ (sliceMap (γ b)) (Fin.tail s))`. Assume the negation of the conclusion as `hni`. Conclude with `hy b ⟨Fin.tail s, ⟨hball b s hs, hni⟩, by simp only [sliceMap, hst, hsy]⟩`. Establish `hγd : DifferentiableAt ℂ (γ b).toFun (hyperplaneEmb d (Fin.tail s))`.

Rewrite using `[hst]`. Conclude with `(γ b).differentiableOn.differentiableAt (Metric.isOpen_ball.mem_nhds hs)`. Establish `hchain : fderiv ℂ (sliceMap (γ b)) (Fin.tail s) = (fderiv ℂ (γ b).toFun (hyperplaneEmb d (Fin.tail s))).comp (hyperplaneEmb d)`. Establish `h` using `fderiv_comp (Fin.tail s) hγd (hyperplaneEmb d).differentiableAt`. Rewrite `h` using `[ContinuousLinearMap.fderiv]`.

Conclude with `h`. Establish `hvt` using `hyperplaneEmb_tail hv0`. Establish `: Fin.tail v = 0` using `hinj (by`. Rewrite using `[hchain, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hvt, hst, hv, map_zero, map_zero])`. Rewrite using `[← hvt, this, map_zero]`.

Rewrite `hyG` using `[hne]`. Conclude with `hyG`. Establish `hpos` using `hmass n d W hW.1.1 hWd x (o ∩ interior N) (ho.inter isOpen_interior) ⟨hxo, hxN⟩ hxW`. Conclude with `hpos.ne' (measure_mono_null hsub (measure_iUnion_null hnull))`.
-/
theorem SliceImmersiveGeneral.proof (hcrit : CriticalImageNull.Statement)
    (hmass : ZeroSetOpenMass.Statement) : SliceImmersiveGeneral.Statement := by
  intro n d J W u p m γ hJ hdim hu hW hp hN
  obtain ⟨N, hN, hsl⟩ := hN
  have hWd := dim_component_linForm hJ hdim hu hW

  have hball : ∀ b, ∀ s ∈ Metric.ball (0 : Fin (d + 1) → ℂ) (γ b).radius,
      Fin.tail s ∈ Metric.ball (0 : Fin d → ℂ) (γ b).radius := by
    intro b s hs
    rw [ball_pi _ (γ b).radius_pos] at hs ⊢
    exact fun j _ => hs j.succ (Set.mem_univ _)
  have hmaps : ∀ b, Set.MapsTo (hyperplaneEmb d) (Metric.ball 0 (γ b).radius)
      (Metric.ball 0 (γ b).radius) := by
    intro b t ht
    rw [ball_pi _ (γ b).radius_pos] at ht ⊢
    intro i _
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hyperplaneEmb_apply, (γ b).radius_pos]
    · simpa [hyperplaneEmb_apply] using ht j (Set.mem_univ _)

  have hnull : ∀ b, μH[((2 * d : ℕ) : ℝ)] (sliceMap (γ b) '' {t | t ∈ Metric.ball 0 (γ b).radius ∧
      ¬ Function.Injective (fderiv ℂ (sliceMap (γ b)) t)}) = 0 := fun b =>
    hcrit d n _ _ Metric.isOpen_ball
      ((γ b).differentiableOn.comp (hyperplaneEmb d).differentiableOn (hmaps b))
  refine ⟨interior N, interior_mem_nhds.2 hN, ?_⟩
  rintro x ⟨hxW, hxN⟩
  rw [mem_closure_iff]
  intro o ho hxo
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne

  have hsub : GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∩ (o ∩ interior N) ⊆
      ⋃ b, sliceMap (γ b) '' {t | t ∈ Metric.ball 0 (γ b).radius ∧
        ¬ Function.Injective (fderiv ℂ (sliceMap (γ b)) t)} := by
    rintro y ⟨hyW, hyo, hyN⟩
    by_contra hy
    simp only [Set.mem_iUnion, not_exists] at hy
    have hyG : y ∈ o ∩ {x | x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∧
        ∀ b, ∃ s ∈ Metric.ball 0 (γ b).radius, s 0 = 0 ∧ (γ b).toFun s = x ∧
          ∀ v : Fin (d + 1) → ℂ, v 0 = 0 → fderiv ℂ (γ b).toFun s v = 0 → v = 0} := by
      refine ⟨hyo, hyW, fun b => ?_⟩
      obtain ⟨s, ⟨hs, hs0⟩, hsy⟩ := hsl b ⟨hyW, interior_subset hyN⟩
      have hs0' : s 0 = 0 := hs0
      refine ⟨s, hs, hs0', hsy, fun v hv0 hv => ?_⟩
      have hst := hyperplaneEmb_tail hs0'
      have hinj : Function.Injective (fderiv ℂ (sliceMap (γ b)) (Fin.tail s)) := by
        by_contra hni
        exact hy b ⟨Fin.tail s, ⟨hball b s hs, hni⟩, by simp only [sliceMap, hst, hsy]⟩
      have hγd : DifferentiableAt ℂ (γ b).toFun (hyperplaneEmb d (Fin.tail s)) := by
        rw [hst]
        exact (γ b).differentiableOn.differentiableAt (Metric.isOpen_ball.mem_nhds hs)
      have hchain : fderiv ℂ (sliceMap (γ b)) (Fin.tail s) =
          (fderiv ℂ (γ b).toFun (hyperplaneEmb d (Fin.tail s))).comp (hyperplaneEmb d) := by
        have h := fderiv_comp (Fin.tail s) hγd (hyperplaneEmb d).differentiableAt
        rw [ContinuousLinearMap.fderiv] at h
        exact h
      have hvt := hyperplaneEmb_tail hv0
      have : Fin.tail v = 0 := hinj (by
        rw [hchain, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hvt, hst, hv,
          map_zero, map_zero])
      rw [← hvt, this, map_zero]
    rw [hne] at hyG
    exact hyG
  have hpos := hmass n d W hW.1.1 hWd x (o ∩ interior N) (ho.inter isOpen_interior) ⟨hxo, hxN⟩ hxW
  exact hpos.ne' (measure_mono_null hsub (measure_iUnion_null hnull))

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
