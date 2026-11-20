import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartDivisorComponents
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartDim
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSectionComponents
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsArithVar IsSectionOn divSupp IsHorizontal IsRelevant IsMultiHomogIdeal mcPts
  segre divSupp_finite divSuppArith mcPts_smul)
open GroundTheory.Heights₂.Heights (segreChartSet segreChartIdeal segreChartComponents mem_segreChartComponents chartLift
  chartLift_segre_apply segre_chartLift chartLift_blockNonzero)

namespace ChartDivisorComponents

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {m : ℕ}

/- English proof (translation)
Take `⟨z, hz, hzi, rfl⟩` from `hx`. Establish `hne : ∀ k, (z ⟨k, i k⟩)⁻¹ ≠ 0` using `fun k => inv_ne_zero fun h0 => by`. Establish `: segre z i = 0` using `Finset.prod_eq_zero (Finset.mem_univ k) h0`. Rewrite `this` using `[hzi]`. Conclude with `one_ne_zero this`.

Establish `heq : chartLift σ i (fun a => segre z (σ a)) = fun p => (z ⟨p.1, i p.1⟩)⁻¹ * z p`. Use function extensionality and compare the values at `p`. Rewrite using `[chartLift_segre_apply σ i z hzi p.1 p.2, mul_comm]`. Rewrite using `[heq]`. Conclude with `mcPts_smul hP (fun k => (z ⟨k, i k⟩)⁻¹) hne hz`.
-/
theorem chartLift_mem_mcPts {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) (σ : Fin m ≃ ((k : K) → ι k))
    (i : (k : K) → ι k) {x : Fin m → ℂ} (hx : x ∈ segreChartSet P σ i) : chartLift σ i x ∈ mcPts P := by
  obtain ⟨z, hz, hzi, rfl⟩ := hx
  have hne : ∀ k, (z ⟨k, i k⟩)⁻¹ ≠ 0 := fun k => inv_ne_zero fun h0 => by
    have : segre z i = 0 := Finset.prod_eq_zero (Finset.mem_univ k) h0
    rw [hzi] at this
    exact one_ne_zero this
  have heq : chartLift σ i (fun a => segre z (σ a)) = fun p => (z ⟨p.1, i p.1⟩)⁻¹ * z p := by
    funext p
    rw [chartLift_segre_apply σ i z hzi p.1 p.2, mul_comm]
  rw [heq]
  exact mcPts_smul hP (fun k => (z ⟨k, i k⟩)⁻¹) hne hz

/- English proof (translation)
Rewrite using `[segreChartIdeal, mem_vanishingIdeal_iff]`. Introduce `x hx`. Express the relevant statement in the definitionally equal form `eval x (chartSection σ i f) = 0`. Rewrite using `[eval_chartSection]`. Conclude with `(chartLift_mem_mcPts hP σ i hx).2 f hf`.
-/
theorem chartSection_mem {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) (σ : Fin m ≃ ((k : K) → ι k))
    (i : (k : K) → ι k) {f : MRing ι} (hf : f ∈ P) : chartSection σ i f ∈ segreChartIdeal P σ i := by
  rw [segreChartIdeal, mem_vanishingIdeal_iff]
  intro x hx
  change eval x (chartSection σ i f) = 0
  rw [eval_chartSection]
  exact (chartLift_mem_mcPts hP σ i hx).2 f hf

/- English proof (translation)
Establish `hxi : x (σ.symm i) = 1`. Establish `hmem : (X (σ.symm i) - 1 : MvPolynomial (Fin m) ℂ) ∈ segreChartIdeal P σ i`. Rewrite using `[segreChartIdeal, mem_vanishingIdeal_iff]`. Introduce and unpack `_ ⟨z, -, hzi, rfl⟩`. Simplify using `[hzi]`.

Establish `h` using `hx _ hmem`. Simplify using `only [map_sub, eval_X, map_one] at h`. Conclude with `sub_eq_zero.1 h`. Establish `hseg : ∀ a, x a = segre (chartLift σ i x) (σ a)`. Introduce `a`.

Establish `hmem : (X a - ∏ k, X (σ.symm (Function.update i k (σ a k))) : MvPolynomial (Fin m) ℂ) ∈ segreChartIdeal P σ i`. Rewrite using `[segreChartIdeal, mem_vanishingIdeal_iff]`. Introduce and unpack `_ ⟨z, -, hzi, rfl⟩`. Establish `h` using `congrFun (segre_chartLift σ i z hzi) (σ a)`. Express the relevant statement in the definitionally equal form `eval _ (X a - ∏ k, X (σ.symm (Function.update i k (σ a k)))) = 0`.

Rewrite using `[map_sub, map_prod, sub_eq_zero]`. Simplify using `only [eval_X]`. Conclude with `h.symm.trans rfl`. Establish `h` using `hx _ hmem`. Simplify using `only [map_sub, eval_X, map_prod] at h`.

Rewrite `h` using `[sub_eq_zero]`. Rewrite using `[h]`. Both sides reduce to the same expression. Use `⟨chartLift σ i x, ⟨chartLift_blockNonzero σ i hxi, fun f hf => ?_⟩, ?_, funext hseg⟩` and prove the remaining obligations. Rewrite using `[← eval_chartSection]`.

Conclude with `hx _ (chartSection_mem hP σ i hf)`. Use `show ∏ k, x (σ.symm (Function.update i k (i k))) = 1`. Simplify using `[hxi]`.
-/
theorem mem_segreChartSet_of_forall {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) (σ : Fin m ≃ ((k : K) → ι k))
    (i : (k : K) → ι k) {x : Fin m → ℂ} (hx : ∀ f ∈ segreChartIdeal P σ i, eval x f = 0) :
    x ∈ segreChartSet P σ i := by
  have hxi : x (σ.symm i) = 1 := by
    have hmem : (X (σ.symm i) - 1 : MvPolynomial (Fin m) ℂ) ∈ segreChartIdeal P σ i := by
      rw [segreChartIdeal, mem_vanishingIdeal_iff]
      rintro _ ⟨z, -, hzi, rfl⟩
      simp [hzi]
    have h := hx _ hmem
    simp only [map_sub, eval_X, map_one] at h
    exact sub_eq_zero.1 h
  have hseg : ∀ a, x a = segre (chartLift σ i x) (σ a) := by
    intro a
    have hmem : (X a - ∏ k, X (σ.symm (Function.update i k (σ a k))) : MvPolynomial (Fin m) ℂ) ∈
        segreChartIdeal P σ i := by
      rw [segreChartIdeal, mem_vanishingIdeal_iff]
      rintro _ ⟨z, -, hzi, rfl⟩
      have h := congrFun (segre_chartLift σ i z hzi) (σ a)
      change eval _ (X a - ∏ k, X (σ.symm (Function.update i k (σ a k)))) = 0
      rw [map_sub, map_prod, sub_eq_zero]
      simp only [eval_X]
      exact h.symm.trans rfl
    have h := hx _ hmem
    simp only [map_sub, eval_X, map_prod] at h
    rw [sub_eq_zero] at h
    rw [h]
    rfl
  refine ⟨chartLift σ i x, ⟨chartLift_blockNonzero σ i hxi, fun f hf => ?_⟩, ?_, funext hseg⟩
  · rw [← eval_chartSection]
    exact hx _ (chartSection_mem hP σ i hf)
  · show ∏ k, x (σ.symm (Function.update i k (i k))) = 1
    simp [hxi]

/- English proof (translation)
Establish `hz` using `chartLift_mem_mcPts hP σ i hx`. Take `⟨z₀, -, hz₀i, hxz₀⟩` from `hx`. Use `set z := chartLift σ i x with hzdef`. Establish `hsz : segre z = segre z₀` using `by rw [hzdef, hxz₀]; exact segre_chartLift σ i z₀ hz₀i`. Set `φ : MRing ι →+* ℂ` to `(eval z).comp (map (Int.castRingHom ℂ))`.

Establish `hφ : ∀ f, φ f = eval z (map (Int.castRingHom ℂ) f)` using `fun _ => rfl`. Establish `: (RingHom.ker φ).IsPrime` using `RingHom.ker_isPrime φ`. Establish `hle : P ⊔ Ideal.span {s} ≤ RingHom.ker φ`. Use `sup_le (fun f hf => by rw [RingHom.mem_ker, hφ]; exact hz.2 f hf) ?_` and prove the remaining obligations. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, hφ, ← eval_chartSection]`.

Conclude with `hs`. Take `⟨W, hW, hWle⟩` from `Ideal.exists_minimalPrimes_le hle`. Use `⟨W, ⟨⟨hW, fun k => ?_⟩, ?_⟩, z, ⟨hz.1, fun f hf => hWle hf⟩, ?_, ?_⟩` and prove the remaining obligations. Take `⟨j, hj⟩` from `hz.1 k`. Conclude with `⟨j, fun h => hj (by simpa [hφ] using hWle h)⟩`.

Use `eq_bot_iff.2 fun c hc => ?_` and prove the remaining obligations. Establish `h` using `hWle hc`. Rewrite `h` using `[RingHom.mem_ker, hφ]`. Simplify using `using h`. Rewrite using `[hsz]`.

Conclude with `hz₀i`. Rewrite using `[hsz]`. Conclude with `hxz₀`.
-/
theorem exists_divSupp_of_eval {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) (σ : Fin m ≃ ((k : K) → ι k))
    (i : (k : K) → ι k) (s : MRing ι) {x : Fin m → ℂ} (hx : x ∈ segreChartSet P σ i)
    (hs : eval x (chartSection σ i s) = 0) :
    ∃ W, (W ∈ divSupp P s ∧ IsHorizontal W) ∧ x ∈ segreChartSet W σ i := by
  have hz := chartLift_mem_mcPts hP σ i hx
  obtain ⟨z₀, -, hz₀i, hxz₀⟩ := hx
  set z := chartLift σ i x with hzdef
  have hsz : segre z = segre z₀ := by rw [hzdef, hxz₀]; exact segre_chartLift σ i z₀ hz₀i
  let φ : MRing ι →+* ℂ := (eval z).comp (map (Int.castRingHom ℂ))
  have hφ : ∀ f, φ f = eval z (map (Int.castRingHom ℂ) f) := fun _ => rfl
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hle : P ⊔ Ideal.span {s} ≤ RingHom.ker φ := by
    refine sup_le (fun f hf => by rw [RingHom.mem_ker, hφ]; exact hz.2 f hf) ?_
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, hφ, ← eval_chartSection]
    exact hs
  obtain ⟨W, hW, hWle⟩ := Ideal.exists_minimalPrimes_le hle
  refine ⟨W, ⟨⟨hW, fun k => ?_⟩, ?_⟩, z, ⟨hz.1, fun f hf => hWle hf⟩, ?_, ?_⟩
  · obtain ⟨j, hj⟩ := hz.1 k
    exact ⟨j, fun h => hj (by simpa [hφ] using hWle h)⟩
  · refine eq_bot_iff.2 fun c hc => ?_
    have h := hWle hc
    rw [RingHom.mem_ker, hφ] at h
    simpa using h
  · rw [hsz]; exact hz₀i
  · rw [hsz]; exact hxz₀

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `h` using `SectionComponents.ringKrullDim_quotient_add_one_le_of_lt (lt_of_le_of_ne hle hne)`. Rewrite `h` using `[hQ']`. Establish `h2 : ((n : ℕ) : WithBot ℕ∞) + 1 + 1 ≤ ((n + 1 : ℕ) : WithBot ℕ∞)`. Rewrite using `[← hQ]`.

Conclude with `add_le_add h le_rfl`. Establish `h3 : ((n + 1 + 1 : ℕ) : WithBot ℕ∞) ≤ ((n + 1 : ℕ) : WithBot ℕ∞)` using `by exact_mod_cast h2`. Establish `h4 : n + 1 + 1 ≤ n + 1` using `by exact_mod_cast h3`. Use linear arithmetic over natural numbers and integers.
-/
theorem eq_of_le_of_dim {Q Q' : Ideal (MvPolynomial (Fin m) ℂ)} [Q.IsPrime] (hle : Q ≤ Q') (n : ℕ)
    (hQ : ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ Q) + 1 = ((n + 1 : ℕ) : WithBot ℕ∞))
    (hQ' : ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ Q') = (n : ℕ)) : Q = Q' := by
  by_contra hne
  have h := SectionComponents.ringKrullDim_quotient_add_one_le_of_lt (lt_of_le_of_ne hle hne)
  rw [hQ'] at h
  have h2 : ((n : ℕ) : WithBot ℕ∞) + 1 + 1 ≤ ((n + 1 : ℕ) : WithBot ℕ∞) := by
    rw [← hQ]
    exact add_le_add h le_rfl
  have h3 : ((n + 1 + 1 : ℕ) : WithBot ℕ∞) ≤ ((n + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast h2
  have h4 : n + 1 + 1 ≤ n + 1 := by exact_mod_cast h3
  omega

/- English proof (translation)
Establish `h₂'` using `h₂`. Take `⟨S, hS, rfl⟩` from `h₂`. Use `Ideal.span_le.2 fun f hf => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hfW`. Take `⟨a, ha⟩` from `hS f hf`.

Establish `hsec : IsSectionOn W₁ (HermLine.sqMetric (ι` using `ι) a) f := ⟨a, fun _ => rfl, ha, hfW⟩`. Conclude with `hNot K ι W₁ n m σ i _ f h₁ hsec W' hW₁ ((mem_segreChartComponents.1 hW₂).1.2 (chartSection_mem h₂' σ i (Ideal.subset_span hf)))`.
-/
theorem le_of_common (hNot : ChartSectionNotMem.Statement) {W₁ W₂ : Ideal (MRing ι)} {n : ℕ}
    (h₁ : IsArithVar W₁ (n + 1)) (h₂ : IsMultiHomogIdeal W₂) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    {W' : Ideal (MvPolynomial (Fin m) ℂ)} (hW₁ : W' ∈ segreChartComponents W₁ σ i)
    (hW₂ : W' ∈ segreChartComponents W₂ σ i) : W₂ ≤ W₁ := by
  have h₂' := h₂
  obtain ⟨S, hS, rfl⟩ := h₂
  refine Ideal.span_le.2 fun f hf => ?_
  by_contra hfW
  obtain ⟨a, ha⟩ := hS f hf
  have hsec : IsSectionOn W₁ (HermLine.sqMetric (ι := ι) a) f := ⟨a, fun _ => rfl, ha, hfW⟩
  exact hNot K ι W₁ n m σ i _ f h₁ hsec W' hW₁
    ((mem_segreChartComponents.1 hW₂).1.2 (chartSection_mem h₂' σ i (Ideal.subset_span hf)))

end ChartDivisorComponents

open ChartDivisorComponents in

/- English proof (translation)
Introduce `K _ _ ι _ P n m σ i A s hP hs`. Establish `hPh : IsMultiHomogIdeal P` using `hP.2.1.2.1`. Establish `hJdim : ∀ J ∈ segreChartComponents P σ i, ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = ((n + 1 : ℕ) : WithBot ℕ∞)` using `SegreChartDim.proof K ι P (n + 1) m σ i hP`. Establish `hWar : ∀ W, W ∈ divSupp P s ∧ IsHorizontal W → IsArithVar W (n + 1)` using `fun W hW => (divSuppArith K ι P (n + 1) A s W hP hs hW.1).1 hW.2`. Establish `hWdim : ∀ W, W ∈ divSupp P s ∧ IsHorizontal W → ∀ W'' ∈ segreChartComponents W σ i, ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ W'') = (n : ℕ)` using `fun W hW => SegreChartDim.proof K ι W n m σ i (hWar W hW)`.

Establish `hsW : ∀ W, W ∈ divSupp P s ∧ IsHorizontal W → ∀ W'' ∈ segreChartComponents W σ i, chartSection σ i s ∈ W''` using `fun W hW W'' hW'' => (mem_segreChartComponents.1 hW'').1.2 (chartSection_mem (hWar W hW).2.1.2.1 σ i (hW.1.1.1.2 (le_sup_right (a := P) (Ideal.mem_span_singleton_self s))))`. Establish `hnot` using `hNot K ι P (n + 1) m σ i A s hP hs`. Use `⟨fun J hJ W' => ⟨fun hW' => ?_, fun ⟨hJW', W, hW, hW'c⟩ => ?_⟩, fun W₁ W₂ h₁ h₂ W' hW₁ hW₂ => ?_⟩` and prove the remaining obligations. Establish `hJp : J.IsPrime` using `(mem_segreChartComponents.1 hJ).1.1`. Establish `hW'p : W'.IsPrime` using `hW'.1.1`.

Establish `hdim` using `SectionComponents.ringKrullDim_quotient_add_one_eq (hnot J hJ) hW'`. Rewrite `hdim` using `[hJdim J hJ]`. Establish `hJW' : J ≤ W'` using `le_sup_left.trans hW'.1.2`. Establish `hsW' : chartSection σ i s ∈ W'` using `((le_sup_right (a := J)).trans hW'.1.2) (Ideal.mem_span_singleton_self _)`. Establish `key : ∃ W, (W ∈ divSupp P s ∧ IsHorizontal W) ∧ ∃ W'' ∈ segreChartComponents W σ i, W'' ≤ W'`.

Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Set `g : Ideal (MRing ι) → Ideal (MvPolynomial (Fin m) ℂ) → MvPolynomial (Fin m) ℂ` to `fun W W'' => if h : (W ∈ divSupp P s ∧ IsHorizontal W) ∧ W'' ∈ segreChartComponents W σ i then (SetLike.not_le_iff_exists.1 (hcon W h.1 W'' h.2)).choose else 1`. Establish `hg : ∀ W W'', (W ∈ divSupp P s ∧ IsHorizontal W) → W'' ∈ segreChartComponents W σ i → g W W'' ∈ W'' ∧ g W W'' ∉ W'` using `fun W W'' hW hW'' => by`. Simplify using `only [g, dif_pos (And.intro hW hW'')]`.

Conclude with `(SetLike.not_le_iff_exists.1 (hcon W hW W'' hW'')).choose_spec`. Use `set T := (divSupp_finite P s).toFinset.filter IsHorizontal`. Establish `hT : ∀ W, W ∈ T ↔ W ∈ divSupp P s ∧ IsHorizontal W` using `fun W => by simp [T]`. Use `set G := ∏ W ∈ T, ∏ W'' ∈ segreChartComponents W σ i, g W W''`. Apply `(show G ∉ W' from fun hG => by` to reduce the goal to its premises.

Rewrite `hG` using `[Ideal.IsPrime.prod_mem_iff]`. Take `⟨W, hWT, hG⟩` from `hG`. Rewrite `hG` using `[Ideal.IsPrime.prod_mem_iff]`. Take `⟨W'', hW'', hG⟩` from `hG`. Conclude with `(hg W W'' ((hT W).1 hWT) hW'').2 hG)`.

Rewrite using `[← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := ℂ) W', mem_vanishingIdeal_iff]`. Introduce `x hx`. Rewrite `hx` using `[mem_zeroLocus_iff]`. Express the relevant statement in the definitionally equal form `∀ p ∈ W', eval x p = 0 at hx`. Express the relevant statement in the definitionally equal form `eval x G = 0`.

Establish `hxS : x ∈ segreChartSet P σ i` using `mem_segreChartSet_of_forall hPh σ i fun f hf => hx f (hJW' ((mem_segreChartComponents.1 hJ).1.2 hf))`. Take `⟨W, hW, hxW⟩` from `exists_divSupp_of_eval hPh σ i s hxS (hx _ hsW')`. Establish `: (RingHom.ker (eval x)).IsPrime` using `RingHom.ker_isPrime _`. Establish `hle : segreChartIdeal W σ i ≤ RingHom.ker (eval x)` using `fun f hf => (mem_vanishingIdeal_iff.1 hf) x hxW`. Take `⟨W'', hW''min, hW''x⟩` from `Ideal.exists_minimalPrimes_le hle`.

Establish `hW'' : W'' ∈ segreChartComponents W σ i` using `mem_segreChartComponents.2 hW''min`. Rewrite using `[map_prod]`. Use `Finset.prod_eq_zero ((hT W).2 hW) ?_` and prove the remaining obligations. Rewrite using `[map_prod]`. Use `Finset.prod_eq_zero hW'' ?_` and prove the remaining obligations.

Conclude with `hW''x (hg W W'' hW hW'').1`. Take `⟨W, hW, W'', hW'', hW''le⟩` from `key`. Establish `hW''p : W''.IsPrime` using `(mem_segreChartComponents.1 hW'').1.1`. Establish `heq : W'' = W'`. Assume the negation of the conclusion as `hne`.

Establish `h` using `SectionComponents.ringKrullDim_quotient_add_one_le_of_lt (lt_of_le_of_ne hW''le hne)`. Rewrite `h` using `[hWdim W hW W'' hW'', hdim]`. Establish `h6 : n + 1 ≤ n` using `by exact_mod_cast h`. Use linear arithmetic over natural numbers and integers. Conclude with `⟨hJW', W, hW, heq ▸ hW''⟩`.

Establish `hJp : J.IsPrime` using `(mem_segreChartComponents.1 hJ).1.1`. Establish `: W'.IsPrime` using `(mem_segreChartComponents.1 hW'c).1.1`. Establish `hle : J ⊔ Ideal.span {chartSection σ i s} ≤ W'` using `sup_le hJW' ((Ideal.span_singleton_le_iff_mem _).2 (hsW W hW W' hW'c))`. Take `⟨Q, hQ, hQW'⟩` from `Ideal.exists_minimalPrimes_le hle`. Establish `hQp : Q.IsPrime` using `hQ.1.1`.

Establish `hdim` using `SectionComponents.ringKrullDim_quotient_add_one_eq (hnot J hJ) hQ`. Rewrite `hdim` using `[hJdim J hJ]`. Rewrite using `[← eq_of_le_of_dim hQW' n hdim (hWdim W hW W' hW'c)]` and apply the resulting hypothesis. Conclude with `le_antisymm (le_of_common hNot (hWar W₂ h₂) (hWar W₁ h₁).2.1.2.1 σ i hW₂ hW₁) (le_of_common hNot (hWar W₁ h₁) (hWar W₂ h₂).2.1.2.1 σ i hW₁ hW₂)`.
-/
theorem ChartDivisorComponents.proof (hNot : ChartSectionNotMem.Statement) : ChartDivisorComponents.Statement := by
  classical
  intro K _ _ ι _ P n m σ i A s hP hs
  have hPh : IsMultiHomogIdeal P := hP.2.1.2.1
  have hJdim : ∀ J ∈ segreChartComponents P σ i,
      ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = ((n + 1 : ℕ) : WithBot ℕ∞) :=
    SegreChartDim.proof K ι P (n + 1) m σ i hP
  have hWar : ∀ W, W ∈ divSupp P s ∧ IsHorizontal W → IsArithVar W (n + 1) :=
    fun W hW => (divSuppArith K ι P (n + 1) A s W hP hs hW.1).1 hW.2
  have hWdim : ∀ W, W ∈ divSupp P s ∧ IsHorizontal W → ∀ W'' ∈ segreChartComponents W σ i,
      ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ W'') = (n : ℕ) :=
    fun W hW => SegreChartDim.proof K ι W n m σ i (hWar W hW)
  have hsW : ∀ W, W ∈ divSupp P s ∧ IsHorizontal W → ∀ W'' ∈ segreChartComponents W σ i,
      chartSection σ i s ∈ W'' := fun W hW W'' hW'' =>
    (mem_segreChartComponents.1 hW'').1.2 (chartSection_mem (hWar W hW).2.1.2.1 σ i
      (hW.1.1.1.2 (le_sup_right (a := P) (Ideal.mem_span_singleton_self s))))
  have hnot := hNot K ι P (n + 1) m σ i A s hP hs
  refine ⟨fun J hJ W' => ⟨fun hW' => ?_, fun ⟨hJW', W, hW, hW'c⟩ => ?_⟩, fun W₁ W₂ h₁ h₂ W' hW₁ hW₂ => ?_⟩
  · have hJp : J.IsPrime := (mem_segreChartComponents.1 hJ).1.1
    have hW'p : W'.IsPrime := hW'.1.1
    have hdim := SectionComponents.ringKrullDim_quotient_add_one_eq (hnot J hJ) hW'
    rw [hJdim J hJ] at hdim
    have hJW' : J ≤ W' := le_sup_left.trans hW'.1.2
    have hsW' : chartSection σ i s ∈ W' :=
      ((le_sup_right (a := J)).trans hW'.1.2) (Ideal.mem_span_singleton_self _)

    have key : ∃ W, (W ∈ divSupp P s ∧ IsHorizontal W) ∧ ∃ W'' ∈ segreChartComponents W σ i, W'' ≤ W' := by
      by_contra hcon
      push Not at hcon
      let g : Ideal (MRing ι) → Ideal (MvPolynomial (Fin m) ℂ) → MvPolynomial (Fin m) ℂ := fun W W'' =>
        if h : (W ∈ divSupp P s ∧ IsHorizontal W) ∧ W'' ∈ segreChartComponents W σ i then
          (SetLike.not_le_iff_exists.1 (hcon W h.1 W'' h.2)).choose else 1
      have hg : ∀ W W'', (W ∈ divSupp P s ∧ IsHorizontal W) → W'' ∈ segreChartComponents W σ i →
          g W W'' ∈ W'' ∧ g W W'' ∉ W' := fun W W'' hW hW'' => by
        simp only [g, dif_pos (And.intro hW hW'')]
        exact (SetLike.not_le_iff_exists.1 (hcon W hW W'' hW'')).choose_spec
      set T := (divSupp_finite P s).toFinset.filter IsHorizontal
      have hT : ∀ W, W ∈ T ↔ W ∈ divSupp P s ∧ IsHorizontal W := fun W => by simp [T]
      set G := ∏ W ∈ T, ∏ W'' ∈ segreChartComponents W σ i, g W W''
      apply (show G ∉ W' from fun hG => by
        rw [Ideal.IsPrime.prod_mem_iff] at hG
        obtain ⟨W, hWT, hG⟩ := hG
        rw [Ideal.IsPrime.prod_mem_iff] at hG
        obtain ⟨W'', hW'', hG⟩ := hG
        exact (hg W W'' ((hT W).1 hWT) hW'').2 hG)
      rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := ℂ) W', mem_vanishingIdeal_iff]
      intro x hx
      rw [mem_zeroLocus_iff] at hx
      change ∀ p ∈ W', eval x p = 0 at hx
      change eval x G = 0
      have hxS : x ∈ segreChartSet P σ i := mem_segreChartSet_of_forall hPh σ i fun f hf =>
        hx f (hJW' ((mem_segreChartComponents.1 hJ).1.2 hf))
      obtain ⟨W, hW, hxW⟩ := exists_divSupp_of_eval hPh σ i s hxS (hx _ hsW')
      have : (RingHom.ker (eval x)).IsPrime := RingHom.ker_isPrime _
      have hle : segreChartIdeal W σ i ≤ RingHom.ker (eval x) :=
        fun f hf => (mem_vanishingIdeal_iff.1 hf) x hxW
      obtain ⟨W'', hW''min, hW''x⟩ := Ideal.exists_minimalPrimes_le hle
      have hW'' : W'' ∈ segreChartComponents W σ i := mem_segreChartComponents.2 hW''min
      rw [map_prod]
      refine Finset.prod_eq_zero ((hT W).2 hW) ?_
      rw [map_prod]
      refine Finset.prod_eq_zero hW'' ?_
      exact hW''x (hg W W'' hW hW'').1
    obtain ⟨W, hW, W'', hW'', hW''le⟩ := key
    have hW''p : W''.IsPrime := (mem_segreChartComponents.1 hW'').1.1
    have heq : W'' = W' := by
      by_contra hne
      have h := SectionComponents.ringKrullDim_quotient_add_one_le_of_lt (lt_of_le_of_ne hW''le hne)
      rw [hWdim W hW W'' hW'', hdim] at h
      have h6 : n + 1 ≤ n := by exact_mod_cast h
      omega
    exact ⟨hJW', W, hW, heq ▸ hW''⟩
  · have hJp : J.IsPrime := (mem_segreChartComponents.1 hJ).1.1
    have : W'.IsPrime := (mem_segreChartComponents.1 hW'c).1.1
    have hle : J ⊔ Ideal.span {chartSection σ i s} ≤ W' :=
      sup_le hJW' ((Ideal.span_singleton_le_iff_mem _).2 (hsW W hW W' hW'c))
    obtain ⟨Q, hQ, hQW'⟩ := Ideal.exists_minimalPrimes_le hle
    have hQp : Q.IsPrime := hQ.1.1
    have hdim := SectionComponents.ringKrullDim_quotient_add_one_eq (hnot J hJ) hQ
    rw [hJdim J hJ] at hdim
    rwa [← eq_of_le_of_dim hQW' n hdim (hWdim W hW W' hW'c)]
  · exact le_antisymm
      (le_of_common hNot (hWar W₂ h₂) (hWar W₁ h₁).2.1.2.1 σ i hW₂ hW₁)
      (le_of_common hNot (hWar W₁ h₁) (hWar W₂ h₂).2.1.2.1 σ i hW₁ hW₂)

end GroundTheory.Heights₂.Heights.Targets
