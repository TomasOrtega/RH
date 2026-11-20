import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import ReciprocityTheory.ThetaQuasiPeriods.Change
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero

namespace GlobalTheory

namespace ThetaCone

open MvPolynomial Filter Topology Module ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf

attribute [local instance] MvPolynomial.gradedAlgebra

section General

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
Rewrite using `[eval_eq, eval_eq, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun s hs => ?_` and prove the remaining obligations. Establish `hw` using `hG (mem_support_iff.mp hs)`. Simplify using `only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one] at hw`. Simplify using `only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hw]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem eval_mul_of_isHomogeneous (q : ι → ℂ) (t : ℂ) {G : MvPolynomial ι ℂ} {m : ℕ}
    (hG : G.IsHomogeneous m) : eval (fun i => t * q i) G = t ^ m * eval q G := by
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hw := hG (mem_support_iff.mp hs)
  simp only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one] at hw
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hw]
  ring

/- English proof (translation)
Apply `MvPolynomial.induction_on F` to reduce the goal to its premises. Introduce `a`. Simplify using `only [eval_C]`. Conclude with `differentiable_const a`. Introduce `p q hp hq`.

Simplify using `only [map_add]`. Conclude with `hp.add hq`. Introduce `p c hp`. Simplify using `only [map_mul, eval_X]`. Conclude with `hp.mul (hφ c)`.
-/
theorem differentiable_eval {φ : ι → E → ℂ} (hφ : ∀ c, Differentiable ℂ (φ c))
    (F : MvPolynomial ι ℂ) : Differentiable ℂ fun z => eval (fun c => φ c z) F := by
  apply MvPolynomial.induction_on F
  · intro a
    simp only [eval_C]
    exact differentiable_const a
  · intro p q hp hq
    simp only [map_add]
    exact hp.add hq
  · intro p c hp
    simp only [map_mul, eval_X]
    exact hp.mul (hφ c)

/- English proof (translation)
Distinguish the cases in `hf0 : ∀ z, f z = 0`. Conclude with `Or.inl hf0`. Use `right`. Simplify using `only [not_forall] at hf0`. Take `⟨a, ha⟩` from `hf0`.

Establish `hev : g =ᶠ[𝓝 a] 0` using `by filter_upwards [hf.continuous.continuousAt.eventually_ne ha] with z hz`. Conclude with `(mul_eq_zero.mp (h z)).resolve_left hz`. Establish `hga : AnalyticOnNhd ℂ g Set.univ` using `GlobalTheory.SCV.analyticOnNhd_of_differentiable hg Set.univ`. Establish `hzero` using `hga.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ a) hev`. Conclude with `fun z => hzero (Set.mem_univ z)`.
-/
theorem eq_zero_or_eq_zero_of_mul [FiniteDimensional ℂ E] {f g : E → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (h : ∀ z, f z * g z = 0) :
    (∀ z, f z = 0) ∨ ∀ z, g z = 0 := by
  by_cases hf0 : ∀ z, f z = 0
  · exact Or.inl hf0
  right
  simp only [not_forall] at hf0
  obtain ⟨a, ha⟩ := hf0

  have hev : g =ᶠ[𝓝 a] 0 := by
    filter_upwards [hf.continuous.continuousAt.eventually_ne ha] with z hz
    exact (mul_eq_zero.mp (h z)).resolve_left hz
  have hga : AnalyticOnNhd ℂ g Set.univ := GlobalTheory.SCV.analyticOnNhd_of_differentiable hg Set.univ
  have hzero := hga.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ a) hev
  exact fun z => hzero (Set.mem_univ z)

/- English proof (translation)
Use `Ideal.isPrime_iff.mpr ⟨fun htop => ?_, fun {F G} hFG => ?_⟩` and prove the remaining obligations. Establish `h1` using `(hI 1).mp ((Ideal.eq_top_iff_one I).mp htop) 1 0`. Simplify using `at h1`. Establish `hmul` using `(hI _).mp hFG`. Establish `hψ : ∀ c, Differentiable ℂ (fun p : ℂ × E => p.1 * φ c p.2)` using `fun c => differentiable_fst.mul ((hφ c).comp differentiable_snd)`.

Break down `eq_zero_or_eq_zero_of_mul (differentiable_eval hψ F) (differentiable_eval hψ G) (fun p => by simpa only [map_mul] using hmul p.1 p.2) with h | h` into its components or cases. Conclude with `Or.inl ((hI F).mpr fun t z => h (t, z))`. Conclude with `Or.inr ((hI G).mpr fun t z => h (t, z))`.
-/
theorem isPrime [FiniteDimensional ℂ E] {φ : ι → E → ℂ} (hφ : ∀ c, Differentiable ℂ (φ c))
    {I : Ideal (MvPolynomial ι ℂ)}
    (hI : ∀ F, F ∈ I ↔ ∀ (t : ℂ) (z : E), eval (fun c => t * φ c z) F = 0) : I.IsPrime := by
  refine Ideal.isPrime_iff.mpr ⟨fun htop => ?_, fun {F G} hFG => ?_⟩
  · have h1 := (hI 1).mp ((Ideal.eq_top_iff_one I).mp htop) 1 0
    simp at h1

  have hmul := (hI _).mp hFG
  have hψ : ∀ c, Differentiable ℂ (fun p : ℂ × E => p.1 * φ c p.2) := fun c =>
    differentiable_fst.mul ((hφ c).comp differentiable_snd)
  rcases eq_zero_or_eq_zero_of_mul (differentiable_eval hψ F) (differentiable_eval hψ G)
      (fun p => by simpa only [map_mul] using hmul p.1 p.2) with h | h
  · exact Or.inl ((hI F).mpr fun t z => h (t, z))
  · exact Or.inr ((hI G).mpr fun t z => h (t, z))

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
/- English proof (translation)
Introduce `i F hF`. Establish `hdec : ((DirectSum.decompose (homogeneousSubmodule ι ℂ) F) i : MvPolynomial ι ℂ) = homogeneousComponent i F` using `decomposition.decompose'_apply F i`. Rewrite using `[hdec]`. Use `(hI _).mpr fun t z => ?_` and prove the remaining obligations. Rewrite using `[eval_mul_of_isHomogeneous (fun c => φ c z) t (homogeneousComponent_isHomogeneous i F)]`.

It suffices to establish `hz : eval (fun c => φ c z) (homogeneousComponent i F) = 0 by rw [hz, mul_zero]`. Establish `hn : F.totalDegree + 1 ≤ F.totalDegree + i + 1` using `by omega`. Establish `hsum : ∑ m ∈ Finset.range (F.totalDegree + i + 1), homogeneousComponent m F = F`. Rewrite using `[← Finset.sum_subset (Finset.range_mono hn) (fun m _ hm => by`. Apply `homogeneousComponent_eq_zero` to reduce the goal to its premises.

Simplify using `only [Finset.mem_range, not_lt] at hm`. Use the proof step `omega)]`. Conclude with `sum_homogeneousComponent F`. Establish `hP : ∀ s : ℂ, (∑ m ∈ Finset.range (F.totalDegree + i + 1), Polynomial.C (eval (fun c => φ c z) (homogeneousComponent m F)) * Polynomial.X ^ m).eval s = (0 : Polynomial ℂ).eval s`. Introduce `s`.

Establish `h0` using `(hI F).mp hF s z`. Rewrite `h0` using `[← hsum, map_sum]`. Simplify using `only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero]`. Rewrite using `[← h0]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations.

Rewrite using `[eval_mul_of_isHomogeneous (fun c => φ c z) s (homogeneousComponent_isHomogeneous m F)]`. Expand and normalize the polynomial expressions, which then agree. Establish `hc` using `congrArg (fun p => Polynomial.coeff p i) (Polynomial.funext hP)`. Simplify using `only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero, Finset.sum_ite_eq, Finset.mem_range] at hc`. Simplify `hc` using `[show i < F.totalDegree + i + 1 by omega]`.
-/
theorem isHomogeneous {φ : ι → E → ℂ} {I : Ideal (MvPolynomial ι ℂ)}
    (hI : ∀ F, F ∈ I ↔ ∀ (t : ℂ) (z : E), eval (fun c => t * φ c z) F = 0) :
    I.IsHomogeneous (homogeneousSubmodule ι ℂ) := by
  intro i F hF
  have hdec : ((DirectSum.decompose (homogeneousSubmodule ι ℂ) F) i : MvPolynomial ι ℂ) =
      homogeneousComponent i F := decomposition.decompose'_apply F i
  rw [hdec]
  refine (hI _).mpr fun t z => ?_
  rw [eval_mul_of_isHomogeneous (fun c => φ c z) t (homogeneousComponent_isHomogeneous i F)]
  suffices hz : eval (fun c => φ c z) (homogeneousComponent i F) = 0 by rw [hz, mul_zero]

  have hn : F.totalDegree + 1 ≤ F.totalDegree + i + 1 := by omega
  have hsum : ∑ m ∈ Finset.range (F.totalDegree + i + 1), homogeneousComponent m F = F := by
    rw [← Finset.sum_subset (Finset.range_mono hn) (fun m _ hm => by
      apply homogeneousComponent_eq_zero
      simp only [Finset.mem_range, not_lt] at hm
      omega)]
    exact sum_homogeneousComponent F
  have hP : ∀ s : ℂ, (∑ m ∈ Finset.range (F.totalDegree + i + 1),
      Polynomial.C (eval (fun c => φ c z) (homogeneousComponent m F)) * Polynomial.X ^ m).eval s
        = (0 : Polynomial ℂ).eval s := by
    intro s
    have h0 := (hI F).mp hF s z
    rw [← hsum, map_sum] at h0
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero]
    rw [← h0]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [eval_mul_of_isHomogeneous (fun c => φ c z) s (homogeneousComponent_isHomogeneous m F)]
    ring
  have hc := congrArg (fun p => Polynomial.coeff p i) (Polynomial.funext hP)
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero,
    Finset.sum_ite_eq, Finset.mem_range] at hc
  simpa [show i < F.totalDegree + i + 1 by omega] using hc

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
/- English proof (translation)
Distinguish the cases in `hfin : FiniteDimensional ℂ (quotPiece I d)`. Use `swap`. Rewrite using `[Module.finrank_of_not_finite hfin]`. Conclude with `Nat.zero_le _`. Set `b` to `Module.finBasis ℂ (quotPiece I d)`.

Establish `hlift : ∀ x ∈ quotPiece I d, ∃ p ∈ homogeneousSubmodule ι ℂ d, (Ideal.Quotient.mkₐ ℂ I).toLinearMap p = x`. Introduce `x hx`. Rewrite `hx` using `[quotPiece_natCast]`. Conclude with `Submodule.mem_map.mp hx`. Establish `hmem : ∀ k, ∃ p ∈ homogeneousSubmodule ι ℂ d, (Ideal.Quotient.mkₐ ℂ I).toLinearMap p = (b k : MvPolynomial ι ℂ ⧸ I)` using `fun k => hlift _ (b k).2`.

Use `choose F hFd hFb using hmem`. Use `hB _ F (fun k => (mem_homogeneousSubmodule d (F k)).mp (hFd k)) ?_` and prove the remaining obligations. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `a ha`. Establish `hhom : (∑ k, a k • F k).IsHomogeneous d` using `(mem_homogeneousSubmodule d _).mp (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hFd k))`.

Establish `hG : ∑ k, a k • F k ∈ I`. Use `(hI _).mpr fun t z => ?_` and prove the remaining obligations. Rewrite using `[eval_mul_of_isHomogeneous (fun c => φ c z) t hhom]`. Establish `hz` using `congrFun ha z`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hz`.

Rewrite using `[map_sum]`. Simplify using `only [smul_eval]`. Rewrite using `[hz, mul_zero]`. Establish `h0 : ∑ k, a k • b k = 0`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero]`. Repeatedly rewrite using `[← hFb, ← map_smul, ← map_sum]`. Simplify using `only [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mpr hG`. Conclude with `(Fintype.linearIndependent_iff.mp b.linearIndependent) a h0`.
-/
theorem finrank_quotPiece_le [Finite ι] {φ : ι → E → ℂ} {I : Ideal (MvPolynomial ι ℂ)}
    (hI : ∀ F, F ∈ I ↔ ∀ (t : ℂ) (z : E), eval (fun c => t * φ c z) F = 0) {d B : ℕ}
    (hB : ∀ (r : ℕ) (F : Fin r → MvPolynomial ι ℂ), (∀ k, (F k).IsHomogeneous d) →
      LinearIndependent ℂ (fun k z => eval (fun c => φ c z) (F k)) → r ≤ B) :
    finrank ℂ (quotPiece I d) ≤ B := by
  classical
  by_cases hfin : FiniteDimensional ℂ (quotPiece I d)
  swap
  · rw [Module.finrank_of_not_finite hfin]
    exact Nat.zero_le _
  let b := Module.finBasis ℂ (quotPiece I d)

  have hlift : ∀ x ∈ quotPiece I d, ∃ p ∈ homogeneousSubmodule ι ℂ d,
      (Ideal.Quotient.mkₐ ℂ I).toLinearMap p = x := by
    intro x hx
    rw [quotPiece_natCast] at hx
    exact Submodule.mem_map.mp hx
  have hmem : ∀ k, ∃ p ∈ homogeneousSubmodule ι ℂ d,
      (Ideal.Quotient.mkₐ ℂ I).toLinearMap p = (b k : MvPolynomial ι ℂ ⧸ I) :=
    fun k => hlift _ (b k).2
  choose F hFd hFb using hmem
  refine hB _ F (fun k => (mem_homogeneousSubmodule d (F k)).mp (hFd k)) ?_
  rw [Fintype.linearIndependent_iff]
  intro a ha
  have hhom : (∑ k, a k • F k).IsHomogeneous d := (mem_homogeneousSubmodule d _).mp
    (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hFd k))
  have hG : ∑ k, a k • F k ∈ I := by
    refine (hI _).mpr fun t z => ?_
    rw [eval_mul_of_isHomogeneous (fun c => φ c z) t hhom]
    have hz := congrFun ha z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hz
    rw [map_sum]
    simp only [smul_eval]
    rw [hz, mul_zero]
  have h0 : ∑ k, a k • b k = 0 := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero]
    simp_rw [← hFb, ← map_smul, ← map_sum]
    simp only [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hG
  exact (Fintype.linearIndependent_iff.mp b.linearIndependent) a h0

/- English proof (translation)
Establish `hprime` using `isPrime hφ hI`. Establish `hhom` using `isHomogeneous hI`. Take `⟨c, hc⟩` from `hne`. Establish `hX : ∃ i, X i ∉ I` using `⟨c, fun hmem => hc (funext fun z => by simpa using (hI _).mp hmem 1 z)⟩`. Use `⟨hprime, ?_⟩` and prove the remaining obligations.

Use `hprime` as an intermediate fact. Rewrite using `[ProjCut.ringKrullDim_eq_natDegree_idealHilbertPoly hhom hX]`. Establish `hle : (idealHilbertPoly I).degree ≤ (Polynomial.C ((N : ℚ) ^ g) * Polynomial.X ^ g).degree`. Apply `degree_le_of_eventually_eval_nat (eventually_idealHilbertPoly_nonneg hhom)` to reduce the goal to its premises. Use `filter_upwards [eventually_finrank_quotPiece hhom, Filter.eventually_ge_atTop 1] with n hn hn1`.

Rewrite using `[← hn]`. Establish `hb` using `finrank_quotPiece_le hI (hB n hn1)`. Simplify using `only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]`. Rewrite using `[← mul_pow]`. Conclude with `hb` after adjusting the coercions.

Establish `hdeg : (idealHilbertPoly I).natDegree ≤ g` using `Polynomial.natDegree_le_of_degree_le (hle.trans (Polynomial.degree_C_mul_X_pow_le _ _))`. Conclude with `(show (idealHilbertPoly I).natDegree + 1 ≤ g + 1 by omega)` after adjusting the coercions.
-/
theorem isPrime_and_ringKrullDim_le [Finite ι] [FiniteDimensional ℂ E] {φ : ι → E → ℂ}
    (hφ : ∀ c, Differentiable ℂ (φ c)) (hne : ∃ c, φ c ≠ 0) {I : Ideal (MvPolynomial ι ℂ)}
    (hI : ∀ F, F ∈ I ↔ ∀ (t : ℂ) (z : E), eval (fun c => t * φ c z) F = 0) {g N : ℕ}
    (hB : ∀ d, 1 ≤ d → ∀ (r : ℕ) (F : Fin r → MvPolynomial ι ℂ), (∀ k, (F k).IsHomogeneous d) →
      LinearIndependent ℂ (fun k z => eval (fun c => φ c z) (F k)) → r ≤ (N * d) ^ g) :
    I.IsPrime ∧ ringKrullDim (MvPolynomial ι ℂ ⧸ I) ≤ (g + 1 : ℕ) := by
  classical
  have hprime := isPrime hφ hI
  have hhom := isHomogeneous hI
  obtain ⟨c, hc⟩ := hne
  have hX : ∃ i, X i ∉ I :=
    ⟨c, fun hmem => hc (funext fun z => by simpa using (hI _).mp hmem 1 z)⟩
  refine ⟨hprime, ?_⟩
  have := hprime
  rw [ProjCut.ringKrullDim_eq_natDegree_idealHilbertPoly hhom hX]

  have hle : (idealHilbertPoly I).degree ≤
      (Polynomial.C ((N : ℚ) ^ g) * Polynomial.X ^ g).degree := by
    apply degree_le_of_eventually_eval_nat (eventually_idealHilbertPoly_nonneg hhom)
    filter_upwards [eventually_finrank_quotPiece hhom, Filter.eventually_ge_atTop 1]
      with n hn hn1
    rw [← hn]
    have hb := finrank_quotPiece_le hI (hB n hn1)
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [← mul_pow]
    exact_mod_cast hb
  have hdeg : (idealHilbertPoly I).natDegree ≤ g :=
    Polynomial.natDegree_le_of_degree_le (hle.trans (Polynomial.degree_C_mul_X_pow_le _ _))
  exact_mod_cast (show (idealHilbertPoly I).natDegree + 1 ≤ g + 1 by omega)

end General

end ThetaCone

open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real

/- English proof (translation)
Introduce `hA hBd g τ hτ N hN I hI`. Set `ψ : (Fin g → Fin N) → (Fin g → ℂ) → ℂ` to `fun c z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)`. Establish `hAc` using `hA g τ hτ N (by omega)`. Establish `hdiff : ∀ c, Differentiable ℂ (ψ c)` using `fun c => (hAc.1 c).1`. Establish `hquasi : ∀ c (n n' : Fin g → ℤ) z, ψ c (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * ψ c z` using `fun c => (hAc.1 c).2`.

Establish `: Nonempty (Fin g → Fin N)` using `⟨fun _ => ⟨0, by omega⟩⟩`. Establish `hne : ∃ c, ψ c ≠ 0` using `⟨Classical.arbitrary _, hAc.2.ne_zero _⟩`. Use `ThetaCone.isPrime_and_ringKrullDim_le (φ := ψ) (g := g) (N := N) hdiff hne hI ?_` and prove the remaining obligations. Introduce `d hd r F hF hind`. Establish `hscale : ∀ (k : Fin r) (w z : Fin g → ℂ) (l : ℂ), (∀ c, ψ c w = l * ψ c z) → MvPolynomial.eval (fun c => ψ c w) (F k) = l ^ d * MvPolynomial.eval (fun c => ψ c z) (F k)`.

Introduce `k w z l h`. Rewrite using `[← ThetaCone.eval_mul_of_isHomogeneous (fun c => ψ c z) l (hF k)]`. Establish `hfun : (fun c => ψ c w) = fun c => l * ψ c z` using `funext h`. Rewrite using `[hfun]`. Establish `hzero : ofIntVec (0 : Fin g → ℤ) = 0`.

Use function extensionality and compare the values at `i`. Simplify using `[ofIntVec]`. Establish `hsingle : ∀ j : Fin g, ofIntVec (Pi.single j (1 : ℤ)) = (Pi.single j 1 : Fin g → ℂ)`. Introduce `j`. Use function extensionality and compare the values at `i`.

Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[ofIntVec]`. Simplify using `[ofIntVec, h]`. Use `hBd g (N * d) τ (fun j => eC (-(τ j j) / 2)) (Nat.mul_pos (by omega) hd) (fun j => Complex.exp_ne_zero _) r (fun k z => MvPolynomial.eval (fun c => ψ c z) (F k)) (fun k => ⟨ThetaCone.differentiable_eval hdiff (F k), fun i z => ?_, fun j z => ?_⟩) hind` and prove the remaining obligations.

Establish `h` using `hscale k (z + Pi.single i 1) z 1 (fun c => by`. Simplify `hquasi c 0 (Pi.single i 1) z)` using `[hzero, hsingle, eC]`. Simplify using `using h`. Establish `h` using `hscale k (z + τ.mulVec (Pi.single j 1)) z (eC (-(N : ℂ) * (τ j j / 2 + z j))) (fun c => by simpa [hzero, hsingle] using hquasi c (Pi.single j 1) 0 z)`. Rewrite using `[h]`.

Use `congr 1`. Simplify using `only [eC, ← Complex.exp_nat_mul, ← Complex.exp_add]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem thetaConeIdeal_isPrime_and_ringKrullDim_le :
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → (∀ c : Fin g → Fin N, (Differentiable ℂ (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) z)) ∧ LinearIndependent ℂ (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))) → (∀ (g n : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (b : Fin g → ℂ), 1 ≤ n → (∀ j, b j ≠ 0) → ∀ (N : ℕ) (f : Fin N → (Fin g → ℂ) → ℂ), (∀ k, (Differentiable ℂ (f k) ∧ (∀ (i : Fin g) z, (f k) (z + Pi.single i 1) = (f k) z) ∧ ∀ (j : Fin g) z, (f k) (z + τ.mulVec (Pi.single j 1)) = b j ^ n * cexp (-(2 * Real.pi * I) * n * z j) * (f k) z)) → LinearIndependent ℂ f → N ≤ n ^ g) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 2 ≤ N → ∀ (I : Ideal (MvPolynomial (Fin g → Fin N) ℂ)), (∀ F, F ∈ I ↔ ∀ (t : ℂ) (z : Fin g → ℂ), MvPolynomial.eval (fun c => t * theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) F = 0) → I.IsPrime ∧ ringKrullDim (MvPolynomial (Fin g → Fin N) ℂ ⧸ I) ≤ (g + 1 : ℕ)) := by
  intro hA hBd g τ hτ N hN I hI
  let ψ : (Fin g → Fin N) → (Fin g → ℂ) → ℂ := fun c z =>
    theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)
  have hAc := hA g τ hτ N (by omega)
  have hdiff : ∀ c, Differentiable ℂ (ψ c) := fun c => (hAc.1 c).1
  have hquasi : ∀ c (n n' : Fin g → ℤ) z, ψ c (z + τ *ᵥ ofIntVec n + ofIntVec n') =
      eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * ψ c z :=
    fun c => (hAc.1 c).2
  have : Nonempty (Fin g → Fin N) := ⟨fun _ => ⟨0, by omega⟩⟩
  have hne : ∃ c, ψ c ≠ 0 := ⟨Classical.arbitrary _, hAc.2.ne_zero _⟩
  refine ThetaCone.isPrime_and_ringKrullDim_le (φ := ψ) (g := g) (N := N) hdiff hne hI ?_
  intro d hd r F hF hind

  have hscale : ∀ (k : Fin r) (w z : Fin g → ℂ) (l : ℂ), (∀ c, ψ c w = l * ψ c z) →
      MvPolynomial.eval (fun c => ψ c w) (F k) = l ^ d * MvPolynomial.eval (fun c => ψ c z) (F k) := by
    intro k w z l h
    rw [← ThetaCone.eval_mul_of_isHomogeneous (fun c => ψ c z) l (hF k)]
    have hfun : (fun c => ψ c w) = fun c => l * ψ c z := funext h
    rw [hfun]
  have hzero : ofIntVec (0 : Fin g → ℤ) = 0 := by
    funext i
    simp [ofIntVec]
  have hsingle : ∀ j : Fin g, ofIntVec (Pi.single j (1 : ℤ)) = (Pi.single j 1 : Fin g → ℂ) := by
    intro j
    funext i
    by_cases h : i = j
    · subst h
      simp [ofIntVec]
    · simp [ofIntVec, h]
  refine hBd g (N * d) τ (fun j => eC (-(τ j j) / 2)) (Nat.mul_pos (by omega) hd)
    (fun j => Complex.exp_ne_zero _) r (fun k z => MvPolynomial.eval (fun c => ψ c z) (F k))
    (fun k => ⟨ThetaCone.differentiable_eval hdiff (F k), fun i z => ?_, fun j z => ?_⟩) hind
  · have h := hscale k (z + Pi.single i 1) z 1 (fun c => by
      simpa [hzero, hsingle, eC] using hquasi c 0 (Pi.single i 1) z)
    simpa using h
  · have h := hscale k (z + τ.mulVec (Pi.single j 1)) z (eC (-(N : ℂ) * (τ j j / 2 + z j)))
      (fun c => by simpa [hzero, hsingle] using hquasi c (Pi.single j 1) 0 z)
    rw [h]
    congr 1
    simp only [eC, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring

end GlobalTheory
