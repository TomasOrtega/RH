import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LogIntegralCongrSmul
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsMultiProjPrimeExtTo
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FractionRingRingEquiv
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FiniteVerticalRecursionStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.VerticalNumberLocalCycleStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.UniformizerDivisorCycleNumberStatement
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num.GenInt

section SlopeTestRemainingChoices

variable {K : Type} {ι : K → Type}

/- English proof (translation)
Unfold `intNumL intNum mixedDiff`. Rewrite using `[List.ofFn_get]`.
-/
theorem intNumL_ofFn_eq [DecidableEq K] (F : Type) [Field F] (Q : Ideal (MRing ι F)) {n : ℕ}
    (b : Fin n → K → ℤ) : intNumL F Q (List.ofFn b) = intNum F Q b := by
  unfold intNumL intNum mixedDiff
  rw [List.ofFn_get]

/- English proof (translation)
Unfold `divCycle`. Rewrite using `[dif_neg]`. Introduce and unpack `⟨h, -⟩`. Establish `e : (P ⊔ Ideal.span {(1 : MRing ι ℤ)}) = ⊤` using `by simp`. Rewrite `h` using `[e]`.

Conclude with `h.1.1.ne_top (top_le_iff.1 h.1.2)`.
-/
theorem divCycle_one (P W : Ideal (MRing ι ℤ)) : divCycle P (1 : MRing ι ℤ) W = 0 := by
  unfold divCycle
  rw [dif_neg]
  rintro ⟨h, -⟩
  have e : (P ⊔ Ideal.span {(1 : MRing ι ℤ)}) = ⊤ := by simp
  rw [e] at h
  exact h.1.1.ne_top (top_le_iff.1 h.1.2)

/- English proof (translation)
Unfold `divCycle at h`. Distinguish the cases in `hc : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes ∧ IsRelevant W`. Conclude with `⟨hc.1.1.1, hc.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))⟩`. Rewrite `h` using `[dif_neg hc]`. Conclude with `absurd rfl h`.
-/
theorem isPrime_mem_of_divCycle_ne {P W : Ideal (MRing ι ℤ)} {s : MRing ι ℤ}
    (h : divCycle P s W ≠ 0) : W.IsPrime ∧ s ∈ W := by
  unfold divCycle at h
  by_cases hc : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes ∧ IsRelevant W
  · exact ⟨hc.1.1.1, hc.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))⟩
  · rw [dif_neg hc] at h
    exact absurd rfl h

end SlopeTestRemainingChoices

end GlobalTheory.CompanionTheory.Ar.Num.GenInt

namespace GlobalTheory.CompanionTheory.Ar.Num.GenInt

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Introduce `m hm k`. Rewrite `hm` using `[C_apply]`. Establish `h0 : m = 0` using `Finset.mem_singleton.1 (support_monomial_subset hm)`. Substitute `h0` using the available equality. Simplify using the standard rewrite rules.
-/
theorem geoHomog_C (c : ℤ) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (C c : MRing ι ℤ) (0 : K → ℕ) := by
  intro m hm k
  rw [C_apply] at hm
  have h0 : m = 0 := Finset.mem_singleton.1 (support_monomial_subset hm)
  subst h0
  simp

/- English proof (translation)
Unfold `vertAt cycEval`. Use `finsum_eq_zero_of_forall_eq_zero fun W => ?_` and prove the remaining obligations. Distinguish the cases in `h : divCycle P (C (2 : ℤ)) W = 0`. Rewrite using `[h, zero_mul]`. Take `⟨hW, h2⟩` from `isPrime_mem_of_divCycle_ne h`.

Establish `hpW : (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∉ W`. Introduce `hpW`. Establish `hcop : IsCoprime (((p : ℕ) : ℤ)) 2`. Establish `: Nat.Coprime (p : ℕ) 2` using `(Nat.coprime_primes p.2 Nat.prime_two).2 hp`. Conclude with `Nat.isCoprime_iff_coprime.2 this` after adjusting the coercions.

Take `⟨a, b, hab⟩` from `hcop`. Apply `hW.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one]`. Establish `: (1 : MvPolynomial (Σ k, ι k) ℤ) = C a * C ((p : ℕ) : ℤ) + C b * C 2`. Rewrite using `[← C_mul, ← C_mul, ← C_add, hab, C_1]`.

Rewrite using `[this]`. Conclude with `W.add_mem (W.mul_mem_left _ hpW) (W.mul_mem_left _ h2)`. Conclude with `mul_eq_zero_of_right _ (if_neg hpW)`.
-/
theorem vertAt_two_of_ne (P : Ideal (MRing ι ℤ)) (p : Nat.Primes) (hp : (p : ℕ) ≠ 2) (l : List (K → ℤ)) :
    vertAt p P (C (2 : ℤ)) l = 0 := by
  classical
  unfold vertAt cycEval
  refine finsum_eq_zero_of_forall_eq_zero fun W => ?_
  by_cases h : divCycle P (C (2 : ℤ)) W = 0
  · rw [h, zero_mul]
  · obtain ⟨hW, h2⟩ := isPrime_mem_of_divCycle_ne h
    have hpW : (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∉ W := by
      intro hpW
      have hcop : IsCoprime (((p : ℕ) : ℤ)) 2 := by
        have : Nat.Coprime (p : ℕ) 2 := (Nat.coprime_primes p.2 Nat.prime_two).2 hp
        exact_mod_cast Nat.isCoprime_iff_coprime.2 this
      obtain ⟨a, b, hab⟩ := hcop
      apply hW.ne_top
      rw [Ideal.eq_top_iff_one]
      have : (1 : MvPolynomial (Σ k, ι k) ℤ) = C a * C ((p : ℕ) : ℤ) + C b * C 2 := by
        rw [← C_mul, ← C_mul, ← C_add, hab, C_1]
      rw [this]
      exact W.add_mem (W.mul_mem_left _ hpW) (W.mul_mem_left _ h2)
    exact mul_eq_zero_of_right _ (if_neg hpW)

/- English proof (translation)
Establish `hPp : P.IsPrime` using `hP.2.1.1`. Establish `hA : IsSmoothHerm (trivLine ι)` using `contDiffOn_const`. Establish `hc` using `ptsIntegral_congr_and_homog K ι P D (fun j z => Real.log ((L j).h z))`. Establish `nm1 : (1 : MRing ι ℤ) ∉ P` using `fun h => hPp.ne_top ((Ideal.eq_top_iff_one _).2 h)`. Establish `nm2 : (C (2 : ℤ) : MRing ι ℤ) ∉ P`.

Introduce `h`. Establish `h2 : (2 : ℤ) ∈ P.comap (C : ℤ →+* MRing ι ℤ)` using `h`. Rewrite `h2` using `[show P.comap (C : ℤ →+* MRing ι ℤ) = ⊥ from hP.2.2.1]`. Simplify using `at h2`. Establish `g1 : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (1 : MRing ι ℤ) (0 : K → ℕ)`.

Simplify using `using geoHomog_C (K := K) (ι := ι) 1`. Establish `g2 : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (C (2 : ℤ) : MRing ι ℤ) (0 : K → ℕ)` using `geoHomog_C 2`. Establish `f1 : IsMultiHomog (1 : MRing ι ℤ) (0 : K → ℕ)` using `isWeightedHomogeneous_one _ _`. Establish `f2 : IsMultiHomog (C (2 : ℤ) : MRing ι ℤ) (0 : K → ℕ)` using `isWeightedHomogeneous_C _ _`. Establish `e1` using `hI.2.2 P D L (trivLine ι) 1 0 hP hL hA (fun k => by simp [trivLine]) g1 nm1`.

Establish `e2` using `hI.2.2 P D L (trivLine ι) (C 2) 0 hP hL hA (fun k => by simp [trivLine]) g2 nm2`. Rewrite `e1` using `[(GlobalTheory.T.finite_vertical_recursion K ι P D hP I 0 1 f1 nm1 L (trivLine ι)).2]`. Rewrite `e2` using `[(GlobalTheory.T.finite_vertical_recursion K ι P D hP I 0 (C 2) f2 nm2 L (trivLine ι)).2]`. Establish `a1 : arInt P (1 : MRing ι ℤ) (trivLine ι) L = 0`. Unfold `arInt`.

Rewrite using `[hc.1 _ (fun _ => (0 : ℝ) * 1) (fun z _ => by simp [ReciprocityTheory.ChartRestriction.G.Geo.logNorm, trivLine]), hc.2 0 (fun _ => 1)]`. Simplify using the standard rewrite rules. Establish `a2 : arInt P (C (2 : ℤ) : MRing ι ℤ) (trivLine ι) L = Real.log 2 * ptsIntegral P (fun j z => Real.log ((L j).h z)) (fun _ => 1)`. Unfold `arInt`. Rewrite using `[hc.1 _ (fun _ => Real.log 2 * 1) (fun z _ => by simp [ReciprocityTheory.ChartRestriction.G.Geo.logNorm, trivLine]), hc.2 (Real.log 2) (fun _ => 1)]`.

Establish `v1 : ∀ p : Nat.Primes, vertAt p P (1 : MRing ι ℤ) (List.ofFn fun j => (L j).a) = 0`. Introduce `p`. Unfold `vertAt cycEval`. Conclude with `finsum_eq_zero_of_forall_eq_zero fun W => by rw [divCycle_one]; simp`. Establish `h1 : ∑ᶠ W, (divCycle P (1 : MRing ι ℤ) W : ℝ) * Set.indicator {W | IsHorizontal W} (fun W => I W D L) W = 0` using `finsum_eq_zero_of_forall_eq_zero fun W => by rw [divCycle_one]; simp`.

Establish `h2 : ∑ᶠ W, (divCycle P (C (2 : ℤ) : MRing ι ℤ) W : ℝ) * Set.indicator {W | IsHorizontal W} (fun W => I W D L) W = 0`. Use `finsum_eq_zero_of_forall_eq_zero fun W => ?_` and prove the remaining obligations. Distinguish the cases in `h : divCycle P (C (2 : ℤ) : MRing ι ℤ) W = 0`. Rewrite using `[h, Int.cast_zero, zero_mul]`. Establish `hW` using `(isPrime_mem_of_divCycle_ne h).2`.

Establish `: W ∉ {W : Ideal (MRing ι ℤ) | IsHorizontal W}`. Introduce `hH`. Establish `h2 : (2 : ℤ) ∈ W.comap (C : ℤ →+* MRing ι ℤ)` using `hW`. Rewrite `h2` using `[show W.comap (C : ℤ →+* MRing ι ℤ) = ⊥ from hH]`. Simplify using `at h2`.

Rewrite using `[Set.indicator_of_notMem this, mul_zero]`. Establish `p1 : ∑ᶠ p : Nat.Primes, Real.log (p : ℕ) * (vertAt p P (1 : MRing ι ℤ) (List.ofFn fun j => (L j).a) : ℝ) = 0` using `finsum_eq_zero_of_forall_eq_zero fun p => by rw [v1]; simp`. Establish `p2 : ∑ᶠ p : Nat.Primes, Real.log (p : ℕ) * (vertAt p P (C (2 : ℤ)) (List.ofFn fun j => (L j).a) : ℝ) = Real.log 2 * (vertAt ⟨2, Nat.prime_two⟩ P (C (2 : ℤ)) (List.ofFn fun j => (L j).a) : ℝ)`. Use `(finsum_eq_single _ (⟨2, Nat.prime_two⟩ : Nat.Primes) ?_).trans ?_` and prove the remaining obligations. Introduce `p hp`.

Establish `: (p : ℕ) ≠ 2` using `fun h => hp (Subtype.ext h)`. Rewrite using `[vertAt_two_of_ne P p this, Int.cast_zero, mul_zero]`. Evaluate the numerical expressions. Rewrite `e1` using `[h1, p1, a1]`. Rewrite `e2` using `[h2, p2, a2]`.

Establish `hlog : Real.log 2 ≠ 0` using `(Real.log_pos (by norm_num)).ne'`. Apply `mul_left_cancel₀ hlog` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ptsIntegral_one_eq_vertAt (P : Ideal (MRing ι ℤ)) (D : ℕ) (hP : IsArithVar P (D + 1))
    (I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (hI : IsIntersectionFamily I)
    (L : Fin D → HermLine ι) (hL : ∀ j, IsSmoothHerm (L j)) :
    ptsIntegral P (fun j z => Real.log ((L j).h z)) (fun _ => 1) =
      (vertAt ⟨2, Nat.prime_two⟩ P (C (2 : ℤ)) (List.ofFn fun j => (L j).a) : ℝ) := by
  classical
  have hPp : P.IsPrime := hP.2.1.1
  have hA : IsSmoothHerm (trivLine ι) := contDiffOn_const
  have hc := ptsIntegral_congr_and_homog K ι P D (fun j z => Real.log ((L j).h z))
  have nm1 : (1 : MRing ι ℤ) ∉ P := fun h => hPp.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have nm2 : (C (2 : ℤ) : MRing ι ℤ) ∉ P := by
    intro h
    have h2 : (2 : ℤ) ∈ P.comap (C : ℤ →+* MRing ι ℤ) := h
    rw [show P.comap (C : ℤ →+* MRing ι ℤ) = ⊥ from hP.2.2.1] at h2
    simp at h2
  have g1 : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (1 : MRing ι ℤ) (0 : K → ℕ) := by
    simpa using geoHomog_C (K := K) (ι := ι) 1
  have g2 : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (C (2 : ℤ) : MRing ι ℤ) (0 : K → ℕ) := geoHomog_C 2
  have f1 : IsMultiHomog (1 : MRing ι ℤ) (0 : K → ℕ) := isWeightedHomogeneous_one _ _
  have f2 : IsMultiHomog (C (2 : ℤ) : MRing ι ℤ) (0 : K → ℕ) := isWeightedHomogeneous_C _ _
  have e1 := hI.2.2 P D L (trivLine ι) 1 0 hP hL hA (fun k => by simp [trivLine]) g1 nm1
  have e2 := hI.2.2 P D L (trivLine ι) (C 2) 0 hP hL hA (fun k => by simp [trivLine]) g2 nm2
  rw [(GlobalTheory.T.finite_vertical_recursion K ι P D hP I 0 1 f1 nm1 L (trivLine ι)).2] at e1
  rw [(GlobalTheory.T.finite_vertical_recursion K ι P D hP I 0 (C 2) f2 nm2 L (trivLine ι)).2] at e2
  have a1 : arInt P (1 : MRing ι ℤ) (trivLine ι) L = 0 := by
    unfold arInt
    rw [hc.1 _ (fun _ => (0 : ℝ) * 1) (fun z _ => by simp [ReciprocityTheory.ChartRestriction.G.Geo.logNorm, trivLine]),
      hc.2 0 (fun _ => 1)]
    simp
  have a2 : arInt P (C (2 : ℤ) : MRing ι ℤ) (trivLine ι) L =
      Real.log 2 * ptsIntegral P (fun j z => Real.log ((L j).h z)) (fun _ => 1) := by
    unfold arInt
    rw [hc.1 _ (fun _ => Real.log 2 * 1) (fun z _ => by simp [ReciprocityTheory.ChartRestriction.G.Geo.logNorm, trivLine]),
      hc.2 (Real.log 2) (fun _ => 1)]
  have v1 : ∀ p : Nat.Primes, vertAt p P (1 : MRing ι ℤ) (List.ofFn fun j => (L j).a) = 0 := by
    intro p
    unfold vertAt cycEval
    exact finsum_eq_zero_of_forall_eq_zero fun W => by rw [divCycle_one]; simp
  have h1 : ∑ᶠ W, (divCycle P (1 : MRing ι ℤ) W : ℝ) *
      Set.indicator {W | IsHorizontal W} (fun W => I W D L) W = 0 :=
    finsum_eq_zero_of_forall_eq_zero fun W => by rw [divCycle_one]; simp
  have h2 : ∑ᶠ W, (divCycle P (C (2 : ℤ) : MRing ι ℤ) W : ℝ) *
      Set.indicator {W | IsHorizontal W} (fun W => I W D L) W = 0 := by
    refine finsum_eq_zero_of_forall_eq_zero fun W => ?_
    by_cases h : divCycle P (C (2 : ℤ) : MRing ι ℤ) W = 0
    · rw [h, Int.cast_zero, zero_mul]
    · have hW := (isPrime_mem_of_divCycle_ne h).2
      have : W ∉ {W : Ideal (MRing ι ℤ) | IsHorizontal W} := by
        intro hH
        have h2 : (2 : ℤ) ∈ W.comap (C : ℤ →+* MRing ι ℤ) := hW
        rw [show W.comap (C : ℤ →+* MRing ι ℤ) = ⊥ from hH] at h2
        simp at h2
      rw [Set.indicator_of_notMem this, mul_zero]
  have p1 : ∑ᶠ p : Nat.Primes, Real.log (p : ℕ) *
      (vertAt p P (1 : MRing ι ℤ) (List.ofFn fun j => (L j).a) : ℝ) = 0 :=
    finsum_eq_zero_of_forall_eq_zero fun p => by rw [v1]; simp
  have p2 : ∑ᶠ p : Nat.Primes, Real.log (p : ℕ) *
      (vertAt p P (C (2 : ℤ)) (List.ofFn fun j => (L j).a) : ℝ) =
      Real.log 2 * (vertAt ⟨2, Nat.prime_two⟩ P (C (2 : ℤ)) (List.ofFn fun j => (L j).a) : ℝ) := by
    refine (finsum_eq_single _ (⟨2, Nat.prime_two⟩ : Nat.Primes) ?_).trans ?_
    · intro p hp
      have : (p : ℕ) ≠ 2 := fun h => hp (Subtype.ext h)
      rw [vertAt_two_of_ne P p this, Int.cast_zero, mul_zero]
    · norm_num
  rw [h1, p1, a1] at e1
  rw [h2, p2, a2] at e2
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  apply mul_left_cancel₀ hlog
  linarith

/- English proof (translation)
Establish `hlen : (List.ofFn b).length = D` using `by simp`. Establish `hm` using `zp_model K ι P D hP p`. Establish `f2 : IsMultiHomog (C ((p : ℕ) : ℤ) : MRing ι ℤ) (0 : K → ℕ)` using `isWeightedHomogeneous_C _ _`. Establish `nm2 : (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∉ P`. Introduce `h`.

Establish `h2 : ((p : ℕ) : ℤ) ∈ P.comap (C : ℤ →+* MRing ι ℤ)` using `h`. Rewrite `h2` using `[show P.comap (C : ℤ →+* MRing ι ℤ) = ⊥ from hP.2.2.1]`. Use `p.2.ne_zero` as an intermediate fact. Simplify the hypotheses and the goal together. Rewrite using `[GlobalTheory.T.vertical_number_local_cycle K ι P D hP p 0 (C ((p : ℕ) : ℤ)) f2 nm2 (List.ofFn b) hlen]`.

Establish `hcy` using `GlobalTheory.T.uniformizer_divisor_cycle_number (ZP p) (((p : ℕ) : ZP p)) hm.1 K ι (extTo (ZP p) P) D hm.2.1 1 1 Empty Empty.elim 1 0 (MvPolynomial.isHomogeneous_one _ _) (List.ofFn b) (by simp)`. Establish `hg` using `genNum_zp_eq_rat K ι P p Empty Empty.elim 1 (List.ofFn b)`. Establish `hcN : ∀ Z : Ideal (MRing ι (ZP p)) → ℤ, cycNum Z (Empty.elim : Empty → K → ℤ) 1 (List.ofFn b) = (cycList Z (List.ofFn b) : ℝ)`. Introduce `Z`. Unfold `cycNum`.

Simplify using `[classList]`. Establish `hgN : genNum ℚ (extTo ℚ P) (Empty.elim : Empty → K → ℤ) 1 (List.ofFn b) = (intNum ℚ (extTo ℚ P) b : ℝ)`. Unfold `genNum`. Simplify using `[classList, intNumL_ofFn_eq]`. Rewrite `hcy` using `[hcN, hg, hgN]`.

Establish `e : MvPolynomial.map (Int.castRingHom (ZP p)) (C ((p : ℕ) : ℤ) : MRing ι ℤ) = C (((1 : (ZP p)ˣ) : ZP p) * ((p : ℕ) : ZP p) ^ 1)`. Simplify using the standard rewrite rules. Rewrite using `[e, hcy]`. Simplify using the standard rewrite rules.
-/
theorem vertAt_self_eq_intNum (P : Ideal (MRing ι ℤ)) (D : ℕ) (hP : IsArithVar P (D + 1))
    (p : Nat.Primes) (b : Fin D → K → ℤ) :
    (vertAt p P (C ((p : ℕ) : ℤ)) (List.ofFn b) : ℝ) = (intNum ℚ (extTo ℚ P) b : ℝ) := by
  classical
  have hlen : (List.ofFn b).length = D := by simp
  have hm := zp_model K ι P D hP p
  have f2 : IsMultiHomog (C ((p : ℕ) : ℤ) : MRing ι ℤ) (0 : K → ℕ) := isWeightedHomogeneous_C _ _
  have nm2 : (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∉ P := by
    intro h
    have h2 : ((p : ℕ) : ℤ) ∈ P.comap (C : ℤ →+* MRing ι ℤ) := h
    rw [show P.comap (C : ℤ →+* MRing ι ℤ) = ⊥ from hP.2.2.1] at h2
    have := p.2.ne_zero
    simp_all
  rw [GlobalTheory.T.vertical_number_local_cycle K ι P D hP p 0 (C ((p : ℕ) : ℤ)) f2 nm2 (List.ofFn b) hlen]
  have hcy := GlobalTheory.T.uniformizer_divisor_cycle_number (ZP p) (((p : ℕ) : ZP p)) hm.1 K ι (extTo (ZP p) P) D hm.2.1 1 1
    Empty Empty.elim 1 0 (MvPolynomial.isHomogeneous_one _ _) (List.ofFn b) (by simp)
  have hg := genNum_zp_eq_rat K ι P p Empty Empty.elim 1 (List.ofFn b)
  have hcN : ∀ Z : Ideal (MRing ι (ZP p)) → ℤ,
      cycNum Z (Empty.elim : Empty → K → ℤ) 1 (List.ofFn b) = (cycList Z (List.ofFn b) : ℝ) := by
    intro Z
    unfold cycNum
    simp [classList]
  have hgN : genNum ℚ (extTo ℚ P) (Empty.elim : Empty → K → ℤ) 1 (List.ofFn b) =
      (intNum ℚ (extTo ℚ P) b : ℝ) := by
    unfold genNum
    simp [classList, intNumL_ofFn_eq]
  rw [hcN, hg, hgN] at hcy
  have e : MvPolynomial.map (Int.castRingHom (ZP p)) (C ((p : ℕ) : ℤ) : MRing ι ℤ) =
      C (((1 : (ZP p)ˣ) : ZP p) * ((p : ℕ) : ZP p) ^ 1) := by
    simp
  rw [e, hcy]
  simp

end GlobalTheory.CompanionTheory.Ar.Num.GenInt

namespace GlobalTheory.CompanionTheory.Ar.Num

/- English proof (translation)
Introduce `K _ _ ι _ P D hP I hI L hL`. Rewrite using `[GenInt.ptsIntegral_one_eq_vertAt P D hP I hI L hL]`. Establish `h` using `GenInt.vertAt_self_eq_intNum P D hP ⟨2, Nat.prime_two⟩ (fun j => (L j).a)`. Establish `e : (((⟨2, Nat.prime_two⟩ : Nat.Primes) : ℕ) : ℤ) = 2` using `rfl`. Rewrite `h` using `[e]`. Then use the resulting hypothesis.
-/
theorem ptsIntegral_one_eq_intNum :
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ (I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I → ∀ L : Fin D → HermLine ι, (∀ j, IsSmoothHerm (L j)) → ptsIntegral P (fun j z => Real.log ((L j).h z)) (fun _ => 1) = (intNum ℚ (extTo ℚ P) (fun j => (L j).a) : ℝ) := by
  intro K _ _ ι _ P D hP I hI L hL
  rw [GenInt.ptsIntegral_one_eq_vertAt P D hP I hI L hL]
  have h := GenInt.vertAt_self_eq_intNum P D hP ⟨2, Nat.prime_two⟩ (fun j => (L j).a)
  have e : (((⟨2, Nat.prime_two⟩ : Nat.Primes) : ℕ) : ℤ) = 2 := rfl
  rwa [e] at h

end GlobalTheory.CompanionTheory.Ar.Num
