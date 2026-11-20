import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSegreArith
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.LemCone
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodB
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

namespace ProjAvoidingForm

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def segreSub : MvPolynomial (Ix ((k : K) → ι k)) ℤ →ₐ[ℤ] MRing ι :=
  aeval fun p => ∏ k, X ⟨k, p.2 k⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem segreSub_X (p : Ix ((k : K) → ι k)) : segreSub (X p) = ∏ k, (X ⟨k, p.2 k⟩ : MRing ι) :=
  aeval_X _ _

variable {Ω : Type} [Field Ω]

/- English proof (translation)
Proceed by induction. Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately. Treat this case separately.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem mConeMap_segreSub (y : (Σ k, ι k) → Ω) (Q : MvPolynomial (Ix ((k : K) → ι k)) ℤ) :
    mConeMap y (segreSub Q) =
      Polynomial.eval₂ MvPolynomial.C (∏ k, (MvPolynomial.X k : MvPolynomial K Ω))
        (coneMap ℤ (segreCoords y) Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    simp only [segreSub, coneMap, mConeMap, eq_intCast, map_intCast]
    exact (map_intCast (Polynomial.eval₂RingHom (MvPolynomial.C : Ω →+* MvPolynomial K Ω)
      (∏ k, (MvPolynomial.X k : MvPolynomial K Ω))) a).symm
  | add p q hp hq => simp only [map_add, hp, hq, Polynomial.eval₂_add]
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp, map_mul, Polynomial.eval₂_mul]
    congr 1
    simp [segreSub, coneMap, mConeMap, segreCoords, Finset.prod_mul_distrib, map_prod,
      Polynomial.eval₂_finsetProd]

/- English proof (translation)
Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem segreSub_mem (y : (Σ k, ι k) → Ω) {Q : MvPolynomial (Ix ((k : K) → ι k)) ℤ}
    (hQ : Q ∈ coordIdeal ℤ (segreCoords y)) : segreSub Q ∈ mCoordIdeal y := by
  rw [coordIdeal, RingHom.mem_ker] at hQ
  rw [mCoordIdeal, RingHom.mem_ker, mConeMap_segreSub, hQ, Polynomial.eval₂_zero]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
theorem eval_segreSub (z : (Σ k, ι k) → ℂ) (Q : MvPolynomial (Ix ((k : K) → ι k)) ℤ) :
    eval z (map (Int.castRingHom ℂ) (segreSub Q)) = eval (segreCoords z) (map (Int.castRingHom ℂ) Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [segreSub]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    simp [segreSub, segreCoords, map_prod]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
theorem aeval_qmap {J : Type} (u : J → ℂ) (Q : MvPolynomial J ℤ) :
    aeval u (qmap Q) = eval u (map (Int.castRingHom ℂ) Q) := by
  show aeval u (map (Int.castRingHom ℚ) Q) = _
  rw [aeval_def, eval₂_map, eval_map]
  congr 1

variable [CharZero Ω]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules.
-/
theorem coneMap_qmap {J : Type} (x : J → Ω) (Q : MvPolynomial J ℤ) : coneMap ℚ x (qmap Q) = coneMap ℤ x Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [coneMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, map_X, hp]; simp [coneMap]

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
theorem aeval_segre_eq_zero (y : (Σ k, ι k) → Ω) {R : MvPolynomial (Ix ((k : K) → ι k)) ℚ} {N : ℕ}
    (hR : R.IsHomogeneous N) (h0 : aeval (segreCoords y) R = 0) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) : aeval (segreCoords z) R = 0 := by
  have h1 : coneMap ℚ (segreCoords y) R = 0 :=
    RingHom.mem_ker.mp (mem_coordIdeal_of_isHomogeneous ℚ (segreCoords y) hR h0)
  obtain ⟨M, hM, R', hR'⟩ := exists_int_mul_eq_qmap R
  have h2 : segreSub R' ∈ mCoordIdeal y := by
    apply segreSub_mem
    rw [coordIdeal, RingHom.mem_ker, ← coneMap_qmap, ← hR', map_mul, h1, mul_zero]
  have h3 := hz.2 _ h2
  rw [eval_segreSub, ← aeval_qmap, ← hR', map_mul] at h3
  simpa [hM] using h3

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Rewrite the conclusion repeatedly using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem aeval_mul_of_isHomogeneous {σ : Type} {G : MvPolynomial σ ℚ} {d : ℕ} (hG : G.IsHomogeneous d)
    (v : σ → ℂ) (c : ℂ) : aeval (fun j => c * v j) G = c ^ d * aeval v G := by
  simp only [aeval_def, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∑ i ∈ m.support, m i = d := by
    have := hG (mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp_rw [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

section Blocks

variable [DecidableEq K]

def blockW (k : K) : (Σ k, ι k) → ℕ := fun p => if p.1 = k then 1 else 0

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem weight_blockW (k : K) (m : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (blockW (ι := ι) k) m = ∑ i, m ⟨k, i⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma]
  simp [blockW]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isMultiHomog_of_weighted {s : MRing ι} {a : K → ℕ}
    (h : ∀ k, IsWeightedHomogeneous (blockW k) s (a k)) : IsMultiHomog s a := by
  intro m hm k
  rw [← weight_blockW]
  exact h k (mem_support_iff.mp hm)

/- English proof (translation)
Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem isWeightedHomogeneous_segreMonomial (k : K) (f : (k : K) → ι k) :
    IsWeightedHomogeneous (blockW k) (∏ k', (X ⟨k', f k'⟩ : MRing ι)) 1 := by
  have := IsWeightedHomogeneous.prod Finset.univ (fun k' => (X ⟨k', f k'⟩ : MRing ι))
    (fun k' => blockW (ι := ι) k ⟨k', f k'⟩) (fun k' _ => isWeightedHomogeneous_X _ _ _)
  simpa [blockW] using this

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem isMultiHomog_segreSub_linear (n : Ix ((k : K) → ι k) → ℤ) :
    IsMultiHomog (segreSub (∑ i, C (n i) * X i)) (fun _ : K => 1) := by
  apply isMultiHomog_of_weighted
  intro k
  simp only [map_sum, map_mul, algHom_C, segreSub_X]
  exact IsWeightedHomogeneous.sum _ _ _ fun i _ => (isWeightedHomogeneous_segreMonomial k i.2).C_mul _

/- English proof (translation)
Proceed by induction. Treat this case separately. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Treat this case separately. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction.

Establish an intermediate fact. Simplify using the standard rewrite rules. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Consider separately whether the proposition holds or fails. Substitute using the available equality. Establish an intermediate fact. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Use linear arithmetic over natural numbers and integers. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem exists_segre_prod (m : ℕ) (e : (Σ k, ι k) → ℕ) (he : ∀ k, ∑ i, e ⟨k, i⟩ = m) :
    ∃ M : MvPolynomial (Ix ((k : K) → ι k)) ℤ, M.IsHomogeneous m ∧
      segreSub M = ∏ p, (X p : MRing ι) ^ e p := by
  classical
  induction m generalizing e with
  | zero =>
    refine ⟨1, isHomogeneous_one _ _, ?_⟩
    have h0 : ∀ p, e p = 0 := fun p => by
      have := he p.1
      rw [Finset.sum_eq_zero_iff] at this
      exact this p.2 (Finset.mem_univ _)
    simp [h0]
  | succ m ih =>
    have hex : ∀ k, ∃ i, e ⟨k, i⟩ ≠ 0 := fun k => by
      by_contra h
      push Not at h
      have := he k
      simp [h] at this
    choose c hc using hex
    let t : (Σ k, ι k) → ℕ := fun p => if p.2 = c p.1 then 1 else 0
    have ht : ∀ k, ∑ i, t ⟨k, i⟩ = 1 := fun k => by simp [t]
    have hsplit : ∀ p, e p = (e p - t p) + t p := fun p => by
      obtain ⟨k, i⟩ := p
      by_cases h : i = c k
      · subst h
        have := hc k
        simp only [t, if_true]
        omega
      · simp [t, h]
    obtain ⟨M, hM, hMe⟩ := ih (fun p => e p - t p) fun k => by
      have h1 := he k
      rw [Finset.sum_congr rfl fun i _ => hsplit ⟨k, i⟩, Finset.sum_add_distrib, ht] at h1
      omega
    refine ⟨M * X ⟨(), c⟩, hM.mul (isHomogeneous_X _ _), ?_⟩
    rw [map_mul, hMe, segreSub_X]
    conv_rhs => rw [Finset.prod_congr rfl fun p _ => by rw [hsplit p]]
    simp_rw [pow_add, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp [t, pow_ite]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion repeatedly using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem exists_segre_form {f : MRing ι} {df : K → ℕ} (hf : IsMultiHomog f df) (c : (k : K) → ι k) :
    ∃ F : MvPolynomial (Ix ((k : K) → ι k)) ℤ, F.IsHomogeneous (∑ k, df k) ∧
      segreSub F = f * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ (∑ k', df k' - df k) := by
  classical
  have hle : ∀ k, df k ≤ ∑ k', df k' := fun k =>
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  have key : ∀ μ ∈ f.support, ∃ M : MvPolynomial (Ix ((k : K) → ι k)) ℤ,
      M.IsHomogeneous (∑ k, df k) ∧
        segreSub M = (∏ p, (X p : MRing ι) ^ μ p) * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ (∑ k', df k' - df k) := by
    intro μ hμ
    obtain ⟨M, hM, hMe⟩ := exists_segre_prod (∑ k, df k)
      (fun p => μ p + if p.2 = c p.1 then ∑ k', df k' - df p.1 else 0) fun k => by
        rw [Finset.sum_add_distrib, hf μ hμ k]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
        have := hle k
        omega
    refine ⟨M, hM, ?_⟩
    rw [hMe]
    simp_rw [pow_add, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp [pow_ite]
  choose! M hM hMe using key
  refine ⟨∑ μ ∈ f.support, C (f.coeff μ) * M μ,
    IsHomogeneous.sum _ _ _ fun μ hμ => (hM μ hμ).C_mul _, ?_⟩
  rw [map_sum]
  conv_rhs => rw [f.as_sum]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [map_mul, algHom_C, hMe μ hμ, monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp [mul_assoc]

end Blocks

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem aeval_aeval_eq {σ τ S : Type} [CommRing S] [Algebra ℚ S] (u : τ → S) (ℓ : σ → MvPolynomial τ ℚ)
    (G : MvPolynomial σ ℚ) : aeval u (aeval ℓ G) = aeval (fun j => aeval u (ℓ j)) G := by
  rw [← AlgHom.comp_apply, comp_aeval]

/- English proof (translation)
Proceed by induction. Treat this case separately. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Treat this case separately.

Treat this case separately. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem isIntegral_coneMap {J : Type} (x : J → Ω) (S : Subalgebra ℚ (Polynomial Ω))
    (hX : ∀ i, IsIntegral S (Polynomial.C (x i) * Polynomial.X)) (P : MvPolynomial J ℚ) :
    IsIntegral S (coneMap ℚ x P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [coneMap, aeval_C]
    rw [IsScalarTower.algebraMap_apply ℚ S (Polynomial Ω)]
    exact isIntegral_algebraMap
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | mul_X p i hp =>
    rw [map_mul]
    simpa [coneMap] using hp.mul (hX i)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Put the expressions in a common number system so they can be compared. Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem minpoly_coeff_zero_ne {S : Subalgebra ℚ (Polynomial Ω)} {α : Polynomial Ω} (hα : IsIntegral S α)
    (h0 : α ≠ 0) : (minpoly S α).coeff 0 ≠ 0 := by
  intro h
  have hX := Polynomial.X_mul_divX_add (minpoly S α)
  rw [h, map_zero, add_zero] at hX
  have hdeg := minpoly.natDegree_pos hα
  have hmon : (Polynomial.divX (minpoly S α)).Monic := by
    unfold Polynomial.Monic Polynomial.leadingCoeff
    rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one, Polynomial.coeff_divX, Nat.sub_add_cancel hdeg]
    exact minpoly.monic hα
  have hev : Polynomial.aeval α (Polynomial.divX (minpoly S α)) = 0 := by
    have := minpoly.aeval S α
    rw [← hX, map_mul, Polynomial.aeval_X] at this
    exact (mul_eq_zero.mp this).resolve_left h0
  have hmin := minpoly.min S α hmon hev
  rw [Polynomial.degree_eq_natDegree (minpoly.ne_zero hα), Polynomial.degree_eq_natDegree hmon.ne_zero,
    Polynomial.natDegree_divX_eq_natDegree_tsub_one] at hmin
  norm_cast at hmin
  omega

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_homogeneousComponent_ne_zero {σ : Type} {G : MvPolynomial σ ℚ} (hG : G ≠ 0) :
    ∃ d, homogeneousComponent d G ≠ 0 := by
  by_contra h
  push Not at h
  apply hG
  rw [← sum_homogeneousComponent G]
  exact Finset.sum_eq_zero fun d _ => h d

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Rewrite the conclusion using the stated equalities.

Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem key_relation {D : ℕ} (y : (Σ k, ι k) → Ω) (w : Fin (D + 1) → Ω)
    (ℓq : Fin (D + 1) → MvPolynomial (Ix ((k : K) → ι k)) ℚ) (hℓ : ∀ j, (ℓq j).IsHomogeneous 1)
    (hℓx : ∀ j, aeval (segreCoords y) (ℓq j) = w j) {P : MvPolynomial (Ix ((k : K) → ι k)) ℚ} {m : ℕ}
    (hP : P.IsHomogeneous m) (p : Polynomial (coneRing ℚ w))
    (hp : Polynomial.aeval (coneMap ℚ (segreCoords y) P) p = 0) (g : ℕ → MvPolynomial (Fin (D + 1)) ℚ)
    (hg : ∀ k, coneMap ℚ w (g k) = (p.coeff k : Polynomial Ω)) (N : ℕ) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) :
    ∑ k ∈ Finset.range (p.natDegree + 1), (if m * k ≤ N then
      aeval (segreCoords z) P ^ k * aeval (fun j => aeval (segreCoords z) (ℓq j))
        (homogeneousComponent (N - m * k) (g k)) else 0) = 0 := by
  set x := segreCoords y
  set Q : MvPolynomial (Ix ((k : K) → ι k)) ℚ := ∑ k ∈ Finset.range (p.natDegree + 1),
    (if m * k ≤ N then P ^ k * aeval ℓq (homogeneousComponent (N - m * k) (g k)) else 0) with hQdef
  have hQ : Q.IsHomogeneous N := by
    refine IsHomogeneous.sum _ _ _ fun k _ => ?_
    split_ifs with h
    · have := (hP.pow k).mul ((homogeneousComponent_isHomogeneous (N - m * k) (g k)).aeval ℓq hℓ)
      convert this using 1
      rw [one_mul]
      omega
    · exact isHomogeneous_zero _ _ _
  have hQx : aeval x Q = 0 := by
    have hc := congrArg (fun q => Polynomial.coeff q N) hp
    simp only [Polynomial.aeval_eq_sum_range, Polynomial.finsetSum_coeff, Polynomial.coeff_zero] at hc
    rw [← hc, hQdef, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [coneMap_of_isHomogeneous ℚ x hP, Algebra.smul_def]
    have hcoe : algebraMap (coneRing ℚ w) (Polynomial Ω) (p.coeff k) = coneMap ℚ w (g k) := (hg k).symm
    rw [hcoe, mul_pow, ← Polynomial.C_pow, ← pow_mul, ← mul_assoc, Polynomial.coeff_mul_X_pow']
    split_ifs with h
    · rw [Polynomial.coeff_mul_C, coeff_coneMap, map_mul, map_pow, aeval_aeval_eq]
      simp only [hℓx]
      ring
    · rw [map_zero]
  have h0 := aeval_segre_eq_zero y hQ hQx hz
  rw [hQdef, map_sum] at h0
  refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) h0
  split_ifs
  · rw [map_mul, map_pow, aeval_aeval_eq]
  · rw [map_zero]

end

end ProjAvoidingForm

end GroundTheory.Heights₂.Heights.HilbertSamuel
