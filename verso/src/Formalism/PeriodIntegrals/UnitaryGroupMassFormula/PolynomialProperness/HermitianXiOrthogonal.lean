import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.TauDefs
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFlagVector
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GNonneg

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

noncomputable section

namespace PI.PolynomialProperness.TauN

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `j _`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma vmv_mulVec {n : ℕ} (x y u : Fin n → ℂ) : vecMulVec x y *ᵥ u = (y ⬝ᵥ u) • x := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, Finset.mul_sum, mul_assoc]`.
-/
lemma smul_mv {n : ℕ} (a : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    (a • M) *ᵥ v = a • (M *ᵥ v) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Unfold `herm`. Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, GBasic.Hpk_herm]`.
-/
lemma star_H_dot (k r : ℕ) (w u : Fin (2 * r + k + 1) → ℂ) :
    star (Hpk k r *ᵥ w) ⬝ᵥ u = herm (Hpk k r) u w := by
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, GBasic.Hpk_herm]

/- English proof (translation)
Simplify using `only [nEich, Matrix.add_mulVec, Matrix.one_mulVec, smul_mv, Matrix.neg_mulVec, vmv_mulVec, star_H_dot, smul_smul]`.
-/
lemma nEich_mulVec (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (ξ : Fin r → ℂ)
    (u : Fin (2 * r + k + 1) → ℂ) :
    nEich k r z ξ *ᵥ u = u + ((1 : ℂ) / ((Tz k r z : ℝ) : ℂ)) •
      (-(herm (Hpk k r) u z • xiV k r ξ) + herm (Hpk k r) u (xiV k r ξ) • z +
        ((1 / 2 : ℂ) * herm (Hpk k r) u (xiV k r ξ)) • xiV k r ξ) := by
  simp only [nEich, Matrix.add_mulVec, Matrix.one_mulVec, smul_mv, Matrix.neg_mulVec, vmv_mulVec, star_H_dot,
    smul_smul]

/- English proof (translation)
Unfold `herm`. Simplify using `only [dotProduct]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `i _`. Distinguish the cases in `hi : i.val < r`.

Establish `hsig : r + k < (GBasic.sig k r i).val`. Unfold `GBasic.sig`. Rewrite using `[if_pos (Or.inl hi)]`. Use `show r + k < 2 * r + k - i.val`. Use linear arithmetic over natural numbers and integers.

Establish `hz : (Hpk k r *ᵥ y) i = 0`. Simplify using `only [Matrix.mulVec, dotProduct, GBasic.Hpk_eq, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, hy _ hsig, mul_zero]`. Rewrite using `[hz, mul_zero]`. Establish `hx : xiV k r p i = 0`. Unfold `xiV`.

Rewrite using `[dif_neg hi]`. Rewrite using `[Pi.star_apply, hx, star_zero, zero_mul]`.
-/
lemma herm_xi_zero (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ)
    (hy : ∀ i : Fin (2 * r + k + 1), r + k < i.val → y i = 0) (p : Fin r → ℂ) :
    herm (Hpk k r) y (xiV k r p) = 0 := by
  unfold herm
  simp only [dotProduct]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i.val < r
  · have hsig : r + k < (GBasic.sig k r i).val := by
      unfold GBasic.sig
      rw [if_pos (Or.inl hi)]
      show r + k < 2 * r + k - i.val
      omega
    have hz : (Hpk k r *ᵥ y) i = 0 := by
      simp only [Matrix.mulVec, dotProduct, GBasic.Hpk_eq, ite_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, hy _ hsig, mul_zero]
    rw [hz, mul_zero]
  · have hx : xiV k r p i = 0 := by
      unfold xiV
      rw [dif_neg hi]
    rw [Pi.star_apply, hx, star_zero, zero_mul]

/- English proof (translation)
Unfold `xiV`. Rewrite using `[dif_neg (show ¬ (i.val < r) by omega)]`.
-/
lemma xiV_hi (k r : ℕ) (p : Fin r → ℂ) (i : Fin (2 * r + k + 1)) (hi : r ≤ i.val) : xiV k r p i = 0 := by
  unfold xiV
  rw [dif_neg (show ¬ (i.val < r) by omega)]

/- English proof (translation)
Unfold `herm`. Simplify using `only [dotProduct]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `i _`. Distinguish the cases in `h : i.val < r ∨ r + k < i.val`.

Rewrite using `[Pi.star_apply, hz i h, star_zero, zero_mul]`. Establish `hs : GBasic.sig k r i = i`. Unfold `GBasic.sig`. Rewrite using `[if_neg h]`. Establish `hx : (Hpk k r *ᵥ xiV k r p) i = 0`.

Simplify using `only [Matrix.mulVec, dotProduct, GBasic.Hpk_eq, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, hs, xiV_hi k r p i (by omega), mul_zero]`. Rewrite using `[hx, mul_zero]`.
-/
lemma hermitian_xi_orthogonal (k r : ℕ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (p : Fin r → ℂ) :
    herm (Hpk k r) (xiV k r p) z = 0 := by
  unfold herm
  simp only [dotProduct]
  apply Finset.sum_eq_zero
  intro i _
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [Pi.star_apply, hz i h, star_zero, zero_mul]
  · have hs : GBasic.sig k r i = i := by
      unfold GBasic.sig
      rw [if_neg h]
    have hx : (Hpk k r *ᵥ xiV k r p) i = 0 := by
      simp only [Matrix.mulVec, dotProduct, GBasic.Hpk_eq, ite_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, hs, xiV_hi k r p i (by omega), mul_zero]
    rw [hx, mul_zero]

/- English proof (translation)
Conclude with `Complex.ofReal_ne_zero.mpr hz.2.ne'`.
-/
lemma T_ne {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : StdZ k r z) : ((Tz k r z : ℝ) : ℂ) ≠ 0 := by
  exact Complex.ofReal_ne_zero.mpr hz.2.ne'

/- English proof (translation)
Rewrite using `[nEich_mulVec, Formalism.FourierDecayAlt.P.B2x4.herm_smul_right]`. Establish `hc : star ((1 : ℂ) / ((Tz k r z : ℝ) : ℂ)) = (1 : ℂ) / ((Tz k r z : ℝ) : ℂ)`. Simplify using `[Complex.star_def]`. Rewrite using `[hc]`. Use function extensionality and compare the values at `i`.

Simplify using `only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma nEich_heis {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : StdZ k r z) (ξ : Fin r → ℂ)
    (u : Fin (2 * r + k + 1) → ℂ) :
    nEich k r z ξ *ᵥ u = u - herm (Hpk k r) u (((1 : ℂ) / ((Tz k r z : ℝ) : ℂ)) • z) • xiV k r ξ +
      herm (Hpk k r) u (xiV k r ξ) • (((1 : ℂ) / ((Tz k r z : ℝ) : ℂ)) • z +
        ((1 : ℂ) / (2 * ((Tz k r z : ℝ) : ℂ))) • xiV k r ξ) := by
  rw [nEich_mulVec, Formalism.FourierDecayAlt.P.B2x4.herm_smul_right]
  have hc : star ((1 : ℂ) / ((Tz k r z : ℝ) : ℂ)) = (1 : ℂ) / ((Tz k r z : ℝ) : ℂ) := by
    simp [Complex.star_def]
  rw [hc]
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Introduce `k r z hz ξ`. Establish `hT` using `T_ne hz`. Establish `hH` using `GBasic.Hpk_herm k r`. Establish `hc : star ((1 : ℂ) / ((Tz k r z : ℝ) : ℂ)) = (1 : ℂ) / ((Tz k r z : ℝ) : ℂ)`. Simplify using `[Complex.star_def]`.

Establish `h2 : star ((1 : ℂ) / 2) = (1 : ℂ) / 2`. Simplify using `[Complex.star_def]`. Establish `hzW : ∀ i : Fin (2 * r + k + 1), r + k < i.val → z i = 0` using `fun i hi => hz.1 i (Or.inr hi)`. Establish `hξW : ∀ i : Fin (2 * r + k + 1), r + k < i.val → xiV k r ξ i = 0` using `fun i hi => xiV_hi k r ξ i (by omega)`. Establish `hξξ : herm (Hpk k r) (xiV k r ξ) (xiV k r ξ) = 0` using `herm_xi_zero k r _ hξW ξ`.

Establish `hξz : herm (Hpk k r) (xiV k r ξ) z = 0` using `hermitian_xi_orthogonal k r hz.1 ξ`. Establish `hzξ : herm (Hpk k r) z (xiV k r ξ) = 0` using `herm_xi_zero k r z hzW ξ`. Establish `hzz : herm (Hpk k r) z z = -((Tz k r z : ℝ) : ℂ)`. Establish `hs` using `Formalism.FourierDecayAlt.P.B2x4.herm_symm (Hpk k r) hH z z`. Apply `Complex.ext` to reduce the goal to its premises.

Simplify using `[Tz]`. Establish `him` using `congrArg Complex.im hs`. Simplify using `only [Complex.star_def, Complex.conj_im] at him`. Rewrite using `[Complex.neg_im, Complex.ofReal_im, neg_zero]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hn : ∀ u, nEich k r z ξ *ᵥ u = u + (-((1 : ℂ) / ((Tz k r z : ℝ) : ℂ) * herm (Hpk k r) u z) + (1 : ℂ) / ((Tz k r z : ℝ) : ℂ) * ((1 : ℂ) / 2) * herm (Hpk k r) u (xiV k r ξ)) • xiV k r ξ + ((1 : ℂ) / ((Tz k r z : ℝ) : ℂ) * herm (Hpk k r) u (xiV k r ξ)) • z`. Introduce `u`. Rewrite using `[nEich_mulVec]`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hfix : ∀ p : Fin r → ℂ, nEich k r z ξ *ᵥ xiV k r p = xiV k r p`. Introduce `p`. Rewrite using `[nEich_mulVec, hermitian_xi_orthogonal k r hz.1 p, herm_xi_zero k r _ (fun i hi => xiV_hi k r p i (by omega)) ξ]`. Simplify using the standard rewrite rules.

Apply the tactic sequence `have hentry : ∀ (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1)), M i j = (M *ᵥ Pi.single j 1) i := by`. Introduce `M i j`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`. Establish `hxe : ∀ a : Fin r, xiV k r (Pi.single a 1) = Pi.single (eI k r a) 1`. Introduce `a`.

Use function extensionality and compare the values at `l`. Unfold `xiV`. Distinguish the cases in `hl : l.val < r`. Rewrite using `[dif_pos hl]`. Distinguish the cases in `h : l = eI k r a`.

Establish `e : (⟨l.val, hl⟩ : Fin r) = a` using `Fin.ext (by show l.val = a.val; rw [h]; rfl)`. Rewrite using `[e, h, Pi.single_eq_same, Pi.single_eq_same]`. Establish `e : (⟨l.val, hl⟩ : Fin r) ≠ a` using `fun e => h (Fin.ext (by show l.val = a.val; rw [← e]))`. Rewrite using `[Pi.single_eq_of_ne e, Pi.single_eq_of_ne h]`. Establish `h' : l ≠ eI k r a`.

Introduce `h`. Apply `hl` to reduce the goal to its premises. Rewrite using `[h]`. Conclude with `a.isLt`. Rewrite using `[dif_neg hl, Pi.single_eq_of_ne h']`.

Use `⟨?_, hfix, ?_⟩` and prove the remaining obligations. Simplify using `only [Nset, Set.mem_setOf_eq]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Apply `Formalism.FourierDecayAlt.P.TwoByOneBlock.mem_UH_of_herm` to reduce the goal to its premises. Introduce `u v`.

Establish `hξv : herm (Hpk k r) (xiV k r ξ) v = star (herm (Hpk k r) v (xiV k r ξ))` using `(Formalism.FourierDecayAlt.P.B2x4.herm_symm (Hpk k r) hH v (xiV k r ξ)).symm`. Establish `hzv : herm (Hpk k r) z v = star (herm (Hpk k r) v z)` using `(Formalism.FourierDecayAlt.P.B2x4.herm_symm (Hpk k r) hH v z).symm`. Rewrite using `[hn u, hn v]`. Simplify using `only [Formalism.FourierDecayAlt.P.B2x4.herm_add_left, Formalism.FourierDecayAlt.P.B2x4.herm_add_right, Formalism.FourierDecayAlt.P.B2x4.herm_smul_left, Formalism.FourierDecayAlt.P.B2x4.herm_smul_right, hξξ, hξz, hzξ, hzz, hξv, hzv, star_add, star_neg, star_mul', hc, h2]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Introduce `a i _`. Apply the tactic sequence `rw [hentry (nEich k r z ξ) i (eI k r a), ← hxe, hfix, hxe, Pi.single_apply]`. Introduce `i j hj1 hj2 hi`. Apply the tactic sequence `rw [hentry (nEich k r z ξ) i j, hn]`.

Establish `h0 : herm (Hpk k r) (Pi.single j 1 : Fin (2 * r + k + 1) → ℂ) (xiV k r ξ) = 0` using `herm_xi_zero k r _ (fun l hl => by`. Rewrite using `[Pi.single_eq_of_ne]`. Introduce `e`. Rewrite `hl` using `[e]`. Use the proof step `omega) ξ`.

Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h0, mul_zero, zero_mul, add_zero, xiV_hi k r ξ i hi, Pi.single_apply]`. Rewrite using `[nEich_mulVec, hzz, hzξ]`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem neFacts : NEFacts := by
  intro k r z hz ξ
  have hT := T_ne hz
  have hH := GBasic.Hpk_herm k r
  have hc : star ((1 : ℂ) / ((Tz k r z : ℝ) : ℂ)) = (1 : ℂ) / ((Tz k r z : ℝ) : ℂ) := by
    simp [Complex.star_def]
  have h2 : star ((1 : ℂ) / 2) = (1 : ℂ) / 2 := by
    simp [Complex.star_def]
  have hzW : ∀ i : Fin (2 * r + k + 1), r + k < i.val → z i = 0 := fun i hi => hz.1 i (Or.inr hi)
  have hξW : ∀ i : Fin (2 * r + k + 1), r + k < i.val → xiV k r ξ i = 0 :=
    fun i hi => xiV_hi k r ξ i (by omega)
  have hξξ : herm (Hpk k r) (xiV k r ξ) (xiV k r ξ) = 0 := herm_xi_zero k r _ hξW ξ
  have hξz : herm (Hpk k r) (xiV k r ξ) z = 0 := hermitian_xi_orthogonal k r hz.1 ξ
  have hzξ : herm (Hpk k r) z (xiV k r ξ) = 0 := herm_xi_zero k r z hzW ξ
  have hzz : herm (Hpk k r) z z = -((Tz k r z : ℝ) : ℂ) := by
    have hs := Formalism.FourierDecayAlt.P.B2x4.herm_symm (Hpk k r) hH z z
    apply Complex.ext
    · simp [Tz]
    · have him := congrArg Complex.im hs
      simp only [Complex.star_def, Complex.conj_im] at him
      rw [Complex.neg_im, Complex.ofReal_im, neg_zero]
      linarith
  have hn : ∀ u, nEich k r z ξ *ᵥ u = u +
      (-((1 : ℂ) / ((Tz k r z : ℝ) : ℂ) * herm (Hpk k r) u z) +
        (1 : ℂ) / ((Tz k r z : ℝ) : ℂ) * ((1 : ℂ) / 2) * herm (Hpk k r) u (xiV k r ξ)) • xiV k r ξ +
      ((1 : ℂ) / ((Tz k r z : ℝ) : ℂ) * herm (Hpk k r) u (xiV k r ξ)) • z := by
    intro u
    rw [nEich_mulVec]
    funext i
    simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hfix : ∀ p : Fin r → ℂ, nEich k r z ξ *ᵥ xiV k r p = xiV k r p := by
    intro p
    rw [nEich_mulVec, hermitian_xi_orthogonal k r hz.1 p, herm_xi_zero k r _ (fun i hi => xiV_hi k r p i (by omega)) ξ]
    simp
  have hentry : ∀ (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1)),
      M i j = (M *ᵥ Pi.single j 1) i := by
    intro M i j
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hxe : ∀ a : Fin r, xiV k r (Pi.single a 1) = Pi.single (eI k r a) 1 := by
    intro a
    funext l
    unfold xiV
    by_cases hl : l.val < r
    · rw [dif_pos hl]
      by_cases h : l = eI k r a
      · have e : (⟨l.val, hl⟩ : Fin r) = a := Fin.ext (by show l.val = a.val; rw [h]; rfl)
        rw [e, h, Pi.single_eq_same, Pi.single_eq_same]
      · have e : (⟨l.val, hl⟩ : Fin r) ≠ a := fun e => h (Fin.ext (by show l.val = a.val; rw [← e]))
        rw [Pi.single_eq_of_ne e, Pi.single_eq_of_ne h]
    · have h' : l ≠ eI k r a := by
        intro h
        apply hl
        rw [h]
        exact a.isLt
      rw [dif_neg hl, Pi.single_eq_of_ne h']
  refine ⟨?_, hfix, ?_⟩
  · simp only [Nset, Set.mem_setOf_eq]
    refine ⟨?_, ?_, ?_⟩
    · apply Formalism.FourierDecayAlt.P.TwoByOneBlock.mem_UH_of_herm
      intro u v
      have hξv : herm (Hpk k r) (xiV k r ξ) v = star (herm (Hpk k r) v (xiV k r ξ)) :=
        (Formalism.FourierDecayAlt.P.B2x4.herm_symm (Hpk k r) hH v (xiV k r ξ)).symm
      have hzv : herm (Hpk k r) z v = star (herm (Hpk k r) v z) :=
        (Formalism.FourierDecayAlt.P.B2x4.herm_symm (Hpk k r) hH v z).symm
      rw [hn u, hn v]
      simp only [Formalism.FourierDecayAlt.P.B2x4.herm_add_left, Formalism.FourierDecayAlt.P.B2x4.herm_add_right,
        Formalism.FourierDecayAlt.P.B2x4.herm_smul_left, Formalism.FourierDecayAlt.P.B2x4.herm_smul_right, hξξ, hξz, hzξ, hzz, hξv, hzv,
        star_add, star_neg, star_mul', hc, h2]
      field_simp
      ring
    · intro a i _
      rw [hentry (nEich k r z ξ) i (eI k r a), ← hxe, hfix, hxe, Pi.single_apply]
    · intro i j hj1 hj2 hi
      rw [hentry (nEich k r z ξ) i j, hn]
      have h0 : herm (Hpk k r) (Pi.single j 1 : Fin (2 * r + k + 1) → ℂ) (xiV k r ξ) = 0 :=
        herm_xi_zero k r _ (fun l hl => by
          rw [Pi.single_eq_of_ne]
          intro e
          rw [e] at hl
          omega) ξ
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h0, mul_zero, zero_mul, add_zero,
        xiV_hi k r ξ i hi, Pi.single_apply]
  · rw [nEich_mulVec, hzz, hzξ]
    funext i
    simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring

end PI.PolynomialProperness.TauN
