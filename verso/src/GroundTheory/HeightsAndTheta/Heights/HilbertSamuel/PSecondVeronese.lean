import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSecondVeronese
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSecondVeroneseParts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Veronese

/- English proof (translation)
Establish `hm : ({i} + {j} : Multiset (Fin (D + 1))) = {k} + {l}`. Use `congrArg Finsupp.toMultiset h` as an intermediate fact. Simplify `this` using `only [map_add, Finsupp.toMultiset_single, one_nsmul]`. Establish `h1 : i = k ∨ i = l`. Establish `: i ∈ ({k} + {l} : Multiset (Fin (D + 1)))` using `hm ▸ Multiset.mem_add.2 (Or.inl (Multiset.mem_singleton_self i))`.

Simplify using `using this`. Establish `h2 : j = k ∨ j = l`. Establish `: j ∈ ({k} + {l} : Multiset (Fin (D + 1)))` using `hm ▸ Multiset.mem_add.2 (Or.inr (Multiset.mem_singleton_self j))`. Simplify using `using this`. Establish `h3 : k = i ∨ k = j`.

Establish `: k ∈ ({i} + {j} : Multiset (Fin (D + 1)))` using `hm.symm ▸ Multiset.mem_add.2 (Or.inl (Multiset.mem_singleton_self k))`. Simplify using `using this`. Establish `h4 : l = i ∨ l = j`. Establish `: l ∈ ({i} + {j} : Multiset (Fin (D + 1)))` using `hm.symm ▸ Multiset.mem_add.2 (Or.inr (Multiset.mem_singleton_self l))`. Simplify using `using this`.

Rewrite `hij`, `hkl` using `[Fin.le_iff_val_le_val]`. Simplify using `only [Fin.ext_iff] at h1 h2 h3 h4 ⊢`. Use linear arithmetic over natural numbers and integers.
-/
theorem pair_eq {D : ℕ} {i j k l : Fin (D + 1)} (hij : i ≤ j) (hkl : k ≤ l)
    (h : (Finsupp.single i 1 + Finsupp.single j 1 : Fin (D + 1) →₀ ℕ) = Finsupp.single k 1 + Finsupp.single l 1) :
    i = k ∧ j = l := by
  have hm : ({i} + {j} : Multiset (Fin (D + 1))) = {k} + {l} := by
    have := congrArg Finsupp.toMultiset h
    simpa only [map_add, Finsupp.toMultiset_single, one_nsmul] using this
  have h1 : i = k ∨ i = l := by
    have : i ∈ ({k} + {l} : Multiset (Fin (D + 1))) := hm ▸ Multiset.mem_add.2 (Or.inl (Multiset.mem_singleton_self i))
    simpa using this
  have h2 : j = k ∨ j = l := by
    have : j ∈ ({k} + {l} : Multiset (Fin (D + 1))) := hm ▸ Multiset.mem_add.2 (Or.inr (Multiset.mem_singleton_self j))
    simpa using this
  have h3 : k = i ∨ k = j := by
    have : k ∈ ({i} + {j} : Multiset (Fin (D + 1))) := hm.symm ▸ Multiset.mem_add.2 (Or.inl (Multiset.mem_singleton_self k))
    simpa using this
  have h4 : l = i ∨ l = j := by
    have : l ∈ ({i} + {j} : Multiset (Fin (D + 1))) := hm.symm ▸ Multiset.mem_add.2 (Or.inr (Multiset.mem_singleton_self l))
    simpa using this
  rw [Fin.le_iff_val_le_val] at hij hkl
  simp only [Fin.ext_iff] at h1 h2 h3 h4 ⊢
  omega

/- English proof (translation)
Introduce `q q' h`. Take `⟨u, ⟨⟨i, j⟩, hij⟩⟩` from `q`. Take `⟨u', ⟨⟨k, l⟩, hkl⟩⟩` from `q'`. Take `⟨rfl, rfl⟩` from `pair_eq hij hkl h`. Consider the cases of `u`.

Consider the cases of `u'`. Both sides reduce to the same expression.
-/
theorem exponent_injective (D : ℕ) :
    Function.Injective fun q : Ix (Idx D) =>
      (Finsupp.single q.2.1.1 1 + Finsupp.single q.2.1.2 1 : Fin (D + 1) →₀ ℕ) := by
  intro q q' h
  obtain ⟨u, ⟨⟨i, j⟩, hij⟩⟩ := q
  obtain ⟨u', ⟨⟨k, l⟩, hkl⟩⟩ := q'
  obtain ⟨rfl, rfl⟩ := pair_eq hij hkl h
  cases u
  cases u'
  rfl

def polyMap (D : ℕ) : MvPolynomial (Fin (D + 1)) ℤ →+* Fld D :=
  (algebraMap (MvPolynomial (Fin (D + 1)) ℚ) (Fld D)).comp (MvPolynomial.map (Int.castRingHom ℚ))

/- English proof (translation)
The claim follows from `(IsFractionRing.injective (MvPolynomial (Fin (D + 1)) ℚ) (Fld D)).comp (MvPolynomial.map_injective _ (RingHom.injective_int (Int.castRingHom ℚ)))`.
-/
theorem polyMap_injective (D : ℕ) : Function.Injective (polyMap D) :=
  (IsFractionRing.injective (MvPolynomial (Fin (D + 1)) ℚ) (Fld D)).comp
    (MvPolynomial.map_injective _ (RingHom.injective_int (Int.castRingHom ℚ)))

/- English proof (translation)
Establish `hmono : LinearIndependent ℤ fun q : Ix (Idx D) => (X q.2.1.1 * X q.2.1.2 : MvPolynomial (Fin (D + 1)) ℤ)`. Establish `h` using `(basisMonomials (Fin (D + 1)) ℤ).linearIndependent.comp _ (exponent_injective D)`. Establish `e : (fun q : Ix (Idx D) => (X q.2.1.1 * X q.2.1.2 : MvPolynomial (Fin (D + 1)) ℤ)) = ⇑(basisMonomials (Fin (D + 1)) ℤ) ∘ fun q : Ix (Idx D) => (Finsupp.single q.2.1.1 1 + Finsupp.single q.2.1.2 1 : Fin (D + 1) →₀ ℕ)`. Use function extensionality and compare the values at `q`. Simplify using `only [Function.comp_apply, coe_basisMonomials, X, monomial_mul, mul_one]`.

Rewrite using `[e]`. Conclude with `h`. Establish `h2` using `hmono.map' (polyMap D).toAddMonoidHom.toIntLinearMap (LinearMap.ker_eq_bot.mpr (polyMap_injective D))`. Establish `e2 : x D = ⇑(polyMap D).toAddMonoidHom.toIntLinearMap ∘ fun q : Ix (Idx D) => (X q.2.1.1 * X q.2.1.2 : MvPolynomial (Fin (D + 1)) ℤ)`. Use function extensionality and compare the values at `q`.

Simplify using `[x, t, polyMap, map_mul]`. Rewrite using `[e2]`. Conclude with `h2`.
-/
theorem x_linearIndependent (D : ℕ) : LinearIndependent ℤ (x D) := by
  have hmono : LinearIndependent ℤ fun q : Ix (Idx D) =>
      (X q.2.1.1 * X q.2.1.2 : MvPolynomial (Fin (D + 1)) ℤ) := by
    have h := (basisMonomials (Fin (D + 1)) ℤ).linearIndependent.comp _ (exponent_injective D)
    have e : (fun q : Ix (Idx D) => (X q.2.1.1 * X q.2.1.2 : MvPolynomial (Fin (D + 1)) ℤ)) =
        ⇑(basisMonomials (Fin (D + 1)) ℤ) ∘ fun q : Ix (Idx D) =>
          (Finsupp.single q.2.1.1 1 + Finsupp.single q.2.1.2 1 : Fin (D + 1) →₀ ℕ) := by
      funext q
      simp only [Function.comp_apply, coe_basisMonomials, X, monomial_mul, mul_one]
    rw [e]
    exact h
  have h2 := hmono.map' (polyMap D).toAddMonoidHom.toIntLinearMap
    (LinearMap.ker_eq_bot.mpr (polyMap_injective D))
  have e2 : x D = ⇑(polyMap D).toAddMonoidHom.toIntLinearMap ∘ fun q : Ix (Idx D) =>
      (X q.2.1.1 * X q.2.1.2 : MvPolynomial (Fin (D + 1)) ℤ) := by
    funext q
    simp [x, t, polyMap, map_mul]
  rw [e2]
  exact h2

/- English proof (translation)
Establish `hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (scale D)` using `contDiff_pi.2 fun q => contDiff_const.mul (contDiff_apply ℝ ℂ q)`. Conclude with `(ProjLine.isSmoothMetric_fs (J := Ix (Idx D))).comp hs.contDiffOn fun z hz => scale_ne_zero hz`.
-/
theorem isSmoothMetric_metric (D : ℕ) : IsSmoothMetric (metric D) := by
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (scale D) :=
    contDiff_pi.2 fun q => contDiff_const.mul (contDiff_apply ℝ ℂ q)
  exact (ProjLine.isSmoothMetric_fs (J := Ix (Idx D))).comp hs.contDiffOn fun z hz => scale_ne_zero hz

/- English proof (translation)
Introduce `z`. Establish `h : scale D (fun q => conj (z q)) = fun q => conj (scale D z q)`. Use function extensionality and compare the values at `q`. Simplify using `[scale, map_mul, Complex.conj_ofReal]`. Use `show (fsMetric (Ix (Idx D))).ρ (scale D _) = (fsMetric (Ix (Idx D))).ρ (scale D z)`.

Rewrite using `[h]`. Conclude with `ProjLine.isConjInvariant_fs (scale D z)`.
-/
theorem isConjInvariant_metric (D : ℕ) : IsConjInvariant (metric D) := by
  intro z
  have h : scale D (fun q => conj (z q)) = fun q => conj (scale D z q) := by
    funext q
    simp [scale, map_mul, Complex.conj_ofReal]
  show (fsMetric (Ix (Idx D))).ρ (scale D _) = (fsMetric (Ix (Idx D))).ρ (scale D z)
  rw [h]
  exact ProjLine.isConjInvariant_fs (scale D z)

/- English proof (translation)
Rewrite using `[eval_eq, eval_eq, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Establish `hdeg : d.degree = n`. Assume the negation of the conclusion as `h`. Conclude with `(mem_support_iff.mp hd) (hφ.coeff_eq_zero h)`.

Simplify using `only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]`. Establish `hs : d.degree = ∑ i ∈ d.support, d i` using `rfl`. Rewrite using `[← hdeg, hs]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eval_smul_homog {ι : Type*} {φ : MvPolynomial ι ℂ} {n : ℕ} (hφ : φ.IsHomogeneous n) (c : ℂ)
    (z : ι → ℂ) : eval (c • z) φ = c ^ n * eval z φ := by
  classical
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : d.degree = n := by
    by_contra h
    exact (mem_support_iff.mp hd) (hφ.coeff_eq_zero h)
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hs : d.degree = ∑ i ∈ d.support, d i := rfl
  rw [← hdeg, hs]
  ring

/- English proof (translation)
Take `⟨f, hf, rfl⟩` from `hb`. Take `⟨f', hf', rfl⟩` from `hb'`. Unfold `pairVal`. Rewrite using `[eval_smul_homog ((hf.map _).map _), eval_smul_homog ((hf'.map _).map _), (metric D).smul]`. Establish `key : c ^ n * conj (c ^ n) = (((‖c‖ ^ (2 * n) : ℝ)) : ℂ)`.

Rewrite using `[map_pow, ← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hK : (((‖c‖ ^ (2 * n) : ℝ)) : ℂ) ≠ 0`. Establish `: (0 : ℝ) < ‖c‖` using `norm_pos_iff.mpr hc`.

Conclude with `(pow_pos this _).ne'` after adjusting the coercions. Establish `hL : ∀ A B : ℂ, A * c ^ n * conj (B * c ^ n) = (((‖c‖ ^ (2 * n) : ℝ)) : ℂ) * (A * conj B)`. Introduce `A B`. Rewrite using `[← key, map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[mul_comm (c ^ n), mul_comm (c ^ n), hL, mul_pow]`. Use `push_cast`. Conclude with `mul_div_mul_left _ _ (by exact_mod_cast hK)`.
-/
theorem pairVal_smul {D n : ℕ} {b b' : MvPolynomial (Ix (Idx D)) ℚ}
    (hb : ∃ f : MvPolynomial (Ix (Idx D)) ℤ, f.IsHomogeneous n ∧ b = MvPolynomial.map (Int.castRingHom ℚ) f)
    (hb' : ∃ f : MvPolynomial (Ix (Idx D)) ℤ, f.IsHomogeneous n ∧ b' = MvPolynomial.map (Int.castRingHom ℚ) f)
    (c : ℂ) (z : Ix (Idx D) → ℂ) (hc : c ≠ 0) :
    pairVal (metric D) n b b' (c • z) = pairVal (metric D) n b b' z := by
  obtain ⟨f, hf, rfl⟩ := hb
  obtain ⟨f', hf', rfl⟩ := hb'
  unfold pairVal
  rw [eval_smul_homog ((hf.map _).map _), eval_smul_homog ((hf'.map _).map _), (metric D).smul]
  have key : c ^ n * conj (c ^ n) = (((‖c‖ ^ (2 * n) : ℝ)) : ℂ) := by
    rw [map_pow, ← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hK : (((‖c‖ ^ (2 * n) : ℝ)) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < ‖c‖ := norm_pos_iff.mpr hc
    exact_mod_cast (pow_pos this _).ne'
  have hL : ∀ A B : ℂ, A * c ^ n * conj (B * c ^ n) = (((‖c‖ ^ (2 * n) : ℝ)) : ℂ) * (A * conj B) := by
    intro A B
    rw [← key, map_mul]
    ring
  rw [mul_comm (c ^ n), mul_comm (c ^ n), hL, mul_pow]
  push_cast
  exact mul_div_mul_left _ _ (by exact_mod_cast hK)

end Veronese

open Veronese

/- English proof (translation)
Introduce `D hD`. Take `⟨J, R, meas, borel, dV, hvol, htr⟩` from `hR D hD`. Set `d : HSMDatum D (Fld D) (Idx D)` to `{ x := x D, m := metric D, P0 := ⊥, J := J, R := R, meas := meas, borel := borel, dV := dV, one_le := hD, arith := hA D hD, indep := x_linearIndependent D, smooth := isSmoothMetric_metric D, conjInv := isConjInvariant_metric D, normalForm_baseLattice_le_dualSpan_sup_line := bot_l …`. Use `⟨Fld D, inferInstance, inferInstance, Idx D, inferInstance, d, fun n => ?_, fun I hI => hT D hD I hI, hG D hD⟩` and prove the remaining obligations. Establish `hgram : ∀ {r : ℕ} (b : Fin r → MvPolynomial (Ix (Idx D)) ℚ), (∀ k, ∃ f : MvPolynomial (Ix (Idx D)) ℤ, f.IsHomogeneous n ∧ b k = MvPolynomial.map (Int.castRingHom ℚ) f) → resGram d n b = gram D n b`.

Introduce `r b hb`. Use extensionality with `k l`. Establish `e1` using `htr (fun z => pairVal (metric D) n (b k) (b l) z) (fun c z hc => pairVal_smul (hb k) (hb l) c z hc)`. Establish `e2` using `htr (fun z => pairVal (metric D) n (b k) (b l) (conjPt z)) fun c z hc => by`. Establish `: conjPt (c • z) = conj c • conjPt z`.

Use function extensionality and compare the values at `q`. Simplify using `[conjPt]`. Simplify using `only [this]`. Conclude with `pairVal_smul (hb k) (hb l) _ _ ((map_ne_zero _).mpr hc)`. Unfold `resGram gram resPt`.

Rewrite using `[e1, e2]`. Rewrite using `[← hC D hD n]`. Unfold `resChi Veronese.chi`. Use `split_ifs with h1`. Rewrite using `[hgram _ h1.choose_spec.1]`.

Both sides reduce to the same expression.
-/
theorem SecondVeronese.proof (hA : VeroneseArith.Statement) (hS : VeroneseSemipos.Statement)
    (hR : VeroneseResolution.Statement) (hC : VeroneseChi.Statement) (hT : VeroneseTop.Statement)
    (hG : VeroneseGenDeg.Statement) : SecondVeronese.Statement := by
  intro D hD
  obtain ⟨J, R, meas, borel, dV, hvol, htr⟩ := hR D hD
  let d : HSMDatum D (Fld D) (Idx D) :=
    { x := x D, m := metric D, P0 := ⊥, J := J, R := R, meas := meas, borel := borel, dV := dV,
      one_le := hD, arith := hA D hD, indep := x_linearIndependent D, smooth := isSmoothMetric_metric D,
      conjInv := isConjInvariant_metric D, normalForm_baseLattice_le_dualSpan_sup_line := bot_le, semipos := hS D, vol := hvol }
  refine ⟨Fld D, inferInstance, inferInstance, Idx D, inferInstance, d, fun n => ?_,
    fun I hI => hT D hD I hI, hG D hD⟩

  have hgram : ∀ {r : ℕ} (b : Fin r → MvPolynomial (Ix (Idx D)) ℚ),
      (∀ k, ∃ f : MvPolynomial (Ix (Idx D)) ℤ, f.IsHomogeneous n ∧ b k = MvPolynomial.map (Int.castRingHom ℚ) f) →
      resGram d n b = gram D n b := by
    intro r b hb
    ext k l
    have e1 := htr (fun z => pairVal (metric D) n (b k) (b l) z)
      (fun c z hc => pairVal_smul (hb k) (hb l) c z hc)
    have e2 := htr (fun z => pairVal (metric D) n (b k) (b l) (conjPt z)) fun c z hc => by
      have : conjPt (c • z) = conj c • conjPt z := by
        funext q
        simp [conjPt]
      simp only [this]
      exact pairVal_smul (hb k) (hb l) _ _ ((map_ne_zero _).mpr hc)
    unfold resGram gram resPt
    rw [e1, e2]
  rw [← hC D hD n]
  unfold resChi Veronese.chi
  split_ifs with h1
  · rw [hgram _ h1.choose_spec.1]
  · rfl

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
