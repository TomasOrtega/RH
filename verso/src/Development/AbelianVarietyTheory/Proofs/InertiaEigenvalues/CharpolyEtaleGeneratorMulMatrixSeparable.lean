import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MulMatMemUnitaryGroup
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.Et.CharpolySep

/- English proof (translation)
Introduce `x hx`. Take `⟨h, hh⟩` from `hx`. Establish `hint : IsIntegral F τ` using `Algebra.IsIntegral.isIntegral τ`. Establish `hm0 : minpoly F τ ≠ 0` using `minpoly.ne_zero hint`. Establish `hs : Polynomial.aeval τ (x * h) = 0`.

Apply `IsReduced.eq_zero` to reduce the goal to its premises. Use `⟨2, ?_⟩` and prove the remaining obligations. Establish `: (x * h) ^ 2 = minpoly F τ * h` using `by rw [hh]; ring`. Rewrite using `[← map_pow, this, map_mul, minpoly.aeval, zero_mul]`. Establish `hd : minpoly F τ ∣ x * h` using `minpoly.dvd F τ hs`.

Rewrite `hd` using `[hh]`. Establish `hxh : x * h ≠ 0`. Introduce `h0`. Apply `hm0` to reduce the goal to its premises. Rewrite using `[hh, mul_assoc, h0, mul_zero]`.

Establish `h2 : x * (x * h) ∣ 1 * (x * h)` using `by rw [one_mul, ← mul_assoc]; exact hd`. Conclude with `isUnit_of_dvd_one ((mul_dvd_mul_iff_right hxh).1 h2)`.
-/
theorem squarefree_minpoly {F K : Type} [Field F] [CommRing K] [Algebra F K] [IsReduced K] [Module.Finite F K]
    (τ : K) : Squarefree (minpoly F τ) := by
  intro x hx
  obtain ⟨h, hh⟩ := hx
  have hint : IsIntegral F τ := Algebra.IsIntegral.isIntegral τ
  have hm0 : minpoly F τ ≠ 0 := minpoly.ne_zero hint
  have hs : Polynomial.aeval τ (x * h) = 0 := by
    apply IsReduced.eq_zero
    refine ⟨2, ?_⟩
    have : (x * h) ^ 2 = minpoly F τ * h := by rw [hh]; ring
    rw [← map_pow, this, map_mul, minpoly.aeval, zero_mul]
  have hd : minpoly F τ ∣ x * h := minpoly.dvd F τ hs
  rw [hh] at hd
  have hxh : x * h ≠ 0 := by
    intro h0; apply hm0; rw [hh, mul_assoc, h0, mul_zero]
  have h2 : x * (x * h) ∣ 1 * (x * h) := by rw [one_mul, ← mul_assoc]; exact hd
  exact isUnit_of_dvd_one ((mul_dvd_mul_iff_right hxh).1 h2)

/- English proof (translation)
Establish `hint : IsIntegral F τ` using `Algebra.IsIntegral.isIntegral τ`. Establish `hmon` using `minpoly.monic hint`. Establish `hcm` using `LinearMap.charpoly_monic (Algebra.lmul F K τ)`. Establish `hcd : (Algebra.lmul F K τ).charpoly.natDegree = r` using `by rw [LinearMap.charpoly_natDegree, hr]`. Establish `hCH : Polynomial.aeval τ (Algebra.lmul F K τ).charpoly = 0`.

Establish `h1` using `LinearMap.aeval_self_charpoly (Algebra.lmul F K τ)`. Rewrite `h1` using `[Polynomial.aeval_algHom_apply]`. Establish `h2` using `congrArg (fun f : Module.End F K => f 1) h1`. Simplify using `using h2`. Establish `hdvd : minpoly F τ ∣ (Algebra.lmul F K τ).charpoly` using `minpoly.dvd F τ hCH`.

Use `Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmon hcm hdvd ?_` and prove the remaining obligations. Rewrite using `[hcd]`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `hsum : ∑ i : Fin r, (minpoly F τ).coeff i • τ ^ (i : ℕ) = 0`.

Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => (minpoly F τ).coeff i • τ ^ i) r, ← Polynomial.aeval_eq_sum_range' hlt, minpoly.aeval]`. Establish `h0` using `Fintype.linearIndependent_iff.1 hli (fun i => (minpoly F τ).coeff i) hsum ⟨(minpoly F τ).natDegree, hlt⟩`. Simplify using `only at h0`. Use `hmon.coeff_natDegree` as an intermediate fact. Rewrite `this` using `[h0]`.

Conclude with `zero_ne_one this`.
-/
theorem charpoly_lmul_eq_minpoly {F K : Type} [Field F] [CommRing K] [Algebra F K] [Module.Finite F K] {r : ℕ}
    (τ : K) (hli : LinearIndependent F (fun i : Fin r => τ ^ (i : ℕ))) (hr : Module.finrank F K = r) :
    (Algebra.lmul F K τ).charpoly = minpoly F τ := by
  have hint : IsIntegral F τ := Algebra.IsIntegral.isIntegral τ
  have hmon := minpoly.monic hint
  have hcm := LinearMap.charpoly_monic (Algebra.lmul F K τ)
  have hcd : (Algebra.lmul F K τ).charpoly.natDegree = r := by rw [LinearMap.charpoly_natDegree, hr]
  have hCH : Polynomial.aeval τ (Algebra.lmul F K τ).charpoly = 0 := by
    have h1 := LinearMap.aeval_self_charpoly (Algebra.lmul F K τ)
    rw [Polynomial.aeval_algHom_apply] at h1
    have h2 := congrArg (fun f : Module.End F K => f 1) h1
    simpa using h2
  have hdvd : minpoly F τ ∣ (Algebra.lmul F K τ).charpoly := minpoly.dvd F τ hCH
  refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmon hcm hdvd ?_
  rw [hcd]
  by_contra hlt
  push_neg at hlt
  have hsum : ∑ i : Fin r, (minpoly F τ).coeff i • τ ^ (i : ℕ) = 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => (minpoly F τ).coeff i • τ ^ i) r,
      ← Polynomial.aeval_eq_sum_range' hlt, minpoly.aeval]
  have h0 := Fintype.linearIndependent_iff.1 hli (fun i => (minpoly F τ).coeff i) hsum
    ⟨(minpoly F τ).natDegree, hlt⟩
  simp only at h0
  have := hmon.coeff_natDegree
  rw [h0] at this
  exact zero_ne_one this

/- English proof (translation)
Introduce `F E _ _ _ _ hU A r τ p hg j B hB`. Use `haveI : CharZero F := hU.charZero`. Establish `hb : IsBaseChange E (IsScalarTower.toAlgHom F A.K A.L).toLinearMap` using `A.push.out`. Use `haveI : Module.Finite E A.L := Module.Finite.equiv hb.equiv`. Use `haveI : Module.Free E A.L := hb.free`.

Establish `e : (Algebra.lmul E A.L (algebraMap A.K A.L τ)).charpoly = (Algebra.lmul F A.K τ).charpoly.map (algebraMap F E)`. Rewrite using `[← LinearMap.charpoly_baseChange, ← hb.equiv.charpoly_conj]`. Use `congr 1`. Use extensionality with `y`. Take `⟨t, rfl⟩` from `hb.equiv.surjective y`.

Simplify using `only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a x => simp [IsBaseChange.equiv_tmul, mul_smul_comm, map_mul]`. Consider the case `add s t hs ht => simp only [map_add, hs, ht, mul_add]`.

Establish `hT : Matrix.toLin' B = j.conj (Algebra.lmul E A.L (algebraMap A.K A.L τ))`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`. Use `hB (j.symm v)` as an intermediate fact. Simplify using `only [LinearEquiv.apply_symm_apply] at this`.

Simplify using `[LinearEquiv.conj_apply, this]`. Establish `hc : B.charpoly = (Matrix.toLin' B).charpoly`. Rewrite using `[← LinearMap.charpoly_toMatrix (Matrix.toLin' B) (Pi.basisFun E (Fin r)), LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']`. Rewrite using `[hc, hT, LinearEquiv.charpoly_conj, e, charpoly_lmul_eq_minpoly τ hg.1 hg.2.1]`. Conclude with `(PerfectField.separable_iff_squarefree.2 (squarefree_minpoly τ)).map`.
-/
theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F), A.IsGen τ p →
    ∀ (j : A.L ≃ₗ[E] (Fin r → E)) (B : Matrix (Fin r) (Fin r) E),
      (∀ z, j (algebraMap A.K A.L τ * z) = B *ᵥ j z) → B.charpoly.Separable := by
  intro F E _ _ _ _ hU A r τ p hg j B hB
  haveI : CharZero F := hU.charZero
  have hb : IsBaseChange E (IsScalarTower.toAlgHom F A.K A.L).toLinearMap := A.push.out
  haveI : Module.Finite E A.L := Module.Finite.equiv hb.equiv
  haveI : Module.Free E A.L := hb.free
  have e : (Algebra.lmul E A.L (algebraMap A.K A.L τ)).charpoly =
      (Algebra.lmul F A.K τ).charpoly.map (algebraMap F E) := by
    rw [← LinearMap.charpoly_baseChange, ← hb.equiv.charpoly_conj]
    congr 1
    ext y
    obtain ⟨t, rfl⟩ := hb.equiv.surjective y
    simp only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp [IsBaseChange.equiv_tmul, mul_smul_comm, map_mul]
    | add s t hs ht => simp only [map_add, hs, ht, mul_add]
  have hT : Matrix.toLin' B = j.conj (Algebra.lmul E A.L (algebraMap A.K A.L τ)) := by
    apply LinearMap.ext
    intro v
    have := hB (j.symm v)
    simp only [LinearEquiv.apply_symm_apply] at this
    simp [LinearEquiv.conj_apply, this]
  have hc : B.charpoly = (Matrix.toLin' B).charpoly := by
    rw [← LinearMap.charpoly_toMatrix (Matrix.toLin' B) (Pi.basisFun E (Fin r)), LinearMap.toMatrix_eq_toMatrix',
      LinearMap.toMatrix'_toLin']
  rw [hc, hT, LinearEquiv.charpoly_conj, e, charpoly_lmul_eq_minpoly τ hg.1 hg.2.1]
  exact (PerfectField.separable_iff_squarefree.2 (squarefree_minpoly τ)).map

end GlobalTheory.JR.Et.CharpolySep
