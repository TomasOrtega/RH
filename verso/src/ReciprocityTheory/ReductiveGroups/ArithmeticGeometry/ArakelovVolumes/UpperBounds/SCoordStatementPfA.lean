import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.SCoA

open MvPolynomial

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {ι : Type*} [Fintype ι]
  {K : Type*} [CommSemiring K] (σ : K →+* ℂ)

/- English proof (translation)
Proceed by induction on `q using MvPolynomial.induction_on with`. Consider the case `C a => simpa using hasFDerivAt_const (σ a) z0`. Consider the case `add p q hp hq`. Simplify using `only [eval₂_add, map_add, add_smul, Finset.sum_add_distrib]`. Conclude with `hp.add hq`.

Consider the case `mul_X p i hp`. Simplify using `only [eval₂_mul, eval₂_X]`. Use `(hp.mul (hh i)).congr_fderiv ?_` and prove the remaining obligations. Simplify using `only [Derivation.leibniz, smul_eq_mul, eval₂_add, eval₂_mul, eval₂_X, add_smul, Finset.sum_add_distrib, Finset.smul_sum, smul_smul]`. Use `congr 1`.

Rewrite using `[Finset.sum_eq_single i]`. Simplify using `[pderiv_X_self]`. Introduce `b _ hb classical`. Rewrite using `[pderiv_X]`. Simplify using `[hb.symm]`.

Simplify using the standard rewrite rules.
-/
theorem hasFDerivAt_mv (q : MvPolynomial ι K) {h : V → ι → ℂ} {z0 : V} {Dh : ι → V →L[ℂ] ℂ}
    (hh : ∀ i, HasFDerivAt (fun z => h z i) (Dh i) z0) :
    HasFDerivAt (fun z => eval₂ σ (h z) q) (∑ i, eval₂ σ (h z0) (pderiv i q) • Dh i) z0 := by
  induction q using MvPolynomial.induction_on with
  | C a => simpa using hasFDerivAt_const (σ a) z0
  | add p q hp hq =>
    simp only [eval₂_add, map_add, add_smul, Finset.sum_add_distrib]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [eval₂_mul, eval₂_X]
    refine (hp.mul (hh i)).congr_fderiv ?_
    simp only [Derivation.leibniz, smul_eq_mul, eval₂_add, eval₂_mul, eval₂_X, add_smul,
      Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
    congr 1
    rw [Finset.sum_eq_single i]
    · simp [pderiv_X_self]
    · intro b _ hb
      classical
      rw [pderiv_X]
      simp [hb.symm]
    · simp

def xTerm {R : Type*} [CommSemiring R] (ψ : MvPolynomial ι K →+* R) (s : R) (i : ι)
    (P : Polynomial (MvPolynomial ι K)) : R :=
  P.sum fun n c => ψ (pderiv i c) * s ^ n

/- English proof (translation)
Unfold `xTerm`. Conclude with `Polynomial.sum_add_index _ _ _ (by simp) (by intros; simp [add_mul])`.
-/
theorem xTerm_add {R : Type*} [CommSemiring R] (ψ : MvPolynomial ι K →+* R) (s : R) (i : ι)
    (P Q : Polynomial (MvPolynomial ι K)) : xTerm ψ s i (P + Q) = xTerm ψ s i P + xTerm ψ s i Q := by
  unfold xTerm
  exact Polynomial.sum_add_index _ _ _ (by simp) (by intros; simp [add_mul])

/- English proof (translation)
Unfold `xTerm`. Conclude with `Polynomial.sum_monomial_index _ _ (by simp)`.
-/
theorem xTerm_monomial {R : Type*} [CommSemiring R] (ψ : MvPolynomial ι K →+* R) (s : R) (i : ι)
    (n : ℕ) (c : MvPolynomial ι K) : xTerm ψ s i (Polynomial.monomial n c) = ψ (pderiv i c) * s ^ n := by
  unfold xTerm
  exact Polynomial.sum_monomial_index _ _ (by simp)

/- English proof (translation)
Unfold `xTerm Polynomial.sum`. Simplify using `[map_sum]`.
-/
theorem map_xTerm {R S : Type*} [CommSemiring R] [CommSemiring S] (ψ : MvPolynomial ι K →+* R)
    (f : R →+* S) (s : R) (i : ι) (P : Polynomial (MvPolynomial ι K)) :
    f (xTerm ψ s i P) = xTerm (f.comp ψ) (f s) i P := by
  unfold xTerm Polynomial.sum
  simp [map_sum]

/- English proof (translation)
Proceed by induction on `P using Polynomial.induction_on' with`. Consider the case `add p q hp hq`. Simplify using `only [Polynomial.eval₂_add]`. Use `(hp.add hq).congr_fderiv ?_` and prove the remaining obligations. Simplify using `only [map_add, Polynomial.eval₂_add, xTerm_add, add_smul, Finset.sum_add_distrib]`.

Normalize the expressions using the abelian group laws. Consider the case `monomial n c`. Simplify using `only [Polynomial.eval₂_monomial]`. Use `((hasFDerivAt_mv σ c hh).mul (hg.pow n)).congr_fderiv ?_` and prove the remaining obligations. Simplify using `only [Polynomial.derivative_monomial, xTerm_monomial, Polynomial.eval₂_monomial, coe_eval₂Hom, Finset.smul_sum, smul_smul, map_mul, map_natCast, nsmul_eq_mul]`.

Use `congr 1`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Conclude with `Finset.sum_congr rfl fun b _ => by rw [mul_comm]`.
-/
theorem hasFDerivAt_eval₂ (P : Polynomial (MvPolynomial ι K)) {h : V → ι → ℂ} {g : V → ℂ} {z0 : V}
    {Dh : ι → V →L[ℂ] ℂ} {Dg : V →L[ℂ] ℂ}
    (hh : ∀ i, HasFDerivAt (fun z => h z i) (Dh i) z0) (hg : HasFDerivAt g Dg z0) :
    HasFDerivAt (fun z => P.eval₂ (eval₂Hom σ (h z)) (g z))
      ((Polynomial.derivative P).eval₂ (eval₂Hom σ (h z0)) (g z0) • Dg +
        ∑ i, xTerm (eval₂Hom σ (h z0)) (g z0) i P • Dh i) z0 := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval₂_add]
    refine (hp.add hq).congr_fderiv ?_
    simp only [map_add, Polynomial.eval₂_add, xTerm_add, add_smul, Finset.sum_add_distrib]
    abel
  | monomial n c =>
    simp only [Polynomial.eval₂_monomial]
    refine ((hasFDerivAt_mv σ c hh).mul (hg.pow n)).congr_fderiv ?_
    simp only [Polynomial.derivative_monomial, xTerm_monomial, Polynomial.eval₂_monomial, coe_eval₂Hom,
      Finset.smul_sum, smul_smul, map_mul, map_natCast, nsmul_eq_mul]
    congr 1
    · congr 1; ring
    · exact Finset.sum_congr rfl fun b _ => by rw [mul_comm]

omit [Fintype ι] in

/- English proof (translation)
Take `⟨q, hq0, hqa⟩` from `ha`. Set `f : Algebra.adjoin K (Set.range y) →+* MvPolynomial ι K` to `hy.aevalEquiv.symm.toRingHom`. Establish `hf : Function.Injective f` using `hy.aevalEquiv.symm.injective`. Establish `hcomp : (aeval y).toRingHom.comp f = algebraMap (Algebra.adjoin K (Set.range y)) Ω`. Use extensionality with `s`.

Use `hy.algebraMap_aevalEquiv (hy.aevalEquiv.symm s)` as an intermediate fact. Rewrite `this` using `[AlgEquiv.apply_symm_apply]`. Conclude with `this.symm`. Establish `hex : ∃ n, ∃ P : Polynomial (MvPolynomial ι K), P ≠ 0 ∧ P.eval₂ (aeval y).toRingHom a = 0 ∧ P.natDegree = n`. Use `⟨_, q.map f, (Polynomial.map_ne_zero_iff hf).mpr hq0, ?_, rfl⟩` and prove the remaining obligations.

Rewrite using `[Polynomial.eval₂_map, hcomp]`. Conclude with `hqa`. Take `⟨P, hP0, hPa, hPn⟩` from `Nat.find_spec hex`. Use `⟨P, hPa, fun hd => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hD : Polynomial.derivative P = 0`.

Establish `h0 : P.natDegree = 0` using `Polynomial.derivative_eq_zero.mp hD`. Rewrite `hPa` using `[Polynomial.eq_C_of_natDegree_eq_zero h0, Polynomial.eval₂_C]`. Establish `hc : P.coeff 0 = 0` using `hy (by simpa using hPa)`. Apply `hP0` to reduce the goal to its premises. Rewrite using `[Polynomial.eq_C_of_natDegree_eq_zero h0, hc, map_zero]`.

Establish `hne : P.natDegree ≠ 0` using `fun h0 => hD (Polynomial.derivative_eq_zero.mpr h0)`. Establish `hlt` using `Polynomial.natDegree_derivative_lt hne`. Rewrite `hlt` using `[hPn]`. Conclude with `Nat.find_min hex hlt ⟨_, hD, hd, rfl⟩`.
-/
theorem exists_rel {K Ω : Type*} [Field K] [CharZero K] [Field Ω] [Algebra K Ω] {y : ι → Ω}
    (hy : AlgebraicIndependent K y) {a : Ω} (ha : IsAlgebraic (Algebra.adjoin K (Set.range y)) a) :
    ∃ P : Polynomial (MvPolynomial ι K), P.eval₂ (aeval y).toRingHom a = 0 ∧
      (Polynomial.derivative P).eval₂ (aeval y).toRingHom a ≠ 0 := by
  classical
  obtain ⟨q, hq0, hqa⟩ := ha
  let f : Algebra.adjoin K (Set.range y) →+* MvPolynomial ι K := hy.aevalEquiv.symm.toRingHom
  have hf : Function.Injective f := hy.aevalEquiv.symm.injective
  have hcomp : (aeval y).toRingHom.comp f = algebraMap (Algebra.adjoin K (Set.range y)) Ω := by
    ext s
    have := hy.algebraMap_aevalEquiv (hy.aevalEquiv.symm s)
    rw [AlgEquiv.apply_symm_apply] at this
    exact this.symm
  have hex : ∃ n, ∃ P : Polynomial (MvPolynomial ι K), P ≠ 0 ∧
      P.eval₂ (aeval y).toRingHom a = 0 ∧ P.natDegree = n := by
    refine ⟨_, q.map f, (Polynomial.map_ne_zero_iff hf).mpr hq0, ?_, rfl⟩
    rw [Polynomial.eval₂_map, hcomp]
    exact hqa
  obtain ⟨P, hP0, hPa, hPn⟩ := Nat.find_spec hex
  refine ⟨P, hPa, fun hd => ?_⟩
  by_cases hD : Polynomial.derivative P = 0
  · have h0 : P.natDegree = 0 := Polynomial.derivative_eq_zero.mp hD
    rw [Polynomial.eq_C_of_natDegree_eq_zero h0, Polynomial.eval₂_C] at hPa
    have hc : P.coeff 0 = 0 := hy (by simpa using hPa)
    apply hP0
    rw [Polynomial.eq_C_of_natDegree_eq_zero h0, hc, map_zero]
  · have hne : P.natDegree ≠ 0 := fun h0 => hD (Polynomial.derivative_eq_zero.mpr h0)
    have hlt := Polynomial.natDegree_derivative_lt hne
    rw [hPn] at hlt
    exact Nat.find_min hex hlt ⟨_, hD, hd, rfl⟩

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.SCoA
