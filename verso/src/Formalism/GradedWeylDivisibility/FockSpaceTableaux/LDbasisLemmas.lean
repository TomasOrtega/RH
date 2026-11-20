import Formalism.GradedWeylDivisibility.StatementD

open MvPolynomial

namespace Formalism.GradedWeylDivisibility

open scoped MonomialOrder

/- English proof (translation)
Rewrite using `[linearIndependent_iff']`. Introduce `s g hsum i hi`. Assume the negation of the conclusion as `hgi`. Establish `htne : (s.filter fun j => g j ≠ 0).Nonempty` using `⟨i, Finset.mem_filter.mpr ⟨hi, hgi⟩⟩`. Take `⟨j, hj, hjmax⟩` from `(s.filter fun j => g j ≠ 0).exists_max_image (fun j => o.toSyn (o.degree (v j))) htne`.

Establish `hcoeff` using `congrArg (MvPolynomial.coeff (o.degree (v j))) hsum`. Rewrite `hcoeff` using `[coeff_zero, coeff_sum, Finset.sum_eq_single j]`. Rewrite `hcoeff` using `[coeff_smul, smul_eq_mul]`. Establish `hone : (v j).coeff (o.degree (v j)) = 1` using `hlc j`. Rewrite `hcoeff` using `[hone, mul_one]`.

Conclude with `(Finset.mem_filter.mp hj).2 hcoeff`. Introduce `k hk hkj`. Rewrite using `[coeff_smul]`. Distinguish the cases in `hgk : g k = 0`. Rewrite using `[hgk, zero_smul]`.

Establish `hle` using `hjmax k (Finset.mem_filter.mpr ⟨hk, hgk⟩)`. Establish `hne : o.degree (v k) ≠ o.degree (v j)` using `fun h => hkj (hinj h)`. Establish `hlt : o.toSyn (o.degree (v k)) < o.toSyn (o.degree (v j))` using `lt_of_le_of_ne hle (fun h => hne (o.toSyn.injective h))`. Rewrite using `[o.coeff_eq_zero_of_lt hlt, smul_zero]`. Introduce `hj'`.

Conclude with `absurd (Finset.mem_filter.mp hj).1 hj'`.
-/
theorem ldbasis_linearIndependent {σ R ι : Type*} [CommRing R] (o : MonomialOrder σ)
    (v : ι → MvPolynomial σ R) (hinj : Function.Injective fun i => o.degree (v i))
    (hlc : ∀ i, o.leadingCoeff (v i) = 1) : LinearIndependent R v := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i hi
  by_contra hgi
  have htne : (s.filter fun j => g j ≠ 0).Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hgi⟩⟩
  obtain ⟨j, hj, hjmax⟩ :=
    (s.filter fun j => g j ≠ 0).exists_max_image (fun j => o.toSyn (o.degree (v j))) htne
  have hcoeff := congrArg (MvPolynomial.coeff (o.degree (v j))) hsum
  rw [coeff_zero, coeff_sum, Finset.sum_eq_single j] at hcoeff
  · rw [coeff_smul, smul_eq_mul] at hcoeff
    have hone : (v j).coeff (o.degree (v j)) = 1 := hlc j
    rw [hone, mul_one] at hcoeff
    exact (Finset.mem_filter.mp hj).2 hcoeff
  · intro k hk hkj
    rw [coeff_smul]
    by_cases hgk : g k = 0
    · rw [hgk, zero_smul]
    · have hle := hjmax k (Finset.mem_filter.mpr ⟨hk, hgk⟩)
      have hne : o.degree (v k) ≠ o.degree (v j) := fun h => hkj (hinj h)
      have hlt : o.toSyn (o.degree (v k)) < o.toSyn (o.degree (v j)) :=
        lt_of_le_of_ne hle (fun h => hne (o.toSyn.injective h))
      rw [o.coeff_eq_zero_of_lt hlt, smul_zero]
  · intro hj'
    exact absurd (Finset.mem_filter.mp hj).1 hj'

/- English proof (translation)
Conclude with `Equiv.sum_comp σ (fun p => (Pi.single (I p) 1 : Fin r → ℕ))`.
-/
theorem ldbasis_sum_single_perm {r s : ℕ} (I : Fin s → Fin r) (σ : Equiv.Perm (Fin s)) :
    (∑ q : Fin s, (Pi.single (I (σ q)) 1 : Fin r → ℕ)) = ∑ p : Fin s, Pi.single (I p) 1 := by
  exact Equiv.sum_comp σ (fun p => (Pi.single (I p) 1 : Fin r → ℕ))

/- English proof (translation)
Unfold `initMinor`. Rewrite using `[Matrix.det_apply]`. Apply `IsWeightedHomogeneous.sum` to reduce the goal to its premises. Introduce `σ _`. Establish `hprod : IsWeightedHomogeneous (rowW r n) (∏ i, (X (I (σ i), Fin.castLE hs i) : MvPolynomial (Fin r × Fin n) R)) (∑ p, Pi.single (I p) 1)`.

Rewrite using `[← ldbasis_sum_single_perm I σ]`. Conclude with `IsWeightedHomogeneous.prod _ _ _ (fun i _ => isWeightedHomogeneous_X R (rowW r n) _)`. Introduce `d hd`. Apply `hprod` to reduce the goal to its premises. Introduce `h0`.

Apply `hd` to reduce the goal to its premises. Use `show coeff d ((Equiv.Perm.sign σ) • ∏ i, (X (I (σ i), Fin.castLE hs i) : MvPolynomial (Fin r × Fin n) R)) = 0`. Rewrite using `[Units.smul_def, coeff_smul, h0, smul_zero]`.
-/
theorem ldbasis_initMinor_rowHom (R : Type*) [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n) :
    IsWeightedHomogeneous (rowW r n) (initMinor R (n := n) I hs) (∑ p : Fin s, Pi.single (I p) 1) := by
  unfold initMinor
  rw [Matrix.det_apply]
  apply IsWeightedHomogeneous.sum
  intro σ _
  have hprod : IsWeightedHomogeneous (rowW r n)
      (∏ i, (X (I (σ i), Fin.castLE hs i) : MvPolynomial (Fin r × Fin n) R))
      (∑ p, Pi.single (I p) 1) := by
    rw [← ldbasis_sum_single_perm I σ]
    exact IsWeightedHomogeneous.prod _ _ _ (fun i _ => isWeightedHomogeneous_X R (rowW r n) _)
  intro d hd
  apply hprod
  intro h0
  apply hd
  show coeff d ((Equiv.Perm.sign σ) •
    ∏ i, (X (I (σ i), Fin.castLE hs i) : MvPolynomial (Fin r × Fin n) R)) = 0
  rw [Units.smul_def, coeff_smul, h0, smul_zero]

/- English proof (translation)
Unfold `bideterminant`. Conclude with `IsWeightedHomogeneous.prod _ _ _ (fun k _ => ldbasis_initMinor_rowHom R (I k) (hsz k))`.
-/
theorem ldbasis_bidet_rowHom (R : Type*) [CommRing R] {r n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) :
    IsWeightedHomogeneous (rowW r n) (bideterminant R sz hsz I)
      (∑ k : Fin K, ∑ p : Fin (sz k), Pi.single (I k p) 1) := by
  unfold bideterminant
  exact IsWeightedHomogeneous.prod _ _ _ (fun k _ => ldbasis_initMinor_rowHom R (I k) (hsz k))

/- English proof (translation)
Use function extensionality and compare the values at `a`. Simplify using `only [rowWt, rowDeg, bidetExp, Finsupp.finset_sum_apply, Finset.sum_apply, Finsupp.single_apply, Pi.single_apply]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun k _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl (fun p _ => ?_)` and prove the remaining obligations. Distinguish the cases in `h : I k p = a`. Substitute `h` using the available equality. Simplify using `[Prod.ext_iff]`. Simplify using `[Prod.ext_iff, h, Ne.symm h]`.
-/
theorem ldbasis_rowWt_bidetExp {r n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) :
    rowWt (bidetExp sz hsz I) = ∑ k : Fin K, ∑ p : Fin (sz k), (Pi.single (I k p) 1 : Fin r → ℕ) := by
  classical
  funext a
  simp only [rowWt, rowDeg, bidetExp, Finsupp.finset_sum_apply, Finset.sum_apply,
    Finsupp.single_apply, Pi.single_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases h : I k p = a
  · subst h
    simp [Prod.ext_iff]
  · simp [Prod.ext_iff, h, Ne.symm h]

end Formalism.GradedWeylDivisibility
