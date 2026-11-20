import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.CycFFTB

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.FFTSteps.CycF

variable {m n : ℕ} (ε : Fin m → Bool)

def eqv : Fin m × Fin n × Bool ≃ VV (Rw ε false) n ⊕ VV (Rw ε true) n where
  toFun k := if h : ε k.1 = true then Sum.inr (if k.2.2 then Sum.inr (⟨k.1, h⟩, k.2.1) else Sum.inl (⟨k.1, h⟩, k.2.1))
    else Sum.inl (if k.2.2 then Sum.inr (⟨k.1, by simpa using h⟩, k.2.1) else Sum.inl (⟨k.1, by simpa using h⟩, k.2.1))
  invFun := Sum.elim (jv ε false) (jv ε true)
  left_inv k := by
    obtain ⟨a, i, t⟩ := k
    by_cases h : ε a = true <;> cases t <;> simp [h, jv]
  right_inv x := by
    rcases x with (⟨⟨a, ha⟩, i⟩ | ⟨⟨a, ha⟩, i⟩) | (⟨⟨a, ha⟩, i⟩ | ⟨⟨a, ha⟩, i⟩) <;> simp [jv, ha]

def Th : PX m n ≃ₐ[ℂ] MvPolynomial (VV (Rw ε false) n) (PV (Rw ε true) (Fin n) (Fin n)) :=
  (renameEquiv ℂ (eqv ε)).trans (sumAlgEquiv ℂ _ _)

variable {ε}

/- English proof (translation)
Simplify using `[Th]`.
-/
theorem th_X (k : Fin m × Fin n × Bool) : Th ε (X k) = sumAlgEquiv ℂ _ _ (X (eqv ε k)) := by
  simp [Th]

/- English proof (translation)
Proceed by induction on `c using MvPolynomial.induction_on with`. Consider the case `C a`. Simplify using `[emb, Th]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p v hp`.

Establish `e : eqv ε (jv ε true v) = Sum.inr v` using `(eqv ε).apply_symm_apply (Sum.inr v)`. Establish `hx : Th ε (emb ε true (X v)) = C (X v)`. Simplify using `only [emb, rename_X]`. Rewrite using `[th_X, e]`. Conclude with `sumRingEquiv_X_inr ℂ _ _ v`.

Rewrite using `[map_mul, map_mul, hp, hx, C_mul]`.
-/
theorem th_embT (c : PV (Rw ε true) (Fin n) (Fin n)) : Th ε (emb ε true c) = C c := by
  induction c using MvPolynomial.induction_on with
  | C a =>
    simp [emb, Th]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    have e : eqv ε (jv ε true v) = Sum.inr v := (eqv ε).apply_symm_apply (Sum.inr v)
    have hx : Th ε (emb ε true (X v)) = C (X v) := by
      simp only [emb, rename_X]
      rw [th_X, e]
      exact sumRingEquiv_X_inr ℂ _ _ v
    rw [map_mul, map_mul, hp, hx, C_mul]

/- English proof (translation)
Proceed by induction on `t using MvPolynomial.induction_on with`. Consider the case `C a`. Simplify using `[emb, Th]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p v hp`.

Establish `e : eqv ε (jv ε false v) = Sum.inl v` using `(eqv ε).apply_symm_apply (Sum.inl v)`. Establish `hx : Th ε (emb ε false (X v)) = X v`. Simplify using `only [emb, rename_X]`. Rewrite using `[th_X, e]`. Conclude with `sumRingEquiv_X_inl ℂ _ _ v`.

Rewrite using `[map_mul, map_mul, hp, hx, map_mul, map_X]`.
-/
theorem th_embF (t : PV (Rw ε false) (Fin n) (Fin n)) :
    Th ε (emb ε false t) = map (algebraMap ℂ (PV (Rw ε true) (Fin n) (Fin n))) t := by
  induction t using MvPolynomial.induction_on with
  | C a =>
    simp [emb, Th]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    have e : eqv ε (jv ε false v) = Sum.inl v := (eqv ε).apply_symm_apply (Sum.inl v)
    have hx : Th ε (emb ε false (X v)) = X v := by
      simp only [emb, rename_X]
      rw [th_X, e]
      exact sumRingEquiv_X_inl ℂ _ _ v
    rw [map_mul, map_mul, hp, hx, map_mul, map_X]

/- English proof (translation)
Rewrite using `[map_mul, th_embT, th_embF, map_monomial, map_one, C_mul_monomial, mul_one]`.
-/
theorem th_prod (c : PV (Rw ε true) (Fin n) (Fin n)) (μ : VV (Rw ε false) n →₀ ℕ) :
    Th ε (emb ε true c * emb ε false (monomial μ 1)) = monomial μ c := by
  rw [map_mul, th_embT, th_embF, map_monomial, map_one, C_mul_monomial, mul_one]

/- English proof (translation)
Apply `(Th ε).injective` to reduce the goal to its premises. Rewrite using `[map_sum]`. Repeatedly rewrite using `[th_prod]`. Conclude with `(Th ε Q).as_sum`.
-/
theorem decomp (Q : PX m n) :
    Q = ∑ μ ∈ (Th ε Q).support, emb ε true ((Th ε Q).coeff μ) * emb ε false (monomial μ 1) := by
  apply (Th ε).injective
  rw [map_sum]
  simp_rw [th_prod]
  exact (Th ε Q).as_sum

/- English proof (translation)
Rewrite using `[coeff_sum]`. Simplify using `only [coeff_monomial]`. Use `split_ifs with h`. Rewrite using `[Finset.sum_eq_single μ]`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Simplify using `[hb]`. Introduce `h'`. Conclude with `absurd h h'`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `b hb`. Establish `: b ≠ μ` using `fun e => h (e ▸ hb)`. Simplify using `[this]`.
-/
theorem coeff_sum_monomial {σ R : Type*} [CommSemiring R] [DecidableEq σ] (S : Finset (σ →₀ ℕ)) (f : (σ →₀ ℕ) → R) (μ : σ →₀ ℕ) :
    coeff μ (∑ ν ∈ S, monomial ν (f ν)) = if μ ∈ S then f μ else 0 := by
  rw [coeff_sum]
  simp only [coeff_monomial]
  split_ifs with h
  · rw [Finset.sum_eq_single μ]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h'
      exact absurd h h'
  · apply Finset.sum_eq_zero
    intro b hb
    have : b ≠ μ := fun e => h (e ▸ hb)
    simp [this]

/- English proof (translation)
Establish `h2` using `congrArg (Th ε) h`. Rewrite `h2` using `[map_sum, map_zero]`. Rewrite `h2` using `[map_mul, th_embT, th_embF]`. Introduce `j`. Use extensionality with `μ`.

Establish `h3` using `congrArg (coeff μ) h2`. Rewrite `h3` using `[coeff_sum, coeff_zero]`. Rewrite `h3` using `[coeff_C_mul, coeff_map]`. Establish `h4 : ∑ i, (coeff μ (t i)) • b i = 0`. Rewrite using `[← h3]`.

Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, mul_comm]`. Use `Fintype.linearIndependent_iff.1 hb _ h4 j` as an intermediate fact. Simplify using `using this`.
-/
theorem indep {J : Type} [Fintype J] (b : J → PV (Rw ε true) (Fin n) (Fin n)) (hb : LinearIndependent ℂ b)
    (t : J → PV (Rw ε false) (Fin n) (Fin n)) (h : ∑ j, emb ε true (b j) * emb ε false (t j) = 0) : ∀ j, t j = 0 := by
  have h2 := congrArg (Th ε) h
  rw [map_sum, map_zero] at h2
  simp_rw [map_mul, th_embT, th_embF] at h2
  intro j
  ext μ
  have h3 := congrArg (coeff μ) h2
  rw [coeff_sum, coeff_zero] at h3
  simp_rw [coeff_C_mul, coeff_map] at h3
  have h4 : ∑ i, (coeff μ (t i)) • b i = 0 := by
    rw [← h3]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Algebra.smul_def, mul_comm]
  have := Fintype.linearIndependent_iff.1 hb _ h4 j
  simpa using this

end PositivityTheory.Rg.Sw.FFTSteps.CycF
