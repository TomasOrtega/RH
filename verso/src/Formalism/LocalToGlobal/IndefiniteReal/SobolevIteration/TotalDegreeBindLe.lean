import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfHaar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Mult
  MeasureTheory Matrix Filter Topology

namespace Formalism.IndefR.Tow.SobPf

namespace KFin

variable {n : ℕ}

def KS (G s : Matrix (Fin n) (Fin n) ℂ) : Set (Fin n → Fin n → ℂ) := {k | Matrix.of k ∈ KAt G s}

/- English proof (translation)
The claim follows from `isCompact_KAt hs`.
-/
theorem isCompact_KS {G s : Matrix (Fin n) (Fin n) ℂ} (hs : IsCartanInv G s) : IsCompact (KS G s) := isCompact_KAt hs

/- English proof (translation)
Establish `h : IsClosed (KS G s)` using `isClosed_KAt G s`. Conclude with `h.measurableSet`.
-/
theorem measurableSet_KS (G s : Matrix (Fin n) (Fin n) ℂ) : MeasurableSet (KS G s) := by

  have h : IsClosed (KS G s) := isClosed_KAt G s
  exact h.measurableSet

section Int

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/- English proof (translation)
Establish `hmaps : Set.MapsTo (fun k : Fin n → Fin n → ℂ => Matrix.of k) (KS G s) (Formalism.QuantumDeterminants.UH G)` using `fun k hk => (show Matrix.of k ∈ Formalism.QuantumDeterminants.UH G ∧ Matrix.of k * s = s * Matrix.of k from hk).1`. Establish `hof : ContinuousOn (fun k : Fin n → Fin n → ℂ => Matrix.of k) (KS G s)` using `continuous_id.continuousOn`. Establish `h1 : ContinuousOn (fun k : Fin n → Fin n → ℂ => π (Matrix.of k) w) (KS G s)` using `(hπ.2.2.2 w).comp hof hmaps`. Conclude with `hp.continuousOn.smul h1`.
-/
theorem continuousOn_avg {G s : Matrix (Fin n) (Fin n) ℂ} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hπ : IsGRep G π) {p : (Fin n → Fin n → ℂ) → ℂ} (hp : Continuous p) (w : H) :
    ContinuousOn (fun k => p k • π (Matrix.of k) w) (KS G s) := by

  have hmaps : Set.MapsTo (fun k : Fin n → Fin n → ℂ => Matrix.of k) (KS G s) (Formalism.QuantumDeterminants.UH G) :=
    fun k hk => (show Matrix.of k ∈ Formalism.QuantumDeterminants.UH G ∧ Matrix.of k * s = s * Matrix.of k from hk).1
  have hof : ContinuousOn (fun k : Fin n → Fin n → ℂ => Matrix.of k) (KS G s) :=
    continuous_id.continuousOn
  have h1 : ContinuousOn (fun k : Fin n → Fin n → ℂ => π (Matrix.of k) w) (KS G s) :=
    (hπ.2.2.2 w).comp hof hmaps
  exact hp.continuousOn.smul h1

/- English proof (translation)
Use `haveI := hμ.1`. Establish `hae : ∀ᵐ k ∂μ, k ∈ KS G s` using `hμ.2.1`. Establish `h` using `(continuousOn_avg (s := s) hπ hp w).integrableOn_compact (μ := μ) (isCompact_KS hs)`. Rewrite `h` using `[IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae]`. Then use the resulting hypothesis.
-/
theorem integrable_avg {G s : Matrix (Fin n) (Fin n) ℂ} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hs : IsCartanInv G s) (hπ : IsGRep G π) {μ : Measure (Fin n → Fin n → ℂ)} (hμ : IsHaarK G s μ)
    {p : (Fin n → Fin n → ℂ) → ℂ} (hp : Continuous p) (w : H) :
    Integrable (fun k => p k • π (Matrix.of k) w) μ := by

  haveI := hμ.1
  have hae : ∀ᵐ k ∂μ, k ∈ KS G s := hμ.2.1
  have h := (continuousOn_avg (s := s) hπ hp w).integrableOn_compact (μ := μ) (isCompact_KS hs)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae] at h

end Int

abbrev Var (n : ℕ) := (Fin n × Fin n) ⊕ (Fin n × Fin n)

def subst (A : Matrix (Fin n) (Fin n) ℂ) : Var n → MvPolynomial (Var n) ℂ
  | Sum.inl ij => ∑ l, MvPolynomial.C (A ij.1 l) * MvPolynomial.X (Sum.inl (l, ij.2))
  | Sum.inr ij => ∑ l, MvPolynomial.C (starRingEnd ℂ (A ij.1 l)) * MvPolynomial.X (Sum.inr (l, ij.2))

/- English proof (translation)
Proceed by induction on `q using MvPolynomial.induction_on`. Use `next a =>`. Simplify using `[evP]`. Use `next p r hp hr =>`. Simplify using `only [evP, map_add] at hp hr ⊢`.

Rewrite using `[hp, hr]`. Use `next p v hp =>`. Simplify using `only [evP, map_mul, MvPolynomial.bind₁_X_right, MvPolynomial.eval_X] at hp ⊢`. Rewrite using `[hp]`. Use `congr 1`.

Break down `v with ⟨i, j⟩ | ⟨i, j⟩` into its components or cases. Simplify using `[subst, Matrix.mul_apply, Matrix.of_apply, MvPolynomial.eval_X, MvPolynomial.eval_C]`. Simplify using `[subst, Matrix.mul_apply, Matrix.of_apply, MvPolynomial.eval_X, MvPolynomial.eval_C, map_sum]`.
-/
theorem evalMatrix_bind₁_mulLeft (A : Matrix (Fin n) (Fin n) ℂ) (q : MvPolynomial (Var n) ℂ) (k : Fin n → Fin n → ℂ) :
    evP (MvPolynomial.bind₁ (subst A) q) k = evP q (Matrix.of.symm (A * Matrix.of k)) := by

  induction q using MvPolynomial.induction_on
  next a =>
    simp [evP]
  next p r hp hr =>
    simp only [evP, map_add] at hp hr ⊢
    rw [hp, hr]
  next p v hp =>
    simp only [evP, map_mul, MvPolynomial.bind₁_X_right, MvPolynomial.eval_X] at hp ⊢
    rw [hp]
    congr 1
    rcases v with ⟨i, j⟩ | ⟨i, j⟩
    · simp [subst, Matrix.mul_apply, Matrix.of_apply, MvPolynomial.eval_X, MvPolynomial.eval_C]
    · simp [subst, Matrix.mul_apply, Matrix.of_apply, MvPolynomial.eval_X, MvPolynomial.eval_C, map_sum]

/- English proof (translation)
Apply the tactic sequence `rcases v with ij | ij <;>`. Simplify using `only [subst]`. Use `(MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun l _ => ?_)` and prove the remaining obligations. Use `(MvPolynomial.totalDegree_mul _ _).trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem totalDegree_subst (A : Matrix (Fin n) (Fin n) ℂ) (v : Var n) : (subst A v).totalDegree ≤ 1 := by

  rcases v with ij | ij <;>
  · simp only [subst]
    refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun l _ => ?_)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    simp

/- English proof (translation)
Use `conv_lhs => rw [q.as_sum]`. Rewrite using `[map_sum]`. Use `(MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun m hm => ?_)` and prove the remaining obligations. Rewrite using `[MvPolynomial.bind₁_monomial]`. Use `(MvPolynomial.totalDegree_mul _ _).trans ?_` and prove the remaining obligations.

Rewrite using `[MvPolynomial.totalDegree_C, zero_add]`. Use `(MvPolynomial.totalDegree_finset_prod _ _).trans ?_` and prove the remaining obligations. Use `le_trans (Finset.sum_le_sum fun i _ => (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul le_rfl (totalDegree_subst A i))) ?_` and prove the remaining obligations. Simplify using `only [mul_one]`. Conclude with `MvPolynomial.le_totalDegree hm`.
-/
theorem totalDegree_bind_le (A : Matrix (Fin n) (Fin n) ℂ) (q : MvPolynomial (Var n) ℂ) :
    (MvPolynomial.bind₁ (subst A) q).totalDegree ≤ q.totalDegree := by

  conv_lhs => rw [q.as_sum]
  rw [map_sum]
  refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun m hm => ?_)
  rw [MvPolynomial.bind₁_monomial]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_finset_prod _ _).trans ?_
  refine le_trans (Finset.sum_le_sum fun i _ => (MvPolynomial.totalDegree_pow _ _).trans
    (Nat.mul_le_mul le_rfl (totalDegree_subst A i))) ?_
  simp only [mul_one]
  exact MvPolynomial.le_totalDegree hm

def Mon (n N : ℕ) : Set (Var n →₀ ℕ) := {m | (m.sum fun _ e => e) ≤ N}

/- English proof (translation)
Use `(Set.finite_range (fun f : Var n → Fin (N + 1) => Finsupp.equivFunOnFinite.symm (fun v => (f v : ℕ)))).subset ?_` and prove the remaining obligations. Introduce `m hm`. Establish `hm' : ∑ v ∈ m.support, m v ≤ N` using `hm`. Establish `hle : ∀ v, m v ≤ N`. Introduce `v`.

Distinguish the cases in `hv : v ∈ m.support`. Conclude with `le_trans (Finset.single_le_sum (f := fun v => m v) (fun _ _ => Nat.zero_le _) hv) hm'`. Establish `h0 : m v = 0` using `by simpa using hv`. Rewrite using `[h0]`. Conclude with `Nat.zero_le _`.

Use `⟨fun v => ⟨m v, Nat.lt_succ_of_le (hle v)⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `v`. Simplify using the standard rewrite rules.
-/
theorem finite_Mon (n N : ℕ) : (Mon n N).Finite := by

  refine (Set.finite_range (fun f : Var n → Fin (N + 1) =>
    Finsupp.equivFunOnFinite.symm (fun v => (f v : ℕ)))).subset ?_
  intro m hm
  have hm' : ∑ v ∈ m.support, m v ≤ N := hm
  have hle : ∀ v, m v ≤ N := by
    intro v
    by_cases hv : v ∈ m.support
    · exact le_trans (Finset.single_le_sum (f := fun v => m v) (fun _ _ => Nat.zero_le _) hv) hm'
    · have h0 : m v = 0 := by simpa using hv
      rw [h0]; exact Nat.zero_le _
  refine ⟨fun v => ⟨m v, Nat.lt_succ_of_le (hle v)⟩, ?_⟩
  ext v
  simp

/- English proof (translation)
Simplify using `only [evP]`. Use `conv_lhs => rw [q.as_sum]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[show MvPolynomial.monomial m (q.coeff m) = MvPolynomial.C (q.coeff m) * MvPolynomial.monomial m (1 : ℂ) by`.

Rewrite using `[MvPolynomial.C_mul_monomial, mul_one], map_mul, MvPolynomial.eval_C]`.
-/
theorem evalMatrix_eq_sum_monomial (q : MvPolynomial (Var n) ℂ) (k : Fin n → Fin n → ℂ) :
    evP q k = ∑ m ∈ q.support, q.coeff m * evP (MvPolynomial.monomial m 1) k := by

  simp only [evP]
  conv_lhs => rw [q.as_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [show MvPolynomial.monomial m (q.coeff m) =
      MvPolynomial.C (q.coeff m) * MvPolynomial.monomial m (1 : ℂ) by
    rw [MvPolynomial.C_mul_monomial, mul_one], map_mul, MvPolynomial.eval_C]

end KFin

end Formalism.IndefR.Tow.SobPf

end
