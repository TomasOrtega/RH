import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.FibOfTens
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.PosNear
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensFibV
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC

noncomputable section

namespace PI.VolStabS

namespace TensAllW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW PositiveNearLattice Matrix

def LIP (R : Type) [CommRing R] : Prop :=
  ∀ (m n : Type) [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (W : Matrix m n R),
    (∀ c, W *ᵥ c = 0 → c = 0) → ∃ P : Matrix n m R, P * W = 1

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

A detailed English derivation is pending.
-/
theorem lip_field (K : Type) [Field K] : LIP K := by
  intro m n _ _ _ _ W hW
  have hk : LinearMap.ker (Matrix.toLin' W) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    exact hW c (by simpa [Matrix.toLin'_apply] using hc)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' W) hk
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have h1 : Matrix.toLin' (LinearMap.toMatrix' g * W) = LinearMap.id := by
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', hg]
  have h2 := congrArg LinearMap.toMatrix' h1
  rwa [LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at h2

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Simplify using the standard rewrite rules. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.

A detailed English derivation is pending.
-/
theorem lip_pi {ι : Type} [Fintype ι] [DecidableEq ι] (K : ι → Type) [∀ i, CommRing (K i)]
    (h : ∀ i, LIP (K i)) : LIP (∀ i, K i) := by
  intro m n _ _ _ _ W hW
  have hv : ∀ v, ∃ P : Matrix n m (K v), P * W.map (fun x => x v) = 1 := by
    intro v
    refine h v m n _ ?_
    intro c hc
    have key : W *ᵥ (fun j => Pi.single v (c j)) = 0 := by
      funext i v'
      simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.mul_apply, Pi.zero_apply]
      by_cases hv' : v' = v
      · subst hv'
        have := congrFun hc i
        simpa [Matrix.mulVec, dotProduct, Matrix.map_apply] using this
      · simp [hv']
    have h0 := hW _ key
    funext j
    have := congrFun (congrFun h0 j) v
    simpa using this
  choose P hP using hv
  let Q : Matrix n m (∀ v, K v) := fun i j v => P v i j
  refine ⟨Q, ?_⟩
  funext i j v
  have := congrFun (congrFun (hP v) i) j
  simp only [Matrix.mul_apply, Matrix.map_apply] at this
  rw [Matrix.mul_apply, Finset.sum_apply]
  show ∑ k, P v i k * W k j v = _
  rw [this]
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem inj_of_isUnit {R : Type} [CommRing R] {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq n] (W : Matrix m n R) (P : Matrix n m R) (hP : IsUnit (P * W).det)
    (c : n → R) (hc : W *ᵥ c = 0) : c = 0 := by
  have h1 : (P * W) *ᵥ c = 0 := by rw [← Matrix.mulVec_mulVec, hc, Matrix.mulVec_zero]
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hP
  have h2 : ((u⁻¹ : (Matrix n n R)ˣ) : Matrix n n R) *ᵥ ((P * W) *ᵥ c) = c := by
    rw [Matrix.mulVec_mulVec, ← hu, Units.inv_mul, Matrix.one_mulVec]
  rw [← h2, h1, Matrix.mulVec_zero]

variable {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)

def wMat (R : Type) [CommRing R] [Algebra F R] {a M : ℕ} (X : Fin a → Fin M → R ⊗[F] E) :
    Matrix (Fin M × Fin d) (Fin a × Fin d) R :=
  fun p q => crd b R (((1 : R) ⊗ₜ[F] b q.2) * X q.1 p.1) p.2

/- English proof (translation)
Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem wMat_mulVec (R : Type) [CommRing R] [Algebra F R] {a M : ℕ}
    (X : Fin a → Fin M → R ⊗[F] E) (c : Fin a × Fin d → R) (j : Fin M) (l : Fin d) :
    (wMat b R X *ᵥ c) (j, l) =
      crd b R (∑ i, (∑ k, c (i, k) • ((1 : R) ⊗ₜ[F] b k)) * X i j) l := by
  simp only [Matrix.mulVec, dotProduct, wMat, crd, Fintype.sum_prod_type, Finset.sum_mul,
    smul_mul_assoc, map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => mul_comm _ _

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules.
-/
theorem wMat_mulVec_eq_zero (R : Type) [CommRing R] [Algebra F R] {a M : ℕ}
    (X : Fin a → Fin M → R ⊗[F] E) (c : Fin a × Fin d → R) :
    wMat b R X *ᵥ c = 0 ↔ ∀ j, ∑ i, (∑ k, c (i, k) • ((1 : R) ⊗ₜ[F] b k)) * X i j = 0 := by
  constructor
  · intro h j
    apply (Algebra.TensorProduct.basis R b).repr.injective
    ext l
    have := congrFun h (j, l)
    rw [wMat_mulVec] at this
    simpa [crd] using this
  · intro h
    funext p
    rw [wMat_mulVec, h p.1]
    simp [crd]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem linIndep_iff (R : Type) [CommRing R] [Algebra F R] {a M : ℕ}
    (X : Fin a → Fin M → R ⊗[F] E) :
    LinearIndependent (R ⊗[F] E) X ↔ ∀ c, wMat b R X *ᵥ c = 0 → c = 0 := by
  set B := Algebra.TensorProduct.basis R b with hB
  have hBk : ∀ k, B k = (1 : R) ⊗ₜ[F] b k := fun k => Algebra.TensorProduct.basis_apply _ _
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro hX c hc
    rw [wMat_mulVec_eq_zero] at hc
    have h0 := hX (fun i => ∑ k, c (i, k) • ((1 : R) ⊗ₜ[F] b k)) (by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      exact hc j)
    funext p
    have h1 := h0 p.1
    have h2 : B.equivFun (∑ k, c (p.1, k) • B k) = fun k => c (p.1, k) := by
      rw [← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
    simp only [hBk] at h2
    rw [h1, map_zero] at h2
    exact (congrFun h2 p.2).symm
  · intro hW g hg i
    have hc := hW (fun p => B.repr (g p.1) p.2) (by
      rw [wMat_mulVec_eq_zero]
      intro j
      have e : ∀ i, ∑ k, B.repr (g i) k • ((1 : R) ⊗ₜ[F] b k) = g i := by
        intro i
        simp only [← hBk]
        exact B.sum_repr (g i)
      simp only [e]
      have := congrFun hg j
      simpa [Finset.sum_apply, smul_eq_mul] using this)
    rw [← B.sum_repr (g i)]
    simp [fun k => congrFun hc (i, k)]

section Top

variable [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
  [IsTopologicalRing R]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem continuous_wMat {a M : ℕ} :
    Continuous (fun X : Fin a → Fin M → R ⊗[F] E => wMat b R X) := by
  refine continuous_pi fun p => continuous_pi fun q => ?_
  exact (continuous_crd b R p.2).comp
    (continuous_const.mul ((continuous_apply p.1).comp (continuous_apply q.1)))

include b in
/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem isOpen_linIndep (hU : IsOpen {r : R | IsUnit r}) (hL : LIP R) {a M : ℕ} :
    IsOpen {X : Fin a → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} := by
  have e : {X : Fin a → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} =
      ⋃ P : Matrix (Fin a × Fin d) (Fin M × Fin d) R,
        (fun X => (P * wMat b R X).det) ⁻¹' {r | IsUnit r} := by
    ext X
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage]
    rw [linIndep_iff b]
    constructor
    · intro h
      obtain ⟨P, hP⟩ := hL _ _ _ h
      exact ⟨P, by rw [hP, Matrix.det_one]; exact isUnit_one⟩
    · rintro ⟨P, hP⟩ c hc
      exact inj_of_isUnit _ P hP c hc
  rw [e]
  exact isOpen_iUnion fun P =>
    hU.preimage ((continuous_const.matrix_mul (continuous_wMat b R)).matrix_det)

end Top

end TensAllW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW TensAllW

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem tensFacts_of {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (a : ℕ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R]
    [SecondCountableTopology R] (hU : IsOpen {r : R | IsUnit r}) (hL : LIP R) :
    TensFacts F E σ M J a R :=
  ⟨inferInstance, inferInstance, inferInstance, isClosed_HermR R σ a, continuous_gramR R σ J,
    gramR_mem R σ hσ J hJ, isOpen_linIndep (Module.finBasis F E) R hU hL⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lip_ainf (F : Type) [Field F] [NumberField F] : LIP (InfiniteAdeleRing F) := by
  classical
  exact lip_pi (fun v : InfinitePlace F => v.Completion) (fun v => lip_field _)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem tensAll_holds : TensAll := by
  intro F E _ _ _ _ _ σ hCM M J hJ _ _ a _ _ X0 hT hdet
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  refine ⟨?_, fun v => ?_⟩
  · exact tensFacts_of σ hσ J hJ.1 a (Ainf F) (isOpen_units_Ainf F) (lip_ainf F)
  · have := secondCountable_Fv F v
    have := locallyCompact_Fv F v
    exact tensFacts_of σ hσ J hJ.1 a (Fv F v) (isOpen_units_Fv F v) (lip_field _)

end PI.VolStabS
