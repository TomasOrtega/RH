import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgHomEqEval
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

noncomputable section

namespace GlobalTheory.EtaleTraceGeom

open TensorProduct

/- English proof (translation)
Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately.

Treat this case separately. A detailed English derivation is pending.
-/
theorem exists_eq_eval {K : Type} [Field K] {P : Type} [Fintype P] [DecidableEq P]
    (θ : (P → K) →ₐ[K] K) : ∃ p : P, ∀ z : P → K, θ z = z p := by
  first
  | exact @_root_.GlobalTheory.AlgHomEqEval.algHom_eq_eval
  | exact _root_.GlobalTheory.AlgHomEqEval.algHom_eq_eval
  | (apply _root_.GlobalTheory.AlgHomEqEval.algHom_eq_eval <;> assumption)
  | (intros; apply _root_.GlobalTheory.AlgHomEqEval.algHom_eq_eval <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AlgHomEqEval.algHom_eq_eval <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AlgHomEqEval.algHom_eq_eval ..)

/- English proof (translation)
Introduce a local definition for the expression. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
-/
theorem trace_pi_self {K : Type} [Field K] {P : Type} [Fintype P] [DecidableEq P] (z : P → K) :
    Algebra.trace K (P → K) z = ∑ p, z p := by
  let b := Pi.basisFun K P
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [Algebra.leftMulMatrix_eq_repr_mul, b, Pi.single_apply]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Equip the data with the indicated structure. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Introduce a local definition for the expression. Introduce a local definition for the expression.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Treat this case separately. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Assume the negation of the conclusion and derive a contradiction. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Assume the hypotheses and unpack their components. Introduce a local definition for the expression.

Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem exists_trace_eq_finsum : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B], Module.Finite R B →
    Algebra.Etale R B → ∀ b : B, ∃ v : R, ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (φ : R →+* Ω),
      φ v = ∑ᶠ χ : {χ : B →+* Ω // χ.comp (algebraMap R B) = φ}, χ.1 b := by
  intro R B _ _ _ hfin het b
  classical
  have : Module.FinitePresentation R B := .of_finite_of_finitePresentation R B
  have : Module.Flat R B := inferInstance
  have : Module.Projective R B := Module.Flat.projective_of_finitePresentation
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R B
  refine ⟨LinearMap.trace R _ (g ∘ₗ Algebra.lmul R B b ∘ₗ f), fun Ω _ _ φ => ?_⟩
  letI := φ.toAlgebra
  have hφ : algebraMap R Ω = φ := rfl

  have step1 : φ (LinearMap.trace R _ (g ∘ₗ Algebra.lmul R B b ∘ₗ f)) =
      Algebra.trace Ω (Ω ⊗[R] B) (1 ⊗ₜ b) := by
    rw [← hφ, ← LinearMap.trace_baseChange, LinearMap.baseChange_comp, LinearMap.baseChange_comp,
      LinearMap.trace_comp_comm', LinearMap.comp_assoc, ← LinearMap.baseChange_comp, hfg,
      LinearMap.baseChange_id, LinearMap.comp_id, Algebra.trace_apply, Algebra.baseChange_lmul]
  rw [step1]
  set e := Algebra.FormallyEtale.equivPiOfIsSepClosed Ω (Ω ⊗[R] B) with he
  haveI : Module.Finite Ω (PrimeSpectrum (Ω ⊗[R] B) → Ω) := Module.Finite.equiv e.toLinearEquiv
  haveI : IsArtinianRing (Ω ⊗[R] B) := isArtinian_of_tower Ω inferInstance
  haveI : Finite (PrimeSpectrum (Ω ⊗[R] B)) := inferInstance
  haveI : Fintype (PrimeSpectrum (Ω ⊗[R] B)) := Fintype.ofFinite _
  rw [← Algebra.trace_eq_of_algEquiv e, trace_pi_self]
  let S := {χ : B →+* Ω // χ.comp (algebraMap R B) = φ}
  let G : PrimeSpectrum (Ω ⊗[R] B) → (B →ₐ[R] Ω) := fun p =>
    (((Pi.evalAlgHom Ω (fun _ => Ω) p).comp (e : Ω ⊗[R] B →ₐ[Ω] _)).restrictScalars R).comp
      Algebra.TensorProduct.includeRight
  let F : PrimeSpectrum (Ω ⊗[R] B) → S := fun p =>
    ⟨(G p).toRingHom, RingHom.ext fun r => (G p).commutes r⟩
  have hF : ∀ p y, (F p).1 y = e (1 ⊗ₜ y) p := fun p y => rfl
  have hinj : Function.Injective F := by
    intro p q h
    have h' : ∀ y : B, e (1 ⊗ₜ y) p = e (1 ⊗ₜ y) q := fun y => by
      rw [← hF, ← hF, h]
    have h'' : ∀ x, e x p = e x q := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a y =>
        rw [show a ⊗ₜ[R] y = a • (1 ⊗ₜ[R] y : Ω ⊗[R] B) by
          rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one], map_smul, Pi.smul_apply,
          Pi.smul_apply, h' y]
      | add x y hx hy => rw [map_add, Pi.add_apply, Pi.add_apply, hx, hy]
    have := h'' (e.symm (Pi.single p 1))
    rw [e.apply_symm_apply, Pi.single_eq_same] at this
    by_contra hne
    rw [Pi.single_eq_of_ne (Ne.symm hne)] at this
    exact one_ne_zero this
  have hsurj : Function.Surjective F := by
    rintro ⟨χ, hχ⟩
    let χ' : B →ₐ[R] Ω := { χ with commutes' := fun r => RingHom.congr_fun hχ r }
    let ψ : Ω ⊗[R] B →ₐ[Ω] Ω := AlgHom.liftEquiv R Ω B Ω χ'
    obtain ⟨p, hp⟩ := exists_eq_eval (ψ.comp e.symm.toAlgHom)
    refine ⟨p, Subtype.ext (RingHom.ext fun y => ?_)⟩
    rw [hF, ← hp (e (1 ⊗ₜ y))]
    simp [ψ, χ']
  rw [← finsum_comp_equiv (Equiv.ofBijective F ⟨hinj, hsurj⟩), finsum_eq_sum_of_fintype]
  rfl

end GlobalTheory.EtaleTraceGeom
