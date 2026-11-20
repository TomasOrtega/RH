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
Use `first`. Consider the case `exact @_root_.GlobalTheory.AlgHomEqEval.algHom_eq_eval`. Consider the case `exact _root_.GlobalTheory.AlgHomEqEval.algHom_eq_eval`. Consider the case `(apply _root_.GlobalTheory.AlgHomEqEval.algHom_eq_eval <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.AlgHomEqEval.algHom_eq_eval <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.AlgHomEqEval.algHom_eq_eval <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.AlgHomEqEval.algHom_eq_eval ..)`.
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
Set `b` to `Pi.basisFun K P`. Rewrite using `[Algebra.trace_eq_matrix_trace b, Matrix.trace]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Simplify using `[Algebra.leftMulMatrix_eq_repr_mul, b, Pi.single_apply]`.
-/
theorem trace_pi_self {K : Type} [Field K] {P : Type} [Fintype P] [DecidableEq P] (z : P → K) :
    Algebra.trace K (P → K) z = ∑ p, z p := by
  let b := Pi.basisFun K P
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [Algebra.leftMulMatrix_eq_repr_mul, b, Pi.single_apply]

/- English proof (translation)
Introduce `R B _ _ _ hfin het b`. Establish `: Module.FinitePresentation R B` using `.of_finite_of_finitePresentation R B`. Establish `: Module.Flat R B` using `inferInstance`. Establish `: Module.Projective R B` using `Module.Flat.projective_of_finitePresentation`. Take `⟨n, f, g, -, -, hfg⟩` from `Module.Finite.exists_comp_eq_id_of_projective R B`.

Use `⟨LinearMap.trace R _ (g ∘ₗ Algebra.lmul R B b ∘ₗ f), fun Ω _ _ φ => ?_⟩` and prove the remaining obligations. Use `letI := φ.toAlgebra`. Establish `hφ : algebraMap R Ω = φ` using `rfl`. Establish `step1 : φ (LinearMap.trace R _ (g ∘ₗ Algebra.lmul R B b ∘ₗ f)) = Algebra.trace Ω (Ω ⊗[R] B) (1 ⊗ₜ b)`. Rewrite using `[← hφ, ← LinearMap.trace_baseChange, LinearMap.baseChange_comp, LinearMap.baseChange_comp, LinearMap.trace_comp_comm', LinearMap.comp_assoc, ← LinearMap.baseChange_comp, hfg, LinearMap.baseChange_id, LinearMap.comp_id, Algebra.trace_apply, Algebra.baseChange_lmul]`.

Rewrite using `[step1]`. Use `set e := Algebra.FormallyEtale.equivPiOfIsSepClosed Ω (Ω ⊗[R] B) with he`. Use `haveI : Module.Finite Ω (PrimeSpectrum (Ω ⊗[R] B) → Ω) := Module.Finite.equiv e.toLinearEquiv`. Use `haveI : IsArtinianRing (Ω ⊗[R] B) := isArtinian_of_tower Ω inferInstance`. Use `haveI : Finite (PrimeSpectrum (Ω ⊗[R] B)) := inferInstance`.

Use `haveI : Fintype (PrimeSpectrum (Ω ⊗[R] B)) := Fintype.ofFinite _`. Rewrite using `[← Algebra.trace_eq_of_algEquiv e, trace_pi_self]`. Set `S` to `{χ : B →+* Ω // χ.comp (algebraMap R B) = φ}`. Set `G : PrimeSpectrum (Ω ⊗[R] B) → (B →ₐ[R] Ω)` to `fun p => (((Pi.evalAlgHom Ω (fun _ => Ω) p).comp (e : Ω ⊗[R] B →ₐ[Ω] _)).restrictScalars R).comp Algebra.TensorProduct.includeRight`. Set `F : PrimeSpectrum (Ω ⊗[R] B) → S` to `fun p => ⟨(G p).toRingHom, RingHom.ext fun r => (G p).commutes r⟩`.

Establish `hF : ∀ p y, (F p).1 y = e (1 ⊗ₜ y) p` using `fun p y => rfl`. Establish `hinj : Function.Injective F`. Introduce `p q h`. Establish `h' : ∀ y : B, e (1 ⊗ₜ y) p = e (1 ⊗ₜ y) q` using `fun y => by`. Rewrite using `[← hF, ← hF, h]`.

Establish `h'' : ∀ x, e x p = e x q`. Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a y`.

Rewrite using `[show a ⊗ₜ[R] y = a • (1 ⊗ₜ[R] y : Ω ⊗[R] B) by`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one], map_smul, Pi.smul_apply,`. Use the proof step `Pi.smul_apply, h' y]`. Consider the case `add x y hx hy => rw [map_add, Pi.add_apply, Pi.add_apply, hx, hy]`. Use `h'' (e.symm (Pi.single p 1))` as an intermediate fact.

Rewrite `this` using `[e.apply_symm_apply, Pi.single_eq_same]`. Assume the negation of the conclusion as `hne`. Rewrite `this` using `[Pi.single_eq_of_ne (Ne.symm hne)]`. Conclude with `one_ne_zero this`. Establish `hsurj : Function.Surjective F`.

Introduce and unpack `⟨χ, hχ⟩`. Set `χ' : B →ₐ[R] Ω` to `{ χ with commutes' := fun r => RingHom.congr_fun hχ r }`. Set `ψ : Ω ⊗[R] B →ₐ[Ω] Ω` to `AlgHom.liftEquiv R Ω B Ω χ'`. Take `⟨p, hp⟩` from `exists_eq_eval (ψ.comp e.symm.toAlgHom)`. Use `⟨p, Subtype.ext (RingHom.ext fun y => ?_)⟩` and prove the remaining obligations.

Rewrite using `[hF, ← hp (e (1 ⊗ₜ y))]`. Simplify using `[ψ, χ']`. Rewrite using `[← finsum_comp_equiv (Equiv.ofBijective F ⟨hinj, hsurj⟩), finsum_eq_sum_of_fintype]`. Both sides reduce to the same expression.
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
