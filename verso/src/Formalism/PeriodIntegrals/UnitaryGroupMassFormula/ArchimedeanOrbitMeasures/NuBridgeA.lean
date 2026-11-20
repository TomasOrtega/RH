import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.LamCut
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ContinuousThetaInf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DensNu
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DensMu
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.FibInv

noncomputable section

namespace PI.AprimeInfW.NuB

open MeasureTheory Topology Filter Metric NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal Formalism.MainNotions.S Formalism.L2.SG.AdBridge
open scoped TensorProduct Matrix ComplexConjugate

section Tr

variable {D : D7} (X : HidaSetting D)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem emb_real (v : InfinitePlace X.B.I.F) (a : X.B.I.F) : conj (v.embedding a) = v.embedding a := by
  have hv : v.IsReal := totReal_of X v
  have h := NumberField.ComplexEmbedding.isReal_iff.1 (InfinitePlace.isReal_iff.1 hv)
  have := RingHom.congr_fun h a
  simpa [NumberField.ComplexEmbedding.conjugate_coe_eq] using this

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem phi_star (v : InfinitePlace X.B.I.F) (e : X.B.I.E) : X.B.I.φ v (star e) = conj (X.B.I.φ v e) :=
  X.B.I.cm.cmUnram.2.1 _ e

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem phi_notReal (v : InfinitePlace X.B.I.F) : ¬ ∀ e : X.B.I.E, conj (X.B.I.φ v e) = X.B.I.φ v e := by
  intro h
  have hr : NumberField.ComplexEmbedding.IsReal (X.B.I.φ v) := by
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext e
    simp [NumberField.ComplexEmbedding.conjugate_coe_eq, h e]
  have hc := X.B.I.cm.cmUnram.1.isComplex (InfinitePlace.mk (X.B.I.φ v))
  exact (InfinitePlace.not_isReal_iff_isComplex.2 hc) (InfinitePlace.isReal_mk_iff.2 hr)

/- English proof (translation)
Equip the data with the indicated structure. Introduce a local definition for the expression. Introduce a local definition for the expression. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Use symmetry to reverse the relation. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem emb_trace (v : InfinitePlace X.B.I.F) (e : X.B.I.E) :
    v.embedding (Algebra.trace X.B.I.F X.B.I.E e) = X.B.I.φ v e + conj (X.B.I.φ v e) := by
  classical
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  letI : Algebra X.B.I.F ℂ := v.embedding.toAlgebra
  let φA : X.B.I.E →ₐ[X.B.I.F] ℂ := { X.B.I.φ v with commutes' := X.B.I.φ_over v }
  let ψA : X.B.I.E →ₐ[X.B.I.F] ℂ :=
    { (starRingEnd ℂ).comp (X.B.I.φ v) with
      commutes' := fun a => by
        show conj (X.B.I.φ v (algebraMap X.B.I.F X.B.I.E a)) = v.embedding a
        rw [X.B.I.φ_over, emb_real] }
  have hne : φA ≠ ψA := by
    intro h
    apply phi_notReal X v
    intro e
    have := congrArg (fun f : X.B.I.E →ₐ[X.B.I.F] ℂ => f e) h
    exact this.symm
  have hcard : Fintype.card (X.B.I.E →ₐ[X.B.I.F] ℂ) = 2 := by
    rw [AlgHom.card X.B.I.F X.B.I.E ℂ, X.B.I.cm.deg2]
  have huniv : (Finset.univ : Finset (X.B.I.E →ₐ[X.B.I.F] ℂ)) = {φA, ψA} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, hcard, Finset.card_pair hne]
  have h := trace_eq_sum_embeddings (K := X.B.I.F) (L := X.B.I.E) ℂ (x := e)
  rw [huniv, Finset.sum_pair hne] at h
  exact h

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem evInf_conj (v : InfinitePlace X.B.I.F) (a : Ainf X.B.I.F) :
    conj (PI.AprimeInfU.evInf X v a) = PI.AprimeInfU.evInf X v a := by
  have hv : v.IsReal := totReal_of X v
  show conj (InfinitePlace.Completion.extensionEmbedding v (a v)) =
    InfinitePlace.Completion.extensionEmbedding v (a v)
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hv]
  exact Complex.conj_ofReal _

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem evInf_alg (v : InfinitePlace X.B.I.F) (a : X.B.I.F) :
    PI.AprimeInfU.evInf X v (algebraMap X.B.I.F (Ainf X.B.I.F) a) = v.embedding a :=
  evV_algebraMap X.B.I v a

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem trace_one_tmul (e : X.B.I.E) :
    Algebra.trace (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) ((1 : Ainf X.B.I.F) ⊗ₜ[X.B.I.F] e) =
      algebraMap X.B.I.F (Ainf X.B.I.F) (Algebra.trace X.B.I.F X.B.I.E e) := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  rw [Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange, ← Algebra.trace_apply]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Treat this case separately. Expand and normalize the polynomial expressions, which then agree.
-/
theorem evInf_trace (v : InfinitePlace X.B.I.F) (z : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) :
    PI.AprimeInfU.evInf X v (Algebra.trace (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) z) =
      PI.AprimeInfU.thetaInf X v z + conj (PI.AprimeInfU.thetaInf X v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    have h1 : a ⊗ₜ[X.B.I.F] e = a • ((1 : Ainf X.B.I.F) ⊗ₜ[X.B.I.F] e) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h1, map_smul, trace_one_tmul, smul_eq_mul, map_mul, evInf_alg, emb_trace, ← h1, thetaInf_tmul, map_mul,
      evInf_conj]
    ring
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]; ring

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Treat this case separately.
-/
theorem theta_sigR (v : InfinitePlace X.B.I.F) (t : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) :
    PI.AprimeInfU.thetaInf X v (sigR (Ainf X.B.I.F) X.B.I.cm.sig t) = conj (PI.AprimeInfU.thetaInf X v t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    have h : sigR (Ainf X.B.I.F) X.B.I.cm.sig (a ⊗ₜ[X.B.I.F] e) = a ⊗ₜ[X.B.I.F] (star e) := rfl
    rw [h, thetaInf_tmul, thetaInf_tmul, map_mul, evInf_conj, phi_star]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem theta_alg (v : InfinitePlace X.B.I.F) (q : X.B.I.F) :
    PI.AprimeInfU.thetaInf X v (algebraMap X.B.I.F (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) q) = v.embedding q := by
  rw [Algebra.TensorProduct.algebraMap_apply, thetaInf_tmul, evInf_alg, map_one, mul_one]

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem theta_surj (z : InfinitePlace X.B.I.F → ℂ) :
    ∃ y : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E, ∀ v, PI.AprimeInfU.thetaInf X v y = z v := by
  classical
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  let b : Module.Basis (Fin 2) X.B.I.F X.B.I.E := Module.finBasisOfFinrankEq X.B.I.F X.B.I.E X.B.I.cm.deg2
  have hr : ∀ v : InfinitePlace X.B.I.F, ∃ r : Fin 2 → ℝ,
      (r 0 : ℂ) * X.B.I.φ v (b 0) + (r 1 : ℂ) * X.B.I.φ v (b 1) = z v := by
    intro v
    let f : Fin 2 → ℂ := ![X.B.I.φ v (b 0), X.B.I.φ v (b 1)]
    have hli : LinearIndependent ℝ f := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      rw [Fin.sum_univ_two] at hg
      have key := theta_lin_indep (X.B.I.φ v) (X.B.I.cm.sig : X.B.I.E →+* X.B.I.E)
        (fun a => X.B.I.cm.cmUnram.2.1 (X.B.I.φ v) a)
        (fun a ha => RingHom.mem_range.1 ((X.B.I.cm.fixed a).1 ha)) b g (by
          simpa [f, Complex.real_smul] using hg)
      intro i
      fin_cases i
      · exact key.1
      · exact key.2
    have hsp : Submodule.span ℝ (Set.range f) = ⊤ :=
      hli.span_eq_top_of_card_eq_finrank (by simp [Complex.finrank_real_complex])
    have hz : z v ∈ Submodule.span ℝ (Set.range f) := by rw [hsp]; trivial
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hz
    refine ⟨r, ?_⟩
    rw [← hr, Fin.sum_univ_two]
    simp [f, Complex.real_smul]
  choose r hr using hr
  have hv : ∀ v : InfinitePlace X.B.I.F, v.IsReal := fun v => totReal_of X v
  let c : Fin 2 → Ainf X.B.I.F := fun i =>
    (fun w => (InfinitePlace.Completion.ringEquivRealOfIsReal (hv w)).symm (r w i) :
      ∀ w : InfinitePlace X.B.I.F, w.Completion)
  have hc : ∀ i v, PI.AprimeInfU.evInf X v (c i) = (r v i : ℂ) := by
    intro i v
    show InfinitePlace.Completion.extensionEmbedding v
      ((InfinitePlace.Completion.ringEquivRealOfIsReal (hv v)).symm (r v i)) = _
    rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (hv v),
      ← InfinitePlace.Completion.ringEquivRealOfIsReal_apply (hv v), RingEquiv.apply_symm_apply]
  refine ⟨c 0 ⊗ₜ[X.B.I.F] b 0 + c 1 ⊗ₜ[X.B.I.F] b 1, fun v => ?_⟩
  rw [map_add, thetaInf_tmul, thetaInf_tmul, hc, hc, hr]

end Tr

end PI.AprimeInfW.NuB
