import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.DefsObj
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.JGenLinLie
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.CapHCMem

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Treat this case separately.

Treat this case separately. A detailed English derivation is pending.
-/
private theorem UpperTheory.ConvolutionTheory.Dp.capZc_mem_of_e {n : ℕ} (S : Subalgebra ℂ (HarishChandra.U n))
    (h : ∀ a b, HarishChandra.e (a, b) ∈ S) (x : HarishChandra.U n) : x ∈ S := by
  induction x using HarishChandra.U.induction with
  | halg r => exact S.algebraMap_mem r
  | hι X =>
    rw [HarishChandra.ι_eq_sum_e]
    exact S.sum_mem fun a _ => S.smul_mem (h a.1 a.2) _
  | hmul a b ha hb => exact S.mul_mem ha hb
  | hadd a b ha hb => exact S.add_mem ha hb

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
private theorem UpperTheory.ConvolutionTheory.Dp.capZc_prod (n : ℕ) (u : ℂ) :
    (∏ k : Fin n, (MvPolynomial.C u + MvPolynomial.X k) : MvPolynomial (Fin n) ℂ) =
      u ^ n • (1 : MvPolynomial (Fin n) ℂ) +
        ∑ i : Fin n, u ^ (n - (i + 1)) • MvPolynomial.esymm (Fin n) ℂ (i + 1) := by
  have h := congrArg (Polynomial.eval (MvPolynomial.C u : MvPolynomial (Fin n) ℂ))
    (MvPolynomial.prod_C_add_X_eq_sum_esymm ℂ (Fin n))
  simp only [Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow, Fintype.card_fin] at h
  rw [h, Finset.sum_range_succ', add_comm, ← Fin.sum_univ_eq_sum_range
    (fun i => MvPolynomial.esymm (Fin n) ℂ (i + 1) * MvPolynomial.C u ^ (n - (i + 1))) n]
  congr 1
  · rw [MvPolynomial.esymm_zero, MvPolynomial.smul_eq_C_mul, map_pow, Nat.sub_zero, mul_comm]
  · exact Finset.sum_congr rfl fun i _ => by rw [MvPolynomial.smul_eq_C_mul, map_pow, mul_comm]

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
private theorem UpperTheory.ConvolutionTheory.Dp.capZc_center {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}
    {z : Cm.UC E n} (h : ∀ τ i j, Cm.genC τ i j * z = z * Cm.genC τ i j) :
    z ∈ Subalgebra.center ℂ (Cm.UC E n) := by
  have : Algebra.adjoin ℂ {x : Cm.UC E n | ∃ τ i j, x = Cm.genC τ i j} ≤ Subalgebra.centralizer ℂ {z} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨τ, i, j, rfl⟩ _ rfl
    exact (h τ i j).symm
  exact Subalgebra.mem_center_iff.2 fun x =>
    (this (Cm.adjoin_genC (E := E) (a := n) ▸ Algebra.mem_top) z rfl).symm

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Both sides reduce to the same expression.

A detailed English derivation is pending.
-/
theorem UpperTheory.ConvolutionTheory.Dp.capZc :
    UpperTheory.ConvolutionTheory.Dp.CapZc := by
  intro E _ _ _ n τ
  obtain ⟨⟨j, hj⟩, hiff⟩ := UpperTheory.ConvolutionTheory.Dp.jGen E n τ
  have hg := (hiff j).1 hj
  set w : Fin n → Subalgebra.center ℂ (HarishChandra.U n) := fun i =>
    (HarishChandra.harishChandraEquiv (n := n)).symm
      ⟨MvPolynomial.esymm (Fin n) ℂ (i + 1), MvPolynomial.esymm_isSymmetric (Fin n) ℂ (i + 1)⟩ with hw
  have hzc : ∀ i : Fin n, UpperTheory.ConvolutionTheory.zc τ i = j (w i) := fun i => by
    obtain ⟨j', hj', e⟩ := Classical.epsilon_spec
      (p := fun z => ∃ j, UpperTheory.ConvolutionTheory.IsJ τ j ∧ z = j (w i : HarishChandra.U n)) ⟨_, j, hj, rfl⟩
    refine e.trans ?_
    exact capZc_mem_of_e (AlgHom.equalizer j' j) (fun a b => ((hiff j').1 hj' a b).trans (hg a b).symm) _
  have hwH : ∀ i, HarishChandra.harishChandraHom (w i) = MvPolynomial.esymm (Fin n) ℂ (i + 1) := fun i => by
    rw [← HarishChandra.harishChandraEquiv_apply, hw, AlgEquiv.apply_symm_apply]
  refine ⟨fun i => ?_, fun u => ?_⟩
  · rw [hzc]
    refine capZc_center fun σ a b => ?_
    by_cases e : σ = τ
    · subst e
      rw [← hg]
      exact (map_mul j _ _).symm.trans
        ((congrArg j (Subalgebra.mem_center_iff.1 (w i).2 _)).trans (map_mul j _ _))
    · have := capZc_mem_of_e ((Subalgebra.centralizer ℂ {Cm.genC σ a b}).comap j) (fun c d => by
        rintro _ rfl
        rw [RingHom.coe_coe, hg]
        exact Cm.commute_genC e a b c d) (w i)
      exact this _ rfl
  · obtain ⟨z, hz, hH⟩ := UpperTheory.ConvolutionTheory.Dp.capHC n u
    have e : z = u ^ n • 1 + ∑ i : Fin n, u ^ (n - (i + 1)) • w i := by
      apply HarishChandra.harishChandraHom_injective
      rw [hH, capZc_prod]
      simp only [map_add, map_smul, map_one, map_sum, hwH]
    have e2 := congrArg (j.comp (Subalgebra.center ℂ (HarishChandra.U n)).val) e
    simp only [map_add, map_smul, map_one, map_sum] at e2
    simp only [hzc]
    refine Eq.trans ?_ e2
    change _ = j (z : HarishChandra.U n)
    rw [hz, Fb.map_qdet]
    simp only [hg]
    rfl
