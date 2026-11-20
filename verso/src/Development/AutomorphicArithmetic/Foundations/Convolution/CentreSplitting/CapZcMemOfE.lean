import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.DefsObj
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.JGenLinLie
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.CapHCMem

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

/- English proof (translation)
Proceed by induction on `x using HarishChandra.U.induction with`. Consider the case `halg r => exact S.algebraMap_mem r`. Consider the case `hι X`. Rewrite using `[HarishChandra.ι_eq_sum_e]`. Conclude with `S.sum_mem fun a _ => S.smul_mem (h a.1 a.2) _`.

Consider the case `hmul a b ha hb => exact S.mul_mem ha hb`. Consider the case `hadd a b ha hb => exact S.add_mem ha hb`.
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
Establish `h` using `congrArg (Polynomial.eval (MvPolynomial.C u : MvPolynomial (Fin n) ℂ)) (MvPolynomial.prod_C_add_X_eq_sum_esymm ℂ (Fin n))`. Simplify using `only [Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow, Fintype.card_fin] at h`. Rewrite using `[h, Finset.sum_range_succ', add_comm, ← Fin.sum_univ_eq_sum_range (fun i => MvPolynomial.esymm (Fin n) ℂ (i + 1) * MvPolynomial.C u ^ (n - (i + 1))) n]`. Use `congr 1`. Rewrite using `[MvPolynomial.esymm_zero, MvPolynomial.smul_eq_C_mul, map_pow, Nat.sub_zero, mul_comm]`.

Conclude with `Finset.sum_congr rfl fun i _ => by rw [MvPolynomial.smul_eq_C_mul, map_pow, mul_comm]`.
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
Establish `: Algebra.adjoin ℂ {x : Cm.UC E n | ∃ τ i j, x = Cm.genC τ i j} ≤ Subalgebra.centralizer ℂ {z}`. Use `Algebra.adjoin_le ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨τ, i, j, rfl⟩ _ rfl`. Conclude with `(h τ i j).symm`. Conclude with `Subalgebra.mem_center_iff.2 fun x => (this (Cm.adjoin_genC (E := E) (a := n) ▸ Algebra.mem_top) z rfl).symm`.
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
Introduce `E _ _ _ n τ`. Take `⟨⟨j, hj⟩, hiff⟩` from `UpperTheory.ConvolutionTheory.Dp.jGen E n τ`. Establish `hg` using `(hiff j).1 hj`. Use `set w : Fin n → Subalgebra.center ℂ (HarishChandra.U n) := fun i => (HarishChandra.harishChandraEquiv (n := n)).symm ⟨MvPolynomial.esymm (Fin n) ℂ (i + 1), MvPolynomial.esymm_isSymmetric (Fin n) ℂ (i + 1)⟩ with hw`. Establish `hzc : ∀ i : Fin n, UpperTheory.ConvolutionTheory.zc τ i = j (w i)` using `fun i => by`.

Take `⟨j', hj', e⟩` from `Classical.epsilon_spec (p := fun z => ∃ j, UpperTheory.ConvolutionTheory.IsJ τ j ∧ z = j (w i : HarishChandra.U n)) ⟨_, j, hj, rfl⟩`. Use `e.trans ?_` and prove the remaining obligations. Conclude with `capZc_mem_of_e (AlgHom.equalizer j' j) (fun a b => ((hiff j').1 hj' a b).trans (hg a b).symm) _`. Establish `hwH : ∀ i, HarishChandra.harishChandraHom (w i) = MvPolynomial.esymm (Fin n) ℂ (i + 1)` using `fun i => by`. Rewrite using `[← HarishChandra.harishChandraEquiv_apply, hw, AlgEquiv.apply_symm_apply]`.

Use `⟨fun i => ?_, fun u => ?_⟩` and prove the remaining obligations. Rewrite using `[hzc]`. Use `capZc_center fun σ a b => ?_` and prove the remaining obligations. Distinguish the cases in `e : σ = τ`. Substitute `e` using the available equality.

Rewrite using `[← hg]`. Conclude with `(map_mul j _ _).symm.trans ((congrArg j (Subalgebra.mem_center_iff.1 (w i).2 _)).trans (map_mul j _ _))`. Use `capZc_mem_of_e ((Subalgebra.centralizer ℂ {Cm.genC σ a b}).comap j) (fun c d => by` as an intermediate fact. Introduce and unpack `_ rfl`. Rewrite using `[RingHom.coe_coe, hg]`.

Conclude with `Cm.commute_genC e a b c d) (w i)`. Conclude with `this _ rfl`. Take `⟨z, hz, hH⟩` from `UpperTheory.ConvolutionTheory.Dp.capHC n u`. Establish `e : z = u ^ n • 1 + ∑ i : Fin n, u ^ (n - (i + 1)) • w i`. Apply `HarishChandra.harishChandraHom_injective` to reduce the goal to its premises.

Rewrite using `[hH, capZc_prod]`. Simplify using `only [map_add, map_smul, map_one, map_sum, hwH]`. Establish `e2` using `congrArg (j.comp (Subalgebra.center ℂ (HarishChandra.U n)).val) e`. Simplify using `only [map_add, map_smul, map_one, map_sum] at e2`. Simplify using `only [hzc]`.

Use `Eq.trans ?_ e2` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = j (z : HarishChandra.U n)`. Rewrite using `[hz, Fb.map_qdet]`. Simplify using `only [hg]`. Both sides reduce to the same expression.
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
