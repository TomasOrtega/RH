import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ForallAevalLineVanishingIdealIff

set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt

namespace GlobalTheory.CompHt.PointLow

set_option autoImplicit false in
open MvPolynomial in
/- English proof (translation)
Use `conv_lhs => rw [p.as_sum]`. Rewrite using `[map_sum]`. Use `Polynomial.natDegree_sum_le_of_forall_le _ _ fun d hd => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.aeval_monomial]`. Use `Polynomial.natDegree_mul_le.trans ?_` and prove the remaining obligations.

Establish `h0 : (algebraMap R (Polynomial S) (p.coeff d)).natDegree = 0`. Rewrite using `[Polynomial.algebraMap_apply]`. Conclude with `Polynomial.natDegree_C _`. Rewrite using `[h0, zero_add, Finsupp.prod]`. Use `(Polynomial.natDegree_prod_le _ _).trans ?_` and prove the remaining obligations.

Use `le_trans ?_ (MvPolynomial.le_totalDegree hd)` and prove the remaining obligations. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Use `Polynomial.natDegree_pow_le.trans ?_` and prove the remaining obligations. Simplify using `using Nat.mul_le_mul_left (d i) (hs i)`.
-/
private lemma natDegree_aeval_le_totalDegree_of_natDegree_le_one {R S σ : Type} [CommRing R] [CommRing S] [Algebra R S]
    (p : MvPolynomial σ R) (s : σ → Polynomial S) (hs : ∀ i, (s i).natDegree ≤ 1) :
    (MvPolynomial.aeval s p).natDegree ≤ p.totalDegree := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun d hd => ?_
  rw [MvPolynomial.aeval_monomial]
  refine Polynomial.natDegree_mul_le.trans ?_
  have h0 : (algebraMap R (Polynomial S) (p.coeff d)).natDegree = 0 := by
    rw [Polynomial.algebraMap_apply]; exact Polynomial.natDegree_C _
  rw [h0, zero_add, Finsupp.prod]
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  refine le_trans ?_ (MvPolynomial.le_totalDegree hd)
  refine Finset.sum_le_sum fun i _ => ?_
  refine Polynomial.natDegree_pow_le.trans ?_
  simpa using Nat.mul_le_mul_left (d i) (hs i)

set_option autoImplicit false in
open MvPolynomial in

/- English proof (translation)
Introduce `K _ _ N δ y j f hyj hf`. Use `set E := IntermediateField.adjoin K (Set.range y) with hE`. Use `haveI : FiniteDimensional K E := IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)`. Rewrite using `[← AlgHom.card K E (AlgebraicClosure K)]`. Set `yE : Fin N → E` to `fun k => ⟨y k, IntermediateField.subset_adjoin K _ ⟨k, rfl⟩⟩`.

Set `pt : (E →ₐ[K] AlgebraicClosure K) → Fin N → AlgebraicClosure K` to `fun σ k => σ (yE k)`. Establish `hpj : ∀ σ, pt σ j = 1`. Introduce `σ`. Establish `: yE j = 1` using `Subtype.ext hyj`. Simplify using `only [pt, this, map_one]`.

Establish `hzero : ∀ σ, ∀ g ∈ _root_.GlobalTheory.CompHt.coneIdeal K y, MvPolynomial.aeval (pt σ) g = 0`. Introduce `σ g hg`. Establish `hy` using `_root_.GlobalTheory.CompHt.aeval_eq_zero_of_mem_coneIdeal hg`. Establish `hE0 : MvPolynomial.aeval yE g = 0`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `MvPolynomial.comp_aeval_apply yE E.val g` as an intermediate fact. Use `show E.val (MvPolynomial.aeval yE g) = E.val 0`. Rewrite using `[this, map_zero]`. Conclude with `hy`. Use `MvPolynomial.comp_aeval_apply yE σ g` as an intermediate fact.

Rewrite `this` using `[hE0, map_zero]`. Conclude with `this.symm`. Establish `hinj : Function.Injective pt`. Introduce `σ τ h`. Use `IntermediateField.adjoin_algHom_ext K fun x hx => ?_` and prove the remaining obligations.

Take `⟨k, rfl⟩` from `hx`. Conclude with `congrFun h k`. Use `set fΩ := MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f with hfΩ`. Establish `hfΩ0 : fΩ ≠ 0`. Introduce `h`.

Conclude with `hf.ne_zero (MvPolynomial.map_injective _ (algebraMap K (AlgebraicClosure K)).injective (by rw [← hfΩ, h, map_zero]))`. Set `lin : (E →ₐ[K] AlgebraicClosure K) → (E →ₐ[K] AlgebraicClosure K) → MvPolynomial (Fin (0 + 1) × Fin N) (AlgebraicClosure K)` to `fun σ τ => ∑ k, X (0, k) * C (pt σ k - pt τ k)`. Establish `hlin_eval : ∀ σ τ (a : Fin (0 + 1) × Fin N → AlgebraicClosure K), eval a (lin σ τ) = ∑ k, a (0, k) * pt σ k - ∑ k, a (0, k) * pt τ k`. Introduce `σ τ a`. Simplify using `only [lin, map_sum, eval_mul, eval_X, eval_C, ← Finset.sum_sub_distrib, mul_sub]`.

Use `set pairs := Finset.univ.filter fun st : (E →ₐ[K] AlgebraicClosure K) × (E →ₐ[K] AlgebraicClosure K) => st.1 ≠ st.2 with hpairs`. Use `set Q := fΩ * ∏ st ∈ pairs, lin st.1 st.2 with hQ`. Establish `hQ0 : Q ≠ 0`. Use `mul_ne_zero hfΩ0 (Finset.prod_ne_zero_iff.mpr fun st hst => ?_)` and prove the remaining obligations. Establish `hne : st.1 ≠ st.2` using `(Finset.mem_filter.mp hst).2`.

Establish `hpne : pt st.1 ≠ pt st.2` using `fun h => hne (hinj h)`. Take `⟨k, hk⟩` from `Function.ne_iff.mp hpne`. Introduce `h0`. Use `congrArg (eval (Pi.single (0, k) 1)) h0` as an intermediate fact. Rewrite `this` using `[hlin_eval, map_zero]`.

Simplify using `only [Pi.single_apply, Prod.mk.injEq, true_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this`. Conclude with `hk (sub_eq_zero.mp this)`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a, eval a Q ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Conclude with `hQ0 (MvPolynomial.funext fun x => by rw [hcon x, map_zero])`. Establish `hfa : eval a fΩ ≠ 0` using `fun h => ha (by rw [hQ, eval_mul, h, zero_mul])`. Set `c : (E →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K` to `fun σ => ∑ k, a (0, k) * pt σ k`. Establish `hdist : Function.Injective c`. Introduce `σ τ h`.

Assume the negation of the conclusion as `hne`. Apply `ha` to reduce the goal to its premises. Rewrite using `[hQ, eval_mul, map_prod]`. Use `mul_eq_zero_of_right _ (Finset.prod_eq_zero (i := (σ, τ)) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩) ?_)` and prove the remaining obligations. Rewrite using `[hlin_eval]`.

Conclude with `sub_eq_zero.mpr h`. Set `s : Fin (0 + 1) × Fin N → Polynomial (AlgebraicClosure K)` to `fun ik => Polynomial.C (a ik) + if ik.2 = j then Polynomial.X else 0`. Use `set g := MvPolynomial.aeval s f with hg`. Establish `heval : ∀ t, g.eval t = MvPolynomial.aeval (fun ik => a ik + if ik.2 = j then t else 0) f`. Introduce `t`.

Use `MvPolynomial.comp_aeval_apply s ((Polynomial.aeval t).restrictScalars K : Polynomial (AlgebraicClosure K) →ₐ[K] AlgebraicClosure K) f` as an intermediate fact. Rewrite using `[hg, ← Polynomial.coe_aeval_eq_eval, show (Polynomial.aeval t) (MvPolynomial.aeval s f) = ((Polynomial.aeval t).restrictScalars K : Polynomial (AlgebraicClosure K) →ₐ[K] AlgebraicClosure K) (MvPolynomial.aeval s f) from rfl, this]`. Use `congrArg (fun v => MvPolynomial.aeval v f) (funext fun ik => ?_)` and prove the remaining obligations. Simplify using `only [s]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `hg0 : g ≠ 0`. Introduce `h`. Use `heval 0` as an intermediate fact. Rewrite `this` using `[h, Polynomial.eval_zero]`. Establish `h2 : (fun ik : Fin (0 + 1) × Fin N => a ik + if ik.2 = j then (0 : AlgebraicClosure K) else 0) = a`.

Apply the tactic sequence `funext ik; split_ifs <;> simp`. Rewrite `this` using `[h2]`. Apply `hfa` to reduce the goal to its premises. Rewrite using `[hfΩ, MvPolynomial.eval_map, ← MvPolynomial.aeval_def]`. Conclude with `this.symm`.

Establish `hroot : ∀ σ, g.eval (-c σ) = 0`. Introduce `σ`. Rewrite using `[heval]`. Use `(hf.zero_iff _).mpr ⟨pt σ, fun h => by simpa [hpj σ] using congrFun h j, hzero σ, fun i => ?_⟩` and prove the remaining obligations. Take `rfl : i = 0` from `Fin.ext (Nat.lt_one_iff.mp i.isLt)`.

Simplify using `only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, hpj σ, mul_one]`. Simplify using `[c]`. Establish `hcard : Fintype.card (E →ₐ[K] AlgebraicClosure K) ≤ g.roots.toFinset.card`. Rewrite using `[← Finset.card_univ]`. Use `Finset.card_le_card_of_injOn (fun σ => -c σ) (fun σ _ => ?_) ?_` and prove the remaining obligations.

Simplify using `only [Finset.mem_coe, Multiset.mem_toFinset]`. Rewrite using `[Polynomial.mem_roots hg0]`. Conclude with `hroot σ`. Introduce `σ _ τ _ h`. Conclude with `hdist (neg_injective h)`.

Establish `hhom` using `((_root_.GlobalTheory.ChowHt.isMultiHomogeneous_iff_block.mp hf.homog).isHomogeneous)`. Establish `htot : f.totalDegree = δ`. Rewrite using `[hhom.totalDegree hf.ne_zero]`. Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [s]`. Use `split_ifs`. Conclude with `(Polynomial.natDegree_add_le _ _).trans (by simp)`. Simplify using the standard rewrite rules. Use `_ = δ := htot`.
-/
theorem _root_.GlobalTheory.CompHt.PointLow.finrank_le_of_isChowFormInt : ∀ (K : Type) [Field K] [CharZero K] (N δ : ℕ) (y : Fin N → AlgebraicClosure K)
    (j : Fin N) (f : MvPolynomial (Fin (0 + 1) × Fin N) K), y j = 1 → _root_.GlobalTheory.ChowHt.IsChowFormInt (_root_.GlobalTheory.CompHt.coneIdeal K y) 0 δ f →
    Module.finrank K (IntermediateField.adjoin K (Set.range y)) ≤ δ := by
  intro K _ _ N δ y j f hyj hf
  classical
  set E := IntermediateField.adjoin K (Set.range y) with hE
  haveI : FiniteDimensional K E :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  rw [← AlgHom.card K E (AlgebraicClosure K)]
  let yE : Fin N → E := fun k => ⟨y k, IntermediateField.subset_adjoin K _ ⟨k, rfl⟩⟩
  let pt : (E →ₐ[K] AlgebraicClosure K) → Fin N → AlgebraicClosure K := fun σ k => σ (yE k)
  have hpj : ∀ σ, pt σ j = 1 := by
    intro σ
    have : yE j = 1 := Subtype.ext hyj
    simp only [pt, this, map_one]
  have hzero : ∀ σ, ∀ g ∈ _root_.GlobalTheory.CompHt.coneIdeal K y, MvPolynomial.aeval (pt σ) g = 0 := by
    intro σ g hg
    have hy := _root_.GlobalTheory.CompHt.aeval_eq_zero_of_mem_coneIdeal hg
    have hE0 : MvPolynomial.aeval yE g = 0 := by
      apply Subtype.ext
      have := MvPolynomial.comp_aeval_apply yE E.val g
      show E.val (MvPolynomial.aeval yE g) = E.val 0
      rw [this, map_zero]
      exact hy
    have := MvPolynomial.comp_aeval_apply yE σ g
    rw [hE0, map_zero] at this
    exact this.symm
  have hinj : Function.Injective pt := by
    intro σ τ h
    refine IntermediateField.adjoin_algHom_ext K fun x hx => ?_
    obtain ⟨k, rfl⟩ := hx
    exact congrFun h k
  set fΩ := MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f with hfΩ
  have hfΩ0 : fΩ ≠ 0 := by
    intro h
    exact hf.ne_zero (MvPolynomial.map_injective _ (algebraMap K (AlgebraicClosure K)).injective
      (by rw [← hfΩ, h, map_zero]))
  let lin : (E →ₐ[K] AlgebraicClosure K) → (E →ₐ[K] AlgebraicClosure K) →
      MvPolynomial (Fin (0 + 1) × Fin N) (AlgebraicClosure K) :=
    fun σ τ => ∑ k, X (0, k) * C (pt σ k - pt τ k)
  have hlin_eval : ∀ σ τ (a : Fin (0 + 1) × Fin N → AlgebraicClosure K),
      eval a (lin σ τ) = ∑ k, a (0, k) * pt σ k - ∑ k, a (0, k) * pt τ k := by
    intro σ τ a
    simp only [lin, map_sum, eval_mul, eval_X, eval_C, ← Finset.sum_sub_distrib, mul_sub]
  set pairs := Finset.univ.filter fun st : (E →ₐ[K] AlgebraicClosure K) × (E →ₐ[K] AlgebraicClosure K) =>
    st.1 ≠ st.2 with hpairs
  set Q := fΩ * ∏ st ∈ pairs, lin st.1 st.2 with hQ
  have hQ0 : Q ≠ 0 := by
    refine mul_ne_zero hfΩ0 (Finset.prod_ne_zero_iff.mpr fun st hst => ?_)
    have hne : st.1 ≠ st.2 := (Finset.mem_filter.mp hst).2
    have hpne : pt st.1 ≠ pt st.2 := fun h => hne (hinj h)
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hpne
    intro h0
    have := congrArg (eval (Pi.single (0, k) 1)) h0
    rw [hlin_eval, map_zero] at this
    simp only [Pi.single_apply, Prod.mk.injEq, true_and, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    exact hk (sub_eq_zero.mp this)
  obtain ⟨a, ha⟩ : ∃ a, eval a Q ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hQ0 (MvPolynomial.funext fun x => by rw [hcon x, map_zero])
  have hfa : eval a fΩ ≠ 0 := fun h => ha (by rw [hQ, eval_mul, h, zero_mul])
  let c : (E →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K := fun σ => ∑ k, a (0, k) * pt σ k
  have hdist : Function.Injective c := by
    intro σ τ h
    by_contra hne
    apply ha
    rw [hQ, eval_mul, map_prod]
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (i := (σ, τ))
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩) ?_)
    rw [hlin_eval]
    exact sub_eq_zero.mpr h
  let s : Fin (0 + 1) × Fin N → Polynomial (AlgebraicClosure K) :=
    fun ik => Polynomial.C (a ik) + if ik.2 = j then Polynomial.X else 0
  set g := MvPolynomial.aeval s f with hg
  have heval : ∀ t, g.eval t = MvPolynomial.aeval (fun ik => a ik + if ik.2 = j then t else 0) f := by
    intro t
    have := MvPolynomial.comp_aeval_apply s
      ((Polynomial.aeval t).restrictScalars K : Polynomial (AlgebraicClosure K) →ₐ[K] AlgebraicClosure K) f
    rw [hg, ← Polynomial.coe_aeval_eq_eval, show (Polynomial.aeval t) (MvPolynomial.aeval s f) =
      ((Polynomial.aeval t).restrictScalars K : Polynomial (AlgebraicClosure K) →ₐ[K] AlgebraicClosure K)
        (MvPolynomial.aeval s f) from rfl, this]
    refine congrArg (fun v => MvPolynomial.aeval v f) (funext fun ik => ?_)
    simp only [s]
    split_ifs <;> simp
  have hg0 : g ≠ 0 := by
    intro h
    have := heval 0
    rw [h, Polynomial.eval_zero] at this
    have h2 : (fun ik : Fin (0 + 1) × Fin N => a ik + if ik.2 = j then (0 : AlgebraicClosure K) else 0) = a := by
      funext ik; split_ifs <;> simp
    rw [h2] at this
    apply hfa
    rw [hfΩ, MvPolynomial.eval_map, ← MvPolynomial.aeval_def]
    exact this.symm
  have hroot : ∀ σ, g.eval (-c σ) = 0 := by
    intro σ
    rw [heval]
    refine (hf.zero_iff _).mpr
      ⟨pt σ, fun h => by simpa [hpj σ] using congrFun h j, hzero σ, fun i => ?_⟩
    obtain rfl : i = 0 := Fin.ext (Nat.lt_one_iff.mp i.isLt)
    simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, hpj σ, mul_one]
    simp [c]
  have hcard : Fintype.card (E →ₐ[K] AlgebraicClosure K) ≤ g.roots.toFinset.card := by
    rw [← Finset.card_univ]
    refine Finset.card_le_card_of_injOn (fun σ => -c σ) (fun σ _ => ?_) ?_
    · simp only [Finset.mem_coe, Multiset.mem_toFinset]
      rw [Polynomial.mem_roots hg0]
      exact hroot σ
    · intro σ _ τ _ h
      exact hdist (neg_injective h)
  have hhom := ((_root_.GlobalTheory.ChowHt.isMultiHomogeneous_iff_block.mp
    hf.homog).isHomogeneous)
  have htot : f.totalDegree = δ := by
    rw [hhom.totalDegree hf.ne_zero]
    simp
  calc Fintype.card (E →ₐ[K] AlgebraicClosure K) ≤ g.roots.toFinset.card := hcard
    _ ≤ Multiset.card g.roots := Multiset.toFinset_card_le _
    _ ≤ g.natDegree := Polynomial.card_roots' g
    _ ≤ f.totalDegree := natDegree_aeval_le_totalDegree_of_natDegree_le_one f s fun ik => by
        simp only [s]
        split_ifs
        · exact (Polynomial.natDegree_add_le _ _).trans (by simp)
        · simp
    _ = δ := htot

end GlobalTheory.CompHt.PointLow
