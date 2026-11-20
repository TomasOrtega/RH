import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHomogeneousCollapseQ
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootLetterInjective
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConsNumber.VertRoots

/- English proof (translation)
Establish `h1 : ∑ l, b l ^ k = ∑ l, (-a l) ^ k`. Repeatedly rewrite using `[hb]`. Conclude with `Equiv.sum_comp e (fun l => (-a l) ^ k)`. Rewrite using `[h1, ← Finset.sum_add_distrib, ← Equiv.sum_comp e' (fun x => r x ^ k + (-r x) ^ k)]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Apply the tactic sequence `rcases ha l with h | h <;> rw [h]`. Rewrite using `[neg_neg, add_comm]`.
-/
theorem sum_pow_add_sum_pow {R : Type} [CommRing R] {ι κ : Type} [Fintype ι] [Fintype κ] (k : ℕ)
    (a b : ι → R) (r : κ → R) (e : ι ≃ ι) (e' : ι ≃ κ)
    (ha : ∀ l, a l = r (e' l) ∨ a l = -r (e' l)) (hb : ∀ l, b l = -a (e l)) :
    (∑ l, a l ^ k) + ∑ l, b l ^ k = ∑ x, (r x ^ k + (-r x) ^ k) := by
  have h1 : ∑ l, b l ^ k = ∑ l, (-a l) ^ k := by
    simp_rw [hb]
    exact Equiv.sum_comp e (fun l => (-a l) ^ k)
  rw [h1, ← Finset.sum_add_distrib, ← Equiv.sum_comp e' (fun x => r x ^ k + (-r x) ^ k)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rcases ha l with h | h <;> rw [h]
  rw [neg_neg, add_comm]

section Model

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ} [Fact p.Prime] {hp : p.Prime}
  {W : ValuationSubring ℂ} {hW : (p : ℂ) ∈ W.nonunits} (z : AdmAt S κ hp hW) (jc : KW p →+* ℂ)

/- English proof (translation)
Break down `h : letterOf S.Dw st with _ | x` into its components or cases. Establish `e : ∀ b, z.stepLB b st = FinLB.triv _` using `fun b => by`. Unfold `admitted.stepLB`. Use `split`. Use `next y hy => exact absurd (hy.symm.trans h) (by simp)`.

Both sides reduce to the same expression. Rewrite using `[e, e, sub_self]`. Conclude with `zero_mem _`. Rewrite using `[z.stepLB_of_some true h, z.stepLB_of_some false h]`. Establish `e : (mdlOf z jc).Z.c1 (z.line true st x h).L = (mdlOf z jc).Z.c1 (z.line false st x h).L - (mdlOf z jc).Z.cD (vdiv hp hW (Formalism.DegreeFormula.dimFl D.what₂.Tau N) (z.line false st x h).L (z.line true st x h).L (z.genId hp hW h))` using `firstChern_eq_sub_divisor hp hW (Formalism.DegreeFormula.dimFl D.what₂.Tau N) (z.line false st x h).L (z.line true st x h).L (z.genId hp hW h)`.

Rewrite using `[e, sub_sub_cancel_left]`. Conclude with `neg_mem (Ideal.subset_span ⟨_, rfl⟩)`.
-/
theorem c1_stepLB_sub_mem (st : ((D.host.E →+* ℂ) × ℕ) ⊕ ℕ) :
    (mdlOf z jc).Z.c1 (z.stepLB true st) - (mdlOf z jc).Z.c1 (z.stepLB false st) ∈
      Ideal.span (Set.range (mdlOf z jc).Z.cD) := by
  rcases h : letterOf S.Dw st with _ | x
  · have e : ∀ b, z.stepLB b st = FinLB.triv _ := fun b => by
      unfold admitted.stepLB
      split
      · next y hy => exact absurd (hy.symm.trans h) (by simp)
      · rfl
    rw [e, e, sub_self]
    exact zero_mem _
  · rw [z.stepLB_of_some true h, z.stepLB_of_some false h]
    have e : (mdlOf z jc).Z.c1 (z.line true st x h).L = (mdlOf z jc).Z.c1 (z.line false st x h).L -
        (mdlOf z jc).Z.cD (vdiv hp hW (Formalism.DegreeFormula.dimFl D.what₂.Tau N) (z.line false st x h).L (z.line true st x h).L
          (z.genId hp hW h)) :=
      firstChern_eq_sub_divisor hp hW (Formalism.DegreeFormula.dimFl D.what₂.Tau N) (z.line false st x h).L (z.line true st x h).L (z.genId hp hW h)
    rw [e, sub_sub_cancel_left]
    exact neg_mem (Ideal.subset_span ⟨_, rfl⟩)

/- English proof (translation)
Unfold `rootOf admitted.rootLB`. Simplify using `only`. Use `split_ifs`. Conclude with `c1_stepLB_sub_mem z jc _`. Rewrite using `[LieGen.c1_dual_mdl, LieGen.c1_dual_mdl, neg_sub_neg]`.

Establish `h` using `neg_mem (c1_stepLB_sub_mem z jc (.inl (conjEmb (tauEmb D r.1), S.Dw.p + S.Dw.q - 1 - (r.2 : ℕ))))`. Rewrite `h` using `[neg_sub]`. Then use the resulting hypothesis.
-/
theorem c1_rootOf_sub_mem (r : Rt D.what₂.Tau N) :
    (mdlOf z jc).Z.c1 (rootOf z jc (true, r)) - (mdlOf z jc).Z.c1 (rootOf z jc (false, r)) ∈
      Ideal.span (Set.range (mdlOf z jc).Z.cD) := by
  unfold rootOf admitted.rootLB
  dsimp only
  split_ifs
  · exact c1_stepLB_sub_mem z jc _
  · rw [LieGen.c1_dual_mdl, LieGen.c1_dual_mdl, neg_sub_neg]
    have h := neg_mem (c1_stepLB_sub_mem z jc (.inl (conjEmb (tauEmb D r.1), S.Dw.p + S.Dw.q - 1 - (r.2 : ℕ))))
    rwa [neg_sub] at h

end Model

/- English proof (translation)
Introduce `D A N j S κ p _ hp W hW z jc G`. Use `set I : Ideal (mdlOf z jc).Z.Ch := Ideal.span (Set.range (mdlOf z jc).Z.cD) with hIdef`. Establish `hI : ∀ v, Ideal.Quotient.mk I ((mdlOf z jc).Z.cD v) = 0` using `fun v => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨v, rfl⟩)`. Take `⟨e', V, hV⟩` from `LieGen.lieW_gen D A N j S κ p hp W hW z jc`. Take `⟨e, he⟩` from `(mdlOf z jc).omW_dual`.

Establish `hA : ∀ l, Ideal.Quotient.mk I ((mdlOf z jc).Z.c1 ((mdlOf z jc).lieW.x l)) = Ideal.Quotient.mk I ((mdlOf z jc).Z.c1 (rootOf z jc (false, e' l))) ∨ Ideal.Quotient.mk I ((mdlOf z jc).Z.c1 ((mdlOf z jc).lieW.x l)) = -Ideal.Quotient.mk I ((mdlOf z jc).Z.c1 (rootOf z jc (false, e' l)))` using `fun l => by`. Rewrite using `[hV l, map_add, hI, add_zero]`. Use `split_ifs`. Use `left`. Rewrite using `[one_smul]`.

Use `right`. Rewrite using `[neg_one_smul, map_neg]`. Establish `hB : ∀ l, Ideal.Quotient.mk I ((mdlOf z jc).Z.c1 ((mdlOf z jc).omW.x l)) = -Ideal.Quotient.mk I ((mdlOf z jc).Z.c1 ((mdlOf z jc).lieW.x (e l)))` using `fun l => by`. Rewrite using `[he l, map_neg]`. Establish `hA' : ∀ l, Ideal.Quotient.mk I ((mdlOf z jc).Z.c1 ((mdlOf z jc).lieW.x' l)) = Ideal.Quotient.mk I ((mdlOf z jc).Z.c1 ((mdlOf z jc).lieW.x l))` using `fun l => by`.

Rewrite using `[(mdlOf z jc).lieW.hx l, map_sub, hI, sub_zero]`. Establish `hB' : ∀ l, Ideal.Quotient.mk I ((mdlOf z jc).Z.c1 ((mdlOf z jc).omW.x' l)) = Ideal.Quotient.mk I ((mdlOf z jc).Z.c1 ((mdlOf z jc).omW.x l))` using `fun l => by`. Rewrite using `[(mdlOf z jc).omW.hx l, map_sub, hI, sub_zero]`. Establish `hsum : ∀ k : ℕ, (∑ l, Ideal.Quotient.mk I ((mdlOf z jc).Z.c1 ((mdlOf z jc).lieW.x l)) ^ k) + ∑ l, Ideal.Quotient.mk I ((mdlOf z jc).Z.c1 ((mdlOf z jc).omW.x l)) ^ k = ∑ t : D.what₂.Tau, ∑ i : Fin N, (Ideal.Quotient.mk I ((mdlOf z jc).Z.c1 (rootOf z jc (false, (t, i)))) ^ k + (-Id …` using `fun k => by`. Rewrite using `[sum_pow_add_sum_pow k _ _ (fun x => Ideal.Quotient.mk I ((mdlOf z jc).Z.c1 (rootOf z jc (false, x)))) e e' hA hB]`.

Conclude with `Fintype.sum_prod_type _`. Establish `key : (Ideal.Quotient.mkₐ ℚ I).comp ((aeval (mdlOf z jc).Z.c1).comp (evV (mdlOf z jc) (rootOf z jc))) = (Ideal.Quotient.mkₐ ℚ I).comp ((aeval fun x => (mdlOf z jc).Z.c1 (rootOf z jc (false, x))).comp (GlobalTheory.ConsNumber.collapseQ D N))`. Use `MvPolynomial.algHom_ext fun v => ?_` and prove the remaining obligations. Break down `v with ⟨b, r⟩ | ⟨b, k⟩` into its components or cases. Simplify using `only [AlgHom.comp_apply, evV, GlobalTheory.ConsNumber.collapseQ, GlobalTheory.ConsNumber.colVar, aeval_X, Ideal.Quotient.mkₐ_eq_mk]`.

Consider the cases of `b`. Both sides reduce to the same expression. Conclude with `Ideal.Quotient.eq.2 (c1_rootOf_sub_mem z jc r)`. Consider the cases of `b`. Simplify using `only [AlgHom.comp_apply, evV, GlobalTheory.ConsNumber.collapseQ, GlobalTheory.ConsNumber.colVar, aeval_X, aeval_C, Ideal.Quotient.mkₐ_eq_mk, map_mul, map_add, map_sum, map_pow, map_neg]`.

Rewrite using `[hsum]`. Simplify using `only [AlgHom.comp_apply, evV, GlobalTheory.ConsNumber.collapseQ, GlobalTheory.ConsNumber.colVar, aeval_X, aeval_C, Ideal.Quotient.mkₐ_eq_mk, map_mul, map_add, map_sum, map_pow, map_neg, hA', hB']`. Rewrite using `[hsum]`. Establish `h` using `AlgHom.congr_fun key G`. Simplify using `only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at h`.

Conclude with `Ideal.Quotient.eq.1 h`.
-/
theorem evC_sub_collapseQ_mem : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (p : ℕ) [Fact p.Prime]
    (hp : p.Prime) (W : ValuationSubring ℂ) (hW : (p : ℂ) ∈ W.nonunits) (z : AdmAt S κ hp hW) (jc : KW p →+* ℂ)
    (G : MvPolynomial (Vm D.what₂.Tau N) ℚ), evC (mdlOf z jc) (rootOf z jc) G -
      aeval (fun x => (mdlOf z jc).Z.c1 (rootOf z jc (false, x))) (GlobalTheory.ConsNumber.collapseQ D N G) ∈
        Ideal.span (Set.range (mdlOf z jc).Z.cD) := by
  intro D A N j S κ p _ hp W hW z jc G
  set I : Ideal (mdlOf z jc).Z.Ch := Ideal.span (Set.range (mdlOf z jc).Z.cD) with hIdef
  have hI : ∀ v, Ideal.Quotient.mk I ((mdlOf z jc).Z.cD v) = 0 :=
    fun v => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨v, rfl⟩)
  obtain ⟨e', V, hV⟩ := LieGen.lieW_gen D A N j S κ p hp W hW z jc
  obtain ⟨e, he⟩ := (mdlOf z jc).omW_dual
  have hA : ∀ l, Ideal.Quotient.mk I ((mdlOf z jc).Z.c1 ((mdlOf z jc).lieW.x l)) =
      Ideal.Quotient.mk I ((mdlOf z jc).Z.c1 (rootOf z jc (false, e' l))) ∨
      Ideal.Quotient.mk I ((mdlOf z jc).Z.c1 ((mdlOf z jc).lieW.x l)) =
      -Ideal.Quotient.mk I ((mdlOf z jc).Z.c1 (rootOf z jc (false, e' l))) := fun l => by
    rw [hV l, map_add, hI, add_zero]
    split_ifs
    · left
      rw [one_smul]
    · right
      rw [neg_one_smul, map_neg]
  have hB : ∀ l, Ideal.Quotient.mk I ((mdlOf z jc).Z.c1 ((mdlOf z jc).omW.x l)) =
      -Ideal.Quotient.mk I ((mdlOf z jc).Z.c1 ((mdlOf z jc).lieW.x (e l))) := fun l => by
    rw [he l, map_neg]
  have hA' : ∀ l, Ideal.Quotient.mk I ((mdlOf z jc).Z.c1 ((mdlOf z jc).lieW.x' l)) =
      Ideal.Quotient.mk I ((mdlOf z jc).Z.c1 ((mdlOf z jc).lieW.x l)) := fun l => by
    rw [(mdlOf z jc).lieW.hx l, map_sub, hI, sub_zero]
  have hB' : ∀ l, Ideal.Quotient.mk I ((mdlOf z jc).Z.c1 ((mdlOf z jc).omW.x' l)) =
      Ideal.Quotient.mk I ((mdlOf z jc).Z.c1 ((mdlOf z jc).omW.x l)) := fun l => by
    rw [(mdlOf z jc).omW.hx l, map_sub, hI, sub_zero]
  have hsum : ∀ k : ℕ, (∑ l, Ideal.Quotient.mk I ((mdlOf z jc).Z.c1 ((mdlOf z jc).lieW.x l)) ^ k) +
      ∑ l, Ideal.Quotient.mk I ((mdlOf z jc).Z.c1 ((mdlOf z jc).omW.x l)) ^ k =
      ∑ t : D.what₂.Tau, ∑ i : Fin N, (Ideal.Quotient.mk I ((mdlOf z jc).Z.c1 (rootOf z jc (false, (t, i)))) ^ k +
        (-Ideal.Quotient.mk I ((mdlOf z jc).Z.c1 (rootOf z jc (false, (t, i))))) ^ k) := fun k => by
    rw [sum_pow_add_sum_pow k _ _ (fun x => Ideal.Quotient.mk I ((mdlOf z jc).Z.c1 (rootOf z jc (false, x)))) e e' hA hB]
    exact Fintype.sum_prod_type _
  have key : (Ideal.Quotient.mkₐ ℚ I).comp ((aeval (mdlOf z jc).Z.c1).comp (evV (mdlOf z jc) (rootOf z jc))) =
      (Ideal.Quotient.mkₐ ℚ I).comp
        ((aeval fun x => (mdlOf z jc).Z.c1 (rootOf z jc (false, x))).comp (GlobalTheory.ConsNumber.collapseQ D N)) := by
    refine MvPolynomial.algHom_ext fun v => ?_
    rcases v with ⟨b, r⟩ | ⟨b, k⟩
    · simp only [AlgHom.comp_apply, evV, GlobalTheory.ConsNumber.collapseQ, GlobalTheory.ConsNumber.colVar, aeval_X,
        Ideal.Quotient.mkₐ_eq_mk]
      cases b
      · rfl
      · exact Ideal.Quotient.eq.2 (c1_rootOf_sub_mem z jc r)
    · cases b
      · simp only [AlgHom.comp_apply, evV, GlobalTheory.ConsNumber.collapseQ, GlobalTheory.ConsNumber.colVar, aeval_X, aeval_C,
          Ideal.Quotient.mkₐ_eq_mk, map_mul, map_add, map_sum, map_pow, map_neg]
        rw [hsum]
      · simp only [AlgHom.comp_apply, evV, GlobalTheory.ConsNumber.collapseQ, GlobalTheory.ConsNumber.colVar, aeval_X, aeval_C,
          Ideal.Quotient.mkₐ_eq_mk, map_mul, map_add, map_sum, map_pow, map_neg, hA', hB']
        rw [hsum]
  have h := AlgHom.congr_fun key G
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at h
  exact Ideal.Quotient.eq.1 h

end GlobalTheory.ConsNumber.VertRoots
