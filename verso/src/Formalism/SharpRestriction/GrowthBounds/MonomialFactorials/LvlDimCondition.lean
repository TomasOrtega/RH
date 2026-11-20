import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.LvlDimGen
import Formalism.MahlerMeasure.MahlerMeasureProofs.TheoremM

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset

section Gen

variable {p : ℕ} [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

/- English proof (translation)
Take `⟨s, hs1, hs2⟩` from `Formalism.GM.M.good_pre (p := p) (r := r) G j jp`. Establish `hpre : Formalism.GM.M.pre (p` using `p) (r := r) G j jp ≠ 0 := by`. Introduce `h0`. Rewrite `hs2` using `[h0, zero_sub]`. Establish `hmem : s ∈ (-(monomial s (1 : ℚ_[p]))).support`.

Rewrite using `[support_neg, support_monomial, if_neg one_ne_zero]`. Conclude with `Finset.mem_singleton_self s`. Conclude with `(hs2 s hmem).2 hs1`. Establish `e : preF (p` using `p) (r := r) G j jp = Formalism.GM.M.pre (p := p) (r := r) G j jp * monomial (Formalism.GM.M.zmS G) 1 := by`. Rewrite using `[← Formalism.GM.M.zmon_eq]`.

Unfold `preF Formalism.GM.M.pre`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `mul_ne_zero hpre (by rw [Ne, monomial_eq_zero]; exact one_ne_zero)`.
-/
theorem preF_ne_zero (j : Fin G.T.t → ℕ) (jp : ℕ) : preF (p := p) (r := r) G j jp ≠ 0 := by
  classical
  obtain ⟨s, hs1, hs2⟩ := Formalism.GM.M.good_pre (p := p) (r := r) G j jp
  have hpre : Formalism.GM.M.pre (p := p) (r := r) G j jp ≠ 0 := by
    intro h0
    rw [h0, zero_sub] at hs2
    have hmem : s ∈ (-(monomial s (1 : ℚ_[p]))).support := by
      rw [support_neg, support_monomial, if_neg one_ne_zero]
      exact Finset.mem_singleton_self s
    exact (hs2 s hmem).2 hs1
  have e : preF (p := p) (r := r) G j jp =
      Formalism.GM.M.pre (p := p) (r := r) G j jp * monomial (Formalism.GM.M.zmS G) 1 := by
    rw [← Formalism.GM.M.zmon_eq]
    unfold preF Formalism.GM.M.pre
    ring
  rw [e]
  exact mul_ne_zero hpre (by rw [Ne, monomial_eq_zero]; exact one_ne_zero)

/- English proof (translation)
Introduce `y hy`. Take `⟨k, hk⟩` from `Formalism.GM.TM.exists_pow_smul_intPol (p := p) y`. Use `⟨(p : ℤ_[p]) ^ k, pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero), ?_⟩` and prove the remaining obligations. Establish `e : (((p : ℤ_[p]) ^ k : ℤ_[p]) : ℚ_[p]) = (p : ℚ_[p]) ^ k` using `by push_cast; rfl`. Rewrite using `[e]`.

Use `⟨Submodule.smul_mem _ _ hy, ?_, hk⟩` and prove the remaining obligations. Conclude with `Submodule.smul_mem _ _ ((inf_le_left : Formalism.GM.M.Y p (r := r) (G.lettersAt j jp) G.T.J G.T.thr ≤ _) hy)`.
-/
theorem den_Y (j : Fin G.T.t → ℕ) (jp : ℕ) :
    ∀ y ∈ Formalism.GM.M.Y p (r := r) (G.lettersAt j jp) G.T.J G.T.thr, ∃ c : ℤ_[p], c ≠ 0 ∧
      ((c : ℚ_[p]) • y) ∈ Formalism.GM.M.YZ p (r := r) (G.lettersAt j jp) G.T.J G.T.thr := by
  intro y hy
  obtain ⟨k, hk⟩ := Formalism.GM.TM.exists_pow_smul_intPol (p := p) y
  refine ⟨(p : ℤ_[p]) ^ k, pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero), ?_⟩
  have e : (((p : ℤ_[p]) ^ k : ℤ_[p]) : ℚ_[p]) = (p : ℚ_[p]) ^ k := by push_cast; rfl
  rw [e]
  refine ⟨Submodule.smul_mem _ _ hy, ?_, hk⟩
  exact Submodule.smul_mem _ _ ((inf_le_left : Formalism.GM.M.Y p (r := r) (G.lettersAt j jp) G.T.J G.T.thr ≤ _) hy)

/- English proof (translation)
Introduce `β hβ x`. Assume the negation of the conclusion as `h`. Establish `hmem : Formalism.GM.M.chainEmb N r G.T.t x ∈ β.support` using `Finsupp.mem_support_iff.2 h`. Take `⟨c, hc⟩` from `(xiMons_spec G n β hβ).1 _ hmem`. Simplify using `only [Formalism.GM.M.chainEmb, Formalism.GM.M.xiVar, Sum.inl.injEq, Prod.mk.injEq] at hc`.

Conclude with `Fin.castSucc_ne_last _ hc.1`.
-/
theorem xiMons_free (n : ℕ) : ∀ β ∈ xiMons (r := r) G n, ∀ x, β (Formalism.GM.M.chainEmb N r G.T.t x) = 0 := by
  intro β hβ x
  by_contra h
  have hmem : Formalism.GM.M.chainEmb N r G.T.t x ∈ β.support := Finsupp.mem_support_iff.2 h
  obtain ⟨c, hc⟩ := (xiMons_spec G n β hβ).1 _ hmem
  simp only [Formalism.GM.M.chainEmb, Formalism.GM.M.xiVar, Sum.inl.injEq, Prod.mk.injEq] at hc
  exact Fin.castSucc_ne_last _ hc.1

/- English proof (translation)
Introduce `β hβ`. Take `⟨h1, h2, -⟩` from `xiMons_spec G n β hβ`. Use `⟨?_, Formalism.GM.M.intPol_monomial' β⟩` and prove the remaining obligations. Use `show monomial β (1 : ℚ_[p]) ∈ MvPolynomial.restrictSupport ℚ_[p] _`. Rewrite using `[MvPolynomial.mem_restrictSupport_iff, support_monomial, if_neg one_ne_zero]`.

Introduce `m hm`. Rewrite `hm` using `[Finset.coe_singleton, Set.mem_singleton_iff]`. Substitute `hm` using the available equality. Conclude with `⟨h1, h2⟩`.
-/
theorem xiMons_mem (n : ℕ) : ∀ β ∈ xiMons (r := r) G n, (monomial β (1 : ℚ_[p])) ∈ Formalism.GM.M.XiPolZ p N r G.T.t n := by
  classical
  intro β hβ
  obtain ⟨h1, h2, -⟩ := xiMons_spec G n β hβ
  refine ⟨?_, Formalism.GM.M.intPol_monomial' β⟩
  show monomial β (1 : ℚ_[p]) ∈ MvPolynomial.restrictSupport ℚ_[p] _
  rw [MvPolynomial.mem_restrictSupport_iff, support_monomial, if_neg one_ne_zero]
  intro m hm
  rw [Finset.coe_singleton, Set.mem_singleton_iff] at hm
  subst hm
  exact ⟨h1, h2⟩

end Gen

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

set_option maxHeartbeats 800000 in
/- English proof (translation)
Introduce `aTop _ aPlus _ b _ x hx`. Establish `hL : (gB C0 CE1 CE2 X aTop aPlus b).LevelOK x.1 x.2`. Unfold `lv levels at hx`. Conclude with `(Finset.mem_filter.1 hx).2`. Establish `hfd : FiniteDimensional ℚ_[X.p] (Submodule.span ℚ_[X.p] ((gB C0 CE1 CE2 X aTop aPlus b).gens X.p (r` using `X.r) x.1 x.2)) := by`.

Establish `h1` using `span_SSZ_fin C0 CE1 CE2 X aTop aPlus b`. Establish `hle : Submodule.span ℚ_[X.p] ((gB C0 CE1 CE2 X aTop aPlus b).gens X.p (r` using `X.r) x.1 x.2) ≤ Submodule.span ℚ_[X.p] (((gB C0 CE1 CE2 X aTop aPlus b).SSZ X.p (r := X.r) : Submodule ℤ_[X.p] (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop aPlus b).T.t) ℚ_[X.p])) : Set (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 …`. Conclude with `Submodule.finiteDimensional_of_le hle`. Conclude with `lvlDim_gen (gB C0 CE1 CE2 X aTop aPlus b) x.1 x.2 (preF_ne_zero _ _ _) (den_Y _ _ _) hfd (xiMons_free _ _) (xiMons_mem _ _)`.
-/
theorem lvlDimCondition : RestLvlDim C0 CE1 CE2 X := by
  classical
  intro aTop _ aPlus _ b _ x hx
  have hL : (gB C0 CE1 CE2 X aTop aPlus b).LevelOK x.1 x.2 := by
    unfold lv levels at hx
    exact (Finset.mem_filter.1 hx).2
  have hfd : FiniteDimensional ℚ_[X.p]
      (Submodule.span ℚ_[X.p] ((gB C0 CE1 CE2 X aTop aPlus b).gens X.p (r := X.r) x.1 x.2)) := by
    have h1 := span_SSZ_fin C0 CE1 CE2 X aTop aPlus b
    have hle : Submodule.span ℚ_[X.p] ((gB C0 CE1 CE2 X aTop aPlus b).gens X.p (r := X.r) x.1 x.2) ≤
        Submodule.span ℚ_[X.p]
          (((gB C0 CE1 CE2 X aTop aPlus b).SSZ X.p (r := X.r) :
            Submodule ℤ_[X.p] (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop aPlus b).T.t) ℚ_[X.p])) :
              Set (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop aPlus b).T.t) ℚ_[X.p])) :=
      Submodule.span_le.2 fun y hy => Submodule.subset_span
        (Formalism.GM.M.gens_mem_SSZ (p := X.p) (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) x.1 x.2 hL y hy)
    exact Submodule.finiteDimensional_of_le hle
  exact lvlDim_gen (gB C0 CE1 CE2 X aTop aPlus b) x.1 x.2 (preF_ne_zero _ _ _) (den_Y _ _ _) hfd
    (xiMons_free _ _) (xiMons_mem _ _)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
