import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.LatSpanLeSpan

noncomputable section

open scoped Classical

namespace Formalism.L2.S.Pv.ClassCounting

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.TermsAtPtFiniteW
  PI.TermsAtPtFiniteW.HeisW PI.TermsAtPtFiniteW.LeviW PI.TermsAtPtFiniteW.FrameW Formalism.L2.SG.Saturated

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws.
-/
theorem psiF_f (e f : Fin r → S.V) (U U' : Matrix (Fin r) (Fin r) E) (hff : ∀ a b, S.hT (f a) (f b) = 0)
    (hef : ∀ a b, S.hT (e a) (f b) = if a = b then 1 else 0) (j : Fin r) :
    psiF e f U U' (f j) = ∑ c, U' c j • f c := by
  rw [psiF_apply]
  simp only [hff, hef, zero_smul, Finset.sum_const_zero, add_zero, ite_smul, one_smul, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  abel

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Proceed by induction. Treat this case separately.

Treat this case separately. Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions.

Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem levi_mem (Λ : Submodule (𝓞 E) S.V) (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (e f : Fin r → S.V) (L : Submodule (𝓞 E) S.V)
    (hΛ : Λ = latSpan aa e ⊔ L ⊔ latSpan (fun a => (aa a)⁻¹) f)
    (hee : ∀ a b, S.hT (e a) (e b) = 0) (hff : ∀ a b, S.hT (f a) (f b) = 0)
    (hef : ∀ a b, S.hT (e a) (f b) = if a = b then 1 else 0)
    (hL : ∀ x ∈ L, ∀ a, S.hT (e a) x = 0 ∧ S.hT (f a) x = 0)
    (haa : ∀ a c : Fin r, c ≤ a → aa a ≤ aa c) (haa0 : ∀ a, aa a ≠ 0)
    (U U' : Matrix (Fin r) (Fin r) E)
    (hU : ∀ c a, (a < c → U c a = 0) ∧ ∃ o : 𝓞 E, (o : E) = U c a)
    (hU' : ∀ c a, (c < a → U' c a = 0) ∧ ∃ o : 𝓞 E, (o : E) = U' c a)
    {v : S.V} (hv : v ∈ Λ) : psiF e f U U' v ∈ Λ := by
  have hA : ∀ y ∈ latSpan aa e, psiF e f U U' y ∈ latSpan aa e := by
    intro y hy
    unfold latSpan at hy ⊢
    induction hy using Submodule.span_induction with
    | zero => simp
    | add y y' _ _ h h' => rw [map_add]; exact Submodule.add_mem _ h h'
    | smul o y _ h => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ o h
    | mem y hy =>
    obtain ⟨a, x, hx, rfl⟩ := hy
    rw [map_smul, psiF_e e f hef U U' hee, Finset.smul_sum]
    refine Submodule.sum_mem _ fun c _ => ?_
    rw [smul_smul]
    rcases lt_or_ge a c with h | h
    · rw [(hU c a).1 h, mul_zero, zero_smul]
      exact Submodule.zero_mem _
    · obtain ⟨o, ho⟩ := (hU c a).2
      refine Submodule.subset_span ⟨c, x * U c a, haa a c h ?_, rfl⟩
      rw [← ho, mul_comm, ← Algebra.smul_def]
      exact Submodule.smul_mem _ o hx
  have hC : ∀ y ∈ latSpan (fun a => (aa a)⁻¹) f, psiF e f U U' y ∈ latSpan (fun a => (aa a)⁻¹) f := by
    intro y hy
    unfold latSpan at hy ⊢
    induction hy using Submodule.span_induction with
    | zero => simp
    | add y y' _ _ h h' => rw [map_add]; exact Submodule.add_mem _ h h'
    | smul o y _ h => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ o h
    | mem y hy =>
    obtain ⟨a, x, hx, rfl⟩ := hy
    rw [map_smul, psiF_f e f U U' hff hef, Finset.smul_sum]
    refine Submodule.sum_mem _ fun c _ => ?_
    rw [smul_smul]
    rcases lt_or_ge c a with h | h
    · rw [(hU' c a).1 h, mul_zero, zero_smul]
      exact Submodule.zero_mem _
    · obtain ⟨o, ho⟩ := (hU' c a).2
      refine Submodule.subset_span ⟨c, x * U' c a, ?_, rfl⟩
      have hle : (aa a)⁻¹ ≤ (aa c)⁻¹ := FractionalIdeal.inv_anti_mono (haa0 c) (haa0 a) (haa c a h)
      refine hle ?_
      rw [← ho, mul_comm, ← Algebra.smul_def]
      exact Submodule.smul_mem _ o hx
  rw [hΛ] at hv ⊢
  obtain ⟨v12, hv12, v3, hv3, rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨v1, hv1, v2, hv2, rfl⟩ := Submodule.mem_sup.mp hv12
  rw [map_add, map_add, psiF_fix e f U U' v2 (fun a => (hL v2 hv2 a).2) (fun a => (hL v2 hv2 a).1)]
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.mem_sup_left (hA _ hv1)))
    (Submodule.mem_sup_left (Submodule.mem_sup_right hv2))) (Submodule.mem_sup_right (hC _ hv3))

end Gen

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ddS_pow_le_one (D : D7) (n : ℕ) : ddS D ^ n ≤ 1 := by
  unfold ddS
  rw [← FractionalIdeal.coeIdeal_pow]
  exact FractionalIdeal.coeIdeal_le_one

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem aaS_mono (D : D7) (a c : Fin D.R.rS) (h : c ≤ a) : aaS D a ≤ aaS D c := by
  rw [PI.TermsAtPtFiniteW.FrameW.aaS_eq, PI.TermsAtPtFiniteW.FrameW.aaS_eq]
  refine FractionalIdeal.inv_anti_mono (pow_ne_zero _ (PI.SRW.ddS_ne D)) (pow_ne_zero _ (PI.SRW.ddS_ne D)) ?_
  have e : ddS D ^ (D.R.rS - c.1) = ddS D ^ (D.R.rS - a.1) * ddS D ^ (a.1 - c.1) := by
    rw [← pow_add]
    congr 1
    have := a.2
    have : c.1 ≤ a.1 := h
    omega
  rw [e, FractionalIdeal.mul_le]
  intro i hi j hj
  have hj1 := ddS_pow_le_one D (a.1 - c.1) hj
  obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).mp hj1
  rw [← ho, mul_comm, ← Algebra.smul_def]
  exact Submodule.smul_mem _ o hi

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem aaS_ne (D : D7) (a : Fin D.R.rS) : aaS D a ≠ 0 := by
  rw [PI.TermsAtPtFiniteW.FrameW.aaS_eq]
  exact inv_ne_zero (pow_ne_zero _ (PI.SRW.ddS_ne D))

end D7

end Formalism.L2.S.Pv.ClassCounting

end
