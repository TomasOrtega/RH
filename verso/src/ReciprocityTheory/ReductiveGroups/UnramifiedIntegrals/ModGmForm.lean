import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModBasic
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGmSlash

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Substitute using the available equality. A detailed English derivation is pending.
-/
theorem IsMF.mdiff {k : ℤ} {f : ℍ → ℂ} (h : IsMF k f) : MDiff f := by
  obtain ⟨g, hg⟩ := h
  have e : f = ⇑g := funext fun τ => (hg τ).symm
  subst e
  exact ModularFormClass.holo g

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Substitute using the available equality. A detailed English derivation is pending.
-/
theorem IsMF.bdd {k : ℤ} {f : ℍ → ℂ} (h : IsMF k f) : IsBoundedAtImInfty f := by
  obtain ⟨g, hg⟩ := h
  have e : f = ⇑g := funext fun τ => (hg τ).symm
  subst e
  exact ModularFormClass.bdd_at_infty g

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Check the signs of the components of the expression.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem pt_im {a e : ℕ} (ha : 0 < a) (he : 0 < e) (b : ℕ) (τ : ℍ) :
    (pt a b e τ).im = (a : ℝ) / e * τ.im := by
  have h1 : (((a : ℂ) * (τ : ℂ) + b) / e).im = (a : ℝ) / e * τ.im := by
    rw [Complex.div_natCast_im]
    simp
    ring
  have hpos : 0 < (((a : ℂ) * (τ : ℂ) + b) / e).im := by
    rw [h1]
    have := τ.im_pos
    have ha' : (0 : ℝ) < a := by exact_mod_cast ha
    have he' : (0 : ℝ) < e := by exact_mod_cast he
    positivity
  unfold pt
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hpos]
  exact h1

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem mdiff_comp_pt {a e : ℕ} (ha : 0 < a) (he : 0 < e) (b : ℕ) {f : ℍ → ℂ} (hf : MDiff f) :
    MDiff (fun τ => f (pt a b e τ)) := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hf ⊢
  have hmap : Set.MapsTo (fun z : ℂ => ((a : ℂ) * z + b) / e) {z | 0 < z.im} {z | 0 < z.im} := by
    intro z hz
    have h := pt_im ha he b ⟨z, hz⟩
    have h2 := congrArg Complex.im (pt_coe ha he b ⟨z, hz⟩)
    have h3 := (pt a b e ⟨z, hz⟩).im_pos
    rw [UpperHalfPlane.coe_im] at h2
    rw [h2] at h3
    exact h3
  have hd : DifferentiableOn ℂ (fun z : ℂ => ((a : ℂ) * z + b) / e) {z | 0 < z.im} := by
    fun_prop
  refine (hf.comp hd hmap).congr fun z hz => ?_
  simp only [Function.comp_apply, pt, ofComplex_apply_of_im_pos hz]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem tendsto_pt {a e : ℕ} (ha : 0 < a) (he : 0 < e) (b : ℕ) :
    Filter.Tendsto (pt a b e) atImInfty atImInfty := by
  rw [UpperHalfPlane.atImInfty, Filter.tendsto_comap_iff]
  have h : (UpperHalfPlane.im ∘ pt a b e) = fun τ => (a : ℝ) / e * τ.im := funext fun τ => pt_im ha he b τ
  rw [h]
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have hc : (0 : ℝ) < (a : ℝ) / e := by positivity
  exact Filter.Tendsto.const_mul_atTop hc Filter.tendsto_comap

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem bdd_comp_pt {a e : ℕ} (ha : 0 < a) (he : 0 < e) (b : ℕ) {f : ℍ → ℂ}
    (hf : IsBoundedAtImInfty f) : IsBoundedAtImInfty (fun τ => f (pt a b e τ)) := by
  exact hf.comp_tendsto (tendsto_pt ha he b)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem fac_mdiff {t : ℕ × ℕ × ℕ} (ht : 0 < t.1 ∧ 0 < t.2.2) : MDiff (fac t) := by
  have hA := isMF_AA.mdiff
  have hD := isMF_DD.mdiff
  exact (hA.mul (mdiff_comp_pt ht.1 ht.2 t.2.1 hD)).sub ((mdiff_comp_pt ht.1 ht.2 t.2.1 hA).mul hD)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem fac_bdd {t : ℕ × ℕ × ℕ} (ht : 0 < t.1 ∧ 0 < t.2.2) : IsBoundedAtImInfty (fac t) := by
  have hA := isMF_AA.bdd
  have hD := isMF_DD.bdd
  exact (hA.mul (bdd_comp_pt ht.1 ht.2 t.2.1 hD)).sub ((bdd_comp_pt ht.1 ht.2 t.2.1 hA).mul hD)

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Fix the arbitrary inputs or assume the hypotheses. Simplify to obtain the desired conclusion from the available facts. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem Gm_mdiff {m : ℕ} (hm : 0 < m) : MDiff (Gm m) := by
  unfold Gm
  have key : ∀ s : Finset (ℕ × ℕ × ℕ), s ⊆ Tm m → MDiff (fun τ => ∏ t ∈ s, fac t τ) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      simpa using (mdifferentiable_const : MDiff (fun _ : ℍ => (1 : ℂ)))
    | insert t s ht ih =>
      intro hs
      simp only [Finset.prod_insert ht]
      exact (fac_mdiff (Tm_pos hm (hs (Finset.mem_insert_self t s)))).mul
        (ih (fun x hx => hs (Finset.mem_insert_of_mem hx)))
  exact key _ subset_rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem Gm_bdd {m : ℕ} (hm : 0 < m) : IsBoundedAtImInfty (Gm m) := by
  unfold Gm
  have key : ∀ s : Finset (ℕ × ℕ × ℕ), s ⊆ Tm m → IsBoundedAtImInfty (fun τ => ∏ t ∈ s, fac t τ) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      simp only [Finset.prod_empty]
      exact Filter.const_boundedAtFilter atImInfty (1 : ℂ)
    | insert t s ht ih =>
      intro hs
      simp only [Finset.prod_insert ht]
      exact Filter.BoundedAtFilter.mul (fac_bdd (Tm_pos hm (hs (Finset.mem_insert_self t s))))
        (ih (fun x hx => hs (Finset.mem_insert_of_mem hx)))
  exact key _ subset_rfl

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Clear the denominators using the available nonvanishing facts.
-/
theorem Gm_slash {m : ℕ} (hm : 0 < m) (γ : SL(2, ℤ)) :
    (Gm m) ∣[24 * ((Tm m).card : ℤ)] γ = Gm m := by
  funext τ
  rw [SL_slash_apply, Gm_smul hm γ τ]
  have hd : denom γ τ ≠ 0 := denom_ne_zero _ τ
  have : (24 * ((Tm m).card : ℤ)) = ((24 * (Tm m).card : ℕ) : ℤ) := by push_cast; ring
  rw [this, zpow_neg, zpow_natCast]
  field_simp

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem gmForm {m : ℕ} (hm : 0 < m) : IsMF (24 * ((Tm m).card : ℤ)) (Gm m) := by
  refine ⟨{ toFun := Gm m
            slash_action_eq' := ?_
            holo' := Gm_mdiff hm
            bdd_at_cusps' := ?_ }, fun τ => rfl⟩
  · intro A hA
    obtain ⟨A, rfl⟩ := hA
    exact Gm_slash hm A
  · intro c hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [Gm_slash hm γ]
    exact Gm_bdd hm

end ReciprocityTheory.ChartRestriction.L1
