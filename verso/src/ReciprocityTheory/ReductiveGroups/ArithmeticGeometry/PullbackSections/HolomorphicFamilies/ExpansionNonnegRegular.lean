import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.RegUnifCut
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing QForm

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Apply the first step, then apply the next step to every resulting obligation.
-/
private lemma coh_lemma {X Y : Scheme} (L : LB X) (φ : Fin 1 ⊕ Fin 1 → (Y ⟶ X))
    (j : Fin 1 → L.ι) : LB.Coh L φ (Sum.elim j j) := by
  intro k₁ k₂ _
  rcases k₁ with a | a <;> rcases k₂ with b | b <;> exact congrArg j (Subsingleton.elim a b)

/- English proof (translation)
Substitute using the available equality. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Substitute using the available equality. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
private lemma res_inj_lemma_2 {X : Scheme} {W V : X.Opens} (h : W ≤ V) {a b : Γ(X, V)}
    {c : Γ(X, W)} (hc : c = 1)
    (hab : c * (X.presheaf.map (homOfLE h).op).hom a = c * (X.presheaf.map (homOfLE h).op).hom b)
    (h' : V ≤ W) : a = b := by
  subst hc
  rw [_root_.one_mul, _root_.one_mul] at hab
  have hWV : W = V := le_antisymm h h'
  subst hWV
  have e : homOfLE h = 𝟙 W := Subsingleton.elim _ _
  rw [e] at hab
  simpa using hab

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Substitute using the available equality. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Treat this case separately. Treat this case separately. Treat this case separately.

Treat this case separately. Substitute using the available equality. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Substitute using the available equality. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions.

Reduce the conclusion to the remaining proof obligations. Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately.

A detailed English derivation is pending.
-/
theorem expansion_nonneg_regular : RegularSectionNonneg := by
  unfold RegularSectionNonneg
  intro V _ _ _ ϖ hϖ D Q hQ vK hvK A G _ _ _ _ _ U k hk σ s hs E hE
  subst hk
  obtain ⟨F, g', hF, -, hFg⟩ := TG.integral_exp (U := U) rfl σ

  have hsK : s = TG.secK U.toUnifPre σ := by
    apply SecOps.sec_ext
    intro j
    have h1 := hs j j (coh_lemma _ _ j)
    have h2 := TG.secK_rel U.toUnifPre σ j j (coh_lemma _ _ j)
    have h3 := h1.symm.trans h2
    refine res_inj_lemma_2 _ (by exact _root_.map_one _) h3 ?_
    refine le_inf le_rfl ?_
    first
      | exact le_rfl
      | (simp only [Category.comp_id]; exact le_rfl)
      | exact fun x hx => hx
      | (intro x hx; simpa [LB.wchart] using hx)
  subst hsK

  have hEF : E = F := ((U.expand 1 le_rfl).1 _).unique hE hF
  rw [hEF]
  refine (n1a V ϖ hϖ D Q hQ (FractionRing V) vK hvK 1 le_rfl {0}
    (fun χ => ⟨0, Finset.mem_singleton_self 0, χ, by simp⟩) F 0).2 ?_
  intro α hα
  rw [Finset.mem_singleton] at hα
  subst hα
  rw [Q_zero hϖ (hQ := hQ)]
  unfold VGe
  refine ⟨1, fun _ => 1, fun _ => g' 0, fun _ => F.s 0, fun _ => hFg 0, fun _ => ?_, fun j => ?_⟩
  · first
      | simp
      | (rw [AddValuation.map_one]; simp)
  · first
      | simp [DegPre.constBF]
      | (simp only [DegPre.constBF, Fin.sum_univ_one, _root_.map_one, _root_.one_mul])

end ReciprocityTheory.ChartRestriction.G.DVR
