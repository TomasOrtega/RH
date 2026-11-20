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
Introduce `k₁ k₂ _`. Apply the tactic sequence `rcases k₁ with a | a <;> rcases k₂ with b | b <;> exact congrArg j (Subsingleton.elim a b)`.
-/
private lemma coh_lemma {X Y : Scheme} (L : LB X) (φ : Fin 1 ⊕ Fin 1 → (Y ⟶ X))
    (j : Fin 1 → L.ι) : LB.Coh L φ (Sum.elim j j) := by
  intro k₁ k₂ _
  rcases k₁ with a | a <;> rcases k₂ with b | b <;> exact congrArg j (Subsingleton.elim a b)

/- English proof (translation)
Substitute `hc` using the available equality. Rewrite `hab` using `[_root_.one_mul, _root_.one_mul]`. Establish `hWV : W = V` using `le_antisymm h h'`. Substitute `hWV` using the available equality. Establish `e : homOfLE h = 𝟙 W` using `Subsingleton.elim _ _`.

Rewrite `hab` using `[e]`. Simplify using `using hab`.
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
Unfold `RegularSectionNonneg`. Introduce `V _ _ _ ϖ hϖ D Q hQ vK hvK A G _ _ _ _ _ U k hk σ s hs E hE`. Substitute `hk` using the available equality. Take `⟨F, g', hF, -, hFg⟩` from `TG.integral_exp (U := U) rfl σ`. Establish `hsK : s = TG.secK U.toUnifPre σ`.

Apply `SecOps.sec_ext` to reduce the goal to its premises. Introduce `j`. Establish `h1` using `hs j j (coh_lemma _ _ j)`. Establish `h2` using `TG.secK_rel U.toUnifPre σ j j (coh_lemma _ _ j)`. Establish `h3` using `h1.symm.trans h2`.

Use `res_inj_lemma_2 _ (by exact _root_.map_one _) h3 ?_` and prove the remaining obligations. Use `le_inf le_rfl ?_` and prove the remaining obligations. Use `first`. Consider the case `exact le_rfl`. Consider the case `(simp only [Category.comp_id]; exact le_rfl)`.

Consider the case `exact fun x hx => hx`. Consider the case `(intro x hx; simpa [LB.wchart] using hx)`. Substitute `hsK` using the available equality. Establish `hEF : E = F` using `((U.expand 1 le_rfl).1 _).unique hE hF`. Rewrite using `[hEF]`.

Use `(n1a V ϖ hϖ D Q hQ (FractionRing V) vK hvK 1 le_rfl {0} (fun χ => ⟨0, Finset.mem_singleton_self 0, χ, by simp⟩) F 0).2 ?_` and prove the remaining obligations. Introduce `α hα`. Rewrite `hα` using `[Finset.mem_singleton]`. Substitute `hα` using the available equality. Rewrite using `[Q_zero hϖ (hQ := hQ)]`.

Unfold `VGe`. Use `⟨1, fun _ => 1, fun _ => g' 0, fun _ => F.s 0, fun _ => hFg 0, fun _ => ?_, fun j => ?_⟩` and prove the remaining obligations. Use `first`. Consider the case `simp`. Consider the case `(rw [AddValuation.map_one]; simp)`.

Use `first`. Consider the case `simp [DegPre.constBF]`. Consider the case `(simp only [DegPre.constBF, Fin.sum_univ_one, _root_.map_one, _root_.one_mul])`.
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
