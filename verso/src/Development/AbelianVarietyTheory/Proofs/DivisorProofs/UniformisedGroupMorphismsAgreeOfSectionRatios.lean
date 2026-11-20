import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecRatioEqRefl
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermRatioAgreeSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningMorphismsAgreeBeyondThresholdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupMorphismsAgreeNearPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Introduce `R _ _ _ hB D A G _ _ hG U`. Take `⟨k₁, hk₁, H₁⟩` from `GlobalTheory.T.thickening_morphisms_agree_beyond_threshold R hB D A G hG U`. Take `⟨k₂, -, H₂⟩` from `GlobalTheory.T.uniformisedGroup_morphisms_agree_near_point R hB D A G hG U`. Use `⟨max k₁ k₂, le_trans hk₁ (le_max_left _ _), ?_⟩` and prove the remaining obligations. Introduce `e k k' hk x x' T hx hx' y s₀ i i' i'' hy₁ hy₂ hy₃`.

Establish `m₁ : (x.left ≫ (fstG (maximalIdeal R) e G).left) y ∈ secChart U.LG.L i` using `(thickObj R (maximalIdeal R) e G).left.basicOpen_le _ hy₁`. Establish `m₂ : (fstG (maximalIdeal R) e G).left y ∈ secChart U.LG.L i'` using `(thickObj R (maximalIdeal R) e G).left.basicOpen_le _ hy₂`. Establish `m₃ : (x'.left ≫ (fstG (maximalIdeal R) e G).left) y ∈ secChart U.LG.L i''` using `(thickObj R (maximalIdeal R) e G).left.basicOpen_le _ hy₃`. Establish `u₁ : IsUnit (secGerm (x.left ≫ (fstG (maximalIdeal R) e G).left) y s₀ i)`. Conclude with `(congrArg IsUnit (gs_eq _ _ _ m₁ _)).mpr ((Scheme.mem_basicOpen (thickObj R (maximalIdeal R) e G).left _ y m₁).1 hy₁)`.

Establish `u₂ : IsUnit (secGerm (fstG (maximalIdeal R) e G).left y (T s₀) i')`. Conclude with `(congrArg IsUnit (gs_eq _ _ _ m₂ _)).mpr ((Scheme.mem_basicOpen (thickObj R (maximalIdeal R) e G).left _ y m₂).1 hy₂)`. Establish `u₃ : IsUnit (secGerm (x'.left ≫ (fstG (maximalIdeal R) e G).left) y s₀ i'')`. Conclude with `(congrArg IsUnit (gs_eq _ _ _ m₃ _)).mpr ((Scheme.mem_basicOpen (thickObj R (maximalIdeal R) e G).left _ y m₃).1 hy₃)`. Establish `hA : GermRatioAgree (x.left ≫ (fstG (maximalIdeal R) e G).left) (x'.left ≫ (fstG (maximalIdeal R) e G).left) s₀ i i'' y`.

Use `⟨m₁, m₃, u₁, u₃, fun s₁ => ?_⟩` and prove the remaining obligations. Establish `e₁` using `secRatioEq_iff_germ.1 (hx s₁ s₀) y i i' m₁ m₂`. Establish `e₂` using `secRatioEq_iff_germ.1 (hx' s₁ s₀) y i'' i' m₃ m₂`. Apply `(u₂.mul_left_inj).1` to reduce the goal to its premises. Take the linear combination `secGerm (x'.left ≫ (fstG (maximalIdeal R) e G).left) y s₀ i'' * e₁ - secGerm (x.left ≫ (fstG (maximalIdeal R) e G).left) y s₀ i * e₂`.

Establish `hb : x.left ≫ (thickObj R (maximalIdeal R) e G).hom = x'.left ≫ (thickObj R (maximalIdeal R) e G).hom`. Rewrite using `[Over.w x, Over.w x']`. Establish `hk₁' : k₁ ≤ k` using `le_trans (le_max_left _ _) hk`. Establish `hk₂' : k₂ ≤ k` using `le_trans (le_max_right _ _) hk`. Conclude with `H₂ e k hk₂' _ x.left x'.left hb s₀ i i'' y hA (H₁ e k hk₁' _ x.left x'.left hb s₀ i i'' y hA)`.
-/
theorem agree_near_of_ratios : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ (e k k' : ℕ), k₀ ≤ k → ∀ (x x' : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G) (T : H0 U.LG.L k → H0 U.LG.L k'), (∀ s₁ s₂ : H0 U.LG.L k, SecRatioEq U.LG.L (x.left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left s₁ s₂ (T s₁) (T s₂)) → (∀ s₁ s₂ : H0 U.LG.L k, SecRatioEq U.LG.L (x'.left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left s₁ s₂ (T s₁) (T s₂)) → ∀ (y : (thickObj R (maximalIdeal R) e G).left) (s₀ : H0 U.LG.L k) (i i' i'' : Fin 1 → U.LG.L.ι), y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen ((((x).left ≫ (fstG (maximalIdeal R) e G).left).app (secChart U.LG.L i)).hom (s₀.f i)) → y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen (((fstG (maximalIdeal R) e G).left.app (secChart U.LG.L i')).hom ((T s₀).f i')) → y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen ((((x').left ≫ (fstG (maximalIdeal R) e G).left).app (secChart U.LG.L i'')).hom (s₀.f i'')) → ∃ W : (thickObj R (maximalIdeal R) e G).left.Opens, y ∈ W ∧ W.ι ≫ x.left = W.ι ≫ x'.left := by

  intro R _ _ _ hB D A G _ _ hG U
  obtain ⟨k₁, hk₁, H₁⟩ := GlobalTheory.T.thickening_morphisms_agree_beyond_threshold R hB D A G hG U
  obtain ⟨k₂, -, H₂⟩ := GlobalTheory.T.uniformisedGroup_morphisms_agree_near_point R hB D A G hG U
  refine ⟨max k₁ k₂, le_trans hk₁ (le_max_left _ _), ?_⟩
  intro e k k' hk x x' T hx hx' y s₀ i i' i'' hy₁ hy₂ hy₃
  have m₁ : (x.left ≫ (fstG (maximalIdeal R) e G).left) y ∈ secChart U.LG.L i :=
    (thickObj R (maximalIdeal R) e G).left.basicOpen_le _ hy₁
  have m₂ : (fstG (maximalIdeal R) e G).left y ∈ secChart U.LG.L i' :=
    (thickObj R (maximalIdeal R) e G).left.basicOpen_le _ hy₂
  have m₃ : (x'.left ≫ (fstG (maximalIdeal R) e G).left) y ∈ secChart U.LG.L i'' :=
    (thickObj R (maximalIdeal R) e G).left.basicOpen_le _ hy₃
  have u₁ : IsUnit (secGerm (x.left ≫ (fstG (maximalIdeal R) e G).left) y s₀ i) := by
    exact (congrArg IsUnit (gs_eq _ _ _ m₁ _)).mpr ((Scheme.mem_basicOpen (thickObj R (maximalIdeal R) e G).left _ y m₁).1 hy₁)
  have u₂ : IsUnit (secGerm (fstG (maximalIdeal R) e G).left y (T s₀) i') := by
    exact (congrArg IsUnit (gs_eq _ _ _ m₂ _)).mpr ((Scheme.mem_basicOpen (thickObj R (maximalIdeal R) e G).left _ y m₂).1 hy₂)
  have u₃ : IsUnit (secGerm (x'.left ≫ (fstG (maximalIdeal R) e G).left) y s₀ i'') := by
    exact (congrArg IsUnit (gs_eq _ _ _ m₃ _)).mpr ((Scheme.mem_basicOpen (thickObj R (maximalIdeal R) e G).left _ y m₃).1 hy₃)
  have hA : GermRatioAgree (x.left ≫ (fstG (maximalIdeal R) e G).left)
      (x'.left ≫ (fstG (maximalIdeal R) e G).left) s₀ i i'' y := by
    refine ⟨m₁, m₃, u₁, u₃, fun s₁ => ?_⟩
    have e₁ := secRatioEq_iff_germ.1 (hx s₁ s₀) y i i' m₁ m₂
    have e₂ := secRatioEq_iff_germ.1 (hx' s₁ s₀) y i'' i' m₃ m₂
    apply (u₂.mul_left_inj).1
    linear_combination secGerm (x'.left ≫ (fstG (maximalIdeal R) e G).left) y s₀ i'' * e₁ -
      secGerm (x.left ≫ (fstG (maximalIdeal R) e G).left) y s₀ i * e₂
  have hb : x.left ≫ (thickObj R (maximalIdeal R) e G).hom = x'.left ≫ (thickObj R (maximalIdeal R) e G).hom := by
    rw [Over.w x, Over.w x']
  have hk₁' : k₁ ≤ k := le_trans (le_max_left _ _) hk
  have hk₂' : k₂ ≤ k := le_trans (le_max_right _ _) hk
  exact H₂ e k hk₂' _ x.left x'.left hb s₀ i i'' y hA (H₁ e k hk₁' _ x.left x'.left hb s₀ i i'' y hA)

end GlobalTheory.Mum
