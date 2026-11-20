import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSectionRatioEqNearThickeningPointStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecRatioEqRefl
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermRatioAgreeSelf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.LocAgree

/- English proof (translation)
Establish `hy : (𝟙 Y : Y ⟶ Y) y ∈ u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i'` using `⟨hi, hi'⟩`. Rewrite using `[gs_mul _ _ _ hy, gs_res _ _ _ hy, gs_res _ _ _ hy]`. Conclude with `congrArg₂ (· * ·) (gs_pull (𝟙 Y) u y _ hi _) (gs_pull (𝟙 Y) v y _ hi' _)`.
-/
theorem gs_prod {X Y : Scheme.{0}} {L : LB X} {k : ℕ} (u v : Y ⟶ X) (i i' : Fin 1 → L.ι) (y : Y)
    (hi : u y ∈ secChart L i) (hi' : v y ∈ secChart L i') (s t : H0 L k) :
    gs (𝟙 Y) y (u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i')
        ((Y.presheaf.map (homOfLE (inf_le_left : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ u ⁻¹ᵁ secChart L i)).op).hom
          ((u.app (secChart L i)).hom (s.f i)) *
        (Y.presheaf.map (homOfLE (inf_le_right : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ v ⁻¹ᵁ secChart L i')).op).hom
          ((v.app (secChart L i')).hom (t.f i'))) = secGerm u y s i * secGerm v y t i' := by
  have hy : (𝟙 Y : Y ⟶ Y) y ∈ u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' := ⟨hi, hi'⟩
  rw [gs_mul _ _ _ hy, gs_res _ _ _ hy, gs_res _ _ _ hy]
  exact congrArg₂ (· * ·) (gs_pull (𝟙 Y) u y _ hi _) (gs_pull (𝟙 Y) v y _ hi' _)

/- English proof (translation)
Rewrite `h` using `[gs_eq _ z O hz, gs_eq _ z O hz]`. Take `⟨V, hzV, iU, iV, e⟩` from `TopCat.Presheaf.germ_eq Z.presheaf z hz hz _ _ h`. Use `⟨V, hzV, leOfHom iU, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hxO : (𝟙 Z : Z ⟶ Z) x ∈ O` using `leOfHom iU hx`. Rewrite using `[gs_eq _ x O hxO, gs_eq _ x O hxO]`.

Conclude with `(TopCat.Presheaf.germ_res_apply Z.presheaf iU x hx _).symm.trans ((congrArg (Z.presheaf.germ V x hx).hom e).trans (TopCat.Presheaf.germ_res_apply Z.presheaf iV x hx _))`.
-/
theorem gs_nbhd {Z : Scheme.{0}} {O : Z.Opens} (a b : Γ(Z, O)) (z : Z) (hz : z ∈ O)
    (h : gs (𝟙 Z) z O a = gs (𝟙 Z) z O b) :
    ∃ V : Z.Opens, z ∈ V ∧ V ≤ O ∧ ∀ x ∈ V, gs (𝟙 Z) x O a = gs (𝟙 Z) x O b := by
  rw [gs_eq _ z O hz, gs_eq _ z O hz] at h
  obtain ⟨V, hzV, iU, iV, e⟩ := TopCat.Presheaf.germ_eq Z.presheaf z hz hz _ _ h
  refine ⟨V, hzV, leOfHom iU, fun x hx => ?_⟩
  have hxO : (𝟙 Z : Z ⟶ Z) x ∈ O := leOfHom iU hx
  rw [gs_eq _ x O hxO, gs_eq _ x O hxO]
  exact (TopCat.Presheaf.germ_res_apply Z.presheaf iU x hx _).symm.trans
    ((congrArg (Z.presheaf.germ V x hx).hom e).trans (TopCat.Presheaf.germ_res_apply Z.presheaf iV x hx _))

end GlobalTheory.Mum.LocAgree

namespace GlobalTheory.Mum.LocAgree

/- English proof (translation)
Introduce `R _ _ _ hB D A G _ _ hG U`. Take `⟨k₀, hk₀, hK⟩` from `GlobalTheory.T.eq_of_sectionRatio_eq_near_thickening_point R hB D A G hG U`. Use `⟨k₀, hk₀, fun e k hk Z u u' hu s₀ i i'' z hg hz => ?_⟩` and prove the remaining obligations. Take `⟨hi, hi'', hunit, hunit', hall⟩` from `hg`. Use `set p := (fstG (maximalIdeal R) e G).left with hp`.

Establish `hiw : p (u z) ∈ secChart U.LG.L i` using `hi`. Establish `hunitw : IsUnit (secGerm p (u z) s₀ i)`. Rewrite `hunit` using `[secGerm_comp u p z s₀ hiw]`. Conclude with `(isUnit_map_iff (u.stalkMap z).hom _).1 hunit`. Take `⟨N, m, σ, hwN, hmono⟩` from `hK e k hk s₀ i (u z) hiw hunitw`.

Establish `hz' : z ∈ (u ≫ p) ⁻¹ᵁ secChart U.LG.L i ⊓ (u' ≫ p) ⁻¹ᵁ secChart U.LG.L i''` using `⟨hi, hi''⟩`. Establish `hV : ∀ l, ∃ V : Z.Opens, z ∈ V ∧ V ≤ (u ≫ p) ⁻¹ᵁ secChart U.LG.L i ⊓ (u' ≫ p) ⁻¹ᵁ secChart U.LG.L i'' ∧ ∀ x ∈ V, secGerm (u ≫ p) x (σ l) i * secGerm (u' ≫ p) x s₀ i'' = secGerm (u ≫ p) x s₀ i * secGerm (u' ≫ p) x (σ l) i''`. Introduce `l`. Take `⟨V, hzV, hVO, hx⟩` from `gs_nbhd _ _ z hz' ((gs_prod (u ≫ p) (u' ≫ p) i i'' z hi hi'' (σ l) s₀).trans ((hall (σ l)).trans (gs_prod (u ≫ p) (u' ≫ p) i i'' z hi hi'' s₀ (σ l)).symm))`. Use `⟨V, hzV, hVO, fun x hxV => ?_⟩` and prove the remaining obligations.

Establish `hxO` using `hVO hxV`. Rewrite using `[← gs_prod (u ≫ p) (u' ≫ p) i i'' x hxO.1 hxO.2, ← gs_prod (u ≫ p) (u' ≫ p) i i'' x hxO.1 hxO.2]`. Conclude with `hx x hxV`. Use `choose V hzV hVO hVx using hV`. Set `W : Z.Opens` to `⟨(⋂ l, (V l : Set Z)) ∩ ((u ≫ p) ⁻¹ᵁ secChart U.LG.L i ⊓ (u' ≫ p) ⁻¹ᵁ secChart U.LG.L i'' : Z.Opens) ∩ (u ⁻¹ᵁ N : Set Z) ∩ (u' ⁻¹ᵁ N : Set Z), (((isOpen_iInter_of_finite fun l => (V l).isOpen).inter (TopologicalSpace.Opens.isOpen _)).inter (TopologicalSpace.Opens.isOpen _)).inter …`.

Establish `hzW : z ∈ W` using `⟨⟨⟨Set.mem_iInter.2 hzV, hz'⟩, hwN⟩, show u' z ∈ N from hz ▸ hwN⟩`. Use `⟨W, hzW, ?_⟩` and prove the remaining obligations. Establish `hmem : ∀ x : W.toScheme, W.ι x ∈ W` using `fun x => by`. Establish `h : W.ι x ∈ Set.range W.ι` using `⟨x, rfl⟩`. Rewrite `h` using `[Scheme.Opens.range_ι]`. Then use the resulting hypothesis.

Apply `hmono W.toScheme (W.ι ≫ u) (W.ι ≫ u')` to reduce the goal to its premises. Simplify using `only [Category.assoc, hu]`. Introduce `x`. Conclude with `(hmem x).1.2`. Introduce `x`.

Conclude with `(hmem x).2`. Introduce `l`. Use `secRatioEq_of_exists_germ fun x => ⟨i, i'', (hmem x).1.1.2.1, (hmem x).1.1.2.2, ?_⟩` and prove the remaining obligations. Simplify using `only [Category.assoc]`. Rewrite using `[secGerm_comp W.ι (u ≫ p) x _ (hmem x).1.1.2.1, secGerm_comp W.ι (u ≫ p) x _ (hmem x).1.1.2.1, secGerm_comp W.ι (u' ≫ p) x _ (hmem x).1.1.2.2, secGerm_comp W.ι (u' ≫ p) x _ (hmem x).1.1.2.2, ← map_mul, ← map_mul, hVx l _ (Set.mem_iInter.1 (hmem x).1.1.1 l)]`.
-/
theorem locAgree : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ (e k : ℕ), k₀ ≤ k → ∀ (Z : Scheme.{0}) (u u' : Z ⟶ (thickObj R (maximalIdeal R) e G).left), u ≫ (thickObj R (maximalIdeal R) e G).hom = u' ≫ (thickObj R (maximalIdeal R) e G).hom → ∀ (s₀ : H0 U.LG.L k) (i i'' : Fin 1 → U.LG.L.ι) (z : Z), GermRatioAgree (u ≫ (fstG (maximalIdeal R) e G).left) (u' ≫ (fstG (maximalIdeal R) e G).left) s₀ i i'' z → u z = u' z → ∃ W : Z.Opens, z ∈ W ∧ W.ι ≫ u = W.ι ≫ u' := by
  intro R _ _ _ hB D A G _ _ hG U
  obtain ⟨k₀, hk₀, hK⟩ := GlobalTheory.T.eq_of_sectionRatio_eq_near_thickening_point R hB D A G hG U
  refine ⟨k₀, hk₀, fun e k hk Z u u' hu s₀ i i'' z hg hz => ?_⟩
  obtain ⟨hi, hi'', hunit, hunit', hall⟩ := hg
  set p := (fstG (maximalIdeal R) e G).left with hp
  have hiw : p (u z) ∈ secChart U.LG.L i := hi
  have hunitw : IsUnit (secGerm p (u z) s₀ i) := by
    rw [secGerm_comp u p z s₀ hiw] at hunit
    exact (isUnit_map_iff (u.stalkMap z).hom _).1 hunit
  obtain ⟨N, m, σ, hwN, hmono⟩ := hK e k hk s₀ i (u z) hiw hunitw

  have hz' : z ∈ (u ≫ p) ⁻¹ᵁ secChart U.LG.L i ⊓ (u' ≫ p) ⁻¹ᵁ secChart U.LG.L i'' := ⟨hi, hi''⟩
  have hV : ∀ l, ∃ V : Z.Opens, z ∈ V ∧ V ≤ (u ≫ p) ⁻¹ᵁ secChart U.LG.L i ⊓ (u' ≫ p) ⁻¹ᵁ secChart U.LG.L i'' ∧
      ∀ x ∈ V, secGerm (u ≫ p) x (σ l) i * secGerm (u' ≫ p) x s₀ i'' =
        secGerm (u ≫ p) x s₀ i * secGerm (u' ≫ p) x (σ l) i'' := by
    intro l
    obtain ⟨V, hzV, hVO, hx⟩ := gs_nbhd _ _ z hz'
      ((gs_prod (u ≫ p) (u' ≫ p) i i'' z hi hi'' (σ l) s₀).trans ((hall (σ l)).trans
        (gs_prod (u ≫ p) (u' ≫ p) i i'' z hi hi'' s₀ (σ l)).symm))
    refine ⟨V, hzV, hVO, fun x hxV => ?_⟩
    have hxO := hVO hxV
    rw [← gs_prod (u ≫ p) (u' ≫ p) i i'' x hxO.1 hxO.2, ← gs_prod (u ≫ p) (u' ≫ p) i i'' x hxO.1 hxO.2]
    exact hx x hxV
  choose V hzV hVO hVx using hV
  let W : Z.Opens := ⟨(⋂ l, (V l : Set Z)) ∩ ((u ≫ p) ⁻¹ᵁ secChart U.LG.L i ⊓ (u' ≫ p) ⁻¹ᵁ secChart U.LG.L i'' : Z.Opens)
      ∩ (u ⁻¹ᵁ N : Set Z) ∩ (u' ⁻¹ᵁ N : Set Z),
    (((isOpen_iInter_of_finite fun l => (V l).isOpen).inter (TopologicalSpace.Opens.isOpen _)).inter (TopologicalSpace.Opens.isOpen _)).inter
      (TopologicalSpace.Opens.isOpen _)⟩
  have hzW : z ∈ W := ⟨⟨⟨Set.mem_iInter.2 hzV, hz'⟩, hwN⟩, show u' z ∈ N from hz ▸ hwN⟩
  refine ⟨W, hzW, ?_⟩
  have hmem : ∀ x : W.toScheme, W.ι x ∈ W := fun x => by
    have h : W.ι x ∈ Set.range W.ι := ⟨x, rfl⟩
    rwa [Scheme.Opens.range_ι] at h
  apply hmono W.toScheme (W.ι ≫ u) (W.ι ≫ u')
  · simp only [Category.assoc, hu]
  · intro x; exact (hmem x).1.2
  · intro x; exact (hmem x).2
  · intro l
    refine secRatioEq_of_exists_germ fun x => ⟨i, i'', (hmem x).1.1.2.1, (hmem x).1.1.2.2, ?_⟩
    simp only [Category.assoc]
    rw [secGerm_comp W.ι (u ≫ p) x _ (hmem x).1.1.2.1, secGerm_comp W.ι (u ≫ p) x _ (hmem x).1.1.2.1,
      secGerm_comp W.ι (u' ≫ p) x _ (hmem x).1.1.2.2, secGerm_comp W.ι (u' ≫ p) x _ (hmem x).1.1.2.2,
      ← map_mul, ← map_mul, hVx l _ (Set.mem_iInter.1 (hmem x).1.1.1 l)]

end GlobalTheory.Mum.LocAgree
