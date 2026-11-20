import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GtPtsTor
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.FnOfComp

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

section Units

variable {Y Z W : Scheme.{0}}

/- English proof (translation)
Apply `TopCat.Presheaf.section_ext Z.sheaf ⊤` to reduce the goal to its premises. Introduce `z hz`. Establish `h1` using `congrArg Units.val (h z)`. Unfold `gm pullU at h1`. Establish `m1 : τ₁ z ∈ (⊤ : Y.Opens)` using `trivial`.

Establish `m2 : τ₂ z ∈ (⊤ : Y.Opens)` using `trivial`. Rewrite `h1` using `[dif_pos m1, dif_pos m2]`. Simplify using `only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe] at h1`. Conclude with `h1`.
-/
theorem appTop_eq_of_gm (τ₁ τ₂ : Z ⟶ Y) (c₁ c₂ : Γ(Y, ⊤)ˣ) (h : ∀ z, gm τ₁ z ⊤ c₁ = gm τ₂ z ⊤ c₂) :
    τ₁.appTop.hom c₁.val = τ₂.appTop.hom c₂.val := by
  apply TopCat.Presheaf.section_ext Z.sheaf ⊤
  intro z hz
  have h1 := congrArg Units.val (h z)
  unfold gm pullU at h1
  have m1 : τ₁ z ∈ (⊤ : Y.Opens) := trivial
  have m2 : τ₂ z ∈ (⊤ : Y.Opens) := trivial
  rw [dif_pos m1, dif_pos m2] at h1
  simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe] at h1
  exact h1

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Unfold `gm pullU`. Establish `m1 : (r ≫ τ) w ∈ (⊤ : Y.Opens)` using `trivial`. Establish `m2 : r w ∈ (⊤ : Z.Opens)` using `trivial`. Rewrite using `[dif_pos m1, dif_pos m2]`.

Simplify using `only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, Scheme.Hom.comp_app, CommRingCat.comp_apply]`. Rewrite using `[← h]`. Both sides reduce to the same expression.
-/
theorem gm_comp_top (r : W ⟶ Z) (τ : Z ⟶ Y) (w : W) (c : Γ(Y, ⊤)ˣ) (c' : Γ(Z, ⊤)ˣ)
    (h : τ.appTop.hom c.val = c'.val) : gm (r ≫ τ) w ⊤ c = gm r w ⊤ c' := by
  apply Units.ext
  unfold gm pullU
  have m1 : (r ≫ τ) w ∈ (⊤ : Y.Opens) := trivial
  have m2 : r w ∈ (⊤ : Z.Opens) := trivial
  rw [dif_pos m1, dif_pos m2]
  simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, Scheme.Hom.comp_app,
    CommRingCat.comp_apply]
  rw [← h]
  rfl

/- English proof (translation)
Set `R` to `CommRingCat.of (Polynomial ℤ)`. Set `g : Γ(Z, ⊤) → (R ⟶ Γ(Z, ⊤))` to `fun c => CommRingCat.ofHom (Polynomial.eval₂RingHom (Int.castRingHom _) c)`. Set `φ : Γ(Z, ⊤) → (Z ⟶ Spec R)` to `fun c => Z.toSpecΓ ≫ Spec.map (g c)`. Establish `hrec : ∀ c, ((Scheme.ΓSpecIso R).inv ≫ (φ c).appTop).hom Polynomial.X = c`. Introduce `c`.

Establish `e : (Scheme.ΓSpecIso R).inv ≫ (φ c).appTop = g c`. Simplify using `only [φ, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]`. Rewrite using `[e]`. Conclude with `Polynomial.eval₂_X _ _`. Establish `hg : g a ≫ p.appTop = g b ≫ p.appTop`.

Apply `CommRingCat.hom_ext` to reduce the goal to its premises. Apply `Polynomial.ringHom_ext` to reduce the goal to its premises. Introduce `n`. Simplify using `[g]`. Simplify using `[g, h]`.

Establish `hφ : φ a = φ b`. Rewrite using `[← cancel_epi p]`. Simplify using `only [φ]`. Rewrite using `[← Category.assoc, ← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp, hg]`. Rewrite using `[← hrec a, ← hrec b, hφ]`.
-/
theorem appTop_inj_of_epi (p : W ⟶ Z) [Epi p] {a b : Γ(Z, ⊤)} (h : p.appTop.hom a = p.appTop.hom b) : a = b := by
  classical

  let R := CommRingCat.of (Polynomial ℤ)
  let g : Γ(Z, ⊤) → (R ⟶ Γ(Z, ⊤)) := fun c =>
    CommRingCat.ofHom (Polynomial.eval₂RingHom (Int.castRingHom _) c)
  let φ : Γ(Z, ⊤) → (Z ⟶ Spec R) := fun c => Z.toSpecΓ ≫ Spec.map (g c)
  have hrec : ∀ c, ((Scheme.ΓSpecIso R).inv ≫ (φ c).appTop).hom Polynomial.X = c := by
    intro c
    have e : (Scheme.ΓSpecIso R).inv ≫ (φ c).appTop = g c := by
      simp only [φ, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality,
        Iso.inv_hom_id_assoc]
    rw [e]
    exact Polynomial.eval₂_X _ _
  have hg : g a ≫ p.appTop = g b ≫ p.appTop := by
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro n
      simp [g]
    · simp [g, h]
  have hφ : φ a = φ b := by
    rw [← cancel_epi p]
    simp only [φ]
    rw [← Category.assoc, ← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc,
      Category.assoc, ← Spec.map_comp, ← Spec.map_comp, hg]
  rw [← hrec a, ← hrec b, hφ]

/- English proof (translation)
Substitute `hφ` using the available equality. Take `⟨ρ, hρ⟩` from `TLinPf.ratio_glue _ (TLinPf.linComb_cover L hL φ ε) t t' ht ht'`. Use `⟨ρ, fun Z r z J hJ => ?_⟩` and prove the remaining obligations. Unfold `val`. Use `erw [hρ (fun k => J (r ≫ φ k)), map_mul]`.

Use `congr 1`. Unfold `gm res pullU`. Establish `hm : r z ∈ L.wchart φ (fun k => J (r ≫ φ k))`. Unfold `LB.wchart`. Simplify using the standard rewrite rules.

Conclude with `fun i => hJ (r ≫ φ i)`. Rewrite using `[dif_pos hm, dif_pos (show r z ∈ (⊤ : Y.Opens) from trivial)]`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [MonoidHom.coe_comp, Function.comp_apply, Units.coe_map, MonoidHom.coe_coe]`. Apply the tactic sequence `try erw [Function.comp_apply]`.

Simplify using `only [Units.coe_map, MonoidHom.coe_coe]`. Use `erw [← Scheme.Hom.germ_stalkMap_apply, ← Scheme.Hom.germ_stalkMap_apply]`. Use `erw [TopCat.Presheaf.germ_res_apply]`.
-/
theorem exists_ratio {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)}
    {ε : K → ℤ} (hφ : φ = φ') (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε)) (ht : t.IsGen)
    (ht' : t'.IsGen) : ∃ ρ : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
      val t r z J = gm r z ⊤ ρ * val t' r z J := by
  subst hφ
  obtain ⟨ρ, hρ⟩ := TLinPf.ratio_glue _ (TLinPf.linComb_cover L hL φ ε) t t' ht ht'
  refine ⟨ρ, fun Z r z J hJ => ?_⟩
  unfold val
  erw [hρ (fun k => J (r ≫ φ k)), map_mul]
  congr 1
  unfold gm res pullU
  have hm : r z ∈ L.wchart φ (fun k => J (r ≫ φ k)) := by
    unfold LB.wchart
    simp
    exact fun i => hJ (r ≫ φ i)
  rw [dif_pos hm, dif_pos (show r z ∈ (⊤ : Y.Opens) from trivial)]
  apply Units.ext
  simp only [MonoidHom.coe_comp, Function.comp_apply, Units.coe_map, MonoidHom.coe_coe]
  try erw [Function.comp_apply]
  simp only [Units.coe_map, MonoidHom.coe_coe]
  erw [← Scheme.Hom.germ_stalkMap_apply, ← Scheme.Hom.germ_stalkMap_apply]
  erw [TopCat.Presheaf.germ_res_apply]

/- English proof (translation)
Unfold `val gm charGen res pullU`. Establish `hm : w z ∈ L.wchart PEmpty.elim (fun k => J (w ≫ k.elim))`. Unfold `LB.wchart`. Simplify using the standard rewrite rules. Rewrite using `[dif_pos hm, dif_pos (show (w ≫ (fst (splitTorus S X) G).left) z ∈ (⊤ : (splitTorus S X).left.Opens) from trivial)]`.

Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [MonoidHom.coe_comp, Function.comp_apply, Units.coe_map, MonoidHom.coe_coe, Scheme.Hom.comp_app, CommRingCat.comp_apply]`. Use `erw [Function.comp_apply]`. Simplify using `only [Units.coe_map, MonoidHom.coe_coe]`. Use `erw [← Scheme.Hom.germ_stalkMap_apply, ← Scheme.Hom.germ_stalkMap_apply]`.

Use `erw [TopCat.Presheaf.germ_res_apply]`. Simplify using `only [Units.coe_map, MonoidHom.coe_coe]`. Use `erw [← Scheme.Hom.germ_stalkMap_apply]`. Rewrite using `[Scheme.Hom.stalkMap_comp]`. Both sides reduce to the same expression.
-/
theorem val_charGen {S : Scheme.{0}} (X : Type) [AddCommGroup X] (G : Over S) {L : LB Y} (χ : X)
    (w : W ⟶ (splitTorus S X ⊗ G).left) (z : W) (J : (W ⟶ Y) → L.ι) :
    val (charGen X G L χ) w z J = gm (w ≫ (fst (splitTorus S X) G).left) z ⊤ (charUnit S X χ) := by
  unfold val gm charGen res pullU
  have hm : w z ∈ L.wchart PEmpty.elim (fun k => J (w ≫ k.elim)) := by
    unfold LB.wchart
    simp
  rw [dif_pos hm, dif_pos (show (w ≫ (fst (splitTorus S X) G).left) z ∈
    (⊤ : (splitTorus S X).left.Opens) from trivial)]
  apply Units.ext
  simp only [MonoidHom.coe_comp, Function.comp_apply, Units.coe_map, MonoidHom.coe_coe,
    Scheme.Hom.comp_app, CommRingCat.comp_apply]
  erw [Function.comp_apply]
  simp only [Units.coe_map, MonoidHom.coe_coe]
  erw [← Scheme.Hom.germ_stalkMap_apply, ← Scheme.Hom.germ_stalkMap_apply]
  erw [TopCat.Presheaf.germ_res_apply]
  simp only [Units.coe_map, MonoidHom.coe_coe]
  erw [← Scheme.Hom.germ_stalkMap_apply]
  rw [Scheme.Hom.stalkMap_comp]
  rfl

end Units

section Weight

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

/- English proof (translation)
Establish `hc` using `val_corr hJ (g.t_weight χ) w`. Rewrite `hc` using `[val_pull, val_mul, val_pull, val_charGen]`. Conclude with `hc`. Apply the tactic sequence `all_goals exact hJ`.
-/
theorem val_t_act (χ : D.X) {W : Scheme.{0}} (w : W ⟶ (WeightPf.Te D I e ⊗ thickObj R I e G).left) (z : W)
    {J : (W ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) :
    val (g.t χ) (w ≫ (WeightPf.act g).left) z J =
      gm (w ≫ (fst (WeightPf.Te D I e) (thickObj R I e G)).left) z ⊤ (charUnit _ D.X χ) *
        val (g.t χ) (w ≫ (snd (WeightPf.Te D I e) (thickObj R I e G)).left) z J := by
  have hc := val_corr hJ (g.t_weight χ) w
  rw [val_pull, val_mul, val_pull, val_charGen] at hc
  · exact hc
  all_goals exact hJ

end Weight

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
