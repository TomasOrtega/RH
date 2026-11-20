import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WhiskerLeftEqLift
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PicGlue

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.coe_map, gm_val f y U h, gm_val (𝟙 X) (f y) U h]`. Conclude with `(Scheme.Hom.germ_stalkMap_apply f U y h _).symm`.
-/
theorem germ_pull_eq_stalkMap {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)ˣ) :
    gm f y U a = Units.map (f.stalkMap y).hom.toMonoidHom (gm (𝟙 X) (f y) U a) := by
  apply Units.ext
  rw [Units.coe_map, gm_val f y U h, gm_val (𝟙 X) (f y) U h]
  exact (Scheme.Hom.germ_stalkMap_apply f U y h _).symm

/- English proof (translation)
Use `congrArg (fun f : Y ⟶ Y ↦ f y) hep` as an intermediate fact. Simplify using `using this`.
-/
theorem retract_section_apply {X Y : Scheme.{0}} (p : X ⟶ Y) (e : Y ⟶ X) (hep : e ≫ p = 𝟙 Y) (y : Y) : p (e y) = y := by
  have := congrArg (fun f : Y ⟶ Y ↦ f y) hep
  simpa using this

/- English proof (translation)
Rewrite using `[← _root_.mul_assoc, k, mul_inv]`. Simplify using `only [_root_.mul_assoc]`. Rewrite using `[mul_left_comm F, mul_left_comm F, mul_inv_cancel_left]`.
-/
theorem norm_glue_comm {G : Type} [CommGroup G] (A B F G' R R' : G) (k : A * G' = F * B) :
    A * (G' * R') * (F * R)⁻¹ = B * R' * R⁻¹ := by
  rw [← _root_.mul_assoc, k, mul_inv]
  simp only [_root_.mul_assoc]
  rw [mul_left_comm F, mul_left_comm F, mul_inv_cancel_left]

/- English proof (translation)
Rewrite using `[h]`. Simplify using `only [mul_inv]`. Simplify using `[mul_comm, mul_left_comm, _root_.mul_assoc]`.
-/
theorem norm_match_comm {G : Type} [CommGroup G] (A S R R' : G) (h : S = A * R' * R⁻¹) :
    A * S⁻¹ * R' = R := by
  rw [h]; simp only [mul_inv]; simp [mul_comm, mul_left_comm, _root_.mul_assoc]

/- English proof (translation)
Establish `hpt` using `retract_section_apply p e hep`. Set `O : L.ι × M.ι → Y.Opens` to `fun i ↦ e ⁻¹ᵁ (p ⁻¹ᵁ V ⊓ (L.U i.1 ⊓ M.U i.2))`. Establish `hOV : ∀ i, O i ≤ V` using `fun i y hy ↦ by`. Establish `: p (e y) ∈ V` using `hy.1`. Rewrite `this` using `[hpt]`. Then use the resulting hypothesis.

Establish `hOa : ∀ i, O i ≤ e ⁻¹ᵁ L.U i.1` using `fun i y hy ↦ hy.2.1`. Establish `hOb : ∀ i, O i ≤ e ⁻¹ᵁ M.U i.2` using `fun i y hy ↦ hy.2.2`. Establish `hcov : V ≤ iSup O` using `fun y hy ↦ by`. Establish `hx : e y ∈ p ⁻¹ᵁ V` using `show p (e y) ∈ V by rwa [hpt]`. Take `⟨a, ha⟩` from `hL.cov _ (h₁ hx)`.

Take `⟨b, hb⟩` from `hM.cov _ (h₂ hx)`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨(a, b), ⟨hx, ha, hb⟩⟩`. Set `u : ∀ i, Γ(Y, O i)ˣ` to `fun i ↦ pullU e _ (w i.1 i.2) * res (hOb i) (r' i.2) * (res (hOa i) (r i.1))⁻¹`. Establish `hu : ∀ i, ∀ y ∈ O i, gm (𝟙 Y) y (O i) (u i) = gm e y _ (w i.1 i.2) * gm (𝟙 Y) y _ (r' i.2) * (gm (𝟙 Y) y _ (r i.1))⁻¹`. Introduce `i y hy`.

Simplify using `only [u, map_mul, map_inv]`. Rewrite using `[gm_res (𝟙 Y) y (hOb i) hy, gm_res (𝟙 Y) y (hOa i) hy, gm_pull (𝟙 Y) e y _ hy, Category.id_comp]`. Take `⟨s, hs⟩` from `glue_unit V O hOV hcov u (by`. Introduce `i j y hy`. Rewrite using `[hu i y hy.1, hu j y hy.2]`.

Take `⟨⟨hV, ha, hb⟩, -, ha', hb'⟩` from `hy`. Establish `k` using `congrArg (Units.map (e.stalkMap y).hom.toMonoidHom) (hw (e y) hV i.1 j.1 i.2 j.2 ha ha' hb hb')`. Simplify using `only [map_mul, ← germ_pull_eq_stalkMap] at k`. Rewrite `k` using `[← germ_pull_eq_stalkMap e y (p ⁻¹ᵁ V ⊓ (L.U i.1 ⊓ M.U i.2)) ⟨hV, ha, hb⟩, ← germ_pull_eq_stalkMap e y (M.U i.2 ⊓ M.U j.2) ⟨hb, hb'⟩, ← germ_pull_eq_stalkMap e y (L.U i.1 ⊓ L.U j.1) ⟨ha, ha'⟩, ← germ_pull_eq_stalkMap e y (p ⁻¹ᵁ V ⊓ (L.U j.1 ⊓ M.U j.2)) ⟨hV, ha', hb'⟩]`. Rewrite using `[hr y i.1 j.1 ha ha', hr' y i.2 j.2 hb hb']`.

Conclude with `norm_glue_comm _ _ _ _ _ _ k)`. Establish `hle : ∀ (a : L.ι) (b : M.ι), p ⁻¹ᵁ V ⊓ (L.U a ⊓ M.U b) ≤ p ⁻¹ᵁ V` using `fun _ _ ↦ inf_le_left`. Use `⟨fun a b ↦ w a b * (res (hle a b) (pullU p V s))⁻¹, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx a a' b b' ha ha' hb hb'`. Simplify using `only [map_mul, map_inv]`.

Rewrite using `[gm_res (𝟙 X) x (hle a b) ⟨hx, ha, hb⟩, gm_res (𝟙 X) x (hle a' b') ⟨hx, ha', hb'⟩]`. Establish `k` using `hw x hx a a' b b' ha ha' hb hb'`. Rewrite using `[mul_right_comm, k, _root_.mul_assoc]`. Introduce `y a b hV ha hb`. Simplify using `only [map_mul, map_inv]`.

Establish `hy : y ∈ O (a, b)` using `⟨hV, ha, hb⟩`. Rewrite using `[gm_res e y (hle a b) ⟨hV, ha, hb⟩, gm_pull e p y V hV, hep, ← gm_res (𝟙 Y) y (hOV (a, b)) hy, hs, hu (a, b) y hy]`. Conclude with `norm_match_comm _ _ _ _ rfl`.
-/
theorem exists_norm (X Y : Scheme.{0}) (p : X ⟶ Y) (e : Y ⟶ X) (hep : e ≫ p = 𝟙 Y) (V : Y.Opens)
    (W₁ W₂ : X.Opens) (L M : LB X) (w : Cmp (p ⁻¹ᵁ V) L M) (r : RigD e L) (r' : RigD e M)
    (hL : IsOn W₁ L) (hM : IsOn W₂ M) (h₁ : p ⁻¹ᵁ V ≤ W₁) (h₂ : p ⁻¹ᵁ V ≤ W₂)
    (hw : IsoOn (p ⁻¹ᵁ V) L M w) (hr : RigOn e L r) (hr' : RigOn e M r') :
    ∃ w' : Cmp (p ⁻¹ᵁ V) L M, IsoOn (p ⁻¹ᵁ V) L M w' ∧ Norm e (p ⁻¹ᵁ V) L M w' r r' := by
  have hpt := retract_section_apply p e hep
  let O : L.ι × M.ι → Y.Opens := fun i ↦ e ⁻¹ᵁ (p ⁻¹ᵁ V ⊓ (L.U i.1 ⊓ M.U i.2))
  have hOV : ∀ i, O i ≤ V := fun i y hy ↦ by
    have : p (e y) ∈ V := hy.1
    rwa [hpt] at this
  have hOa : ∀ i, O i ≤ e ⁻¹ᵁ L.U i.1 := fun i y hy ↦ hy.2.1
  have hOb : ∀ i, O i ≤ e ⁻¹ᵁ M.U i.2 := fun i y hy ↦ hy.2.2
  have hcov : V ≤ iSup O := fun y hy ↦ by
    have hx : e y ∈ p ⁻¹ᵁ V := show p (e y) ∈ V by rwa [hpt]
    obtain ⟨a, ha⟩ := hL.cov _ (h₁ hx)
    obtain ⟨b, hb⟩ := hM.cov _ (h₂ hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(a, b), ⟨hx, ha, hb⟩⟩
  let u : ∀ i, Γ(Y, O i)ˣ := fun i ↦
    pullU e _ (w i.1 i.2) * res (hOb i) (r' i.2) * (res (hOa i) (r i.1))⁻¹
  have hu : ∀ i, ∀ y ∈ O i, gm (𝟙 Y) y (O i) (u i) =
      gm e y _ (w i.1 i.2) * gm (𝟙 Y) y _ (r' i.2) * (gm (𝟙 Y) y _ (r i.1))⁻¹ := by
    intro i y hy
    simp only [u, map_mul, map_inv]
    rw [gm_res (𝟙 Y) y (hOb i) hy, gm_res (𝟙 Y) y (hOa i) hy, gm_pull (𝟙 Y) e y _ hy, Category.id_comp]
  obtain ⟨s, hs⟩ := glue_unit V O hOV hcov u (by
    intro i j y hy
    rw [hu i y hy.1, hu j y hy.2]
    obtain ⟨⟨hV, ha, hb⟩, -, ha', hb'⟩ := hy
    have k := congrArg (Units.map (e.stalkMap y).hom.toMonoidHom) (hw (e y) hV i.1 j.1 i.2 j.2 ha ha' hb hb')
    simp only [map_mul, ← germ_pull_eq_stalkMap] at k
    rw [← germ_pull_eq_stalkMap e y (p ⁻¹ᵁ V ⊓ (L.U i.1 ⊓ M.U i.2)) ⟨hV, ha, hb⟩,
      ← germ_pull_eq_stalkMap e y (M.U i.2 ⊓ M.U j.2) ⟨hb, hb'⟩,
      ← germ_pull_eq_stalkMap e y (L.U i.1 ⊓ L.U j.1) ⟨ha, ha'⟩,
      ← germ_pull_eq_stalkMap e y (p ⁻¹ᵁ V ⊓ (L.U j.1 ⊓ M.U j.2)) ⟨hV, ha', hb'⟩] at k
    rw [hr y i.1 j.1 ha ha', hr' y i.2 j.2 hb hb']
    exact norm_glue_comm _ _ _ _ _ _ k)
  have hle : ∀ (a : L.ι) (b : M.ι), p ⁻¹ᵁ V ⊓ (L.U a ⊓ M.U b) ≤ p ⁻¹ᵁ V := fun _ _ ↦ inf_le_left
  refine ⟨fun a b ↦ w a b * (res (hle a b) (pullU p V s))⁻¹, ?_, ?_⟩
  · intro x hx a a' b b' ha ha' hb hb'
    simp only [map_mul, map_inv]
    rw [gm_res (𝟙 X) x (hle a b) ⟨hx, ha, hb⟩, gm_res (𝟙 X) x (hle a' b') ⟨hx, ha', hb'⟩]
    have k := hw x hx a a' b b' ha ha' hb hb'
    rw [mul_right_comm, k, _root_.mul_assoc]
  · intro y a b hV ha hb
    simp only [map_mul, map_inv]
    have hy : y ∈ O (a, b) := ⟨hV, ha, hb⟩
    rw [gm_res e y (hle a b) ⟨hV, ha, hb⟩, gm_pull e p y V hV, hep, ← gm_res (𝟙 Y) y (hOV (a, b)) hy, hs,
      hu (a, b) y hy]
    exact norm_match_comm _ _ _ _ rfl

end GlobalTheory.PicGlue
