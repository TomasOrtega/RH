import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHom
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.LBPush

/- English proof (translation)
Establish `hU : (𝟙 X) (κ z) ∈ U` using `h`. Unfold `gm pullU at e ⊢`. Rewrite `e` using `[dif_pos h]`. Rewrite using `[dif_pos hU]`. Establish `e'` using `congrArg Units.val e`.

Apply `Units.ext` to reduce the goal to its premises. Apply `(ConcreteCategory.bijective_of_isIso (κ.stalkMap z)).1` to reduce the goal to its premises. Use `((Scheme.Hom.germ_stalkMap_apply κ U z h (a : Γ(X, U))).trans ?_).trans (map_one _).symm` and prove the remaining obligations. Conclude with `e'`.
-/
theorem gm_eq_one {X Z : Scheme.{0}} (κ : Z ⟶ X) [IsOpenImmersion κ] (z : Z) {U : X.Opens} (h : κ z ∈ U)
    {a : Γ(X, U)ˣ} (e : gm κ z U a = 1) : gm (𝟙 X) (κ z) U a = 1 := by
  have hU : (𝟙 X) (κ z) ∈ U := h
  unfold gm pullU at e ⊢
  rw [dif_pos h] at e
  rw [dif_pos hU]
  have e' := congrArg Units.val e
  apply Units.ext
  apply (ConcreteCategory.bijective_of_isIso (κ.stalkMap z)).1
  refine ((Scheme.Hom.germ_stalkMap_apply κ U z h (a : Γ(X, U))).trans ?_).trans (map_one _).symm
  exact e'

/- English proof (translation)
Use `⟨Units.map (κ.appIso V).inv.hom a, fun Z r z hz => ?_⟩` and prove the remaining obligations. Establish `h1 : (r ≫ κ) z ∈ κ ''ᵁ V` using `⟨r z, hz, rfl⟩`. Unfold `gm pullU`. Rewrite using `[dif_pos hz, dif_pos h1]`. Apply `Units.ext` to reduce the goal to its premises.

Use `(Scheme.Hom.germ_stalkMap_apply (r ≫ κ) (κ ''ᵁ V) z h1 _).symm.trans ?_` and prove the remaining obligations. Use `Eq.trans ?_ (Scheme.Hom.germ_stalkMap_apply r V z hz (a : Γ(Y, V)))` and prove the remaining obligations. Rewrite using `[Scheme.Hom.stalkMap_comp]`. Use `congrArg (r.stalkMap z) ?_` and prove the remaining obligations. Use `(Scheme.Hom.germ_stalkMap_apply κ (κ ''ᵁ V) (r z) h1 _).trans ?_` and prove the remaining obligations.

Use `(congrArg (ConcreteCategory.hom (Y.presheaf.germ (κ ⁻¹ᵁ κ ''ᵁ V) (r z) h1)) (Scheme.Hom.appIso_inv_app_apply κ V (a : Γ(Y, V)))).trans ?_` and prove the remaining obligations. Conclude with `TopCat.Presheaf.germ_res_apply' Y.presheaf _ (r z) _ _`.
-/
theorem exists_unit_image {X Y : Scheme.{0}} (κ : Y ⟶ X) [IsOpenImmersion κ] (V : Y.Opens) (a : Γ(Y, V)ˣ) :
    ∃ b : Γ(X, κ ''ᵁ V)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), r z ∈ V →
      gm (r ≫ κ) z (κ ''ᵁ V) b = gm r z V a := by
  refine ⟨Units.map (κ.appIso V).inv.hom a, fun Z r z hz => ?_⟩
  have h1 : (r ≫ κ) z ∈ κ ''ᵁ V := ⟨r z, hz, rfl⟩
  unfold gm pullU
  rw [dif_pos hz, dif_pos h1]
  apply Units.ext
  refine (Scheme.Hom.germ_stalkMap_apply (r ≫ κ) (κ ''ᵁ V) z h1 _).symm.trans ?_
  refine Eq.trans ?_ (Scheme.Hom.germ_stalkMap_apply r V z hz (a : Γ(Y, V)))
  rw [Scheme.Hom.stalkMap_comp]
  refine congrArg (r.stalkMap z) ?_
  refine (Scheme.Hom.germ_stalkMap_apply κ (κ ''ᵁ V) (r z) h1 _).trans ?_
  refine (congrArg (ConcreteCategory.hom (Y.presheaf.germ (κ ⁻¹ᵁ κ ''ᵁ V) (r z) h1))
    (Scheme.Hom.appIso_inv_app_apply κ V (a : Γ(Y, V)))).trans ?_
  exact TopCat.Presheaf.germ_res_apply' Y.presheaf _ (r z) _ _

/- English proof (translation)
Unfold `gm pullU res`. Rewrite using `[dif_pos ht, dif_pos (hVU ht)]`. Apply `Units.ext` to reduce the goal to its premises. Use `(Scheme.Hom.germ_stalkMap_apply f V t ht _).symm.trans ?_` and prove the remaining obligations. Use `Eq.trans ?_ (Scheme.Hom.germ_stalkMap_apply f U t (hVU ht) (a : Γ(S, U)))` and prove the remaining obligations.

Use `congr 1`. Conclude with `TopCat.Presheaf.germ_res_apply S.presheaf (homOfLE hVU) (f t) ht _`.
-/
private theorem gm_res_eq_gm {S T : Scheme.{0}} (f : T ⟶ S) (t : T) {U V : S.Opens} (hVU : V ≤ U) (a : Γ(S, U)ˣ)
    (ht : f t ∈ V) : gm f t V (res hVU a) = gm f t U a := by
  unfold gm pullU res
  rw [dif_pos ht, dif_pos (hVU ht)]
  apply Units.ext
  refine (Scheme.Hom.germ_stalkMap_apply f V t ht _).symm.trans ?_
  refine Eq.trans ?_ (Scheme.Hom.germ_stalkMap_apply f U t (hVU ht) (a : Γ(S, U)))
  congr 1
  exact TopCat.Presheaf.germ_res_apply S.presheaf (homOfLE hVU) (f t) ht _

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Apply `TopCat.Presheaf.section_ext S.sheaf W` to reduce the goal to its premises. Introduce `x hx`. Use `congrArg Units.val (h x hx)` as an intermediate fact. Unfold `gm pullU at this`.

Rewrite `this` using `[dif_pos (show (𝟙 S) x ∈ W from hx)]`. Conclude with `this`.
-/
private theorem units_eq_of_gm_eq {S : Scheme.{0}} {W : S.Opens} {a b : Γ(S, W)ˣ}
    (h : ∀ x, x ∈ W → gm (𝟙 S) x W a = gm (𝟙 S) x W b) : a = b := by
  apply Units.ext
  apply TopCat.Presheaf.section_ext S.sheaf W
  intro x hx
  have := congrArg Units.val (h x hx)
  unfold gm pullU at this
  rw [dif_pos (show (𝟙 S) x ∈ W from hx)] at this
  exact this

/- English proof (translation)
Unfold `gm`. Rewrite using `[dif_pos (show (𝟙 T) t ∈ f ⁻¹ᵁ W from ht), dif_pos ht]`. Both sides reduce to the same expression.
-/
private theorem gm_id_pullU' {S T : Scheme.{0}} (f : T ⟶ S) (t : T) (W : S.Opens) (c : Γ(S, W)ˣ) (ht : f t ∈ W) :
    gm (𝟙 T) t (f ⁻¹ᵁ W) (pullU f W c) = gm f t W c := by
  unfold gm
  rw [dif_pos (show (𝟙 T) t ∈ f ⁻¹ᵁ W from ht), dif_pos ht]
  rfl

/- English proof (translation)
The claim follows from `map_inv _ _`.
-/
private theorem gm_inv_moduli {S T : Scheme.{0}} (f : T ⟶ S) (t : T) (U : S.Opens) (a : Γ(S, U)ˣ) :
    gm f t U a⁻¹ = (gm f t U a)⁻¹ :=
  map_inv _ _

/- English proof (translation)
Apply `units_eq_of_gm_eq` to reduce the goal to its premises. Introduce `x hx`. Rewrite using `[map_mul, map_mul, gm_inv_moduli, gm_res_eq_gm (𝟙 S) x hA a hx, gm_res_eq_gm (𝟙 S) x hB b hx, gm_res_eq_gm (𝟙 S) x hC c hx, gm_res_eq_gm (𝟙 S) x hD d hx]`. Conclude with `h x hx`.
-/
private theorem res_eq_mul_inv_mul_of_gm {S : Scheme.{0}} {W A B C D : S.Opens} (hA : W ≤ A) (hB : W ≤ B) (hC : W ≤ C)
    (hD : W ≤ D) (a : Γ(S, A)ˣ) (b : Γ(S, B)ˣ) (c : Γ(S, C)ˣ) (d : Γ(S, D)ˣ)
    (h : ∀ x, x ∈ W → gm (𝟙 S) x A a = gm (𝟙 S) x B b * (gm (𝟙 S) x C c)⁻¹ * gm (𝟙 S) x D d) :
    res hA a = res hB b * (res hC c)⁻¹ * res hD d := by
  apply units_eq_of_gm_eq
  intro x hx
  rw [map_mul, map_mul, gm_inv_moduli, gm_res_eq_gm (𝟙 S) x hA a hx, gm_res_eq_gm (𝟙 S) x hB b hx,
    gm_res_eq_gm (𝟙 S) x hC c hx, gm_res_eq_gm (𝟙 S) x hD d hx]
  exact h x hx

/- English proof (translation)
Introduce `X Y ψ _ L hL`. Establish `himg : ∀ i j, ψ ''ᵁ L.U i ⊓ ψ ''ᵁ L.U j ≤ ψ ''ᵁ (L.U i ⊓ L.U j)`. Introduce and unpack `i j x ⟨⟨y, hy, rfl⟩, ⟨y', hy', e⟩⟩`. Establish `e' : y' = y` using `ψ.isOpenEmbedding.injective e`. Rewrite `hy'` using `[e']`.

Conclude with `⟨y, ⟨hy, hy'⟩, rfl⟩`. Use `choose b hb using fun i j => exists_unit_image ψ (L.U i ⊓ L.U j) (L.g i j)`. Set `M : LB X` to `⟨L.ι, fun i => ψ ''ᵁ L.U i, fun i j => res (himg i j) (b i j)⟩`. Establish `hcov : ∀ y : Y, ∃ i, y ∈ L.U i`. Introduce `y`.

Establish `hy : y ∈ ⨆ i, L.U i` using `by rw [hL.cover]; trivial`. Conclude with `TopologicalSpace.Opens.mem_iSup.1 hy`. Establish `hmem : ∀ (j : PUnit → L.ι) (y : Y), y ∈ (M.pull ψ).U j ↔ y ∈ L.U (j PUnit.unit)`. Introduce `j y`. Prove the components needed by the constructor for the conclusion.

Introduce `hy`. Take `⟨y', hy', e⟩` from `Set.mem_iInter.1 hy PUnit.unit`. Rewrite `hy'` using `[ψ.isOpenEmbedding.injective e]`. Then use the resulting hypothesis. Introduce `hy`. Conclude with `Set.mem_iInter.2 fun k => ⟨y, hy, rfl⟩`.

Establish `Gself : ∀ i y, y ∈ L.U i → gm (𝟙 Y) y (L.U i ⊓ L.U i) (L.g i i) = 1`. Introduce `i y hy`. Use `congrArg (gm (𝟙 Y) y _) (hL.g_self i)` as an intermediate fact. Rewrite `this` using `[gm_res_eq_gm (𝟙 Y) y, map_one]`. Conclude with `this`.

Conclude with `hy`. Establish `Gcoc : ∀ i j k y, y ∈ L.U i → y ∈ L.U j → y ∈ L.U k → gm (𝟙 Y) y (L.U i ⊓ L.U j) (L.g i j) * gm (𝟙 Y) y (L.U j ⊓ L.U k) (L.g j k) = gm (𝟙 Y) y (L.U i ⊓ L.U k) (L.g i k)`. Introduce `i j k y hi hj hk`. Use `congrArg (gm (𝟙 Y) y _) (hL.cocycle i j k)` as an intermediate fact. Rewrite `this` using `[map_mul, gm_res_eq_gm (𝟙 Y) y, gm_res_eq_gm (𝟙 Y) y, gm_res_eq_gm (𝟙 Y) y]`.

Conclude with `this`. Apply the tactic sequence `all_goals exact ⟨⟨hi, hj⟩, hk⟩`. Establish `key : ∀ i j y, y ∈ L.U i → y ∈ L.U j → gm ψ y (M.U i ⊓ M.U j) (M.g i j) = gm (𝟙 Y) y (L.U i ⊓ L.U j) (L.g i j)`. Introduce `i j y hi hj`. Use `hb i j Y (𝟙 Y) y ⟨hi, hj⟩` as an intermediate fact.

Rewrite `this` using `[Category.id_comp]`. Conclude with `(gm_res_eq_gm ψ y (himg i j) (b i j) ⟨⟨y, hi, rfl⟩, ⟨y, hj, rfl⟩⟩).trans this`. Establish `hN : ∀ (j j' : PUnit → L.ι) y, y ∈ L.U (j PUnit.unit) → y ∈ L.U (j' PUnit.unit) → gm (𝟙 Y) y ((M.pull ψ).U j ⊓ (M.pull ψ).U j') ((M.pull ψ).g j j') = gm (𝟙 Y) y (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit)) (L.g (j PUnit.unit) (j' PUnit.unit))`. Introduce `j j' y h1 h2`. Rewrite using `[← key _ _ y h1 h2]`.

Unfold `LB.pull LB.LinComb`. Simplify using `only`. Rewrite using `[map_prod, Fintype.prod_unique, map_zpow, zpow_one]`. Use `(gm_res_eq_gm (𝟙 Y) y _ _ ?_).trans (gm_id_pullU' ψ y (M.U (j default) ⊓ M.U (j' default)) _ ?_)` and prove the remaining obligations. Apply the tactic sequence `all_goals first`.

Consider the case `exact ⟨(hmem j y).2 h1, (hmem j' y).2 h2⟩`. Consider the case `exact ⟨⟨y, h1, rfl⟩, ⟨y, h2, rfl⟩⟩`. Use `⟨M, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`.

Take `⟨i, y, hy, rfl⟩` from `TopologicalSpace.Opens.mem_iSup.1 hx`. Conclude with `⟨y, rfl⟩`. Introduce and unpack `x ⟨y, rfl⟩`. Take `⟨i, hi⟩` from `hcov y`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨i, y, hi, rfl⟩`.

Introduce and unpack `a x ⟨y, hy, rfl⟩`. Conclude with `gm_eq_one ψ y (U := M.U a ⊓ M.U a) ⟨⟨y, hy, rfl⟩, ⟨y, hy, rfl⟩⟩ ((key a a y hy hy).trans (Gself a y hy))`. Apply `eq_top_iff.2` to reduce the goal to its premises. Introduce `y _`. Take `⟨i, hi⟩` from `hcov y`.

Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, (hmem _ y).2 hi⟩`. Introduce `j`. Apply `units_eq_of_gm_eq` to reduce the goal to its premises. Introduce `y hy`. Establish `h1` using `(hmem j y).1 hy`.

Rewrite using `[gm_res_eq_gm (𝟙 Y) y, map_one, hN j j y h1 h1, Gself _ y h1]`. Conclude with `hy`. Introduce `j j' j''`. Apply `units_eq_of_gm_eq` to reduce the goal to its premises. Introduce `y hy`.

Establish `h1` using `(hmem j y).1 hy.1.1`. Establish `h2` using `(hmem j' y).1 hy.1.2`. Establish `h3` using `(hmem j'' y).1 hy.2`. Rewrite using `[map_mul, gm_res_eq_gm (𝟙 Y) y, gm_res_eq_gm (𝟙 Y) y, gm_res_eq_gm (𝟙 Y) y, hN j j' y h1 h2, hN j' j'' y h2 h3, hN j j'' y h1 h3]`. Conclude with `Gcoc _ _ _ y h1 h2 h3`.

Apply the tactic sequence `all_goals exact hy`. Unfold `LBIso LB.Iso LB.div LB.Gen.IsGen`. Establish `hle : ∀ p : (PUnit → L.ι) × L.ι, (M.pull ψ).U p.1 ⊓ L.U p.2 ≤ L.U (p.1 PUnit.unit) ⊓ L.U p.2` using `fun p y hy => ⟨(hmem p.1 y).1 hy.1, hy.2⟩`. Use `⟨⟨fun p => res (hle p) (L.g (p.1 PUnit.unit) p.2)⟩, ?_⟩` and prove the remaining obligations. Introduce `p q`.

Use `res_eq_mul_inv_mul_of_gm _ _ _ _ _ _ _ _ (fun y hy => ?_)` and prove the remaining obligations. Establish `ha` using `(hmem p.1 y).1 hy.1.1`. Establish `hi` using `hy.1.2`. Establish `ha'` using `(hmem q.1 y).1 hy.2.1`. Establish `hi'` using `hy.2.2`.

Establish `eA` using `gm_res_eq_gm (𝟙 Y) y (hle p) (L.g (p.1 PUnit.unit) p.2) hy.1`. Establish `eD` using `gm_res_eq_gm (𝟙 Y) y (hle q) (L.g (q.1 PUnit.unit) q.2) hy.2`. Establish `eB` using `hN p.1 q.1 y ha ha'`. Establish `hG : gm (𝟙 Y) y (L.U (p.1 PUnit.unit) ⊓ L.U p.2) (L.g (p.1 PUnit.unit) p.2) = gm (𝟙 Y) y (L.U (p.1 PUnit.unit) ⊓ L.U (q.1 PUnit.unit)) (L.g (p.1 PUnit.unit) (q.1 PUnit.unit)) * (gm (𝟙 Y) y (L.U p.2 ⊓ L.U q.2) (L.g p.2 q.2))⁻¹ * gm (𝟙 Y) y (L.U (q.1 PUnit.unit) ⊓ L.U q.2) (L.g (q. …`. Rewrite using `[mul_right_comm, Gcoc _ _ _ y ha ha' hi', ← Gcoc _ _ _ y ha hi hi', mul_inv_cancel_right]`.

Use `eA.trans (hG.trans ?_)` and prove the remaining obligations. Conclude with `congrArg₂ (· * ·) (congrArg₂ (· * ·) eB.symm rfl) eD.symm`.
-/
theorem exists_push : ∀ (X Y : Scheme.{0}) (ψ : Y ⟶ X) [IsOpenImmersion ψ] (L : LB Y), L.IsLB →
    ∃ M : LB X, ⨆ a, M.U a = ψ.opensRange ∧
      (∀ (a : M.ι) (x : X), x ∈ M.U a → gm (𝟙 X) x (M.U a ⊓ M.U a) (M.g a a) = 1) ∧
      (M.pull ψ).IsLB ∧ LBIso L (M.pull ψ) := by
  intro X Y ψ _ L hL
  have himg : ∀ i j, ψ ''ᵁ L.U i ⊓ ψ ''ᵁ L.U j ≤ ψ ''ᵁ (L.U i ⊓ L.U j) := by
    rintro i j x ⟨⟨y, hy, rfl⟩, ⟨y', hy', e⟩⟩
    have e' : y' = y := ψ.isOpenEmbedding.injective e
    rw [e'] at hy'
    exact ⟨y, ⟨hy, hy'⟩, rfl⟩
  choose b hb using fun i j => exists_unit_image ψ (L.U i ⊓ L.U j) (L.g i j)
  let M : LB X := ⟨L.ι, fun i => ψ ''ᵁ L.U i, fun i j => res (himg i j) (b i j)⟩
  have hcov : ∀ y : Y, ∃ i, y ∈ L.U i := by
    intro y
    have hy : y ∈ ⨆ i, L.U i := by rw [hL.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hy
  have hmem : ∀ (j : PUnit → L.ι) (y : Y), y ∈ (M.pull ψ).U j ↔ y ∈ L.U (j PUnit.unit) := by
    intro j y
    constructor
    · intro hy
      obtain ⟨y', hy', e⟩ := Set.mem_iInter.1 hy PUnit.unit
      rwa [ψ.isOpenEmbedding.injective e] at hy'
    · intro hy
      exact Set.mem_iInter.2 fun k => ⟨y, hy, rfl⟩
  have Gself : ∀ i y, y ∈ L.U i → gm (𝟙 Y) y (L.U i ⊓ L.U i) (L.g i i) = 1 := by
    intro i y hy
    have := congrArg (gm (𝟙 Y) y _) (hL.g_self i)
    rw [gm_res_eq_gm (𝟙 Y) y, map_one] at this
    · exact this
    · exact hy
  have Gcoc : ∀ i j k y, y ∈ L.U i → y ∈ L.U j → y ∈ L.U k →
      gm (𝟙 Y) y (L.U i ⊓ L.U j) (L.g i j) * gm (𝟙 Y) y (L.U j ⊓ L.U k) (L.g j k) =
        gm (𝟙 Y) y (L.U i ⊓ L.U k) (L.g i k) := by
    intro i j k y hi hj hk
    have := congrArg (gm (𝟙 Y) y _) (hL.cocycle i j k)
    rw [map_mul, gm_res_eq_gm (𝟙 Y) y, gm_res_eq_gm (𝟙 Y) y, gm_res_eq_gm (𝟙 Y) y] at this
    · exact this
    all_goals exact ⟨⟨hi, hj⟩, hk⟩
  have key : ∀ i j y, y ∈ L.U i → y ∈ L.U j →
      gm ψ y (M.U i ⊓ M.U j) (M.g i j) = gm (𝟙 Y) y (L.U i ⊓ L.U j) (L.g i j) := by
    intro i j y hi hj
    have := hb i j Y (𝟙 Y) y ⟨hi, hj⟩
    rw [Category.id_comp] at this
    exact (gm_res_eq_gm ψ y (himg i j) (b i j) ⟨⟨y, hi, rfl⟩, ⟨y, hj, rfl⟩⟩).trans this
  have hN : ∀ (j j' : PUnit → L.ι) y, y ∈ L.U (j PUnit.unit) → y ∈ L.U (j' PUnit.unit) →
      gm (𝟙 Y) y ((M.pull ψ).U j ⊓ (M.pull ψ).U j') ((M.pull ψ).g j j') =
        gm (𝟙 Y) y (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit)) (L.g (j PUnit.unit) (j' PUnit.unit)) := by
    intro j j' y h1 h2
    rw [← key _ _ y h1 h2]
    unfold LB.pull LB.LinComb
    dsimp only
    rw [map_prod, Fintype.prod_unique, map_zpow, zpow_one]
    refine (gm_res_eq_gm (𝟙 Y) y _ _ ?_).trans (gm_id_pullU' ψ y (M.U (j default) ⊓ M.U (j' default)) _ ?_)
    all_goals first
      | exact ⟨(hmem j y).2 h1, (hmem j' y).2 h2⟩
      | exact ⟨⟨y, h1, rfl⟩, ⟨y, h2, rfl⟩⟩
  refine ⟨M, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · apply le_antisymm
    · intro x hx
      obtain ⟨i, y, hy, rfl⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
      exact ⟨y, rfl⟩
    · rintro x ⟨y, rfl⟩
      obtain ⟨i, hi⟩ := hcov y
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, y, hi, rfl⟩
  · rintro a x ⟨y, hy, rfl⟩
    exact gm_eq_one ψ y (U := M.U a ⊓ M.U a) ⟨⟨y, hy, rfl⟩, ⟨y, hy, rfl⟩⟩ ((key a a y hy hy).trans (Gself a y hy))
  · apply eq_top_iff.2
    intro y _
    obtain ⟨i, hi⟩ := hcov y
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, (hmem _ y).2 hi⟩
  · intro j
    apply units_eq_of_gm_eq
    intro y hy
    have h1 := (hmem j y).1 hy
    rw [gm_res_eq_gm (𝟙 Y) y, map_one, hN j j y h1 h1, Gself _ y h1]
    exact hy
  · intro j j' j''
    apply units_eq_of_gm_eq
    intro y hy
    have h1 := (hmem j y).1 hy.1.1
    have h2 := (hmem j' y).1 hy.1.2
    have h3 := (hmem j'' y).1 hy.2
    rw [map_mul, gm_res_eq_gm (𝟙 Y) y, gm_res_eq_gm (𝟙 Y) y, gm_res_eq_gm (𝟙 Y) y, hN j j' y h1 h2, hN j' j'' y h2 h3,
      hN j j'' y h1 h3]
    · exact Gcoc _ _ _ y h1 h2 h3
    all_goals exact hy
  · unfold LBIso LB.Iso LB.div LB.Gen.IsGen
    have hle : ∀ p : (PUnit → L.ι) × L.ι, (M.pull ψ).U p.1 ⊓ L.U p.2 ≤ L.U (p.1 PUnit.unit) ⊓ L.U p.2 :=
      fun p y hy => ⟨(hmem p.1 y).1 hy.1, hy.2⟩
    refine ⟨⟨fun p => res (hle p) (L.g (p.1 PUnit.unit) p.2)⟩, ?_⟩
    intro p q
    refine res_eq_mul_inv_mul_of_gm _ _ _ _ _ _ _ _ (fun y hy => ?_)
    have ha := (hmem p.1 y).1 hy.1.1
    have hi := hy.1.2
    have ha' := (hmem q.1 y).1 hy.2.1
    have hi' := hy.2.2
    have eA := gm_res_eq_gm (𝟙 Y) y (hle p) (L.g (p.1 PUnit.unit) p.2) hy.1
    have eD := gm_res_eq_gm (𝟙 Y) y (hle q) (L.g (q.1 PUnit.unit) q.2) hy.2
    have eB := hN p.1 q.1 y ha ha'
    have hG : gm (𝟙 Y) y (L.U (p.1 PUnit.unit) ⊓ L.U p.2) (L.g (p.1 PUnit.unit) p.2) =
        gm (𝟙 Y) y (L.U (p.1 PUnit.unit) ⊓ L.U (q.1 PUnit.unit)) (L.g (p.1 PUnit.unit) (q.1 PUnit.unit)) *
          (gm (𝟙 Y) y (L.U p.2 ⊓ L.U q.2) (L.g p.2 q.2))⁻¹ *
            gm (𝟙 Y) y (L.U (q.1 PUnit.unit) ⊓ L.U q.2) (L.g (q.1 PUnit.unit) q.2) := by
      rw [mul_right_comm, Gcoc _ _ _ y ha ha' hi', ← Gcoc _ _ _ y ha hi hi', mul_inv_cancel_right]
    refine eA.trans (hG.trans ?_)
    exact congrArg₂ (· * ·) (congrArg₂ (· * ·) eB.symm rfl) eD.symm

end GlobalTheory.LBPush
