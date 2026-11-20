import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHom
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.PartialCocycle

/- English proof (translation)
Establish `key : X.presheaf.map (homOfLE hle).op ≫ f.app V ≫ Z.presheaf.germ (f ⁻¹ᵁ V) z hz = f.app U ≫ Z.presheaf.germ (f ⁻¹ᵁ U) z (hle hz)`. Rewrite using `[← Scheme.Hom.germ_stalkMap, ← Scheme.Hom.germ_stalkMap, ← Category.assoc, TopCat.Presheaf.germ_res]`. Unfold `gm`. Rewrite using `[dif_pos hz, dif_pos (hle hz)]`. Use `ext`.

Simplify using `only [MonoidHom.comp_apply, Units.coe_map]`. Unfold `res pullU`. Establish `h2` using `congrArg (fun g => g.hom (u : Γ(X, U))) key`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply] at h2`. Conclude with `h2`.
-/
private theorem gm_res_eq_gm {X Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) {U V : X.Opens} (hle : V ≤ U)
    (hz : f z ∈ V) (u : Γ(X, U)ˣ) : gm f z V (res hle u) = gm f z U u := by
  have key : X.presheaf.map (homOfLE hle).op ≫ f.app V ≫ Z.presheaf.germ (f ⁻¹ᵁ V) z hz =
      f.app U ≫ Z.presheaf.germ (f ⁻¹ᵁ U) z (hle hz) := by
    rw [← Scheme.Hom.germ_stalkMap, ← Scheme.Hom.germ_stalkMap, ← Category.assoc, TopCat.Presheaf.germ_res]
  unfold gm
  rw [dif_pos hz, dif_pos (hle hz)]
  ext
  simp only [MonoidHom.comp_apply, Units.coe_map]
  unfold res pullU
  have h2 := congrArg (fun g => g.hom (u : Γ(X, U))) key
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  exact h2

/- English proof (translation)
Establish `hz : f z ∈ (M.U a ⊓ L.U b) ⊓ (M.U a' ⊓ L.U b')` using `⟨⟨ha, hb⟩, ⟨ha', hb'⟩⟩`. Establish `h₁ : (M.U a ⊓ L.U b) ⊓ (M.U a' ⊓ L.U b') ≤ M.U a ⊓ L.U b` using `inf_le_left`. Establish `h₂ : (M.U a ⊓ L.U b) ⊓ (M.U a' ⊓ L.U b') ≤ M.U a ⊓ M.U a'` using `le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)`. Establish `h₃ : (M.U a ⊓ L.U b) ⊓ (M.U a' ⊓ L.U b') ≤ L.U b ⊓ L.U b'` using `le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)`. Establish `h₄ : (M.U a ⊓ L.U b) ⊓ (M.U a' ⊓ L.U b') ≤ M.U a' ⊓ L.U b'` using `inf_le_right`.

Establish `h1` using `hw (a, b) (a', b')`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_mul, map_mul, map_inv, gm_res_eq_gm f z h₂ hz, gm_res_eq_gm f z h₃ hz]`. Conclude with `congrArg _ (gm_res_eq_gm f z h₄ hz _)`.
-/
theorem gm_iso {X Z : Scheme.{0}} {L M : LB X} {w : LB.Iso L M} (hw : w.IsGen) (f : Z ⟶ X) (z : Z)
    (a a' : M.ι) (b b' : L.ι) (ha : f z ∈ M.U a) (ha' : f z ∈ M.U a') (hb : f z ∈ L.U b) (hb' : f z ∈ L.U b') :
    gm f z (M.U a ⊓ L.U b) (w.s (a, b)) =
      gm f z (M.U a ⊓ M.U a') (M.g a a') * (gm f z (L.U b ⊓ L.U b') (L.g b b'))⁻¹ *
        gm f z (M.U a' ⊓ L.U b') (w.s (a', b')) := by
  have hz : f z ∈ (M.U a ⊓ L.U b) ⊓ (M.U a' ⊓ L.U b') := ⟨⟨ha, hb⟩, ⟨ha', hb'⟩⟩
  have h₁ : (M.U a ⊓ L.U b) ⊓ (M.U a' ⊓ L.U b') ≤ M.U a ⊓ L.U b := inf_le_left
  have h₂ : (M.U a ⊓ L.U b) ⊓ (M.U a' ⊓ L.U b') ≤ M.U a ⊓ M.U a' :=
    le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
  have h₃ : (M.U a ⊓ L.U b) ⊓ (M.U a' ⊓ L.U b') ≤ L.U b ⊓ L.U b' :=
    le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  have h₄ : (M.U a ⊓ L.U b) ⊓ (M.U a' ⊓ L.U b') ≤ M.U a' ⊓ L.U b' := inf_le_right
  have h1 := hw (a, b) (a', b')
  calc gm f z (M.U a ⊓ L.U b) (w.s (a, b))
      = gm f z _ (res h₁ (w.s (a, b))) := (gm_res_eq_gm f z h₁ hz _).symm
    _ = gm f z _ (res h₂ (M.g a a') * (res h₃ (L.g b b'))⁻¹ * res h₄ (w.s (a', b'))) := congrArg _ h1
    _ = _ := by
      rw [map_mul, map_mul, map_inv, gm_res_eq_gm f z h₂ hz, gm_res_eq_gm f z h₃ hz]
      exact congrArg _ (gm_res_eq_gm f z h₄ hz _)

/- English proof (translation)
Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv]`. Normalize the expressions using the abelian group laws.
-/
private theorem algebraMap_OmS_eq_algebraMap_comp {G : Type*} [CommGroup G] (A B C s t u : G) :
    A * B⁻¹ * s * (B * C⁻¹ * t) * (A * C⁻¹ * u)⁻¹ = s * t * u⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

/- English proof (translation)
Unfold `gm`. Rewrite using `[dif_pos hz]`. Both sides reduce to the same expression.
-/
private theorem gm_val_eq_germ_app' {X Z : Scheme.{0}} (g : Z ⟶ X) (z : Z) (U : X.Opens) (hz : g z ∈ U)
    (u : Γ(X, U)ˣ) : ((gm g z U u : Z.presheaf.stalk z)) = Z.presheaf.germ (g ⁻¹ᵁ U) z hz (g.app U u.val) := by
  unfold gm
  rw [dif_pos hz]
  rfl

/- English proof (translation)
Conclude with `gm_val_eq_germ_app' (𝟙 X) z U hz u`.
-/
private theorem gm_id_val_eq_germ' {X : Scheme.{0}} (z : X) (U : X.Opens) (hz : z ∈ U)
    (u : Γ(X, U)ˣ) : ((gm (𝟙 X) z U u : X.presheaf.stalk z)) = X.presheaf.germ U z hz u.val := by
  exact gm_val_eq_germ_app' (𝟙 X) z U hz u

/- English proof (translation)
Introduce `X S p e V₁ V₂ V₃ M₁ M₂ M₃ w₁₂ w₂₃ w₁₃ hep hrig hU₁ hU₂ hU₃ hg₁₂ hg₂₃ hg₁₃ hcoc y a b c hya hyb hyc`. Set `T : M₁.ι × M₂.ι × M₃.ι → X.Opens` to `fun i => M₁.U i.1 ⊓ M₂.U i.2.1 ⊓ M₃.U i.2.2`. Establish `l₁ : ∀ i, T i ≤ M₁.U i.1 ⊓ M₂.U i.2.1` using `fun i => inf_le_left`. Establish `l₂ : ∀ i, T i ≤ M₂.U i.2.1 ⊓ M₃.U i.2.2` using `fun i => le_inf (inf_le_left.trans inf_le_right) inf_le_right`. Establish `l₃ : ∀ i, T i ≤ M₁.U i.1 ⊓ M₃.U i.2.2` using `fun i => le_inf (inf_le_left.trans inf_le_left) inf_le_right`.

Set `t : ∀ i, Γ(X, T i)ˣ` to `fun i => res (l₁ i) (w₁₂.s (i.1, i.2.1)) * res (l₂ i) (w₂₃.s (i.2.1, i.2.2)) * (res (l₃ i) (w₁₃.s (i.1, i.2.2)))⁻¹`. Establish `hprod : ∀ {Z : Scheme.{0}} (g : Z ⟶ X) (z : Z) i (hz : g z ∈ T i), gm g z (T i) (t i) = gm g z (M₁.U i.1 ⊓ M₂.U i.2.1) (w₁₂.s (i.1, i.2.1)) * gm g z (M₂.U i.2.1 ⊓ M₃.U i.2.2) (w₂₃.s (i.2.1, i.2.2)) * (gm g z (M₁.U i.1 ⊓ M₃.U i.2.2) (w₁₃.s (i.1, i.2.2)))⁻¹`. Introduce `Z g z i hz`. Simplify using `only [t, map_mul, map_inv]`. Conclude with `congrArg₂ _ (congrArg₂ _ (gm_res_eq_gm g z (l₁ i) hz _) (gm_res_eq_gm g z (l₂ i) hz _)) (congrArg _ (gm_res_eq_gm g z (l₃ i) hz _))`.

Establish `hindep : ∀ {Z : Scheme.{0}} (g : Z ⟶ X) (z : Z) i j (hi : g z ∈ T i) (hj : g z ∈ T j), gm g z (T i) (t i) = gm g z (T j) (t j)`. Introduce `Z g z i j hi hj`. Rewrite using `[hprod g z i hi, hprod g z j hj]`. Take `⟨⟨hi1, hi2⟩, hi3⟩` from `hi`. Take `⟨⟨hj1, hj2⟩, hj3⟩` from `hj`.

Rewrite using `[gm_iso hg₁₂ g z i.1 j.1 i.2.1 j.2.1 hi1 hj1 hi2 hj2, gm_iso hg₂₃ g z i.2.1 j.2.1 i.2.2 j.2.2 hi2 hj2 hi3 hj3, gm_iso hg₁₃ g z i.1 j.1 i.2.2 j.2.2 hi1 hj1 hi3 hj3]`. Conclude with `algebraMap_OmS_eq_algebraMap_comp _ _ _ _ _ _`. Establish `hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 T (fun i => (t i).val)`. Introduce `i j`. Apply `TopCat.Presheaf.section_ext X.sheaf` to reduce the goal to its premises.

Introduce `z hz`. Use `show X.presheaf.germ (T i ⊓ T j) z hz (X.presheaf.map (TopologicalSpace.Opens.infLELeft (T i) (T j)).op (t i).val) = X.presheaf.germ (T i ⊓ T j) z hz (X.presheaf.map (TopologicalSpace.Opens.infLERight (T i) (T j)).op (t j).val)`. Rewrite using `[TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]`. Rewrite using `[← gm_id_val_eq_germ' z (T i) _ (t i), ← gm_id_val_eq_germ' z (T j) _ (t j)]`. Conclude with `congrArg Units.val (hindep (𝟙 X) z i j hz.1 hz.2)`.

Take `⟨s, hs, -⟩` from `X.sheaf.existsUnique_gluing T (fun i => (t i).val) hcompat`. Establish `hcov : p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃) ≤ iSup T`. Introduce `x hx`. Take `⟨⟨h1, h2⟩, h3⟩` from `hx`. Establish `m1 : x ∈ ⨆ a, M₁.U a` using `by rw [hU₁]; exact h1`.

Establish `m2 : x ∈ ⨆ a, M₂.U a` using `by rw [hU₂]; exact h2`. Establish `m3 : x ∈ ⨆ a, M₃.U a` using `by rw [hU₃]; exact h3`. Take `⟨a₁, ha₁⟩` from `TopologicalSpace.Opens.mem_iSup.1 m1`. Take `⟨a₂, ha₂⟩` from `TopologicalSpace.Opens.mem_iSup.1 m2`. Take `⟨a₃, ha₃⟩` from `TopologicalSpace.Opens.mem_iSup.1 m3`.

Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨(a₁, a₂, a₃), ⟨⟨ha₁, ha₂⟩, ha₃⟩⟩`. Establish `hV : V₁ ⊓ V₂ ⊓ V₃ ≤ e ⁻¹ᵁ (p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃))`. Introduce `x hx`. Use `show (e ≫ p) x ∈ V₁ ⊓ V₂ ⊓ V₃`. Rewrite using `[hep]`.

Conclude with `hx`. Set `u : Γ(X, p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃))` to `X.presheaf.map (homOfLE hcov).op s`. Establish `hsT : ∀ i (z : X) (hz : z ∈ T i) (hz' : z ∈ iSup T), X.presheaf.germ (iSup T) z hz' s = X.presheaf.germ (T i) z hz (t i).val`. Introduce `i z hz hz'`. Establish `h` using `hs i`.

Simplify using `only at h`. Rewrite using `[← h]`. Conclude with `(TopCat.Presheaf.germ_res_apply X.presheaf (TopologicalSpace.Opens.leSupr T i) z hz s).symm`. Establish `hu1 : (e.appLE (p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃)) (V₁ ⊓ V₂ ⊓ V₃) hV).hom u = 1`. Apply `TopCat.Presheaf.section_ext S.sheaf` to reduce the goal to its premises.

Introduce `x hx`. Establish `hex : e x ∈ p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃)` using `hV hx`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 (hcov hex)`. Use `show S.presheaf.germ _ x hx ((e.appLE (p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃)) (V₁ ⊓ V₂ ⊓ V₃) hV).hom u) = S.presheaf.germ _ x hx 1`. Rewrite using `[map_one]`.

Establish `k1 : e.appLE (p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃)) (V₁ ⊓ V₂ ⊓ V₃) hV ≫ S.presheaf.germ _ x hx = X.presheaf.germ (p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃)) (e x) hex ≫ e.stalkMap x`. Rewrite using `[Scheme.Hom.germ_stalkMap, Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]`. Establish `k2` using `congrArg (fun g => g.hom u) k1`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply] at k2`. Rewrite using `[k2]`.

Establish `hg1 : gm e x (T i) (t i) = 1`. Rewrite using `[hprod e x i hi]`. Take `⟨⟨hi1, hi2⟩, hi3⟩` from `hi`. Rewrite using `[hcoc x i.1 i.2.1 i.2.2 hi1 hi2 hi3, mul_inv_cancel]`. Rewrite using `[← Units.val_one, ← hg1, gm_val_eq_germ_app' e x (T i) hi]`.

Simplify using `only [u]`. Use `erw [TopCat.Presheaf.germ_res_apply, hsT i (e x) hi, Scheme.Hom.germ_stalkMap_apply]`. Establish `hu : u = 1` using `hrig _ u hV hu1`. Establish `hyT : y ∈ T (a, b, c)` using `⟨⟨hya, hyb⟩, hyc⟩`. Establish `hyS : y ∈ iSup T` using `TopologicalSpace.Opens.mem_iSup.2 ⟨(a, b, c), hyT⟩`.

Establish `fin : gm (𝟙 X) y (T (a, b, c)) (t (a, b, c)) = 1`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[gm_id_val_eq_germ' y _ hyT, Units.val_one, ← hsT (a, b, c) y hyT hyS]`. Establish `hyV : y ∈ p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃)`. Use `⟨⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Use `(le_iSup M₁.U a) hya` as an intermediate fact. Rewrite `this` using `[hU₁]`. Conclude with `this`. Use `(le_iSup M₂.U b) hyb` as an intermediate fact. Rewrite `this` using `[hU₂]`.

Conclude with `this`. Use `(le_iSup M₃.U c) hyc` as an intermediate fact. Rewrite `this` using `[hU₃]`. Conclude with `this`. Establish `k3` using `congrArg (X.presheaf.germ (p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃)) y hyV) hu`.

Simplify using `only [u, map_one] at k3`. Use `erw [TopCat.Presheaf.germ_res_apply] at k3`. Conclude with `k3`. Rewrite `fin` using `[hprod (𝟙 X) y (a, b, c) hyT]`. Conclude with `mul_inv_eq_one.1 fin`.
-/
theorem cocycle_of_rigid : ∀ (X S : Scheme.{0}) (p : X ⟶ S) (e : S ⟶ X) (V₁ V₂ V₃ : S.Opens) (M₁ M₂ M₃ : LB X) (w₁₂ : LB.Iso M₂ M₁) (w₂₃ : LB.Iso M₃ M₂) (w₁₃ : LB.Iso M₃ M₁), e ≫ p = 𝟙 S → (∀ (V : S.Opens) (u : Γ(X, p ⁻¹ᵁ V)) (h : V ≤ e ⁻¹ᵁ (p ⁻¹ᵁ V)), (e.appLE _ V h).hom u = 1 → u = 1) → ⨆ a, M₁.U a = p ⁻¹ᵁ V₁ → ⨆ a, M₂.U a = p ⁻¹ᵁ V₂ → ⨆ a, M₃.U a = p ⁻¹ᵁ V₃ → w₁₂.IsGen → w₂₃.IsGen → w₁₃.IsGen → (∀ (x : S) a b c, e x ∈ M₁.U a → e x ∈ M₂.U b → e x ∈ M₃.U c → gm e x (M₁.U a ⊓ M₂.U b) (w₁₂.s (a, b)) * gm e x (M₂.U b ⊓ M₃.U c) (w₂₃.s (b, c)) = gm e x (M₁.U a ⊓ M₃.U c) (w₁₃.s (a, c))) → ∀ (y : X) a b c, y ∈ M₁.U a → y ∈ M₂.U b → y ∈ M₃.U c → gm (𝟙 X) y (M₁.U a ⊓ M₂.U b) (w₁₂.s (a, b)) * gm (𝟙 X) y (M₂.U b ⊓ M₃.U c) (w₂₃.s (b, c)) = gm (𝟙 X) y (M₁.U a ⊓ M₃.U c) (w₁₃.s (a, c)) := by
  intro X S p e V₁ V₂ V₃ M₁ M₂ M₃ w₁₂ w₂₃ w₁₃ hep hrig hU₁ hU₂ hU₃ hg₁₂ hg₂₃ hg₁₃ hcoc y a b c hya hyb hyc
  let T : M₁.ι × M₂.ι × M₃.ι → X.Opens := fun i => M₁.U i.1 ⊓ M₂.U i.2.1 ⊓ M₃.U i.2.2
  have l₁ : ∀ i, T i ≤ M₁.U i.1 ⊓ M₂.U i.2.1 := fun i => inf_le_left
  have l₂ : ∀ i, T i ≤ M₂.U i.2.1 ⊓ M₃.U i.2.2 := fun i => le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have l₃ : ∀ i, T i ≤ M₁.U i.1 ⊓ M₃.U i.2.2 := fun i => le_inf (inf_le_left.trans inf_le_left) inf_le_right
  let t : ∀ i, Γ(X, T i)ˣ := fun i => res (l₁ i) (w₁₂.s (i.1, i.2.1)) * res (l₂ i) (w₂₃.s (i.2.1, i.2.2)) *
    (res (l₃ i) (w₁₃.s (i.1, i.2.2)))⁻¹
  have hprod : ∀ {Z : Scheme.{0}} (g : Z ⟶ X) (z : Z) i (hz : g z ∈ T i), gm g z (T i) (t i) =
      gm g z (M₁.U i.1 ⊓ M₂.U i.2.1) (w₁₂.s (i.1, i.2.1)) * gm g z (M₂.U i.2.1 ⊓ M₃.U i.2.2) (w₂₃.s (i.2.1, i.2.2)) *
        (gm g z (M₁.U i.1 ⊓ M₃.U i.2.2) (w₁₃.s (i.1, i.2.2)))⁻¹ := by
    intro Z g z i hz
    simp only [t, map_mul, map_inv]
    exact congrArg₂ _ (congrArg₂ _ (gm_res_eq_gm g z (l₁ i) hz _) (gm_res_eq_gm g z (l₂ i) hz _))
      (congrArg _ (gm_res_eq_gm g z (l₃ i) hz _))
  have hindep : ∀ {Z : Scheme.{0}} (g : Z ⟶ X) (z : Z) i j (hi : g z ∈ T i) (hj : g z ∈ T j),
      gm g z (T i) (t i) = gm g z (T j) (t j) := by
    intro Z g z i j hi hj
    rw [hprod g z i hi, hprod g z j hj]
    obtain ⟨⟨hi1, hi2⟩, hi3⟩ := hi
    obtain ⟨⟨hj1, hj2⟩, hj3⟩ := hj
    rw [gm_iso hg₁₂ g z i.1 j.1 i.2.1 j.2.1 hi1 hj1 hi2 hj2, gm_iso hg₂₃ g z i.2.1 j.2.1 i.2.2 j.2.2 hi2 hj2 hi3 hj3,
      gm_iso hg₁₃ g z i.1 j.1 i.2.2 j.2.2 hi1 hj1 hi3 hj3]
    exact algebraMap_OmS_eq_algebraMap_comp _ _ _ _ _ _
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 T (fun i => (t i).val) := by
    intro i j
    apply TopCat.Presheaf.section_ext X.sheaf
    intro z hz
    show X.presheaf.germ (T i ⊓ T j) z hz (X.presheaf.map (TopologicalSpace.Opens.infLELeft (T i) (T j)).op (t i).val) =
      X.presheaf.germ (T i ⊓ T j) z hz (X.presheaf.map (TopologicalSpace.Opens.infLERight (T i) (T j)).op (t j).val)
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    rw [← gm_id_val_eq_germ' z (T i) _ (t i), ← gm_id_val_eq_germ' z (T j) _ (t j)]
    exact congrArg Units.val (hindep (𝟙 X) z i j hz.1 hz.2)
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing T (fun i => (t i).val) hcompat
  have hcov : p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃) ≤ iSup T := by
    intro x hx
    obtain ⟨⟨h1, h2⟩, h3⟩ := hx
    have m1 : x ∈ ⨆ a, M₁.U a := by rw [hU₁]; exact h1
    have m2 : x ∈ ⨆ a, M₂.U a := by rw [hU₂]; exact h2
    have m3 : x ∈ ⨆ a, M₃.U a := by rw [hU₃]; exact h3
    obtain ⟨a₁, ha₁⟩ := TopologicalSpace.Opens.mem_iSup.1 m1
    obtain ⟨a₂, ha₂⟩ := TopologicalSpace.Opens.mem_iSup.1 m2
    obtain ⟨a₃, ha₃⟩ := TopologicalSpace.Opens.mem_iSup.1 m3
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(a₁, a₂, a₃), ⟨⟨ha₁, ha₂⟩, ha₃⟩⟩
  have hV : V₁ ⊓ V₂ ⊓ V₃ ≤ e ⁻¹ᵁ (p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃)) := by
    intro x hx
    show (e ≫ p) x ∈ V₁ ⊓ V₂ ⊓ V₃
    rw [hep]
    exact hx
  let u : Γ(X, p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃)) := X.presheaf.map (homOfLE hcov).op s
  have hsT : ∀ i (z : X) (hz : z ∈ T i) (hz' : z ∈ iSup T),
      X.presheaf.germ (iSup T) z hz' s = X.presheaf.germ (T i) z hz (t i).val := by
    intro i z hz hz'
    have h := hs i
    dsimp only at h
    rw [← h]
    exact (TopCat.Presheaf.germ_res_apply X.presheaf (TopologicalSpace.Opens.leSupr T i) z hz s).symm
  have hu1 : (e.appLE (p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃)) (V₁ ⊓ V₂ ⊓ V₃) hV).hom u = 1 := by
    apply TopCat.Presheaf.section_ext S.sheaf
    intro x hx
    have hex : e x ∈ p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃) := hV hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov hex)
    show S.presheaf.germ _ x hx ((e.appLE (p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃)) (V₁ ⊓ V₂ ⊓ V₃) hV).hom u) = S.presheaf.germ _ x hx 1
    rw [map_one]
    have k1 : e.appLE (p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃)) (V₁ ⊓ V₂ ⊓ V₃) hV ≫ S.presheaf.germ _ x hx =
        X.presheaf.germ (p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃)) (e x) hex ≫ e.stalkMap x := by
      rw [Scheme.Hom.germ_stalkMap, Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
    have k2 := congrArg (fun g => g.hom u) k1
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at k2
    rw [k2]
    have hg1 : gm e x (T i) (t i) = 1 := by
      rw [hprod e x i hi]
      obtain ⟨⟨hi1, hi2⟩, hi3⟩ := hi
      rw [hcoc x i.1 i.2.1 i.2.2 hi1 hi2 hi3, mul_inv_cancel]
    rw [← Units.val_one, ← hg1, gm_val_eq_germ_app' e x (T i) hi]
    simp only [u]
    erw [TopCat.Presheaf.germ_res_apply, hsT i (e x) hi, Scheme.Hom.germ_stalkMap_apply]
  have hu : u = 1 := hrig _ u hV hu1
  have hyT : y ∈ T (a, b, c) := ⟨⟨hya, hyb⟩, hyc⟩
  have hyS : y ∈ iSup T := TopologicalSpace.Opens.mem_iSup.2 ⟨(a, b, c), hyT⟩
  have fin : gm (𝟙 X) y (T (a, b, c)) (t (a, b, c)) = 1 := by
    apply Units.ext
    rw [gm_id_val_eq_germ' y _ hyT, Units.val_one, ← hsT (a, b, c) y hyT hyS]
    have hyV : y ∈ p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃) := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have := (le_iSup M₁.U a) hya
        rw [hU₁] at this
        exact this
      · have := (le_iSup M₂.U b) hyb
        rw [hU₂] at this
        exact this
      · have := (le_iSup M₃.U c) hyc
        rw [hU₃] at this
        exact this
    have k3 := congrArg (X.presheaf.germ (p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃)) y hyV) hu
    simp only [u, map_one] at k3
    erw [TopCat.Presheaf.germ_res_apply] at k3
    exact k3
  rw [hprod (𝟙 X) y (a, b, c) hyT] at fin
  exact mul_inv_eq_one.1 fin

end GlobalTheory.PartialCocycle
