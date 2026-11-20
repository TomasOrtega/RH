import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.LBSpreads
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TranslateTrivialEqOneOfFiniteTypePoints

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.SpreadingModels GlobalTheory.GenLimit

noncomputable section

namespace GlobalTheory.CompanionTheory.LBLimit

/- English proof (translation)
Use `top_le_iff.1 fun y _ => ?_` and prove the remaining obligations. Take `⟨k, hk⟩` from `hcov y`. Conclude with `Opens.mem_iSup.2 ⟨k, hk⟩`. Use `g_self i := unit_ext fun y hy => by`. Establish `e` using `hcoc i i i y hy hy hy`.

Rewrite using `[gm_res _ y _ hy, map_one]`. Conclude with `mul_eq_left.1 e`. Use `cocycle i j k := unit_ext fun y hy => by`. Establish `hm₁ : y ∈ V i ⊓ V j` using `hy.1`. Establish `hj : y ∈ V j` using `hy.1.2`.

Establish `hk : y ∈ V k` using `hy.2`. Establish `hi : y ∈ V i` using `hy.1.1`. Rewrite using `[map_mul, gm_res _ y _ hy, gm_res _ y _ hy, gm_res _ y _ hy]`. Conclude with `hcoc i j k y hi hj hk`.
-/
theorem isLB_of_germs {B : Scheme.{0}} {S : Type} (V : S → B.Opens) (t : ∀ k l, Γ(B, V k ⊓ V l)ˣ)
    (hcov : ∀ y, ∃ k, y ∈ V k)
    (hcoc : ∀ k l m (y : B), y ∈ V k → y ∈ V l → y ∈ V m →
      gm (𝟙 B) y _ (t k l) * gm (𝟙 B) y _ (t l m) = gm (𝟙 B) y _ (t k m)) :
    LB.IsLB (⟨S, V, t⟩ : LB B) where
  cover := by
    refine top_le_iff.1 fun y _ => ?_
    obtain ⟨k, hk⟩ := hcov y
    exact Opens.mem_iSup.2 ⟨k, hk⟩
  g_self i := unit_ext fun y hy => by
    have e := hcoc i i i y hy hy hy
    rw [gm_res _ y _ hy, map_one]
    exact mul_eq_left.1 e
  cocycle i j k := unit_ext fun y hy => by
    have hm₁ : y ∈ V i ⊓ V j := hy.1
    have hj : y ∈ V j := hy.1.2
    have hk : y ∈ V k := hy.2
    have hi : y ∈ V i := hy.1.1
    rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy, gm_res _ y _ hy]
    exact hcoc i j k y hi hj hk

/- English proof (translation)
Establish `le : ∀ p : (PUnit → M₁.ι) × M.ι, (M₁.pull ρ).U p.1 ⊓ M.U p.2 ≤ M.U (a (p.1 PUnit.unit)) ⊓ M.U p.2` using `fun p y hy => ⟨hle _ (mem_pull.1 hy.1), hy.2⟩`. Use `⟨⟨fun p => res (le p) (M.g (a (p.1 PUnit.unit)) p.2)⟩, fun p q => unit_ext fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨⟨hp₁, hp₂⟩, hq₁, hq₂⟩` from `hy`. Establish `hy : y ∈ (M₁.pull ρ).U p.1 ⊓ M.U p.2 ⊓ ((M₁.pull ρ).U q.1 ⊓ M.U q.2)` using `⟨⟨hp₁, hp₂⟩, hq₁, hq₂⟩`. Establish `ha₁ : y ∈ M.U (a (p.1 PUnit.unit))` using `hle _ (mem_pull.1 hp₁)`.

Establish `ha₂ : y ∈ M.U (a (q.1 PUnit.unit))` using `hle _ (mem_pull.1 hq₁)`. Establish `c₁` using `gm_cocycle hM (𝟙 X) y ha₁ ha₂ hq₂`. Establish `c₂` using `gm_cocycle hM (𝟙 X) y ha₁ hp₂ hq₂`. Establish `e` using `gm_div M (M₁.pull ρ) (𝟙 X) y p q hy`. Establish `e₂` using `gm_pull_g M₁ ρ (𝟙 X) y p.1 q.1 hp₁ hq₁`.

Rewrite `e₂` using `[Category.id_comp, hg _ _ y (mem_pull.1 hp₁) (mem_pull.1 hq₁)]`. Rewrite `e` using `[e₂]`. Use `(gm_res (𝟙 X) y _ hy _).trans (Eq.trans ?_ (Eq.trans (congrArg₂ (· * ·) e.symm (gm_res (𝟙 X) y _ hy _).symm) (map_mul _ _ _).symm))` and prove the remaining obligations. Establish `v : ∀ r : (PUnit → M₁.ι) × M.ι, y ∈ (M₁.pull ρ).U r.1 ⊓ M.U r.2 → gm (𝟙 X) y ((M₁.pull ρ).U r.1 ⊓ M.U r.2) (res (le r) (M.g (a (r.1 PUnit.unit)) r.2)) = gm (𝟙 X) y _ (M.g (a (r.1 PUnit.unit)) r.2)` using `fun r hr => gm_res _ y _ hr _`. Use `(v p ⟨hp₁, hp₂⟩).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (v q ⟨hq₁, hq₂⟩).symm))` and prove the remaining obligations.

Rewrite using `[mul_right_comm, c₁, ← c₂, mul_inv_cancel_right]`.
-/
theorem exists_iso_pull {X B : Scheme.{0}} (ρ : X ⟶ B) (M : LB X) (hM : M.IsLB) (M₁ : LB B)
    (a : M₁.ι → M.ι) (hle : ∀ k, ρ ⁻¹ᵁ M₁.U k ≤ M.U (a k))
    (hg : ∀ k l (y : X), ρ y ∈ M₁.U k → ρ y ∈ M₁.U l →
      gm ρ y (M₁.U k ⊓ M₁.U l) (M₁.g k l) = gm (𝟙 X) y _ (M.g (a k) (a l))) :
    ∃ w : LB.Iso M (M₁.pull ρ), w.IsGen := by
  have le : ∀ p : (PUnit → M₁.ι) × M.ι,
      (M₁.pull ρ).U p.1 ⊓ M.U p.2 ≤ M.U (a (p.1 PUnit.unit)) ⊓ M.U p.2 := fun p y hy =>
    ⟨hle _ (mem_pull.1 hy.1), hy.2⟩
  refine ⟨⟨fun p => res (le p) (M.g (a (p.1 PUnit.unit)) p.2)⟩, fun p q => unit_ext fun y hy => ?_⟩
  obtain ⟨⟨hp₁, hp₂⟩, hq₁, hq₂⟩ := hy
  have hy : y ∈ (M₁.pull ρ).U p.1 ⊓ M.U p.2 ⊓ ((M₁.pull ρ).U q.1 ⊓ M.U q.2) := ⟨⟨hp₁, hp₂⟩, hq₁, hq₂⟩
  have ha₁ : y ∈ M.U (a (p.1 PUnit.unit)) := hle _ (mem_pull.1 hp₁)
  have ha₂ : y ∈ M.U (a (q.1 PUnit.unit)) := hle _ (mem_pull.1 hq₁)
  have c₁ := gm_cocycle hM (𝟙 X) y ha₁ ha₂ hq₂
  have c₂ := gm_cocycle hM (𝟙 X) y ha₁ hp₂ hq₂
  have e := gm_div M (M₁.pull ρ) (𝟙 X) y p q hy
  have e₂ := gm_pull_g M₁ ρ (𝟙 X) y p.1 q.1 hp₁ hq₁
  rw [Category.id_comp, hg _ _ y (mem_pull.1 hp₁) (mem_pull.1 hq₁)] at e₂
  rw [e₂] at e
  refine (gm_res (𝟙 X) y _ hy _).trans (Eq.trans ?_ (Eq.trans
    (congrArg₂ (· * ·) e.symm (gm_res (𝟙 X) y _ hy _).symm) (map_mul _ _ _).symm))
  have v : ∀ r : (PUnit → M₁.ι) × M.ι, y ∈ (M₁.pull ρ).U r.1 ⊓ M.U r.2 →
      gm (𝟙 X) y ((M₁.pull ρ).U r.1 ⊓ M.U r.2) (res (le r) (M.g (a (r.1 PUnit.unit)) r.2)) =
        gm (𝟙 X) y _ (M.g (a (r.1 PUnit.unit)) r.2) := fun r hr => gm_res _ y _ hr _
  refine (v p ⟨hp₁, hp₂⟩).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (v q ⟨hq₁, hq₂⟩).symm))
  rw [mul_right_comm, c₁, ← c₂, mul_inv_cancel_right]

section Limit

variable {I : Type} [Category.{0} I] [IsCofiltered I] (D : I ⥤ Scheme.{0}) (c : Cone D)
  (hc : IsLimit c) [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]

include hc in

/- English proof (translation)
Use `Scheme.compactSpace_of_isLimit D c hc` as an intermediate fact. Establish `loc : ∀ x : c.pt, ∃ (a : M.ι) (i : I) (V : (D.obj i).Opens), IsAffineOpen V ∧ x ∈ c.π.app i ⁻¹ᵁ V ∧ c.π.app i ⁻¹ᵁ V ≤ M.U a` using `fun x => by`. Take `⟨a, ha⟩` from `exists_chart hM x`. Take `⟨_, ⟨_, ⟨i, V, hV, rfl⟩, rfl⟩, hx, hle⟩` from `(isBasis_preimage_isAffineOpen D c hc).exists_subset_of_mem_open ha (M.U a).isOpen`. Conclude with `⟨a, i, V, hV, hx, hle⟩`.

Use `choose a i V hV hx hle using loc`. Set `P : c.pt → c.pt.Opens` to `fun x => c.π.app (i x) ⁻¹ᵁ V x`. Take `⟨T, hT⟩` from `isCompact_univ.elim_finite_subcover (fun x => (P x : Set c.pt)) (fun x => (P x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hx x⟩)`. Take `⟨j₀, hj₀⟩` from `IsCofiltered.inf_objs_exists (T.image i)`. Set `e : ∀ k : T, j₀ ⟶ i k` to `fun k => (hj₀ (Finset.mem_image_of_mem i k.2)).some`.

Set `W₀ : T → (D.obj j₀).Opens` to `fun k => D.map (e k) ⁻¹ᵁ V k`. Establish `hpre : ∀ k : T, c.π.app j₀ ⁻¹ᵁ W₀ k = c.π.app (i k) ⁻¹ᵁ V k` using `fun k => by show c.π.app j₀ ⁻¹ᵁ (D.map (e k) ⁻¹ᵁ V k) = _`. Rewrite using `[← Scheme.Hom.comp_preimage, c.w]`. Take `⟨j, f, hf⟩` from `exists_map_eq_top D c hc (⨆ k, W₀ k) (by`. Use `top_le_iff.1 fun y _ => ?_` and prove the remaining obligations.

Take `⟨k, hk, hy⟩` from `Set.mem_iUnion₂.1 (hT (Set.mem_univ y))`. Use `Opens.mem_iSup.2 ⟨⟨k, hk⟩, ?_⟩` and prove the remaining obligations. Conclude with `(hpre ⟨k, hk⟩).ge hy)`. Use `⟨j, T, inferInstance, fun k => D.map f ⁻¹ᵁ W₀ k, fun k => a k, fun k => ?_, fun y => ?_, fun k => ?_⟩` and prove the remaining obligations. Conclude with `(((hV k).preimage (D.map (e k))).preimage (D.map f)).isCompact`.

Establish `: y ∈ D.map f ⁻¹ᵁ (⨆ k, W₀ k)` using `by rw [hf]; trivial`. Take `⟨k, hk⟩` from `Opens.mem_iSup.1 this`. Conclude with `⟨k, hk⟩`. Establish `: c.π.app j ⁻¹ᵁ (D.map f ⁻¹ᵁ W₀ k) = c.π.app j₀ ⁻¹ᵁ W₀ k`. Rewrite using `[← Scheme.Hom.comp_preimage, c.w]`.

Rewrite using `[this, hpre k]`. Conclude with `hle k`.
-/
theorem exists_finite_cover [∀ i, CompactSpace (D.obj i)] (M : LB c.pt) (hM : M.IsLB) :
    ∃ (j : I) (S : Type) (_ : Finite S) (W : S → (D.obj j).Opens) (a : S → M.ι),
      (∀ k, IsCompact (W k : Set (D.obj j))) ∧ (∀ y, ∃ k, y ∈ W k) ∧
        ∀ k, c.π.app j ⁻¹ᵁ W k ≤ M.U (a k) := by
  classical
  have := Scheme.compactSpace_of_isLimit D c hc
  have loc : ∀ x : c.pt, ∃ (a : M.ι) (i : I) (V : (D.obj i).Opens), IsAffineOpen V ∧
      x ∈ c.π.app i ⁻¹ᵁ V ∧ c.π.app i ⁻¹ᵁ V ≤ M.U a := fun x => by
    obtain ⟨a, ha⟩ := exists_chart hM x
    obtain ⟨_, ⟨_, ⟨i, V, hV, rfl⟩, rfl⟩, hx, hle⟩ :=
      (isBasis_preimage_isAffineOpen D c hc).exists_subset_of_mem_open ha (M.U a).isOpen
    exact ⟨a, i, V, hV, hx, hle⟩
  choose a i V hV hx hle using loc
  let P : c.pt → c.pt.Opens := fun x => c.π.app (i x) ⁻¹ᵁ V x
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun x => (P x : Set c.pt))
    (fun x => (P x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hx x⟩)
  obtain ⟨j₀, hj₀⟩ := IsCofiltered.inf_objs_exists (T.image i)
  let e : ∀ k : T, j₀ ⟶ i k := fun k => (hj₀ (Finset.mem_image_of_mem i k.2)).some
  let W₀ : T → (D.obj j₀).Opens := fun k => D.map (e k) ⁻¹ᵁ V k
  have hpre : ∀ k : T, c.π.app j₀ ⁻¹ᵁ W₀ k = c.π.app (i k) ⁻¹ᵁ V k := fun k => by
    show c.π.app j₀ ⁻¹ᵁ (D.map (e k) ⁻¹ᵁ V k) = _
    rw [← Scheme.Hom.comp_preimage, c.w]
  obtain ⟨j, f, hf⟩ := exists_map_eq_top D c hc (⨆ k, W₀ k) (by
    refine top_le_iff.1 fun y _ => ?_
    obtain ⟨k, hk, hy⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ y))
    refine Opens.mem_iSup.2 ⟨⟨k, hk⟩, ?_⟩
    exact (hpre ⟨k, hk⟩).ge hy)
  refine ⟨j, T, inferInstance, fun k => D.map f ⁻¹ᵁ W₀ k, fun k => a k, fun k => ?_,
    fun y => ?_, fun k => ?_⟩
  · exact (((hV k).preimage (D.map (e k))).preimage (D.map f)).isCompact
  · have : y ∈ D.map f ⁻¹ᵁ (⨆ k, W₀ k) := by rw [hf]; trivial
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 this
    exact ⟨k, hk⟩
  · have : c.π.app j ⁻¹ᵁ (D.map f ⁻¹ᵁ W₀ k) = c.π.app j₀ ⁻¹ᵁ W₀ k := by
      rw [← Scheme.Hom.comp_preimage, c.w]
    rw [this, hpre k]
    exact hle k

include hc in

/- English proof (translation)
Establish `hmono : ∀ (p : A) (n n' : I) (g : n' ⟶ n) (f : n ⟶ j), (∃ t : Γ(D.obj n, D.map f ⁻¹ᵁ U p)ˣ, ∀ z, c.π.app j z ∈ U p → gm (c.π.app n) z _ t = gm (𝟙 c.pt) z _ (s p)) → (∃ t : Γ(D.obj n', D.map (g ≫ f) ⁻¹ᵁ U p)ˣ, ∀ z, c.π.app j z ∈ U p → gm (c.π.app n') z _ t = gm (𝟙 c.pt) z _ (s p))`. Introduce and unpack `p n n' g f ⟨t, ht⟩`. Establish `hle : D.map (g ≫ f) ⁻¹ᵁ U p ≤ D.map g ⁻¹ᵁ (D.map f ⁻¹ᵁ U p)`. Rewrite using `[Functor.map_comp]`. Conclude with `le_rfl`.

Use `⟨res hle (pullU (D.map g) _ t), fun z hz => ?_⟩` and prove the remaining obligations. Establish `e1 : D.map (g ≫ f) (c.π.app n' z) = c.π.app j z`. Rewrite using `[← Scheme.Hom.comp_apply, c.w]`. Establish `e2 : D.map f (D.map g (c.π.app n' z)) = c.π.app j z`. Rewrite using `[← Scheme.Hom.comp_apply (c.π.app n') (D.map g), c.w g, ← Scheme.Hom.comp_apply, c.w f]`.

Establish `hz' : c.π.app n' z ∈ D.map (g ≫ f) ⁻¹ᵁ U p` using `by show D.map (g ≫ f) (c.π.app n' z) ∈ U p`. Rewrite using `[e1]`. Conclude with `hz`. Establish `hz'' : D.map g (c.π.app n' z) ∈ D.map f ⁻¹ᵁ U p` using `by show D.map f (D.map g (c.π.app n' z)) ∈ U p`. Rewrite using `[e2]`.

Conclude with `hz`. Rewrite using `[gm_res _ _ hle hz', gm_pull _ _ _ _ hz'', c.w g]`. Conclude with `ht z hz`. Establish `hexist : ∀ p : A, ∃ (n : I) (f : n ⟶ j) (t : Γ(D.obj n, D.map f ⁻¹ᵁ U p)ˣ), ∀ z, c.π.app j z ∈ U p → gm (c.π.app n) z _ t = gm (𝟙 c.pt) z _ (s p)` using `fun p => exists_unit D c hc (U p) (hU p) (s p)`. Take `⟨n, f, hnf⟩` from `exists_forall_of_cofiltered (i := j) (J := A) (fun p n (f : n ⟶ j) => ∃ t : Γ(D.obj n, D.map f ⁻¹ᵁ U p)ˣ, ∀ z, c.π.app j z ∈ U p → gm (c.π.app n) z _ t = gm (𝟙 c.pt) z _ (s p)) (fun p n n' g f h => hmono p n n' g f h) hexist`.

Use `choose t ht using hnf`. Conclude with `⟨n, f, t, ht⟩`.
-/
theorem exists_units_stage [∀ i, QuasiSeparatedSpace (D.obj i)] {j : I} {A : Type} [Finite A]
    (U : A → (D.obj j).Opens) (hU : ∀ p, IsCompact (U p : Set (D.obj j)))
    (s : ∀ p, Γ(c.pt, c.π.app j ⁻¹ᵁ U p)ˣ) :
    ∃ (n : I) (f : n ⟶ j) (t : ∀ p, Γ(D.obj n, D.map f ⁻¹ᵁ U p)ˣ),
      ∀ p z, c.π.app j z ∈ U p → gm (c.π.app n) z _ (t p) = gm (𝟙 c.pt) z _ (s p) := by
  have hmono : ∀ (p : A) (n n' : I) (g : n' ⟶ n) (f : n ⟶ j),
      (∃ t : Γ(D.obj n, D.map f ⁻¹ᵁ U p)ˣ, ∀ z, c.π.app j z ∈ U p →
        gm (c.π.app n) z _ t = gm (𝟙 c.pt) z _ (s p)) →
      (∃ t : Γ(D.obj n', D.map (g ≫ f) ⁻¹ᵁ U p)ˣ, ∀ z, c.π.app j z ∈ U p →
        gm (c.π.app n') z _ t = gm (𝟙 c.pt) z _ (s p)) := by
    rintro p n n' g f ⟨t, ht⟩
    have hle : D.map (g ≫ f) ⁻¹ᵁ U p ≤ D.map g ⁻¹ᵁ (D.map f ⁻¹ᵁ U p) := by
      rw [Functor.map_comp]
      exact le_rfl
    refine ⟨res hle (pullU (D.map g) _ t), fun z hz => ?_⟩
    have e1 : D.map (g ≫ f) (c.π.app n' z) = c.π.app j z := by
      rw [← Scheme.Hom.comp_apply, c.w]
    have e2 : D.map f (D.map g (c.π.app n' z)) = c.π.app j z := by
      rw [← Scheme.Hom.comp_apply (c.π.app n') (D.map g), c.w g, ← Scheme.Hom.comp_apply, c.w f]
    have hz' : c.π.app n' z ∈ D.map (g ≫ f) ⁻¹ᵁ U p := by
      show D.map (g ≫ f) (c.π.app n' z) ∈ U p
      rw [e1]
      exact hz
    have hz'' : D.map g (c.π.app n' z) ∈ D.map f ⁻¹ᵁ U p := by
      show D.map f (D.map g (c.π.app n' z)) ∈ U p
      rw [e2]
      exact hz
    rw [gm_res _ _ hle hz', gm_pull _ _ _ _ hz'', c.w g]
    exact ht z hz
  have hexist : ∀ p : A, ∃ (n : I) (f : n ⟶ j) (t : Γ(D.obj n, D.map f ⁻¹ᵁ U p)ˣ),
      ∀ z, c.π.app j z ∈ U p → gm (c.π.app n) z _ t = gm (𝟙 c.pt) z _ (s p) := fun p =>
    exists_unit D c hc (U p) (hU p) (s p)
  obtain ⟨n, f, hnf⟩ := exists_forall_of_cofiltered (i := j) (J := A)
    (fun p n (f : n ⟶ j) => ∃ t : Γ(D.obj n, D.map f ⁻¹ᵁ U p)ˣ, ∀ z, c.π.app j z ∈ U p →
        gm (c.π.app n) z _ t = gm (𝟙 c.pt) z _ (s p))
    (fun p n n' g f h => hmono p n n' g f h) hexist
  choose t ht using hnf
  exact ⟨n, f, t, ht⟩

include hc in

/- English proof (translation)
Establish `hmono : ∀ (q : S × S × S) (n₁ n₂ : I) (g' : n₂ ⟶ n₁) (g : n₁ ⟶ n), (∀ y, D.map g y ∈ V q.1 → D.map g y ∈ V q.2.1 → D.map g y ∈ V q.2.2 → gm (D.map g) y _ (t q.1 q.2.1) * gm (D.map g) y _ (t q.2.1 q.2.2) = gm (D.map g) y _ (t q.1 q.2.2)) → (∀ y, D.map (g' ≫ g) y ∈ V q.1 → D.map (g …`. Introduce and unpack `⟨k, l, m⟩ n₁ n₂ g' g hP y hk hl hm`. Simplify using `only at hP hk hl hm ⊢`. Rewrite `hk`, `hl`, `hm`, the goal using `[Functor.map_comp]`. Rewrite `hk`, `hl`, `hm` using `[Scheme.Hom.comp_apply]`.

Rewrite using `[gm_comp _ _ _ _ (Opens.mem_inf.2 ⟨hk, hl⟩), gm_comp _ _ _ _ (Opens.mem_inf.2 ⟨hl, hm⟩), gm_comp _ _ _ _ (Opens.mem_inf.2 ⟨hk, hm⟩), ← map_mul, hP _ hk hl hm]`. Establish `hexist : ∀ q : S × S × S, ∃ (n₁ : I) (g : n₁ ⟶ n), ∀ y, D.map g y ∈ V q.1 → D.map g y ∈ V q.2.1 → D.map g y ∈ V q.2.2 → gm (D.map g) y _ (t q.1 q.2.1) * gm (D.map g) y _ (t q.2.1 q.2.2) = gm (D.map g) y _ (t q.1 q.2.2)`. Introduce and unpack `⟨k, l, m⟩`. Establish `hkl : IsCompact ((V k ⊓ V l : (D.obj n).Opens) : Set (D.obj n))`. Rewrite using `[Opens.coe_inf]`.

Conclude with `QuasiSeparatedSpace.inter_isCompact _ _ (V k).isOpen (hV k) (V l).isOpen (hV l)`. Establish `hW : IsCompact ((V k ⊓ V l ⊓ V m : (D.obj n).Opens) : Set (D.obj n))`. Rewrite using `[Opens.coe_inf]`. Conclude with `QuasiSeparatedSpace.inter_isCompact _ _ (V k ⊓ V l).isOpen hkl (V m).isOpen (hV m)`. Establish `h1 : V k ⊓ V l ⊓ V m ≤ V k ⊓ V l` using `inf_le_left`.

Establish `h2 : V k ⊓ V l ⊓ V m ≤ V l ⊓ V m` using `le_inf (inf_le_left.trans inf_le_right) inf_le_right`. Establish `h3 : V k ⊓ V l ⊓ V m ≤ V k ⊓ V m` using `le_inf (inf_le_left.trans inf_le_left) inf_le_right`. Take `⟨n₁, g, hg⟩` from `exists_unit_eq D c hc (V k ⊓ V l ⊓ V m) hW (res h1 (t k l) * res h2 (t l m)) (res h3 (t k m)) (fun z hz => by`. Rewrite using `[map_mul, gm_res _ _ h1 hz, gm_res _ _ h2 hz, gm_res _ _ h3 hz]`. Take `⟨hz12, hz3⟩` from `Opens.mem_inf.1 hz`.

Take `⟨hz1, hz2⟩` from `Opens.mem_inf.1 hz12`. Conclude with `h k l m z hz1 hz2 hz3)`. Use `⟨n₁, g, fun y hk hl hm => ?_⟩` and prove the remaining obligations. Establish `hy : D.map g y ∈ V k ⊓ V l ⊓ V m` using `Opens.mem_inf.2 ⟨Opens.mem_inf.2 ⟨hk, hl⟩, hm⟩`. Use `hg y hy` as an intermediate fact.

Rewrite `this` using `[map_mul, gm_res _ _ h1 hy, gm_res _ _ h2 hy, gm_res _ _ h3 hy]`. Then use the resulting hypothesis. Take `⟨n', g, hg⟩` from `exists_forall_of_cofiltered (i := n) (J := S × S × S) (fun q n₁ (g : n₁ ⟶ n) => ∀ y, D.map g y ∈ V q.1 → D.map g y ∈ V q.2.1 → D.map g y ∈ V q.2.2 → gm (D.map g) y _ (t q.1 q.2.1) * gm (D.map g) y _ (t q.2.1 q.2.2) = gm (D.map g) y _ (t q.1 q.2.2)) (fun q n₁ n₂ g' g h => hmono q …`. Conclude with `⟨n', g, fun k l m y hk hl hm => hg (k, l, m) y hk hl hm⟩`.
-/
theorem exists_cocycle_stage {n : I} {S : Type} [Finite S] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (V : S → (D.obj n).Opens) (hV : ∀ k, IsCompact (V k : Set (D.obj n)))
    (t : ∀ k l, Γ(D.obj n, V k ⊓ V l)ˣ)
    (h : ∀ k l m z, c.π.app n z ∈ V k → c.π.app n z ∈ V l → c.π.app n z ∈ V m →
      gm (c.π.app n) z _ (t k l) * gm (c.π.app n) z _ (t l m) = gm (c.π.app n) z _ (t k m)) :
    ∃ (n' : I) (g : n' ⟶ n), ∀ k l m y, D.map g y ∈ V k → D.map g y ∈ V l → D.map g y ∈ V m →
      gm (D.map g) y _ (t k l) * gm (D.map g) y _ (t l m) = gm (D.map g) y _ (t k m) := by
  have hmono : ∀ (q : S × S × S) (n₁ n₂ : I) (g' : n₂ ⟶ n₁) (g : n₁ ⟶ n),
      (∀ y, D.map g y ∈ V q.1 → D.map g y ∈ V q.2.1 → D.map g y ∈ V q.2.2 →
        gm (D.map g) y _ (t q.1 q.2.1) * gm (D.map g) y _ (t q.2.1 q.2.2) =
          gm (D.map g) y _ (t q.1 q.2.2)) →
      (∀ y, D.map (g' ≫ g) y ∈ V q.1 → D.map (g' ≫ g) y ∈ V q.2.1 → D.map (g' ≫ g) y ∈ V q.2.2 →
        gm (D.map (g' ≫ g)) y _ (t q.1 q.2.1) * gm (D.map (g' ≫ g)) y _ (t q.2.1 q.2.2) =
          gm (D.map (g' ≫ g)) y _ (t q.1 q.2.2)) := by
    rintro ⟨k, l, m⟩ n₁ n₂ g' g hP y hk hl hm
    simp only at hP hk hl hm ⊢
    rw [Functor.map_comp] at hk hl hm ⊢
    rw [Scheme.Hom.comp_apply] at hk hl hm
    rw [gm_comp _ _ _ _ (Opens.mem_inf.2 ⟨hk, hl⟩), gm_comp _ _ _ _ (Opens.mem_inf.2 ⟨hl, hm⟩),
      gm_comp _ _ _ _ (Opens.mem_inf.2 ⟨hk, hm⟩), ← map_mul, hP _ hk hl hm]
  have hexist : ∀ q : S × S × S, ∃ (n₁ : I) (g : n₁ ⟶ n),
      ∀ y, D.map g y ∈ V q.1 → D.map g y ∈ V q.2.1 → D.map g y ∈ V q.2.2 →
        gm (D.map g) y _ (t q.1 q.2.1) * gm (D.map g) y _ (t q.2.1 q.2.2) =
          gm (D.map g) y _ (t q.1 q.2.2) := by
    rintro ⟨k, l, m⟩
    have hkl : IsCompact ((V k ⊓ V l : (D.obj n).Opens) : Set (D.obj n)) := by
      rw [Opens.coe_inf]
      exact QuasiSeparatedSpace.inter_isCompact _ _ (V k).isOpen (hV k) (V l).isOpen (hV l)
    have hW : IsCompact ((V k ⊓ V l ⊓ V m : (D.obj n).Opens) : Set (D.obj n)) := by
      rw [Opens.coe_inf]
      exact QuasiSeparatedSpace.inter_isCompact _ _ (V k ⊓ V l).isOpen hkl (V m).isOpen (hV m)
    have h1 : V k ⊓ V l ⊓ V m ≤ V k ⊓ V l := inf_le_left
    have h2 : V k ⊓ V l ⊓ V m ≤ V l ⊓ V m := le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have h3 : V k ⊓ V l ⊓ V m ≤ V k ⊓ V m := le_inf (inf_le_left.trans inf_le_left) inf_le_right
    obtain ⟨n₁, g, hg⟩ := exists_unit_eq D c hc (V k ⊓ V l ⊓ V m) hW
      (res h1 (t k l) * res h2 (t l m)) (res h3 (t k m)) (fun z hz => by
        rw [map_mul, gm_res _ _ h1 hz, gm_res _ _ h2 hz, gm_res _ _ h3 hz]
        obtain ⟨hz12, hz3⟩ := Opens.mem_inf.1 hz
        obtain ⟨hz1, hz2⟩ := Opens.mem_inf.1 hz12
        exact h k l m z hz1 hz2 hz3)
    refine ⟨n₁, g, fun y hk hl hm => ?_⟩
    have hy : D.map g y ∈ V k ⊓ V l ⊓ V m := Opens.mem_inf.2 ⟨Opens.mem_inf.2 ⟨hk, hl⟩, hm⟩
    have := hg y hy
    rwa [map_mul, gm_res _ _ h1 hy, gm_res _ _ h2 hy, gm_res _ _ h3 hy] at this
  obtain ⟨n', g, hg⟩ := exists_forall_of_cofiltered (i := n) (J := S × S × S)
    (fun q n₁ (g : n₁ ⟶ n) => ∀ y, D.map g y ∈ V q.1 → D.map g y ∈ V q.2.1 → D.map g y ∈ V q.2.2 →
        gm (D.map g) y _ (t q.1 q.2.1) * gm (D.map g) y _ (t q.2.1 q.2.2) =
          gm (D.map g) y _ (t q.1 q.2.2))
    (fun q n₁ n₂ g' g h => hmono q n₁ n₂ g' g h) hexist
  exact ⟨n', g, fun k l m y hk hl hm => hg (k, l, m) y hk hl hm⟩

include hc in

/- English proof (translation)
Take `⟨j, S, _, W, a, hW, hcov, hle⟩` from `exists_finite_cover D c hc M hM`. Establish `hcomp : ∀ p : S × S, IsCompact ((W p.1 ⊓ W p.2 : (D.obj j).Opens) : Set (D.obj j))` using `fun p => QuasiSeparatedSpace.inter_isCompact _ _ (W p.1).isOpen (hW p.1) (W p.2).isOpen (hW p.2)`. Establish `hle₂ : ∀ p : S × S, c.π.app j ⁻¹ᵁ (W p.1 ⊓ W p.2) ≤ M.U (a p.1) ⊓ M.U (a p.2)` using `fun p y hy => ⟨hle _ hy.1, hle _ hy.2⟩`. Take `⟨n, f, t, ht⟩` from `exists_units_stage D c hc (fun p : S × S => W p.1 ⊓ W p.2) hcomp (fun p => res (hle₂ p) (M.g (a p.1) (a p.2)))`. Establish `hπ : ∀ {n₁ n₂ : I} (g : n₂ ⟶ n₁) (z : c.pt), D.map g (c.π.app n₂ z) = c.π.app n₁ z` using `fun g z => by rw [← Scheme.Hom.comp_apply, c.w]`.

Set `V : S → (D.obj n).Opens` to `fun k => D.map f ⁻¹ᵁ W k`. Establish `hV : ∀ k, IsCompact (V k : Set (D.obj n))` using `fun k => (D.map f).isCompact_preimage (hW k)`. Establish `lV : ∀ k l, V k ⊓ V l ≤ D.map f ⁻¹ᵁ (W k ⊓ W l)` using `fun k l _ h => h`. Set `t₁ : ∀ k l, Γ(D.obj n, V k ⊓ V l)ˣ` to `fun k l => res (lV k l) (t (k, l))`. Establish `ht₁ : ∀ k l z, c.π.app n z ∈ V k → c.π.app n z ∈ V l → gm (c.π.app n) z _ (t₁ k l) = gm (𝟙 c.pt) z _ (M.g (a k) (a l))` using `fun k l z hk hl => by`.

Establish `hz : c.π.app j z ∈ W k ⊓ W l`. Rewrite using `[← hπ f z]`. Conclude with `⟨hk, hl⟩`. Conclude with `(gm_res _ z (lV k l) ⟨hk, hl⟩ _).trans ((ht (k, l) z hz).trans (gm_res (𝟙 c.pt) z (hle₂ (k, l)) (show z ∈ c.π.app j ⁻¹ᵁ (W k ⊓ W l) from hz) _))`. Establish `hle₁ : ∀ k, c.π.app n ⁻¹ᵁ V k ≤ M.U (a k)` using `fun k => by`.

Establish `: c.π.app n ⁻¹ᵁ V k = c.π.app j ⁻¹ᵁ W k` using `by show c.π.app n ⁻¹ᵁ (D.map f ⁻¹ᵁ W k) = _`. Rewrite using `[← Scheme.Hom.comp_preimage, c.w]`. Rewrite using `[this]`. Conclude with `hle k`. Take `⟨n', g, hg⟩` from `exists_cocycle_stage D c hc V hV t₁ (fun k l m z h₁ h₂ h₃ => by`.

Rewrite using `[ht₁ k l z h₁ h₂, ht₁ l m z h₂ h₃, ht₁ k m z h₁ h₃]`. Conclude with `gm_cocycle hM (𝟙 c.pt) z (hle₁ k h₁) (hle₁ l h₂) (hle₁ m h₃))`. Set `V₁ : S → (D.obj n').Opens` to `fun k => D.map g ⁻¹ᵁ V k`. Establish `lV₁ : ∀ k l, V₁ k ⊓ V₁ l ≤ D.map g ⁻¹ᵁ (V k ⊓ V l)` using `fun k l _ h => h`. Set `t₂ : ∀ k l, Γ(D.obj n', V₁ k ⊓ V₁ l)ˣ` to `fun k l => res (lV₁ k l) (pullU (D.map g) _ (t₁ k l))`.

Establish `ht₂ : ∀ {Z : Scheme.{0}} (r : Z ⟶ D.obj n') (k l) (z : Z), r z ∈ V₁ k → r z ∈ V₁ l → gm r z _ (t₂ k l) = gm (r ≫ D.map g) z _ (t₁ k l)` using `fun r k l z hk hl => (gm_res r z (lV₁ k l) ⟨hk, hl⟩ _).trans (gm_pull r (D.map g) z _ (lV₁ k l ⟨hk, hl⟩) _)`. Use `⟨n', ⟨S, V₁, t₂⟩, isLB_of_germs V₁ t₂ (fun y => ?_) (fun k l m y h₁ h₂ h₃ => ?_), ?_⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `hcov (D.map (g ≫ f) y)`. Use `⟨k, ?_⟩` and prove the remaining obligations. Use `show D.map f (D.map g y) ∈ W k`.

Rewrite using `[← Scheme.Hom.comp_apply, ← D.map_comp]`. Conclude with `hk`. Rewrite using `[ht₂ _ k l y h₁ h₂, ht₂ _ l m y h₂ h₃, ht₂ _ k m y h₁ h₃, Category.id_comp]`. Conclude with `hg k l m y h₁ h₂ h₃`. Use `exists_iso_pull (c.π.app n') M hM ⟨S, V₁, t₂⟩ a (fun k y hy => ?_) (fun k l y hk hl => ?_)` and prove the remaining obligations.

Use `hle₁ k ?_ show c.π.app n y ∈ V k` and prove the remaining obligations. Rewrite using `[← hπ g y]`. Conclude with `hy`. Establish `hk' : c.π.app n y ∈ V k` using `by rw [← hπ g y]; exact hk`. Establish `hl' : c.π.app n y ∈ V l` using `by rw [← hπ g y]; exact hl`.

Use `(ht₂ _ k l y hk hl).trans ?_` and prove the remaining obligations. Rewrite using `[c.w g]`. Conclude with `ht₁ k l y hk' hl'`.
-/
theorem exists_lb_stage [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (M : LB c.pt) (hM : M.IsLB) :
    ∃ (i : I) (M₁ : LB (D.obj i)), M₁.IsLB ∧ ∃ w : LB.Iso M (M₁.pull (c.π.app i)), w.IsGen := by
  obtain ⟨j, S, _, W, a, hW, hcov, hle⟩ := exists_finite_cover D c hc M hM
  have hcomp : ∀ p : S × S, IsCompact ((W p.1 ⊓ W p.2 : (D.obj j).Opens) : Set (D.obj j)) :=
    fun p => QuasiSeparatedSpace.inter_isCompact _ _ (W p.1).isOpen (hW p.1) (W p.2).isOpen (hW p.2)
  have hle₂ : ∀ p : S × S, c.π.app j ⁻¹ᵁ (W p.1 ⊓ W p.2) ≤ M.U (a p.1) ⊓ M.U (a p.2) :=
    fun p y hy => ⟨hle _ hy.1, hle _ hy.2⟩
  obtain ⟨n, f, t, ht⟩ := exists_units_stage D c hc (fun p : S × S => W p.1 ⊓ W p.2) hcomp
    (fun p => res (hle₂ p) (M.g (a p.1) (a p.2)))
  have hπ : ∀ {n₁ n₂ : I} (g : n₂ ⟶ n₁) (z : c.pt), D.map g (c.π.app n₂ z) = c.π.app n₁ z :=
    fun g z => by rw [← Scheme.Hom.comp_apply, c.w]
  let V : S → (D.obj n).Opens := fun k => D.map f ⁻¹ᵁ W k
  have hV : ∀ k, IsCompact (V k : Set (D.obj n)) := fun k => (D.map f).isCompact_preimage (hW k)
  have lV : ∀ k l, V k ⊓ V l ≤ D.map f ⁻¹ᵁ (W k ⊓ W l) := fun k l _ h => h
  let t₁ : ∀ k l, Γ(D.obj n, V k ⊓ V l)ˣ := fun k l => res (lV k l) (t (k, l))
  have ht₁ : ∀ k l z, c.π.app n z ∈ V k → c.π.app n z ∈ V l →
      gm (c.π.app n) z _ (t₁ k l) = gm (𝟙 c.pt) z _ (M.g (a k) (a l)) := fun k l z hk hl => by
    have hz : c.π.app j z ∈ W k ⊓ W l := by
      rw [← hπ f z]; exact ⟨hk, hl⟩
    exact (gm_res _ z (lV k l) ⟨hk, hl⟩ _).trans ((ht (k, l) z hz).trans
      (gm_res (𝟙 c.pt) z (hle₂ (k, l)) (show z ∈ c.π.app j ⁻¹ᵁ (W k ⊓ W l) from hz) _))
  have hle₁ : ∀ k, c.π.app n ⁻¹ᵁ V k ≤ M.U (a k) := fun k => by
    have : c.π.app n ⁻¹ᵁ V k = c.π.app j ⁻¹ᵁ W k := by
      show c.π.app n ⁻¹ᵁ (D.map f ⁻¹ᵁ W k) = _
      rw [← Scheme.Hom.comp_preimage, c.w]
    rw [this]; exact hle k
  obtain ⟨n', g, hg⟩ := exists_cocycle_stage D c hc V hV t₁ (fun k l m z h₁ h₂ h₃ => by
    rw [ht₁ k l z h₁ h₂, ht₁ l m z h₂ h₃, ht₁ k m z h₁ h₃]
    exact gm_cocycle hM (𝟙 c.pt) z (hle₁ k h₁) (hle₁ l h₂) (hle₁ m h₃))
  let V₁ : S → (D.obj n').Opens := fun k => D.map g ⁻¹ᵁ V k
  have lV₁ : ∀ k l, V₁ k ⊓ V₁ l ≤ D.map g ⁻¹ᵁ (V k ⊓ V l) := fun k l _ h => h
  let t₂ : ∀ k l, Γ(D.obj n', V₁ k ⊓ V₁ l)ˣ := fun k l => res (lV₁ k l) (pullU (D.map g) _ (t₁ k l))
  have ht₂ : ∀ {Z : Scheme.{0}} (r : Z ⟶ D.obj n') (k l) (z : Z), r z ∈ V₁ k → r z ∈ V₁ l →
      gm r z _ (t₂ k l) = gm (r ≫ D.map g) z _ (t₁ k l) := fun r k l z hk hl =>
    (gm_res r z (lV₁ k l) ⟨hk, hl⟩ _).trans (gm_pull r (D.map g) z _ (lV₁ k l ⟨hk, hl⟩) _)
  refine ⟨n', ⟨S, V₁, t₂⟩, isLB_of_germs V₁ t₂ (fun y => ?_) (fun k l m y h₁ h₂ h₃ => ?_), ?_⟩
  · obtain ⟨k, hk⟩ := hcov (D.map (g ≫ f) y)
    refine ⟨k, ?_⟩
    show D.map f (D.map g y) ∈ W k
    rw [← Scheme.Hom.comp_apply, ← D.map_comp]
    exact hk
  · rw [ht₂ _ k l y h₁ h₂, ht₂ _ l m y h₂ h₃, ht₂ _ k m y h₁ h₃, Category.id_comp]
    exact hg k l m y h₁ h₂ h₃
  · refine exists_iso_pull (c.π.app n') M hM ⟨S, V₁, t₂⟩ a (fun k y hy => ?_)
      (fun k l y hk hl => ?_)
    · refine hle₁ k ?_
      show c.π.app n y ∈ V k
      rw [← hπ g y]
      exact hy
    · have hk' : c.π.app n y ∈ V k := by rw [← hπ g y]; exact hk
      have hl' : c.π.app n y ∈ V l := by rw [← hπ g y]; exact hl
      refine (ht₂ _ k l y hk hl).trans ?_
      rw [c.w g]
      exact ht₁ k l y hk' hl'

end Limit

/- English proof (translation)
Introduce `R R₀ _ _ φ Y Y₀ f f₀ π hmod M hM`. Take `⟨hft, -, hqc, hqs, hpb⟩` from `hmod`. Use `letI : Algebra R₀ R := φ.toAlgebra`. Set `A : Finset R → Subalgebra R₀ R` to `fun s => Algebra.adjoin R₀ (s : Set R)`. Set `F : Finset R ⥤ CommRingCat.{0}` to `{ obj s := .of (A s) map {s t} h := CommRingCat.ofHom (Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.mpr h.le))).toRingHom }`.

Set `cF : Cocone F` to `{ pt := .of R := { app s := CommRingCat.ofHom (A s).val.toRingHom } }`. Establish `: ReflectsFilteredColimits (forget CommRingCat.{0})` using `⟨fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms⟩`. Establish `hcF : IsColimit cF` using `isColimitOfReflects (forget _) (Types.FilteredColimit.isColimitOf' _ _ (fun x ↦ by`. Set `x' : R` to `x`. Conclude with `⟨({x'} : Finset R), (⟨x', Algebra.subset_adjoin (by simp)⟩ : Algebra.adjoin R₀ (({x'} : Finset R) : Set R)), rfl⟩)`.

Use the proof step `(fun i x y hxy ↦ ⟨i, 𝟙 i, congrArg _ (Subtype.ext hxy)⟩))`. Set `G : (Finset R)ᵒᵖ ⥤ Scheme.{0}` to `F.op ⋙ Scheme.Spec`. Set `cG : Cone G` to `Scheme.Spec.mapCone cF.op`. Establish `hcG : IsLimit cG` using `isLimitOfPreserves Scheme.Spec hcF.op`. Set `κ (s : (Finset R)ᵒᵖ) : G.obj s ⟶ Spec (CommRingCat.of R₀)` to `Spec.map (CommRingCat.ofHom (algebraMap R₀ (A s.unop)))`.

Establish `hι {s t : (Finset R)ᵒᵖ} (h : s ⟶ t) : G.map h ≫ κ t = κ s`. Express the relevant statement in the definitionally equal form `Spec.map _ ≫ Spec.map _ = Spec.map _`. Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression. Establish `hι' (s : (Finset R)ᵒᵖ) : cG.π.app s ≫ κ s = Spec.map (CommRingCat.ofHom φ)`.

Express the relevant statement in the definitionally equal form `Spec.map _ ≫ Spec.map _ = Spec.map _`. Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression. Set `mp {s t : (Finset R)ᵒᵖ} (h : s ⟶ t) : pullback f₀ (κ s) ⟶ pullback f₀ (κ t)` to `pullback.lift (pullback.fst f₀ (κ s)) (pullback.snd f₀ (κ s) ≫ G.map h) (by rw [pullback.condition, Category.assoc, hι])`. Establish `mp₁ {s t : (Finset R)ᵒᵖ} (h : s ⟶ t) : mp h ≫ pullback.fst f₀ (κ t) = pullback.fst f₀ (κ s)` using `pullback.lift_fst _ _ _`.

Establish `mp₂ {s t : (Finset R)ᵒᵖ} (h : s ⟶ t) : mp h ≫ pullback.snd f₀ (κ t) = pullback.snd f₀ (κ s) ≫ G.map h` using `pullback.lift_snd _ _ _`. Set `D : (Finset R)ᵒᵖ ⥤ Scheme.{0}` to `{ obj s := pullback f₀ (κ s) map h := mp h map_id s := by`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[mp₁, Category.id_comp]`. Rewrite using `[mp₂, G.map_id, Category.comp_id, Category.id_comp]`.

Use `map_comp {s t u} h h' := by`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, mp₁, mp₁, mp₁]`. Rewrite using `[Category.assoc, mp₂, mp₂, ← Category.assoc, mp₂, Category.assoc, G.map_comp] }`. Set `α : D ⟶ G` to `{ app s := pullback.snd _ _ naturality s t h := mp₂ h }`.

Set `ρ (s : (Finset R)ᵒᵖ) : Y ⟶ pullback f₀ (κ s)` to `pullback.lift π (f ≫ cG.π.app s) (by rw [hpb.w, Category.assoc, hι'])`. Establish `ρ₁ (s : (Finset R)ᵒᵖ) : ρ s ≫ pullback.fst f₀ (κ s) = π` using `pullback.lift_fst _ _ _`. Establish `ρ₂ (s : (Finset R)ᵒᵖ) : ρ s ≫ pullback.snd f₀ (κ s) = f ≫ cG.π.app s` using `pullback.lift_snd _ _ _`. Set `cD : Cone D` to `{ pt := Y π := { app s := ρ s naturality s t h := (Category.id_comp _).trans (pullback.hom_ext (by show ρ t ≫ pullback.fst f₀ (κ t) = (ρ s ≫ mp h) ≫ pullback.fst f₀ (κ t)`. Rewrite using `[Category.assoc, mp₁, ρ₁, ρ₁])`.

Use the proof step `(by show ρ t ≫ pullback.snd f₀ (κ t) = (ρ s ≫ mp h) ≫ pullback.snd f₀ (κ t)`. Rewrite using `[Category.assoc, mp₂, ← Category.assoc, ρ₂, ρ₂, Category.assoc, cG.w h])) } }`. Establish `hρ (s : (Finset R)ᵒᵖ) : IsPullback (ρ s) f (pullback.snd f₀ (κ s)) (cG.π.app s)`. Use `IsPullback.of_right (h₁₂ := pullback.fst f₀ (κ s)) (v₁₃ := f₀) (h₂₂ := κ s) ?_ (ρ₂ s) (IsPullback.of_hasPullback f₀ (κ s))` and prove the remaining obligations. Rewrite using `[hι', ρ₁]`.

Conclude with `hpb`. Establish `hcD : IsLimit cD` using `isLimitOfIsPullbackOfIsConnected α cD cG { hom := f, w s := (hρ s).w.symm } (fun s => hρ s) hcG`. Establish `hD {s t : (Finset R)ᵒᵖ} (h : s ⟶ t) : IsPullback (D.map h) (pullback.snd f₀ (κ s)) (pullback.snd f₀ (κ t)) (G.map h)`. Use `IsPullback.of_right (h₁₂ := pullback.fst f₀ (κ t)) (v₁₃ := f₀) (h₂₂ := κ t) ?_ (mp₂ h) (IsPullback.of_hasPullback f₀ (κ t))` and prove the remaining obligations. Rewrite using `[hι h, show D.map h ≫ pullback.fst f₀ (κ t) = pullback.fst f₀ (κ s) from mp₁ h]`.

Conclude with `IsPullback.of_hasPullback f₀ (κ s)`. Establish `hG (s : (Finset R)ᵒᵖ) : IsAffine (G.obj s)` using `inferInstanceAs (IsAffine (Spec _))`. Establish `hGa {s t : (Finset R)ᵒᵖ} (h : s ⟶ t) : IsAffineHom (G.map h)` using `inferInstance`. Establish `{s t : (Finset R)ᵒᵖ} (h : s ⟶ t) : IsAffineHom (D.map h)` using `MorphismProperty.of_isPullback (hD h).flip (hGa h)`. Establish `(s : (Finset R)ᵒᵖ) : CompactSpace (D.obj s)`.

Establish `: QuasiCompact (pullback.snd f₀ (κ s))` using `inferInstance`. Use the proof step `QuasiCompact.compactSpace_of_compactSpace (pullback.snd f₀ (κ s))`. Establish `(s : (Finset R)ᵒᵖ) : QuasiSeparatedSpace (D.obj s)`. Establish `: QuasiSeparated (pullback.snd f₀ (κ s))` using `inferInstance`. Use the proof step `(quasiSeparated_iff_quasiSeparatedSpace (pullback.snd f₀ (κ s))).mp this`.

Take `⟨i, M₁, hM₁, w, hw⟩` from `exists_lb_stage D cD hcD M hM`. Establish `hft₁ : Algebra.FiniteType R₀ (A i.unop)` using `Algebra.FiniteType.adjoin_of_finite i.unop.finite_toSet`. Use `⟨A i.unop, inferInstance, algebraMap R₀ (A i.unop), (A i.unop).val.toRingHom, ρ i, ?_, Algebra.FiniteType.trans hft hft₁, ρ₁ i, ?_, M₁, hM₁, w, hw⟩` and prove the remaining obligations. Use extensionality with `x`. Both sides reduce to the same expression.

Conclude with `ρ₂ i`.
-/
theorem lbSpreads : LBSpreads := by
  intro R R₀ _ _ φ Y Y₀ f f₀ π hmod M hM
  obtain ⟨hft, -, hqc, hqs, hpb⟩ := hmod
  classical
  letI : Algebra R₀ R := φ.toAlgebra
  let A : Finset R → Subalgebra R₀ R := fun s => Algebra.adjoin R₀ (s : Set R)
  let F : Finset R ⥤ CommRingCat.{0} :=
    { obj s := .of (A s)
      map {s t} h := CommRingCat.ofHom
        (Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.mpr h.le))).toRingHom }
  let cF : Cocone F :=
    { pt := .of R
      «ι» := { app s := CommRingCat.ofHom (A s).val.toRingHom } }
  have : ReflectsFilteredColimits (forget CommRingCat.{0}) :=
    ⟨fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms⟩
  have hcF : IsColimit cF := isColimitOfReflects (forget _)
    (Types.FilteredColimit.isColimitOf' _ _
      (fun x ↦ by
        let x' : R := x
        exact ⟨({x'} : Finset R), (⟨x', Algebra.subset_adjoin (by simp)⟩ :
          Algebra.adjoin R₀ (({x'} : Finset R) : Set R)), rfl⟩)
      (fun i x y hxy ↦ ⟨i, 𝟙 i, congrArg _ (Subtype.ext hxy)⟩))
  let G : (Finset R)ᵒᵖ ⥤ Scheme.{0} := F.op ⋙ Scheme.Spec
  let cG : Cone G := Scheme.Spec.mapCone cF.op
  have hcG : IsLimit cG := isLimitOfPreserves Scheme.Spec hcF.op
  let κ (s : (Finset R)ᵒᵖ) : G.obj s ⟶ Spec (CommRingCat.of R₀) :=
    Spec.map (CommRingCat.ofHom (algebraMap R₀ (A s.unop)))
  have hι {s t : (Finset R)ᵒᵖ} (h : s ⟶ t) : G.map h ≫ κ t = κ s := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  have hι' (s : (Finset R)ᵒᵖ) : cG.π.app s ≫ κ s = Spec.map (CommRingCat.ofHom φ) := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  let mp {s t : (Finset R)ᵒᵖ} (h : s ⟶ t) : pullback f₀ (κ s) ⟶ pullback f₀ (κ t) :=
    pullback.lift (pullback.fst f₀ (κ s)) (pullback.snd f₀ (κ s) ≫ G.map h)
      (by rw [pullback.condition, Category.assoc, hι])
  have mp₁ {s t : (Finset R)ᵒᵖ} (h : s ⟶ t) :
      mp h ≫ pullback.fst f₀ (κ t) = pullback.fst f₀ (κ s) := pullback.lift_fst _ _ _
  have mp₂ {s t : (Finset R)ᵒᵖ} (h : s ⟶ t) :
      mp h ≫ pullback.snd f₀ (κ t) = pullback.snd f₀ (κ s) ≫ G.map h := pullback.lift_snd _ _ _
  let D : (Finset R)ᵒᵖ ⥤ Scheme.{0} :=
    { obj s := pullback f₀ (κ s)
      map h := mp h
      map_id s := by
        apply pullback.hom_ext
        · rw [mp₁, Category.id_comp]
        · rw [mp₂, G.map_id, Category.comp_id, Category.id_comp]
      map_comp {s t u} h h' := by
        apply pullback.hom_ext
        · rw [Category.assoc, mp₁, mp₁, mp₁]
        · rw [Category.assoc, mp₂, mp₂, ← Category.assoc, mp₂, Category.assoc, G.map_comp] }
  let α : D ⟶ G :=
    { app s := pullback.snd _ _
      naturality s t h := mp₂ h }
  let ρ (s : (Finset R)ᵒᵖ) : Y ⟶ pullback f₀ (κ s) :=
    pullback.lift π (f ≫ cG.π.app s) (by rw [hpb.w, Category.assoc, hι'])
  have ρ₁ (s : (Finset R)ᵒᵖ) : ρ s ≫ pullback.fst f₀ (κ s) = π := pullback.lift_fst _ _ _
  have ρ₂ (s : (Finset R)ᵒᵖ) : ρ s ≫ pullback.snd f₀ (κ s) = f ≫ cG.π.app s :=
    pullback.lift_snd _ _ _
  let cD : Cone D :=
    { pt := Y
      π :=
        { app s := ρ s
          naturality s t h := (Category.id_comp _).trans (pullback.hom_ext
            (by
              show ρ t ≫ pullback.fst f₀ (κ t) = (ρ s ≫ mp h) ≫ pullback.fst f₀ (κ t)
              rw [Category.assoc, mp₁, ρ₁, ρ₁])
            (by
              show ρ t ≫ pullback.snd f₀ (κ t) = (ρ s ≫ mp h) ≫ pullback.snd f₀ (κ t)
              rw [Category.assoc, mp₂, ← Category.assoc, ρ₂, ρ₂, Category.assoc, cG.w h])) } }
  have hρ (s : (Finset R)ᵒᵖ) : IsPullback (ρ s) f (pullback.snd f₀ (κ s)) (cG.π.app s) := by
    refine IsPullback.of_right (h₁₂ := pullback.fst f₀ (κ s)) (v₁₃ := f₀) (h₂₂ := κ s) ?_
      (ρ₂ s) (IsPullback.of_hasPullback f₀ (κ s))
    rw [hι', ρ₁]
    exact hpb
  have hcD : IsLimit cD := isLimitOfIsPullbackOfIsConnected α cD cG
    { hom := f, w s := (hρ s).w.symm } (fun s => hρ s) hcG
  have hD {s t : (Finset R)ᵒᵖ} (h : s ⟶ t) :
      IsPullback (D.map h) (pullback.snd f₀ (κ s)) (pullback.snd f₀ (κ t)) (G.map h) := by
    refine IsPullback.of_right (h₁₂ := pullback.fst f₀ (κ t)) (v₁₃ := f₀) (h₂₂ := κ t) ?_
      (mp₂ h) (IsPullback.of_hasPullback f₀ (κ t))
    rw [hι h, show D.map h ≫ pullback.fst f₀ (κ t) = pullback.fst f₀ (κ s) from mp₁ h]
    exact IsPullback.of_hasPullback f₀ (κ s)
  have hG (s : (Finset R)ᵒᵖ) : IsAffine (G.obj s) := inferInstanceAs (IsAffine (Spec _))
  have hGa {s t : (Finset R)ᵒᵖ} (h : s ⟶ t) : IsAffineHom (G.map h) := inferInstance
  have {s t : (Finset R)ᵒᵖ} (h : s ⟶ t) : IsAffineHom (D.map h) :=
    MorphismProperty.of_isPullback (hD h).flip (hGa h)
  have (s : (Finset R)ᵒᵖ) : CompactSpace (D.obj s) :=
    have : QuasiCompact (pullback.snd f₀ (κ s)) := inferInstance
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f₀ (κ s))
  have (s : (Finset R)ᵒᵖ) : QuasiSeparatedSpace (D.obj s) :=
    have : QuasiSeparated (pullback.snd f₀ (κ s)) := inferInstance
    (quasiSeparated_iff_quasiSeparatedSpace (pullback.snd f₀ (κ s))).mp this
  obtain ⟨i, M₁, hM₁, w, hw⟩ := exists_lb_stage D cD hcD M hM
  have hft₁ : Algebra.FiniteType R₀ (A i.unop) :=
    Algebra.FiniteType.adjoin_of_finite i.unop.finite_toSet
  refine ⟨A i.unop, inferInstance, algebraMap R₀ (A i.unop), (A i.unop).val.toRingHom, ρ i, ?_,
    Algebra.FiniteType.trans hft hft₁, ρ₁ i, ?_, M₁, hM₁, w, hw⟩
  · ext x
    rfl
  · exact ρ₂ i

end GlobalTheory.CompanionTheory.LBLimit
