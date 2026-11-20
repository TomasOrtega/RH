import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelRefinementGenerating
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.TrueGeo.SmallSec

namespace GlobalTheory.ProjSpace

section
variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

/- English proof (translation)
Take `⟨U, hx, s, rfl⟩` from `h.exists_fnOf`. Establish `hy : y ∈ j ⁻¹ᵁ U` using `hx`. Rewrite using `[fnMap_fnOf j hη _ (gen_mem hy)]`. Conclude with `regAt_fnOf hy _ _`.
-/
theorem regAt_fnMap_of (j : Y ⟶ X) (hη : j (genericPoint Y) ⤳ genericPoint X) {y : Y} {t : X.functionField}
    (h : RegAt (j y) t) : RegAt y (fnMap j hη t) := by
  obtain ⟨U, hx, s, rfl⟩ := h.exists_fnOf
  have hy : y ∈ j ⁻¹ᵁ U := hx
  rw [fnMap_fnOf j hη _ (gen_mem hy)]
  exact regAt_fnOf hy _ _

/- English proof (translation)
Rewrite using `[fnMap_fnOf j hη h (e h')]`. Conclude with `fnOf_resG e h' (j.app U a)`.
-/
theorem fnOf_appLE (j : Y ⟶ X) (hη : j (genericPoint Y) ⤳ genericPoint X) {U : X.Opens} {V : Y.Opens}
    (e : V ≤ j ⁻¹ᵁ U) (h : genericPoint X ∈ U) (h' : genericPoint Y ∈ V) (a : Γ(X, U)) :
    fnOf V h' ((j.appLE U V e).hom a) = fnMap j hη (fnOf U h a) := by
  rw [fnMap_fnOf j hη h (e h')]
  exact fnOf_resG e h' (j.app U a)

/- English proof (translation)
Rewrite using `[Scheme.Hom.comp_apply]`. Conclude with `(ha.map b.continuous).trans hb`.
-/
theorem comp_genericPoint_specializes {Z : Scheme.{0}} [IsIntegral Z] (a : Z ⟶ Y) (b : Y ⟶ X)
    (ha : a (genericPoint Z) ⤳ genericPoint Y) (hb : b (genericPoint Y) ⤳ genericPoint X) :
    (a ≫ b) (genericPoint Z) ⤳ genericPoint X := by
  rw [Scheme.Hom.comp_apply]
  exact (ha.map b.continuous).trans hb

/- English proof (translation)
Take `⟨U, hx, s, rfl⟩` from `(regAt_genericPoint t).exists_fnOf`. Establish `h1 : genericPoint Y ∈ b ⁻¹ᵁ U` using `hb.mem_open U.isOpen hx`. Establish `h2 : genericPoint Z ∈ a ⁻¹ᵁ (b ⁻¹ᵁ U)` using `ha.mem_open (b ⁻¹ᵁ U).isOpen h1`. Rewrite using `[fnMap_fnOf b hb _ h1, fnMap_fnOf a ha _ h2, fnMap_fnOf (a ≫ b) hab _ h2, Scheme.Hom.comp_app]`. Both sides reduce to the same expression.
-/
theorem fnMap_comp {Z : Scheme.{0}} [IsIntegral Z] (a : Z ⟶ Y) (b : Y ⟶ X)
    (ha : a (genericPoint Z) ⤳ genericPoint Y) (hb : b (genericPoint Y) ⤳ genericPoint X)
    (hab : (a ≫ b) (genericPoint Z) ⤳ genericPoint X) (t : X.functionField) :
    fnMap (a ≫ b) hab t = fnMap a ha (fnMap b hb t) := by
  obtain ⟨U, hx, s, rfl⟩ := (regAt_genericPoint t).exists_fnOf
  have h1 : genericPoint Y ∈ b ⁻¹ᵁ U := hb.mem_open U.isOpen hx
  have h2 : genericPoint Z ∈ a ⁻¹ᵁ (b ⁻¹ᵁ U) := ha.mem_open (b ⁻¹ᵁ U).isOpen h1
  rw [fnMap_fnOf b hb _ h1, fnMap_fnOf a ha _ h2, fnMap_fnOf (a ≫ b) hab _ h2, Scheme.Hom.comp_app]
  rfl

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
theorem fnMap_congr {a b : Y ⟶ X} (e : a = b) (ha : a (genericPoint Y) ⤳ genericPoint X)
    (hb : b (genericPoint Y) ⤳ genericPoint X) (t : X.functionField) : fnMap a ha t = fnMap b hb t := by
  subst e; rfl
end

/- English proof (translation)
The claim follows from `hU.to_subtype haveI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι ∃ (w : Fin (N + 1) → Y.functionField) (i₀ : Fin (N + 1)), w i₀ = 1 ∧ ∀ (u : U.toScheme) (k : Fin (N + 1)) (hk : u ∈ φ ⁻¹ᵁ GlobalTheory.ProjSpace.chart F N k), w k ≠ 0 ∧ ∀ j, GlobalTheory.TrueGeo.Smal …`.
-/
theorem exists_ratCoords : ∀ (F : Type) [Field F] (Y : Scheme.{0}) [IsIntegral Y] (N : ℕ) (U : Y.Opens) (hU : (U : Set Y).Nonempty)
    (φ : U.toScheme ⟶ PSpace F N),
    haveI : Nonempty U := hU.to_subtype
    haveI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
    ∃ (w : Fin (N + 1) → Y.functionField) (i₀ : Fin (N + 1)), w i₀ = 1 ∧
      ∀ (u : U.toScheme) (k : Fin (N + 1)) (hk : u ∈ φ ⁻¹ᵁ GlobalTheory.ProjSpace.chart F N k), w k ≠ 0 ∧ ∀ j,
        GlobalTheory.TrueGeo.SmallSec.fnMap U.ι (specializes_of_eq (genericPoint_eq_of_isOpenImmersion U.ι)) (w j / w k) =
          GlobalTheory.Cartier.fnOf (φ ⁻¹ᵁ GlobalTheory.ProjSpace.chart F N k) (GlobalTheory.Cartier.gen_mem hk)
            (GlobalTheory.ProjSpace.pullRatio φ _ k le_rfl j) := by
  intro F _ Y _ N U hU φ
  haveI : Nonempty U := hU.to_subtype
  haveI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  have hηU : U.ι (genericPoint U.toScheme) ⤳ genericPoint Y :=
    specializes_of_eq (genericPoint_eq_of_isOpenImmersion U.ι)
  obtain ⟨i₀, hi₀⟩ := exists_mem_chart F N (φ (genericPoint U.toScheme))
  have hg₀ : genericPoint U.toScheme ∈ φ ⁻¹ᵁ chart F N i₀ := hi₀
  choose w hw using fun j => fnMap_surjective U.ι hηU (fnOf _ hg₀ (pullRatio φ _ i₀ le_rfl j))
  refine ⟨w, i₀, ?_, fun u k hk => ?_⟩
  · apply (fnMap U.ι hηU).injective
    rw [hw, pullRatio_self, map_one, map_one]
  have hV : genericPoint U.toScheme ∈ φ ⁻¹ᵁ chart F N i₀ ⊓ φ ⁻¹ᵁ chart F N k := ⟨hg₀, gen_mem hk⟩
  have hmul : ∀ j, fnMap U.ι hηU (w j) =
      fnMap U.ι hηU (w k) * fnOf _ (gen_mem hk) (pullRatio φ _ k le_rfl j) := by
    intro j
    rw [hw, hw, ← fnOf_resG inf_le_left hV, ← fnOf_resG inf_le_left hV, ← fnOf_resG inf_le_right hV, ← map_mul,
      resG_pullRatio, resG_pullRatio, resG_pullRatio, pullRatio_mul_pullRatio]
  have hk0 : fnMap U.ι hηU (w k) ≠ 0 := by
    rw [hw, ← fnOf_resG inf_le_left hV, resG_pullRatio]
    refine ((unitAt_fnOf_iff hV hV _).2 ?_).ne_zero
    rw [basicOpen_pullRatio]
    exact ⟨hV, hV.2⟩
  refine ⟨fun h => hk0 (by rw [h, map_zero]), fun j => ?_⟩
  rw [map_div₀, hmul j, mul_div_cancel_left₀ _ hk0]

/- English proof (translation)
Introduce `F _ N Y _ q w hw`. Establish `hopen : ∀ k, IsOpen {y : Y | w k ≠ 0 ∧ ∀ j, RegAt y (w j / w k)}` using `fun k => by`. Use `isOpen_iff_forall_mem_open.2 fun y ⟨h0, hy⟩ => ?_` and prove the remaining obligations. Take `⟨W, hyW, hW⟩` from `GlobalTheory.InvertIdeal.exists_common_open hy`. Use `⟨W, fun y' hy' => ⟨h0, fun j => ?_⟩, W.isOpen, hyW⟩` and prove the remaining obligations.

Take `⟨a, ha⟩` from `hW j`. Conclude with `ha ▸ regAt_fnOf hy' _ a`. Set `U' : Fin (N + 1) → Y.Opens` to `fun k => ⟨_, hopen k⟩`. Establish `hr : ∀ k j, ∃ a : Γ(Y, U' k), ∀ h, fnOf (U' k) h a = w j / w k` using `fun k j => by`. Distinguish the cases in `h : genericPoint Y ∈ U' k`.

Take `⟨a, ha⟩` from `exists_fnOf_eq h fun y hy => hy.2 j`. Conclude with `⟨a, fun _ => ha⟩`. Conclude with `⟨0, fun h' => (h h').elim⟩`. Use `choose r hr using hr`. Establish `H : IsCoordFamily U' r` using `{ cover := top_le_iff.1 fun y _ => Opens.mem_iSup.2 (hw y) self := fun k => fn_ext fun h => by rw [hr, map_one, div_self h.1] mul := fun i j k => fn_ext fun h => by`.

Rewrite using `[map_mul, fnOf_resG, fnOf_resG, fnOf_resG, hr, hr, hr]`. Establish `hi : w i ≠ 0` using `h.1.1`. Establish `hj : w j ≠ 0` using `h.2.1`. Clear the denominators using the available nonvanishing facts. Use `basicOpen_le := fun i j y hy => by`.

Establish `hyi : y ∈ U' i` using `Y.basicOpen_le _ hy`. Establish `hu` using `(unitAt_fnOf_iff hyi (gen_mem hyi) (r i j)).2 hy`. Rewrite `hu` using `[hr]`. Establish `hi0 : w i ≠ 0` using `hyi.1`. Establish `hj0 : w j ≠ 0` using `fun h0 => hu.ne_zero (by rw [h0, zero_div])`.

Use `⟨hj0, fun l => ?_⟩` and prove the remaining obligations. Use `(hyi.2 l).mul hu.inv.regAt` as an intermediate fact. Rewrite using `[show w l / w i * (w j / w i)⁻¹ = w l / w j by field_simp] at this }` and apply the resulting hypothesis. Use `⟨H.toHom q, H.toHom_str q, fun y k hk0 hreg => ⟨U' k, ⟨hk0, hreg⟩, H.le_toHom_preimage q k, fun j => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[H.pullRatio_toHom q k j]`.

Conclude with `hr k j _`.
-/
theorem exists_hom_of_ratCoords : ∀ (F : Type) [Field F] (N : ℕ) (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp F)
    (w : Fin (N + 1) → Y.functionField),
    (∀ y : Y, ∃ k, w k ≠ 0 ∧ ∀ j, GlobalTheory.Cartier.RegAt y (w j / w k)) →
    ∃ g : Y ⟶ PSpace F N, g ≫ PSpace.str F N = q ∧ ∀ (y : Y) (k : Fin (N + 1)), w k ≠ 0 →
      (∀ j, GlobalTheory.Cartier.RegAt y (w j / w k)) →
      ∃ (W : Y.Opens) (hy : y ∈ W) (hW : W ≤ g ⁻¹ᵁ GlobalTheory.ProjSpace.chart F N k),
        ∀ j, GlobalTheory.Cartier.fnOf W (GlobalTheory.Cartier.gen_mem hy) (GlobalTheory.ProjSpace.pullRatio g W k hW j) = w j / w k := by
  intro F _ N Y _ q w hw
  classical
  have hopen : ∀ k, IsOpen {y : Y | w k ≠ 0 ∧ ∀ j, RegAt y (w j / w k)} := fun k => by
    refine isOpen_iff_forall_mem_open.2 fun y ⟨h0, hy⟩ => ?_
    obtain ⟨W, hyW, hW⟩ := GlobalTheory.InvertIdeal.exists_common_open hy
    refine ⟨W, fun y' hy' => ⟨h0, fun j => ?_⟩, W.isOpen, hyW⟩
    obtain ⟨a, ha⟩ := hW j
    exact ha ▸ regAt_fnOf hy' _ a
  let U' : Fin (N + 1) → Y.Opens := fun k => ⟨_, hopen k⟩
  have hr : ∀ k j, ∃ a : Γ(Y, U' k), ∀ h, fnOf (U' k) h a = w j / w k := fun k j => by
    by_cases h : genericPoint Y ∈ U' k
    · obtain ⟨a, ha⟩ := exists_fnOf_eq h fun y hy => hy.2 j
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h' => (h h').elim⟩
  choose r hr using hr
  have H : IsCoordFamily U' r :=
    { cover := top_le_iff.1 fun y _ => Opens.mem_iSup.2 (hw y)
      self := fun k => fn_ext fun h => by rw [hr, map_one, div_self h.1]
      mul := fun i j k => fn_ext fun h => by
        rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG, hr, hr, hr]
        have hi : w i ≠ 0 := h.1.1
        have hj : w j ≠ 0 := h.2.1
        field_simp
      basicOpen_le := fun i j y hy => by
        have hyi : y ∈ U' i := Y.basicOpen_le _ hy
        have hu := (unitAt_fnOf_iff hyi (gen_mem hyi) (r i j)).2 hy
        rw [hr] at hu
        have hi0 : w i ≠ 0 := hyi.1
        have hj0 : w j ≠ 0 := fun h0 => hu.ne_zero (by rw [h0, zero_div])
        refine ⟨hj0, fun l => ?_⟩
        have := (hyi.2 l).mul hu.inv.regAt
        rwa [show w l / w i * (w j / w i)⁻¹ = w l / w j by field_simp] at this }
  refine ⟨H.toHom q, H.toHom_str q, fun y k hk0 hreg => ⟨U' k, ⟨hk0, hreg⟩, H.le_toHom_preimage q k, fun j => ?_⟩⟩
  rw [H.pullRatio_toHom q k j]
  exact hr k j _

/- English proof (translation)
Introduce `F _ Y _ p N U φ hφ hU`. Use `haveI : Nonempty U := hU.to_subtype`. Use `haveI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι`. Establish `hηU : U.ι (genericPoint U.toScheme) ⤳ genericPoint Y` using `specializes_of_eq (genericPoint_eq_of_isOpenImmersion U.ι)`. Take `⟨w, i₀, hw₀, hw⟩` from `exists_ratCoords F Y N U hU φ`.

Establish `loc : ∀ (u : U.toScheme) k, u ∈ φ ⁻¹ᵁ chart F N k → w k ≠ 0 ∧ ∀ j, RegAt (U.ι u) (w j / w k)`. Introduce `u k hk`. Use `⟨(hw u k hk).1, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[← regAt_fnMap_iff U.ι hηU, (hw u k hk).2 j]`. Conclude with `regAt_fnOf hk _ _`.

Use `⟨w, i₀, hw₀, fun y hy => ?_, ?_⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `exists_mem_chart F N (φ ⟨y, hy⟩)`. Conclude with `⟨k, loc ⟨y, hy⟩ k hk⟩`. Introduce `Y' _ s hη hY'`. Take `⟨g, hg, hgW⟩` from `exists_hom_of_ratCoords F N Y' (s ≫ p) (fun j => fnMap s (specializes_of_eq hη) (w j)) hY'`.

Use `⟨g, hg, hom_ext ?_ fun z => ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, hg, Category.assoc, hφ, ← Category.assoc (s ∣_ U), morphismRestrict_ι, Category.assoc]`. Use `haveI : Nonempty (s ⁻¹ᵁ U).toScheme := ⟨z⟩`. Use `haveI : IsIntegral (s ⁻¹ᵁ U).toScheme := isIntegral_of_isOpenImmersion (s ⁻¹ᵁ U).ι`. Establish `hu : U.ι ((s ∣_ U) z) = s ((s ⁻¹ᵁ U).ι z)`.

Rewrite using `[← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]`. Establish `hηι : (s ⁻¹ᵁ U).ι (genericPoint (s ⁻¹ᵁ U).toScheme) ⤳ genericPoint Y'` using `specializes_of_eq (genericPoint_eq_of_isOpenImmersion _)`. Establish `hηr : (s ∣_ U) (genericPoint (s ⁻¹ᵁ U).toScheme) ⤳ genericPoint U.toScheme`. Use `specializes_of_eq (U.ι.isOpenEmbedding.injective ?_)` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply, genericPoint_eq_of_isOpenImmersion, hη, genericPoint_eq_of_isOpenImmersion]`.

Take `⟨k, hk⟩` from `exists_mem_chart F N (φ ((s ∣_ U) z))`. Take `⟨hk0, hreg⟩` from `loc _ k hk`. Establish `hreg' : ∀ j, RegAt ((s ⁻¹ᵁ U).ι z) (fnMap s (specializes_of_eq hη) (w j) / fnMap s (specializes_of_eq hη) (w k))` using `fun j => by`. Rewrite using `[← map_div₀]`. Conclude with `regAt_fnMap_of s _ (hu ▸ hreg j)`.

Take `⟨W, hzW, hW, hWj⟩` from `hgW _ k ((map_ne_zero _).2 hk0) hreg'`. Establish `hz : z ∈ (s ⁻¹ᵁ U).ι ⁻¹ᵁ W ⊓ (s ∣_ U) ⁻¹ᵁ (φ ⁻¹ᵁ chart F N k)` using `⟨hzW, hk⟩`. Use `⟨_, hz, k, inf_le_left.trans ((s ⁻¹ᵁ U).ι.preimage_mono hW), inf_le_right, fun j => ?_⟩` and prove the remaining obligations. Use `fnOf_injective _ (gen_mem hz) ?_` and prove the remaining obligations. Rewrite using `[← appLE_pullRatio (φ := g) (hi := hW) (s ⁻¹ᵁ U).ι inf_le_left, ← appLE_pullRatio (φ := φ) (hi := le_rfl) (s ∣_ U) inf_le_right, fnOf_appLE _ hηι _ (gen_mem hzW), fnOf_appLE _ hηr _ (gen_mem hk), hWj, ← (hw _ k hk).2 j, ← map_div₀, ← fnMap_comp _ _ hηι (specializes_of_eq hη) (com …`.

Conclude with `fnMap_congr (morphismRestrict_ι s U).symm _ _ _`.
-/
theorem exists_ratCoords_extend : ∀ (F : Type) [Field F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F) (N : ℕ) (U : Y.Opens)
    (φ : U.toScheme ⟶ PSpace F N), φ ≫ PSpace.str F N = U.ι ≫ p → (U : Set Y).Nonempty →
    ∃ (w : Fin (N + 1) → Y.functionField) (i₀ : Fin (N + 1)), w i₀ = 1 ∧
      (∀ y ∈ U, ∃ k, w k ≠ 0 ∧ ∀ j, GlobalTheory.Cartier.RegAt y (w j / w k)) ∧
      ∀ (Y' : Scheme.{0}) [IsIntegral Y'] (s : Y' ⟶ Y) (hη : s (genericPoint Y') = genericPoint Y),
        (∀ y' : Y', ∃ k, GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w k) ≠ 0 ∧ ∀ j, GlobalTheory.Cartier.RegAt y'
          (GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w j) / GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w k))) →
        ∃ g : Y' ⟶ PSpace F N, g ≫ PSpace.str F N = s ≫ p ∧ (s ⁻¹ᵁ U).ι ≫ g = (s ∣_ U) ≫ φ := by
  intro F _ Y _ p N U φ hφ hU
  haveI : Nonempty U := hU.to_subtype
  haveI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  have hηU : U.ι (genericPoint U.toScheme) ⤳ genericPoint Y :=
    specializes_of_eq (genericPoint_eq_of_isOpenImmersion U.ι)
  obtain ⟨w, i₀, hw₀, hw⟩ := exists_ratCoords F Y N U hU φ
  have loc : ∀ (u : U.toScheme) k, u ∈ φ ⁻¹ᵁ chart F N k → w k ≠ 0 ∧ ∀ j, RegAt (U.ι u) (w j / w k) := by
    intro u k hk
    refine ⟨(hw u k hk).1, fun j => ?_⟩
    rw [← regAt_fnMap_iff U.ι hηU, (hw u k hk).2 j]
    exact regAt_fnOf hk _ _
  refine ⟨w, i₀, hw₀, fun y hy => ?_, ?_⟩
  · obtain ⟨k, hk⟩ := exists_mem_chart F N (φ ⟨y, hy⟩)
    exact ⟨k, loc ⟨y, hy⟩ k hk⟩
  intro Y' _ s hη hY'
  obtain ⟨g, hg, hgW⟩ := exists_hom_of_ratCoords F N Y' (s ≫ p) (fun j => fnMap s (specializes_of_eq hη) (w j)) hY'
  refine ⟨g, hg, hom_ext ?_ fun z => ?_⟩
  · rw [Category.assoc, hg, Category.assoc, hφ, ← Category.assoc (s ∣_ U), morphismRestrict_ι, Category.assoc]
  haveI : Nonempty (s ⁻¹ᵁ U).toScheme := ⟨z⟩
  haveI : IsIntegral (s ⁻¹ᵁ U).toScheme := isIntegral_of_isOpenImmersion (s ⁻¹ᵁ U).ι
  have hu : U.ι ((s ∣_ U) z) = s ((s ⁻¹ᵁ U).ι z) := by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  have hηι : (s ⁻¹ᵁ U).ι (genericPoint (s ⁻¹ᵁ U).toScheme) ⤳ genericPoint Y' :=
    specializes_of_eq (genericPoint_eq_of_isOpenImmersion _)
  have hηr : (s ∣_ U) (genericPoint (s ⁻¹ᵁ U).toScheme) ⤳ genericPoint U.toScheme := by
    refine specializes_of_eq (U.ι.isOpenEmbedding.injective ?_)
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply,
      genericPoint_eq_of_isOpenImmersion, hη, genericPoint_eq_of_isOpenImmersion]
  obtain ⟨k, hk⟩ := exists_mem_chart F N (φ ((s ∣_ U) z))
  obtain ⟨hk0, hreg⟩ := loc _ k hk
  have hreg' : ∀ j, RegAt ((s ⁻¹ᵁ U).ι z)
      (fnMap s (specializes_of_eq hη) (w j) / fnMap s (specializes_of_eq hη) (w k)) := fun j => by
    rw [← map_div₀]
    exact regAt_fnMap_of s _ (hu ▸ hreg j)
  obtain ⟨W, hzW, hW, hWj⟩ := hgW _ k ((map_ne_zero _).2 hk0) hreg'
  have hz : z ∈ (s ⁻¹ᵁ U).ι ⁻¹ᵁ W ⊓ (s ∣_ U) ⁻¹ᵁ (φ ⁻¹ᵁ chart F N k) := ⟨hzW, hk⟩
  refine ⟨_, hz, k, inf_le_left.trans ((s ⁻¹ᵁ U).ι.preimage_mono hW), inf_le_right, fun j => ?_⟩
  refine fnOf_injective _ (gen_mem hz) ?_
  rw [← appLE_pullRatio (φ := g) (hi := hW) (s ⁻¹ᵁ U).ι inf_le_left,
    ← appLE_pullRatio (φ := φ) (hi := le_rfl) (s ∣_ U) inf_le_right,
    fnOf_appLE _ hηι _ (gen_mem hzW), fnOf_appLE _ hηr _ (gen_mem hk), hWj, ← (hw _ k hk).2 j, ← map_div₀,
    ← fnMap_comp _ _ hηι (specializes_of_eq hη) (comp_genericPoint_specializes _ _ hηι (specializes_of_eq hη)),
    ← fnMap_comp _ _ hηr hηU (comp_genericPoint_specializes _ _ hηr hηU)]
  exact fnMap_congr (morphismRestrict_ι s U).symm _ _ _

end GlobalTheory.ProjSpace
