import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfLocalOnBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsBasisOfIsField
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.AppLESurjective
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsStdSympZmod
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsLevelStructureOfWeilPairing

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

noncomputable section

namespace GlobalTheory.PrincipalNumerics

/- English proof (translation)
Establish `hc : ∀ (U : X.Opens) (a : K), constFn p U a = (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom (p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a))` using `fun U a => rfl`. Establish `hb : Function.Bijective (fun a : K => p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a))` using `hp.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv)`. Use `⟨fun _ => ⟨fun _ => 1, fun i j => by rw [hg, map_one, map_one, Units.val_one, _root_.mul_one]⟩, fun t => ?_⟩` and prove the remaining obligations. Take `⟨s, hs, hu⟩` from `X.sheaf.existsUnique_gluing' M.U ⊤ (fun i => homOfLE le_top) hM.cover.ge t.f (fun i j => by`. Use `t.compat i j` as an intermediate fact.

Rewrite `this` using `[hg, Units.val_one, _root_.one_mul]`. Conclude with `this)`. Take `⟨a, rfl⟩` from `hb.2 s`. Use `⟨fun _ => a, fun j => ?_, fun b hb' => ?_⟩` and prove the remaining obligations. Rewrite using `[Fin.sum_univ_one, _root_.mul_one, hc]`.

Conclude with `(hs j).symm`. Use function extensionality and compare the values at `i`. Take `rfl : i = 0` from `Subsingleton.elim _ _`. Use `hb.1 (hu _ fun j => ?_)` and prove the remaining obligations. Use `hb' j` as an intermediate fact.

Rewrite `this` using `[Fin.sum_univ_one, _root_.mul_one, hc]`. Conclude with `this.symm`.
-/
theorem sectionsFiniteDimension_one_trivial_transitions {K : Type} [Field K] {X : Scheme.{0}} (p : X ⟶ Sp K)
    (hp : Function.Bijective p.appTop.hom) {M : LB X} (hM : M.IsLB) (hg : ∀ i j, M.g i j = 1) : SectionsHaveFiniteDimension p M 1 := by
  have hc : ∀ (U : X.Opens) (a : K), constFn p U a = (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
      (p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)) := fun U a => rfl
  have hb : Function.Bijective (fun a : K => p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)) :=
    hp.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv)
  refine ⟨fun _ => ⟨fun _ => 1, fun i j => by rw [hg, map_one, map_one, Units.val_one, _root_.mul_one]⟩, fun t => ?_⟩
  obtain ⟨s, hs, hu⟩ := X.sheaf.existsUnique_gluing' M.U ⊤ (fun i => homOfLE le_top) hM.cover.ge t.f (fun i j => by
    have := t.compat i j
    rw [hg, Units.val_one, _root_.one_mul] at this
    exact this)
  obtain ⟨a, rfl⟩ := hb.2 s
  refine ⟨fun _ => a, fun j => ?_, fun b hb' => ?_⟩
  · rw [Fin.sum_univ_one, _root_.mul_one, hc]
    exact (hs j).symm
  · funext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    refine hb.1 (hu _ fun j => ?_)
    have := hb' j
    rw [Fin.sum_univ_one, _root_.mul_one, hc] at this
    exact this.symm

variable {K : Type} [Field K]

/- English proof (translation)
Use `⟨fun e => if e = 0 then 1 else e ^ P.g, fun e => ?_, ?_⟩` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos e with rfl | he` into its components or cases. Use `sectionsFiniteDimension_one_trivial_transitions _ (hG _ P.A P.isAb) (DVR.linComb_isLB _ P.isLB _ _) fun i j => ?_ show ∏ _ : PUnit.{1}, (_ : Γ(P.A.left, LB.wchart P.L (fun _ : PUnit.{1} => 𝟙 _) i ⊓ LB.wchart P.L (fun _ : PUnit.{1} => 𝟙 _) j)ˣ) ^ (0 : ℤ) = 1` and prove the remaining obligations. Simplify using `only [zpow_zero, Finset.prod_const_one]`. Simplify using `only [if_neg he.ne']`.

Conclude with `PowSec.exists_basis_sections hH K P e he`. Use `tendsto_const_nhds.congr' ?_ filter_upwards [Filter.eventually_gt_atTop 0] with e he` and prove the remaining obligations. Establish `: (e : ℝ) ^ P.g ≠ 0` using `pow_ne_zero _ (Nat.cast_ne_zero.2 he.ne')`. Rewrite using `[if_neg he.ne', Nat.cast_pow, div_self this]`.
-/
theorem vol_one [IsAlgClosed K] (hH : Out.GlobalSectionsRankAlgClosed) (hG : Out.GlobalFnsSt) (P : Out.PolAV (Sp K)) :
    Vol P.A.hom P.L P.g 1 := by
  refine ⟨fun e => if e = 0 then 1 else e ^ P.g, fun e => ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos e with rfl | he
    · refine sectionsFiniteDimension_one_trivial_transitions _ (hG _ P.A P.isAb) (DVR.linComb_isLB _ P.isLB _ _) fun i j => ?_
      show ∏ _ : PUnit.{1}, (_ : Γ(P.A.left, LB.wchart P.L (fun _ : PUnit.{1} => 𝟙 _) i ⊓
        LB.wchart P.L (fun _ : PUnit.{1} => 𝟙 _) j)ˣ) ^ (0 : ℤ) = 1
      simp only [zpow_zero, Finset.prod_const_one]
    · simp only [if_neg he.ne']
      exact PowSec.exists_basis_sections hH K P e he
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with e he
    have : (e : ℝ) ^ P.g ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 he.ne')
    rw [if_neg he.ne', Nat.cast_pow, div_self this]

/- English proof (translation)
Use `⟨inferInstance, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.comp_id]`. Conclude with `PolBaseChange.lbIso_refl (DVR.linComb_isLB _ P.isLB _ _)`.
-/
theorem formIs_id (P : Out.PolAV (Sp K)) : FormIs P P.L (𝟙 P.A) := by
  refine ⟨inferInstance, ?_⟩
  rw [Category.comp_id]
  exact PolBaseChange.lbIso_refl (DVR.linComb_isLB _ P.isLB _ _)

/- English proof (translation)
Take `⟨u, hu⟩` from `exists_gen_neg_of_sym hG P.isAb P.isLB P.sym`. Establish `le : ∀ j : (PUnit → P.L.ι) × P.L.ι, (P.L.pull (GrpObj.inv : P.A ⟶ P.A).left).U j.1 ⊓ P.L.U j.2 ≤ LB.wchart P.L (![(GrpObj.inv : P.A ⟶ P.A).left, 𝟙 P.A.left] : Fin 2 → _) ![j.1 PUnit.unit, j.2]` using `fun j y hy => Set.mem_iInter.2 fun k => by fin_cases k exacts [Set.mem_iInter.1 hy.1 PUnit.unit, hy.2]`. Use `gen_chartPull (h := 𝟙 _) (A' := LB.div (P.L.pull (GrpObj.inv : P.A ⟶ P.A).left) P.L) (A := LB.LinComb P.L (K := Fin 2) ![(GrpObj.inv : P.A ⟶ P.A).left, 𝟙 P.A.left] ![1, -1]) ⟨fun j => ![j.1 PUnit.unit, j.2], le, fun y j j' hj hj' => ?_⟩ u hu` and prove the remaining obligations. Use `(gm_div P.L (P.L.pull (GrpObj.inv : P.A ⟶ P.A).left) (𝟙 _) y j j' ⟨hj, hj'⟩).trans (Eq.trans ?_ (gm_linComb P.L _ _ (𝟙 _) y _ _ (le j hj) (le j' hj')).symm)` and prove the remaining obligations. Use `Eq.trans (congrArg₂ (· * ·) ?_ ?_) (Fin.prod_univ_two _).symm` and prove the remaining obligations.

Conclude with `(gm_pull_g P.L _ _ y j.1 j'.1 hj.1 hj'.1).trans (zpow_one _).symm`. Conclude with `(zpow_neg_one _).symm`.
-/
theorem symB (hG : Out.GlobalFnsSt) (P : Out.PolAV (Sp K)) : SymB P.L := by
  obtain ⟨u, hu⟩ := exists_gen_neg_of_sym hG P.isAb P.isLB P.sym
  have le : ∀ j : (PUnit → P.L.ι) × P.L.ι, (P.L.pull (GrpObj.inv : P.A ⟶ P.A).left).U j.1 ⊓ P.L.U j.2 ≤
      LB.wchart P.L (![(GrpObj.inv : P.A ⟶ P.A).left, 𝟙 P.A.left] : Fin 2 → _) ![j.1 PUnit.unit, j.2] :=
    fun j y hy => Set.mem_iInter.2 fun k => by
      fin_cases k
      exacts [Set.mem_iInter.1 hy.1 PUnit.unit, hy.2]
  refine gen_chartPull (h := 𝟙 _) (A' := LB.div (P.L.pull (GrpObj.inv : P.A ⟶ P.A).left) P.L)
    (A := LB.LinComb P.L (K := Fin 2) ![(GrpObj.inv : P.A ⟶ P.A).left, 𝟙 P.A.left] ![1, -1])
    ⟨fun j => ![j.1 PUnit.unit, j.2], le, fun y j j' hj hj' => ?_⟩ u hu
  refine (gm_div P.L (P.L.pull (GrpObj.inv : P.A ⟶ P.A).left) (𝟙 _) y j j' ⟨hj, hj'⟩).trans
    (Eq.trans ?_ (gm_linComb P.L _ _ (𝟙 _) y _ _ (le j hj) (le j' hj')).symm)
  refine Eq.trans (congrArg₂ (· * ·) ?_ ?_) (Fin.prod_univ_two _).symm
  · exact (gm_pull_g P.L _ _ y j.1 j'.1 hj.1 hj'.1).trans (zpow_one _).symm
  · exact (zpow_neg_one _).symm

/- English proof (translation)
The claim follows from `MapDeg.id_one X`.
-/
theorem mapDeg_id (X : Scheme.{0}) : MapDeg (𝟙 X) 1 := MapDeg.id_one X

/- English proof (translation)
Establish `: NeZero k` using `⟨hk.ne'⟩`. Set `T : Subgroup G` to `(powMonoidHom k).ker`. Use `choose w hw hw' using fun x y : T => hW x y x.2 y.2`. Establish `wl : ∀ x x' y, w (x * x') y = w x y * w x' y` using `fun x x' y => (hw' _ _ _ (hmul _ _ _ _ _ (hw x y) (hw x' y))).symm`. Establish `ws : ∀ x y, w y x = (w x y)⁻¹` using `fun x y => (hw' _ _ _ (hsymm _ _ _ (hw x y))).symm`.

Establish `wr : ∀ x y y', w x (y * y') = w x y * w x y'` using `fun x y y' => by`. Rewrite using `[ws _ x, wl, mul_inv, ← ws, ← ws]`. Set `e : T →* T →* Rˣ` to `MonoidHom.mk' (fun x => MonoidHom.mk' (w x) (wr x)) fun x x' => MonoidHom.ext fun y => wl x x' y`. Take `⟨v, hv⟩` from `exists_stdSymp_of_alternating_pairing k g T R ze hk hz (fun x => Subtype.ext x.2) (fun d hd => by`. Rewrite using `[← hc d hd]`.

Use `Nat.card_congr ⟨fun x => ⟨x.1.1, congrArg Subtype.val x.2⟩, fun x => ⟨⟨x.1, ?_⟩, Subtype.ext x.2⟩, fun _ => rfl, fun _ => rfl⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `hd`. Use `show x.1 ^ _ = 1`. Rewrite using `[hc, pow_mul, x.2, one_pow]) e (fun x => (hw' _ _ _ (halt _ x.2)).symm)`. Use the proof step `(fun x hx => Subtype.ext (hnd _ x.2 fun y hy => by`.

Establish `h : w x ⟨y, hy⟩ = 1` using `hx ⟨y, hy⟩`. Conclude with `h ▸ hw x ⟨y, hy⟩))`. Establish `cm : ∀ a b : G, Commute a b` using `fun a b => _root_.mul_comm a b`. Establish `tor : ∀ i, (v i).1 ^ k = 1` using `fun i => (v i).2`. Establish `inj` using `LevelOfPairing.injective_comb cm hW hmul hz (fun i => (v i).1) tor (fun i j => (show w (v i) (v j) = _ from hv i j) ▸ hw _ _)`.

Use `⟨fun i => (v i).1, tor, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨c, hcy⟩` from `LevelOfPairing.surjective_comb cm hk.ne' _ tor (hc k dvd_rfl) inj y hy`. Use `⟨fun i => ((c i : ℕ) : ZMod k), ?_, fun c' hc' => ?_⟩` and prove the remaining obligations. Simplify `hcy` using `only [ZMod.val_cast_of_lt (c _).2]`. Use `inj (fun i => ⟨(c' i).val, ZMod.val_lt _⟩) c (hc'.trans hcy.symm)` as an intermediate fact.

Use function extensionality and compare the values at `i`. Rewrite using `[← this]`. Conclude with `(ZMod.natCast_zmod_val _).symm`.
-/
theorem exists_basis_of_pairing {k g : ℕ} (hk : 0 < k) {G R : Type} [CommGroup G] [CommRing R] [IsDomain R]
    (hc : ∀ d, d ∣ k → Nat.card {x : G // x ^ d = 1} = d ^ (2 * g)) {ze : Rˣ} (hz : IsPrimitiveRoot ze k)
    (W : G → G → Rˣ → Prop) (hW : ∀ x y, x ^ k = 1 → y ^ k = 1 → ∃! c, W x y c)
    (hmul : ∀ x x' y c c', W x y c → W x' y c' → W (x * x') y (c * c')) (halt : ∀ x, x ^ k = 1 → W x x 1)
    (hsymm : ∀ x y c, W x y c → W y x c⁻¹)
    (hnd : ∀ x, x ^ k = 1 → (∀ y, y ^ k = 1 → W x y 1) → x = 1) :
    ∃ v : Fin (2 * g) → G, (∀ i, v i ^ k = 1) ∧ ∀ y : G, y ^ k = 1 →
      ∃! c : Fin (2 * g) → ZMod k, (List.ofFn fun i => v i ^ (c i).val).prod = y := by
  have : NeZero k := ⟨hk.ne'⟩
  let T : Subgroup G := (powMonoidHom k).ker
  choose w hw hw' using fun x y : T => hW x y x.2 y.2
  have wl : ∀ x x' y, w (x * x') y = w x y * w x' y := fun x x' y =>
    (hw' _ _ _ (hmul _ _ _ _ _ (hw x y) (hw x' y))).symm
  have ws : ∀ x y, w y x = (w x y)⁻¹ := fun x y => (hw' _ _ _ (hsymm _ _ _ (hw x y))).symm
  have wr : ∀ x y y', w x (y * y') = w x y * w x y' := fun x y y' => by
    rw [ws _ x, wl, mul_inv, ← ws, ← ws]
  let e : T →* T →* Rˣ := MonoidHom.mk' (fun x => MonoidHom.mk' (w x) (wr x))
    fun x x' => MonoidHom.ext fun y => wl x x' y
  obtain ⟨v, hv⟩ := exists_stdSymp_of_alternating_pairing k g T R ze hk hz (fun x => Subtype.ext x.2)
    (fun d hd => by
      rw [← hc d hd]
      refine Nat.card_congr ⟨fun x => ⟨x.1.1, congrArg Subtype.val x.2⟩,
        fun x => ⟨⟨x.1, ?_⟩, Subtype.ext x.2⟩, fun _ => rfl, fun _ => rfl⟩
      obtain ⟨c, hc⟩ := hd
      show x.1 ^ _ = 1
      rw [hc, pow_mul, x.2, one_pow]) e (fun x => (hw' _ _ _ (halt _ x.2)).symm)
    (fun x hx => Subtype.ext (hnd _ x.2 fun y hy => by
      have h : w x ⟨y, hy⟩ = 1 := hx ⟨y, hy⟩
      exact h ▸ hw x ⟨y, hy⟩))
  have cm : ∀ a b : G, Commute a b := fun a b => _root_.mul_comm a b
  have tor : ∀ i, (v i).1 ^ k = 1 := fun i => (v i).2
  have inj := LevelOfPairing.injective_comb cm hW hmul hz (fun i => (v i).1) tor
    (fun i j => (show w (v i) (v j) = _ from hv i j) ▸ hw _ _)
  refine ⟨fun i => (v i).1, tor, fun y hy => ?_⟩
  obtain ⟨c, hcy⟩ := LevelOfPairing.surjective_comb cm hk.ne' _ tor (hc k dvd_rfl) inj y hy
  refine ⟨fun i => ((c i : ℕ) : ZMod k), ?_, fun c' hc' => ?_⟩
  · simpa only [ZMod.val_cast_of_lt (c _).2] using hcy
  · have := inj (fun i => ⟨(c' i).val, ZMod.val_lt _⟩) c (hc'.trans hcy.symm)
    funext i
    rw [← this]
    exact (ZMod.natCast_zmod_val _).symm

/- English proof (translation)
Use `P.isAb.comm` as an intermediate fact. Set `c : Γ(Sp K, ⊤) ≃+* K` to `(Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv`. Establish `: IsDomain Γ(Sp K, ⊤)` using `c.toMulEquiv.isDomain _`. Establish `hk0 : k ≠ 0` using `fun e => hk (by rw [e, Nat.cast_zero])`. Establish `: NeZero (k : K)` using `⟨hk⟩`.

Establish `: NeZero k` using `⟨hk0⟩`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot K k`. Establish `hζ' : IsPrimitiveRoot (c.symm ζ) k` using `hζ.map_of_injective c.symm.injective`. Take `⟨w₁, w₂, w₃, -⟩` from `hL.weil _ P k (Out.baseOver _)`. Use `Exists.imp (fun pt h => ⟨Nat.pos_of_ne_zero hk0, h⟩) ?_` and prove the remaining obligations.

Conclude with `exists_basis_of_pairing (G := Out.baseOver _ ⟶ P.A) (g := P.g) (Nat.pos_of_ne_zero hk0) (fun d hd => (hL.mulN _ P d (Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hk0))).2.2.2.2 K (𝟙 _) (by`. Take `⟨e, rfl⟩` from `hd`. Rewrite `hk` using `[Nat.cast_mul]`. Conclude with `left_ne_zero_of_mul hk))`. Use the proof step `(hζ'.isUnit_unit hk0) (fun x y c => Out.WeilIs P.A P.L k x y c) w₁ w₂ w₃`.

Use the proof step `(fun _ _ _ h => CommPairing.weilIs_symm P.isLB h) (hL.weilNondeg K P _ hk)`.
-/
theorem exists_torsBasis [IsAlgClosed K] (hL : Out.Laws) (P : Out.PolAV (Sp K)) (k : ℕ) (hk : (k : K) ≠ 0) :
    ∃ pt : Fin (2 * P.g) → (Out.baseOver (Sp K) ⟶ P.A), TorsBasis P.A k pt := by
  have := P.isAb.comm
  let c : Γ(Sp K, ⊤) ≃+* K := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  have : IsDomain Γ(Sp K, ⊤) := c.toMulEquiv.isDomain _
  have hk0 : k ≠ 0 := fun e => hk (by rw [e, Nat.cast_zero])
  have : NeZero (k : K) := ⟨hk⟩
  have : NeZero k := ⟨hk0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K k
  have hζ' : IsPrimitiveRoot (c.symm ζ) k := hζ.map_of_injective c.symm.injective
  obtain ⟨w₁, w₂, w₃, -⟩ := hL.weil _ P k (Out.baseOver _)
  refine Exists.imp (fun pt h => ⟨Nat.pos_of_ne_zero hk0, h⟩) ?_
  exact exists_basis_of_pairing (G := Out.baseOver _ ⟶ P.A) (g := P.g) (Nat.pos_of_ne_zero hk0)
    (fun d hd => (hL.mulN _ P d (Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hk0))).2.2.2.2 K (𝟙 _) (by
      obtain ⟨e, rfl⟩ := hd
      rw [Nat.cast_mul] at hk
      exact left_ne_zero_of_mul hk))
    (hζ'.isUnit_unit hk0) (fun x y c => Out.WeilIs P.A P.L k x y c) w₁ w₂ w₃
    (fun _ _ _ h => CommPairing.weilIs_symm P.isLB h) (hL.weilNondeg K P _ hk)

/- English proof (translation)
Use `P.isAb.comm` as an intermediate fact. Use `⟨hk0, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[Category.comp_id, Out.linComb, List.prod_ofFn, Finset.prod_eq_single i (fun b _ hb => by`. Rewrite using `[Matrix.one_apply_ne hb, ZMod.val_zero, pow_zero]) (fun h => absurd (Finset.mem_univ _) h),`. Use the proof step `Matrix.one_apply_eq, ZMod.val_one'' hk, pow_one]`.
-/
theorem actsBy_id (P : Out.PolAV (Sp K)) {k m : ℕ} (hk0 : 0 < k) (hk : k ≠ 1) (pt : Fin m → (Out.baseOver (Sp K) ⟶ P.A)) :
    ActsBy pt (𝟙 P.A) (1 : Matrix _ _ (ZMod k)) := by
  have := P.isAb.comm
  refine ⟨hk0, fun i => ?_⟩
  rw [Category.comp_id, Out.linComb, List.prod_ofFn, Finset.prod_eq_single i (fun b _ hb => by
    rw [Matrix.one_apply_ne hb, ZMod.val_zero, pow_zero]) (fun h => absurd (Finset.mem_univ _) h),
    Matrix.one_apply_eq, ZMod.val_one'' hk, pow_one]

end GlobalTheory.PrincipalNumerics

open GlobalTheory.PrincipalNumerics in

/- English proof (translation)
Introduce `hL _ K _ _ P`. Use `⟨vol_one hL.globalSectionsRank hL.globalFns P, formIs_id P, symB hL.globalFns P, mapDeg_id _, GlobalTheory.veryAmple_lbPow hL.ample K P 4 le_rfl, fun k hk => ?_⟩` and prove the remaining obligations. Take `⟨pt, hpt⟩` from `exists_torsBasis hL P k hk`. Conclude with `⟨pt, hpt, fun h => actsBy_id P hpt.pos h pt⟩`.
-/
theorem GlobalTheory.principal_polarisation_numerics : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)), Vol P.A.hom P.L P.g 1 ∧ FormIs P P.L (𝟙 P.A) ∧ SymB P.L ∧ MapDeg (𝟙 P.A.left) 1 ∧ (∃ (m : ℕ) (th : Fin (m + 1) → (lbPow P.L 4).Sec), VAmp P.A.hom (lbPow P.L 4) th) ∧ ∀ k : ℕ, (k : K) ≠ 0 → ∃ pt : Fin (2 * P.g) → (Out.baseOver (Sp K) ⟶ P.A), TorsBasis P.A k pt ∧ (k ≠ 1 → ActsBy pt (𝟙 P.A) (1 : Matrix _ _ (ZMod k))) := by
  intro hL _ K _ _ P
  refine ⟨vol_one hL.globalSectionsRank hL.globalFns P, formIs_id P, symB hL.globalFns P, mapDeg_id _,
    GlobalTheory.veryAmple_lbPow hL.ample K P 4 le_rfl, fun k hk => ?_⟩
  obtain ⟨pt, hpt⟩ := exists_torsBasis hL P k hk
  exact ⟨pt, hpt, fun h => actsBy_id P hpt.pos h pt⟩

end
