import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePointsCycAway
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIffEighthPowerPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectEighthPowerPrincipalSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisedE8ThetaPowerOverModuli
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelLevelLoweringQuotientRepresentsReduced
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.SiegLev GlobalTheory.SiegLevCalc GlobalTheory.SiegelPullComp GlobalTheory.SiegelPull
open ReciprocityTheory.ChartRestriction.G GlobalTheory.CechPic

noncomputable section

namespace GlobalTheory.SiegLift

/- English proof (translation)
Introduce `g n N B _ ζ k _ _ s c b ho hN3 hc hg`. Establish `hL` using `GlobalTheory.abelianSchemeLaws_all.1`. Establish `hG` using `hL.globalFns`. Establish `hD : c.diag.IsLB` using `pull_isLB c.isLB _`. Establish `hN : ((N : ℕ) : k) ≠ 0` using `b.unit.ne_zero`.

Establish `hN₀ : N ≠ 0` using `fun e => hN (by rw [e, Nat.cast_zero])`. Establish `hz : IsPrimitiveRoot b.ζ N` using `IsPrimitiveRoot.coe_units_iff.1 (b.prim k (RingHom.id k))`. Establish `hz₂ : IsPrimitiveRoot (b.ζ ^ 2) N` using `hz.pow_of_coprime 2 (Nat.coprime_two_left.2 ho)`. Establish `card` using `GlobalTheory.card_torsion_geometricPoint_of_field GlobalTheory.card_torsion_abelianVariety _ c.A c.ab g hg`. Take `⟨L, hLM, ⟨cu⟩⟩` from `GlobalTheory.Moduli.cubicalStr_of_triv_theta hL _ c.A c.ab c.diag hD (DVR.exists_gen_of_isLB_local (V := k) _ (pull_isLB hD _)) (GlobalTheory.exists_gen_theta_of_isAbelianScheme k c.A c.ab _ hD)`.

Establish `toW : ∀ {m : ℕ} {T : Over (Sp k)} {x y : T ⟶ c.A} {u}, UU.CubWeil cu m x y u → Out.WeilIs c.A c.diag m x y u` using `fun H => hLM ▸ (UU.cubWeil_iff_weilIs hG c.ab H.1 H.2.1 _).1 H`. Take `⟨f₁, f₂, f₃⟩` from `(GlobalTheory.ChF.exists_gen_theta_tensor_and_finite_flat_surjective_pow k c.A c.diag c.P c.ab hD hc.1 c.isLB).2 N (Nat.pos_of_ne_zero hN₀)`. Set `H : Subgroup (𝟙_ (Over (Sp k)) ⟶ c.A)` to `(powMonoidHom N).ker`. Establish `hH : ∀ x : H, x.1 ^ N = 1` using `fun x => x.2`. Establish `ex : ∀ x y : H, ∃ u : kˣ, UU.CubWeil cu N x.1 y.1 (unitOn u)` using `fun x y => by`.

Take `⟨u, hu, -⟩` from `UU.existsUnique_cubWeil cu (hH x) (hH y)`. Take `⟨w, rfl⟩ : ∃ w : kˣ, unitOn w = u` from `⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.toMonoidHom u, Units.ext (CommRingCat.inv_hom_apply (Scheme.ΓSpecIso (CommRingCat.of k)) u.val)⟩`. Conclude with `⟨w, hu⟩`. Use `choose w hw using ex`. Establish `uq : ∀ x y u, UU.CubWeil cu N x.1 y.1 (unitOn u) → w x y = u` using `fun x y u H => SiegelOfPolarised.unitOn_inj ((hw x y).unique H)`.

Establish `l : ∀ x x' y, w (x * x') y = w x y * w x' y` using `fun x x' y => uq _ _ _ (by`. Use `(hw x y).mul_left (hw x' y)` as an intermediate fact. Unfold `unitOn at this ⊢`. Rewrite using `[map_mul])` and apply the resulting hypothesis. Establish `sk : ∀ x y, w y x = (w x y)⁻¹` using `fun x y => uq _ _ _ (by`.

Use `(hw x y).symm` as an intermediate fact. Unfold `unitOn at this ⊢`. Rewrite using `[map_inv])` and apply the resulting hypothesis. Establish `u1 : unitOn (1 : kˣ) = 1` using `map_one _`. Set `e : H →* H →* kˣ` to `MonoidHom.mk' (fun x => MonoidHom.mk' (w x) fun y y' => by`.

Rewrite using `[sk (y * y'), l, mul_inv, ← sk, ← sk]) fun x x' => MonoidHom.ext fun y => l x x' y`. Take `⟨l₁, add₁, w₁⟩` from `exists_symplectic_hom (g := g) (Nat.pos_of_ne_zero hN₀) hz₂ (fun x => Subtype.ext (hH x)) (fun m hm => by`. Take `⟨r, hr⟩` from `hm`. Establish `hm : (m : k) ≠ 0` using `left_ne_zero_of_mul (by rwa [hr, Nat.cast_mul] at hN)`. Use `Eq.trans (Nat.card_congr ?_) (card k (𝟙 _) m hm)` and prove the remaining obligations.

Conclude with `⟨fun x => ⟨x.1.1, congrArg Subtype.val x.2⟩, fun x => ⟨⟨x.1, show x.1 ^ N = 1 by`. Rewrite using `[hr, pow_mul, x.2, one_pow]⟩, Subtype.ext x.2⟩, fun _ => rfl, fun _ => rfl⟩)`. Use `e (fun x => uq _ _ _ (u1 ▸ UU.cubWeil_self cu (hH x))) (fun x hx => Subtype.ext (by`. Establish `t` using `GlobalTheory.CubNondeg.main hL _ c.A c.ab L cu k (𝟙 _) N hN f₁ f₂ f₃ x.1 (hH x) fun y hy => by`. Use `hw x ⟨y, hy⟩` as an intermediate fact.

Rewrite `this` using `[show w x ⟨y, hy⟩ = 1 from hx ⟨y, hy⟩, u1]`. Then use the resulting hypothesis. Rewrite `t` using `[hLM]`. Establish `s₂ : x.1 ^ 2 = 1` using `sq_eq_one_of_translDiff c hc (𝟙 _) x.1 t`. Conclude with `(pow_eq_one_iff_of_coprime (Nat.coprime_two_left.2 ho)).1 ⟨s₂, hH x⟩))`. Set `l₂ : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp k)) ⟶ c.A)` to `fun a => (l₁ a).1`.

Establish `add₂ : ∀ a a', l₂ (a + a') = l₂ a * l₂ a'` using `fun a a' => congrArg Subtype.val (add₁ a a')`. Establish `tors₂ : ∀ a, l₂ a ^ N = 1` using `fun a => hH _`. Establish `w₂ : ∀ a a', UU.CubWeil cu N (l₂ a) (l₂ a') (unitOn ((b.ζ ^ 2) ^ omegaStd a a'))` using `fun a a' => (show w (l₁ a) (l₁ a') = _ from w₁ a a') ▸ hw (l₁ a) (l₁ a')`. Establish `mk : ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (x : Sp k' ⟶ Sp k) (β : k →+* k') (z : k'ˣ), x ≫ 𝟙 _ = spMap β → (z : k') = β b.ζ → (∀ a, (toUnit (Over.mk x) ≫ l₂ a = 1 ↔ ∃ v, a = N • v)) ∧ (∀ y : Over.mk x ⟶ c.A, y ^ N = 1 → ∃ a, toUnit _ ≫ l₂ a = y) ∧ ∀ a a', Out.WeilIs c.A c.di …`. Introduce `k' _ _ x β z hx hzz`.

Take `rfl : x = spMap β` from `(Category.comp_id _).symm.trans hx`. Take `rfl : z = Units.map β.toMonoidHom b.ζ` from `Units.ext hzz`. Establish `hz' : IsPrimitiveRoot (Units.map β.toMonoidHom (b.ζ ^ 2)) N` using `hz₂.map_of_injective (Units.map_injective β.injective)`. Establish `hk' : ((N : ℕ) : k') ≠ 0` using `by rw [← map_natCast β]; exact (map_ne_zero β).2 hN`. Establish `W : ∀ a a', UU.CubWeil cu N (toUnit (Over.mk (spMap β)) ≫ l₂ a) (toUnit _ ≫ l₂ a') (unitOn (Units.map β.toMonoidHom (b.ζ ^ 2) ^ omegaStd a a'))` using `fun a a' => by`.

Establish `H` using `(w₂ a a').comp (toUnit (Over.mk (spMap β)))`. Establish `e : Units.map (toUnit (Over.mk (spMap β))).left.appTop.hom.toMonoidHom (unitOn ((b.ζ ^ 2) ^ omegaStd a a')) = unitOn (Units.map β.toMonoidHom ((b.ζ ^ 2) ^ omegaStd a a'))` using `Units.ext (congrArg (fun q => q.hom ((b.ζ ^ 2) ^ omegaStd a a').val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm`. Rewrite `H` using `[e, map_zpow]`. Conclude with `H`. Establish `ker : ∀ a, toUnit (Over.mk (spMap β)) ≫ l₂ a = 1 → ∃ v, a = N • v` using `fun a ha => SiegelOfPolarised.exists_smul_of_dvd fun a' => by`.

Establish `w₁` using `W a a'`. Rewrite `w₁` using `[ha]`. Establish `e` using `SiegelOfPolarised.unitOn_inj ((w₁.unique (UU.cubWeil_one_left cu w₁.2.1)).trans (map_one _).symm)`. Conclude with `(hz'.zpow_eq_one_iff_dvd _).1 e`. Use `⟨fun a => ⟨ker a, ?_⟩, SiegelOfPolarised.onto_torsion hN₀ _ (fun a b => by rw [add₂, MonObj.comp_mul]) (fun a => by rw [← MonObj.comp_pow, tors₂, MonObj.comp_one]) ker ?_, fun a a' => ?_⟩` and prove the remaining obligations.

Introduce and unpack `⟨v, rfl⟩`. Establish `pw : ∀ m : ℕ, l₂ (m • v) = l₂ v ^ m` using `fun m => by`. Proceed by induction on `m with`. Consider the case `zero => rw [zero_smul, pow_zero]; exact mul_eq_left.1 ((add₂ 0 0).symm.trans (by rw [add_zero]))`. Consider the case `succ m ih => rw [succ_nsmul, add₂, ih, pow_succ]`.

Rewrite using `[pw, tors₂, MonObj.comp_one]`. Rewrite using `[card k' _ _ hk']`. Simplify using `[two_mul]`. Establish `H` using `toW (W a a')`. Rewrite `H` using `[map_pow, ← zpow_ofNat, ← zpow_mul]`. Then use the resulting hypothesis.

Use `⟨{ A := c.A ab := c.ab P := c.P isLB := c.isLB rig₁ := c.rig₁ rig₂ := c.rig₂` and prove the remaining obligations. Use symmetry as in `:= c.symm`. Use `lev := l₂`. Use `lev_add := add₂`. Use `lev_tors := tors₂`.

Use `geom := mk },`. Use `𝟙 _, @isGrpPullback_of_iso _ _ _ _ _ (Iso.refl c.A) (inferInstanceAs (IsMonHom (𝟙 c.A))),`. Use the proof step `⟨𝟙 _, ⟨by simp, by simp⟩, ?_⟩, fun a => ?_⟩`. Conclude with `(CechPic.cls_eq_iff c.isLB (pull_isLB c.isLB _)).1 ((CechPic.pull_id _).symm.trans (CechPic.cls_pull c.isLB _ _).symm)`. Simplify using the standard rewrite rules.
-/
theorem exists_level_of_forget : ∀ (g n N : ℕ) (B : Type) [CommRing B] (ζ : B) (K : Type) [Field K] [IsAlgClosed K]
    (s : Sp K ⟶ Sp B) (c : SiegPre g n ζ s) (b : TBase K N), Odd N → 3 ≤ N → c.Principal →
    SmoothOfRelativeDimension g c.A.hom → ∃ C : SiegPre g N (b.ζ : K) (𝟙 (Sp K)), SRel C c 0 0 (𝟙 _) := by
  intro g n N B _ ζ k _ _ s c b ho hN3 hc hg
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  have hG := hL.globalFns
  have hD : c.diag.IsLB := pull_isLB c.isLB _
  have hN : ((N : ℕ) : k) ≠ 0 := b.unit.ne_zero
  have hN₀ : N ≠ 0 := fun e => hN (by rw [e, Nat.cast_zero])
  have hz : IsPrimitiveRoot b.ζ N := IsPrimitiveRoot.coe_units_iff.1 (b.prim k (RingHom.id k))
  have hz₂ : IsPrimitiveRoot (b.ζ ^ 2) N := hz.pow_of_coprime 2 (Nat.coprime_two_left.2 ho)
  have card := GlobalTheory.card_torsion_geometricPoint_of_field GlobalTheory.card_torsion_abelianVariety _ c.A c.ab g hg

  obtain ⟨L, hLM, ⟨cu⟩⟩ := GlobalTheory.Moduli.cubicalStr_of_triv_theta hL _ c.A c.ab c.diag hD
    (DVR.exists_gen_of_isLB_local (V := k) _ (pull_isLB hD _))
    (GlobalTheory.exists_gen_theta_of_isAbelianScheme k c.A c.ab _ hD)
  have toW : ∀ {m : ℕ} {T : Over (Sp k)} {x y : T ⟶ c.A} {u}, UU.CubWeil cu m x y u →
      Out.WeilIs c.A c.diag m x y u := fun H => hLM ▸ (UU.cubWeil_iff_weilIs hG c.ab H.1 H.2.1 _).1 H
  obtain ⟨f₁, f₂, f₃⟩ := (GlobalTheory.ChF.exists_gen_theta_tensor_and_finite_flat_surjective_pow k c.A c.diag c.P c.ab
    hD hc.1 c.isLB).2 N (Nat.pos_of_ne_zero hN₀)
  let H : Subgroup (𝟙_ (Over (Sp k)) ⟶ c.A) := (powMonoidHom N).ker
  have hH : ∀ x : H, x.1 ^ N = 1 := fun x => x.2
  have ex : ∀ x y : H, ∃ u : kˣ, UU.CubWeil cu N x.1 y.1 (unitOn u) := fun x y => by
    obtain ⟨u, hu, -⟩ := UU.existsUnique_cubWeil cu (hH x) (hH y)
    obtain ⟨w, rfl⟩ : ∃ w : kˣ, unitOn w = u :=
      ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.toMonoidHom u,
        Units.ext (CommRingCat.inv_hom_apply (Scheme.ΓSpecIso (CommRingCat.of k)) u.val)⟩
    exact ⟨w, hu⟩
  choose w hw using ex
  have uq : ∀ x y u, UU.CubWeil cu N x.1 y.1 (unitOn u) → w x y = u := fun x y u H =>
    SiegelOfPolarised.unitOn_inj ((hw x y).unique H)
  have l : ∀ x x' y, w (x * x') y = w x y * w x' y := fun x x' y => uq _ _ _ (by
    have := (hw x y).mul_left (hw x' y)
    unfold unitOn at this ⊢
    rwa [map_mul])
  have sk : ∀ x y, w y x = (w x y)⁻¹ := fun x y => uq _ _ _ (by
    have := (hw x y).symm
    unfold unitOn at this ⊢
    rwa [map_inv])
  have u1 : unitOn (1 : kˣ) = 1 := map_one _
  let e : H →* H →* kˣ := MonoidHom.mk' (fun x => MonoidHom.mk' (w x) fun y y' => by
    rw [sk (y * y'), l, mul_inv, ← sk, ← sk]) fun x x' => MonoidHom.ext fun y => l x x' y
  obtain ⟨l₁, add₁, w₁⟩ := exists_symplectic_hom (g := g) (Nat.pos_of_ne_zero hN₀) hz₂
    (fun x => Subtype.ext (hH x)) (fun m hm => by
      obtain ⟨r, hr⟩ := hm
      have hm : (m : k) ≠ 0 := left_ne_zero_of_mul (by rwa [hr, Nat.cast_mul] at hN)
      refine Eq.trans (Nat.card_congr ?_) (card k (𝟙 _) m hm)
      exact ⟨fun x => ⟨x.1.1, congrArg Subtype.val x.2⟩, fun x => ⟨⟨x.1, show x.1 ^ N = 1 by
        rw [hr, pow_mul, x.2, one_pow]⟩, Subtype.ext x.2⟩, fun _ => rfl, fun _ => rfl⟩)
    e (fun x => uq _ _ _ (u1 ▸ UU.cubWeil_self cu (hH x))) (fun x hx => Subtype.ext (by
      have t := GlobalTheory.CubNondeg.main hL _ c.A c.ab L cu k (𝟙 _) N hN f₁ f₂ f₃ x.1 (hH x) fun y hy => by
        have := hw x ⟨y, hy⟩
        rwa [show w x ⟨y, hy⟩ = 1 from hx ⟨y, hy⟩, u1] at this
      rw [hLM] at t
      have s₂ : x.1 ^ 2 = 1 := sq_eq_one_of_translDiff c hc (𝟙 _) x.1 t
      exact (pow_eq_one_iff_of_coprime (Nat.coprime_two_left.2 ho)).1 ⟨s₂, hH x⟩))
  let l₂ : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp k)) ⟶ c.A) := fun a => (l₁ a).1
  have add₂ : ∀ a a', l₂ (a + a') = l₂ a * l₂ a' := fun a a' => congrArg Subtype.val (add₁ a a')
  have tors₂ : ∀ a, l₂ a ^ N = 1 := fun a => hH _
  have w₂ : ∀ a a', UU.CubWeil cu N (l₂ a) (l₂ a') (unitOn ((b.ζ ^ 2) ^ omegaStd a a')) := fun a a' =>
    (show w (l₁ a) (l₁ a') = _ from w₁ a a') ▸ hw (l₁ a) (l₁ a')

  have mk : ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (x : Sp k' ⟶ Sp k) (β : k →+* k') (z : k'ˣ),
        x ≫ 𝟙 _ = spMap β → (z : k') = β b.ζ →
        (∀ a, (toUnit (Over.mk x) ≫ l₂ a = 1 ↔ ∃ v, a = N • v)) ∧
        (∀ y : Over.mk x ⟶ c.A, y ^ N = 1 → ∃ a, toUnit _ ≫ l₂ a = y) ∧
        ∀ a a', Out.WeilIs c.A c.diag (N : ℕ) (toUnit (Over.mk x) ≫ l₂ a) (toUnit _ ≫ l₂ a')
          (unitOn (z ^ (2 * omegaStd a a'))) := by
    intro k' _ _ x β z hx hzz
    obtain rfl : x = spMap β := (Category.comp_id _).symm.trans hx
    obtain rfl : z = Units.map β.toMonoidHom b.ζ := Units.ext hzz
    have hz' : IsPrimitiveRoot (Units.map β.toMonoidHom (b.ζ ^ 2)) N :=
      hz₂.map_of_injective (Units.map_injective β.injective)
    have hk' : ((N : ℕ) : k') ≠ 0 := by rw [← map_natCast β]; exact (map_ne_zero β).2 hN
    have W : ∀ a a', UU.CubWeil cu N (toUnit (Over.mk (spMap β)) ≫ l₂ a) (toUnit _ ≫ l₂ a')
        (unitOn (Units.map β.toMonoidHom (b.ζ ^ 2) ^ omegaStd a a')) := fun a a' => by
      have H := (w₂ a a').comp (toUnit (Over.mk (spMap β)))
      have e : Units.map (toUnit (Over.mk (spMap β))).left.appTop.hom.toMonoidHom
          (unitOn ((b.ζ ^ 2) ^ omegaStd a a')) = unitOn (Units.map β.toMonoidHom ((b.ζ ^ 2) ^ omegaStd a a')) :=
        Units.ext (congrArg (fun q => q.hom ((b.ζ ^ 2) ^ omegaStd a a').val)
          (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm
      rw [e, map_zpow] at H
      exact H
    have ker : ∀ a, toUnit (Over.mk (spMap β)) ≫ l₂ a = 1 → ∃ v, a = N • v := fun a ha =>
      SiegelOfPolarised.exists_smul_of_dvd fun a' => by
        have w₁ := W a a'
        rw [ha] at w₁
        have e := SiegelOfPolarised.unitOn_inj
          ((w₁.unique (UU.cubWeil_one_left cu w₁.2.1)).trans (map_one _).symm)
        exact (hz'.zpow_eq_one_iff_dvd _).1 e
    refine ⟨fun a => ⟨ker a, ?_⟩, SiegelOfPolarised.onto_torsion hN₀ _ (fun a b => by rw [add₂, MonObj.comp_mul])
      (fun a => by rw [← MonObj.comp_pow, tors₂, MonObj.comp_one]) ker ?_, fun a a' => ?_⟩
    · rintro ⟨v, rfl⟩
      have pw : ∀ m : ℕ, l₂ (m • v) = l₂ v ^ m := fun m => by
        induction m with
        | zero => rw [zero_smul, pow_zero]; exact mul_eq_left.1 ((add₂ 0 0).symm.trans (by rw [add_zero]))
        | succ m ih => rw [succ_nsmul, add₂, ih, pow_succ]
      rw [pw, tors₂, MonObj.comp_one]
    · rw [card k' _ _ hk']
      simp [two_mul]
    · have H := toW (W a a')
      rwa [map_pow, ← zpow_ofNat, ← zpow_mul] at H
  refine ⟨{ A := c.A
            ab := c.ab
            P := c.P
            isLB := c.isLB
            rig₁ := c.rig₁
            rig₂ := c.rig₂
            symm := c.symm
            lev := l₂
            lev_add := add₂
            lev_tors := tors₂
            geom := mk },
    𝟙 _, @isGrpPullback_of_iso _ _ _ _ _ (Iso.refl c.A) (inferInstanceAs (IsMonHom (𝟙 c.A))),
    ⟨𝟙 _, ⟨by simp, by simp⟩, ?_⟩, fun a => ?_⟩
  · exact (CechPic.cls_eq_iff c.isLB (pull_isLB c.isLB _)).1
      ((CechPic.pull_id _).symm.trans (CechPic.cls_pull c.isLB _ _).symm)
  · simp

end GlobalTheory.SiegLift
