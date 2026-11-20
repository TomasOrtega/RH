import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RigidIsoCube

/- English proof (translation)
Establish `: IsSchemeTheoreticallyDominant q` using `IsSchemeTheoreticallyDominant.of_isPullback h.flip`. Establish `: QuasiCompact q` using `MorphismProperty.of_isPullback h.flip ‹_›`. Establish `inj : Function.Injective q.appTop.hom` using `q.app_injective ⊤`. Establish `cmp : ∀ {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (x : Γ(C, ⊤)), f.appTop.hom (g.appTop.hom x) = (f ≫ g).appTop.hom x` using `fun f g x => by`. Rewrite using `[Scheme.Hom.comp_appTop]`.

Both sides reduce to the same expression. Introduce `a`. Take `⟨c, hc⟩` from `hs (q.appTop.hom a)`. Set `e' : S' ⟶ Y'` to `h.lift (j ≫ e) (𝟙 _) (by rw [Category.assoc, he, Category.comp_id, Category.id_comp])`. Establish `h₁ : e' ≫ q = j ≫ e` using `h.lift_fst _ _ _`.

Establish `h₂ : e' ≫ p' = 𝟙 _` using `h.lift_snd _ _ _`. Establish `hc' : c = j.appTop.hom (e.appTop.hom a)`. Use `congrArg e'.appTop.hom hc` as an intermediate fact. Rewrite `this` using `[cmp, cmp, h₁, h₂, Scheme.Hom.id_appTop]`. Rewrite using `[cmp]`.

Conclude with `this`. Use `⟨e.appTop.hom a, inj ?_⟩` and prove the remaining obligations. Rewrite using `[← hc, hc', cmp q p, cmp p' j, h.w]`.
-/
theorem surjective_appTop_of_baseChange {Y S Y' S' : Scheme.{0}} {q : Y' ⟶ Y} {p' : Y' ⟶ S'} {p : Y ⟶ S} {j : S' ⟶ S}
    (h : IsPullback q p' p j) [Flat p] [QuasiCompact j] [IsSchemeTheoreticallyDominant j] (e : S ⟶ Y) (he : e ≫ p = 𝟙 _)
    (hs : Function.Surjective p'.appTop.hom) : Function.Surjective p.appTop.hom := by
  have : IsSchemeTheoreticallyDominant q := IsSchemeTheoreticallyDominant.of_isPullback h.flip
  have : QuasiCompact q := MorphismProperty.of_isPullback h.flip ‹_›
  have inj : Function.Injective q.appTop.hom := q.app_injective ⊤
  have cmp : ∀ {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (x : Γ(C, ⊤)),
      f.appTop.hom (g.appTop.hom x) = (f ≫ g).appTop.hom x := fun f g x => by
    rw [Scheme.Hom.comp_appTop]; rfl
  intro a
  obtain ⟨c, hc⟩ := hs (q.appTop.hom a)
  let e' : S' ⟶ Y' := h.lift (j ≫ e) (𝟙 _) (by rw [Category.assoc, he, Category.comp_id, Category.id_comp])
  have h₁ : e' ≫ q = j ≫ e := h.lift_fst _ _ _
  have h₂ : e' ≫ p' = 𝟙 _ := h.lift_snd _ _ _
  have hc' : c = j.appTop.hom (e.appTop.hom a) := by
    have := congrArg e'.appTop.hom hc
    rw [cmp, cmp, h₁, h₂, Scheme.Hom.id_appTop] at this
    rw [cmp]; exact this
  refine ⟨e.appTop.hom a, inj ?_⟩
  rw [← hc, hc', cmp q p, cmp p' j, h.w]

/- English proof (translation)
Set `T' : Over S'` to `Over.mk (pullback.snd T.hom k)`. Establish `: IsSchemeTheoreticallyDominant (pullback.fst T.hom k)` using `IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback T.hom k).flip`. Establish `big : IsPullback (pullback.fst A.hom T'.hom ≫ g) (pullback.snd A.hom T'.hom) G.hom (pullback.fst T.hom k ≫ T.hom)`. Rewrite using `[pullback.condition]`. Conclude with `(IsPullback.of_hasPullback A.hom T'.hom).paste_horiz hg`.

Establish `sq : IsPullback (pullback.lift (pullback.fst A.hom T'.hom ≫ g) (pullback.snd A.hom T'.hom ≫ pullback.fst T.hom k) (by rw [big.w, Category.assoc])) (pullback.snd A.hom T'.hom) (pullback.snd G.hom T.hom) (pullback.fst T.hom k)` using `IsPullback.of_right (by rw [pullback.lift_fst]; exact big) (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback G.hom T.hom)`. Establish `: Flat (snd G T).left` using `inferInstanceAs (Flat (pullback.snd G.hom T.hom))`. Use `surjective_appTop_of_baseChange (p := (snd G T).left) sq (lift (1 : T ⟶ G) (𝟙 T)).left ?_ (surj_snd hG hA T')` and prove the remaining obligations. Conclude with `congrArg (fun q => q.left) (lift_snd (1 : T ⟶ G) (𝟙 T))`.
-/
theorem surjective_snd_of_generic (hG : GlobalFnsSt) {S S' : Scheme.{0}} (k : S' ⟶ S) [QuasiCompact k]
    [IsSchemeTheoreticallyDominant k] (G : Over S) [GrpObj G] [Flat G.hom] {A : Over S'} [GrpObj A]
    (hA : IsAbelianScheme A) {g : A.left ⟶ G.left} (hg : IsPullback g A.hom G.hom k) (T : Over S) [Flat T.hom] :
    Function.Surjective (snd G T).left.appTop.hom := by
  let T' : Over S' := Over.mk (pullback.snd T.hom k)
  have : IsSchemeTheoreticallyDominant (pullback.fst T.hom k) :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback T.hom k).flip
  have big : IsPullback (pullback.fst A.hom T'.hom ≫ g) (pullback.snd A.hom T'.hom) G.hom
      (pullback.fst T.hom k ≫ T.hom) := by
    rw [pullback.condition]
    exact (IsPullback.of_hasPullback A.hom T'.hom).paste_horiz hg
  have sq : IsPullback (pullback.lift (pullback.fst A.hom T'.hom ≫ g) (pullback.snd A.hom T'.hom ≫ pullback.fst T.hom k)
      (by rw [big.w, Category.assoc])) (pullback.snd A.hom T'.hom) (pullback.snd G.hom T.hom) (pullback.fst T.hom k) :=
    IsPullback.of_right (by rw [pullback.lift_fst]; exact big) (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback G.hom T.hom)
  have : Flat (snd G T).left := inferInstanceAs (Flat (pullback.snd G.hom T.hom))
  refine surjective_appTop_of_baseChange (p := (snd G T).left) sq (lift (1 : T ⟶ G) (𝟙 T)).left ?_ (surj_snd hG hA T')
  exact congrArg (fun q => q.left) (lift_snd (1 : T ⟶ G) (𝟙 T))

/- English proof (translation)
Take `rfl : φ = fun k => φ' k ≫ F` from `funext fun k => (hψ k).symm`. Take `⟨t₁, ht₁, hv⟩` from `exists_up hw hL hL' a ha`. Establish `key` using `gen_unique hL p e he hp ht ht₁ (fun y J hJ => by choose J' hJ' using fun ψ : S₀ ⟶ X' => exists_chart hL' (ψ y)`. Establish `v` using `hv _ e y _ _ (Good.mem hJ _ e) (Good.mem hJ' _ e)`. Use `(h y J J' hJ hJ').trans (Eq.trans (congrArg₂ (· * ·) ?_ rfl) v.symm)` and prove the remaining obligations.

Simplify using `only [pw, Category.assoc])`. Introduce `Z r z i q hi hq`. Rewrite using `[Category.comp_id]`. Establish `hi' : r z ∈ LB.wchart L (fun k => φ' k ≫ F) i` using `Set.mem_iInter.2 hi`. Use `choose J hJ using fun ψ : Z ⟶ X => exists_chart hL (ψ z)`.

Conclude with `((gen_trans ht r z hi' (Good.mem hJ _ r)).trans ((congrArg _ (key Z r z J hJ)).trans (gen_trans ht₁ r z hi' (Good.mem hJ _ r)).symm)).trans (hv Z r z i q hi' (Set.mem_iInter.2 hq))`.
-/
theorem pmaps_of_section {X X' Y S₀ : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
    {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {φ' : K → (Y ⟶ X')}
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen) (t : LB.Gen (LB.LinComb L φ ε))
    (ht : t.IsGen) (hψ : ∀ k, φ' k ≫ F = φ k) (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _)
    (hp : Function.Surjective p.appTop.hom)
    (h : ∀ (y : S₀) J J', Good L y J → Good L' y J' → val t e y J =
      (∏ k, gw w (e ≫ φ' k) y (J ((e ≫ φ' k) ≫ F)) (J' (e ≫ φ' k)) ^ ε k) * val a e y J') :
    PMaps w φ' φ ε a t (𝟙 Y) := by
  obtain rfl : φ = fun k => φ' k ≫ F := funext fun k => (hψ k).symm
  obtain ⟨t₁, ht₁, hv⟩ := exists_up hw hL hL' a ha
  have key := gen_unique hL p e he hp ht ht₁ (fun y J hJ => by
    choose J' hJ' using fun ψ : S₀ ⟶ X' => exists_chart hL' (ψ y)
    have v := hv _ e y _ _ (Good.mem hJ _ e) (Good.mem hJ' _ e)
    refine (h y J J' hJ hJ').trans (Eq.trans (congrArg₂ (· * ·) ?_ rfl) v.symm)
    simp only [pw, Category.assoc])
  intro Z r z i q hi hq
  rw [Category.comp_id]
  have hi' : r z ∈ LB.wchart L (fun k => φ' k ≫ F) i := Set.mem_iInter.2 hi
  choose J hJ using fun ψ : Z ⟶ X => exists_chart hL (ψ z)
  exact ((gen_trans ht r z hi' (Good.mem hJ _ r)).trans ((congrArg _ (key Z r z J hJ)).trans
    (gen_trans ht₁ r z hi' (Good.mem hJ _ r)).symm)).trans (hv Z r z i q hi' (Set.mem_iInter.2 hq))

end GlobalTheory.RigidIsoCube

namespace GlobalTheory

open RigidIsoCube in

/- English proof (translation)
Introduce `hG R _ _ _ I _ D D' A A' G _ _ _ U U' wL _ hw _`. Use `U.smooth` as an intermediate fact. Establish `: IsDominant (jK R)` using `⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩`. Use `IsSchemeTheoreticallyDominant.of_isDominant (jK R)` as an intermediate fact. Establish `hg : IsPullback (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) A.A.hom G.hom (jK R)`.

Establish `: IsIso U.gen.inv.left` using `inferInstanceAs (IsIso ((Over.forget _).map U.gen.inv))`. Establish `s : IsPullback U.gen.inv.left A.A.hom (pullback.snd G.hom (jK R)) (𝟙 _)` using `IsPullback.of_horiz_isIso ⟨(Over.w U.gen.inv).trans (Category.comp_id _).symm⟩`. Simplify using `using s.paste_horiz (IsPullback.of_hasPullback G.hom (jK R))`. Establish `s₁ : Function.Surjective G.hom.appTop.hom` using `surjective_appTop_of_baseChange hg (eSec G) (Over.w η[G]) (hG _ _ A.isAb).2`. Establish `: Flat (G ⊗ G).hom` using `by rw [Over.tensorObj_hom]; infer_instance`.

Establish `sj : Function.Surjective ((snd G (G ⊗ G)).left ≫ (snd G G).left ≫ G.hom).appTop.hom` using `surj_comp (surjective_snd_of_generic hG (jK R) G A.isAb hg _) (surj_comp (surjective_snd_of_generic hG (jK R) G A.isAb hg _) s₁)`. Establish `pg` using `(isGen_iff wL).1 hw`. Prove the components needed by the constructor for the conclusion. Set `e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G3 G` to `lift 1 (lift 1 1)`. Establish `he : e.left ≫ (snd G (G ⊗ G)).left ≫ (snd G G).left ≫ G.hom = 𝟙 _`.

Rewrite using `[Over.w, Over.w]`. Conclude with `Over.w e`. Use `pmaps_of_section pg U.LG.isLB U'.LG.isLB (φ' := thφ G (x3 G)) (φ := thφ G (x3 G)) (ε := thε) U'.cubG.t U'.cubG.isGen U.cubG.t U.cubG.isGen (fun _ => Category.comp_id _) _ e.left he sj fun y J J' hJ hJ' => ?_` and prove the remaining obligations. Establish `p` using `prod_cub (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G) 1 1 (fun q => gw wL q y (J (q ≫ 𝟙 _)) (J' q))`. Rewrite `p` using `[_root_.mul_one, _root_.mul_one]`.

Use `((isCub_cubV U.cubG hJ).face 1 1).trans (Eq.trans ?_ (congrArg₂ (· * ·) p ((isCub_cubV U'.cubG hJ').face 1 1)).symm)` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `oi : eSec G ≫ (ι[G]).left = eSec G`. Establish `: η[G] ≫ ι[G] = η[G]` using `by simp`. Conclude with `congrArg (fun q => q.left) this`.

Use `pmaps_of_section pg U.LG.isLB U'.LG.isLB U'.symG U'.symG_gen U.symG U.symG_gen (fun _ => Category.comp_id _) G.hom (eSec G) (Over.w η[G]) s₁ fun y J J' hJ hJ' => ?_` and prove the remaining obligations. Establish `a` using `val_corr hJ U.symG_rig (𝟙 _)`. Rewrite `a` using `[val_pull hJ, val_one, Category.id_comp]`. Establish `b` using `val_corr hJ' U'.symG_rig (𝟙 _)`. Rewrite `b` using `[val_pull hJ', val_one, Category.id_comp]`.

Rewrite using `[a, b, Fin.prod_univ_two]`. Use `show 1 = gw wL (eSec G ≫ (ι[G]).left) y (J ((eSec G ≫ (ι[G]).left) ≫ 𝟙 _)) (J' (eSec G ≫ (ι[G]).left)) ^ (1 : ℤ) * gw wL (eSec G ≫ 𝟙 _) y (J ((eSec G ≫ 𝟙 _) ≫ 𝟙 _)) (J' (eSec G ≫ 𝟙 _)) ^ (-1 : ℤ) * 1`. Simplify using `only [oi, Category.comp_id]`. Simplify using the standard rewrite rules.
-/
theorem rigidified_iso_respects_cube_and_symmetry : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G) (wL : LB.Iso U'.LG.L (U.LG.L.pull (𝟙 G.left))) (he : eSec G ≫ 𝟙 G.left = 𝟙 _ ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G) (fun _ => 1)) U'.LG.rig (rigPullOf (𝟙 G.left) (𝟙 _) he U.LG.L U.LG.rig) → (Geo.Tor.PMaps wL (thφ G (x3 G)) (thφ G (x3 G)) thε U'.cubG.t U.cubG.t (𝟙 _) ∧ Geo.Tor.PMaps wL (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![(ι[G]).left, 𝟙 G.left] ![1, -1] U'.symG U.symG (𝟙 G.left)) := by
  intro hG R _ _ _ I _ D D' A A' G _ _ _ U U' wL _ hw _
  have := U.smooth
  have : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have hg : IsPullback (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) A.A.hom G.hom (jK R) := by
    have : IsIso U.gen.inv.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.inv))
    have s : IsPullback U.gen.inv.left A.A.hom (pullback.snd G.hom (jK R)) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨(Over.w U.gen.inv).trans (Category.comp_id _).symm⟩
    simpa using s.paste_horiz (IsPullback.of_hasPullback G.hom (jK R))
  have s₁ : Function.Surjective G.hom.appTop.hom :=
    surjective_appTop_of_baseChange hg (eSec G) (Over.w η[G]) (hG _ _ A.isAb).2
  have : Flat (G ⊗ G).hom := by rw [Over.tensorObj_hom]; infer_instance
  have sj : Function.Surjective ((snd G (G ⊗ G)).left ≫ (snd G G).left ≫ G.hom).appTop.hom :=
    surj_comp (surjective_snd_of_generic hG (jK R) G A.isAb hg _)
      (surj_comp (surjective_snd_of_generic hG (jK R) G A.isAb hg _) s₁)
  have pg := (isGen_iff wL).1 hw
  constructor
  · let e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G3 G := lift 1 (lift 1 1)
    have he : e.left ≫ (snd G (G ⊗ G)).left ≫ (snd G G).left ≫ G.hom = 𝟙 _ := by
      rw [Over.w, Over.w]; exact Over.w e
    refine pmaps_of_section pg U.LG.isLB U'.LG.isLB (φ' := thφ G (x3 G)) (φ := thφ G (x3 G)) (ε := thε)
      U'.cubG.t U'.cubG.isGen U.cubG.t U.cubG.isGen (fun _ => Category.comp_id _) _ e.left he sj fun y J J' hJ hJ' => ?_
    have p := prod_cub (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G) 1 1
      (fun q => gw wL q y (J (q ≫ 𝟙 _)) (J' q))
    rw [_root_.mul_one, _root_.mul_one] at p
    refine ((isCub_cubV U.cubG hJ).face 1 1).trans
      (Eq.trans ?_ (congrArg₂ (· * ·) p ((isCub_cubV U'.cubG hJ').face 1 1)).symm)
    simp
  · have oi : eSec G ≫ (ι[G]).left = eSec G := by
      have : η[G] ≫ ι[G] = η[G] := by simp
      exact congrArg (fun q => q.left) this
    refine pmaps_of_section pg U.LG.isLB U'.LG.isLB U'.symG U'.symG_gen U.symG U.symG_gen
      (fun _ => Category.comp_id _) G.hom (eSec G) (Over.w η[G]) s₁ fun y J J' hJ hJ' => ?_
    have a := val_corr hJ U.symG_rig (𝟙 _)
    rw [val_pull hJ, val_one, Category.id_comp] at a
    have b := val_corr hJ' U'.symG_rig (𝟙 _)
    rw [val_pull hJ', val_one, Category.id_comp] at b
    rw [a, b, Fin.prod_univ_two]
    show 1 = gw wL (eSec G ≫ (ι[G]).left) y (J ((eSec G ≫ (ι[G]).left) ≫ 𝟙 _)) (J' (eSec G ≫ (ι[G]).left)) ^ (1 : ℤ) *
      gw wL (eSec G ≫ 𝟙 _) y (J ((eSec G ≫ 𝟙 _) ≫ 𝟙 _)) (J' (eSec G ≫ 𝟙 _)) ^ (-1 : ℤ) * 1
    simp only [oi, Category.comp_id]
    simp

end GlobalTheory
