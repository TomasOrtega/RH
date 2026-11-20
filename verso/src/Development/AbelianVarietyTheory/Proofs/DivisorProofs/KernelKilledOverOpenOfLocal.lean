import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerKilledOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.KerKilledLocal

open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [pullU, Scheme.Hom.comp_app, Units.coe_map]`. Both sides reduce to the same expression.
-/
theorem pullU_comp' {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (U : X.Opens) (x : Γ(X, U)ˣ) :
    pullU (f ≫ g) U x = pullU f (g ⁻¹ᵁ U) (pullU g U x) := by
  apply Units.ext
  simp only [pullU, Scheme.Hom.comp_app, Units.coe_map]
  rfl

/- English proof (translation)
Take `⟨t, ht⟩` from `hg`. Establish `h1 : ∃ t : LB.Gen (((L.pull a).pull b).pull h), t.IsGen` using `⟨LB.genPull _ t h, LB.isGen_genPull _ t ht h⟩`. Establish `hb : ∀ z : Z', a.base (b.base (h.base z)) = c.base (e.base z)` using `fun z => by`. Use `congrArg (fun φ => φ.base z) heq` as an intermediate fact. Simplify using `using this`.

Establish `hmem : ∀ (j : PUnit.{1} → PUnit.{1} → L.ι) (z : Z'), z ∈ ((L.pull c).pull e).U j → z ∈ (((L.pull a).pull b).pull h).U (fun _ => j)`. Introduce `j z hz`. Establish `h1` using `(mem_wchart_pu L c _ _).1 ((mem_wchart_pu (L.pull c) e j z).1 hz)`. Apply `(mem_wchart_pu ((L.pull a).pull b) h _ z).2` to reduce the goal to its premises. Apply `(mem_wchart_pu (L.pull a) b j _).2` to reduce the goal to its premises.

Apply `(mem_wchart_pu L a _ _).2` to reduce the goal to its premises. Rewrite using `[hb z]`. Conclude with `h1`. Use `exists_gen_transfer (L := ((L.pull a).pull b).pull h) (L' := (L.pull c).pull e) (fun j => fun _ => j) (fun j z hz => hmem j z hz) ?_ h1` and prove the remaining obligations. Introduce `i j y hy`.

Establish `hy1 : y ∈ (e ≫ c) ⁻¹ᵁ (L.U (i PUnit.unit PUnit.unit) ⊓ L.U (j PUnit.unit PUnit.unit))` using `pull_inf_le L c _ _ (pull_inf_le (L.pull c) e i j hy)`. Establish `hy2 : y ∈ (h ≫ b ≫ a) ⁻¹ᵁ (L.U (i PUnit.unit PUnit.unit) ⊓ L.U (j PUnit.unit PUnit.unit))`. Rewrite using `[heq]`. Conclude with `hy1`. Establish `hm : y ∈ h ⁻¹ᵁ (((L.pull a).pull b).U i ⊓ ((L.pull a).pull b).U j)` using `pull_inf_le ((L.pull a).pull b) h (fun _ => i) (fun _ => j) ⟨hmem i y hy.1, hmem j y hy.2⟩`.

Establish `hy' : h.base y ∈ (b ≫ a) ⁻¹ᵁ (L.U (i PUnit.unit PUnit.unit) ⊓ L.U (j PUnit.unit PUnit.unit))` using `hy2`. Use `(germ_pull_pull L c e i j y hy hy1).trans ((gU_pullU_congr heq.symm _ _ y hy1 hy2).trans ?_)` and prove the remaining obligations. Use `Eq.trans ?_ (germ_pull ((L.pull a).pull b) h (fun _ => i) (fun _ => j) y _ hm).symm` and prove the remaining obligations. Establish `hy3 : y ∈ h ⁻¹ᵁ ((b ≫ a) ⁻¹ᵁ (L.U (i PUnit.unit PUnit.unit) ⊓ L.U (j PUnit.unit PUnit.unit)))` using `hy2`. Rewrite using `[gU_pullU h _ y hm, germ_pull_pull L a b i j (h.base y) hm hy', ← gU_pullU h _ y hy3]`.

Use `erw [pullU_comp']`. Both sides reduce to the same expression.
-/
theorem gen_pull3 {X Y Z Z' Y' : Scheme.{0}} (L : LB X) (a : Y ⟶ X) (b : Z ⟶ Y) (h : Z' ⟶ Z)
    (c : Y' ⟶ X) (e : Z' ⟶ Y') (heq : h ≫ b ≫ a = e ≫ c)
    (hg : ∃ t : LB.Gen ((L.pull a).pull b), t.IsGen) : ∃ t : LB.Gen ((L.pull c).pull e), t.IsGen := by
  obtain ⟨t, ht⟩ := hg
  have h1 : ∃ t : LB.Gen (((L.pull a).pull b).pull h), t.IsGen :=
    ⟨LB.genPull _ t h, LB.isGen_genPull _ t ht h⟩
  have hb : ∀ z : Z', a.base (b.base (h.base z)) = c.base (e.base z) := fun z => by
    have := congrArg (fun φ => φ.base z) heq
    simpa using this
  have hmem : ∀ (j : PUnit.{1} → PUnit.{1} → L.ι) (z : Z'), z ∈ ((L.pull c).pull e).U j →
      z ∈ (((L.pull a).pull b).pull h).U (fun _ => j) := by
    intro j z hz
    have h1 := (mem_wchart_pu L c _ _).1 ((mem_wchart_pu (L.pull c) e j z).1 hz)
    apply (mem_wchart_pu ((L.pull a).pull b) h _ z).2
    apply (mem_wchart_pu (L.pull a) b j _).2
    apply (mem_wchart_pu L a _ _).2
    rw [hb z]
    exact h1
  refine exists_gen_transfer (L := ((L.pull a).pull b).pull h) (L' := (L.pull c).pull e)
    (fun j => fun _ => j) (fun j z hz => hmem j z hz) ?_ h1
  intro i j y hy
  have hy1 : y ∈ (e ≫ c) ⁻¹ᵁ (L.U (i PUnit.unit PUnit.unit) ⊓ L.U (j PUnit.unit PUnit.unit)) :=
    pull_inf_le L c _ _ (pull_inf_le (L.pull c) e i j hy)
  have hy2 : y ∈ (h ≫ b ≫ a) ⁻¹ᵁ (L.U (i PUnit.unit PUnit.unit) ⊓ L.U (j PUnit.unit PUnit.unit)) := by
    rw [heq]; exact hy1
  have hm : y ∈ h ⁻¹ᵁ (((L.pull a).pull b).U i ⊓ ((L.pull a).pull b).U j) :=
    pull_inf_le ((L.pull a).pull b) h (fun _ => i) (fun _ => j) ⟨hmem i y hy.1, hmem j y hy.2⟩
  have hy' : h.base y ∈ (b ≫ a) ⁻¹ᵁ (L.U (i PUnit.unit PUnit.unit) ⊓ L.U (j PUnit.unit PUnit.unit)) := hy2
  refine (germ_pull_pull L c e i j y hy hy1).trans ((gU_pullU_congr heq.symm _ _ y hy1 hy2).trans ?_)
  refine Eq.trans ?_ (germ_pull ((L.pull a).pull b) h (fun _ => i) (fun _ => j) y _ hm).symm
  have hy3 : y ∈ h ⁻¹ᵁ ((b ≫ a) ⁻¹ᵁ (L.U (i PUnit.unit PUnit.unit) ⊓ L.U (j PUnit.unit PUnit.unit))) := hy2
  rw [gU_pullU h _ y hm, germ_pull_pull L a b i j (h.base y) hm hy', ← gU_pullU h _ y hy3]
  erw [pullU_comp']
  rfl

end GlobalTheory.KerKilledLocal

namespace GlobalTheory.KerKilledLocal

open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison

noncomputable section Grp

variable {S' : Scheme.{0}} (G : Over S') [GrpObj G] [IsCommMonObj G]

/- English proof (translation)
Rewrite using `[← Over.comp_left, lift_fst]`.
-/
theorem lift_left_fst' {S : Scheme.{0}} {T X Y : Over S} (a : T ⟶ X) (b : T ⟶ Y) :
    (lift a b).left ≫ (fst X Y).left = a.left := by
  rw [← Over.comp_left, lift_fst]

/- English proof (translation)
Rewrite using `[← Over.comp_left, lift_snd]`.
-/
theorem lift_left_snd' {S : Scheme.{0}} {T X Y : Over S} (a : T ⟶ X) (b : T ⟶ Y) :
    (lift a b).left ≫ (snd X Y).left = b.left := by
  rw [← Over.comp_left, lift_snd]

/- English proof (translation)
Rewrite using `[← Category.assoc, lift_left_fst']`.
-/
theorem lift_left_fst'_assoc {S : Scheme.{0}} {T X Y : Over S} (a : T ⟶ X) (b : T ⟶ Y) {Q : Scheme.{0}}
    (q : X.left ⟶ Q) : (lift a b).left ≫ (fst X Y).left ≫ q = a.left ≫ q := by
  rw [← Category.assoc, lift_left_fst']

/- English proof (translation)
Rewrite using `[← Category.assoc, lift_left_snd']`.
-/
theorem lift_left_snd'_assoc {S : Scheme.{0}} {T X Y : Over S} (a : T ⟶ X) (b : T ⟶ Y) {Q : Scheme.{0}}
    (q : Y.left ⟶ Q) : (lift a b).left ≫ (snd X Y).left ≫ q = b.left ≫ q := by
  rw [← Category.assoc, lift_left_snd']

def down (V : S'.Opens) {T : Over V.toScheme} (x : T ⟶ (Over.pullback V.ι).obj G) :
    Over.mk (T.hom ≫ V.ι) ⟶ G :=
  Over.homMk (x.left ≫ pullback.fst G.hom V.ι) (by
    have wx : x.left ≫ pullback.snd G.hom V.ι = T.hom := Over.w x
    change (x.left ≫ pullback.fst G.hom V.ι) ≫ G.hom = T.hom ≫ V.ι
    rw [Category.assoc, pullback.condition, ← Category.assoc, wx])

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Conclude with `((isGrpPullback V.ι G).2 T x y (down G V x) (down G V y) rfl rfl).symm`.
-/
theorem down_mul (V : S'.Opens) {T : Over V.toScheme} (x y : T ⟶ (Over.pullback V.ι).obj G) :
    down G V (x * y) = down G V x * down G V y := by
  apply Over.OverMorphism.ext
  exact ((isGrpPullback V.ι G).2 T x y (down G V x) (down G V y) rfl rfl).symm

/- English proof (translation)
Establish `h1 : x.left ≫ pullback.fst G.hom V.ι = y.left ≫ pullback.fst G.hom V.ι` using `congrArg CommaMorphism.left h`. Establish `wx : x.left ≫ pullback.snd G.hom V.ι = T.hom` using `Over.w x`. Establish `wy : y.left ≫ pullback.snd G.hom V.ι = T.hom` using `Over.w y`. Conclude with `Over.OverMorphism.ext (pullback.hom_ext h1 (wx.trans wy.symm))`.
-/
theorem down_injective (V : S'.Opens) {T : Over V.toScheme} (x y : T ⟶ (Over.pullback V.ι).obj G)
    (h : down G V x = down G V y) : x = y := by
  have h1 : x.left ≫ pullback.fst G.hom V.ι = y.left ≫ pullback.fst G.hom V.ι :=
    congrArg CommaMorphism.left h
  have wx : x.left ≫ pullback.snd G.hom V.ι = T.hom := Over.w x
  have wy : y.left ≫ pullback.snd G.hom V.ι = T.hom := Over.w y
  exact Over.OverMorphism.ext (pullback.hom_ext h1 (wx.trans wy.symm))

/- English proof (translation)
Establish `h` using `down_mul G V (1 : T ⟶ (Over.pullback V.ι).obj G) 1`. Rewrite `h` using `[_root_.mul_one]`. Conclude with `mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)`.
-/
theorem down_one (V : S'.Opens) {T : Over V.toScheme} :
    down G V (1 : T ⟶ (Over.pullback V.ι).obj G) = 1 := by
  have h := down_mul G V (1 : T ⟶ (Over.pullback V.ι).obj G) 1
  rw [_root_.mul_one] at h
  exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero, pow_zero, down_one]`. Consider the case `succ n ih => rw [pow_succ, pow_succ, down_mul, ih]`.
-/
theorem down_pow (V : S'.Opens) {T : Over V.toScheme} (x : T ⟶ (Over.pullback V.ι).obj G) (n : ℕ) :
    down G V (x ^ n) = down G V x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, down_one]
  | succ n ih => rw [pow_succ, pow_succ, down_mul, ih]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero, pow_zero, MonObj.comp_one]`. Consider the case `succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]`.
-/
theorem comp_pow_pt {A B : Over S'} (f : A ⟶ B) (g : B ⟶ G) (n : ℕ) : f ≫ g ^ n = (f ≫ g) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

end Grp

end GlobalTheory.KerKilledLocal

namespace GlobalTheory.KerKilledLocal

open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison GlobalTheory.KerKilledLocus

noncomputable section Main

variable {S' : Scheme.{0}} (G : Over S') [GrpObj G] [IsCommMonObj G]

/- English proof (translation)
Use `set U : T.left.Opens := (T.hom ≫ W.ι) ⁻¹ᵁ V with hU`. Establish `hr : Set.range (U.ι ≫ T.hom ≫ W.ι) ⊆ Set.range V.ι`. Introduce and unpack `_ ⟨u, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `u.2`.

Use `set k := IsOpenImmersion.lift V.ι (U.ι ≫ T.hom ≫ W.ι) hr with hkdef`. Establish `hk : k ≫ V.ι = U.ι ≫ T.hom ≫ W.ι` using `IsOpenImmersion.lift_fac _ _ _`. Set `Tp : Over V.toScheme` to `Over.mk k`. Establish `wx : x.left ≫ pullback.snd G.hom W.ι = T.hom` using `Over.w x`. Set `xp : Tp ⟶ (Over.pullback V.ι).obj G` to `Over.homMk (pullback.lift (U.ι ≫ x.left ≫ pullback.fst G.hom W.ι) k (by`.

Rewrite using `[hk, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc x.left, wx]))`. Use the proof step `(pullback.lift_snd _ _ _)`. Set `ρ : Over.mk (Tp.hom ≫ V.ι) ⟶ Over.mk (T.hom ≫ W.ι)` to `Over.homMk U.ι hk.symm`. Establish `hρ : ρ ≫ down G W x = down G V xp`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `U.ι ≫ x.left ≫ pullback.fst G.hom W.ι = pullback.lift _ _ _ ≫ pullback.fst G.hom V.ι`. Rewrite using `[pullback.lift_fst]`. Set `GW` to `(Over.pullback W.ι).obj G`. Set `GV` to `(Over.pullback V.ι).obj G`. Set `bz : (GV ⊗ Tp).left ⟶ T.left` to `(snd GV Tp).left ≫ U.ι`.

Set `Z' : Over W.toScheme` to `Over.mk (bz ≫ T.hom)`. Set `v : Z' ⟶ T` to `Over.homMk bz rfl`. Establish `e1 : (fst GV Tp).left ≫ pullback.snd G.hom V.ι = (GV ⊗ Tp).hom` using `Over.w (fst GV Tp)`. Establish `e2 : (snd GV Tp).left ≫ k = (GV ⊗ Tp).hom` using `Over.w (snd GV Tp)`. Set `u : Z' ⟶ GW` to `Over.homMk (pullback.lift ((fst GV Tp).left ≫ pullback.fst G.hom V.ι) (bz ≫ T.hom) (by`.

Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, e1, ← e2, Category.assoc, hk]`. Simplify using `only [bz, Category.assoc]))`. Use the proof step `(pullback.lift_snd _ _ _)`. Establish `heq : (lift u v).left ≫ (lift (snd GW T ≫ x) (fst GW T)).left ≫ pφ₂ W.ι G = (lift (snd GV Tp ≫ xp) (fst GV Tp)).left ≫ pφ₂ V.ι G`. Apply `adelic_GL2_ext_of_local_components G` to reduce the goal to its premises.

Simplify using `only [Category.assoc, pφ₂_fst]`. Rewrite using `[lift_left_fst'_assoc, lift_left_fst'_assoc]`. Simplify using `only [Over.comp_left, Category.assoc]`. Rewrite using `[lift_left_snd'_assoc]`. Express the relevant statement in the definitionally equal form `bz ≫ x.left ≫ pullback.fst G.hom W.ι = (snd GV Tp).left ≫ pullback.lift _ _ _ ≫ pullback.fst G.hom V.ι`.

Rewrite using `[pullback.lift_fst]`. Simplify using `only [bz, Category.assoc]`. Simplify using `only [Category.assoc, pφ₂_snd]`. Rewrite using `[lift_left_snd'_assoc, lift_left_snd'_assoc, lift_left_fst'_assoc]`. Express the relevant statement in the definitionally equal form `pullback.lift _ _ _ ≫ pullback.fst G.hom W.ι = _`.

Rewrite using `[pullback.lift_fst]`. Both sides reduce to the same expression. Establish `hgen` using `GlobalTheory.KerKilledLocal.gen_pull3 P (pφ₂ W.ι G) _ (lift u v).left (pφ₂ V.ι G) _ heq hs`. Establish `hxp : xp ^ d = 1` using `hV Tp xp hgen`. Establish `key : ρ ≫ down G W x ^ d = ρ ≫ 1`.

Rewrite using `[comp_pow_pt, hρ, ← down_pow, hxp, down_one, MonObj.comp_one]`. Conclude with `congrArg CommaMorphism.left key`.
-/
theorem step (d : ℕ) (P : LB (G2 G).left) (V W : S'.Opens) (hV : KerKilledOn d G P V)
    (T : Over W.toScheme) (x : T ⟶ (Over.pullback W.ι).obj G)
    (hs : ∃ s : ((P.pull (pφ₂ W.ι G)).pull
        (lift (snd ((Over.pullback W.ι).obj G) T ≫ x) (fst ((Over.pullback W.ι).obj G) T)).left).Gen,
        s.IsGen) :
    ((T.hom ≫ W.ι) ⁻¹ᵁ V).ι ≫ (down G W x ^ d).left =
      ((T.hom ≫ W.ι) ⁻¹ᵁ V).ι ≫ (1 : Over.mk (T.hom ≫ W.ι) ⟶ G).left := by
  set U : T.left.Opens := (T.hom ≫ W.ι) ⁻¹ᵁ V with hU
  have hr : Set.range (U.ι ≫ T.hom ≫ W.ι) ⊆ Set.range V.ι := by
    rintro _ ⟨u, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact u.2
  set k := IsOpenImmersion.lift V.ι (U.ι ≫ T.hom ≫ W.ι) hr with hkdef
  have hk : k ≫ V.ι = U.ι ≫ T.hom ≫ W.ι := IsOpenImmersion.lift_fac _ _ _
  let Tp : Over V.toScheme := Over.mk k
  have wx : x.left ≫ pullback.snd G.hom W.ι = T.hom := Over.w x
  let xp : Tp ⟶ (Over.pullback V.ι).obj G :=
    Over.homMk (pullback.lift (U.ι ≫ x.left ≫ pullback.fst G.hom W.ι) k (by
      rw [hk, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc x.left, wx]))
      (pullback.lift_snd _ _ _)
  let ρ : Over.mk (Tp.hom ≫ V.ι) ⟶ Over.mk (T.hom ≫ W.ι) := Over.homMk U.ι hk.symm
  have hρ : ρ ≫ down G W x = down G V xp := by
    apply Over.OverMorphism.ext
    change U.ι ≫ x.left ≫ pullback.fst G.hom W.ι = pullback.lift _ _ _ ≫ pullback.fst G.hom V.ι
    rw [pullback.lift_fst]

  let GW := (Over.pullback W.ι).obj G
  let GV := (Over.pullback V.ι).obj G
  let bz : (GV ⊗ Tp).left ⟶ T.left := (snd GV Tp).left ≫ U.ι
  let Z' : Over W.toScheme := Over.mk (bz ≫ T.hom)
  let v : Z' ⟶ T := Over.homMk bz rfl
  have e1 : (fst GV Tp).left ≫ pullback.snd G.hom V.ι = (GV ⊗ Tp).hom := Over.w (fst GV Tp)
  have e2 : (snd GV Tp).left ≫ k = (GV ⊗ Tp).hom := Over.w (snd GV Tp)
  let u : Z' ⟶ GW :=
    Over.homMk (pullback.lift ((fst GV Tp).left ≫ pullback.fst G.hom V.ι) (bz ≫ T.hom) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, e1, ← e2, Category.assoc, hk]
      simp only [bz, Category.assoc]))
      (pullback.lift_snd _ _ _)
  have heq : (lift u v).left ≫ (lift (snd GW T ≫ x) (fst GW T)).left ≫ pφ₂ W.ι G =
      (lift (snd GV Tp ≫ xp) (fst GV Tp)).left ≫ pφ₂ V.ι G := by
    apply adelic_GL2_ext_of_local_components G
    · simp only [Category.assoc, pφ₂_fst]
      rw [lift_left_fst'_assoc, lift_left_fst'_assoc]
      simp only [Over.comp_left, Category.assoc]
      rw [lift_left_snd'_assoc]
      change bz ≫ x.left ≫ pullback.fst G.hom W.ι = (snd GV Tp).left ≫ pullback.lift _ _ _ ≫ pullback.fst G.hom V.ι
      rw [pullback.lift_fst]
      simp only [bz, Category.assoc]
    · simp only [Category.assoc, pφ₂_snd]
      rw [lift_left_snd'_assoc, lift_left_snd'_assoc, lift_left_fst'_assoc]
      change pullback.lift _ _ _ ≫ pullback.fst G.hom W.ι = _
      rw [pullback.lift_fst]
      rfl
  have hgen := GlobalTheory.KerKilledLocal.gen_pull3 P (pφ₂ W.ι G) _ (lift u v).left (pφ₂ V.ι G) _ heq hs
  have hxp : xp ^ d = 1 := hV Tp xp hgen
  have key : ρ ≫ down G W x ^ d = ρ ≫ 1 := by
    rw [comp_pow_pt, hρ, ← down_pow, hxp, down_one, MonObj.comp_one]
  exact congrArg CommaMorphism.left key

end Main

end GlobalTheory.KerKilledLocal

namespace GlobalTheory.KerKilledLocal

open GlobalTheory.KerKilledLocus

/- English proof (translation)
Introduce `d S' G _ _ P W hloc T x hs`. Apply `down_injective G W` to reduce the goal to its premises. Rewrite using `[down_pow, down_one]`. Establish `hmem : ∀ t : T.left, (T.hom ≫ W.ι) t ∈ W` using `fun t => by`. Establish `h : (T.hom ≫ W.ι) t ∈ Set.range W.ι` using `⟨T.hom t, by simp⟩`.

Rewrite `h` using `[Scheme.Opens.range_ι]`. Then use the resulting hypothesis. Use `choose V hpV hV using fun t : T.left => hloc _ (hmem t)`. Set `U : T.left → T.left.Opens` to `fun t => (T.hom ≫ W.ι) ⁻¹ᵁ V t`. Establish `hc : TopologicalSpace.IsOpenCover U`. Rewrite using `[TopologicalSpace.IsOpenCover, eq_top_iff]`.

Conclude with `fun t _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨t, hpV t⟩`. Use `Over.OverMorphism.ext ((T.left.openCoverOfIsOpenCover U hc).hom_ext _ _ fun t => ?_)` and prove the remaining obligations. Conclude with `step G d P (V t) W (hV t) T x hs`.
-/
theorem kerKilledOn_of_local : ∀ (d : ℕ) (S' : Scheme.{0}) (G : Over S') [GrpObj G] [IsCommMonObj G]
    (P : LB (G2 G).left) (W : S'.Opens),
    (∀ p ∈ W, ∃ V : S'.Opens, p ∈ V ∧ GlobalTheory.KerKilledLocus.KerKilledOn d G P V) →
      GlobalTheory.KerKilledLocus.KerKilledOn d G P W := by
  intro d S' G _ _ P W hloc T x hs
  apply down_injective G W
  rw [down_pow, down_one]
  have hmem : ∀ t : T.left, (T.hom ≫ W.ι) t ∈ W := fun t => by
    have h : (T.hom ≫ W.ι) t ∈ Set.range W.ι := ⟨T.hom t, by simp⟩
    rwa [Scheme.Opens.range_ι] at h
  choose V hpV hV using fun t : T.left => hloc _ (hmem t)
  let U : T.left → T.left.Opens := fun t => (T.hom ≫ W.ι) ⁻¹ᵁ V t
  have hc : TopologicalSpace.IsOpenCover U := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    exact fun t _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨t, hpV t⟩
  refine Over.OverMorphism.ext ((T.left.openCoverOfIsOpenCover U hc).hom_ext _ _ fun t => ?_)
  exact step G d P (V t) W (hV t) T x hs

end GlobalTheory.KerKilledLocal
