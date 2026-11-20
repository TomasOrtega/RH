import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

/- English proof (translation)
Take `⟨i', hi'⟩ : ∃ i' : Γ.G.left ⟶ pullback G.hom x, i' = pullback.lift i Γ.G.hom h.isOver` from `⟨_, rfl⟩`. Rewrite using `[← hi']`. Establish `i'fst : i' ≫ pullback.fst G.hom x = i` using `by rw [hi']; exact pullback.lift_fst _ _ _`. Establish `i'snd : i' ≫ pullback.snd G.hom x = Γ.G.hom` using `by rw [hi']; exact pullback.lift_snd _ _ _`. Set `PO : Over X` to `Over.mk (pullback.snd G.hom x ≫ x)`.

Set `u : PO ⟶ G` to `Over.homMk (pullback.fst G.hom x) pullback.condition`. Take `⟨f, hfdef⟩ : ∃ f : pullback G.hom x ⟶ G.left, f = (u ^ N).left` from `⟨_, rfl⟩`. Take `⟨g, hgdef⟩ : ∃ g : pullback G.hom x ⟶ G.left, g = (1 : PO ⟶ G).left` from `⟨_, rfl⟩`. Establish `hf : f ≫ G.hom = pullback.snd G.hom x ≫ x` using `by rw [hfdef]; exact Over.w (u ^ N)`. Establish `hg : g ≫ G.hom = pullback.snd G.hom x ≫ x` using `by rw [hgdef]; exact Over.w (1 : PO ⟶ G)`.

Establish `hfg : f ≫ G.hom = g ≫ G.hom` using `hf.trans hg.symm`. Set `jq : pullback (pullback.diagonal G.hom) (pullback.lift f g hfg) ⟶ pullback G.hom x` to `pullback.snd _ _`. Use `haveI : IsClosedImmersion jq := inferInstance`. Establish `l1 : pullback.lift f g hfg ≫ pullback.fst G.hom G.hom = f` using `pullback.lift_fst _ _ _`. Establish `l2 : pullback.lift f g hfg ≫ pullback.snd G.hom G.hom = g` using `pullback.lift_snd _ _ _`.

Establish `cond` using `pullback.condition (f := pullback.diagonal G.hom) (g := pullback.lift f g hfg)`. Establish `jqf : jq ≫ f = pullback.fst _ _`. Use `congrArg (· ≫ pullback.fst G.hom G.hom) cond` as an intermediate fact. Simplify `this.symm` using `[jq, l1]`. Establish `jqg : jq ≫ g = pullback.fst _ _`.

Use `congrArg (· ≫ pullback.snd G.hom G.hom) cond` as an intermediate fact. Simplify `this.symm` using `[jq, l2]`. Establish `jqeq : jq ≫ f = jq ≫ g` using `jqf.trans jqg.symm`. Establish `key : i' ≫ f = i' ≫ g`. Set `g₀ : Over.mk (Γ.G.hom ≫ x) ⟶ G` to `Over.homMk i h.isOver`.

Establish `h0 : g₀ ^ N = 1` using `(h.kernel Γ.G g₀).2 ⟨𝟙 _, by simp [g₀]⟩`. Set `ψ : Over.mk (Γ.G.hom ≫ x) ⟶ PO` to `Over.homMk i' (by simp [PO, reassoc_of% i'snd])`. Establish `h1 : ψ ≫ u = g₀` using `by ext1`. Simplify `i'fst` using `[ψ, u, g₀]`. Establish `h2 : ψ ≫ u ^ N = ψ ≫ 1` using `by rw [MonObj.comp_pow, h1, h0, MonObj.comp_one]`.

Establish `h3 : i' ≫ (u ^ N).left = i' ≫ (1 : PO ⟶ G).left` using `congrArg (fun m => m.left) h2`. Rewrite using `[hfdef, hgdef]`. Conclude with `h3`. Set `b : Γ.G.left ⟶ pullback (pullback.diagonal G.hom) (pullback.lift f g hfg)` to `pullback.lift (i' ≫ f) i' (by`. Apply `pullback.hom_ext` to reduce the goal to its premises.

Simplify using `[l1]`. Simplify using `[l2, key])`. Establish `bjq : b ≫ jq = i'` using `pullback.lift_snd _ _ _`. Set `Qs : Over (Spec (CommRingCat.of R))` to `Over.mk (jq ≫ pullback.snd G.hom x)`. Set `g' : Over.mk (Qs.hom ≫ x) ⟶ G` to `Over.homMk (jq ≫ pullback.fst G.hom x) (by simp [Qs, pullback.condition])`.

Establish `hg' : g' ^ N = 1`. Set `φ : Over.mk (Qs.hom ≫ x) ⟶ PO` to `Over.homMk jq (by simp [PO, Qs])`. Establish `h1 : φ ≫ u = g'` using `by ext1`. Simplify using `[φ, u, g']`. Establish `h2 : φ ≫ u ^ N = φ ≫ 1`.

Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `jq ≫ (u ^ N).left = jq ≫ (1 : PO ⟶ G).left`. Rewrite using `[← hfdef, ← hgdef]`. Conclude with `jqeq`. Rewrite using `[← h1, ← MonObj.comp_pow, h2, MonObj.comp_one]`.

Take `⟨y, hy⟩` from `(h.kernel Qs g').1 hg'`. Establish `hyl : y.left ≫ i = jq ≫ pullback.fst G.hom x` using `hy`. Establish `hys : y.left ≫ Γ.G.hom = jq ≫ pullback.snd G.hom x` using `Over.w y`. Establish `yi' : y.left ≫ i' = jq`. Apply `pullback.hom_ext` to reduce the goal to its premises.

Simplify using `[i'fst, hyl]`. Simplify using `[i'snd, hys]`. Establish `ab : y.left ≫ b = 𝟙 _`. Rewrite using `[← cancel_mono jq]`. Simplify using `[bjq, yi']`.

Establish `ba : b ≫ y.left = 𝟙 _`. Establish `e : (Over.homMk (b ≫ y.left) (by`. Express the relevant statement in the definitionally equal form `(b ≫ y.left) ≫ Γ.G.hom = Γ.G.hom`. Rewrite using `[Category.assoc, hys, ← Category.assoc, bjq, i'snd]) : Γ.G ⟶ Γ.G) = 𝟙 Γ.G := by`. Apply `h.inj Γ.G` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `(b ≫ y.left) ≫ i = 𝟙 _ ≫ i`. Rewrite using `[Category.assoc, hyl, ← Category.assoc, bjq, i'fst, Category.id_comp]`. Conclude with `congrArg (fun m => m.left) e`. Use `haveI : IsIso b := ⟨y.left, ba, ab⟩`. Rewrite using `[← bjq]`.

Use `infer_instance`.
-/
theorem isClosedImmersion_torsion_lift {X : Scheme.{0}} (G : Over X) [GrpObj G] [IsSeparated G.hom]
    (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : QFGroup R T)
    (x : Spec (CommRingCat.of R) ⟶ X) (N : ℕ) (i : Γ.G.left ⟶ G.left)
    (h : Γ.IsTorsionAlong G x N i) :
    IsClosedImmersion (pullback.lift i Γ.G.hom h.isOver : Γ.G.left ⟶ pullback G.hom x) := by
  obtain ⟨i', hi'⟩ : ∃ i' : Γ.G.left ⟶ pullback G.hom x, i' = pullback.lift i Γ.G.hom h.isOver :=
    ⟨_, rfl⟩
  rw [← hi']
  have i'fst : i' ≫ pullback.fst G.hom x = i := by rw [hi']; exact pullback.lift_fst _ _ _
  have i'snd : i' ≫ pullback.snd G.hom x = Γ.G.hom := by rw [hi']; exact pullback.lift_snd _ _ _
  let PO : Over X := Over.mk (pullback.snd G.hom x ≫ x)
  let u : PO ⟶ G := Over.homMk (pullback.fst G.hom x) pullback.condition
  obtain ⟨f, hfdef⟩ : ∃ f : pullback G.hom x ⟶ G.left, f = (u ^ N).left := ⟨_, rfl⟩
  obtain ⟨g, hgdef⟩ : ∃ g : pullback G.hom x ⟶ G.left, g = (1 : PO ⟶ G).left := ⟨_, rfl⟩
  have hf : f ≫ G.hom = pullback.snd G.hom x ≫ x := by rw [hfdef]; exact Over.w (u ^ N)
  have hg : g ≫ G.hom = pullback.snd G.hom x ≫ x := by rw [hgdef]; exact Over.w (1 : PO ⟶ G)
  have hfg : f ≫ G.hom = g ≫ G.hom := hf.trans hg.symm

  let jq : pullback (pullback.diagonal G.hom) (pullback.lift f g hfg) ⟶ pullback G.hom x :=
    pullback.snd _ _
  haveI : IsClosedImmersion jq := inferInstance
  have l1 : pullback.lift f g hfg ≫ pullback.fst G.hom G.hom = f := pullback.lift_fst _ _ _
  have l2 : pullback.lift f g hfg ≫ pullback.snd G.hom G.hom = g := pullback.lift_snd _ _ _
  have cond := pullback.condition (f := pullback.diagonal G.hom) (g := pullback.lift f g hfg)
  have jqf : jq ≫ f = pullback.fst _ _ := by
    have := congrArg (· ≫ pullback.fst G.hom G.hom) cond
    simpa [jq, l1] using this.symm
  have jqg : jq ≫ g = pullback.fst _ _ := by
    have := congrArg (· ≫ pullback.snd G.hom G.hom) cond
    simpa [jq, l2] using this.symm
  have jqeq : jq ≫ f = jq ≫ g := jqf.trans jqg.symm

  have key : i' ≫ f = i' ≫ g := by
    let g₀ : Over.mk (Γ.G.hom ≫ x) ⟶ G := Over.homMk i h.isOver
    have h0 : g₀ ^ N = 1 := (h.kernel Γ.G g₀).2 ⟨𝟙 _, by simp [g₀]⟩
    let ψ : Over.mk (Γ.G.hom ≫ x) ⟶ PO :=
      Over.homMk i' (by simp [PO, reassoc_of% i'snd])
    have h1 : ψ ≫ u = g₀ := by
      ext1
      simpa [ψ, u, g₀] using i'fst
    have h2 : ψ ≫ u ^ N = ψ ≫ 1 := by rw [MonObj.comp_pow, h1, h0, MonObj.comp_one]
    have h3 : i' ≫ (u ^ N).left = i' ≫ (1 : PO ⟶ G).left := congrArg (fun m => m.left) h2
    rw [hfdef, hgdef]
    exact h3
  let b : Γ.G.left ⟶ pullback (pullback.diagonal G.hom) (pullback.lift f g hfg) :=
    pullback.lift (i' ≫ f) i' (by
      apply pullback.hom_ext
      · simp [l1]
      · simp [l2, key])
  have bjq : b ≫ jq = i' := pullback.lift_snd _ _ _

  let Qs : Over (Spec (CommRingCat.of R)) := Over.mk (jq ≫ pullback.snd G.hom x)
  let g' : Over.mk (Qs.hom ≫ x) ⟶ G := Over.homMk (jq ≫ pullback.fst G.hom x)
    (by simp [Qs, pullback.condition])
  have hg' : g' ^ N = 1 := by
    let φ : Over.mk (Qs.hom ≫ x) ⟶ PO := Over.homMk jq (by simp [PO, Qs])
    have h1 : φ ≫ u = g' := by
      ext1
      simp [φ, u, g']
    have h2 : φ ≫ u ^ N = φ ≫ 1 := by
      apply Over.OverMorphism.ext
      change jq ≫ (u ^ N).left = jq ≫ (1 : PO ⟶ G).left
      rw [← hfdef, ← hgdef]
      exact jqeq
    rw [← h1, ← MonObj.comp_pow, h2, MonObj.comp_one]
  obtain ⟨y, hy⟩ := (h.kernel Qs g').1 hg'
  have hyl : y.left ≫ i = jq ≫ pullback.fst G.hom x := hy
  have hys : y.left ≫ Γ.G.hom = jq ≫ pullback.snd G.hom x := Over.w y
  have yi' : y.left ≫ i' = jq := by
    apply pullback.hom_ext
    · simp [i'fst, hyl]
    · simp [i'snd, hys]
  have ab : y.left ≫ b = 𝟙 _ := by
    rw [← cancel_mono jq]
    simp [bjq, yi']
  have ba : b ≫ y.left = 𝟙 _ := by
    have e : (Over.homMk (b ≫ y.left) (by
        change (b ≫ y.left) ≫ Γ.G.hom = Γ.G.hom
        rw [Category.assoc, hys, ← Category.assoc, bjq, i'snd]) : Γ.G ⟶ Γ.G) = 𝟙 Γ.G := by
      apply h.inj Γ.G
      change (b ≫ y.left) ≫ i = 𝟙 _ ≫ i
      rw [Category.assoc, hyl, ← Category.assoc, bjq, i'fst, Category.id_comp]
    exact congrArg (fun m => m.left) e
  haveI : IsIso b := ⟨y.left, ba, ab⟩
  rw [← bjq]
  infer_instance

end GlobalTheory.CompanionTheory.Ar.BT
