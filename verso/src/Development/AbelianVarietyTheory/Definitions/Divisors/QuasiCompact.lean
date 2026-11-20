import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

structure Near {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} (π : S ⟶ Sp R) (G : Over S) where

  U : Over (Sp R)

  smooth : Smooth U.hom

  separated : IsSeparated U.hom

  quasiCompact : QuasiCompact U.hom

  u : pullback U.hom π ⟶ G.left

  isOpen : IsOpenImmersion u

  u_over : u ≫ G.hom = pullback.snd U.hom π

  all : ∀ g : G.left, π (G.hom g) = closedPoint R → g ∈ Set.range u

def Near.self {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [Smooth G.hom] [IsSeparated G.hom]
    [QuasiCompact G.hom] : Near (𝟙 (Sp R)) G where
  U := G
  smooth := inferInstance
  separated := inferInstance
  quasiCompact := inferInstance
  u := pullback.fst G.hom (𝟙 _)
  isOpen := inferInstance
  u_over := by simpa using pullback.condition (f := G.hom) (g := 𝟙 (Sp R))
  all := fun g _ => (pullback.fst G.hom (𝟙 (Sp R))).surjective g

section

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}

def Near.Pt (N : Near π G) {T : Scheme.{0}} (s : T ⟶ S) (a : T ⟶ N.U.left) (x : T ⟶ G.left) : Prop :=
  ∃ x₀ : T ⟶ pullback N.U.hom π, x₀ ≫ pullback.fst _ _ = a ∧ x₀ ≫ pullback.snd _ _ = s ∧ x₀ ≫ N.u = x

def Near.Law [GrpObj G] (N : Near π G) : Prop :=
  ∃ (V : (N.U ⊗ N.U).left.Opens) (m : V.toScheme ⟶ N.U.left),
    (∀ z : (N.U ⊗ N.U).left, (N.U ⊗ N.U).hom z = closedPoint R → z ∈ V) ∧ m ≫ N.U.hom = V.ι ≫ (N.U ⊗ N.U).hom ∧
    ∀ (T : Scheme.{0}) (v : T ⟶ V.toScheme) (s : T ⟶ S) (x y : Over.mk s ⟶ G),
      N.Pt s (v ≫ V.ι ≫ (fst N.U N.U).left) x.left → N.Pt s (v ≫ V.ι ≫ (snd N.U N.U).left) y.left →
      N.Pt s (v ≫ m) (x * y).left

def Near.Datum [GrpObj G] (N : Near π G)
    (φ : (Over.pullback (pullback.fst π π)).obj G ≅ (Over.pullback (pullback.snd π π)).obj G) : Prop :=
  IsMonHom φ.hom ∧ ∀ (T : Scheme.{0}) (a : T ⟶ N.U.left) (x : T ⟶ ((Over.pullback (pullback.fst π π)).obj G).left),
    N.Pt (x ≫ pullback.snd G.hom (pullback.fst π π) ≫ pullback.fst π π) a (x ≫ pullback.fst G.hom (pullback.fst π π)) →
    N.Pt (x ≫ pullback.snd G.hom (pullback.fst π π) ≫ pullback.snd π π) a
      (x ≫ φ.hom.left ≫ pullback.fst G.hom (pullback.snd π π))

end

def Gal {R R' : Type} [CommRing R] [CommRing R'] (ρ : R →+* R') : Subgroup (R' ≃+* R') where
  carrier := {σ | ∀ r, σ (ρ r) = ρ r}
  mul_mem' := fun {a b} ha hb r => by rw [RingAut.mul_apply, hb r, ha r]
  one_mem' := fun _ => rfl
  inv_mem' := fun {a} ha r => by
    have := congrArg a.symm (ha r)
    rw [RingEquiv.symm_apply_apply] at this
    exact this.symm

def Gal.hom {R R' : Type} [CommRing R] [CommRing R'] {ρ : R →+* R'} (σ : Gal ρ) : R' →+* R' := σ.1.toRingHom

def PullOver {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {ρ : R →+* R'} {s : R' →+* R'} {D : DegPre R}
    {D' : DegPre R'} (hD : IsPullDeg ρ D D') (h : IsPullDeg s D' D') : Prop :=
  (∀ x, h.xe x = x) ∧ ∀ (b : D'.P.A.left ⟶ D.P.A.left) (c : D'.P.A.left ⟶ D'.P.A.left),
    b = hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf ρ) → c = h.e.hom.left ≫ pullback.fst D'.P.A.hom (specOf s) → c ≫ b = b

def IsGal {R R' : Type} [CommRing R] [CommRing R'] (ρ : R →+* R') : Prop :=
  Finite (Gal ρ) ∧ ∀ x : R', (∀ σ ∈ Gal ρ, σ x = x) → x ∈ ρ.range

structure GalAct {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R'} (ρ : R →+* R')
    {D : DegPre R} {D' : DegData R' I} (hD : IsPullDeg ρ D D'.toPre) {A' : PolAV (Sp (FractionRing R'))} {G' : Over (Sp R')}
    [GrpObj G'] [IsCommMonObj G'] (U' : Unif I D' A' G') where

  act : Gal ρ → (G'.left ⟶ G'.left)

  cart : ∀ σ, IsGrpPullback G' G' (spMap (Gal.hom σ)) (act σ)

  act_one : act 1 = 𝟙 _

  act_mul : ∀ σ τ, act (σ * τ) = act σ ≫ act τ

  unif : ∀ σ, ∃ (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre)
    (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'),
    bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = act σ ∧ IsPullUnif (Gal.hom σ) h bc U' U' ∧ PullOver hD h

/- English proof (translation)
Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.
-/
example {R R' : Type} [CommRing R] [CommRing R'] {ρ : R →+* R'} (σ τ : Gal ρ) :
    spMap (Gal.hom (σ * τ)) = spMap (Gal.hom σ) ≫ spMap (Gal.hom τ) := by
  rw [← Spec.map_comp]; rfl

/- English proof (translation)
Use `⟨⟨starRingAut, fun r => by simp⟩, 1, fun h => ?_⟩` and prove the remaining obligations. Establish `h₁ : (starRingEnd ℂ) Complex.I = Complex.I` using `congrArg (fun σ : Gal (algebraMap ℝ ℂ) => σ.1 Complex.I) h`. Establish `h₂` using `congrArg Complex.im h₁`. Evaluate the numerical expressions using `at h₂`.
-/
example : Nontrivial (Gal (algebraMap ℝ ℂ)) := by
  refine ⟨⟨starRingAut, fun r => by simp⟩, 1, fun h => ?_⟩
  have h₁ : (starRingEnd ℂ) Complex.I = Complex.I := congrArg (fun σ : Gal (algebraMap ℝ ℂ) => σ.1 Complex.I) h
  have h₂ := congrArg Complex.im h₁
  norm_num at h₂

/- English proof (translation)
Introduce and unpack `⟨-, h⟩`. Take `⟨n, hn⟩` from `h (1 / 2) (fun σ _ => by simp)`. Establish `h₁ : ((2 * n : ℤ) : ℚ) = ((1 : ℤ) : ℚ)`. Establish `: (n : ℚ) = 1 / 2` using `hn`. Use `push_cast`.

Rewrite using `[this]`. Evaluate the numerical expressions. Establish `h₂ : 2 * n = 1` using `by exact_mod_cast h₁`. Use linear arithmetic over natural numbers and integers.
-/
example : ¬ IsGal (Int.castRingHom ℚ) := by
  rintro ⟨-, h⟩
  obtain ⟨n, hn⟩ := h (1 / 2) (fun σ _ => by simp)
  have h₁ : ((2 * n : ℤ) : ℚ) = ((1 : ℤ) : ℚ) := by
    have : (n : ℚ) = 1 / 2 := hn
    push_cast
    rw [this]; norm_num
  have h₂ : 2 * n = 1 := by exact_mod_cast h₁
  omega

/- English proof (translation)
Set `N : Near π ((Over.pullback π).obj G)` to `{ U := G smooth := inferInstance separated := inferInstance quasiCompact := inferInstance u := 𝟙 _ isOpen := inferInstanceAs (IsOpenImmersion (𝟙 (pullback G.hom π))) u_over := Category.id_comp _ all := fun g _ => ⟨g, rfl⟩ }`. Establish `pt : ∀ {T : Scheme.{0}} (s : T ⟶ S) (a : T ⟶ G.left) (x : T ⟶ pullback G.hom π), N.Pt s a x ↔ x ≫ pullback.fst _ _ = a ∧ x ≫ pullback.snd _ _ = s` using `fun s a x => ⟨fun ⟨x₀, h₁, h₂, h₃⟩ => by`. Take `rfl : x₀ = x` from `(Category.comp_id _).symm.trans h₃`. Conclude with `⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨x, h₁, h₂, Category.comp_id _⟩⟩`. Use `⟨N, rfl, ⟨⊤, (⊤ : (G ⊗ G).left.Opens).ι ≫ μ[G].left, fun _ _ => trivial, ?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Conclude with `(Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Over.w μ[G]))`. Introduce `T v s x y hx hy`. Take `⟨hx, hx'⟩` from `(pt _ _ _).1 hx`. Take `⟨hy, -⟩` from `(pt _ _ _).1 hy`. Use `(pt _ _ _).2 ⟨?_, Over.w (x * y)⟩` and prove the remaining obligations.

Establish `hw : (v ≫ (⊤ : (G ⊗ G).left.Opens).ι) ≫ (G ⊗ G).hom = s ≫ π`. Rewrite using `[← Over.w (fst G G), ← hx', Category.assoc x.left, ← pullback.condition, ← Category.assoc x.left]`. Use `erw [hx]`. Conclude with `(Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans (congrArg (v ≫ ·) (Category.assoc _ _ _))).symm`. Set `p : Over.mk (s ≫ π) ⟶ G ⊗ G` to `Over.homMk (v ≫ (⊤ : (G ⊗ G).left.Opens).ι) hw`.

Use `(isGrpPullback_pullback G π).2 (Over.mk s) x y (p ≫ fst G G) (p ≫ snd G G) ((Category.assoc _ _ _).trans hx.symm) ((Category.assoc _ _ _).trans hy.symm)` as an intermediate fact. Use `erw [← this]`. Rewrite using `[Hom.mul_def, ← comp_lift, lift_fst_snd, Category.comp_id]`. Conclude with `Category.assoc _ _ _`. Establish `p₁` using `(isGrpPullback_pullback ((Over.pullback π).obj G) (pullback.fst π π)).comp (isGrpPullback_pullback G π)`.

Establish `p₂` using `(isGrpPullback_pullback ((Over.pullback π).obj G) (pullback.snd π π)).comp (isGrpPullback_pullback G π)`. Take `⟨φ, hφ, e⟩` from `grpPullback_iso p₁ (p₂.congr pullback.condition.symm rfl)`. Use `⟨φ, hφ, fun T a x hx => ?_⟩` and prove the remaining obligations. Take `⟨hx, -⟩` from `(pt _ _ _).1 hx`. Use `(pt _ _ _).2 ⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hx]`. Simplify using `only [Category.assoc]`. Conclude with `congrArg (x ≫ ·) e`. Simplify using `only [Category.assoc]`. Use `congrArg (x ≫ ·) ?_` and prove the remaining obligations.

Use `(congrArg (φ.hom.left ≫ ·) pullback.condition).trans ?_` and prove the remaining obligations. Conclude with `(Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (Over.w φ.hom))`.
-/
example {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} (π : S ⟶ Sp R) (G : Over (Sp R)) [GrpObj G]
    [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] :
    ∃ N : Near π ((Over.pullback π).obj G), N.U = G ∧ N.Law ∧ ∃ φ, N.Datum φ := by
  let N : Near π ((Over.pullback π).obj G) :=
    { U := G
      smooth := inferInstance
      separated := inferInstance
      quasiCompact := inferInstance
      u := 𝟙 _
      isOpen := inferInstanceAs (IsOpenImmersion (𝟙 (pullback G.hom π)))
      u_over := Category.id_comp _
      all := fun g _ => ⟨g, rfl⟩ }
  have pt : ∀ {T : Scheme.{0}} (s : T ⟶ S) (a : T ⟶ G.left) (x : T ⟶ pullback G.hom π),
      N.Pt s a x ↔ x ≫ pullback.fst _ _ = a ∧ x ≫ pullback.snd _ _ = s := fun s a x =>
    ⟨fun ⟨x₀, h₁, h₂, h₃⟩ => by
      obtain rfl : x₀ = x := (Category.comp_id _).symm.trans h₃
      exact ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨x, h₁, h₂, Category.comp_id _⟩⟩
  refine ⟨N, rfl, ⟨⊤, (⊤ : (G ⊗ G).left.Opens).ι ≫ μ[G].left, fun _ _ => trivial, ?_, ?_⟩, ?_⟩
  · exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Over.w μ[G]))
  · intro T v s x y hx hy
    obtain ⟨hx, hx'⟩ := (pt _ _ _).1 hx
    obtain ⟨hy, -⟩ := (pt _ _ _).1 hy
    refine (pt _ _ _).2 ⟨?_, Over.w (x * y)⟩
    have hw : (v ≫ (⊤ : (G ⊗ G).left.Opens).ι) ≫ (G ⊗ G).hom = s ≫ π := by
      rw [← Over.w (fst G G), ← hx', Category.assoc x.left, ← pullback.condition, ← Category.assoc x.left]
      erw [hx]
      exact (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans (congrArg (v ≫ ·) (Category.assoc _ _ _))).symm
    let p : Over.mk (s ≫ π) ⟶ G ⊗ G := Over.homMk (v ≫ (⊤ : (G ⊗ G).left.Opens).ι) hw
    have := (isGrpPullback_pullback G π).2 (Over.mk s) x y (p ≫ fst G G) (p ≫ snd G G)
      ((Category.assoc _ _ _).trans hx.symm) ((Category.assoc _ _ _).trans hy.symm)
    erw [← this]
    rw [Hom.mul_def, ← comp_lift, lift_fst_snd, Category.comp_id]
    exact Category.assoc _ _ _
  · have p₁ := (isGrpPullback_pullback ((Over.pullback π).obj G) (pullback.fst π π)).comp (isGrpPullback_pullback G π)
    have p₂ := (isGrpPullback_pullback ((Over.pullback π).obj G) (pullback.snd π π)).comp (isGrpPullback_pullback G π)
    obtain ⟨φ, hφ, e⟩ := grpPullback_iso p₁ (p₂.congr pullback.condition.symm rfl)
    refine ⟨φ, hφ, fun T a x hx => ?_⟩
    obtain ⟨hx, -⟩ := (pt _ _ _).1 hx
    refine (pt _ _ _).2 ⟨?_, ?_⟩
    · rw [← hx]
      simp only [Category.assoc]
      exact congrArg (x ≫ ·) e
    · simp only [Category.assoc]
      refine congrArg (x ≫ ·) ?_
      refine (congrArg (φ.hom.left ≫ ·) pullback.condition).trans ?_
      exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (Over.w φ.hom))

end GlobalTheory.Mum
