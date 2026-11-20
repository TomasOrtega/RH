import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GenPoint

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 y₀ hy`. Use `haveI : FiniteDimensional ℚ c.F := c.fin`. Use `haveI : NumberField c.F := {}`. Use `haveI := Y.jQ_open`. Establish `hd : 𝔐.ξ ≫ 𝔐.f = spMap 𝔐.fn ≫ 𝔐.ξ₀` using `𝔐.fn_over`.

Set `b₀ : 𝓞 c.F →+* 𝔐.Ω₀` to `(Spec.preimage (𝔐.ξ₀ ≫ Y.s)).hom`. Establish `hb : 𝔐.ξ₀ ≫ Y.s = spMap b₀` using `(Spec.map_preimage _).symm`. Establish `hc : 𝔐.fn.comp b₀ = 𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)`. Establish `hsp : spMap (𝔐.fn.comp b₀) = spMap (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F))`. Establish `hm : spMap (𝔐.fn.comp b₀) = spMap 𝔐.fn ≫ spMap b₀`.

Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression. Rewrite using `[hm, ← hb, ← 𝔐.cst_over, ← Category.assoc, ← Category.assoc, hd]`. Use `CommRingCat.hom_ext_iff.1 (Spec.map_injective hsp)` as an intermediate fact. Simplify using `using this`.

Establish `hinj : Function.Injective b₀`. Introduce `u v huv`. Establish `h` using `congrArg 𝔐.fn huv`. Establish `hu : ∀ w, 𝔐.fn (b₀ w) = 𝔐.cst (algebraMap (𝓞 c.F) c.F w)` using `fun w => RingHom.congr_fun hc w`. Rewrite `h` using `[hu, hu]`.

Conclude with `IsFractionRing.injective (𝓞 c.F) c.F (𝔐.cst.injective h)`. Set `cst₀ : c.F →+* 𝔐.Ω₀` to `IsFractionRing.lift hinj`. Establish `hl : cst₀.comp (algebraMap (𝓞 c.F) c.F) = b₀`. Use extensionality with `w`. Conclude with `IsFractionRing.lift_algebraMap hinj w`.

Establish `hfn : 𝔐.fn.comp cst₀ = 𝔐.cst`. Use `IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) ?_` and prove the remaining obligations. Rewrite using `[RingHom.comp_assoc, hl, hc]`. Establish `hs : 𝔐.ξ₀ ≫ Y.s = spMap (cst₀.comp (algebraMap (𝓞 c.F) c.F))` using `by rw [hl, hb]`. Establish `hcomp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C), spMap (g.comp f) = spMap g ≫ spMap f`.

Introduce `A B C _ _ _ f g`. Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression. Set `w : Sp 𝔐.Ω₀ ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F))` to `pullback.lift 𝔐.ξ₀ (spMap cst₀) (by rw [hs, hcomp])`. Set `u : c.F →+* Ω` to `(Spec.preimage (y₀ ≫ pullback.snd _ _)).hom`.

Establish `hu : y₀ ≫ pullback.snd _ _ = spMap u` using `(Spec.map_preimage _).symm`. Establish `huc : u = 𝔐.cst`. Establish `hsp : spMap (u.comp (algebraMap (𝓞 c.F) c.F)) = spMap (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F))`. Rewrite using `[hcomp, ← hu, ← 𝔐.cst_over, ← Category.assoc 𝔐.ξ, hy, Model.j]`. Simplify using `only [Category.assoc]`.

Rewrite using `[pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over]`. Establish `h1` using `CommRingCat.hom_ext_iff.1 (Spec.map_injective hsp)`. Establish `h2 : u.comp (algebraMap (𝓞 c.F) c.F) = 𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)` using `by simpa using h1`. Conclude with `IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) h2`. Establish `hw : spMap 𝔐.fn ≫ w = y₀ ≫ Y.jQ`.

Use `pullback.hom_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, pullback.lift_fst, ← hd, hy, Model.j, Category.assoc]`. Rewrite using `[Category.assoc, pullback.lift_snd, ← hcomp, hfn, Category.assoc, Y.jQ_over, hu, huc]`. Establish `hr : Set.range w ⊆ Set.range Y.jQ`. Introduce and unpack `_ ⟨a, rfl⟩`.

Take `⟨a', rfl⟩ : ∃ a', (spMap 𝔐.fn) a' = a` from `⟨IsLocalRing.closedPoint _, Subsingleton.elim _ _⟩`. Use `⟨y₀ a', ?_⟩` and prove the remaining obligations. Use `congrArg (fun φ => φ a') hw` as an intermediate fact. Simplify using `using this.symm`. Use `⟨cst₀, IsOpenImmersion.lift Y.jQ w hr, ?_, hs, hfn⟩` and prove the remaining obligations.

Rewrite using `[Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]`.
-/
theorem exists_open_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (y₀ : Sp Ω ⟶ Xo.XF c), 𝔐.ξ ≫ 𝔐.f = y₀ ≫ Y.j → ∃ (cst₀ : c.F →+* 𝔐.Ω₀) (y₁ : Sp 𝔐.Ω₀ ⟶ Xo.XF c), 𝔐.ξ₀ = y₁ ≫ Y.j ∧ 𝔐.ξ₀ ≫ Y.s = spMap (cst₀.comp (algebraMap (𝓞 c.F) c.F)) ∧ 𝔐.fn.comp cst₀ = 𝔐.cst := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 y₀ hy
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := {}
  haveI := Y.jQ_open
  have hd : 𝔐.ξ ≫ 𝔐.f = spMap 𝔐.fn ≫ 𝔐.ξ₀ := 𝔐.fn_over

  let b₀ : 𝓞 c.F →+* 𝔐.Ω₀ := (Spec.preimage (𝔐.ξ₀ ≫ Y.s)).hom
  have hb : 𝔐.ξ₀ ≫ Y.s = spMap b₀ := (Spec.map_preimage _).symm
  have hc : 𝔐.fn.comp b₀ = 𝔐.cst.comp (algebraMap (𝓞 c.F) c.F) := by
    have hsp : spMap (𝔐.fn.comp b₀) = spMap (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)) := by
      have hm : spMap (𝔐.fn.comp b₀) = spMap 𝔐.fn ≫ spMap b₀ := by
        rw [← Spec.map_comp]; rfl
      rw [hm, ← hb, ← 𝔐.cst_over, ← Category.assoc, ← Category.assoc, hd]
    have := CommRingCat.hom_ext_iff.1 (Spec.map_injective hsp)
    simpa using this
  have hinj : Function.Injective b₀ := by
    intro u v huv
    have h := congrArg 𝔐.fn huv
    have hu : ∀ w, 𝔐.fn (b₀ w) = 𝔐.cst (algebraMap (𝓞 c.F) c.F w) := fun w => RingHom.congr_fun hc w
    rw [hu, hu] at h
    exact IsFractionRing.injective (𝓞 c.F) c.F (𝔐.cst.injective h)
  let cst₀ : c.F →+* 𝔐.Ω₀ := IsFractionRing.lift hinj
  have hl : cst₀.comp (algebraMap (𝓞 c.F) c.F) = b₀ := by
    ext w
    exact IsFractionRing.lift_algebraMap hinj w
  have hfn : 𝔐.fn.comp cst₀ = 𝔐.cst := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) ?_
    rw [RingHom.comp_assoc, hl, hc]
  have hs : 𝔐.ξ₀ ≫ Y.s = spMap (cst₀.comp (algebraMap (𝓞 c.F) c.F)) := by rw [hl, hb]
  have hcomp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C),
      spMap (g.comp f) = spMap g ≫ spMap f := by
    intro A B C _ _ _ f g
    rw [← Spec.map_comp]; rfl

  let w : Sp 𝔐.Ω₀ ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F)) :=
    pullback.lift 𝔐.ξ₀ (spMap cst₀) (by rw [hs, hcomp])

  let u : c.F →+* Ω := (Spec.preimage (y₀ ≫ pullback.snd _ _)).hom
  have hu : y₀ ≫ pullback.snd _ _ = spMap u := (Spec.map_preimage _).symm
  have huc : u = 𝔐.cst := by
    have hsp : spMap (u.comp (algebraMap (𝓞 c.F) c.F)) = spMap (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)) := by
      rw [hcomp, ← hu, ← 𝔐.cst_over, ← Category.assoc 𝔐.ξ, hy, Model.j]
      simp only [Category.assoc]
      rw [pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over]
    have h1 := CommRingCat.hom_ext_iff.1 (Spec.map_injective hsp)
    have h2 : u.comp (algebraMap (𝓞 c.F) c.F) = 𝔐.cst.comp (algebraMap (𝓞 c.F) c.F) := by simpa using h1
    exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) h2
  have hw : spMap 𝔐.fn ≫ w = y₀ ≫ Y.jQ := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, ← hd, hy, Model.j, Category.assoc]
    · rw [Category.assoc, pullback.lift_snd, ← hcomp, hfn, Category.assoc, Y.jQ_over, hu, huc]
  have hr : Set.range w ⊆ Set.range Y.jQ := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨a', rfl⟩ : ∃ a', (spMap 𝔐.fn) a' = a :=
      ⟨IsLocalRing.closedPoint _, Subsingleton.elim _ _⟩
    refine ⟨y₀ a', ?_⟩
    have := congrArg (fun φ => φ a') hw
    simpa using this.symm
  refine ⟨cst₀, IsOpenImmersion.lift Y.jQ w hr, ?_, hs, hfn⟩
  rw [Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]

end GlobalTheory.CompanionTheory.Ar.GenPoint
