import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

/- English proof (translation)
Introduce `S G _ _ L ρ hL hρ g m R _ _ x K _ i hm hu hP th pt c c' H H'`. Take `⟨P, α, -, hp, w, hw⟩` from `hP`. Take `⟨ρ₁, -, hr⟩` from `GlobalTheory.Ex.OneGen.exists_rigidificationPullbackCompatibleIso hp hw hL P.isLB hρ`. Set `T : Over (Sp R)` to `Over.mk (spMap i)`. Set `T₀ : Over S` to `Over.mk (spMap i ≫ x)`.

Establish `hτ : 𝟙 (Sp K) ≫ T₀.hom = T.hom ≫ x` using `Category.id_comp _`. Take `⟨th₁, hth⟩` from `GlobalTheory.ThetaPtMove.exists_secRel hp (T := T) (T₀ := T₀) (𝟙 _) hτ hw hL P.isLB th`. Establish `hsq : pt.left ≫ G.hom = spMap i ≫ x` using `Over.w pt`. Set `x₁ : T ⟶ P.A` to `Over.homMk (hp.1.lift pt.left (spMap i) hsq) (hp.1.lift_snd _ _ _)`. Establish `hx : 𝟙 (Sp K) ≫ pt.left = x₁.left ≫ α`.

Rewrite using `[Category.id_comp]`. Conclude with `(hp.1.lift_fst _ _ _).symm`. Establish `hn : x₁ ^ (m ^ 2) = 1`. Establish `h1` using `GlobalTheory.ThetaPtMove.over_pow hp (T := T) (T₀ := T₀) (𝟙 _) hτ hx (m ^ 2)`. Rewrite `h1` using `[H.1]`.

Establish `h2` using `GlobalTheory.ThetaPtMove.over_one hp (T := T) (T₀ := T₀) (𝟙 _) hτ`. Conclude with `Over.OverMorphism.ext (hp.1.hom_ext (h1.symm.trans h2) ((Over.w _).trans (Over.w _).symm))`. Establish `hu' : IsUnit ((m ^ 2 : ℕ) : Γ(Sp R, ⊤))`. Rewrite using `[Nat.cast_pow, ← map_natCast (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom m, ← map_pow]`. Conclude with `(hu.pow 2).map _`.

Establish `m1 : ThG P.A P.L ρ₁ m th₁ x₁ ((𝟙 (Sp K) : Sp K ⟶ Sp K).appTop.hom (fn c))` using `ThG.move (T := T) (T₀ := T₀) hp (𝟙 _) hτ hw hL P.isLB hr hx hn hth H`. Establish `m2 : ThG P.A P.L ρ₁ m th₁ x₁ ((𝟙 (Sp K) : Sp K ⟶ Sp K).appTop.hom (fn c'))` using `ThG.move (T := T) (T₀ := T₀) hp (𝟙 _) hτ hw hL P.isLB hr hx hn hth H'`. Establish `e` using `ThG.unique (T := T) abelianSchemeLaws_all.1 P hm hu' m1 m2`. Establish `e2` using `congrArg (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom e`. Simplify using `using e2`.
-/
theorem thG_unique_of_polFib : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (x : Sp R ⟶ S) (K : Type) [Field K] (i : R →+* K), Odd m → IsUnit (m : R) → PolFib G L g x → ∀ (th : SecAt G L (spMap i ≫ x)) (pt : Over.mk (spMap i ≫ x) ⟶ G) (c c' : K), ThG G L ρ m th pt (fn c) → ThG G L ρ m th pt (fn c') → c = c' := by
  intro S G _ _ L ρ hL hρ g m R _ _ x K _ i hm hu hP th pt c c' H H'
  obtain ⟨P, α, -, hp, w, hw⟩ := hP
  obtain ⟨ρ₁, -, hr⟩ := GlobalTheory.Ex.OneGen.exists_rigidificationPullbackCompatibleIso hp hw hL P.isLB hρ
  let T : Over (Sp R) := Over.mk (spMap i)
  let T₀ : Over S := Over.mk (spMap i ≫ x)
  have hτ : 𝟙 (Sp K) ≫ T₀.hom = T.hom ≫ x := Category.id_comp _
  obtain ⟨th₁, hth⟩ := GlobalTheory.ThetaPtMove.exists_secRel hp (T := T) (T₀ := T₀) (𝟙 _) hτ hw hL P.isLB th
  have hsq : pt.left ≫ G.hom = spMap i ≫ x := Over.w pt
  let x₁ : T ⟶ P.A := Over.homMk (hp.1.lift pt.left (spMap i) hsq) (hp.1.lift_snd _ _ _)
  have hx : 𝟙 (Sp K) ≫ pt.left = x₁.left ≫ α := by
    rw [Category.id_comp]; exact (hp.1.lift_fst _ _ _).symm
  have hn : x₁ ^ (m ^ 2) = 1 := by
    have h1 := GlobalTheory.ThetaPtMove.over_pow hp (T := T) (T₀ := T₀) (𝟙 _) hτ hx (m ^ 2)
    rw [H.1] at h1
    have h2 := GlobalTheory.ThetaPtMove.over_one hp (T := T) (T₀ := T₀) (𝟙 _) hτ
    exact Over.OverMorphism.ext (hp.1.hom_ext (h1.symm.trans h2) ((Over.w _).trans (Over.w _).symm))
  have hu' : IsUnit ((m ^ 2 : ℕ) : Γ(Sp R, ⊤)) := by
    rw [Nat.cast_pow, ← map_natCast (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom m, ← map_pow]
    exact (hu.pow 2).map _
  have m1 : ThG P.A P.L ρ₁ m th₁ x₁ ((𝟙 (Sp K) : Sp K ⟶ Sp K).appTop.hom (fn c)) :=
    ThG.move (T := T) (T₀ := T₀) hp (𝟙 _) hτ hw hL P.isLB hr hx hn hth H
  have m2 : ThG P.A P.L ρ₁ m th₁ x₁ ((𝟙 (Sp K) : Sp K ⟶ Sp K).appTop.hom (fn c')) :=
    ThG.move (T := T) (T₀ := T₀) hp (𝟙 _) hτ hw hL P.isLB hr hx hn hth H'
  have e := ThG.unique (T := T) abelianSchemeLaws_all.1 P hm hu' m1 m2
  have e2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom e
  simpa using e2

end GlobalTheory.UMin
