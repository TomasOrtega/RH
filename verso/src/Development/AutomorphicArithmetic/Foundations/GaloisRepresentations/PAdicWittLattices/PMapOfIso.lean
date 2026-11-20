import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

/- English proof (translation)
Introduce `G₀ R _ _ gb S s N o o' θ hiso hmon hact hpol heta`. Use `haveI : IsIso θ.left := (Over.forget S).map_isIso θ`. Use `⟨⟨θ.left, Hecke.sq2 θ, ⟨IsPullback.of_horiz_isIso ⟨by rw [Over.w, Category.comp_id]⟩, ?_⟩, ⟨?_, ?_⟩, fun c => ?_, hpol, fun y => ?_⟩, rfl⟩` and prove the remaining obligations. Introduce `T x y x₀ y₀ hx hy`. Set `u : Over.mk (T.hom ≫ 𝟙 S) ⟶ T` to `Over.homMk (𝟙 T.left) (by simp)`.

Establish `ex : x₀ = u ≫ x ≫ θ` using `Over.OverMorphism.ext (by simp [u, hx])`. Establish `ey : y₀ = u ≫ y ≫ θ` using `Over.OverMorphism.ext (by simp [u, hy])`. Rewrite using `[ex, ey, ← MonObj.comp_mul, ← MonObj.mul_comp]`. Simplify using `[u]`. Rewrite using `[Hecke.sq2, ← Over.comp_left, lift_fst, Over.comp_left]`.

Rewrite using `[Hecke.sq2, ← Over.comp_left, lift_snd, Over.comp_left]`. Rewrite using `[← Over.comp_left, hact c, Over.comp_left]`. Rewrite using `[← Over.comp_left, heta y, Category.id_comp]`.
-/
theorem UpperTheory.Gal.G3.pMapOfIso :
    MapOfIso := by
  intro G₀ R _ _ gb S s N o o' θ hiso hmon hact hpol heta
  haveI : IsIso θ.left := (Over.forget S).map_isIso θ
  refine ⟨⟨θ.left, Hecke.sq2 θ, ⟨IsPullback.of_horiz_isIso ⟨by rw [Over.w, Category.comp_id]⟩, ?_⟩, ⟨?_, ?_⟩,
    fun c => ?_, hpol, fun y => ?_⟩, rfl⟩
  · intro T x y x₀ y₀ hx hy
    let u : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
    have ex : x₀ = u ≫ x ≫ θ := Over.OverMorphism.ext (by simp [u, hx])
    have ey : y₀ = u ≫ y ≫ θ := Over.OverMorphism.ext (by simp [u, hy])
    rw [ex, ey, ← MonObj.comp_mul, ← MonObj.mul_comp]
    simp [u]
  · rw [Hecke.sq2, ← Over.comp_left, lift_fst, Over.comp_left]
  · rw [Hecke.sq2, ← Over.comp_left, lift_snd, Over.comp_left]
  · rw [← Over.comp_left, hact c, Over.comp_left]
  · rw [← Over.comp_left, heta y, Category.id_comp]
