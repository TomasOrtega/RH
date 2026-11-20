import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverCompImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedAdjointRingActionScheme
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleSpreadSubring
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.ZRelLevs

/- English proof (translation)
Introduce `h h' M O _ e jl n o κ S' T t z act g c' w' actw' hpb hz`. Take `⟨φ, φ₂, hφ, -, -, hl, ha⟩` from `hpb`. Take `⟨inc, pr, -, -, hip, hpi, -, hc, hw⟩` from `hz`. Establish `key : ∀ b (oo : O), (w'.lev b ≫ actw' oo).left ≫ φ = g ≫ (z.lev b ≫ act oo).left`. Introduce `b oo`.

Rewrite using `[Over.comp_left, Over.comp_left, Category.assoc, ha, ← Category.assoc, hl, Category.assoc]`. Use `⟨fun a => ?_, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[← key, ← hl]`. Use `congr 2`. Rewrite using `[← hc, Category.assoc, ← hpi, ← Category.assoc inc, hip, Category.id_comp]`.

Rewrite using `[← hl, hw a]`. Establish `e1 : ((List.ofFn fun k => c'.lev (κ k a) ≫ inc ≫ actw' (o k)).prod).left ≫ φ = (pushHom hφ (𝟙_ (Over T)) (List.ofFn fun k => c'.lev (κ k a) ≫ inc ≫ actw' (o k)).prod).left` using `rfl`. Rewrite using `[e1, map_list_prod, List.map_ofFn]`. Establish `e2 : g ≫ ((List.ofFn fun k => z.lev (jl (κ k a)) ≫ act (o k)).prod).left = (toUnit (Over.mk ((𝟙_ (Over T)).hom ≫ g)) ≫ (List.ofFn fun k => z.lev (jl (κ k a)) ≫ act (o k)).prod).left`. Rewrite using `[Over.comp_left, Over.toUnit_left]`.

Both sides reduce to the same expression. Rewrite using `[e2, GlobalTheory.comp_list_prod_ofFn]`. Use `congr 3`. Use function extensionality and compare the values at `k`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Use `show (c'.lev (κ k a) ≫ inc ≫ actw' (o k)).left ≫ φ = _`. Rewrite using `[← Category.assoc, hc, key]`. Simplify using `only [Over.comp_left, Over.toUnit_left, Over.mk_hom]`. Both sides reduce to the same expression.
-/
theorem zrel_levs : ∀ (h h' M : ℕ) (O : Type) [Ring O] (e : O) (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) (n : ℕ) (o : Fin n → O) (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S' T : Scheme.{0}) (t : S' ⟶ Sp (cycAway M)) (z : SiegPre h' M (zetaAway M) t) (act : O → (z.A ⟶ z.A)) (g : T ⟶ S') (c' : SiegPre h M (zetaAway M) (g ≫ t)) (w' : SiegPre h' M (zetaAway M) (g ≫ t)) (actw' : O → (w'.A ⟶ w'.A)), ActPB w' actw' z act g → ZRel e jl o κ c' w' actw' → (∀ a, g ≫ (z.lev (jl a) ≫ act e).left = g ≫ (z.lev (jl a)).left) ∧ ∀ a, g ≫ (z.lev a).left = g ≫ ((List.ofFn fun k => z.lev (jl (κ k a)) ≫ act (o k)).prod).left := by
  intro h h' M O _ e jl n o κ S' T t z act g c' w' actw' hpb hz
  obtain ⟨φ, φ₂, hφ, -, -, hl, ha⟩ := hpb
  obtain ⟨inc, pr, -, -, hip, hpi, -, hc, hw⟩ := hz
  have key : ∀ b (oo : O), (w'.lev b ≫ actw' oo).left ≫ φ = g ≫ (z.lev b ≫ act oo).left := by
    intro b oo
    rw [Over.comp_left, Over.comp_left, Category.assoc, ha, ← Category.assoc, hl, Category.assoc]
  refine ⟨fun a => ?_, fun a => ?_⟩
  · rw [← key, ← hl]
    congr 2
    rw [← hc, Category.assoc, ← hpi, ← Category.assoc inc, hip, Category.id_comp]
  · rw [← hl, hw a]
    have e1 : ((List.ofFn fun k => c'.lev (κ k a) ≫ inc ≫ actw' (o k)).prod).left ≫ φ =
        (pushHom hφ (𝟙_ (Over T)) (List.ofFn fun k => c'.lev (κ k a) ≫ inc ≫ actw' (o k)).prod).left := rfl
    rw [e1, map_list_prod, List.map_ofFn]
    have e2 : g ≫ ((List.ofFn fun k => z.lev (jl (κ k a)) ≫ act (o k)).prod).left =
        (toUnit (Over.mk ((𝟙_ (Over T)).hom ≫ g)) ≫
          (List.ofFn fun k => z.lev (jl (κ k a)) ≫ act (o k)).prod).left := by
      rw [Over.comp_left, Over.toUnit_left]
      rfl
    rw [e2, GlobalTheory.comp_list_prod_ofFn]
    congr 3
    funext k
    apply Over.OverMorphism.ext
    show (c'.lev (κ k a) ≫ inc ≫ actw' (o k)).left ≫ φ = _
    rw [← Category.assoc, hc, key]
    simp only [Over.comp_left, Over.toUnit_left, Over.mk_hom]
    rfl

end GlobalTheory.ZRelLevs
