import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CarriesLinCombGeneratorCalculusStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsGroupIsoCubicalIsoOfTripleMapIdStatement

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ChartCmp

/- English proof (translation)
Substitute `h` using the available equality. Use `⟨c, hc, fun j j' _ _ hj => ?_⟩` and prove the remaining obligations. Take `rfl : j = j'` from `funext fun k => hj k k rfl`. Both sides reduce to the same expression.
-/
theorem exists_corr_of_family_eq {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)}
    (h : φ = φ') (ε : K → ℤ) (c : LB.Gen (LB.LinComb L φ ε)) (hc : c.IsGen) :
    ∃ c' : LB.Gen (LB.LinComb L φ' ε), c'.IsGen ∧ LB.Gen.Corr L _ _ _ _ c c' := by
  subst h
  refine ⟨c, hc, fun j j' _ _ hj => ?_⟩
  obtain rfl : j = j' := funext fun k => hj k k rfl
  rfl

/- English proof (translation)
Introduce `E _ _ _ H V _ t t' n w d x x' e hw hx he`. Take `⟨ψ, hψ, hmon, -⟩` from `GlobalTheory.T.exists_groupIso_cubicalIso_of_tripleMap_id E H V t t' n`. Use `haveI : IsIso n.φ := by`. Rewrite using `[← hψ]`. Conclude with `inferInstanceAs (IsIso ((Over.forget _).map ψ.hom))`.

Establish `hcar` using `(GlobalTheory.T.carriesLinCombGenerator_calculus _ _ t.PP.L t'.PP.L n.φ w t.PP.isLB t'.PP.isLB hw).1`. Establish `hx' : ∀ m, x' m = x m ≫ ψ.hom` using `fun m => by ext1`. Rewrite using `[hx, Over.comp_left, hψ]`. Establish `hfam : ∀ m, (fun J => cφG t ![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)] J ≫ n.φ) = cφG t' ![jptG t' (𝟙 (Sp V)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp V)) d x' m (1 : Fin 2)]` using `fun m => by`. Use function extensionality and compare the values at `J`.

Establish `hv : (![jptG t' (𝟙 (Sp V)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp V)) d x' m (1 : Fin 2)] : Fin 2 → _) = fun k => (![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)] : Fin 2 → _) k ≫ ψ.hom`. Use function extensionality and compare the values at `k`. Apply the tactic sequence `fin_cases k <;> simp [jptG, hx']`. Rewrite using `[hv]`. Simplify using `only [cφG, psum]`.

Rewrite using `[← hψ, ← Over.comp_left, foldr_padd_comp]`. Establish `key : ∀ m, ∃ e' : FrTyG t' (𝟙 (Sp V)) d x' m, e'.IsGen ∧ ∃ c : LB.Gen (LB.LinComb t'.PP.L (fun J => cφG t ![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)] J ≫ n.φ) (cε 2)), c.IsGen ∧ LB.Gen.Corr t'.PP.L _ _ _ _ c e' ∧ Carries t'.PP.L n.φ w (cφG t ![jptG …` using `fun m => by`. Take `⟨c, hc, hcc⟩` from `hcar _ _ (cφG t ![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)]) (cε 2) (e m) (he m)`. Take `⟨e', he', hce⟩` from `exists_corr_of_family_eq t'.PP.L (hfam m) (cε 2) c hc`. Conclude with `⟨e', he', c, hc, hce, hcc⟩`.

Use `choose e' he' using key`. Conclude with `⟨e', he'⟩`.
-/
theorem exists_pushFr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))) (w : LB.Iso t.PP.L (t'.PP.L.pull n.φ)) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m), w.IsGen → (∀ m, (x' m).left = (x m).left ≫ n.φ) → (∀ m, (e m).IsGen) → ∃ e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d x' m, PushFr n w x x' e e' := by
  intro E _ _ _ H V _ t t' n w d x x' e hw hx he
  obtain ⟨ψ, hψ, hmon, -⟩ := GlobalTheory.T.exists_groupIso_cubicalIso_of_tripleMap_id E H V t t' n
  haveI : IsIso n.φ := by
    rw [← hψ]
    exact inferInstanceAs (IsIso ((Over.forget _).map ψ.hom))
  have hcar := (GlobalTheory.T.carriesLinCombGenerator_calculus _ _ t.PP.L t'.PP.L n.φ w t.PP.isLB t'.PP.isLB hw).1
  have hx' : ∀ m, x' m = x m ≫ ψ.hom := fun m => by
    ext1
    rw [hx, Over.comp_left, hψ]
  have hfam : ∀ m, (fun J => cφG t ![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)] J ≫ n.φ) =
      cφG t' ![jptG t' (𝟙 (Sp V)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp V)) d x' m (1 : Fin 2)] := fun m => by
    funext J
    have hv : (![jptG t' (𝟙 (Sp V)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp V)) d x' m (1 : Fin 2)] : Fin 2 → _) =
        fun k => (![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)] : Fin 2 → _) k ≫ ψ.hom := by
      funext k
      fin_cases k <;> simp [jptG, hx']
    rw [hv]
    simp only [cφG, psum]
    rw [← hψ, ← Over.comp_left, foldr_padd_comp]
  have key : ∀ m, ∃ e' : FrTyG t' (𝟙 (Sp V)) d x' m, e'.IsGen ∧ ∃ c : LB.Gen (LB.LinComb t'.PP.L
      (fun J => cφG t ![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)] J ≫ n.φ) (cε 2)),
      c.IsGen ∧ LB.Gen.Corr t'.PP.L _ _ _ _ c e' ∧
      Carries t'.PP.L n.φ w (cφG t ![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)])
        (cε 2) (e m) c := fun m => by
    obtain ⟨c, hc, hcc⟩ := hcar _ _
      (cφG t ![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)]) (cε 2) (e m) (he m)
    obtain ⟨e', he', hce⟩ := exists_corr_of_family_eq t'.PP.L (hfam m) (cε 2) c hc
    exact ⟨e', he', c, hc, hce, hcc⟩
  choose e' he' using key
  exact ⟨e', he'⟩

end GlobalTheory.ChartCmp
