import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsGroupIsoCubicalIsoOfTripleMapIdStatement

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.PushChart

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp [MonObj.one_comp]`. Consider the case `succ m ih => rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, MonObj.mul_comp, ih]`.
-/
theorem prod_ofFn_comp {S : Scheme.{0}} {T G G' : Over S} [GrpObj G] [GrpObj G'] (ψ : G ⟶ G') [IsMonHom ψ]
    {m : ℕ} (u : Fin m → (T ⟶ G)) : (List.ofFn u).prod ≫ ψ = (List.ofFn fun i => u i ≫ ψ).prod := by
  induction m with
  | zero => simp [MonObj.one_comp]
  | succ m ih => rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, MonObj.mul_comp, ih]

/- English proof (translation)
Take `⟨u, hu, hw⟩` from `h`. Use `⟨fun i => u i ≫ ψ, fun i => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hv, Over.comp_left, hu]`. Conclude with `Category.assoc _ _ _`. Rewrite using `[← prod_ofFn_comp, Over.comp_left, hw]`.
-/
theorem isCombAtG_comp {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t t' : SAB H X0}
    (ψ : t.G ⟶ t'.G) [IsMonHom ψ] {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} {v' : Fin m → (Sp (DualNumber S) ⟶ t'.G.left)}
    (hv : ∀ i, v' i = v i ≫ ψ.left) {cf : Fin m → S} {w : Sp (DualNumber S) ⟶ t.G.left}
    (h : IsCombAtG t x0 v cf w) : IsCombAtG t' x0 v' cf (w ≫ ψ.left) := by
  obtain ⟨u, hu, hw⟩ := h
  refine ⟨fun i => u i ≫ ψ, fun i => ?_, ?_⟩
  · rw [hv, Over.comp_left, hu]
    exact Category.assoc _ _ _
  · rw [← prod_ofFn_comp, Over.comp_left, hw]

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Use `⟨fun m => ?_, fun m => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, h1]`. Rewrite using `[← Category.assoc, h2, MonObj.one_comp]`. Introduce `A _ _ aug m hm y hy`.

Establish `hy' : Formalism.L2.Pj.homAt (𝟙 (Sp V)) aug ≫ (y ≫ ψ.inv) = 1`. Rewrite using `[← cancel_mono ψ.hom, MonObj.one_comp]`. Simplify using `using hy`. Take `⟨f, ⟨hf1, hf2⟩, hf3⟩` from `h3 A aug m hm (y ≫ ψ.inv) hy'`. Use `⟨f, ⟨hf1, ?_⟩, fun g hg => hf3 g ⟨hg.1, ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[← Category.assoc, ← hf2]`. Simplify using the standard rewrite rules. Rewrite using `[hg.2]`. Simplify using the standard rewrite rules.
-/
theorem isUnivJ_comp {V : Type} [CommRing V] {G G' : Over (Sp V)} [GrpObj G] [GrpObj G'] (ψ : G ≅ G') [IsMonHom ψ.hom]
    {κ : Type} {z : GlobalTheory.PowGerm.JetPts G κ} (h : GlobalTheory.PowGerm.IsUnivJ G κ z) :
    GlobalTheory.PowGerm.IsUnivJ G' κ (fun m => z m ≫ ψ.hom) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun m => ?_, fun m => ?_, ?_⟩
  · rw [← Category.assoc, h1]
  · rw [← Category.assoc, h2, MonObj.one_comp]
  · intro A _ _ aug m hm y hy
    have hy' : Formalism.L2.Pj.homAt (𝟙 (Sp V)) aug ≫ (y ≫ ψ.inv) = 1 := by
      rw [← cancel_mono ψ.hom, MonObj.one_comp]
      simpa using hy
    obtain ⟨f, ⟨hf1, hf2⟩, hf3⟩ := h3 A aug m hm (y ≫ ψ.inv) hy'
    refine ⟨f, ⟨hf1, ?_⟩, fun g hg => hf3 g ⟨hg.1, ?_⟩⟩
    · rw [← Category.assoc, ← hf2]; simp
    · rw [hg.2]; simp

/- English proof (translation)
Introduce `E _ _ _ H V _ t t' n d x`. Take `⟨ψ, hl, hmon, hact, -⟩` from `GlobalTheory.T.exists_groupIso_cubicalIso_of_tripleMap_id E H V t t' n`. Establish `hc : ∀ (u : Fin d → V) (v : Sp (DualNumber V) ⟶ t.G.left), IsCombAtG t (𝟙 (Sp V)) (dirs x) u v → IsCombAtG t' (𝟙 (Sp V)) (dirs fun m => x m ≫ ψ.hom) u (v ≫ n.φ)`. Introduce `u v h`. Rewrite using `[← hl]`.

Use `isCombAtG_comp ψ.hom _ (fun i => ?_) h` and prove the remaining obligations. Simplify using `only [dirs, Over.comp_left]`. Conclude with `(Category.assoc _ _ _).symm`. Use `⟨fun m => x m ≫ ψ.hom, fun m => ?_, fun h => isUnivJ_comp ψ h, ?_, hc⟩` and prove the remaining obligations. Rewrite using `[Over.comp_left, hl]`.

Introduce `F act κ _ tg uv h`. Use `⟨fun m => ?_, fun m => ?_, fun m => ?_, fun m a => ?_, fun l => hc _ _ (h.tan l), h.basis⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, h.zero, MonObj.one_comp]`. Rewrite using `[← Category.assoc, h.trunc]`. Rewrite using `[← Category.assoc, h.law, MonObj.mul_comp]`.

Simplify using `only [jptG, Category.assoc]`. Rewrite using `[Category.assoc, ← hact, ← Category.assoc, h.act, Category.assoc]`.
-/
theorem pushChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G), ∃ x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G, (∀ m, (x' m).left = (x m).left ≫ n.φ) ∧ (GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x → GlobalTheory.PowGerm.IsUnivJ t'.G (Fin 1 × Fin d) x') ∧ (∀ (F : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V), IsChartG t (𝟙 (Sp V)) d F act tg uv x → IsChartG t' (𝟙 (Sp V)) d F act (fun l => tg l ≫ n.φ) uv x') ∧ ∀ (u : Fin d → V) (v : Sp (DualNumber V) ⟶ t.G.left), IsCombAtG t (𝟙 (Sp V)) (dirs x) u v → IsCombAtG t' (𝟙 (Sp V)) (dirs x') u (v ≫ n.φ) := by
  intro E _ _ _ H V _ t t' n d x
  obtain ⟨ψ, hl, hmon, hact, -⟩ := GlobalTheory.T.exists_groupIso_cubicalIso_of_tripleMap_id E H V t t' n
  have hc : ∀ (u : Fin d → V) (v : Sp (DualNumber V) ⟶ t.G.left), IsCombAtG t (𝟙 (Sp V)) (dirs x) u v →
      IsCombAtG t' (𝟙 (Sp V)) (dirs fun m => x m ≫ ψ.hom) u (v ≫ n.φ) := by
    intro u v h
    rw [← hl]
    refine isCombAtG_comp ψ.hom _ (fun i => ?_) h
    simp only [dirs, Over.comp_left]
    exact (Category.assoc _ _ _).symm
  refine ⟨fun m => x m ≫ ψ.hom, fun m => ?_, fun h => isUnivJ_comp ψ h, ?_, hc⟩
  · rw [Over.comp_left, hl]
  · intro F act κ _ tg uv h
    refine ⟨fun m => ?_, fun m => ?_, fun m => ?_, fun m a => ?_, fun l => hc _ _ (h.tan l), h.basis⟩
    · rw [← Category.assoc, h.zero, MonObj.one_comp]
    · rw [← Category.assoc, h.trunc]
    · rw [← Category.assoc, h.law, MonObj.mul_comp]
      simp only [jptG, Category.assoc]
    · rw [Category.assoc, ← hact, ← Category.assoc, h.act, Category.assoc]

end GlobalTheory.PushChart
