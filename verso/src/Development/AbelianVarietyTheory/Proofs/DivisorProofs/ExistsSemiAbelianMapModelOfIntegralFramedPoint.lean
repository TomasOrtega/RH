import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhiAt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianDvrExtensionsIsoCompatible
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c O _ β Y T io`. Use `letI := io.toAlgebra`. Introduce `y x hx G t' m1 m2`. Establish `tr : ∀ {S S' : Scheme.{0}} {s : SAB H S} {s' : SAB H S'} {f g : S' ⟶ S}, f = g → ∀ m : SABMap s' s f, ∃ m' : SABMap s' s g, m'.φ = m.φ`. Introduce `S S' s s' f g h m`.

Substitute `h` using the available equality. Conclude with `⟨m, rfl⟩`. Take `⟨m1', hm1⟩` from `tr (GlobalTheory.FlagMod.frX_fst y).symm m1`. Take `⟨ρ, hρ⟩` from `sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m0.toSABMap m1'`. Take `⟨a, ha⟩` from `sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m ρ`.

Take `⟨a', ha'⟩` from `tr hx.symm a`. Choose the witnesses or unpack the hypotheses as in `⟨G₂, ⟨pull⟩⟩ : ∃ G₂ : SAB H (Sp T.V), Nonempty (SABMap G₂ Y.t x) := by`. Take `⟨_, _, _, _, _, m, -⟩` from `sabPull ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull x Y.t`. Conclude with `⟨_, ⟨m⟩⟩`. Take `⟨c2, hc2⟩` from `sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ pull a'`.

Take `⟨k, n, hk, hn⟩` from `sab_extensions_iso E H Dw l Xo T.V T.Fr y.x G G₂ t' t' m1 m2 m1 c2`. Establish `hk1 : k.φ = 𝟙 _`. Apply `m1.cart.1.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.id_comp]`. Conclude with `hk`.

Rewrite using `[Category.id_comp]`. Conclude with `k.cart.1.w.trans (Category.comp_id _)`. Take `⟨b, hb⟩` from `sabComp pullCubComp E H _ _ _ _ _ _ _ _ pull n`. Take `⟨ψ, hψ⟩` from `tr (Category.id_comp x) b`. Use `⟨ψ, ρ.φ, by rw [← hρ, hm1], ρ.cart.1.w, ?_⟩` and prove the remaining obligations.

Rewrite using `[← ha, ← ha', hc2, hψ, hb, ← Category.assoc, hn, hk1, Category.id_comp]`.
-/
theorem exists_sabMap_model_of_integral_frPt : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (y : FrPt Xo c T.Fr) (x : Sp T.V ⟶ Y.X), spMap (algebraMap T.V T.Fr) ≫ x = GlobalTheory.FlagMod.frX y ≫ Y.j → ∀ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (m1 : SABMap t' Xo.univ.t y.x) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))), ∃ (ψ : SABMap G Y.t x) (ρ : t'.G.left ⟶ Y.oF.t.G.left), ρ ≫ Y.m0.toSABMap.φ = m1.φ ∧ ρ ≫ Y.oF.t.G.hom = t'.G.hom ≫ GlobalTheory.FlagMod.frX y ∧ ρ ≫ Y.m.φ = m2.φ ≫ ψ.φ := by
  intro E _ _ _ H Dw l Xo c O _ β Y T io
  letI := io.toAlgebra
  intro y x hx G t' m1 m2
  have tr : ∀ {S S' : Scheme.{0}} {s : SAB H S} {s' : SAB H S'} {f g : S' ⟶ S}, f = g → ∀ m : SABMap s' s f,
      ∃ m' : SABMap s' s g, m'.φ = m.φ := by
    intro S S' s s' f g h m
    subst h
    exact ⟨m, rfl⟩
  obtain ⟨m1', hm1⟩ := tr (GlobalTheory.FlagMod.frX_fst y).symm m1
  obtain ⟨ρ, hρ⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m0.toSABMap m1'
  obtain ⟨a, ha⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m ρ
  obtain ⟨a', ha'⟩ := tr hx.symm a
  obtain ⟨G₂, ⟨pull⟩⟩ : ∃ G₂ : SAB H (Sp T.V), Nonempty (SABMap G₂ Y.t x) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull x Y.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨c2, hc2⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ pull a'
  obtain ⟨k, n, hk, hn⟩ := sab_extensions_iso E H Dw l Xo T.V T.Fr y.x G G₂ t' t' m1 m2 m1 c2
  have hk1 : k.φ = 𝟙 _ := by
    apply m1.cart.1.hom_ext
    · rw [Category.id_comp]; exact hk
    · rw [Category.id_comp]; exact k.cart.1.w.trans (Category.comp_id _)
  obtain ⟨b, hb⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ pull n
  obtain ⟨ψ, hψ⟩ := tr (Category.id_comp x) b
  refine ⟨ψ, ρ.φ, by rw [← hρ, hm1], ρ.cart.1.w, ?_⟩
  rw [← ha, ← ha', hc2, hψ, hb, ← Category.assoc, hn, hk1, Category.id_comp]

end GlobalTheory
