import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliFiniteSurjectiveOverGenericFamily
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.Reg GlobalTheory.FlagMod

noncomputable section

namespace GlobalTheory.MChartDown

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `⟨m, rfl⟩`.
-/
theorem sabMap_base_congr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f f' : S' ⟶ S} (m : SABMap t' t f) (h : f = f') :
    ∃ m' : SABMap t' t f', m'.φ = m.φ := by
  subst h; exact ⟨m, rfl⟩

/- English proof (translation)
Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR]`.
-/
theorem dualMapR_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (g : R →+* R') (f : R' →+* R'') :
    ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (f.comp g) =
      (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f).comp (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR g) := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR]

/- English proof (translation)
Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem dualMapR_comp_algebraMap {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') :
    (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f).comp (algebraMap R (DualNumber R)) =
      (algebraMap R' (DualNumber R')).comp f := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

/- English proof (translation)
Rewrite using `[spMap, spMap, spMap, ← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (g : R →+* R') (f : R' →+* R'') :
    spMap (f.comp g) = spMap f ≫ spMap g := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c O O' _ _ β β' Y Y' v n M U' hU' hle`. Set `g : Γ(Y.X, M.U) →+* Γ(Y'.X, U')` to `(v.appLE M.U U' hle).hom`. Establish `hsq : spMap g ≫ M.hU.fromSpec = hU'.fromSpec ≫ v` using `IsAffineOpen.SpecMap_appLE_fromSpec v M.hU hU' hle`. Take `⟨t₀, ⟨m₀⟩⟩` from `GlobalTheory.ModFam.exists_sabPull hU'.fromSpec Y'.t`. Take `⟨k₀, hk₀⟩` from `GlobalTheory.ObjMaps.exists_sab_comp n m₀`.

Take `⟨k₁, hk₁⟩` from `sabMap_base_congr k₀ hsq.symm`. Take `⟨u, hu, -, -⟩` from `M.lie _ g t₀ k₁`. Use `⟨M.n, fun j => (u j).left ≫ m₀.φ, fun a => (M.ρ a).map g, ?_⟩` and prove the remaining obligations. Introduce `R' _ f t' m`. Take `⟨p₀, hp₀⟩` from `GlobalTheory.ObjMaps.exists_sab_comp n m`.

Establish `hb : (spMap f ≫ hU'.fromSpec) ≫ v = spMap (f.comp g) ≫ M.hU.fromSpec`. Rewrite using `[Category.assoc, ← hsq, spMap_comp, Category.assoc]`. Take `⟨p₁, hp₁⟩` from `sabMap_base_congr p₀ hb`. Take `⟨v', hv', hB, hC⟩` from `M.lie R' (f.comp g) t' p₁`. Use `⟨v', fun j => ?_, hB, fun a j => hC a j⟩` and prove the remaining obligations.

Apply `n.cart.1.hom_ext` to reduce the goal to its premises. Establish `e1` using `hv' j`. Establish `e2` using `hu j`. Rewrite `e1` using `[hp₁, hp₀]`. Rewrite `e2` using `[hk₁, hk₀]`.

Simplify using `only [Category.assoc] at e1 e2 ⊢`. Rewrite using `[e1, e2, dualMapR_comp, spMap_comp, Category.assoc]`. Establish `w1` using `m.cart.1.w`. Establish `w0` using `m₀.cart.1.w`. Establish `o1` using `Over.w (v' j)`.

Establish `o0` using `Over.w (u j)`. Simplify using `only [Category.assoc] at w1 w0 ⊢`. Rewrite using `[w1, w0, reassoc_of% o1, reassoc_of% o0]`. Simplify using `only [← Category.assoc]`. Use `congr 1`.

Simplify using `only [epsR, Over.mk_hom, ← spMap_comp, dualMapR_comp_algebraMap]`.
-/
theorem lieDown : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F} (Y : Model Xo c β) (Y' : Model Xo c β') (v : Y'.X ⟶ Y.X), SABMap Y'.t Y.t v → ∀ (M : MChart Y) (U' : Y'.X.Opens) (hU' : IsAffineOpen U'), U' ≤ v ⁻¹ᵁ M.U → ∃ (k : ℕ) (v₀ : Fin k → (Sp (DualNumber Γ(Y'.X, U')) ⟶ Y'.t.G.left)) (ρ : 𝓞 E → Matrix (Fin k) (Fin k) Γ(Y'.X, U')), ∀ (R' : Type) [CommRing R'] (f : Γ(Y'.X, U') →+* R') (t' : SAB H (Sp R')) (m : SABMap t' Y'.t (spMap f ≫ hU'.fromSpec)), ∃ v' : Fin k → (epsR R' ⟶ t'.G), (∀ j, (v' j).left ≫ m.φ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ v₀ j) ∧ IsLieBasis v' ∧ ∀ a j, IsLieComb (fun i => f (ρ a i j)) v' (v' j ≫ t'.act.act a) := by
  intro E _ _ _ H D l Xo c O O' _ _ β β' Y Y' v n M U' hU' hle
  let g : Γ(Y.X, M.U) →+* Γ(Y'.X, U') := (v.appLE M.U U' hle).hom
  have hsq : spMap g ≫ M.hU.fromSpec = hU'.fromSpec ≫ v := IsAffineOpen.SpecMap_appLE_fromSpec v M.hU hU' hle
  obtain ⟨t₀, ⟨m₀⟩⟩ := GlobalTheory.ModFam.exists_sabPull hU'.fromSpec Y'.t
  obtain ⟨k₀, hk₀⟩ := GlobalTheory.ObjMaps.exists_sab_comp n m₀
  obtain ⟨k₁, hk₁⟩ := sabMap_base_congr k₀ hsq.symm
  obtain ⟨u, hu, -, -⟩ := M.lie _ g t₀ k₁
  refine ⟨M.n, fun j => (u j).left ≫ m₀.φ, fun a => (M.ρ a).map g, ?_⟩
  intro R' _ f t' m
  obtain ⟨p₀, hp₀⟩ := GlobalTheory.ObjMaps.exists_sab_comp n m
  have hb : (spMap f ≫ hU'.fromSpec) ≫ v = spMap (f.comp g) ≫ M.hU.fromSpec := by
    rw [Category.assoc, ← hsq, spMap_comp, Category.assoc]
  obtain ⟨p₁, hp₁⟩ := sabMap_base_congr p₀ hb
  obtain ⟨v', hv', hB, hC⟩ := M.lie R' (f.comp g) t' p₁
  refine ⟨v', fun j => ?_, hB, fun a j => hC a j⟩
  apply n.cart.1.hom_ext
  · have e1 := hv' j
    have e2 := hu j
    rw [hp₁, hp₀] at e1
    rw [hk₁, hk₀] at e2
    simp only [Category.assoc] at e1 e2 ⊢
    rw [e1, e2, dualMapR_comp, spMap_comp, Category.assoc]
  · have w1 := m.cart.1.w
    have w0 := m₀.cart.1.w
    have o1 := Over.w (v' j)
    have o0 := Over.w (u j)
    simp only [Category.assoc] at w1 w0 ⊢
    rw [w1, w0, reassoc_of% o1, reassoc_of% o0]
    simp only [← Category.assoc]
    congr 1
    simp only [epsR, Over.mk_hom, ← spMap_comp, dualMapR_comp_algebraMap]

end GlobalTheory.MChartDown
