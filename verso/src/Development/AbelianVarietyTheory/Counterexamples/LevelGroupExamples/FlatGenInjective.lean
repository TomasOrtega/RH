import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IntChartCheck

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h choose a ha using h`. Conclude with `⟨a, MvPowerSeries.ext fun e => (ha e).symm.trans (MvPowerSeries.coeff_map _ _ _).symm⟩`. Introduce and unpack `⟨g, rfl⟩ e`. Conclude with `⟨MvPowerSeries.coeff e g, (MvPowerSeries.coeff_map _ _ _).symm⟩`.
-/
theorem isIntPS_iff (T : CDVR) {n d : ℕ} (f : Germ.PS T.Fr n d) :
    IsIntPS T f ↔ ∃ g : Germ.PS T.V n d, f = MvPowerSeries.map (algebraMap T.V T.Fr) g := by
  constructor
  · intro h
    choose a ha using h
    exact ⟨a, MvPowerSeries.ext fun e => (ha e).symm.trans (MvPowerSeries.coeff_map _ _ _).symm⟩
  · rintro ⟨g, rfl⟩ e
    exact ⟨MvPowerSeries.coeff e g, (MvPowerSeries.coeff_map _ _ _).symm⟩

/- English proof (translation)
Take `⟨a⟩` from `a`. Take `⟨b⟩` from `b`. Use `congr 1`. Use function extensionality and compare the values at `j`. Establish `h1` using `congrFun (congrArg LB.Gen.s h) (fun k _ => j k)`.

Establish `hU : LB.wchart (L.pull F) φ (fun k _ => j k) = LB.wchart L (fun k => φ k ≫ F) j`. Use `le_antisymm (wchart_pull_le L F φ _) ?_` and prove the remaining obligations. Introduce `y hy`. Use `Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => ?_` and prove the remaining obligations. Conclude with `Set.mem_iInter.1 hy k`.

Establish `h2` using `congrArg (res hU.ge) h1`. Establish `key : ∀ u : Γ(Y, LB.wchart L (fun k => φ k ≫ F) j)ˣ, res hU.ge (res hU.le u) = u` using `fun u => by`. Use `ext`. Simplify using `only [res, Units.coe_map, MonoidHom.coe_coe, ← CommRingCat.comp_apply, ← Functor.map_comp]`. Use `erw [show ((homOfLE hU.le).op ≫ (homOfLE hU.ge).op) = 𝟙 _ from Subsingleton.elim _ _, Y.presheaf.map_id]`.

Both sides reduce to the same expression. Conclude with `(key (a j)).symm.trans (h2.trans (key (b j)))`.
-/
theorem flatGen_injective {X X' Y : Scheme.{0}} (L : LB X) (F : X' ⟶ X) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X')) (ε : K → ℤ) (a b : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε))
    (h : flatGen L F φ ε a = flatGen L F φ ε b) : a = b := by
  obtain ⟨a⟩ := a
  obtain ⟨b⟩ := b
  congr 1
  funext j
  have h1 := congrFun (congrArg LB.Gen.s h) (fun k _ => j k)
  have hU : LB.wchart (L.pull F) φ (fun k _ => j k) = LB.wchart L (fun k => φ k ≫ F) j := by
    refine le_antisymm (wchart_pull_le L F φ _) ?_
    intro y hy
    refine Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => ?_
    exact Set.mem_iInter.1 hy k
  have h2 := congrArg (res hU.ge) h1
  have key : ∀ u : Γ(Y, LB.wchart L (fun k => φ k ≫ F) j)ˣ,
      res hU.ge (res hU.le u) = u := fun u => by
    ext
    simp only [res, Units.coe_map, MonoidHom.coe_coe, ← CommRingCat.comp_apply, ← Functor.map_comp]
    erw [show ((homOfLE hU.le).op ≫ (homOfLE hU.ge).op) = 𝟙 _ from Subsingleton.elim _ _, Y.presheaf.map_id]
    rfl
  exact (key (a j)).symm.trans (h2.trans (key (b j)))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

/- English proof (translation)
Take `⟨⟨h1, h2, h3, h4, h5, h6, -⟩, -⟩` from `C.gen`. Conclude with `⟨fun j => (isIntPS_iff T _).2 ⟨_, h1 j⟩, fun a j => (isIntPS_iff T _).2 ⟨_, h2 a j⟩, (isIntPS_iff T _).2 ⟨_, h3⟩, (isIntPS_iff T _).2 ⟨_, h4⟩, (isIntPS_iff T _).2 ⟨_, h5⟩, fun a => (isIntPS_iff T _).2 ⟨_, h6 a⟩⟩`.
-/
theorem series_integral (C : IntegralChartA3 Xo c T io y) :
    letI := io.toAlgebra
    (∀ j, IsIntPS T (C.ch.B.G.F j)) ∧ (∀ a j, IsIntPS T (C.ch.B.A.act a j)) ∧ IsIntPS T C.ch.B.ph1 ∧
      IsIntPS T C.ch.B.ph2 ∧ IsIntPS T C.ch.B.sy ∧ ∀ a, IsIntPS T (C.ch.B.ad a) := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, -⟩, -⟩ := C.gen
  exact ⟨fun j => (isIntPS_iff T _).2 ⟨_, h1 j⟩, fun a j => (isIntPS_iff T _).2 ⟨_, h2 a j⟩,
    (isIntPS_iff T _).2 ⟨_, h3⟩, (isIntPS_iff T _).2 ⟨_, h4⟩, (isIntPS_iff T _).2 ⟨_, h5⟩,
    fun a => (isIntPS_iff T _).2 ⟨_, h6 a⟩⟩

/- English proof (translation)
Use `letI := io.toAlgebra`. Take `⟨⟨h1, h2, -⟩, -⟩` from `C.gen`. Use `⟨fun j => ?_, fun a j => ?_⟩` and prove the remaining obligations. Use `C.ch.B.G.const j` as an intermediate fact. Rewrite `this` using `[h1 j, MvPowerSeries.constantCoeff_map]`.

Conclude with `(map_eq_zero_iff _ (IsFractionRing.injective T.V T.Fr)).1 this`. Use `C.ch.B.A.const a j` as an intermediate fact. Rewrite `this` using `[h2 a j, MvPowerSeries.constantCoeff_map]`. Conclude with `(map_eq_zero_iff _ (IsFractionRing.injective T.V T.Fr)).1 this`.
-/
theorem const_zero (C : IntegralChartA3 Xo c T io y) :
    (∀ j, MvPowerSeries.constantCoeff (C.FT j) = 0) ∧ ∀ a j, MvPowerSeries.constantCoeff (C.actT a j) = 0 := by
  letI := io.toAlgebra
  obtain ⟨⟨h1, h2, -⟩, -⟩ := C.gen
  refine ⟨fun j => ?_, fun a j => ?_⟩
  · have := C.ch.B.G.const j
    rw [h1 j, MvPowerSeries.constantCoeff_map] at this
    exact (map_eq_zero_iff _ (IsFractionRing.injective T.V T.Fr)).1 this
  · have := C.ch.B.A.const a j
    rw [h2 a j, MvPowerSeries.constantCoeff_map] at this
    exact (map_eq_zero_iff _ (IsFractionRing.injective T.V T.Fr)).1 this

/- English proof (translation)
Use `letI := io.toAlgebra`. Set `f : (Lt1 Dw → T.Fr) →ₗ[T.Fr] (Fin C.ch.d → T.Fr)` to `{ toFun := fun a j => ∑ ℓ, a ℓ * C.ch.uvec ℓ j map_add' := fun a b => by funext j; simp [add_mul, Finset.sum_add_distrib] map_smul' := fun r a => by funext j; simp [Finset.mul_sum, _root_.mul_assoc] }`. Establish `hb : Function.Bijective f` using `(Function.bijective_iff_existsUnique f).2 fun v => by`. Take `⟨a, ha, hu⟩` from `C.ch.chart.basis v`. Conclude with `⟨a, funext ha, fun b hb => hu b (congrFun hb)⟩`.

Use `(LinearEquiv.ofBijective f hb).finrank_eq` as an intermediate fact. Simplify using `using this.symm`.
-/
theorem dim_eq (C : IntegralChartA3 Xo c T io y) : chD C.ch = Fintype.card (Lt1 Dw) := by
  letI := io.toAlgebra
  let f : (Lt1 Dw → T.Fr) →ₗ[T.Fr] (Fin C.ch.d → T.Fr) :=
    { toFun := fun a j => ∑ ℓ, a ℓ * C.ch.uvec ℓ j
      map_add' := fun a b => by funext j; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun r a => by funext j; simp [Finset.mul_sum, _root_.mul_assoc] }
  have hb : Function.Bijective f := (Function.bijective_iff_existsUnique f).2 fun v => by
    obtain ⟨a, ha, hu⟩ := C.ch.chart.basis v
    exact ⟨a, funext ha, fun b hb => hu b (congrFun hb)⟩
  have := (LinearEquiv.ofBijective f hb).finrank_eq
  simpa using this.symm

end GlobalTheory.IntChartCheck
