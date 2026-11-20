import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAbelianSchemeThick
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianDvrExtensionsIsoCompatible
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenOfRangeGenericSubset
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntChartFrTruncExists

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj

namespace GlobalTheory.GoodChartExt

/- English proof (translation)
Distinguish the cases in `ha : algebraMap T.V T.Fr a = 0`. Rewrite using `[ha]`. Simplify using `[vV]`. Establish `hv : valV T.V (algebraMap T.V T.Fr a) ≤ 1` using `(IsDiscreteValuationRing.maximalIdeal T.V).valuation_le_one a`. Use `(WithZero.log_le_log (valV_ne_zero (V := T.V) ha) one_ne_zero).2 hv` as an intermediate fact.

Simplify using `only [WithZero.log_one] at this`. Simplify using `only [vV]`. Use linear arithmetic over natural numbers and integers.
-/
theorem vV_nonneg (T : CDVR) (a : T.V) : 0 ≤ vV T.V (algebraMap T.V T.Fr a) := by
  by_cases ha : algebraMap T.V T.Fr a = 0
  · rw [ha]; simp [vV]
  · have hv : valV T.V (algebraMap T.V T.Fr a) ≤ 1 :=
      (IsDiscreteValuationRing.maximalIdeal T.V).valuation_le_one a
    have := (WithZero.log_le_log (valV_ne_zero (V := T.V) ha) one_ne_zero).2 hv
    simp only [WithZero.log_one] at this
    simp only [vV]; omega

/- English proof (translation)
Establish `inj` using `IsFractionRing.injective T'.V T'.Fr`. Establish `hm : ∀ a : T.V, ∃ b, algebraMap T'.V T'.Fr b = iT (algebraMap T.V T.Fr a)` using `fun a => Formalism.L2.PjFree.mem_range_of_vV_nonneg (by`. Rewrite using `[hv]; exact mul_nonneg (by exact_mod_cast he.le) (vV_nonneg T a))`. Use `choose f hf using hm`. Set `φ : T.V →+* T'.V` to `{ toFun := f map_one' := inj (by simp [hf]) map_mul' := fun a b => inj (by simp [hf]) map_zero' := inj (by simp [hf]) map_add' := fun a b => inj (by simp [hf]) }`.

Use `⟨φ, RingHom.ext hf, ⟨fun a ha => ?_⟩⟩` and prove the remaining obligations. Take `⟨w, hw⟩` from `ha.exists_right_inv`. Establish `h1 : iT (algebraMap T.V T.Fr a) * algebraMap T'.V T'.Fr w = 1`. Rewrite using `[← hf, ← map_mul]`. Conclude with `(congrArg _ hw).trans (map_one _)`.

Establish `h0 : algebraMap T.V T.Fr a ≠ 0` using `fun h => by simp [h] at h1`. Establish `h2 : iT (algebraMap T.V T.Fr a)⁻¹ = algebraMap T'.V T'.Fr w`. Rewrite using `[map_inv₀]`. Conclude with `(eq_inv_of_mul_eq_one_right h1).symm`. Establish `h3` using `vV_nonneg T' w`.

Rewrite `h3` using `[← h2, hv]`. Establish `h4 : 0 ≤ vV T.V (algebraMap T.V T.Fr a)⁻¹` using `le_of_mul_le_mul_left (by simpa using h3) (by exact_mod_cast he : (0 : ℤ) < e)`. Take `⟨b, hb⟩` from `Formalism.L2.PjFree.mem_range_of_vV_nonneg h4`. Use `IsUnit.of_mul_eq_one b (IsFractionRing.injective T.V T.Fr ?_)` and prove the remaining obligations. Rewrite using `[map_mul, hb, mul_inv_cancel₀ h0, map_one]`.
-/
theorem exists_local_restrict (T T' : CDVR) (iT : T.Fr →+* T'.Fr) (e : ℕ) (he : 0 < e)
    (hv : ∀ a : T.Fr, vV T'.V (iT a) = (e : ℤ) * vV T.V a) :
    ∃ φ : T.V →+* T'.V, (algebraMap T'.V T'.Fr).comp φ = iT.comp (algebraMap T.V T.Fr) ∧ IsLocalHom φ := by
  have inj := IsFractionRing.injective T'.V T'.Fr
  have hm : ∀ a : T.V, ∃ b, algebraMap T'.V T'.Fr b = iT (algebraMap T.V T.Fr a) := fun a =>
    Formalism.L2.PjFree.mem_range_of_vV_nonneg (by
      rw [hv]; exact mul_nonneg (by exact_mod_cast he.le) (vV_nonneg T a))
  choose f hf using hm
  let φ : T.V →+* T'.V :=
    { toFun := f
      map_one' := inj (by simp [hf])
      map_mul' := fun a b => inj (by simp [hf])
      map_zero' := inj (by simp [hf])
      map_add' := fun a b => inj (by simp [hf]) }
  refine ⟨φ, RingHom.ext hf, ⟨fun a ha => ?_⟩⟩
  obtain ⟨w, hw⟩ := ha.exists_right_inv
  have h1 : iT (algebraMap T.V T.Fr a) * algebraMap T'.V T'.Fr w = 1 := by
    rw [← hf, ← map_mul]; exact (congrArg _ hw).trans (map_one _)
  have h0 : algebraMap T.V T.Fr a ≠ 0 := fun h => by simp [h] at h1
  have h2 : iT (algebraMap T.V T.Fr a)⁻¹ = algebraMap T'.V T'.Fr w := by
    rw [map_inv₀]; exact (eq_inv_of_mul_eq_one_right h1).symm
  have h3 := vV_nonneg T' w
  rw [← h2, hv] at h3
  have h4 : 0 ≤ vV T.V (algebraMap T.V T.Fr a)⁻¹ :=
    le_of_mul_le_mul_left (by simpa using h3) (by exact_mod_cast he : (0 : ℤ) < e)
  obtain ⟨b, hb⟩ := Formalism.L2.PjFree.mem_range_of_vV_nonneg h4
  refine IsUnit.of_mul_eq_one b (IsFractionRing.injective T.V T.Fr ?_)
  rw [map_mul, hb, mul_inv_cancel₀ h0, map_one]

/- English proof (translation)
Take `⟨E₀, -, -, -, -, ⟨d⟩⟩` from `GlobalTheory.gtCoord_isGt V _ D.toPre 0 G ⟨U.gt 0⟩`. Set `g : V ⧸ (maximalIdeal V) ^ (0 + 1) →+* ResidueField V'` to `(ResidueField.map φ).comp (Ideal.Quotient.factor (Ideal.pow_le_self (by norm_num)))`. Establish `hr : spMap g ≫ thick V (maximalIdeal V) 0 = spMap (residue V') ≫ spMap φ`. Rewrite using `[← Spec.map_comp, ← Spec.map_comp]`. Use `congr 1`.

Take `⟨j, hj, -⟩` from `grpPullback_iso (((isGrpPullback_pullback (thickObj V (maximalIdeal V) 0 G) (spMap g)).comp (isGrpPullback_pullback G (thick V (maximalIdeal V) 0))).congr hr rfl) ((isGrpPullback_pullback G' (spMap (residue V'))).comp h)`. Conclude with `⟨_, isGt_of_iso j (GtBaseChange.isGt_extBC (spMap g) E₀ _ d)⟩`.
-/
theorem split_of_pullback {V V' : Type} [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing V'] [IsLocalRing V']
    (φ : V →+* V') [IsLocalHom φ] {D : DegData V (maximalIdeal V)} {A : PolAV (Sp (FractionRing V))}
    {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G)
    {G' : Over (Sp V')} [GrpObj G'] {ψ : G'.left ⟶ G.left} (h : IsGrpPullback G' G (spMap φ) ψ) :
    ∃ S : SplitExt (Sp (ResidueField V')), S.IsGt ((Over.pullback (spMap (residue V'))).obj G') := by
  obtain ⟨E₀, -, -, -, -, ⟨d⟩⟩ := GlobalTheory.gtCoord_isGt V _ D.toPre 0 G ⟨U.gt 0⟩
  let g : V ⧸ (maximalIdeal V) ^ (0 + 1) →+* ResidueField V' :=
    (ResidueField.map φ).comp (Ideal.Quotient.factor (Ideal.pow_le_self (by norm_num)))
  have hr : spMap g ≫ thick V (maximalIdeal V) 0 = spMap (residue V') ≫ spMap φ := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  obtain ⟨j, hj, -⟩ := grpPullback_iso (((isGrpPullback_pullback (thickObj V (maximalIdeal V) 0 G)
    (spMap g)).comp (isGrpPullback_pullback G (thick V (maximalIdeal V) 0))).congr hr rfl)
    ((isGrpPullback_pullback G' (spMap (residue V'))).comp h)
  exact ⟨_, isGt_of_iso j (GtBaseChange.isGt_extBC (spMap g) E₀ _ d)⟩

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c _ hstar T io y C hC T' iT e y' hy`. Take `⟨-, P, -⟩` from `hC`. Take `⟨he, hv, ψ, hψ, hx, -⟩` from `hy`. Establish `hx' : xOf y' = spMap iT ≫ xOf y` using `hx.trans (congrArg (fun r => spMap r ≫ xOf y) hψ)`. Take `⟨C', hC'⟩` from `GlobalTheory.IntChartTrunc.intChart_frTrunc_exists E H Dw l Xo c hstar T' (iT.comp io) y'`.

Use `⟨C', hC', ?_⟩` and prove the remaining obligations. Take `⟨φ, hφ, hloc⟩` from `exists_local_restrict T T' iT e he hv`. Establish `hsq : spMap iT ≫ spMap (algebraMap T.V T.Fr) = spMap (algebraMap T'.V T'.Fr) ≫ spMap φ`. Rewrite using `[← spMap_comp, ← spMap_comp, hφ]`. Establish `tr : ∀ {S S' : Scheme.{0}} {s : SAB H S} {s' : SAB H S'} {f g : S' ⟶ S}, f = g → SABMap s' s f → Nonempty (SABMap s' s g)`.

Introduce `S S' s s' f g h m`. Substitute `h` using the available equality. Conclude with `⟨m⟩`. Choose the witnesses or unpack the hypotheses as in `⟨G₂, ⟨m⟩⟩ : ∃ G₂ : SAB H (Sp T'.V), Nonempty (SABMap G₂ C.I.G (spMap φ)) := by`. Take `⟨_, _, _, _, _, m, -⟩` from `sabPull Out.CubePf.cubePull (spMap φ) C.I.G`.

Conclude with `⟨_, ⟨m⟩⟩`. Choose the witnesses or unpack the hypotheses as in `⟨t₂, ⟨p⟩⟩ : ∃ t₂ : SAB H (Sp T'.Fr), Nonempty (SABMap t₂ C.I.t' (spMap iT)) := by`. Take `⟨_, _, _, _, _, m, -⟩` from `sabPull Out.CubePf.cubePull (spMap iT) C.I.t'`. Conclude with `⟨_, ⟨m⟩⟩`. Take `⟨a₁, -⟩` from `sabComp pullCubComp E H _ _ _ _ _ _ _ _ C.I.m1 p`.

Take `⟨n₁⟩` from `tr hx'.symm a₁`. Take `⟨a₂, -⟩` from `sabComp pullCubComp E H _ _ _ _ _ _ _ _ C.I.m2 p`. Take `⟨b₂⟩` from `tr hsq a₂`. Take `⟨n₂, -⟩` from `sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m b₂`. Take `⟨-, n, -⟩` from `GlobalTheory.sab_extensions_iso E H Dw l Xo T'.V T'.Fr (xOf y') C'.I.G G₂ C'.I.t' t₂ C'.I.m1 C'.I.m2 n₁ n₂`.

Take `⟨a₃, -⟩` from `sabComp pullCubComp E H _ _ _ _ _ _ _ _ m n`. Take `⟨k⟩` from `tr (Category.id_comp _) a₃`. Establish `hp` using `GlobalTheory.UnifAfterExt.polAt_of_sabMap k C.I.m2 C.I.m1 Xo.univ.proper Xo.univ.ample Xo.univ.ktriv (jK T'.V) (spMap iT) hsq.symm`. Take `⟨-, P', -, hP'⟩` from `GlobalTheory.UnifAfterExt.isOpen_and_uniformised T'.V inferInstance C'.I.G hp (split_of_pullback φ P.U.toUnifPre k.cart)`. Conclude with `⟨P', hP'⟩`.
-/
theorem exists_good_chart_ext : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), Good3 C → ∀ (T' : CDVR) (iT : T.Fr →+* T'.Fr) (e : ℕ) (y' : IntFr Xo c T' (iT.comp io)), IsExt y iT e y' → ∃ C' : IntegralChartA3 Xo c T' (iT.comp io) y', Good3 C' := by
  intro E _ _ _ H Dw l Xo c _ hstar T io y C hC T' iT e y' hy
  obtain ⟨-, P, -⟩ := hC
  obtain ⟨he, hv, ψ, hψ, hx, -⟩ := hy
  have hx' : xOf y' = spMap iT ≫ xOf y := hx.trans (congrArg (fun r => spMap r ≫ xOf y) hψ)
  obtain ⟨C', hC'⟩ := GlobalTheory.IntChartTrunc.intChart_frTrunc_exists E H Dw l Xo c hstar T' (iT.comp io) y'
  refine ⟨C', hC', ?_⟩
  obtain ⟨φ, hφ, hloc⟩ := exists_local_restrict T T' iT e he hv
  have hsq : spMap iT ≫ spMap (algebraMap T.V T.Fr) = spMap (algebraMap T'.V T'.Fr) ≫ spMap φ := by
    rw [← spMap_comp, ← spMap_comp, hφ]
  have tr : ∀ {S S' : Scheme.{0}} {s : SAB H S} {s' : SAB H S'} {f g : S' ⟶ S}, f = g → SABMap s' s f →
      Nonempty (SABMap s' s g) := by
    intro S S' s s' f g h m
    subst h
    exact ⟨m⟩
  obtain ⟨G₂, ⟨m⟩⟩ : ∃ G₂ : SAB H (Sp T'.V), Nonempty (SABMap G₂ C.I.G (spMap φ)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap φ) C.I.G
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨t₂, ⟨p⟩⟩ : ∃ t₂ : SAB H (Sp T'.Fr), Nonempty (SABMap t₂ C.I.t' (spMap iT)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap iT) C.I.t'
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨a₁, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ C.I.m1 p
  obtain ⟨n₁⟩ := tr hx'.symm a₁
  obtain ⟨a₂, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ C.I.m2 p
  obtain ⟨b₂⟩ := tr hsq a₂
  obtain ⟨n₂, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m b₂
  obtain ⟨-, n, -⟩ := GlobalTheory.sab_extensions_iso E H Dw l Xo T'.V T'.Fr (xOf y') C'.I.G G₂ C'.I.t' t₂ C'.I.m1 C'.I.m2 n₁ n₂
  obtain ⟨a₃, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m n
  obtain ⟨k⟩ := tr (Category.id_comp _) a₃
  have hp := GlobalTheory.UnifAfterExt.polAt_of_sabMap k C.I.m2 C.I.m1 Xo.univ.proper Xo.univ.ample Xo.univ.ktriv
    (jK T'.V) (spMap iT) hsq.symm
  obtain ⟨-, P', -, hP'⟩ := GlobalTheory.UnifAfterExt.isOpen_and_uniformised T'.V inferInstance C'.I.G hp
    (split_of_pullback φ P.U.toUnifPre k.cart)
  exact ⟨P', hP'⟩

end GlobalTheory.GoodChartExt
