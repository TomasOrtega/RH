import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GtPtsVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefiningDegenerationDataTauCoordinateUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TauCoordinateEqUnitMulPsiQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonomialTauOfPerFactor
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SiegelSmoothOfRelativeDimensionCharZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfSubsingleton

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.TraitTau

open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues Formalism.L2.Pj

/- English proof (translation)
Take `⟨u, hu⟩ : ∃ u : LB.Gen (LB.LinComb Q.M.L (lamPts (Q.c a) (Q.c b)) negε), u.IsGen` from `DVR.exists_gen_of_local (V := R) Q.M.L Q.M.isLB _ _`. Establish `hφ : lamPts (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b) = fun k => (toUnit (TK R)).left ≫ lamPts (Q.c a) (Q.c b) k`. Use function extensionality and compare the values at `k`. Use `fin_cases k`. Conclude with `(congrArg (fun q : TK R ⟶ Q.B => q.left) (MonObj.comp_mul (toUnit (TK R)) (Q.c a) (Q.c b))).symm`.

Both sides reduce to the same expression. Both sides reduce to the same expression. Conclude with `(congrArg (fun q : TK R ⟶ Q.B => q.left) (MonObj.comp_one (toUnit (TK R)))).symm`. Take `⟨ρ, hρ⟩` from `ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_ratio Q.M.isLB hφ (Q.tau a b) (LB.pullGen Q.M.L _ negε u (toUnit (TK R)).left) (Q.tau_gen a b) (DVR.pullGen_isGen _ _ _ _ hu _)`. Set `k : (FractionRing R)ˣ` to `Units.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom.toMonoidHom ρ`.

Establish `hk : unitOn k = ρ` using `Units.ext ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom_inv_id_apply ρ.val)`. Use `⟨k, u, hu, fun z J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[hρ _ _ z J hJ, val_pull hJ, Category.id_comp, hk]`.
-/
theorem exists_tauCoord {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (Q : Data R) (a b : Q.X) :
    ∃ k, Q.TauCoord a b k := by
  obtain ⟨u, hu⟩ : ∃ u : LB.Gen (LB.LinComb Q.M.L (lamPts (Q.c a) (Q.c b)) negε), u.IsGen :=
    DVR.exists_gen_of_local (V := R) Q.M.L Q.M.isLB _ _
  have hφ : lamPts (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b) =
      fun k => (toUnit (TK R)).left ≫ lamPts (Q.c a) (Q.c b) k := by
    funext k
    fin_cases k
    · exact (congrArg (fun q : TK R ⟶ Q.B => q.left) (MonObj.comp_mul (toUnit (TK R)) (Q.c a) (Q.c b))).symm
    · rfl
    · rfl
    · exact (congrArg (fun q : TK R ⟶ Q.B => q.left) (MonObj.comp_one (toUnit (TK R)))).symm
  obtain ⟨ρ, hρ⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_ratio Q.M.isLB hφ (Q.tau a b)
    (LB.pullGen Q.M.L _ negε u (toUnit (TK R)).left) (Q.tau_gen a b) (DVR.pullGen_isGen _ _ _ _ hu _)
  let k : (FractionRing R)ˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom.toMonoidHom ρ
  have hk : unitOn k = ρ := Units.ext ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom_inv_id_apply ρ.val)
  refine ⟨k, u, hu, fun z J hJ => ?_⟩
  rw [hρ _ _ z J hJ, val_pull hJ, Category.id_comp, hk]

/- English proof (translation)
Introduce `(a : D.X) (b : D.X)`. Take `⟨k, hk⟩` from `exists_tauCoord (Wit.ofDeg D hB) a b`. Take `⟨x, hx⟩` from `GlobalTheory.PsiFromTau.exists_isTauCoord R D a b`. Take `⟨u₁, hu₁⟩` from `GlobalTheory.RefTauCoord.main R R (Wit.ofDeg D hB) (RingHom.id R) D (AddEquiv.refl _) Function.injective_id (Wit.refines_ofDeg D hB) a b k hk x hx`. Establish `hl : ∀ σ : FractionRing R →+* FractionRing R, (∀ r, σ (algebraMap R (FractionRing R) r) = algebraMap R (FractionRing R) (RingHom.id R r)) → ∀ y, σ y = y` using `fun σ hσ => RingHom.congr_fun (IsLocalization.ringHom_ext (nonZeroDivisors R) (k := RingHom.id _) (RingHom.ext hσ))`.

Rewrite `hu₁` using `[hl _ (fun r => by rw [IsFractionRing.lift_algebraMap]; rfl)]`. Take `⟨_, _, -, ha⟩` from `h a`. Take `⟨_, _, -, hb⟩` from `h b`. Take `⟨_, _, -, hab⟩` from `h (a + b)`. Take `⟨u₃, hu₃⟩` from `h.tau hs ht ha hb hab`.

Take `⟨xa, ha₁, ha₂⟩` from `(GlobalTheory.PeriodFormCompare.psiCoord_iff D a _).1 ha`. Take `⟨xb, hb₁, hb₂⟩` from `(GlobalTheory.PeriodFormCompare.psiCoord_iff D b _).1 hb`. Take `⟨xab, hab₁, hab₂⟩` from `(GlobalTheory.PeriodFormCompare.psiCoord_iff D (a + b) _).1 hab`. Take `⟨u₂, hu₂⟩` from `GlobalTheory.TauCoordQuot.main R D a b x xab xa xb hx hab₁ ha₁ hb₁`. Rewrite `hu₃` using `[← ha₂, ← hb₂, ← hab₂]`.

Establish `hc` using `Taut.tauCoord_mul_unit hk (u₁ * u₂⁻¹ * u₃⁻¹)`. Use `⟨k * Units.map (algebraMap R (FractionRing R) : R →* FractionRing R) (u₁ * u₂⁻¹ * u₃⁻¹), ?_, hc⟩` and prove the remaining obligations. Use `Eq.trans (b := ∏ i, algebraMap R (FractionRing R) (t i) ^ β i a b) ?_ rfl` and prove the remaining obligations. Use `clear hc hk hl`. Establish `hu : ∀ u : Rˣ, algebraMap R (FractionRing R) (u : R) ≠ 0` using `fun u => (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 u.ne_zero`.

Establish `e : algebraMap R (FractionRing R) u₁ * (k : FractionRing R) = algebraMap R (FractionRing R) u₂ * (algebraMap R (FractionRing R) u₃ * ∏ i, algebraMap R (FractionRing R) (t i) ^ β i a b)`. Rewrite using `[← hu₃, ← hu₁, hu₂, div_eq_mul_inv, mul_inv]`. Expand and normalize the polynomial expressions, which then agree. Establish `h₂` using `hu u₂`. Establish `h₃` using `hu u₃`.

Generalize the expression as in `∏ i, algebraMap R (FractionRing R) (t i) ^ β i a b = P at e ⊢`. Rewrite using `[Units.val_mul, Units.coe_map, MonoidHom.coe_coe]`. Simplify using `only [Units.val_mul, map_mul, map_units_inv]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `e`.
-/
theorem isMonomialTau_ofDeg {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (hB : D.TauBimult) {m : ℕ}
    {t : Fin m → R} {β : Fin m → LinearMap.BilinForm ℤ D.X} (h : IsMonomial D t β) (hs : ∀ i y z, β i y z = β i z y)
    (ht : ∀ i, t i ≠ 0) : (Wit.ofDeg D hB).IsMonomialTau t β := by
  intro (a : D.X) (b : D.X)
  obtain ⟨k, hk⟩ := exists_tauCoord (Wit.ofDeg D hB) a b
  obtain ⟨x, hx⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D a b
  obtain ⟨u₁, hu₁⟩ := GlobalTheory.RefTauCoord.main R R (Wit.ofDeg D hB) (RingHom.id R) D (AddEquiv.refl _) Function.injective_id
    (Wit.refines_ofDeg D hB) a b k hk x hx
  have hl : ∀ σ : FractionRing R →+* FractionRing R,
      (∀ r, σ (algebraMap R (FractionRing R) r) = algebraMap R (FractionRing R) (RingHom.id R r)) → ∀ y, σ y = y :=
    fun σ hσ => RingHom.congr_fun (IsLocalization.ringHom_ext (nonZeroDivisors R) (k := RingHom.id _) (RingHom.ext hσ))
  rw [hl _ (fun r => by rw [IsFractionRing.lift_algebraMap]; rfl)] at hu₁
  obtain ⟨_, _, -, ha⟩ := h a
  obtain ⟨_, _, -, hb⟩ := h b
  obtain ⟨_, _, -, hab⟩ := h (a + b)
  obtain ⟨u₃, hu₃⟩ := h.tau hs ht ha hb hab
  obtain ⟨xa, ha₁, ha₂⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D a _).1 ha
  obtain ⟨xb, hb₁, hb₂⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D b _).1 hb
  obtain ⟨xab, hab₁, hab₂⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D (a + b) _).1 hab
  obtain ⟨u₂, hu₂⟩ := GlobalTheory.TauCoordQuot.main R D a b x xab xa xb hx hab₁ ha₁ hb₁
  rw [← ha₂, ← hb₂, ← hab₂] at hu₃
  have hc := Taut.tauCoord_mul_unit hk (u₁ * u₂⁻¹ * u₃⁻¹)
  refine ⟨k * Units.map (algebraMap R (FractionRing R) : R →* FractionRing R) (u₁ * u₂⁻¹ * u₃⁻¹), ?_, hc⟩
  refine Eq.trans (b := ∏ i, algebraMap R (FractionRing R) (t i) ^ β i a b) ?_ rfl
  clear hc hk hl
  have hu : ∀ u : Rˣ, algebraMap R (FractionRing R) (u : R) ≠ 0 := fun u =>
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 u.ne_zero
  have e : algebraMap R (FractionRing R) u₁ * (k : FractionRing R) = algebraMap R (FractionRing R) u₂ *
      (algebraMap R (FractionRing R) u₃ * ∏ i, algebraMap R (FractionRing R) (t i) ^ β i a b) := by
    rw [← hu₃, ← hu₁, hu₂, div_eq_mul_inv, mul_inv]
    ring
  have h₂ := hu u₂
  have h₃ := hu u₃
  generalize ∏ i, algebraMap R (FractionRing R) (t i) ^ β i a b = P at e ⊢
  rw [Units.val_mul, Units.coe_map, MonoidHom.coe_coe]
  simp only [Units.val_mul, map_mul, map_units_inv]
  field_simp
  linear_combination e

/- English proof (translation)
Set `K` to `AlgebraicClosure (FractionRing T.V)`. Use `haveI : CharZero (FractionRing T.V) := (RingHom.charZero_iff (IsFractionRing.injective T.V (FractionRing T.V))).1 inferInstance`. Establish `hK : (n : K) ≠ 0` using `Nat.cast_ne_zero.2 (by omega)`. Set `κ : Sp K ⟶ Sp (FractionRing T.V)` to `spMap (algebraMap _ K)`. Establish `hp` using `IsPullback.of_hasPullback F.univ.A.hom (κ ≫ T.y)`.

Establish `hq : IsPullback (T.cart.1.lift (pullback.fst F.univ.A.hom (κ ≫ T.y)) (pullback.snd F.univ.A.hom (κ ≫ T.y) ≫ κ) (by rw [Category.assoc]; exact hp.w)) (pullback.snd F.univ.A.hom (κ ≫ T.y)) T.A.A.hom κ` using `IsPullback.of_right (by rw [IsPullback.lift_fst]; exact hp) (T.cart.1.lift_snd _ _ _) T.cart.1`. Establish `hd : SmoothOfRelativeDimension T.A.g (pullback.snd F.univ.A.hom (κ ≫ T.y))` using `(smoothOfRelativeDimension_isStableUnderBaseChange T.A.g).of_isPullback hq T.A.smoothDim`. Establish `e : T.A.g = g` using `GlobalTheory.SiegDim.dim_geometric_fibre F.univ hn hζ hK (κ ≫ T.y) hd`. Establish `hR : AdmBase T.V (maximalIdeal T.V)` using `⟨inferInstance, inferInstance, inferInstance, T.complete⟩`. Establish `h` using `GlobalTheory.TateUnif.rank_add_dim hR T.semi T.U`.

Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_le {g n : ℕ} {o : Type} [CommRing o] {ζ : o} {F : SFam g n ζ} (T : Trait F) (hn : 2 ≤ n) (hζ : IsUnit ζ) :
    Module.finrank ℤ T.D.toPre.X ≤ g := by
  let K := AlgebraicClosure (FractionRing T.V)
  haveI : CharZero (FractionRing T.V) :=
    (RingHom.charZero_iff (IsFractionRing.injective T.V (FractionRing T.V))).1 inferInstance
  have hK : (n : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  let κ : Sp K ⟶ Sp (FractionRing T.V) := spMap (algebraMap _ K)
  have hp := IsPullback.of_hasPullback F.univ.A.hom (κ ≫ T.y)
  have hq : IsPullback (T.cart.1.lift (pullback.fst F.univ.A.hom (κ ≫ T.y)) (pullback.snd F.univ.A.hom (κ ≫ T.y) ≫ κ)
      (by rw [Category.assoc]; exact hp.w)) (pullback.snd F.univ.A.hom (κ ≫ T.y)) T.A.A.hom κ :=
    IsPullback.of_right (by rw [IsPullback.lift_fst]; exact hp) (T.cart.1.lift_snd _ _ _) T.cart.1
  have hd : SmoothOfRelativeDimension T.A.g (pullback.snd F.univ.A.hom (κ ≫ T.y)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange T.A.g).of_isPullback hq T.A.smoothDim
  have e : T.A.g = g := GlobalTheory.SiegDim.dim_geometric_fibre F.univ hn hζ hK (κ ≫ T.y) hd
  have hR : AdmBase T.V (maximalIdeal T.V) := ⟨inferInstance, inferInstance, inferInstance, T.complete⟩
  have h := GlobalTheory.TateUnif.rank_add_dim hR T.semi T.U
  omega

/- English proof (translation)
Introduce `g n o _ ζ F T`. Use `⟨isMonomialTau_ofDeg _ _ T.mono (fun i => ?_) (fun i => ?_), T.mono.nonneg 0, fun a ha => ?_, finrank_le T⟩` and prove the remaining obligations. Use `fin_cases i`. Conclude with `T.symm`. Use `fin_cases i`.

Conclude with `T.irr.ne_zero`. Take `⟨i, hi⟩` from `T.mono.exists_pos (maximalIdeal.isMaximal _).ne_top ha fin_cases i`. Conclude with `hi`.
-/
theorem main : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (T : Trait F), (GlobalTheory.PolDeg.Wit.ofDeg T.D.toPre T.D.tau_bimult).IsMonomialTau ![T.ϖ] ![T.β] ∧ (∀ a, 0 ≤ T.β a a) ∧ (∀ a, a ≠ 0 → 0 < T.β a a) ∧ (2 ≤ n → IsUnit ζ → Module.finrank ℤ T.D.toPre.X ≤ g) := by
  intro g n o _ ζ F T
  refine ⟨isMonomialTau_ofDeg _ _ T.mono (fun i => ?_) (fun i => ?_), T.mono.nonneg 0, fun a ha => ?_, finrank_le T⟩
  · fin_cases i
    exact T.symm
  · fin_cases i
    exact T.irr.ne_zero
  · obtain ⟨i, hi⟩ := T.mono.exists_pos (maximalIdeal.isMaximal _).ne_top ha
    fin_cases i
    exact hi

end GlobalTheory.Poinc.TraitTau
