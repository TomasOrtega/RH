import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ContinuousIdeleCircle

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

namespace GlobalTheory.CompanionTheory.HeckeBridge

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Use `MonoidHom.ext fun a => ?_` and prove the remaining obligations. Use `show (toHecke χ hu).toIdele (ofFinite (finiteUnitsSingle v a)) = (toHecke χ hu).localComponent v a`. Rewrite using `[GroundTheory.Global.IdeleGroup.ofFinite_finiteUnitsSingle, GroundTheory.Global.HeckeCharacter.localComponent_apply]`.
-/
theorem comp_finiteUnitsSingle (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) :
    (((toHecke χ hu).toIdele.comp ofFinite).comp (finiteUnitsSingle v)) =
      ((toHecke χ hu).localComponent v : (v.adicCompletion E)ˣ →* Circle) := by
  refine MonoidHom.ext fun a => ?_
  show (toHecke χ hu).toIdele (ofFinite (finiteUnitsSingle v a)) = (toHecke χ hu).localComponent v a
  rw [GroundTheory.Global.IdeleGroup.ofFinite_finiteUnitsSingle, GroundTheory.Global.HeckeCharacter.localComponent_apply]

/- English proof (translation)
Rewrite using `[comp_finiteUnitsSingle χ hu v]`. Establish `h` using `coe_localComponent χ hu v x`. Prove the components needed by the constructor for the conclusion. Introduce `h1`. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[← h]`. Establish `h1' : (toHecke χ hu).localComponent v x = 1` using `h1`. Rewrite using `[h1', Circle.coe_one, Units.val_one]`. Introduce `h1`. Establish `h1' : (toHecke χ hu).localComponent v x = 1`.

Apply `Circle.ext` to reduce the goal to its premises. Rewrite using `[h, h1, Units.val_one, Circle.coe_one]`. Conclude with `h1'`.
-/
private theorem toHecke_local_eq_one_iff (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E))
    (x : (v.adicCompletion E)ˣ) :
    (((toHecke χ hu).toIdele.comp ofFinite).comp (finiteUnitsSingle v)) x = 1 ↔ χ.loc v x = 1 := by
  rw [comp_finiteUnitsSingle χ hu v]
  have h := coe_localComponent χ hu v x
  constructor
  · intro h1
    apply Units.ext
    rw [← h]
    have h1' : (toHecke χ hu).localComponent v x = 1 := h1
    rw [h1', Circle.coe_one, Units.val_one]
  · intro h1
    have h1' : (toHecke χ hu).localComponent v x = 1 := by
      apply Circle.ext
      rw [h, h1, Units.val_one, Circle.coe_one]
    exact h1'

/- English proof (translation)
Unfold `Formalism.L2.Host.HChar.LevelLe`. Prove the components needed by the constructor for the conclusion. Introduce `h x hx`. Rewrite `hx` using `[GroundTheory.Global.mem_unitsLevel]`. Rewrite using `[MonoidHom.mem_ker, toHecke_local_eq_one_iff χ hu v x]`.

Conclude with `h x hx.1 hx.2`. Introduce `h x hux hx`. Rewrite using `[← toHecke_local_eq_one_iff χ hu v x]`. Conclude with `h (GroundTheory.Global.mem_unitsLevel.mpr ⟨hux, hx⟩)`.
-/
theorem levelLe_iff_unitsLevel_le_ker (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    χ.LevelLe v n ↔
      unitsLevel v n ≤ (((toHecke χ hu).toIdele.comp ofFinite).comp (finiteUnitsSingle v)).ker := by
  unfold Formalism.L2.Host.HChar.LevelLe
  constructor
  · intro h x hx
    rw [GroundTheory.Global.mem_unitsLevel] at hx
    rw [MonoidHom.mem_ker, toHecke_local_eq_one_iff χ hu v x]
    exact h x hx.1 hx.2
  · intro h x hux hx
    rw [← toHecke_local_eq_one_iff χ hu v x]
    exact h (GroundTheory.Global.mem_unitsLevel.mpr ⟨hux, hx⟩)

/- English proof (translation)
Rewrite using `[levelLe_iff_unitsLevel_le_ker χ hu v n]`. Conclude with `GroundTheory.Global.unitsLevel_le_ker_iff v GroundTheory.Global.Circle.noSmallSubgroups _ (((toHecke χ hu).continuous_toIdele.comp GroundTheory.Global.IdeleGroup.continuous_ofFinite).comp (GroundTheory.Global.IdeleGroup.continuous_finiteUnitsSingle v))`.
-/
theorem levelLe_iff_conductorExponentAt (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    χ.LevelLe v n ↔ conductorExponentAt ((toHecke χ hu).toIdele.comp ofFinite) v ≤ n := by
  rw [levelLe_iff_unitsLevel_le_ker χ hu v n]
  exact GroundTheory.Global.unitsLevel_le_ker_iff v GroundTheory.Global.Circle.noSmallSubgroups _
    (((toHecke χ hu).continuous_toIdele.comp GroundTheory.Global.IdeleGroup.continuous_ofFinite).comp
      (GroundTheory.Global.IdeleGroup.continuous_finiteUnitsSingle v))

/- English proof (translation)
Establish `hfin : (Function.mulSupport fun w : HeightOneSpectrum R => w.asIdeal ^ a w).Finite`. Rewrite using `[GroundTheory.Global.mulSupport_asIdeal_pow]`. Conclude with `ha`. Prove the components needed by the constructor for the conclusion. Introduce `hk`.

Assume the negation of the conclusion as `hlt`. Rewrite `hlt` using `[not_le]`. Use `set b : HeightOneSpectrum R → ℕ := Function.update a v 0 with hb`. Establish `hbfin : (Function.support b).Finite`. Use `ha.subset (fun w hw => ?_)` and prove the remaining obligations.

Distinguish the cases in `hwv : w = v`. Substitute `hwv` using the available equality. Simplify using `[hb] at hw`. Simplify `hw` using `[hb, Function.update_of_ne hwv]`. Establish `hcfin : (Function.mulSupport fun w : HeightOneSpectrum R => w.asIdeal ^ (if w = v then a v else 0)).Finite`.

Use `(Set.finite_singleton v).subset (fun w hw => ?_)` and prove the remaining obligations. Rewrite using `[Set.mem_singleton_iff]`. Assume the negation of the conclusion as `hwv`. Conclude with `hw (by simp [hwv])`. Establish `hbfin' : (Function.mulSupport fun w : HeightOneSpectrum R => w.asIdeal ^ b w).Finite`.

Rewrite using `[GroundTheory.Global.mulSupport_asIdeal_pow]`. Conclude with `hbfin`. Establish `hsingle : ∏ᶠ w : HeightOneSpectrum R, w.asIdeal ^ (if w = v then a v else 0) = v.asIdeal ^ a v`. Rewrite using `[finprod_eq_single _ v (fun w hw => by simp [hw])]`. Simplify using the standard rewrite rules.

Establish `hsplit : ∏ᶠ w : HeightOneSpectrum R, w.asIdeal ^ a w = v.asIdeal ^ a v * ∏ᶠ w : HeightOneSpectrum R, w.asIdeal ^ b w`. Rewrite using `[← hsingle, ← finprod_mul_distrib hcfin hbfin']`. Use `finprod_congr fun w => ?_` and prove the remaining obligations. Distinguish the cases in `hwv : w = v`. Substitute `hwv` using the available equality.

Simplify using `[hb]`. Simplify using `[hb, hwv, Function.update_of_ne hwv]`. Rewrite `hk` using `[hsplit]`. Establish `hpow : v.asIdeal ^ k = v.asIdeal ^ a v * v.asIdeal ^ (k - a v)`. Rewrite using `[← pow_add]`.

Use `congr 1`. Use linear arithmetic over natural numbers and integers. Rewrite `hk` using `[hpow]`. Establish `hne0 : v.asIdeal ^ a v ≠ 0` using `pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact v.ne_bot)`. Establish `hk'` using `(mul_dvd_mul_iff_left hne0).mp hk`.

Establish `hv : v.asIdeal ∣ ∏ᶠ w : HeightOneSpectrum R, w.asIdeal ^ b w` using `(dvd_pow_self _ (by omega)).trans hk'`. Establish `h1` using `(GroundTheory.Global.asIdeal_dvd_finprod_iff hbfin v).mp hv`. Simplify using `[hb] at h1`. Introduce `hk`. Conclude with `(pow_dvd_pow _ hk).trans (finprod_mem_dvd (f := fun w : HeightOneSpectrum R => w.asIdeal ^ a w) v hfin)`.
-/
private theorem asIdeal_pow_dvd_finprod_iff {R : Type*} [CommRing R] [IsDedekindDomain R]
    {a : HeightOneSpectrum R → ℕ} (ha : (Function.support a).Finite) (v : HeightOneSpectrum R) (k : ℕ) :
    v.asIdeal ^ k ∣ ∏ᶠ w : HeightOneSpectrum R, w.asIdeal ^ a w ↔ k ≤ a v := by
  classical
  have hfin : (Function.mulSupport fun w : HeightOneSpectrum R => w.asIdeal ^ a w).Finite := by
    rw [GroundTheory.Global.mulSupport_asIdeal_pow]; exact ha
  constructor
  · intro hk
    by_contra hlt
    rw [not_le] at hlt
    set b : HeightOneSpectrum R → ℕ := Function.update a v 0 with hb
    have hbfin : (Function.support b).Finite := by
      refine ha.subset (fun w hw => ?_)
      by_cases hwv : w = v
      · subst hwv
        simp [hb] at hw
      · simpa [hb, Function.update_of_ne hwv] using hw
    have hcfin : (Function.mulSupport fun w : HeightOneSpectrum R =>
        w.asIdeal ^ (if w = v then a v else 0)).Finite := by
      refine (Set.finite_singleton v).subset (fun w hw => ?_)
      rw [Set.mem_singleton_iff]
      by_contra hwv
      exact hw (by simp [hwv])
    have hbfin' : (Function.mulSupport fun w : HeightOneSpectrum R => w.asIdeal ^ b w).Finite := by
      rw [GroundTheory.Global.mulSupport_asIdeal_pow]; exact hbfin
    have hsingle : ∏ᶠ w : HeightOneSpectrum R, w.asIdeal ^ (if w = v then a v else 0) = v.asIdeal ^ a v := by
      rw [finprod_eq_single _ v (fun w hw => by simp [hw])]
      simp
    have hsplit : ∏ᶠ w : HeightOneSpectrum R, w.asIdeal ^ a w =
        v.asIdeal ^ a v * ∏ᶠ w : HeightOneSpectrum R, w.asIdeal ^ b w := by
      rw [← hsingle, ← finprod_mul_distrib hcfin hbfin']
      refine finprod_congr fun w => ?_
      by_cases hwv : w = v
      · subst hwv
        simp [hb]
      · simp [hb, hwv, Function.update_of_ne hwv]
    rw [hsplit] at hk
    have hpow : v.asIdeal ^ k = v.asIdeal ^ a v * v.asIdeal ^ (k - a v) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow] at hk
    have hne0 : v.asIdeal ^ a v ≠ 0 := pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact v.ne_bot)
    have hk' := (mul_dvd_mul_iff_left hne0).mp hk
    have hv : v.asIdeal ∣ ∏ᶠ w : HeightOneSpectrum R, w.asIdeal ^ b w :=
      (dvd_pow_self _ (by omega)).trans hk'
    have h1 := (GroundTheory.Global.asIdeal_dvd_finprod_iff hbfin v).mp hv
    simp [hb] at h1
  · intro hk
    exact (pow_dvd_pow _ hk).trans
      (finprod_mem_dvd (f := fun w : HeightOneSpectrum R => w.asIdeal ^ a w) v hfin)

/- English proof (translation)
Establish `hcont : Continuous ((toHecke χ hu).toIdele.comp ofFinite)` using `(toHecke χ hu).continuous_toIdele.comp GroundTheory.Global.IdeleGroup.continuous_ofFinite`. Establish `hfin` using `GroundTheory.Global.IdeleGroup.finite_support_conductorExponentAt GroundTheory.Global.Circle.noSmallSubgroups _ hcont`. Establish `hne` using `(toHecke χ hu).conductor_ne_bot`. Establish `hcond : χ.IsCond (toHecke χ hu).conductor`. Unfold `Formalism.L2.Host.HChar.IsCond`.

Use `⟨hne, fun w n => ?_⟩` and prove the remaining obligations. Rewrite using `[levelLe_iff_conductorExponentAt χ hu w n]`. Establish `h1` using `asIdeal_pow_dvd_finprod_iff hfin w (n + 1)`. Express the relevant statement in the definitionally equal form `_ ↔ ¬ w.asIdeal ^ (n + 1) ∣ ∏ᶠ u : HeightOneSpectrum (𝓞 E), u.asIdeal ^ conductorExponentAt ((toHecke χ hu).toIdele.comp ofFinite) u`. Rewrite using `[h1]`.

Apply the tactic sequence `constructor <;> intro h2 <;> omega`. Conclude with `(GlobalTheory.CMVal.ExpAt.unique h ((GlobalTheory.CMVal.isCond_iff_expAt χ hne).mp hcond v)).symm`.
-/
theorem multiplicity_conductor_toHecke (E : Type) [Field E] [NumberField E] (χ : HChar E) (hu : IsUnitary χ)
    (v : HeightOneSpectrum (𝓞 E)) (m : ℕ) (h : ExpAt χ v m) :
    multiplicity v.asIdeal (toHecke χ hu).conductor = m := by
  have hcont : Continuous ((toHecke χ hu).toIdele.comp ofFinite) :=
    (toHecke χ hu).continuous_toIdele.comp GroundTheory.Global.IdeleGroup.continuous_ofFinite
  have hfin := GroundTheory.Global.IdeleGroup.finite_support_conductorExponentAt
    GroundTheory.Global.Circle.noSmallSubgroups _ hcont
  have hne := (toHecke χ hu).conductor_ne_bot
  have hcond : χ.IsCond (toHecke χ hu).conductor := by
    unfold Formalism.L2.Host.HChar.IsCond
    refine ⟨hne, fun w n => ?_⟩
    rw [levelLe_iff_conductorExponentAt χ hu w n]
    have h1 := asIdeal_pow_dvd_finprod_iff hfin w (n + 1)
    change _ ↔ ¬ w.asIdeal ^ (n + 1) ∣ ∏ᶠ u : HeightOneSpectrum (𝓞 E),
      u.asIdeal ^ conductorExponentAt ((toHecke χ hu).toIdele.comp ofFinite) u
    rw [h1]
    constructor <;> intro h2 <;> omega
  exact (GlobalTheory.CMVal.ExpAt.unique h ((GlobalTheory.CMVal.isCond_iff_expAt χ hne).mp hcond v)).symm

end GlobalTheory.CompanionTheory.HeckeBridge
