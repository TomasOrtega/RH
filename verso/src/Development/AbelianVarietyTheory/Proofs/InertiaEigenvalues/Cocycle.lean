import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisOfSubmodule

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory.ConnCoc

section General

variable {G Qp LL O : Type} [Group G] [TopologicalSpace G] [Field Qp] [Field LL]
  [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Apply `hι` to reduce the goal to its premises. Establish `e : ((f g + actT Y.L g (f h) : ↥Y.L.T) : Y.V) = (f g : Y.V) + Y.ρ g (f h : Y.V)` using `rfl`. Rewrite using `[e, map_add, ι.equiv, hf, hf, hf, map_sub, map_mul, Module.End.mul_apply]`. Normalize the expressions using the abelian group laws.
-/
theorem cocycle (Y Yt : LocLat G Qp LL O) (ι : LatHom Y.L Yt.L) (hι : Function.Injective ι.f)
    (yt : Yt.V) (f : G → ↥Y.L.T) (hf : ∀ g, ι.f (f g : Y.V) = Yt.ρ g yt - yt) (g h : G) :
    f (g * h) = f g + actT Y.L g (f h) := by
  apply Subtype.ext
  apply hι
  have e : ((f g + actT Y.L g (f h) : ↥Y.L.T) : Y.V) = (f g : Y.V) + Y.ρ g (f h : Y.V) := rfl
  rw [e, map_add, ι.equiv, hf, hf, hf, map_sub, map_mul, Module.End.mul_apply]
  abel

/- English proof (translation)
Take `⟨r, hr⟩` from `LinearMap.exists_leftInverse_of_injective ι.f (LinearMap.ker_eq_bot.2 hι)`. Establish `: ContinuousSMul LL Y.V` using `IsModuleTopology.toContinuousSMul LL Y.V`. Establish `hc : Continuous r` using `IsModuleTopology.continuous_of_linearMap r`. Establish `e : (fun g => (f g : Y.V)) = fun g => r (Yt.ρ g yt) + (- r yt)`. Use function extensionality and compare the values at `g`.

Rewrite using `[← sub_eq_add_neg, ← map_sub, ← hf]`. Conclude with `(LinearMap.congr_fun hr _).symm`. Rewrite using `[e]`. Conclude with `(hc.comp (Yt.cont yt)).add continuous_const`.
-/
theorem continuous (Y Yt : LocLat G Qp LL O) (ι : LatHom Y.L Yt.L) (hι : Function.Injective ι.f)
    (yt : Yt.V) (f : G → ↥Y.L.T) (hf : ∀ g, ι.f (f g : Y.V) = Yt.ρ g yt - yt) :
    Continuous fun g => (f g : Y.V) := by
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective ι.f (LinearMap.ker_eq_bot.2 hι)
  have : ContinuousSMul LL Y.V := IsModuleTopology.toContinuousSMul LL Y.V
  have hc : Continuous r := IsModuleTopology.continuous_of_linearMap r
  have e : (fun g => (f g : Y.V)) = fun g => r (Yt.ρ g yt) + (- r yt) := by
    funext g
    rw [← sub_eq_add_neg, ← map_sub, ← hf]
    exact (LinearMap.congr_fun hr _).symm
  rw [e]
  exact (hc.comp (Yt.cont yt)).add continuous_const

end General

/- English proof (translation)
Establish `hl : ((l : ℚ_[l]) ^ n) ≠ 0` using `pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)`. Establish `key : ∀ i, ∀ᶠ h in nhds g, ‖((l : ℚ_[l]) ^ n)⁻¹ * (w.equivFun (F h) i - w.equivFun (F g) i)‖ < 1`. Introduce `i`. Establish `c : Continuous fun h => ‖((l : ℚ_[l]) ^ n)⁻¹ * (w.equivFun (F h) i - w.equivFun (F g) i)‖` using `(continuous_const.mul (((continuous_apply i).comp (hc.comp hF)).sub continuous_const)).norm`. Apply `c.continuousAt.eventually_lt continuousAt_const` to reduce the goal to its premises.

Simplify using the standard rewrite rules. Use `filter_upwards [Filter.eventually_all.2 key] with h hh`. Use `⟨((l : ℚ_[l]) ^ n)⁻¹ • (F h - F g), (hw _).2 fun i => ?_, ?_⟩` and prove the remaining obligations. Use `(hh i).le` as an intermediate fact. Simplify `this` using `[Module.Basis.equivFun_apply]`.

Rewrite using `[← Nat.cast_smul_eq_nsmul ℚ_[l], smul_smul, Nat.cast_pow, mul_inv_cancel₀ hl, one_smul]`.
-/
theorem locConst {l : ℕ} [Fact l.Prime] {G V : Type} [TopologicalSpace G] [AddCommGroup V]
    [Module ℚ_[l] V] [TopologicalSpace V] (T : Set V) {m : ℕ} (w : Module.Basis (Fin m) ℚ_[l] V)
    (hw : ∀ x : V, x ∈ T ↔ ∀ i, ‖w.repr x i‖ ≤ 1) (hc : Continuous w.equivFun)
    (F : G → V) (hF : Continuous F) (n : ℕ) (g : G) :
    ∀ᶠ h in nhds g, ∃ y ∈ T, F h - F g = (l ^ n : ℕ) • y := by
  have hl : ((l : ℚ_[l]) ^ n) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have key : ∀ i, ∀ᶠ h in nhds g,
      ‖((l : ℚ_[l]) ^ n)⁻¹ * (w.equivFun (F h) i - w.equivFun (F g) i)‖ < 1 := by
    intro i
    have c : Continuous fun h =>
        ‖((l : ℚ_[l]) ^ n)⁻¹ * (w.equivFun (F h) i - w.equivFun (F g) i)‖ :=
      (continuous_const.mul (((continuous_apply i).comp (hc.comp hF)).sub continuous_const)).norm
    apply c.continuousAt.eventually_lt continuousAt_const
    simp
  filter_upwards [Filter.eventually_all.2 key] with h hh
  refine ⟨((l : ℚ_[l]) ^ n)⁻¹ • (F h - F g), (hw _).2 fun i => ?_, ?_⟩
  · have := (hh i).le
    simpa [Module.Basis.equivFun_apply] using this
  · rw [← Nat.cast_smul_eq_nsmul ℚ_[l], smul_smul, Nat.cast_pow, mul_inv_cancel₀ hl, one_smul]

/- English proof (translation)
Introduce `l _ G _ _ LL Y Yt ι hι yt f hf`. Use `⟨cocycle Y Yt ι hι yt f hf, fun n g => ?_⟩` and prove the remaining obligations. Take `⟨m, w, hw, hc, -⟩` from `GlobalTheory.Cyc.LatBasis.exists_basis l G LL Y`. Use `locConst (Y.L.T : Set Y.V) w hw hc _ (continuous Y Yt ι hι yt f hf) n g` as an intermediate fact. Use `filter_upwards [this] with h hh`.

Take `⟨y, hy, e⟩` from `hh`. Conclude with `⟨⟨y, hy⟩, Subtype.ext e⟩`.
-/
theorem conn : ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] (LL : FinExt l) (Y Yt : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) (ι : LatHom Y.L Yt.L), Function.Injective ι.f → ∀ (yt : Yt.V) (f : G → ↥Y.L.T), (∀ g, ι.f (f g : Y.V) = Yt.ρ g yt - yt) → (∀ g h, f (g * h) = f g + actT Y.L g (f h)) ∧ ∀ (n : ℕ) (g : G), ∀ᶠ h in nhds g, ∃ y : ↥Y.L.T, f h - f g = (l ^ n : ℕ) • y := by
  intro l _ G _ _ LL Y Yt ι hι yt f hf
  refine ⟨cocycle Y Yt ι hι yt f hf, fun n g => ?_⟩
  obtain ⟨m, w, hw, hc, -⟩ := GlobalTheory.Cyc.LatBasis.exists_basis l G LL Y
  have := locConst (Y.L.T : Set Y.V) w hw hc _ (continuous Y Yt ι hι yt f hf) n g
  filter_upwards [this] with h hh
  obtain ⟨y, hy, e⟩ := hh
  exact ⟨⟨y, hy⟩, Subtype.ext e⟩

end GlobalTheory.ConnCoc
