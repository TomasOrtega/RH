import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Mult Formalism.MainNotions.S
open MeasureTheory IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp GlobalTheory.Orb
open GlobalTheory.AutomorphicL2Unitary (starFn)
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (HypH)
open GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoDim

/- English proof (translation)
Use `set a := Module.finrank E W`. Set `b` to `Module.finBasis E W`. Set `ψ : V.V →ₗ[E] (Fin a → E)` to `LinearMap.pi fun i => V.hT (b i : V.V)`. Establish `hker : LinearMap.ker ψ = GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V W`. Use extensionality with `y`.

Simplify using `only [LinearMap.mem_ker, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp, Submodule.mem_iInf]`. Prove the components needed by the constructor for the conclusion. Introduce `h w hw`. Establish `e` using `congrArg (fun v : Fin a → E => v) h`. Establish `hw' : (⟨w, hw⟩ : W) = ∑ i, (b.repr ⟨w, hw⟩ i) • b i` using `(b.sum_repr _).symm`.

Establish `: w = ∑ i, (b.repr ⟨w, hw⟩ i) • (b i : V.V)`. Use `congrArg Subtype.val hw'` as an intermediate fact. Rewrite `this` using `[Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul] at this`. Conclude with `this`.

Rewrite using `[this, map_sum, LinearMap.sum_apply]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.map_smulₛₗ, LinearMap.smul_apply]`. Use `congrFun h i` as an intermediate fact. Simplify using `only [ψ, LinearMap.pi_apply, Pi.zero_apply] at this`.

Rewrite using `[this, smul_zero]`. Introduce `h`. Use function extensionality and compare the values at `i`. Simplify `h (b i) (b i).2` using `[ψ]`. Establish `hsurj : LinearMap.range ψ = ⊤`.

Assume the negation of the conclusion as `hne`. Take `⟨f, hf0, hf⟩` from `Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance`. Set `c : Fin a → E` to `fun i => f (Pi.single i 1)`. Establish `hfc : ∀ v : Fin a → E, f v = ∑ i, v i * c i`. Introduce `v`.

Rewrite using `[LinearMap.pi_apply_eq_sum_univ f v]`. Simplify using `only [smul_eq_mul, c]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `congr 2`. Use function extensionality and compare the values at `j`.

Simplify using `[Pi.single_apply, eq_comm]`. Establish `hy : ∀ y, V.hT (∑ i, (star (c i)) • (b i : V.V)) y = 0`. Introduce `y`. Establish `h1 : f (ψ y) = 0`. Establish `: f (ψ y) ∈ (LinearMap.range ψ).map f` using `⟨ψ y, ⟨y, rfl⟩, rfl⟩`.

Rewrite `this` using `[hf]`. Conclude with `(Submodule.mem_bot E).1 this`. Rewrite `h1` using `[hfc]`. Rewrite using `[map_sum, LinearMap.sum_apply]`. Rewrite using `[← h1]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]`. Simplify using `[ψ, mul_comm]`. Establish `hx` using `V.nondeg.1 _ hy`. Establish `hli : LinearIndependent E (fun i => (b i : V.V))` using `b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)`.

Establish `hc : ∀ i, star (c i) = 0`. Use `(Fintype.linearIndependent_iff.1 hli) (fun i => star (c i)) hx` as an intermediate fact. Conclude with `this`. Apply `hf0` to reduce the goal to its premises. Apply `LinearMap.ext` to reduce the goal to its premises.

Introduce `v`. Rewrite using `[hfc]`. Simplify using `[fun i => star_eq_zero.1 (hc i)]`. Establish `hrn` using `LinearMap.finrank_range_add_finrank_ker ψ`. Rewrite `hrn` using `[hsurj, hker, finrank_top, Module.finrank_fin_fun, V.rank_eq]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_perp_add {E : Type} [Field E] [NumberField E] [StarRing E] (V : HSpace E)
    (W : Submodule E V.V) :
    Module.finrank E (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V W) + Module.finrank E W = V.rank := by
  classical
  set a := Module.finrank E W
  let b := Module.finBasis E W
  let ψ : V.V →ₗ[E] (Fin a → E) := LinearMap.pi fun i => V.hT (b i : V.V)
  have hker : LinearMap.ker ψ = GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V W := by
    ext y
    simp only [LinearMap.mem_ker, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp, Submodule.mem_iInf]
    constructor
    · intro h w hw
      have e := congrArg (fun v : Fin a → E => v) h
      have hw' : (⟨w, hw⟩ : W) = ∑ i, (b.repr ⟨w, hw⟩ i) • b i := (b.sum_repr _).symm
      have : w = ∑ i, (b.repr ⟨w, hw⟩ i) • (b i : V.V) := by
        have := congrArg Subtype.val hw'
        rw [Submodule.coe_sum] at this
        simp only [Submodule.coe_smul] at this
        exact this
      rw [this, map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply]
      have := congrFun h i
      simp only [ψ, LinearMap.pi_apply, Pi.zero_apply] at this
      rw [this, smul_zero]
    · intro h
      funext i
      simpa [ψ] using h (b i) (b i).2
  have hsurj : LinearMap.range ψ = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance
    let c : Fin a → E := fun i => f (Pi.single i 1)
    have hfc : ∀ v : Fin a → E, f v = ∑ i, v i * c i := by
      intro v
      rw [LinearMap.pi_apply_eq_sum_univ f v]
      simp only [smul_eq_mul, c]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 2
      funext j
      simp [Pi.single_apply, eq_comm]
    have hy : ∀ y, V.hT (∑ i, (star (c i)) • (b i : V.V)) y = 0 := by
      intro y
      have h1 : f (ψ y) = 0 := by
        have : f (ψ y) ∈ (LinearMap.range ψ).map f := ⟨ψ y, ⟨y, rfl⟩, rfl⟩
        rw [hf] at this
        exact (Submodule.mem_bot E).1 this
      rw [hfc] at h1
      rw [map_sum, LinearMap.sum_apply]
      rw [← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
      simp [ψ, mul_comm]
    have hx := V.nondeg.1 _ hy
    have hli : LinearIndependent E (fun i => (b i : V.V)) :=
      b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
    have hc : ∀ i, star (c i) = 0 := by
      have := (Fintype.linearIndependent_iff.1 hli) (fun i => star (c i)) hx
      exact this
    apply hf0
    apply LinearMap.ext
    intro v
    rw [hfc]
    simp [fun i => star_eq_zero.1 (hc i)]
  have hrn := LinearMap.finrank_range_add_finrank_ker ψ
  rw [hsurj, hker, finrank_top, Module.finrank_fin_fun, V.rank_eq] at hrn
  omega

end GlobalTheory.IsoDim

/- English proof (translation)
Introduce `D V hodd W hW`. Establish `h` using `GlobalTheory.IsoDim.finrank_perp_add V W`. Establish `hle : Module.finrank D.host.E W ≤ Module.finrank D.host.E (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V W)` using `Submodule.finrank_mono hW.2`. Establish `hpos : 0 < Module.finrank D.host.E W` using `Nat.pos_of_ne_zero fun h0 => hW.1 (Submodule.finrank_eq_zero.1 h0)`. Take `⟨k, hk⟩` from `hodd`.

Use `⟨hpos, ?_⟩` and prove the remaining obligations. Use linear arithmetic over natural numbers and integers.
-/
theorem GlobalTheory.IsoDim.isotropic_dim_bounds : ∀ (D : D7) (V : HSp D), Odd V.rank → ∀ W : Submodule D.host.E V.V, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V W →
    0 < Module.finrank D.host.E W ∧ 2 * Module.finrank D.host.E W + 1 ≤ V.rank := by
  intro D V hodd W hW
  have h := GlobalTheory.IsoDim.finrank_perp_add V W
  have hle : Module.finrank D.host.E W ≤ Module.finrank D.host.E (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V W) :=
    Submodule.finrank_mono hW.2
  have hpos : 0 < Module.finrank D.host.E W :=
    Nat.pos_of_ne_zero fun h0 => hW.1 (Submodule.finrank_eq_zero.1 h0)
  obtain ⟨k, hk⟩ := hodd
  refine ⟨hpos, ?_⟩
  omega
