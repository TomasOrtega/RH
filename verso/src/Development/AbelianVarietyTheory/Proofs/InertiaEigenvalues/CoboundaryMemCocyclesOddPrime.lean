import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneTmulBcrisGaloisLatticeInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisLatticePrimePowSmulTendstoZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisCoboundaryEventuallyMemPrimePowLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowSmulMem
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.CobCont

/- English proof (translation)
The claim follows from `GlobalTheory.T.one_tmul_bcris_galoisLattice_injective`.
-/
theorem inj1 : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL),
    Function.Injective (fun x : ↥T.L.T => (1 : OB l ↥(OL LL)) ⊗ₜ[↥(OL LL)] x) := GlobalTheory.T.one_tmul_bcris_galoisLattice_injective

/- English proof (translation)
The claim follows from `GlobalTheory.T.galoisLattice_prime_pow_smul_tendsto_zero`.
-/
theorem nbhd : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (U : Set T.V), U ∈ nhds (0 : T.V) →
    ∃ m : ℕ, ∀ x ∈ T.L.T, ((l : ↥LL.1) ^ m) • x ∈ U := GlobalTheory.T.galoisLattice_prime_pow_smul_tendsto_zero

/- English proof (translation)
The claim follows from `GlobalTheory.T.bcrisCoboundary_eventually_mem_prime_pow_lattice`.
-/
theorem cont1 : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (LL : FinExt l) (T : QLat LL) (b : TW (OB l ↥(OL LL)) T)
    (c : Gl l → T.V), IsCobOf (sQ l) T b c → ∀ m : ℕ, ∀ᶠ g in nhds (1 : Gl l),
      ∃ x ∈ T.L.T, c g = ((l : ↥LL.1) ^ m) • x := GlobalTheory.T.bcrisCoboundary_eventually_mem_prime_pow_lattice

variable {l : ℕ} [Fact l.Prime] {LL : FinExt l}

/- English proof (translation)
Use `T.L.T.smul_mem o hx` as an intermediate fact. Rewrite `this` using `[← algebraMap_smul ↥LL.1 o x]`. Then use the resulting hypothesis.
-/
theorem o_smul_mem (T : QLat LL) (o : ↥(OL LL)) (x : T.V) (hx : x ∈ T.L.T) : (o : ↥LL.1) • x ∈ T.L.T := by
  have := T.L.T.smul_mem o hx
  rwa [← algebraMap_smul ↥LL.1 o x] at this

/- English proof (translation)
Use `o_smul_mem T ((l : ↥(OL LL)) ^ n) x hx` as an intermediate fact. Simplify using `using this`.
-/
theorem lpow_smul_mem (T : QLat LL) (n : ℕ) (x : T.V) (hx : x ∈ T.L.T) : (l : ↥LL.1) ^ n • x ∈ T.L.T := by
  have := o_smul_mem T ((l : ↥(OL LL)) ^ n) x hx
  simpa using this

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem`. Consider the case `exact _root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem`. Consider the case `(apply _root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem ..)`.
-/
theorem exists_pow_smul_mem (T : QLat LL) (v : T.V) : ∃ n : ℕ, (l : ↥LL.1) ^ n • v ∈ T.L.T := by
  first
  | exact @_root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem
  | exact _root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem
  | (apply _root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem ..)

/- English proof (translation)
Simplify using `[actB, TWact]`.
-/
theorem actB_tmul_one (T : QLat LL) (g : Gl l) (x : ↥T.L.T) :
    actB (sQ l) T g ((1 : OB l ↥(OL LL)) ⊗ₜ[↥(OL LL)] x) = (1 : OB l ↥(OL LL)) ⊗ₜ[↥(OL LL)] T.actT g x := by
  simp [actB, TWact]

/- English proof (translation)
Proceed by induction on `o using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul a w`. Conclude with `congrArg (fun z => a ⊗ₜ[ℤ_[l]] z) ((GlobalTheory.MemLoc.ActLaws.act_laws l).1 _ _ w)`.
-/
theorem galOB_mul' {O : Type} [CommRing O] [Algebra ℤ_[l] O] (g h : GQ l) (o : OB l O) :
    galOB O (g * h) o = galOB O g (galOB O h o) := by
  induction o using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a w =>
    exact congrArg (fun z => a ⊗ₜ[ℤ_[l]] z) ((GlobalTheory.MemLoc.ActLaws.act_laws l).1 _ _ w)

/- English proof (translation)
The claim follows from `Subtype.ext (by show T.ρ (g * h) (x : T.V) = T.ρ g (T.ρ h x) rw [map_mul]; rfl)`.
-/
theorem actT_mul (T : QLat LL) (g h : Gl l) (x : ↥T.L.T) : T.actT (g * h) x = T.actT g (T.actT h x) :=
  Subtype.ext (by
    show T.ρ (g * h) (x : T.V) = T.ρ g (T.ρ h x)
    rw [map_mul]; rfl)

/- English proof (translation)
The claim follows from `TensorProduct.map_tmul _ _ _ _`.
-/
theorem actB_tmul (T : QLat LL) (g : Gl l) (o : OB l ↥(OL LL)) (x : ↥T.L.T) :
    actB (sQ l) T g (o ⊗ₜ[↥(OL LL)] x) = (galOB ↥(OL LL) (sQ l g) o) ⊗ₜ[↥(OL LL)] T.actT g x :=
  TensorProduct.map_tmul _ _ _ _

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Establish `e1` using `actB_tmul T (g*h) o x`. Establish `e2` using `actB_tmul T h o x`. Establish `e3` using `actB_tmul T g (galOB _ (sQ l h) o) (T.actT h x)`. Use `e1.trans (Eq.trans ?_ ((congrArg (actB (sQ l) T g) e2).trans e3).symm)` and prove the remaining obligations. Use `congrArg₂ (fun a b => a ⊗ₜ[↥(OL LL)] b) ?_ (actT_mul T g h x)` and prove the remaining obligations.

Rewrite using `[map_mul]`. Conclude with `galOB_mul' _ _ o`.
-/
theorem actB_mul_a (T : QLat LL) (g h : Gl l) (o : OB l ↥(OL LL)) (x : ↥T.L.T) :
    actB (sQ l) T (g * h) (o ⊗ₜ[↥(OL LL)] x) = actB (sQ l) T g (actB (sQ l) T h (o ⊗ₜ[↥(OL LL)] x)) := by
  have e1 := actB_tmul T (g*h) o x
  have e2 := actB_tmul T h o x
  have e3 := actB_tmul T g (galOB _ (sQ l h) o) (T.actT h x)
  refine e1.trans (Eq.trans ?_ ((congrArg (actB (sQ l) T g) e2).trans e3).symm)
  refine congrArg₂ (fun a b => a ⊗ₜ[↥(OL LL)] b) ?_ (actT_mul T g h x)
  rw [map_mul]
  exact galOB_mul' _ _ o

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul o x => exact actB_mul_a T g h o x`.
-/
theorem actB_mul (T : QLat LL) (g h : Gl l) (y : TW (OB l ↥(OL LL)) T) :
    actB (sQ l) T (g * h) y = actB (sQ l) T g (actB (sQ l) T h y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul o x => exact actB_mul_a T g h o x

/- English proof (translation)
Rewrite using `[e3, e2, e1, hmul, map_smul, map_sub, ← smul_add]`. Use `congr 1`. Normalize the expressions using the abelian group laws.
-/
theorem abs_cocycle {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (Fg Fh Fgh : M →ₗ[R] M)
    (hmul : ∀ y, Fgh y = Fg (Fh y)) (b y1 y2 y3 : M) (r : R) (e1 : y1 = r • (Fg b - b))
    (e2 : y2 = r • (Fh b - b)) (e3 : y3 = r • (Fgh b - b)) : y3 = Fg y2 + y1 := by
  rw [e3, e2, e1, hmul, map_smul, map_sub, ← smul_add]
  congr 1
  abel

/- English proof (translation)
Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hk`. Rewrite using `[pow_add, mul_comm, mul_smul]`. Conclude with `lpow_smul_mem T _ _ hv`.
-/
theorem pow_le_mem (T : QLat LL) {k n : ℕ} (hk : k ≤ n) (v : T.V) (hv : (l : ↥LL.1) ^ k • v ∈ T.L.T) :
    (l : ↥LL.1) ^ n • v ∈ T.L.T := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [pow_add, mul_comm, mul_smul]
  exact lpow_smul_mem T _ _ hv

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Take `⟨n1, h1⟩` from `exists_pow_smul_mem T (c g)`. Take `⟨n2, h2⟩` from `exists_pow_smul_mem T (c h)`. Take `⟨n3, h3⟩` from `exists_pow_smul_mem T (c (g * h))`. Establish `m1` using `pow_le_mem T (n := n1 + n2 + n3) (by omega) _ h1`. Establish `m2` using `pow_le_mem T (n := n1 + n2 + n3) (by omega) _ h2`.

Establish `m3` using `pow_le_mem T (n := n1 + n2 + n3) (by omega) _ h3`. Establish `e1` using `hc g _ ⟨_, m1⟩ rfl`. Establish `e2` using `hc h _ ⟨_, m2⟩ rfl`. Establish `e3` using `hc (g * h) _ ⟨_, m3⟩ rfl`. Establish `key : (⟨_, m3⟩ : ↥T.L.T) = T.actT g ⟨_, m2⟩ + ⟨_, m1⟩`.

Apply `inj1 l LL T` to reduce the goal to its premises. Use `abs_cocycle (actB (sQ l) T g) (actB (sQ l) T h) (actB (sQ l) T (g * h)) (actB_mul T g h) _ _ _ _ _ e1 e2 e3` as an intermediate fact. Use `this.trans ?_` and prove the remaining obligations. Use `(congrArg (· + _) (actB_tmul_one T g _)).trans ?_` and prove the remaining obligations. Conclude with `(TensorProduct.tmul_add _ _ _).symm`.

Establish `key'` using `congrArg (fun z : ↥T.L.T => (z : T.V)) key`. Simplify using `only [Submodule.coe_add] at key'`. Express the relevant statement in the definitionally equal form `(l : ↥LL.1) ^ (n1 + n2 + n3) • c (g * h) = T.ρ g ((l : ↥LL.1) ^ (n1 + n2 + n3) • c h) + (l : ↥LL.1) ^ (n1 + n2 + n3) • c g at key'`. Rewrite `key'` using `[map_smul, ← smul_add]`. Establish `hl : ((l : ↥LL.1) ^ (n1 + n2 + n3)) ≠ 0` using `pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero)`.

Rewrite using `[smul_right_injective T.V hl key', add_comm]`.
-/
theorem cocycle (T : QLat LL) (b : TW (OB l ↥(OL LL)) T) (c : Gl l → T.V) (hc : IsCobOf (sQ l) T b c)
    (g h : Gl l) : c (g * h) = c g + T.ρ g (c h) := by
  obtain ⟨n1, h1⟩ := exists_pow_smul_mem T (c g)
  obtain ⟨n2, h2⟩ := exists_pow_smul_mem T (c h)
  obtain ⟨n3, h3⟩ := exists_pow_smul_mem T (c (g * h))
  have m1 := pow_le_mem T (n := n1 + n2 + n3) (by omega) _ h1
  have m2 := pow_le_mem T (n := n1 + n2 + n3) (by omega) _ h2
  have m3 := pow_le_mem T (n := n1 + n2 + n3) (by omega) _ h3
  have e1 := hc g _ ⟨_, m1⟩ rfl
  have e2 := hc h _ ⟨_, m2⟩ rfl
  have e3 := hc (g * h) _ ⟨_, m3⟩ rfl
  have key : (⟨_, m3⟩ : ↥T.L.T) = T.actT g ⟨_, m2⟩ + ⟨_, m1⟩ := by
    apply inj1 l LL T
    have := abs_cocycle (actB (sQ l) T g) (actB (sQ l) T h) (actB (sQ l) T (g * h)) (actB_mul T g h) _ _ _ _ _ e1 e2 e3
    refine this.trans ?_
    refine (congrArg (· + _) (actB_tmul_one T g _)).trans ?_
    exact (TensorProduct.tmul_add _ _ _).symm
  have key' := congrArg (fun z : ↥T.L.T => (z : T.V)) key
  simp only [Submodule.coe_add] at key'
  change (l : ↥LL.1) ^ (n1 + n2 + n3) • c (g * h) =
    T.ρ g ((l : ↥LL.1) ^ (n1 + n2 + n3) • c h) + (l : ↥LL.1) ^ (n1 + n2 + n3) • c g at key'
  rw [map_smul, ← smul_add] at key'
  have hl : ((l : ↥LL.1) ^ (n1 + n2 + n3)) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
  rw [smul_right_injective T.V hl key', add_comm]

/- English proof (translation)
Establish `h` using `cocycle T b c hc 1 1`. Rewrite `h` using `[mul_one, map_one, Module.End.one_apply]`. Conclude with `left_eq_add.1 h`.
-/
theorem c_one (T : QLat LL) (b : TW (OB l ↥(OL LL)) T) (c : Gl l → T.V) (hc : IsCobOf (sQ l) T b c) :
    c 1 = 0 := by
  have h := cocycle T b c hc 1 1
  rw [mul_one, map_one, Module.End.one_apply] at h
  exact left_eq_add.1 h

/- English proof (translation)
Rewrite using `[ContinuousAt, c_one T b c hc]`. Introduce `U hU`. Take `⟨m, hm⟩` from `nbhd l LL T U hU`. Rewrite using `[Filter.mem_map]`. Use `filter_upwards [cont1 l hl2 LL T b c hc m] with g hg`.

Take `⟨x, hx, e⟩` from `hg`. Rewrite using `[Set.mem_preimage, e]`. Conclude with `hm x hx`.
-/
theorem contAt_one (hl2 : l ≠ 2) (T : QLat LL) (b : TW (OB l ↥(OL LL)) T) (c : Gl l → T.V)
    (hc : IsCobOf (sQ l) T b c) : ContinuousAt c 1 := by
  rw [ContinuousAt, c_one T b c hc]
  intro U hU
  obtain ⟨m, hm⟩ := nbhd l LL T U hU
  rw [Filter.mem_map]
  filter_upwards [cont1 l hl2 LL T b c hc m] with g hg
  obtain ⟨x, hx, e⟩ := hg
  rw [Set.mem_preimage, e]
  exact hm x hx

/- English proof (translation)
Introduce `l _ hl2 LL T b c hc`. Use `⟨?_, cocycle T b c hc⟩` and prove the remaining obligations. Establish `h1` using `contAt_one hl2 T b c hc`. Establish `hρ : ∀ g : Gl l, Continuous (T.ρ g)` using `fun g => IsModuleTopology.continuous_of_linearMap (T.ρ g)`. Rewrite using `[continuous_iff_continuousAt]`.

Introduce `g0`. Establish `e : c = fun g => c g0 + T.ρ g0 (c (g0⁻¹ * g))`. Use function extensionality and compare the values at `g`. Rewrite using `[← cocycle T b c hc, mul_inv_cancel_left]`. Rewrite using `[e]`.

Use `continuousAt_const.add ((hρ g0).continuousAt.comp ?_)` and prove the remaining obligations. Use `ContinuousAt.comp (f := fun g => g0⁻¹ * g) ?_ (continuous_const.mul continuous_id).continuousAt` and prove the remaining obligations. Simplify using `using h1`.
-/
theorem main : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (LL : FinExt l) (T : QLat LL) (b : TW (OB l ↥(OL LL)) T)
    (c : Gl l → T.V), IsCobOf (sQ l) T b c → c ∈ continuousCocycles T.ρ := by
  intro l _ hl2 LL T b c hc
  refine ⟨?_, cocycle T b c hc⟩
  have h1 := contAt_one hl2 T b c hc
  have hρ : ∀ g : Gl l, Continuous (T.ρ g) := fun g =>
    IsModuleTopology.continuous_of_linearMap (T.ρ g)
  rw [continuous_iff_continuousAt]
  intro g0
  have e : c = fun g => c g0 + T.ρ g0 (c (g0⁻¹ * g)) := by
    funext g
    rw [← cocycle T b c hc, mul_inv_cancel_left]
  rw [e]
  refine continuousAt_const.add ((hρ g0).continuousAt.comp ?_)
  refine ContinuousAt.comp (f := fun g => g0⁻¹ * g) ?_ (continuous_const.mul continuous_id).continuousAt
  simpa using h1

end GlobalTheory.CobCont
