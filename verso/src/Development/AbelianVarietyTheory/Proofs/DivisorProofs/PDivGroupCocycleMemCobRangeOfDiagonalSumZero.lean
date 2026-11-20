import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneDiagSumEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagSumPullTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleMemRangeCobOfPullbackMulByPow

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

/- English proof (translation)
Proceed by induction on `c using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp [pullbackTwo]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem lift_counit_pullTwo {R D D' : Type} [CommRing R] [CommRing D] [Bialgebra R D] [CommRing D']
    [Bialgebra R D'] (f : D →ₐc[R] D') (c : D ⊗[R] D) :
    Algebra.TensorProduct.lift (Bialgebra.counitAlgHom R D') (Bialgebra.counitAlgHom R D')
        (fun _ _ ↦ Commute.all _ _) (pullbackTwo f c) =
      Algebra.TensorProduct.lift (Bialgebra.counitAlgHom R D) (Bialgebra.counitAlgHom R D)
        (fun _ _ ↦ Commute.all _ _) c := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [pullbackTwo]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Rewrite using `[Algebra.TensorProduct.one_def, diagSum_tmul]`. Simplify using the standard rewrite rules.
-/
theorem diagSum_one (R D : Type) [CommRing R] [CommRing D] [Bialgebra R D] [Coalgebra.IsCocomm R D] (m : ℕ) :
    diagSum R D m 1 = (m : D) := by
  rw [Algebra.TensorProduct.one_def, diagSum_tmul]
  simp

/- English proof (translation)
Introduce `p _ R _ N hp G z hz`. Establish `hq : ((p ^ N : ℕ) : R) = 0` using `by rw [Nat.cast_pow, hp]`. Set `ε : ∀ n, G.A n ⊗[R] G.A n →ₐ[R] R` to `fun n => Algebra.TensorProduct.lift (Bialgebra.counitAlgHom R (G.A n)) (Bialgebra.counitAlgHom R (G.A n)) (fun _ _ ↦ Commute.all _ _)`. Establish `hr : ∀ n, ε n (z.1 n) = ε 0 (z.1 0)`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => rfl`. Consider the case `succ n ih => rw [← ih, ← (z.2 n).2]`. Conclude with `(lift_counit_pullTwo _ _).symm`. Set `o : G.funs` to `⟨fun _ => 1, fun n => map_one (G.res n)⟩`.

Set `z' : G.cocycles` to `z + ε 0 (z.1 0) • G.cob o`. Establish `hz' : ∀ n, z'.1 n = z.1 n - ε 0 (z.1 0) • (1 : G.A n ⊗[R] G.A n)`. Introduce `n`. Express the relevant statement in the definitionally equal form `z.1 n + ε 0 (z.1 0) • cobOne R (G.A n) 1 = _`. Rewrite using `[cobOne_apply, Bialgebra.comul_one, ← Algebra.TensorProduct.one_def, sub_self, zero_sub, smul_neg, sub_eq_add_neg]`.

Establish `h0 : ∀ n, ε n (z'.1 n) = 0`. Introduce `n`. Rewrite using `[hz', map_sub, map_smul, map_one, hr, smul_eq_mul, _root_.mul_one, sub_self]`. Establish `hmem : z' ∈ LinearMap.range G.cob`. Use `cocycle_mem_range_cob_of_pullback_mulBy_pow p R G N z' (fun n => diagSum R (G.A n) (p ^ N) (z'.1 n)) (fun n => ?_) (fun n => ?_) ?_` and prove the remaining obligations.

Rewrite using `[diagSum_pullTwo, (z'.2 n).2]`. Rewrite using `[cobOne_diagSum_eq p R G n (p ^ N) hq _ (z'.2 n).1]`. Use `h0 n` as an intermediate fact. Simplify using `only [ε] at this`. Rewrite using `[this, zero_smul, sub_zero]`.

Express the relevant statement in the definitionally equal form `diagSum R (G.A N) (p ^ N) (z'.1 N) = 0`. Rewrite using `[hz', map_sub, map_smul, hz, diagSum_one, ← map_natCast (algebraMap R (G.A N)), hq, map_zero, smul_zero, sub_zero]`. Establish `: z = z' - ε 0 (z.1 0) • G.cob o` using `by simp [z']`. Rewrite using `[this]`. Conclude with `Submodule.sub_mem _ hmem (Submodule.smul_mem _ _ ⟨o, rfl⟩)`.
-/
theorem cocycle_mem_range_cob_of_diagSum_eq_zero :
    ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 →
      ∀ (G : PDivGroup p R) (z : G.cocycles), diagSum R (G.A N) (p ^ N) (z.1 N) = 0 →
        z ∈ LinearMap.range G.cob := by
  intro p _ R _ N hp G z hz
  have hq : ((p ^ N : ℕ) : R) = 0 := by rw [Nat.cast_pow, hp]
  let ε : ∀ n, G.A n ⊗[R] G.A n →ₐ[R] R := fun n =>
    Algebra.TensorProduct.lift (Bialgebra.counitAlgHom R (G.A n)) (Bialgebra.counitAlgHom R (G.A n))
      (fun _ _ ↦ Commute.all _ _)
  have hr : ∀ n, ε n (z.1 n) = ε 0 (z.1 0) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [← ih, ← (z.2 n).2]; exact (lift_counit_pullTwo _ _).symm
  let o : G.funs := ⟨fun _ => 1, fun n => map_one (G.res n)⟩
  let z' : G.cocycles := z + ε 0 (z.1 0) • G.cob o
  have hz' : ∀ n, z'.1 n = z.1 n - ε 0 (z.1 0) • (1 : G.A n ⊗[R] G.A n) := by
    intro n
    change z.1 n + ε 0 (z.1 0) • cobOne R (G.A n) 1 = _
    rw [cobOne_apply, Bialgebra.comul_one, ← Algebra.TensorProduct.one_def, sub_self, zero_sub, smul_neg,
      sub_eq_add_neg]
  have h0 : ∀ n, ε n (z'.1 n) = 0 := by
    intro n
    rw [hz', map_sub, map_smul, map_one, hr, smul_eq_mul, _root_.mul_one, sub_self]
  have hmem : z' ∈ LinearMap.range G.cob := by
    refine cocycle_mem_range_cob_of_pullback_mulBy_pow p R G N z'
      (fun n => diagSum R (G.A n) (p ^ N) (z'.1 n)) (fun n => ?_) (fun n => ?_) ?_
    · rw [diagSum_pullTwo, (z'.2 n).2]
    · rw [cobOne_diagSum_eq p R G n (p ^ N) hq _ (z'.2 n).1]
      have := h0 n
      simp only [ε] at this
      rw [this, zero_smul, sub_zero]
    · change diagSum R (G.A N) (p ^ N) (z'.1 N) = 0
      rw [hz', map_sub, map_smul, hz, diagSum_one, ← map_natCast (algebraMap R (G.A N)), hq, map_zero,
        smul_zero, sub_zero]
  have : z = z' - ε 0 (z.1 0) • G.cob o := by simp [z']
  rw [this]
  exact Submodule.sub_mem _ hmem (Submodule.smul_mem _ _ ⟨o, rfl⟩)

end GlobalTheory.PtExt
