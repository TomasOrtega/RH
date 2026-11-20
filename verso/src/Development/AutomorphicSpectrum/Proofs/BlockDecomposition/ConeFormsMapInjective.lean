import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMulPowEqIncl
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KaehlerFreeConeRingStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.OmlInj
open scoped TensorProduct
open GlobalTheory.TopForm

def allE (n d : ℕ) : Gam n d := ∑ e, oneE e

/- English proof (translation)
Simplify using `[allE, oneE, Finset.sum_apply, Pi.single_apply]`.
-/
theorem allE_apply {n d : ℕ} (e : E n d) : allE n d e = 1 := by
  classical
  simp [allE, oneE, Finset.sum_apply, Pi.single_apply]

/- English proof (translation)
The claim follows from `sum_mem fun e _ => oneE_mem S e`.
-/
theorem allE_mem {n d : ℕ} (S : Finset (Fin d)) : allE n d ∈ (cone S : AddSubmonoid (Gam n d)) :=
  sum_mem fun e _ => oneE_mem S e

/- English proof (translation)
Use `⟨(∑ e, |g e|).toNat, ?_⟩` and prove the remaining obligations. Establish `hall : ∀ e, 0 ≤ (g + (∑ e, |g e|).toNat • allE n d) e`. Introduce `e`. Establish `h1 : |g e| ≤ ∑ e, |g e|` using `Finset.single_le_sum (f := fun e => |g e|) (fun _ _ => abs_nonneg _) (Finset.mem_univ e)`. Establish `h2 : ((∑ e, |g e|).toNat : ℤ) = ∑ e, |g e|` using `Int.toNat_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)`.

Establish `h3` using `neg_abs_le (g e)`. Rewrite using `[Pi.add_apply, Pi.smul_apply, allE_apply, nsmul_eq_mul, mul_one, h2]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `⟨fun _ => hall _, fun _ _ => hall _, Finset.sum_nonneg fun _ _ => hall _⟩`.
-/
theorem exists_add_nsmul_mem {n d : ℕ} (S : Finset (Fin d)) (g : Gam n d) :
    ∃ N : ℕ, g + N • allE n d ∈ (cone S : AddSubmonoid (Gam n d)) := by
  refine ⟨(∑ e, |g e|).toNat, ?_⟩
  have hall : ∀ e, 0 ≤ (g + (∑ e, |g e|).toNat • allE n d) e := by
    intro e
    have h1 : |g e| ≤ ∑ e, |g e| :=
      Finset.single_le_sum (f := fun e => |g e|) (fun _ _ => abs_nonneg _) (Finset.mem_univ e)
    have h2 : ((∑ e, |g e|).toNat : ℤ) = ∑ e, |g e| :=
      Int.toNat_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    have h3 := neg_abs_le (g e)
    rw [Pi.add_apply, Pi.smul_apply, allE_apply, nsmul_eq_mul, mul_one, h2]
    linarith
  exact ⟨fun _ => hall _, fun _ _ => hall _, Finset.sum_nonneg fun _ _ => hall _⟩

/- English proof (translation)
Establish `h2` using `Module.Flat.rTensor_preserves_injective_linearMap (M := M) (Algebra.linearMap A B) hinj`. Introduce `x y hxy`. Establish `h3 : (1 : B) ⊗ₜ[A] x = (1 : B) ⊗ₜ[A] y`. Apply `hf.equiv.injective` to reduce the goal to its premises. Simplify using `[IsBaseChange.equiv_tmul, hxy]`.

Establish `h4 : (1 : A) ⊗ₜ[A] x = (1 : A) ⊗ₜ[A] y`. Apply `h2` to reduce the goal to its premises. Simplify using `using h3`. Simplify using `using congrArg (TensorProduct.lid A M) h4`.
-/
theorem injective_of_isBaseChange {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module.Flat A M] [AddCommGroup N] [Module A N] [Module B N]
    [IsScalarTower A B N] {f : M →ₗ[A] N} (hf : IsBaseChange B f)
    (hinj : Function.Injective (algebraMap A B)) : Function.Injective f := by
  have h2 := Module.Flat.rTensor_preserves_injective_linearMap (M := M) (Algebra.linearMap A B) hinj
  intro x y hxy
  have h3 : (1 : B) ⊗ₜ[A] x = (1 : B) ⊗ₜ[A] y := by
    apply hf.equiv.injective
    simp [IsBaseChange.equiv_tmul, hxy]
  have h4 : (1 : A) ⊗ₜ[A] x = (1 : A) ⊗ₜ[A] y := by
    apply h2
    simpa using h3
  simpa using congrArg (TensorProduct.lid A M) h4

/- English proof (translation)
Introduce `K _ n d S a`. Use `letI : Algebra (R0 K n d S) (Lr K n d) := (incl (K := K) (le_top : (cone S : AddSubmonoid (Gam n d)) ≤ ⊤)).toRingHom.toAlgebra`. Use `haveI : IsScalarTower K (R0 K n d S) (Lr K n d) := IsScalarTower.of_algHom (incl (K := K) (le_top : (cone S : AddSubmonoid (Gam n d)) ≤ ⊤))`. Use `haveI hl : IsLocalization.Away (mon K (allE n d) (allE_mem S)) (Lr K n d) := Away.isLocalization_away le_top (allE n d) (allE_mem S) (AddSubmonoid.mem_top _) (fun g _ => exists_add_nsmul_mem S g)`. Use `haveI : Algebra.FormallyEtale (R0 K n d S) (Lr K n d) := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (mon K (allE n d) (allE_mem S)))`.

Establish `hb` using `KaehlerDifferential.isBaseChange_of_formallyEtale K (R0 K n d S) (Lr K n d)`. Establish `hE` using `GlobalTheory.TopForm.isBaseChange_exteriorPower hb a`. Use `haveI : Module.Free (R0 K n d S) Ω[R0 K n d S⁄K] := GlobalTheory.T.kaehler_free_cone_ring S`. Establish `hinj` using `injective_of_isBaseChange hE (Away.incl_injective le_top)`. Establish `heq : ∀ ω, omMap (K` using `K) (incl (le_top : (cone S : AddSubmonoid (Gam n d)) ≤ ⊤)) a ω = exteriorPowerMapOver (Lr K n d) a (KaehlerDifferential.map K K (R0 K n d S) (Lr K n d)) ω := by`.

Introduce `ω`. Establish `hs : ω ∈ (⊤ : Submodule (R0 K n d S) (Om K (R0 K n d S) a))` using `trivial`. Rewrite `hs` using `[← exteriorPower.ιMulti_span]`. Proceed by induction on `hs using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨v, rfl⟩` from `hx`. Rewrite using `[omMap_ιMulti, exteriorPowerMapOver_ιMulti]`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => simp only [map_add, hx, hy]`. Consider the case `smul c x _ hx`.

Rewrite using `[omMap_smul, hx, map_smul]`. Conclude with `algebraMap_smul (Lr K n d) c _`. Introduce `x y hxy`. Conclude with `hinj (by rw [← heq, ← heq, hxy])`.
-/
theorem omMap_incl_injective : ∀ {K : Type} [Field K] {n d : ℕ} (S : Finset (Fin d)) (a : ℕ),
    Function.Injective (omMap (K := K) (incl (le_top : (cone S : AddSubmonoid (Gam n d)) ≤ ⊤)) a) := by
  intro K _ n d S a
  letI : Algebra (R0 K n d S) (Lr K n d) :=
    (incl (K := K) (le_top : (cone S : AddSubmonoid (Gam n d)) ≤ ⊤)).toRingHom.toAlgebra
  haveI : IsScalarTower K (R0 K n d S) (Lr K n d) :=
    IsScalarTower.of_algHom (incl (K := K) (le_top : (cone S : AddSubmonoid (Gam n d)) ≤ ⊤))
  haveI hl : IsLocalization.Away (mon K (allE n d) (allE_mem S)) (Lr K n d) :=
    Away.isLocalization_away le_top (allE n d) (allE_mem S) (AddSubmonoid.mem_top _)
      (fun g _ => exists_add_nsmul_mem S g)
  haveI : Algebra.FormallyEtale (R0 K n d S) (Lr K n d) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (mon K (allE n d) (allE_mem S)))
  have hb := KaehlerDifferential.isBaseChange_of_formallyEtale K (R0 K n d S) (Lr K n d)
  have hE := GlobalTheory.TopForm.isBaseChange_exteriorPower hb a
  haveI : Module.Free (R0 K n d S) Ω[R0 K n d S⁄K] := GlobalTheory.T.kaehler_free_cone_ring S
  have hinj := injective_of_isBaseChange hE (Away.incl_injective le_top)
  have heq : ∀ ω, omMap (K := K) (incl (le_top : (cone S : AddSubmonoid (Gam n d)) ≤ ⊤)) a ω =
      exteriorPowerMapOver (Lr K n d) a (KaehlerDifferential.map K K (R0 K n d S) (Lr K n d)) ω := by
    intro ω
    have hs : ω ∈ (⊤ : Submodule (R0 K n d S) (Om K (R0 K n d S) a)) := trivial
    rw [← exteriorPower.ιMulti_span] at hs
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, rfl⟩ := hx
      rw [omMap_ιMulti, exteriorPowerMapOver_ιMulti]
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add, hx, hy]
    | smul c x _ hx =>
      rw [omMap_smul, hx, map_smul]
      exact algebraMap_smul (Lr K n d) c _
  intro x y hxy
  exact hinj (by rw [← heq, ← heq, hxy])

end GlobalTheory.CompanionTheory.SurjectionOntoH4.OmlInj
