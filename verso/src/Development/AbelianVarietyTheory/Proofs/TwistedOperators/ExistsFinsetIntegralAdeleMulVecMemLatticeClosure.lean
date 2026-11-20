import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolMatchFiniteSetVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankAlgebraicDataSchrodingerModelLeAleph0
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNsmulMemLattice

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
namespace GlobalTheory.AdelicLatticeIntegral

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.NatMultipleInLattice.exists_nsmul_mem_lattice`. Consider the case `exact _root_.GlobalTheory.NatMultipleInLattice.exists_nsmul_mem_lattice`. Consider the case `(apply _root_.GlobalTheory.NatMultipleInLattice.exists_nsmul_mem_lattice <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.NatMultipleInLattice.exists_nsmul_mem_lattice <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.NatMultipleInLattice.exists_nsmul_mem_lattice <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.NatMultipleInLattice.exists_nsmul_mem_lattice ..)`.
-/
theorem exists_nsmul_mem {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsLattice E)
    (x : Fin n → E) : ∃ D : ℕ, D ≠ 0 ∧ D • x ∈ L := by
  first
  | exact @_root_.GlobalTheory.NatMultipleInLattice.exists_nsmul_mem_lattice
  | exact _root_.GlobalTheory.NatMultipleInLattice.exists_nsmul_mem_lattice
  | (apply _root_.GlobalTheory.NatMultipleInLattice.exists_nsmul_mem_lattice <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatMultipleInLattice.exists_nsmul_mem_lattice <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatMultipleInLattice.exists_nsmul_mem_lattice <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatMultipleInLattice.exists_nsmul_mem_lattice ..)

/- English proof (translation)
Take `⟨s, hs⟩` from `hL.fg`. Use `choose! D hD hDm using fun g => exists_nsmul_mem L hL (N g)`. Use `⟨∏ g ∈ s, D g, Finset.prod_ne_zero_iff.mpr fun g _ => hD g, ?_⟩` and prove the remaining obligations. Introduce `y hy`. Rewrite `hy` using `[← hs]`.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem g hg`. Take `⟨k, hk⟩` from `Finset.dvd_prod_of_mem D hg`. Rewrite using `[hk, mul_comm, mul_smul]`. Conclude with `nsmul_mem (hDm g) k`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add, smul_add]`. Conclude with `L.add_mem hx hy`. Consider the case `smul r x _ hx`. Establish `: N (r • x) = r • N x` using `N.map_smul_of_tower r x`.

Rewrite using `[this, smul_comm]`. Conclude with `L.smul_mem r hx`.
-/
theorem exists_nsmul_map_mem {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsLattice E)
    (N : (Fin n → E) →ₗ[E] (Fin n → E)) : ∃ D : ℕ, D ≠ 0 ∧ ∀ y ∈ L, D • N y ∈ L := by
  obtain ⟨s, hs⟩ := hL.fg
  choose! D hD hDm using fun g => exists_nsmul_mem L hL (N g)
  refine ⟨∏ g ∈ s, D g, Finset.prod_ne_zero_iff.mpr fun g _ => hD g, ?_⟩
  intro y hy
  rw [← hs] at hy
  induction hy using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem D hg
      rw [hk, mul_comm, mul_smul]; exact nsmul_mem (hDm g) k
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, smul_add]; exact L.add_mem hx hy
  | smul r x _ hx =>
      have : N (r • x) = r • N x := N.map_smul_of_tower r x
      rw [this, smul_comm]; exact L.smul_mem r hx

end GlobalTheory.AdelicLatticeIntegral

namespace GlobalTheory.AdelicLatticeIntegral

/- English proof (translation)
Introduce `F E _ _ _ _ _ n M L hL`. Set `bF` to `Module.finBasis F E`. Set `B` to `Algebra.TensorProduct.basis (AF F) bF`. Set `c : Fin n × Fin n × Fin (Module.finrank F E) → AF F` to `fun j => B.repr (M j.1 j.2.1) j.2.2`. Set `Nm : Fin n × Fin n × Fin (Module.finrank F E) → (Fin n → E) →ₗ[E] (Fin n → E)` to `fun j => (LinearMap.single E (fun _ : Fin n => E) j.1) ∘ₗ (bF j.2.2 • LinearMap.proj j.2.1)`.

Set `incV : (Fin n → E) → (Fin n → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)` to `fun y i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y i)`. Establish `key : ∀ y, (M *ᵥ incV y) = ∑ j, c j • incV (Nm j y)`. Introduce `y`. Use function extensionality and compare the values at `r`. Simplify using `only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply]`.

Rewrite using `[Fintype.sum_prod_type]`. Use `symm`. Rewrite using `[Finset.sum_eq_single r]`. Rewrite using `[Fintype.sum_prod_type]`. Use `symm`.

Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Use `conv_lhs => rw [← B.sum_repr (M r q)]`. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[Nm, incV, B, c, Algebra.TensorProduct.basis_apply, smul_mul_assoc, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]`.

Introduce `p _ hp`. Simplify using `[Nm, incV, Pi.single_apply, Ne.symm hp]`. Simplify using the standard rewrite rules. Use `choose D hD0 hDL using fun j => exists_nsmul_map_mem L hL (Nm j)`. Set `c' : Fin n × Fin n × Fin (Module.finrank F E) → AF F` to `fun j => c j * algebraMap F (AF F) ((D j : F)⁻¹)`.

Establish `hfin : ∀ j, {w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F | ¬ GlobalTheory.AdelicU.evFin F w (c' j) ∈ w.adicCompletionIntegers F}.Finite` using `fun j => Filter.eventually_cofinite.mp (GlobalTheory.AlgCountDim.eventually_evFin_integral (c' j))`. Use `⟨(Set.finite_iUnion hfin).toFinset, ?_⟩` and prove the remaining obligations. Introduce `w hw a ha hai y hy`. Establish `hc' : ∀ j, GlobalTheory.AdelicU.evFin F w (c' j) ∈ w.adicCompletionIntegers F`. Introduce `j`.

Assume the negation of the conclusion as `h`. Conclude with `hw ((Set.Finite.mem_toFinset _).mpr (Set.mem_iUnion.mpr ⟨j, h⟩))`. Establish `hterm : ∀ j, a • (c j • incV (Nm j y)) = (a * c' j) • incV (D j • Nm j y)`. Introduce `j`. Establish `h1 : incV (D j • Nm j y) = D j • incV (Nm j y)`.

Use function extensionality and compare the values at `i`. Simplify using `[incV]`. Rewrite using `[h1, ← Nat.cast_smul_eq_nsmul (AF F), smul_smul, smul_smul]`. Use `congr 1`. Establish `h2 : (D j : F) ≠ 0` using `Nat.cast_ne_zero.mpr (hD0 j)`.

Simplify using `only [c', mul_assoc]`. Rewrite using `[← map_natCast (algebraMap F (AF F)), ← map_mul, inv_mul_cancel₀ h2, map_one, mul_one]`. Express the relevant statement in the definitionally equal form `a • (M *ᵥ incV y) ∈ _`. Rewrite using `[key, Finset.smul_sum]`. Use `AddSubgroup.sum_mem _ fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[hterm j]`. Use `AddSubgroup.subset_closure ⟨a * c' j, ?_, ?_, D j • Nm j y, hDL j y hy, rfl⟩` and prove the remaining obligations. Introduce `u hu`. Rewrite using `[smul_eq_mul, ← mul_assoc, ← smul_eq_mul u a, ha u hu, zero_mul]`. Rewrite using `[map_mul]`.

Conclude with `mul_mem hai (hc' j)`.
-/
theorem exists_finset_smul_mulVec_mem_closure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (M : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) (L : Submodule (𝓞 E) (Fin n → E)), L.IsLattice E →
    ∃ S₁ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), ∀ w ∉ S₁, ∀ a : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) a →
      GlobalTheory.AdelicU.evFin F w a ∈ w.adicCompletionIntegers F → ∀ y ∈ L,
      a • (M *ᵥ fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y i)) ∈
        AddSubgroup.closure {z | ∃ b : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) b ∧
          GlobalTheory.AdelicU.evFin F w b ∈ w.adicCompletionIntegers F ∧
          ∃ y' ∈ L, z = b • fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y' i)} := by
  intro F E _ _ _ _ _ n M L hL
  classical
  let bF := Module.finBasis F E
  let B := Algebra.TensorProduct.basis (AF F) bF
  let c : Fin n × Fin n × Fin (Module.finrank F E) → AF F := fun j => B.repr (M j.1 j.2.1) j.2.2
  let Nm : Fin n × Fin n × Fin (Module.finrank F E) → (Fin n → E) →ₗ[E] (Fin n → E) := fun j =>
    (LinearMap.single E (fun _ : Fin n => E) j.1) ∘ₗ (bF j.2.2 • LinearMap.proj j.2.1)
  let incV : (Fin n → E) → (Fin n → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) := fun y i =>
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y i)
  have key : ∀ y, (M *ᵥ incV y) = ∑ j, c j • incV (Nm j y) := by
    intro y
    funext r
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply]
    rw [Fintype.sum_prod_type]
    symm
    rw [Finset.sum_eq_single r]
    · rw [Fintype.sum_prod_type]
      symm
      refine Finset.sum_congr rfl fun q _ => ?_
      conv_lhs => rw [← B.sum_repr (M r q)]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Nm, incV, B, c, Algebra.TensorProduct.basis_apply, smul_mul_assoc, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]
    · intro p _ hp
      simp [Nm, incV, Pi.single_apply, Ne.symm hp]
    · simp
  choose D hD0 hDL using fun j => exists_nsmul_map_mem L hL (Nm j)
  let c' : Fin n × Fin n × Fin (Module.finrank F E) → AF F :=
    fun j => c j * algebraMap F (AF F) ((D j : F)⁻¹)
  have hfin : ∀ j, {w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F |
      ¬ GlobalTheory.AdelicU.evFin F w (c' j) ∈ w.adicCompletionIntegers F}.Finite :=
    fun j => Filter.eventually_cofinite.mp (GlobalTheory.AlgCountDim.eventually_evFin_integral (c' j))
  refine ⟨(Set.finite_iUnion hfin).toFinset, ?_⟩
  intro w hw a ha hai y hy
  have hc' : ∀ j, GlobalTheory.AdelicU.evFin F w (c' j) ∈ w.adicCompletionIntegers F := by
    intro j
    by_contra h
    exact hw ((Set.Finite.mem_toFinset _).mpr (Set.mem_iUnion.mpr ⟨j, h⟩))
  have hterm : ∀ j, a • (c j • incV (Nm j y)) = (a * c' j) • incV (D j • Nm j y) := by
    intro j
    have h1 : incV (D j • Nm j y) = D j • incV (Nm j y) := by
      funext i; simp [incV]
    rw [h1, ← Nat.cast_smul_eq_nsmul (AF F), smul_smul, smul_smul]
    congr 1
    have h2 : (D j : F) ≠ 0 := Nat.cast_ne_zero.mpr (hD0 j)
    simp only [c', mul_assoc]
    rw [← map_natCast (algebraMap F (AF F)), ← map_mul, inv_mul_cancel₀ h2, map_one, mul_one]
  change a • (M *ᵥ incV y) ∈ _
  rw [key, Finset.smul_sum]
  refine AddSubgroup.sum_mem _ fun j _ => ?_
  rw [hterm j]
  refine AddSubgroup.subset_closure ⟨a * c' j, ?_, ?_, D j • Nm j y, hDL j y hy, rfl⟩
  · intro u hu
    rw [smul_eq_mul, ← mul_assoc, ← smul_eq_mul u a, ha u hu, zero_mul]
  · rw [map_mul]; exact mul_mem hai (hc' j)

end GlobalTheory.AdelicLatticeIntegral
