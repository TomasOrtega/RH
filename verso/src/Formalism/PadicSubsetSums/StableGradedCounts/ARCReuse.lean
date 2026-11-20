import Formalism.PadicSubsetSums.CentralIdempotents.WindowSums
import Formalism.WindowSums.PowerSeriesRelationList
import Formalism.FrobeniusContraction.FrobeniusContractionProofs.ContractBij
import Formalism.EisensteinCokernelLengths.FactorialValuationBounds.ToolsB
import Formalism.EisensteinCokernelLengths.FactorialValuationBounds.FactorialValuationBoundsProofFact
import Formalism.EisensteinCokernelLengths.FactorialValuationBounds.LagrangeIdealSgProof
import Mathlib
import Formalism.GaloisIrreducibility.NoSolvableTransitive
import Formalism.ResultantValuation.ResultantAdjugateProofs.Adjugate
import Formalism.ResultantValuation.ResultantAdjugateProofs.Mobius
import Formalism.ResultantValuation.ResultantAdjugateProofs.Window
import Formalism.ResultantValuation.ResultantAdjugateProofs.Koszul
import Formalism.ResultantValuation.ResultantAdjugateProofs.Parabolic
import Formalism.ResultantValuation.BoundedCubic
import Formalism.ResultantValuation.ResultantAdjugateProofs.Laplace
import Formalism.ResultantValuation.PrimePairDyadicDisjointAlt

namespace Formalism.IrreducibleCountingLemmas.WindowSums

open Polynomial

/- English proof (translation)
The claim follows from `Formalism.ZetaNonvanishing.EisensteinCokernelLengthsFacts.FactorialValuationBoundsFacts.lenBound2`.
-/
theorem colength_bound_two_layers : ColengthTwoStep := Formalism.ZetaNonvanishing.EisensteinCokernelLengthsFacts.FactorialValuationBoundsFacts.lenBound2

/- English proof (translation)
Introduce `l _ D₁ D₂ ρ hd hρ`. Establish `hass : ∀ a ∈ D₁, ∀ b ∈ D₁ ∪ D₂, a ≠ b → Associated (((a : ℤ) : ℤ_[l]) - ((b : ℤ) : ℤ_[l])) ((l : ℤ_[l]) ^ (0 + padicValInt l (a - b)))`. Introduce `a _ b _ hab`. Establish `hne : a - b ≠ 0` using `sub_ne_zero.mpr hab`. Use `set v := padicValInt l (a - b) with hv`.

Take `⟨c, hc⟩ : (l : ℤ) ^ v ∣ a - b` from `padicValInt_dvd (a - b)`. Establish `hcn : ¬ (l : ℤ) ∣ c`. Introduce `⟨c', hc'⟩`. Establish `: (l : ℤ) ^ (v + 1) ∣ a - b` using `⟨c', by rw [hc, hc']; ring⟩`. Establish `h2` using `(padicValInt_dvd_iff (p := l) _ (a - b)).mp this`.

Break down `h2 with h2 | h2` into its components or cases. Conclude with `hne h2`. Use linear arithmetic over natural numbers and integers. Establish `hu : IsUnit ((c : ℤ) : ℤ_[l])`. Rewrite using `[PadicInt.isUnit_iff, PadicInt.norm_intCast_eq_one_iff]`.

Conclude with `((Nat.prime_iff_prime_int.mp (Fact.out : l.Prime)).coprime_iff_not_dvd.mpr hcn).symm`. Rewrite using `[zero_add, ← Int.cast_sub, hc]`. Use `push_cast`. Conclude with `(associated_mul_unit_left _ _ hu)`. Establish `h` using `Formalism.ZetaNonvanishing.LIFTV.lagrangeIdealSg_proof l ℤ_[l] 0 D₁ D₂ (fun a => ((a : ℤ) : ℤ_[l])) hd hass`.

Use `set E := D₁.sup fun a => (∑ b ∈ D₂, (0 + padicValInt l (a - b))) + ∑ a' ∈ D₁.erase a, (0 + padicValInt l (a - a')) with hE`. Establish `hle : E ≤ ρ`. Rewrite using `[hE]`. Apply `Finset.sup_le` to reduce the goal to its premises. Introduce `a ha`.

Simplify using `using hρ a ha`. Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hle`. Rewrite using `[pow_add, mul_comm, C_mul]`. Conclude with `Ideal.mul_mem_left _ _ h`.
-/
theorem lagrange_resolvent_T : LagrangeT := by
  intro l _ D₁ D₂ ρ hd hρ
  have hass : ∀ a ∈ D₁, ∀ b ∈ D₁ ∪ D₂, a ≠ b →
      Associated (((a : ℤ) : ℤ_[l]) - ((b : ℤ) : ℤ_[l])) ((l : ℤ_[l]) ^ (0 + padicValInt l (a - b))) := by
    intro a _ b _ hab
    have hne : a - b ≠ 0 := sub_ne_zero.mpr hab
    set v := padicValInt l (a - b) with hv
    obtain ⟨c, hc⟩ : (l : ℤ) ^ v ∣ a - b := padicValInt_dvd (a - b)
    have hcn : ¬ (l : ℤ) ∣ c := by
      intro ⟨c', hc'⟩
      have : (l : ℤ) ^ (v + 1) ∣ a - b := ⟨c', by rw [hc, hc']; ring⟩
      have h2 := (padicValInt_dvd_iff (p := l) _ (a - b)).mp this
      rcases h2 with h2 | h2
      · exact hne h2
      · omega
    have hu : IsUnit ((c : ℤ) : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_intCast_eq_one_iff]
      exact ((Nat.prime_iff_prime_int.mp (Fact.out : l.Prime)).coprime_iff_not_dvd.mpr hcn).symm
    rw [zero_add, ← Int.cast_sub, hc]
    push_cast
    exact (associated_mul_unit_left _ _ hu)
  have h := Formalism.ZetaNonvanishing.LIFTV.lagrangeIdealSg_proof l ℤ_[l] 0 D₁ D₂ (fun a => ((a : ℤ) : ℤ_[l])) hd hass
  set E := D₁.sup fun a => (∑ b ∈ D₂, (0 + padicValInt l (a - b))) +
    ∑ a' ∈ D₁.erase a, (0 + padicValInt l (a - a')) with hE
  have hle : E ≤ ρ := by
    rw [hE]; apply Finset.sup_le; intro a ha
    simpa using hρ a ha
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [pow_add, mul_comm, C_mul]
  exact Ideal.mul_mem_left _ _ h

/- English proof (translation)
Introduce `R V _ _ _ T F c k a`. Proceed by induction on `a with`. Consider the case `zero => intro _ x hx`. Simplify using `using hx`. Consider the case `succ a ih`.

Introduce `h x hx`. Establish `hy` using `ih (fun i h1 h2 => h i h1 (by omega)) x hx`. Rewrite using `[← add_assoc, Finset.prod_Ico_succ_top (by omega), mul_comm, map_mul, Module.End.mul_apply]`. Use `h (k + a) (by omega) (by omega) _ hy` as an intermediate fact. Simplify `this` using `[Module.algebraMap_end_apply]`.
-/
theorem filtered_product : FiltProd := by
  intro R V _ _ _ T F c k a
  induction a with
  | zero => intro _ x hx; simpa using hx
  | succ a ih =>
    intro h x hx
    have hy := ih (fun i h1 h2 => h i h1 (by omega)) x hx
    rw [← add_assoc, Finset.prod_Ico_succ_top (by omega), mul_comm, map_mul, Module.End.mul_apply]
    have := h (k + a) (by omega) (by omega) _ hy
    simpa [Module.algebraMap_end_apply] using this

/- English proof (translation)
Establish `hpow : ∀ (n : ℕ) (z : V), ((W.mapQ W T hW : Module.End R (V ⧸ W)) ^ n) (W.mkQ z) = W.mkQ ((T ^ n) z)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro z`. Simplify using the standard rewrite rules.

Consider the case `succ n ih`. Introduce `z`. Rewrite using `[pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply]`. Establish `: (W.mapQ W T hW : Module.End R (V ⧸ W)) (W.mkQ z) = W.mkQ (T z)` using `rfl`. Rewrite using `[this, ih]`.

Proceed by induction on `P using Polynomial.induction_on' with`. Consider the case `add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]`. Consider the case `monomial n r`. Simplify using `only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, hpow, map_smul]`.
-/
theorem aeval_mapQ {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (T : Module.End R V)
    (W : Submodule R V) (hW : W ≤ W.comap T) (P : R[X]) (y : V) :
    aeval (W.mapQ W T hW : Module.End R (V ⧸ W)) P (W.mkQ y) = W.mkQ (aeval T P y) := by
  have hpow : ∀ (n : ℕ) (z : V),
      ((W.mapQ W T hW : Module.End R (V ⧸ W)) ^ n) (W.mkQ z) = W.mkQ ((T ^ n) z) := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ n ih =>
      intro z
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply]
      have : (W.mapQ W T hW : Module.End R (V ⧸ W)) (W.mkQ z) = W.mkQ (T z) := rfl
      rw [this, ih]
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial n r =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, hpow,
      map_smul]

end Formalism.IrreducibleCountingLemmas.WindowSums
