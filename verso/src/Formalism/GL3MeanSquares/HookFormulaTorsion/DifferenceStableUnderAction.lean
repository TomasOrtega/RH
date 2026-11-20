import Mathlib
import Formalism.GL3MeanSquares.OrbitPointsDistinct
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.BehrendSets.TranslateMean
import Formalism.BehrendSets.FinalE

namespace Formalism.HermitianLattices.FiltrationBoundaryCriterion

namespace PfM

section
open Formalism.HermitianLattices.FiltrationBoundaryCriterion Formalism.FrobeniusOrbits

/- English proof (translation)
Introduce `e φ hφ`. Establish `hp : ∀ g : GG e, (placeOf g).2 = g.2 ∧ (placeOf g).1 = (g.1.1 * g.1.2, 1)`. Introduce `g`. Break down `Int.units_eq_one_or g.1.2 with hg | hg` into its components or cases. Use `⟨by simp [placeOf, hg], ?_⟩` and prove the remaining obligations.

Apply the tactic sequence `ext <;> simp [placeOf, hg]`. Use `⟨by simp [placeOf, hg, cc], ?_⟩` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp [placeOf, hg, cc, c0]`. Establish `hsq : ∀ x : ℤˣ, ∀ i : ℤ, x ^ i = if Even i then 1 else x`. Introduce `x i`.

Break down `Int.even_or_odd' i with ⟨k, rfl | rfl⟩` into its components or cases. Simplify using `[zpow_mul, Int.units_sq]`. Establish `: ¬ Even (2 * k + 1)` using `by simp`. Simplify using `[zpow_add, zpow_mul, Int.units_sq]`. Use `⟨⟨?_, rfl, ?_, orderOf_inv φ⟩, ?_⟩` and prove the remaining obligations.

Apply the tactic sequence `rcases hφ with h | h <;> rw [Prod.fst_inv, h] <;> ext <;> simp [c0]`. Rewrite using `[Prod.snd_inv, orderOf_inv]`. Introduce `τ i`. Apply the tactic sequence `have h2 : φ.1.2 = -1 := by rcases hφ with h | h <;> simp [h, c0]`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[mem_Psi_iff, mem_Psi_iff]`. Establish `: (φ ^ i * τ).1.2 = φ.1.2 ^ i * τ.1.2` using `by simp`. Rewrite using `[this, h2, hsq]`. Apply the tactic sequence `rcases Int.units_eq_one_or τ.1.2 with ht | ht <;> by_cases hi : Even i <;> simp [ht, hi]`. Rewrite using `[(hp _).1]`.

Simplify using the standard rewrite rules. Introduce `h`. Rewrite using `[(hp _).2, (hp _).2]`. Establish `a1 : (φ ^ i * τ).1.1 = φ.1.1 ^ i * τ.1.1` using `by simp`. Establish `a2 : (φ ^ i * τ).1.2 = φ.1.2 ^ i * τ.1.2` using `by simp`.

Rewrite using `[a1, a2, h, hsq, hsq]`. Apply the tactic sequence `by_cases hi : Even i <;> ext <;> simp [hi, c0]`. Introduce `h`. Rewrite using `[(hp _).2, (hp _).2]`. Establish `a1 : (φ ^ i * τ).1.1 = φ.1.1 ^ i * τ.1.1` using `by simp`.

Establish `a2 : (φ ^ i * τ).1.2 = φ.1.2 ^ i * τ.1.2` using `by simp`. Rewrite using `[a1, a2, h, hsq, hsq]`. Apply the tactic sequence `by_cases hi : Even i <;> ext <;> simp [hi, sg]`.
-/
theorem orbitsInt : OrbitsInt := by
  intro e φ hφ
  have hp : ∀ g : GG e, (placeOf g).2 = g.2 ∧ (placeOf g).1 = (g.1.1 * g.1.2, 1) := by
    intro g
    rcases Int.units_eq_one_or g.1.2 with hg | hg
    · refine ⟨by simp [placeOf, hg], ?_⟩
      ext <;> simp [placeOf, hg]
    · refine ⟨by simp [placeOf, hg, cc], ?_⟩
      ext <;> simp [placeOf, hg, cc, c0]
  have hsq : ∀ x : ℤˣ, ∀ i : ℤ, x ^ i = if Even i then 1 else x := by
    intro x i
    rcases Int.even_or_odd' i with ⟨k, rfl | rfl⟩
    · simp [zpow_mul, Int.units_sq]
    · have : ¬ Even (2 * k + 1) := by simp
      simp [zpow_add, zpow_mul, Int.units_sq]
  refine ⟨⟨?_, rfl, ?_, orderOf_inv φ⟩, ?_⟩
  · rcases hφ with h | h <;> rw [Prod.fst_inv, h] <;> ext <;> simp [c0]
  · rw [Prod.snd_inv, orderOf_inv]
  · intro τ i
    have h2 : φ.1.2 = -1 := by rcases hφ with h | h <;> simp [h, c0]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [mem_Psi_iff, mem_Psi_iff]
      have : (φ ^ i * τ).1.2 = φ.1.2 ^ i * τ.1.2 := by simp
      rw [this, h2, hsq]
      rcases Int.units_eq_one_or τ.1.2 with ht | ht <;> by_cases hi : Even i <;> simp [ht, hi]
    · rw [(hp _).1]; simp
    · intro h
      rw [(hp _).2, (hp _).2]
      have a1 : (φ ^ i * τ).1.1 = φ.1.1 ^ i * τ.1.1 := by simp
      have a2 : (φ ^ i * τ).1.2 = φ.1.2 ^ i * τ.1.2 := by simp
      rw [a1, a2, h, hsq, hsq]
      by_cases hi : Even i <;> ext <;> simp [hi, c0]
    · intro h
      rw [(hp _).2, (hp _).2]
      have a1 : (φ ^ i * τ).1.1 = φ.1.1 ^ i * τ.1.1 := by simp
      have a2 : (φ ^ i * τ).1.2 = φ.1.2 ^ i * τ.1.2 := by simp
      rw [a1, a2, h, hsq, hsq]
      by_cases hi : Even i <;> ext <;> simp [hi, sg]

end

section
open Formalism.HermitianLattices.FiltrationBoundaryCriterion Formalism.FrobeniusOrbits NumberField Ideal

/- English proof (translation)
Introduce `R _ I g k hg A hA m`. Establish `hmul : ∀ (a b : ℕ) (X Y : Matrix (Fin k) (Fin k) R), (∀ i j, X i j ∈ I ^ a) → (∀ i j, Y i j ∈ I ^ b) → ∀ i j, (X * Y) i j ∈ I ^ (a + b)`. Introduce `a b X Y hX hY i j`. Rewrite using `[Matrix.mul_apply]`. Conclude with `Ideal.sum_mem _ fun l _ => by rw [pow_add]; exact Ideal.mul_mem_mul (hX i l) (hY l j)`.

Proceed by induction on `m with`. Consider the case `zero => simpa using hA`. Consider the case `succ m ih => set B := A ^ g ^ m with hB`. Establish `hBI : ∀ i j, (B - 1) i j ∈ I` using `fun i j => Ideal.pow_le_self (by omega) (ih i j)`. Establish `hpow : ∀ n : ℕ, ∀ i j, (B ^ n - 1) i j ∈ I`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro i j`. Simplify using the standard rewrite rules. Consider the case `succ n ihn`.

Introduce `i j`. Establish `: B ^ (n + 1) - 1 = (B ^ n - 1) * (B - 1) + (B ^ n - 1) + (B - 1)`. Rewrite using `[pow_succ]`. Use `noncomm_ring`. Rewrite using `[this]`.

Use `I.add_mem (I.add_mem ?_ (ihn i j)) (hBI i j)` and prove the remaining obligations. Use `hmul 1 1 _ _ (by simpa using ihn) (by simpa using hBI) i j` as an intermediate fact. Conclude with `Ideal.pow_le_self (by omega) this`. Establish `hgeom : B ^ g - 1 = (B - 1) * ∑ n ∈ Finset.range g, B ^ n`. Use `(Commute.one_right B).mul_geom_sum₂ g` as an intermediate fact.

Simplify using `using this.symm`. Establish `hsum : ∀ i j, (∑ n ∈ Finset.range g, B ^ n) i j ∈ I ^ 1`. Introduce `i j`. Establish `: (∑ n ∈ Finset.range g, B ^ n) = (∑ n ∈ Finset.range g, (B ^ n - 1)) + (g : R) • 1`. Rewrite using `[Finset.sum_sub_distrib]`.

Simplify using `[Matrix.smul_one_eq_diagonal, nsmul_eq_mul]`. Use extensionality with `i j`. Simplify using `[Matrix.natCast_apply, Matrix.diagonal_apply]`. Rewrite using `[this, pow_one, Matrix.add_apply, Matrix.sum_apply]`. Use `I.add_mem (Ideal.sum_mem _ fun n _ => hpow n i j) ?_` and prove the remaining obligations.

Rewrite using `[Matrix.smul_apply]`. Conclude with `I.mul_mem_right _ hg`. Introduce `i j`. Establish `e1 : A ^ g ^ (m + 1) = B ^ g` using `by rw [hB, ← pow_mul, pow_succ]`. Rewrite using `[e1, hgeom]`.

Conclude with `hmul (m + 1) 1 _ _ ih hsum i j`.
-/
theorem congruencePowers : CongruencePowers := by
  intro R _ I g k hg A hA m

  have hmul : ∀ (a b : ℕ) (X Y : Matrix (Fin k) (Fin k) R), (∀ i j, X i j ∈ I ^ a) →
      (∀ i j, Y i j ∈ I ^ b) → ∀ i j, (X * Y) i j ∈ I ^ (a + b) := by
    intro a b X Y hX hY i j
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun l _ => by rw [pow_add]; exact Ideal.mul_mem_mul (hX i l) (hY l j)
  induction m with
  | zero => simpa using hA
  | succ m ih =>
    set B := A ^ g ^ m with hB
    have hBI : ∀ i j, (B - 1) i j ∈ I := fun i j => Ideal.pow_le_self (by omega) (ih i j)
    have hpow : ∀ n : ℕ, ∀ i j, (B ^ n - 1) i j ∈ I := by
      intro n
      induction n with
      | zero => intro i j; simp
      | succ n ihn =>
        intro i j
        have : B ^ (n + 1) - 1 = (B ^ n - 1) * (B - 1) + (B ^ n - 1) + (B - 1) := by
          rw [pow_succ]; noncomm_ring
        rw [this]
        refine I.add_mem (I.add_mem ?_ (ihn i j)) (hBI i j)
        have := hmul 1 1 _ _ (by simpa using ihn) (by simpa using hBI) i j
        exact Ideal.pow_le_self (by omega) this
    have hgeom : B ^ g - 1 = (B - 1) * ∑ n ∈ Finset.range g, B ^ n := by
      have := (Commute.one_right B).mul_geom_sum₂ g
      simpa using this.symm
    have hsum : ∀ i j, (∑ n ∈ Finset.range g, B ^ n) i j ∈ I ^ 1 := by
      intro i j
      have : (∑ n ∈ Finset.range g, B ^ n) = (∑ n ∈ Finset.range g, (B ^ n - 1)) + (g : R) • 1 := by
        rw [Finset.sum_sub_distrib]; simp [Matrix.smul_one_eq_diagonal, nsmul_eq_mul]
        ext i j; simp [Matrix.natCast_apply, Matrix.diagonal_apply]
      rw [this, pow_one, Matrix.add_apply, Matrix.sum_apply]
      refine I.add_mem (Ideal.sum_mem _ fun n _ => hpow n i j) ?_
      rw [Matrix.smul_apply]
      exact I.mul_mem_right _ hg
    intro i j
    have e1 : A ^ g ^ (m + 1) = B ^ g := by rw [hB, ← pow_mul, pow_succ]
    rw [e1, hgeom]
    exact hmul (m + 1) 1 _ _ ih hsum i j

end

section
open Formalism.HermitianLattices.FiltrationBoundaryCriterion Formalism.FrobeniusOrbits

end

section
open Formalism.HermitianLattices.FiltrationBoundaryCriterion Formalism.FrobeniusOrbits

/- English proof (translation)
Rewrite using `[((orbitsInt e φ hφ).2 τ i).2.1, map_mul, map_zpow, toAdd_mul, toAdd_zpow, add_comm]`.
-/
theorem coord {e : ℕ} (ι : HGrp e ≃* Multiplicative (ZMod (2 ^ e))) (φ τ : GG e)
    (hφ : φ.1 = c0 ∨ φ.1 = ((1 : ℤˣ), (-1 : ℤˣ))) (i : ℤ) :
    Multiplicative.toAdd (ι (placeOf (φ ^ i * τ)).2) =
      Multiplicative.toAdd (ι τ.2) + i • Multiplicative.toAdd (ι φ.2) := by
  rw [((orbitsInt e φ hφ).2 τ i).2.1, map_mul, map_zpow, toAdd_mul, toAdd_zpow, add_comm]

end

section
open Formalism.HermitianLattices.FiltrationBoundaryCriterion Formalism.FrobeniusOrbits

end

section
open Formalism.HermitianLattices.FiltrationBoundaryCriterion Formalism.FrobeniusOrbits

end

section
open Formalism.HermitianLattices.FiltrationBoundaryCriterion Formalism.FrobeniusOrbits NumberField IsDedekindDomain
open scoped TensorProduct

/- English proof (translation)
Use extensionality with `i l`. Simplify using `[Formalism.UG.bc, Formalism.UG.prV, Formalism.UG.inclE]`.
-/
theorem bc_pr_incl {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (k : ℕ)
    (w : HeightOneSpectrum (𝓞 F)) (γ₀ : Matrix.GeneralLinearGroup (Fin k) E) :
    Formalism.UG.bc (Formalism.UG.prV (E := E) w) (Formalism.UG.bc (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ₀) =
      Formalism.UG.bc (Formalism.UG.inclE (F := F) (w.adicCompletion F)) γ₀ := by
  ext i l
  simp [Formalism.UG.bc, Formalism.UG.prV, Formalism.UG.inclE]

end

end PfM

open Formalism.FrobeniusOrbits

/- English proof (translation)
The claim follows from `PfM.congruencePowers`.
-/
theorem congruence_powers : CongruencePowers := PfM.congruencePowers

end Formalism.HermitianLattices.FiltrationBoundaryCriterion
