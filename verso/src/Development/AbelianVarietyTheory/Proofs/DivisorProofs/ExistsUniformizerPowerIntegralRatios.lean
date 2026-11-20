import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntBTmulBasis
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

namespace GlobalTheory

/- English proof (translation)
Introduce `L _ _ C _ _ ι r e N l c i i' h v β`. Use `set φ := Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι with hφ`. Set `P : (Fin r → v.adicCompletion ℚ ⊗[ℚ] L) → Prop` to `fun β => ∑ k, φ ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] l k) * (∑ i'', φ (β i'') * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i'')) * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] c k) = φ (β i') * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i)`. Establish `hzero : P 0` using `by simp [P]`. Establish `hadd : ∀ β₁ β₂, P β₁ → P β₂ → P (β₁ + β₂)`.

Introduce `β₁ β₂ h₁ h₂`. Simplify using `only [P, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib, mul_add] at h₁ h₂ ⊢`. Rewrite using `[h₁, h₂]`. Establish `hpure : ∀ (a : v.adicCompletion ℚ) (γ : Fin r → L), P (fun j => a ⊗ₜ[ℚ] γ j)`. Introduce `a γ`.

Simplify using `only [P, hφ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ← TensorProduct.tmul_sum]`. Rewrite using `[h γ]`. Establish `hsingle : ∀ j x, P (Pi.single j x)`. Introduce `j x`. Proceed by induction on `x using TensorProduct.induction_on with`.

Consider the case `zero => simpa using hzero`. Consider the case `tmul a m`. Establish `: (Pi.single j (a ⊗ₜ[ℚ] m) : Fin r → v.adicCompletion ℚ ⊗[ℚ] L) = fun j' => a ⊗ₜ[ℚ] (Pi.single j m : Fin r → L) j'`. Use function extensionality and compare the values at `j'`. Distinguish the cases in `hj : j' = j`.

Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hj]`. Rewrite using `[this]`. Conclude with `hpure a _`.

Consider the case `add x y hx hy`. Rewrite using `[Pi.single_add]`. Conclude with `hadd _ _ hx hy`. Establish `hall : P (∑ j, Pi.single j (β j))` using `Finset.sum_induction _ P hadd hzero (fun j _ => hsingle j (β j))`. Rewrite `hall` using `[Finset.univ_sum_single]`.

Conclude with `hall`.
-/
theorem adicCompletion_tensor_matrixUnit_identity : ∀ (L : Type) [Field L] [NumberField L] (C : Type) [Ring C] [Algebra ℚ C] (ι : L →ₐ[ℚ] C) (r : ℕ)
    (e : Fin r → C) (N : ℕ) (l : Fin N → L) (c : Fin N → C) (i i' : Fin r),
    (∀ β : Fin r → L, ∑ k, ι (l k) * (∑ i'', ι (β i'') * e i'') * c k = ι (β i') * e i) →
    ∀ (v : HeightOneSpectrum ℤ) (β : Fin r → v.adicCompletion ℚ ⊗[ℚ] L),
    ∑ k, Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] l k) *
        (∑ i'', Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι (β i'') *
          ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i'')) * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] c k) =
      Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι (β i') * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i) := by
  intro L _ _ C _ _ ι r e N l c i i' h v β
  set φ := Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι with hφ
  let P : (Fin r → v.adicCompletion ℚ ⊗[ℚ] L) → Prop := fun β =>
    ∑ k, φ ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] l k) *
        (∑ i'', φ (β i'') * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i'')) * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] c k) =
      φ (β i') * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i)
  have hzero : P 0 := by simp [P]
  have hadd : ∀ β₁ β₂, P β₁ → P β₂ → P (β₁ + β₂) := by
    intro β₁ β₂ h₁ h₂
    simp only [P, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib, mul_add] at h₁ h₂ ⊢
    rw [h₁, h₂]
  have hpure : ∀ (a : v.adicCompletion ℚ) (γ : Fin r → L), P (fun j => a ⊗ₜ[ℚ] γ j) := by
    intro a γ
    simp only [P, hφ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ← TensorProduct.tmul_sum]
    rw [h γ]
  have hsingle : ∀ j x, P (Pi.single j x) := by
    intro j x
    induction x using TensorProduct.induction_on with
    | zero => simpa using hzero
    | tmul a m =>
      have : (Pi.single j (a ⊗ₜ[ℚ] m) : Fin r → v.adicCompletion ℚ ⊗[ℚ] L) =
          fun j' => a ⊗ₜ[ℚ] (Pi.single j m : Fin r → L) j' := by
        funext j'
        by_cases hj : j' = j
        · subst hj; simp
        · simp [Pi.single_apply, hj]
      rw [this]; exact hpure a _
    | add x y hx hy =>
      rw [Pi.single_add]; exact hadd _ _ hx hy
  have hall : P (∑ j, Pi.single j (β j)) :=
    Finset.sum_induction _ P hadd hzero (fun j _ => hsingle j (β j))
  rw [Finset.univ_sum_single] at hall
  exact hall

end GlobalTheory
