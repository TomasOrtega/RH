import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo

namespace GlobalTheory.CuspGeo

/- English proof (translation)
Set `A : (Fin N → ℤ) →ₗ[ℤ] (Fin n → E)` to `Fintype.linearCombination ℤ e`. Set `B : (Fin N → ℤ) →ₗ[ℤ] (Fin n → E)` to `Fintype.linearCombination ℤ e₀`. Establish `hA : ∀ z, A z = ∑ i, z i • e i` using `fun z => Fintype.linearCombination_apply ℤ e z`. Establish `hB : ∀ z, B z = ∑ i, z i • e₀ i` using `fun z => Fintype.linearCombination_apply ℤ e₀ z`. Establish `hAs : ∀ j, A (Pi.single j 1) = e j` using `fun j => by simp [A]`.

Establish `hBs : ∀ j, B (Pi.single j 1) = e₀ j` using `fun j => by simp [B]`. Establish `hAinj : Function.Injective A`. Use `(injective_iff_map_eq_zero A).2 fun z hz => ?_` and prove the remaining obligations. Rewrite `hz` using `[hA]`. Conclude with `funext (Fintype.linearIndependent_iff.1 hli z hz)`.

Establish `heint : ∀ j i, IsIntegral ℤ (e j i)` using `fun j => (he _).2 ⟨Pi.single j 1, by rw [← hA, hAs]⟩`. Set `S : Submodule ℤ ((Fin n → E) × (Fin n → E))` to `LinearMap.range (A.prod B)`. Establish `hk : ∀ (k : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (z : Fin N → ℤ), (integralBasis E k : E) • (A z, B z) ∈ S`. Introduce `k z`. Establish `h1 : (integralBasis E k : E) • (A z, B z) = ∑ j, z j • ((integralBasis E k : E) • (e j, e₀ j))`.

Establish `h0 : (A z, B z) = ∑ j, z j • (e j, e₀ j)`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Rewrite using `[Prod.fst_sum]`. Conclude with `hA z`. Rewrite using `[Prod.snd_sum]`.

Conclude with `hB z`. Rewrite using `[h0, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[smul_comm (z j)]`. Rewrite using `[h1]`.

Use `S.sum_mem fun j _ => S.smul_mem _ ?_` and prove the remaining obligations. Establish `hint : ∀ i, IsIntegral ℤ (((integralBasis E k : E) • e j) i)` using `fun i => by`. Rewrite using `[Pi.smul_apply, smul_eq_mul, integralBasis_apply]`. Conclude with `(RingOfIntegers.isIntegral_coe _).mul (heint j i)`. Take `⟨w, hw⟩` from `(he _).1 hint`.

Use `⟨w, ?_⟩` and prove the remaining obligations. Establish `hw₀` using `h k j w hw`. Rewrite `hw` using `[← hA]`. Rewrite `hw₀` using `[← hB]`. Conclude with `Prod.ext hw.symm hw₀.symm`.

Establish `ha : ∀ a : E, IsIntegral ℤ a → ∀ z : Fin N → ℤ, a • (A z, B z) ∈ S`. Introduce `a hai z`. Set `a' : 𝓞 E` to `⟨a, hai⟩`. Establish `h1 : a = ∑ k, (RingOfIntegers.basis E).repr a' k • (integralBasis E k : E)`. Establish `h2` using `congrArg (algebraMap (𝓞 E) E) ((RingOfIntegers.basis E).sum_repr a')`.

Rewrite `h2` using `[map_sum]`. Simplify using `only [map_zsmul] at h2`. Simplify using `only [integralBasis_apply]`. Conclude with `h2.symm`. Rewrite using `[h1, Finset.sum_smul]`.

Use `S.sum_mem fun k _ => ?_` and prove the remaining obligations. Rewrite using `[smul_assoc]`. Conclude with `S.smul_mem _ (hk k z)`. Establish `hu : ∀ j : Fin n, ∃ z : Fin N → ℤ, (Pi.single j 1 : Fin n → E) = A z` using `fun j => by`. Take `⟨z, hz⟩` from `(he (Pi.single j 1)).1 fun i => by`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `using isIntegral_one`. Simplify `isIntegral_zero` using `[hij]`. Conclude with `⟨z, by rw [hA]; exact hz⟩`.

Use `choose c hc using hu`. Use `⟨Matrix.of fun i j => B (c j) i, fun i j => (he₀ _).2 ⟨c j, hB _⟩ i, fun l => ?_⟩` and prove the remaining obligations. Establish `hs : ∑ j, e l j • (A (c j), B (c j)) ∈ S` using `S.sum_mem fun j _ => ha _ (heint l j) _`. Take `⟨w, hw⟩` from `hs`. Establish `hw1 : A w = e l`.

Establish `h1` using `congrArg Prod.fst hw`. Rewrite `h1` using `[Prod.fst_sum]`. Simplify using `only [Prod.smul_mk, ← hc] at h1`. Use `Eq.trans h1 ?_` and prove the remaining obligations. Use extensionality with `i`.

Simplify using `[Finset.sum_apply, Pi.single_apply]`. Establish `hw2 : B w = ∑ j, e l j • B (c j)`. Establish `h1` using `congrArg Prod.snd hw`. Rewrite `h1` using `[Prod.snd_sum]`. Conclude with `h1`.

Establish `hw3 : w = Pi.single l 1` using `hAinj (by rw [hw1, hAs])`. Rewrite using `[← hBs, ← hw3, hw2]`. Use extensionality with `i`. Simplify using `[Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]`.
-/
theorem exists_integralMatrix_of_same_multiplicationMatrices {E : Type*} [Field E] [NumberField E] {n N : ℕ}
    (e e₀ : Fin N → Fin n → E) (hli : LinearIndependent ℤ e)
    (he : ∀ u : Fin n → E, (∀ i, IsIntegral ℤ (u i)) ↔ ∃ z : Fin N → ℤ, u = ∑ i, z i • e i)
    (he₀ : ∀ u : Fin n → E, (∀ i, IsIntegral ℤ (u i)) ↔ ∃ z : Fin N → ℤ, u = ∑ i, z i • e₀ i)
    (h : ∀ (k : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (j : Fin N) (z : Fin N → ℤ),
      (integralBasis E k : E) • e j = ∑ i, z i • e i → (integralBasis E k : E) • e₀ j = ∑ i, z i • e₀ i) :
    ∃ M : Matrix (Fin n) (Fin n) E, (∀ i j, IsIntegral ℤ (M i j)) ∧ ∀ j, M *ᵥ e j = e₀ j := by
  classical
  let A : (Fin N → ℤ) →ₗ[ℤ] (Fin n → E) := Fintype.linearCombination ℤ e
  let B : (Fin N → ℤ) →ₗ[ℤ] (Fin n → E) := Fintype.linearCombination ℤ e₀
  have hA : ∀ z, A z = ∑ i, z i • e i := fun z => Fintype.linearCombination_apply ℤ e z
  have hB : ∀ z, B z = ∑ i, z i • e₀ i := fun z => Fintype.linearCombination_apply ℤ e₀ z
  have hAs : ∀ j, A (Pi.single j 1) = e j := fun j => by simp [A]
  have hBs : ∀ j, B (Pi.single j 1) = e₀ j := fun j => by simp [B]
  have hAinj : Function.Injective A := by
    refine (injective_iff_map_eq_zero A).2 fun z hz => ?_
    rw [hA] at hz
    exact funext (Fintype.linearIndependent_iff.1 hli z hz)
  have heint : ∀ j i, IsIntegral ℤ (e j i) := fun j => (he _).2 ⟨Pi.single j 1, by rw [← hA, hAs]⟩
  let S : Submodule ℤ ((Fin n → E) × (Fin n → E)) := LinearMap.range (A.prod B)
  have hk : ∀ (k : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (z : Fin N → ℤ),
      (integralBasis E k : E) • (A z, B z) ∈ S := by
    intro k z
    have h1 : (integralBasis E k : E) • (A z, B z)
        = ∑ j, z j • ((integralBasis E k : E) • (e j, e₀ j)) := by
      have h0 : (A z, B z) = ∑ j, z j • (e j, e₀ j) := by
        refine Prod.ext ?_ ?_
        · rw [Prod.fst_sum]; exact hA z
        · rw [Prod.snd_sum]; exact hB z
      rw [h0, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_comm (z j)]
    rw [h1]
    refine S.sum_mem fun j _ => S.smul_mem _ ?_
    have hint : ∀ i, IsIntegral ℤ (((integralBasis E k : E) • e j) i) := fun i => by
      rw [Pi.smul_apply, smul_eq_mul, integralBasis_apply]
      exact (RingOfIntegers.isIntegral_coe _).mul (heint j i)
    obtain ⟨w, hw⟩ := (he _).1 hint
    refine ⟨w, ?_⟩
    have hw₀ := h k j w hw
    rw [← hA] at hw
    rw [← hB] at hw₀
    exact Prod.ext hw.symm hw₀.symm
  have ha : ∀ a : E, IsIntegral ℤ a → ∀ z : Fin N → ℤ, a • (A z, B z) ∈ S := by
    intro a hai z
    let a' : 𝓞 E := ⟨a, hai⟩
    have h1 : a = ∑ k, (RingOfIntegers.basis E).repr a' k • (integralBasis E k : E) := by
      have h2 := congrArg (algebraMap (𝓞 E) E) ((RingOfIntegers.basis E).sum_repr a')
      rw [map_sum] at h2
      simp only [map_zsmul] at h2
      simp only [integralBasis_apply]
      exact h2.symm
    rw [h1, Finset.sum_smul]
    refine S.sum_mem fun k _ => ?_
    rw [smul_assoc]
    exact S.smul_mem _ (hk k z)
  have hu : ∀ j : Fin n, ∃ z : Fin N → ℤ, (Pi.single j 1 : Fin n → E) = A z := fun j => by
    obtain ⟨z, hz⟩ := (he (Pi.single j 1)).1 fun i => by
      by_cases hij : i = j
      · subst hij; simpa using isIntegral_one
      · simpa [hij] using isIntegral_zero
    exact ⟨z, by rw [hA]; exact hz⟩
  choose c hc using hu
  refine ⟨Matrix.of fun i j => B (c j) i, fun i j => (he₀ _).2 ⟨c j, hB _⟩ i, fun l => ?_⟩
  have hs : ∑ j, e l j • (A (c j), B (c j)) ∈ S := S.sum_mem fun j _ => ha _ (heint l j) _
  obtain ⟨w, hw⟩ := hs
  have hw1 : A w = e l := by
    have h1 := congrArg Prod.fst hw
    rw [Prod.fst_sum] at h1
    simp only [Prod.smul_mk, ← hc] at h1
    refine Eq.trans h1 ?_
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hw2 : B w = ∑ j, e l j • B (c j) := by
    have h1 := congrArg Prod.snd hw
    rw [Prod.snd_sum] at h1
    exact h1
  have hw3 : w = Pi.single l 1 := hAinj (by rw [hw1, hAs])
  rw [← hBs, ← hw3, hw2]
  ext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

/- English proof (translation)
Introduce `_ _ e e₀ he he₀ h` and use `exists_integralMatrix_of_same_multiplicationMatrices e e₀ he.1 he.2 he₀.2 h`.
-/
theorem exists_integral_matrix_of_same_mul : ∀ (I : AutInst) {N : ℕ} (e e₀ : Fin N → Fin I.n → I.E),
    IsZBasis I e → IsZBasis I e₀ →
    (∀ (k : Module.Free.ChooseBasisIndex ℤ (𝓞 I.E)) (j : Fin N) (z : Fin N → ℤ),
      (integralBasis I.E k : I.E) • e j = ∑ i, z i • e i → (integralBasis I.E k : I.E) • e₀ j = ∑ i, z i • e₀ i) →
    ∃ M : Matrix (Fin I.n) (Fin I.n) I.E, (∀ i j, IsIntegral ℤ (M i j)) ∧ ∀ j, M *ᵥ e j = e₀ j :=
  fun _ _ e e₀ he he₀ h => exists_integralMatrix_of_same_multiplicationMatrices e e₀ he.1 he.2 he₀.2 h

end GlobalTheory.CuspGeo
