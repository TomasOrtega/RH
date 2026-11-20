import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SimultaneousEigenvectors.SimEig

noncomputable section

open scoped TensorProduct

namespace UpperTheory.V.Cj.S

section SlopeTestRemainingChoices

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/- English proof (translation)
Proceed by induction on `u using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y => simp [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]`. Consider the case `add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]`.
-/
private theorem coordB_natural {β : Type} [DecidableEq β] (b : Module.Basis β ℂ W) (f : Module.End ℂ V)
    (u : V ⊗[ℂ] W) (j : β) :
    TensorProduct.equivFinsuppOfBasisRight b (TensorProduct.map f 1 u) j =
      f (TensorProduct.equivFinsuppOfBasisRight b u j) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

/- English proof (translation)
Set `b` to `Module.Basis.ofVectorSpace ℂ W`. Establish `hne : TensorProduct.equivFinsuppOfBasisRight (M` using `V) b u ≠ 0 := by`. Rewrite using `[Ne, LinearEquiv.map_eq_zero_iff]` and apply the resulting hypothesis. Take `⟨j, hj⟩` from `Finsupp.ne_iff.1 hne`. Use `⟨_, hj, fun i => ?_⟩` and prove the remaining obligations.

Rewrite using `[← coordB_natural, h, map_smul, Finsupp.smul_apply]`.
-/
private theorem leftB {ι : Type} (A : ι → Module.End ℂ V) (l : ι → ℂ) {u : V ⊗[ℂ] W} (hu : u ≠ 0)
    (h : ∀ i, TensorProduct.map (A i) (1 : Module.End ℂ W) u = l i • u) :
    ∃ v : V, v ≠ 0 ∧ ∀ i, A i v = l i • v := by
  classical
  let b := Module.Basis.ofVectorSpace ℂ W
  have hne : TensorProduct.equivFinsuppOfBasisRight (M := V) b u ≠ 0 := by
    rwa [Ne, LinearEquiv.map_eq_zero_iff]
  obtain ⟨j, hj⟩ := Finsupp.ne_iff.1 hne
  refine ⟨_, hj, fun i => ?_⟩
  rw [← coordB_natural, h, map_smul, Finsupp.smul_apply]

/- English proof (translation)
Use `leftB (W := V) B m (u := TensorProduct.comm ℂ V W u) (by rwa [Ne, LinearEquiv.map_eq_zero_iff]) fun k => ?_` and prove the remaining obligations. Rewrite using `[← map_smul, ← h]`. Conclude with `TensorProduct.map_comm _ _ u`.
-/
private theorem rightB {κ : Type} (B : κ → Module.End ℂ W) (m : κ → ℂ) {u : V ⊗[ℂ] W} (hu : u ≠ 0)
    (h : ∀ k, TensorProduct.map (1 : Module.End ℂ V) (B k) u = m k • u) :
    ∃ w : W, w ≠ 0 ∧ ∀ k, B k w = m k • w := by
  refine leftB (W := V) B m (u := TensorProduct.comm ℂ V W u) (by rwa [Ne, LinearEquiv.map_eq_zero_iff]) fun k => ?_
  rw [← map_smul, ← h]
  exact TensorProduct.map_comm _ _ u

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `V W _ _ _ _ _ _ ι κ A B hA hB z hz`. Set `A' : Option ι → Module.End ℂ V` to `fun o => o.elim 1 A`. Set `B' : Option κ → Module.End ℂ W` to `fun o => o.elim 1 B`. Establish `hA' : ∀ o o', A' o * A' o' = A' o' * A' o`. Apply the tactic sequence `rintro (_ | i) (_ | i') <;> simp [A']`.

Conclude with `hA i i'`. Establish `hB' : ∀ o o', B' o * B' o' = B' o' * B' o`. Apply the tactic sequence `rintro (_ | i) (_ | i') <;> simp [B']`. Conclude with `hB i i'`. Set `T : Option ι × Option κ → Module.End ℂ (V ⊗[ℂ] W)` to `fun p => TensorProduct.map (A' p.1) (B' p.2)`.

Establish `hT : ∀ p q, T p * T q = T q * T p`. Introduce `p q`. Simplify using `only [T, ← TensorProduct.map_mul]`. Rewrite using `[hA', hB']`. Set `U : Submodule ℂ (V ⊗[ℂ] W)` to `⨅ P : {P : Module.End ℂ (V ⊗[ℂ] W) // (∀ p, P * T p = T p * P) ∧ P z = 0}, LinearMap.ker P.1`.

Establish `hU : ∀ x, x ∈ U ↔ ∀ P : Module.End ℂ (V ⊗[ℂ] W), (∀ p, P * T p = T p * P) → P z = 0 → P x = 0`. Introduce `x`. Simplify using `[U, Submodule.mem_iInf]`. Establish `hzU : z ∈ U` using `(hU z).2 fun _ _ h => h`. Take `⟨u, huU, hu, hc⟩` from `UpperTheory.V.LinAlg.simEig T hT _ U rfl (fun h => hz (by simpa [h] using hzU)) (fun p x hx => (hU _).2 fun P hP hPz => by`.

Rewrite using `[← Module.End.mul_apply, hP, Module.End.mul_apply, (hU x).1 hx P hP hPz, map_zero])`. Use `choose χ hχ using hc`. Take `⟨v, hv, hv'⟩` from `leftB A (fun i => χ (some i, none)) hu fun i => hχ (some i, none)`. Take `⟨w, hw, hw'⟩` from `rightB B (fun k => χ (none, some k)) hu fun k => hχ (none, some k)`. Use `⟨v, w, _, _, hv, hw, hv', hw', fun σ _ c i k e he => ?_⟩` and prove the remaining obligations.

Establish `hprod : ∀ p, T (some (i p), some (k p)) u = (χ (some (i p), none) * χ (none, some (k p))) • u`. Introduce `p`. Establish `h1 : T (some (i p), some (k p)) = T (some (i p), none) * T (none, some (k p))`. Simplify using `[T, A', B', ← TensorProduct.map_mul]`. Rewrite using `[h1, Module.End.mul_apply, hχ, map_smul, hχ, smul_smul, mul_comm]`.

Establish `key` using `(hU u).1 huU (∑ p, c p • T (some (i p), some (k p)) - e • 1) (fun q => by`. Simplify using `only [sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hT q])`. Use the proof step `(by`. Rewrite using `[LinearMap.sub_apply, LinearMap.sum_apply, sub_eq_zero]`. Conclude with `he)`.

Rewrite `key` using `[LinearMap.sub_apply, LinearMap.sum_apply, sub_eq_zero]`. Simplify using `only [LinearMap.smul_apply, hprod, smul_smul, ← Finset.sum_smul, Module.End.one_apply, ← mul_assoc] at key`. Conclude with `smul_left_injective ℂ hu key`.
-/
theorem tensEigB : TensEig := by
  intro V W _ _ _ _ _ _ ι κ A B hA hB z hz

  let A' : Option ι → Module.End ℂ V := fun o => o.elim 1 A
  let B' : Option κ → Module.End ℂ W := fun o => o.elim 1 B
  have hA' : ∀ o o', A' o * A' o' = A' o' * A' o := by
    rintro (_ | i) (_ | i') <;> simp [A']
    exact hA i i'
  have hB' : ∀ o o', B' o * B' o' = B' o' * B' o := by
    rintro (_ | i) (_ | i') <;> simp [B']
    exact hB i i'
  let T : Option ι × Option κ → Module.End ℂ (V ⊗[ℂ] W) := fun p => TensorProduct.map (A' p.1) (B' p.2)
  have hT : ∀ p q, T p * T q = T q * T p := by
    intro p q
    simp only [T, ← TensorProduct.map_mul]
    rw [hA', hB']

  let U : Submodule ℂ (V ⊗[ℂ] W) :=
    ⨅ P : {P : Module.End ℂ (V ⊗[ℂ] W) // (∀ p, P * T p = T p * P) ∧ P z = 0}, LinearMap.ker P.1
  have hU : ∀ x, x ∈ U ↔ ∀ P : Module.End ℂ (V ⊗[ℂ] W), (∀ p, P * T p = T p * P) → P z = 0 → P x = 0 := by
    intro x
    simp [U, Submodule.mem_iInf]
  have hzU : z ∈ U := (hU z).2 fun _ _ h => h
  obtain ⟨u, huU, hu, hc⟩ := UpperTheory.V.LinAlg.simEig T hT _ U rfl
    (fun h => hz (by simpa [h] using hzU)) (fun p x hx => (hU _).2 fun P hP hPz => by
      rw [← Module.End.mul_apply, hP, Module.End.mul_apply, (hU x).1 hx P hP hPz, map_zero])
  choose χ hχ using hc
  obtain ⟨v, hv, hv'⟩ := leftB A (fun i => χ (some i, none)) hu fun i => hχ (some i, none)
  obtain ⟨w, hw, hw'⟩ := rightB B (fun k => χ (none, some k)) hu fun k => hχ (none, some k)
  refine ⟨v, w, _, _, hv, hw, hv', hw', fun σ _ c i k e he => ?_⟩
  have hprod : ∀ p, T (some (i p), some (k p)) u = (χ (some (i p), none) * χ (none, some (k p))) • u := by
    intro p
    have h1 : T (some (i p), some (k p)) = T (some (i p), none) * T (none, some (k p)) := by
      simp [T, A', B', ← TensorProduct.map_mul]
    rw [h1, Module.End.mul_apply, hχ, map_smul, hχ, smul_smul, mul_comm]
  have key := (hU u).1 huU (∑ p, c p • T (some (i p), some (k p)) - e • 1)
    (fun q => by
      simp only [sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
        hT q])
    (by
      rw [LinearMap.sub_apply, LinearMap.sum_apply, sub_eq_zero]
      exact he)
  rw [LinearMap.sub_apply, LinearMap.sum_apply, sub_eq_zero] at key
  simp only [LinearMap.smul_apply, hprod, smul_smul, ← Finset.sum_smul, Module.End.one_apply, ← mul_assoc] at key
  exact smul_left_injective ℂ hu key

end UpperTheory.V.Cj.S
