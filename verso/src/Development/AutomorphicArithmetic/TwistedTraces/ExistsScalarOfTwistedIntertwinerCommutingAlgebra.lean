import Mathlib
import Development.AutomorphicArithmetic.TwistedTraces.ListOfFnProdEqMulUpdateOneOfPairwiseCommute
import Development.AutomorphicArithmetic.TwistedTraces.LinearFormEqMulTraceOfTwistedInvariant
open scoped BigOperators

/- English proof (translation)
Introduce `r X _ _ _ P _ _ _ c J ρ hc hJ hρ`. Establish `hE : ∀ i, ∃ E : Module.End ℂ (P i), LinearMap.trace ℂ (P i) (E * J i) = 1`. Introduce `i`. Establish `hx : ∃ x, J i x ≠ 0`. Assume the negation of the conclusion as `hne`.

Use `push_neg at hne`. Conclude with `hJ i (LinearMap.ext hne)`. Take `⟨x₀, hx₀⟩` from `hx`. Establish `hφ : ∃ φ : Module.Dual ℂ (P i), φ (J i x₀) ≠ 0`. Assume the negation of the conclusion as `hne`.

Use `push_neg at hne`. Conclude with `hx₀ ((Module.forall_dual_apply_eq_zero_iff ℂ (J i x₀)).1 hne)`. Take `⟨φ, hφ⟩` from `hφ`. Use `⟨((φ (J i x₀))⁻¹ • φ).smulRight x₀, ?_⟩` and prove the remaining obligations. Establish `e : (((φ (J i x₀))⁻¹ • φ).smulRight x₀) * J i = dualTensorHom ℂ (P i) (P i) (TensorProduct.tmul ℂ (((φ (J i x₀))⁻¹ • φ) ∘ₗ J i) x₀)`.

Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `y`. Simplify using `[Module.End.mul_apply, dualTensorHom_apply]`. Rewrite using `[e, LinearMap.trace_eq_contract_apply ℂ (P i)]`. Simplify using `[contractLeft_apply, hφ]`.

Use `choose E hE using hE`. Take `⟨F, hF⟩ : ∃ F : (∀ i, Module.End ℂ (P i)) → ℂ, ∀ b, F b = LinearMap.trace ℂ X ((List.ofFn fun i => c i (b i)).prod * ρ)` from `⟨_, fun _ => rfl⟩`. Establish `step : ∀ (b : ∀ i, Module.End ℂ (P i)) (i : Fin r) (y : Module.End ℂ (P i)), F (Function.update b i y) = F (Function.update b i (E i)) * LinearMap.trace ℂ (P i) (y * J i)`. Introduce `b i y`. Take `⟨a, ha⟩ : ∃ a : Fin r → Module.End ℂ X, a = fun j => c j (b j)` from `⟨_, rfl⟩`.

Take `⟨Q, hQ⟩ : ∃ Q : Module.End ℂ X, Q = (List.ofFn (Function.update a i 1)).prod` from `⟨_, rfl⟩`. Establish `fac : ∀ z, (List.ofFn fun j => c j (Function.update b i z j)).prod = c i z * Q`. Introduce `z`. Establish `h` using `(UpperTheory.list_ofFn_prod_eq_mul_update_one_of_pairwise_commute (Module.End ℂ X) r (fun j => c j (Function.update b i z j)) (fun p q hpq => hc p q hpq _ _) i).1`. Establish `e : Function.update (fun j => c j (Function.update b i z j)) i 1 = Function.update a i 1`.

Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Rewrite using `[Function.update_self, Function.update_self]`. Rewrite using `[Function.update_of_ne hj, Function.update_of_ne hj, Function.update_of_ne hj, ha]`.

Rewrite using `[h, e, Function.update_self, hQ]`. Establish `com : ∀ z, Commute (c i z) Q`. Introduce `z`. Rewrite using `[hQ]`. Use `(UpperTheory.list_ofFn_prod_eq_mul_update_one_of_pairwise_commute (Module.End ℂ X) r a ?_ i).2 (c i z) ?_` and prove the remaining obligations.

Introduce `p q hpq`. Rewrite using `[ha]`. Conclude with `hc p q hpq _ _`. Introduce `j hj`. Rewrite using `[ha]`.

Conclude with `hc i j (Ne.symm hj) _ _`. Take `⟨l, hl⟩ : ∃ l : Module.End ℂ (P i) →ₗ[ℂ] ℂ, ∀ z, l z = LinearMap.trace ℂ X (c i z * Q * ρ)` from `⟨(LinearMap.trace ℂ X) ∘ₗ (LinearMap.mulRight ℂ (Q * ρ)) ∘ₗ (c i).toLinearMap, by`. Introduce `z`. Simplify using `[mul_assoc]⟩`. Establish `hyp : ∀ a a' t : Module.End ℂ (P i), a' * J i = J i * a → l (t * a') = l (a * t)`.

Introduce `a a' t h`. Establish `h1` using `hρ i a a' h`. Establish `e1 : c i (t * a') * Q * ρ = (c i t * Q * ρ) * c i a`. Rewrite using `[map_mul, mul_assoc (c i t), (com a').eq, mul_assoc (c i t * Q) ρ, h1]`. Simplify using `only [mul_assoc]`.

Establish `e2 : c i (a * t) * Q * ρ = c i a * (c i t * Q * ρ)`. Rewrite using `[map_mul]`. Simplify using `only [mul_assoc]`. Rewrite using `[hl, hl, e1, e2, LinearMap.trace_mul_comm]`. Establish `key` using `UpperTheory.linearForm_eq_mul_trace_of_twisted_invariant (P i) (J i) (E i) l (hE i) hyp y`.

Rewrite using `[hF, hF, fac, fac, ← hl, ← hl]`. Conclude with `key`. Establish `ind : ∀ (S : Finset (Fin r)) (b : ∀ i, Module.End ℂ (P i)), F b = F (S.piecewise E b) * ∏ i ∈ S, LinearMap.trace ℂ (P i) (b i * J i)`. Introduce `S b`. Proceed by induction on `S using Finset.induction_on with`.

Consider the case `empty => simp`. Consider the case `insert i S hi ih`. Establish `hb : S.piecewise E b i = b i` using `Finset.piecewise_eq_of_notMem _ _ _ hi`. Establish `h1` using `step (S.piecewise E b) i (b i)`. Rewrite `h1` using `[← hb, Function.update_eq_self, hb]`.

Rewrite using `[Finset.prod_insert hi, Finset.piecewise_insert, ih, h1]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨F E, fun b => ?_⟩` and prove the remaining obligations. Establish `h` using `ind Finset.univ b`. Rewrite `h` using `[Finset.piecewise_univ]`.

Rewrite using `[← hF, h]`.
-/
theorem UpperTheory.exists_scalar_of_twisted_intertwiner_commuting_algebras :
    ∀ (r : ℕ) (X : Type) [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X] (P : Fin r → Type) [∀ i, AddCommGroup (P i)] [∀ i, Module ℂ (P i)] [∀ i, FiniteDimensional ℂ (P i)] (c : ∀ i, Module.End ℂ (P i) →ₐ[ℂ] Module.End ℂ X) (J : ∀ i, Module.End ℂ (P i)) (ρ : Module.End ℂ X), (∀ i j, i ≠ j → ∀ s t, Commute (c i s) (c j t)) → (∀ i, J i ≠ 0) → (∀ i a b, b * J i = J i * a → ρ * c i a = c i b * ρ) → ∃ κ : ℂ, ∀ b : ∀ i, Module.End ℂ (P i), LinearMap.trace ℂ X ((List.ofFn fun i => c i (b i)).prod * ρ) = κ * ∏ i, LinearMap.trace ℂ (P i) (b i * J i) := by
  intro r X _ _ _ P _ _ _ c J ρ hc hJ hρ
  have hE : ∀ i, ∃ E : Module.End ℂ (P i), LinearMap.trace ℂ (P i) (E * J i) = 1 := by
    intro i
    have hx : ∃ x, J i x ≠ 0 := by
      by_contra hne
      push_neg at hne
      exact hJ i (LinearMap.ext hne)
    obtain ⟨x₀, hx₀⟩ := hx
    have hφ : ∃ φ : Module.Dual ℂ (P i), φ (J i x₀) ≠ 0 := by
      by_contra hne
      push_neg at hne
      exact hx₀ ((Module.forall_dual_apply_eq_zero_iff ℂ (J i x₀)).1 hne)
    obtain ⟨φ, hφ⟩ := hφ
    refine ⟨((φ (J i x₀))⁻¹ • φ).smulRight x₀, ?_⟩
    have e : (((φ (J i x₀))⁻¹ • φ).smulRight x₀) * J i
        = dualTensorHom ℂ (P i) (P i)
            (TensorProduct.tmul ℂ (((φ (J i x₀))⁻¹ • φ) ∘ₗ J i) x₀) := by
      apply LinearMap.ext
      intro y
      simp [Module.End.mul_apply, dualTensorHom_apply]
    rw [e, LinearMap.trace_eq_contract_apply ℂ (P i)]
    simp [contractLeft_apply, hφ]
  choose E hE using hE
  obtain ⟨F, hF⟩ : ∃ F : (∀ i, Module.End ℂ (P i)) → ℂ, ∀ b, F b =
      LinearMap.trace ℂ X ((List.ofFn fun i => c i (b i)).prod * ρ) := ⟨_, fun _ => rfl⟩
  have step : ∀ (b : ∀ i, Module.End ℂ (P i)) (i : Fin r) (y : Module.End ℂ (P i)),
      F (Function.update b i y)
        = F (Function.update b i (E i)) * LinearMap.trace ℂ (P i) (y * J i) := by
    intro b i y
    obtain ⟨a, ha⟩ : ∃ a : Fin r → Module.End ℂ X, a = fun j => c j (b j) := ⟨_, rfl⟩
    obtain ⟨Q, hQ⟩ : ∃ Q : Module.End ℂ X, Q = (List.ofFn (Function.update a i 1)).prod :=
      ⟨_, rfl⟩
    have fac : ∀ z, (List.ofFn fun j => c j (Function.update b i z j)).prod = c i z * Q := by
      intro z
      have h := (UpperTheory.list_ofFn_prod_eq_mul_update_one_of_pairwise_commute (Module.End ℂ X) r (fun j => c j (Function.update b i z j))
        (fun p q hpq => hc p q hpq _ _) i).1
      have e : Function.update (fun j => c j (Function.update b i z j)) i 1
          = Function.update a i 1 := by
        funext j
        by_cases hj : j = i
        · subst hj
          rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne hj, Function.update_of_ne hj, Function.update_of_ne hj, ha]
      rw [h, e, Function.update_self, hQ]
    have com : ∀ z, Commute (c i z) Q := by
      intro z
      rw [hQ]
      refine (UpperTheory.list_ofFn_prod_eq_mul_update_one_of_pairwise_commute (Module.End ℂ X) r a ?_ i).2 (c i z) ?_
      · intro p q hpq
        rw [ha]
        exact hc p q hpq _ _
      · intro j hj
        rw [ha]
        exact hc i j (Ne.symm hj) _ _
    obtain ⟨l, hl⟩ : ∃ l : Module.End ℂ (P i) →ₗ[ℂ] ℂ,
        ∀ z, l z = LinearMap.trace ℂ X (c i z * Q * ρ) :=
      ⟨(LinearMap.trace ℂ X) ∘ₗ (LinearMap.mulRight ℂ (Q * ρ)) ∘ₗ (c i).toLinearMap, by
        intro z
        simp [mul_assoc]⟩
    have hyp : ∀ a a' t : Module.End ℂ (P i), a' * J i = J i * a → l (t * a') = l (a * t) := by
      intro a a' t h
      have h1 := hρ i a a' h
      have e1 : c i (t * a') * Q * ρ = (c i t * Q * ρ) * c i a := by
        rw [map_mul, mul_assoc (c i t), (com a').eq, mul_assoc (c i t * Q) ρ, h1]
        simp only [mul_assoc]
      have e2 : c i (a * t) * Q * ρ = c i a * (c i t * Q * ρ) := by
        rw [map_mul]
        simp only [mul_assoc]
      rw [hl, hl, e1, e2, LinearMap.trace_mul_comm]
    have key := UpperTheory.linearForm_eq_mul_trace_of_twisted_invariant (P i) (J i) (E i) l (hE i) hyp y
    rw [hF, hF, fac, fac, ← hl, ← hl]
    exact key
  have ind : ∀ (S : Finset (Fin r)) (b : ∀ i, Module.End ℂ (P i)),
      F b = F (S.piecewise E b) * ∏ i ∈ S, LinearMap.trace ℂ (P i) (b i * J i) := by
    intro S b
    induction S using Finset.induction_on with
    | empty => simp
    | insert i S hi ih =>
      have hb : S.piecewise E b i = b i := Finset.piecewise_eq_of_notMem _ _ _ hi
      have h1 := step (S.piecewise E b) i (b i)
      rw [← hb, Function.update_eq_self, hb] at h1
      rw [Finset.prod_insert hi, Finset.piecewise_insert, ih, h1]
      ring
  refine ⟨F E, fun b => ?_⟩
  have h := ind Finset.univ b
  rw [Finset.piecewise_univ] at h
  rw [← hF, h]
