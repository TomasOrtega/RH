import Mathlib
open scoped BigOperators

open TensorProduct in
/- English proof (translation)
Take `⟨u, rfl⟩` from `(dualTensorHomEquiv ℂ S S).surjective t`. Proceed by induction on `u using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, add_mul, hx, hy]`. Consider the case `tmul f x`.

Establish `hab : (dualTensorHom ℂ S S (f ⊗ₜ x)) = (dualTensorHom ℂ S S (ξ ⊗ₜ x)) * (dualTensorHom ℂ S S (f ⊗ₜ e))`. Use extensionality with `y`. Simplify using `[dualTensorHom_apply, h]`. Establish `hba : (dualTensorHom ℂ S S (f ⊗ₜ e)) * (dualTensorHom ℂ S S (ξ ⊗ₜ x)) = f x • dualTensorHom ℂ S S (ξ ⊗ₜ e)`. Use extensionality with `y`.

Simplify using `[dualTensorHom_apply, smul_smul, mul_comm]`. Establish `hE : dualTensorHomEquiv ℂ S S (f ⊗ₜ x) = dualTensorHom ℂ S S (f ⊗ₜ x)` using `rfl`. Rewrite using `[hE, LinearMap.trace_eq_contract_apply, contractLeft_apply, hab, hτ, hba, map_smul, smul_eq_mul]`.
-/
private lemma traceForm {S : Type} [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S]
    (τ : Module.End ℂ S →ₗ[ℂ] ℂ) (hτ : ∀ a b, τ (a * b) = τ (b * a))
    (ξ : Module.Dual ℂ S) (e : S) (h : ξ e = 1) (t : Module.End ℂ S) :
    τ t = LinearMap.trace ℂ S t * τ (dualTensorHom ℂ S S (ξ ⊗ₜ e)) := by
  obtain ⟨u, rfl⟩ := (dualTensorHomEquiv ℂ S S).surjective t
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, add_mul, hx, hy]
  | tmul f x =>
    have hab : (dualTensorHom ℂ S S (f ⊗ₜ x)) =
        (dualTensorHom ℂ S S (ξ ⊗ₜ x)) * (dualTensorHom ℂ S S (f ⊗ₜ e)) := by
      ext y
      simp [dualTensorHom_apply, h]
    have hba : (dualTensorHom ℂ S S (f ⊗ₜ e)) * (dualTensorHom ℂ S S (ξ ⊗ₜ x)) =
        f x • dualTensorHom ℂ S S (ξ ⊗ₜ e) := by
      ext y
      simp [dualTensorHom_apply, smul_smul, mul_comm]
    have hE : dualTensorHomEquiv ℂ S S (f ⊗ₜ x) = dualTensorHom ℂ S S (f ⊗ₜ x) := rfl
    rw [hE, LinearMap.trace_eq_contract_apply, contractLeft_apply, hab, hτ, hba, map_smul,
      smul_eq_mul]

/- English proof (translation)
Take `⟨e, he⟩` from `exists_ne (0 : S)`. Establish `: ∃ f : Module.Dual ℂ S, f e ≠ 0`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `he ((Module.forall_dual_apply_eq_zero_iff ℂ e).1 hc)`.

Take `⟨f, hf⟩` from `this`. Conclude with `⟨(f e)⁻¹ • f, e, by simp [hf]⟩`.
-/
private lemma existsDual (S : Type) [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S]
    [Nontrivial S] : ∃ (ξ : Module.Dual ℂ S) (e : S), ξ e = 1 := by
  obtain ⟨e, he⟩ := exists_ne (0 : S)
  have : ∃ f : Module.Dual ℂ S, f e ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact he ((Module.forall_dual_apply_eq_zero_iff ℂ e).1 hc)
  obtain ⟨f, hf⟩ := this
  exact ⟨(f e)⁻¹ • f, e, by simp [hf]⟩

open TensorProduct in
/- English proof (translation)
Introduce `r`. Proceed by induction on `r with`. Consider the case `zero`. Introduce `S _ _ _ _ c hc B hB hcomm`. Use `⟨Module.finrank ℂ (LinearMap.range B), fun t => ?_⟩` and prove the remaining obligations.

Use `(LinearMap.IsIdempotentElem.isProj_range B hB).trace` as an intermediate fact. Simplify using `using this`. Consider the case `succ r ih`. Introduce `S _ _ _ _ c hc B hB hcomm`. Take `⟨ξ, e, h1⟩` from `existsDual (S 0)`.

Use `set E : Module.End ℂ (S 0) := dualTensorHom ℂ (S 0) (S 0) (ξ ⊗ₜ e) with hEdef`. Establish `hE : IsIdempotentElem E` using `by show E * E = E`. Use extensionality with `y`. Simplify using `[hEdef, dualTensorHom_apply, h1]`. Establish `hB' : IsIdempotentElem (B * c 0 E)` using `IsIdempotentElem.mul_of_commute (hcomm 0 E) hB (hE.map (c 0))`.

Establish `hcomm' : ∀ (i : Fin r) (s : Module.End ℂ (S i.succ)), Commute (B * c 0 E) (c i.succ s)` using `fun i s => (hcomm i.succ s).mul_left (hc 0 i.succ (Fin.succ_ne_zero i).symm E s)`. Take `⟨N, hN⟩` from `ih (fun i => S i.succ) (fun i => c i.succ) (fun i j hij s t => hc i.succ j.succ (fun h => hij (Fin.succ_injective _ h)) s t) (B * c 0 E) hB' hcomm'`. Use `⟨N, fun t => ?_⟩` and prove the remaining obligations. Rewrite using `[List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]`. Use `set A : Module.End ℂ X := (List.ofFn fun i : Fin r => c i.succ (t i.succ)).prod with hA`.

Establish `hAc : ∀ s, Commute (c 0 s) A` using `fun s => by`. Use `Commute.list_prod_right _ _ ?_` and prove the remaining obligations. Introduce `x hx`. Take `⟨i, rfl⟩` from `(List.mem_ofFn' _ _).1 hx`. Conclude with `hc 0 i.succ (Fin.succ_ne_zero i).symm s _`.

Set `τ : Module.End ℂ (S 0) →ₗ[ℂ] ℂ` to `(LinearMap.trace ℂ X) ∘ₗ (LinearMap.mulRight ℂ A) ∘ₗ (LinearMap.mulLeft ℂ B) ∘ₗ (c 0).toLinearMap`. Establish `hτv : ∀ s, τ s = LinearMap.trace ℂ X (B * c 0 s * A)` using `fun s => rfl`. Establish `hτ : ∀ a b, τ (a * b) = τ (b * a)`. Introduce `a b`. Rewrite using `[hτv, hτv, map_mul (c 0), map_mul (c 0)]`.

Establish `e1 : B * (c 0 a * c 0 b) * A = c 0 a * (B * c 0 b * A)`. Rewrite using `[← mul_assoc B, (hcomm 0 a).eq]`. Simplify using `only [mul_assoc]`. Establish `e2 : (B * c 0 b * A) * c 0 a = B * (c 0 b * c 0 a) * A`. Rewrite using `[mul_assoc (B * c 0 b) A, ← (hAc a).eq]`.

Simplify using `only [mul_assoc]`. Rewrite using `[e1, LinearMap.trace_mul_comm, e2]`. Establish `key` using `traceForm τ hτ ξ e h1 (t 0)`. Establish `hN'` using `hN (fun i => t i.succ)`. Rewrite using `[← mul_assoc, ← hτv, key, hτv, ← hEdef, hN']`.

Expand and normalize the polynomial expressions, which then agree.
-/
private lemma commuting_idempotent_trace {X : Type} [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X] :
    ∀ (r : ℕ) (S : Fin r → Type) [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)]
      [∀ i, FiniteDimensional ℂ (S i)] [∀ i, Nontrivial (S i)]
      (c : ∀ i, Module.End ℂ (S i) →ₐ[ℂ] Module.End ℂ X),
      (∀ i j, i ≠ j → ∀ s t, Commute (c i s) (c j t)) →
      ∀ B : Module.End ℂ X, IsIdempotentElem B → (∀ i s, Commute B (c i s)) →
      ∃ N : ℕ, ∀ t : ∀ i, Module.End ℂ (S i),
        LinearMap.trace ℂ X (B * (List.ofFn fun i => c i (t i)).prod)
          = N * ∏ i, LinearMap.trace ℂ (S i) (t i) := by
  intro r
  induction r with
  | zero =>
    intro S _ _ _ _ c hc B hB hcomm
    refine ⟨Module.finrank ℂ (LinearMap.range B), fun t => ?_⟩
    have := (LinearMap.IsIdempotentElem.isProj_range B hB).trace
    simpa using this
  | succ r ih =>
    intro S _ _ _ _ c hc B hB hcomm
    obtain ⟨ξ, e, h1⟩ := existsDual (S 0)
    set E : Module.End ℂ (S 0) := dualTensorHom ℂ (S 0) (S 0) (ξ ⊗ₜ e) with hEdef
    have hE : IsIdempotentElem E := by
      show E * E = E
      ext y
      simp [hEdef, dualTensorHom_apply, h1]
    have hB' : IsIdempotentElem (B * c 0 E) :=
      IsIdempotentElem.mul_of_commute (hcomm 0 E) hB (hE.map (c 0))
    have hcomm' : ∀ (i : Fin r) (s : Module.End ℂ (S i.succ)),
        Commute (B * c 0 E) (c i.succ s) := fun i s =>
      (hcomm i.succ s).mul_left (hc 0 i.succ (Fin.succ_ne_zero i).symm E s)
    obtain ⟨N, hN⟩ := ih (fun i => S i.succ) (fun i => c i.succ)
      (fun i j hij s t => hc i.succ j.succ (fun h => hij (Fin.succ_injective _ h)) s t)
      (B * c 0 E) hB' hcomm'
    refine ⟨N, fun t => ?_⟩
    rw [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
    set A : Module.End ℂ X := (List.ofFn fun i : Fin r => c i.succ (t i.succ)).prod with hA
    have hAc : ∀ s, Commute (c 0 s) A := fun s => by
      refine Commute.list_prod_right _ _ ?_
      intro x hx
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
      exact hc 0 i.succ (Fin.succ_ne_zero i).symm s _
    let τ : Module.End ℂ (S 0) →ₗ[ℂ] ℂ :=
      (LinearMap.trace ℂ X) ∘ₗ (LinearMap.mulRight ℂ A) ∘ₗ (LinearMap.mulLeft ℂ B) ∘ₗ
        (c 0).toLinearMap
    have hτv : ∀ s, τ s = LinearMap.trace ℂ X (B * c 0 s * A) := fun s => rfl
    have hτ : ∀ a b, τ (a * b) = τ (b * a) := by
      intro a b
      rw [hτv, hτv, map_mul (c 0), map_mul (c 0)]
      have e1 : B * (c 0 a * c 0 b) * A = c 0 a * (B * c 0 b * A) := by
        rw [← mul_assoc B, (hcomm 0 a).eq]
        simp only [mul_assoc]
      have e2 : (B * c 0 b * A) * c 0 a = B * (c 0 b * c 0 a) * A := by
        rw [mul_assoc (B * c 0 b) A, ← (hAc a).eq]
        simp only [mul_assoc]
      rw [e1, LinearMap.trace_mul_comm, e2]
    have key := traceForm τ hτ ξ e h1 (t 0)
    have hN' := hN (fun i => t i.succ)
    rw [← mul_assoc, ← hτv, key, hτv, ← hEdef, hN']
    ring

/- English proof (translation)
Introduce `r X _ _ _ S _ _ _ _ c hc`. Take `⟨N, hN⟩` from `commuting_idempotent_trace r S c hc 1 IsIdempotentElem.one (fun _ _ => Commute.one_left _)`. Conclude with `⟨N, fun t => by simpa using hN t⟩`.
-/
theorem UpperTheory.trace_pairing_separates_endomorphisms :
    ∀ (r : ℕ) (X : Type) [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X] (S : Fin r → Type) [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)] [∀ i, FiniteDimensional ℂ (S i)] [∀ i, Nontrivial (S i)] (c : ∀ i, Module.End ℂ (S i) →ₐ[ℂ] Module.End ℂ X), (∀ i j, i ≠ j → ∀ s t, Commute (c i s) (c j t)) → ∃ N : ℕ, ∀ t : ∀ i, Module.End ℂ (S i), LinearMap.trace ℂ X (List.ofFn fun i => c i (t i)).prod = N * ∏ i, LinearMap.trace ℂ (S i) (t i) := by
  intro r X _ _ _ S _ _ _ _ c hc
  obtain ⟨N, hN⟩ := commuting_idempotent_trace r S c hc 1 IsIdempotentElem.one (fun _ _ => Commute.one_left _)
  exact ⟨N, fun t => by simpa using hN t⟩
