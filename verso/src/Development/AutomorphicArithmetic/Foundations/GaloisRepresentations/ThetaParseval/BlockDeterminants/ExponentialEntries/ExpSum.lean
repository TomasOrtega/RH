import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ExponentialEntries.RightSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyFinitePiTensorSumOfFactorOperators

open scoped TensorProduct Matrix
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.RealLift UpperTheory.TP.RP

namespace UpperTheory.TP.RP

section FiniteDim

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Rewrite using `[← sub_eq_zero]`. Conclude with `(Module.forall_dual_apply_eq_zero_iff ℂ (a - b)).1 fun f => by`. Rewrite using `[map_sub, h f, sub_self]`.
-/
private theorem sep {a b : V} (h : ∀ l : V →ₗ[ℂ] ℂ, l a = l b) : a = b := by
  rw [← sub_eq_zero]
  exact (Module.forall_dual_apply_eq_zero_iff ℂ (a - b)).1 fun f => by
    rw [map_sub, h f, sub_self]

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable [FiniteDimensional ℂ V]

private noncomputable def em :
    Module.End ℂ V ≃ₐ[ℂ] Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ :=
  algEquivMatrix (Module.finBasis ℂ V)

private noncomputable def Ex (A : Module.End ℂ V) : Module.End ℂ V :=
  em.symm (NormedSpace.exp (em A))

/- English proof (translation)
Introduce `v l`. Use `haveI : CompleteSpace (Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ) := FiniteDimensional.complete ℂ _`. Establish `hs` using `NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (em A)`. Set `φ : Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ →ₗ[ℂ] ℂ` to `(l ∘ₗ (LinearMap.applyₗ v)) ∘ₗ (em (V := V)).symm.toLinearMap`. Establish `hc : Continuous φ` using `LinearMap.continuous_of_finiteDimensional φ`.

Use `hs.map φ.toAddMonoidHom hc` as an intermediate fact. Use `this using 2 with n` and compare the differences between its conclusion and the goal. Simplify using `[φ, map_pow]`. Both sides reduce to the same expression.
-/
private theorem isExp_Ex (A : Module.End ℂ V) : IsExp A (Ex A) := by
  intro v l
  haveI : CompleteSpace (Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ) :=
    FiniteDimensional.complete ℂ _
  have hs := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (em A)
  let φ : Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ →ₗ[ℂ] ℂ :=
    (l ∘ₗ (LinearMap.applyₗ v)) ∘ₗ (em (V := V)).symm.toLinearMap
  have hc : Continuous φ := LinearMap.continuous_of_finiteDimensional φ
  have := hs.map φ.toAddMonoidHom hc
  convert this using 2 with n
  · simp [φ, map_pow]
  · rfl

/- English proof (translation)
Use `haveI : CompleteSpace (Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ) := FiniteDimensional.complete ℂ _`. Establish `hc : Commute (em A) (em B)` using `h.map em`. Simplify using `only [Ex, map_add]`. Conclude with `(congrArg em.symm (NormedSpace.exp_add_of_commute hc)).trans (map_mul _ _ _)`.
-/
private theorem Ex_add {A B : Module.End ℂ V} (h : Commute A B) : Ex (A + B) = Ex A * Ex B := by
  haveI : CompleteSpace (Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ) :=
    FiniteDimensional.complete ℂ _
  have hc : Commute (em A) (em B) := h.map em
  simp only [Ex, map_add]
  exact (congrArg em.symm (NormedSpace.exp_add_of_commute hc)).trans (map_mul _ _ _)

end FiniteDim

section Stable

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Proceed by induction on `n generalizing x with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]`.
-/
private theorem pow_compat {N : Submodule ℂ V} {C : Module.End ℂ V} {C' : Module.End ℂ N}
    (h : ∀ x : N, ((C' x : N) : V) = C x) (n : ℕ) (x : N) :
    (((C' ^ n) x : N) : V) = (C ^ n) (x : V) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]

/- English proof (translation)
Use `hE x (l ∘ₗ N.subtype)` as an intermediate fact. Simplify `this` using `[pow_compat h]`.
-/
private theorem hasSum_compat {N : Submodule ℂ V} {C : Module.End ℂ V} {C' : Module.End ℂ N}
    (h : ∀ x : N, ((C' x : N) : V) = C x) {E : Module.End ℂ N} (hE : IsExp C' E) (x : N)
    (l : V →ₗ[ℂ] ℂ) :
    HasSum (fun n : ℕ => ((n.factorial : ℂ))⁻¹ * l ((C ^ n) (x : V))) (l (E x : V)) := by
  have := hE x (l ∘ₗ N.subtype)
  simpa [pow_compat h] using this

/- English proof (translation)
The claim follows from `sep fun l => (hU x l).unique (hasSum_compat h hE x l)`.
-/
private theorem eq_compat {N : Submodule ℂ V} {C : Module.End ℂ V} {C' : Module.End ℂ N}
    (h : ∀ x : N, ((C' x : N) : V) = C x) {U : Module.End ℂ V} {E : Module.End ℂ N}
    (hU : IsExp C U) (hE : IsExp C' E) (x : N) : U (x : V) = (E x : V) :=
  sep fun l => (hU x l).unique (hasSum_compat h hE x l)

/- English proof (translation)
Introduce `v l`. Take `⟨N, hf, hv, hA, hB⟩` from `hN v`. Set `A' : Module.End ℂ N` to `A.restrict hA`. Set `B' : Module.End ℂ N` to `B.restrict hB`. Establish `cA : ∀ x : N, ((A' x : N) : V) = A x` using `fun x => rfl`.

Establish `cB : ∀ x : N, ((B' x : N) : V) = B x` using `fun x => rfl`. Establish `cS : ∀ x : N, (((A' + B') x : N) : V) = (A + B) x` using `fun x => rfl`. Establish `hc' : Commute A' B'`. Use `LinearMap.ext fun x => Subtype.ext ?_` and prove the remaining obligations. Conclude with `LinearMap.congr_fun hc.eq (x : V)`.

Establish `e1 : W v = (Ex B' ⟨v, hv⟩ : V)` using `eq_compat cB hW (isExp_Ex B') ⟨v, hv⟩`. Establish `e : (U * W) v = (Ex (A' + B') ⟨v, hv⟩ : V)`. Rewrite using `[Ex_add hc', Module.End.mul_apply, Module.End.mul_apply, e1]`. Conclude with `eq_compat cA hU (isExp_Ex A') _`. Rewrite using `[e]`.

Conclude with `hasSum_compat cS (isExp_Ex _) ⟨v, hv⟩ l`.
-/
private theorem isExp_add {A B U W : Module.End ℂ V} (hU : IsExp A U) (hW : IsExp B W)
    (hc : Commute A B)
    (hN : ∀ v, ∃ N : Submodule ℂ V, FiniteDimensional ℂ N ∧ v ∈ N ∧ (∀ y ∈ N, A y ∈ N) ∧
      ∀ y ∈ N, B y ∈ N) :
    IsExp (A + B) (U * W) := by
  intro v l
  obtain ⟨N, hf, hv, hA, hB⟩ := hN v
  let A' : Module.End ℂ N := A.restrict hA
  let B' : Module.End ℂ N := B.restrict hB
  have cA : ∀ x : N, ((A' x : N) : V) = A x := fun x => rfl
  have cB : ∀ x : N, ((B' x : N) : V) = B x := fun x => rfl
  have cS : ∀ x : N, (((A' + B') x : N) : V) = (A + B) x := fun x => rfl
  have hc' : Commute A' B' := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    exact LinearMap.congr_fun hc.eq (x : V)
  have e1 : W v = (Ex B' ⟨v, hv⟩ : V) := eq_compat cB hW (isExp_Ex B') ⟨v, hv⟩
  have e : (U * W) v = (Ex (A' + B') ⟨v, hv⟩ : V) := by
    rw [Ex_add hc', Module.End.mul_apply, Module.End.mul_apply, e1]
    exact eq_compat cA hU (isExp_Ex A') _
  rw [e]
  exact hasSum_compat cS (isExp_Ex _) ⟨v, hv⟩ l

end Stable

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)]
  [∀ i, Module ℂ (V i)]

/- English proof (translation)
Rewrite using `[atPl, PiTensorProduct.map_tprod]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Distinguish the cases in `h : i = w`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Function.update_of_ne h]`.
-/
private theorem atPl_tprod (w : ι) (L : Module.End ℂ (V w)) (f : ∀ i, V i) :
    atPl w L (PiTensorProduct.tprod ℂ f) =
      PiTensorProduct.tprod ℂ (Function.update f w (L (f w))) := by
  rw [atPl, PiTensorProduct.map_tprod]
  congr 1
  funext i
  by_cases h : i = w
  · subst h
    simp
  · simp [Function.update_of_ne h]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[pow_succ', Module.End.mul_apply, ih, atPl_tprod]`. Simplify using `[pow_succ']`.
-/
private theorem atPl_pow_tprod (w : ι) (L : Module.End ℂ (V w)) (f : ∀ i, V i) (n : ℕ) :
    (atPl w L ^ n) (PiTensorProduct.tprod ℂ f) =
      PiTensorProduct.tprod ℂ (Function.update f w ((L ^ n) (f w))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, atPl_tprod]
    simp [pow_succ']

/- English proof (translation)
Introduce `t l`. Proceed by induction on `t using PiTensorProduct.induction_on with`. Consider the case `smul_tprod r f`. Establish `h2` using `(h (f w) (l ∘ₗ (PiTensorProduct.tprod ℂ (s := V)).toLinearMap f w)).mul_left r`. Simplify using `only [map_smul, atPl_tprod, smul_eq_mul]`.

Establish `e' : ∀ y, (l ∘ₗ (PiTensorProduct.tprod ℂ (s` using `V)).toLinearMap f w) y = l (PiTensorProduct.tprod ℂ (Function.update f w y)) := fun _ => rfl`. Establish `e : ∀ n : ℕ, ((n.factorial : ℂ))⁻¹ * (r * l ((atPl w L ^ n) (PiTensorProduct.tprod ℂ f))) = r * (((n.factorial : ℂ))⁻¹ * (l ∘ₗ (PiTensorProduct.tprod ℂ (s` using `V)).toLinearMap f w) ((L ^ n) (f w))) := fun n => by`. Rewrite using `[atPl_pow_tprod, e']`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [e]`.

Conclude with `h2`. Consider the case `add a b ha hb`. Simplify `ha.add hb` using `[mul_add]`.
-/
private theorem isExp_atPl {w : ι} {L U : Module.End ℂ (V w)} (h : IsExp L U) :
    IsExp (atPl w L) (atPl w U) := by
  intro t l
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    have h2 := (h (f w) (l ∘ₗ (PiTensorProduct.tprod ℂ (s := V)).toLinearMap f w)).mul_left r
    simp only [map_smul, atPl_tprod, smul_eq_mul]
    have e' : ∀ y, (l ∘ₗ (PiTensorProduct.tprod ℂ (s := V)).toLinearMap f w) y =
        l (PiTensorProduct.tprod ℂ (Function.update f w y)) := fun _ => rfl
    have e : ∀ n : ℕ, ((n.factorial : ℂ))⁻¹ * (r * l ((atPl w L ^ n) (PiTensorProduct.tprod ℂ f))) =
        r * (((n.factorial : ℂ))⁻¹ *
          (l ∘ₗ (PiTensorProduct.tprod ℂ (s := V)).toLinearMap f w) ((L ^ n) (f w))) := fun n => by
      rw [atPl_pow_tprod, e']
      ring
    simp only [e]
    exact h2
  | add a b ha hb =>
    simpa [mul_add] using ha.add hb

/- English proof (translation)
Use `PiTensorProduct.ext (MultilinearMap.ext fun f => ?_)` and prove the remaining obligations. Simplify using `only [LinearMap.compMultilinearMap_apply, Module.End.mul_apply, atPl_tprod, Function.update_of_ne h, Function.update_of_ne h.symm]`. Rewrite using `[Function.update_comm h]`.
-/
private theorem atPl_comm {a b : ι} (h : a ≠ b) (X : Module.End ℂ (V a)) (Y : Module.End ℂ (V b)) :
    Commute (atPl a X) (atPl b Y) := by
  refine PiTensorProduct.ext (MultilinearMap.ext fun f => ?_)
  simp only [LinearMap.compMultilinearMap_apply, Module.End.mul_apply, atPl_tprod,
    Function.update_of_ne h, Function.update_of_ne h.symm]
  rw [Function.update_comm h]

/- English proof (translation)
Proceed by induction on `t using PiTensorProduct.induction_on with`. Consider the case `smul_tprod r f => choose N hNf hfN hN using fun i => hL i (f i)`. Use `⟨LinearMap.range (PiTensorProduct.map fun i => (N i).subtype), inferInstance, ?_, ?_⟩` and prove the remaining obligations. Conclude with `⟨r • PiTensorProduct.tprod ℂ (fun i => (⟨f i, hfN i⟩ : N i)), by simp [PiTensorProduct.map_tprod]⟩`. Conclude with `fun w y hy => atPl_mem_range_map L N hN w y hy`.

Consider the case `add a b ha hb`. Take `⟨N₁, h₁, ha₁, hs₁⟩` from `ha`. Take `⟨N₂, h₂, hb₂, hs₂⟩` from `hb`. Use `⟨N₁ ⊔ N₂, inferInstance, Submodule.add_mem_sup ha₁ hb₂, fun w y hy => ?_⟩` and prove the remaining obligations. Take `⟨y₁, hy₁, y₂, hy₂, rfl⟩` from `Submodule.mem_sup.1 hy`.

Rewrite using `[map_add]`. Conclude with `Submodule.add_mem_sup (hs₁ w y₁ hy₁) (hs₂ w y₂ hy₂)`.
-/
private theorem jointStable (L : ∀ i, Module.End ℂ (V i)) (hL : ∀ i, LocFin (L i)) (t : ⨂[ℂ] i, V i) :
    ∃ N : Submodule ℂ (⨂[ℂ] i, V i), FiniteDimensional ℂ N ∧ t ∈ N ∧
      ∀ w, ∀ y ∈ N, atPl w (L w) y ∈ N := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    choose N hNf hfN hN using fun i => hL i (f i)
    refine ⟨LinearMap.range (PiTensorProduct.map fun i => (N i).subtype), inferInstance, ?_, ?_⟩
    · exact ⟨r • PiTensorProduct.tprod ℂ (fun i => (⟨f i, hfN i⟩ : N i)),
        by simp [PiTensorProduct.map_tprod]⟩
    · exact fun w y hy => atPl_mem_range_map L N hN w y hy
  | add a b ha hb =>
    obtain ⟨N₁, h₁, ha₁, hs₁⟩ := ha
    obtain ⟨N₂, h₂, hb₂, hs₂⟩ := hb
    refine ⟨N₁ ⊔ N₂, inferInstance, Submodule.add_mem_sup ha₁ hb₂, fun w y hy => ?_⟩
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hy
    rw [map_add]
    exact Submodule.add_mem_sup (hs₁ w y₁ hy₁) (hs₂ w y₂ hy₂)

/- English proof (translation)
Introduce `v l`. Use `hasSum_single (f := fun n : ℕ => ((n.factorial : ℂ))⁻¹ * l (((0 : Module.End ℂ W) ^ n) v)) 0 (fun n hn => by simp [zero_pow hn]) using 1` and compare the differences between its conclusion and the goal. Simplify using the standard rewrite rules.
-/
private theorem isExp_zero_one {W : Type} [AddCommGroup W] [Module ℂ W] :
    IsExp (0 : Module.End ℂ W) 1 := by
  intro v l
  convert hasSum_single (f := fun n : ℕ => ((n.factorial : ℂ))⁻¹ * l (((0 : Module.End ℂ W) ^ n) v))
    0 (fun n hn => by simp [zero_pow hn]) using 1
  simp

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Establish `: (PiTensorProduct.map fun i => if i ∈ (∅ : Finset ι) then U i else (LinearMap.id : V i →ₗ[ℂ] V i)) = 1`. Simplify using `only [Finset.notMem_empty, if_false]`. Conclude with `PiTensorProduct.map_id`.

Rewrite using `[this, Finset.sum_empty]`. Conclude with `isExp_zero_one`. Consider the case `insert a s ha ih`. Establish `e : (PiTensorProduct.map fun i => if i ∈ insert a s then U i else (LinearMap.id : V i →ₗ[ℂ] V i)) = atPl a (U a) * PiTensorProduct.map fun i => if i ∈ s then U i else (LinearMap.id : V i →ₗ[ℂ] V i)`. Rewrite using `[atPl, Module.End.mul_eq_comp, ← PiTensorProduct.map_comp]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Distinguish the cases in `h : i = a`. Substitute `h` using the available equality. Simplify using `[ha]`.

Simplify using `[h, Function.update_of_ne h]`. Rewrite using `[e, Finset.sum_insert ha]`. Use `isExp_add (isExp_atPl (hU a)) ih ?_ fun v => ?_` and prove the remaining obligations. Use `Commute.sum_right _ _ _ fun w hw => atPl_comm ?_ _ _` and prove the remaining obligations. Introduce and unpack `rfl`.

Conclude with `ha hw`. Take `⟨N, hf, hv, hN⟩` from `jointStable L hL v`. Use `⟨N, hf, hv, hN a, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.sum_apply]`. Conclude with `Submodule.sum_mem _ fun w _ => hN w y hy`.
-/
private theorem isExp_partial (L U : ∀ i, Module.End ℂ (V i)) (hL : ∀ i, LocFin (L i))
    (hU : ∀ i, IsExp (L i) (U i)) (s : Finset ι) :
    IsExp (∑ w ∈ s, atPl w (L w))
      (PiTensorProduct.map fun i => if i ∈ s then U i else (LinearMap.id : V i →ₗ[ℂ] V i)) := by
  induction s using Finset.induction_on with
  | empty =>
    have : (PiTensorProduct.map fun i =>
        if i ∈ (∅ : Finset ι) then U i else (LinearMap.id : V i →ₗ[ℂ] V i)) = 1 := by
      simp only [Finset.notMem_empty, if_false]
      exact PiTensorProduct.map_id
    rw [this, Finset.sum_empty]
    exact isExp_zero_one
  | insert a s ha ih =>
    have e : (PiTensorProduct.map fun i =>
          if i ∈ insert a s then U i else (LinearMap.id : V i →ₗ[ℂ] V i)) =
        atPl a (U a) * PiTensorProduct.map fun i =>
          if i ∈ s then U i else (LinearMap.id : V i →ₗ[ℂ] V i) := by
      rw [atPl, Module.End.mul_eq_comp, ← PiTensorProduct.map_comp]
      congr 1
      funext i
      by_cases h : i = a
      · subst h
        simp [ha]
      · simp [h, Function.update_of_ne h]
    rw [e, Finset.sum_insert ha]
    refine isExp_add (isExp_atPl (hU a)) ih ?_ fun v => ?_
    · refine Commute.sum_right _ _ _ fun w hw => atPl_comm ?_ _ _
      rintro rfl
      exact ha hw
    · obtain ⟨N, hf, hv, hN⟩ := jointStable L hL v
      refine ⟨N, hf, hv, hN a, fun y hy => ?_⟩
      rw [LinearMap.sum_apply]
      exact Submodule.sum_mem _ fun w _ => hN w y hy

end Tensor

end UpperTheory.TP.RP

/- English proof (translation)
Introduce `ι _ _ V _ _ L U hL hU`. Establish `h` using `UpperTheory.TP.RP.isExp_partial L U hL hU Finset.univ`. Simplify `h` using `[sumPl]`.
-/
theorem UpperTheory.TP.RP.expSum :
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
      (L U : ∀ i, Module.End ℂ (V i)), (∀ i, LocFin (L i)) → (∀ i, IsExp (L i) (U i)) → IsExp (sumPl L) (PiTensorProduct.map U) := by
  intro ι _ _ V _ _ L U hL hU
  have h := UpperTheory.TP.RP.isExp_partial L U hL hU Finset.univ
  simpa [sumPl] using h
