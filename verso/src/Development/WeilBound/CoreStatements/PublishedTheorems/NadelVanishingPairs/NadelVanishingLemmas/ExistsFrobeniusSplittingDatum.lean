import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExteriorAlgebraExtensionOfFrobeniusSemilin

open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

/- English proof (translation)
Introduce `K _ V _ _ ι _ p _ _ d f h hD`. Establish `lopAddV : ∀ (x x' : V) (y : Finset ι → ExteriorAlgebra K V), Lop f h (x + x') y = Lop f h x y + Lop f h x' y`. Introduce `x x' y`. Use function extensionality and compare the values at `t`. Simplify using `only [Lop, Pi.add_apply]`.

Apply the tactic sequence `split_ifs <;> simp only [map_add, add_mul, smul_add, add_smul, add_zero] <;> abel`. Establish `lopAddY : ∀ (x : V) (y y' : Finset ι → ExteriorAlgebra K V), Lop f h x (y + y') = Lop f h x y + Lop f h x y'`. Introduce `x y y'`. Use function extensionality and compare the values at `t`. Simplify using `only [Lop, Pi.add_apply]`.

Apply the tactic sequence `split_ifs <;> simp only [mul_add, smul_add, add_zero] <;> abel`. Establish `lopSmulV : ∀ (c : K) (x : V) (y : Finset ι → ExteriorAlgebra K V), Lop f h (c • x) y = c ^ p • Lop f h x y`. Introduce `c x y`. Use function extensionality and compare the values at `t`. Simplify using `only [Lop, Pi.smul_apply]`.

Apply the tactic sequence `split_ifs <;>`. Simplify using `only [hD.f_smul, hD.h_smul, map_smul, smul_mul_assoc, mul_smul, smul_add, smul_zero, smul_comm ((-1 : ℤ) ^ t.card) (c ^ p)]`. Establish `lopSmulY : ∀ (k : K) (x : V) (y : Finset ι → ExteriorAlgebra K V), Lop f h x (k • y) = k • Lop f h x y`. Introduce `k x y`. Use function extensionality and compare the values at `t`.

Simplify using `only [Lop, Pi.smul_apply]`. Apply the tactic sequence `split_ifs <;>`. Simplify using `only [mul_smul_comm, smul_add, smul_zero, smul_comm ((-1 : ℤ) ^ t.card) k, smul_comm _ k]`. Establish `hcons : ∀ (x : V) (l : List V), prodL f h (x :: l) = Lop f h x (prodL f h l)` using `fun _ _ => rfl`. Establish `hupd0 : ∀ {a : ℕ} (v : Fin (a + 1) → V) (z : V), (fun k : Fin a => Function.update v 0 z k.succ) = fun k => v k.succ`.

Introduce `a v z`. Use function extensionality and compare the values at `k`. Conclude with `Function.update_of_ne (Fin.succ_ne_zero k) _ _`. Establish `hupds : ∀ {a : ℕ} (v : Fin (a + 1) → V) (j : Fin a) (z : V), (fun k : Fin a => Function.update v j.succ z k.succ) = Function.update (fun k => v k.succ) j z`. Introduce `a v j z`.

Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k = j`. Substitute `hk` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Function.update_of_ne hk, Function.update_of_ne (fun e => hk (Fin.succ_injective _ e))]`.

Establish `hPadd : ∀ (a : ℕ) (v : Fin a → V) (i : Fin a) (x x' : V), prodL f h (List.ofFn (Function.update v i (x + x'))) = prodL f h (List.ofFn (Function.update v i x)) + prodL f h (List.ofFn (Function.update v i x'))`. Introduce `a`. Proceed by induction on `a with`. Consider the case `zero => intro v i`. Conclude with `i.elim0`.

Consider the case `succ a ih`. Introduce `v i x x'`. Break down `Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩` into its components or cases. Simplify using `only [List.ofFn_succ, hcons, Function.update_self, hupd0]`. Conclude with `lopAddV _ _ _`.

Simplify using `only [List.ofFn_succ, hcons, hupds, Function.update_of_ne (Fin.succ_ne_zero j).symm]`. Rewrite using `[ih, lopAddY]`. Establish `hPsmul : ∀ (a : ℕ) (v : Fin a → V) (i : Fin a) (c : K) (x : V), prodL f h (List.ofFn (Function.update v i (c • x))) = c ^ p • prodL f h (List.ofFn (Function.update v i x))`. Introduce `a`. Proceed by induction on `a with`.

Consider the case `zero => intro v i`. Conclude with `i.elim0`. Consider the case `succ a ih`. Introduce `v i c x`. Break down `Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩` into its components or cases.

Simplify using `only [List.ofFn_succ, hcons, Function.update_self, hupd0]`. Conclude with `lopSmulV _ _ _`. Simplify using `only [List.ofFn_succ, hcons, hupds, Function.update_of_ne (Fin.succ_ne_zero j).symm]`. Rewrite using `[ih, lopSmulY]`. Establish `key : ∃ Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V), (∀ (c : K) (x : ExteriorAlgebra K V), Φ (c • x) = c ^ p • Φ x) ∧ ∀ (a : ℕ) (v : Fin a → V), Φ (ExteriorAlgebra.ιMulti K a v) = alt f h a v`.

Use `letI tw : Module K (Finset ι → ExteriorAlgebra K V) := Module.compHom _ (frobenius K p)`. Set `P : ∀ a : ℕ, MultilinearMap K (fun _ : Fin a => V) (Finset ι → ExteriorAlgebra K V)` to `fun a => { toFun := fun v => prodL f h (List.ofFn v) map_update_add' := fun v i x x' => by`. Take `rfl : ‹DecidableEq (Fin a)› = instDecidableEqFin a` from `Subsingleton.elim _ _`. Conclude with `hPadd a v i x x'`. Use the proof step `map_update_smul' := fun v i c x => by`.

Take `rfl : ‹DecidableEq (Fin a)› = instDecidableEqFin a` from `Subsingleton.elim _ _`. Conclude with `hPsmul a v i c x }`. Set `A : ∀ a : ℕ, V [⋀^Fin a]→ₗ[K] (Finset ι → ExteriorAlgebra K V)` to `fun a => MultilinearMap.alternatization (P a)`. Set `Φ0` to `ExteriorAlgebra.liftAlternating (R := K) A`. Use `⟨Φ0.toAddMonoidHom, fun c x => ?_, fun a v => ?_⟩` and prove the remaining obligations.

Conclude with `Φ0.map_smul c x`. Use `show Φ0 (ExteriorAlgebra.ιMulti K a v) = _`. Rewrite using `[ExteriorAlgebra.liftAlternating_apply_ιMulti]`. Use `show (MultilinearMap.alternatization (P a)) v = alt f h a v`. Rewrite using `[MultilinearMap.alternatization_apply]`.

Unfold `alt`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `σ _`. Rewrite using `[Units.smul_def]`. Both sides reduce to the same expression.

Take `⟨Φ, h1, h2⟩` from `key`. Conclude with `⟨Φ, fun c a v => by rw [h1, h2]⟩`.
-/
theorem exists_isPhi : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) [Fact p.Prime] [CharP K p] (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V) (h : ι → ι → V →+ K), IsDatum p d f h → ∃ Φ, IsPhi p f h Φ := by
  intro K _ V _ _ ι _ p _ _ d f h hD
  have lopAddV : ∀ (x x' : V) (y : Finset ι → ExteriorAlgebra K V),
      Lop f h (x + x') y = Lop f h x y + Lop f h x' y := by
    intro x x' y
    funext t
    simp only [Lop, Pi.add_apply]
    split_ifs <;> simp only [map_add, add_mul, smul_add, add_smul, add_zero] <;> abel
  have lopAddY : ∀ (x : V) (y y' : Finset ι → ExteriorAlgebra K V),
      Lop f h x (y + y') = Lop f h x y + Lop f h x y' := by
    intro x y y'
    funext t
    simp only [Lop, Pi.add_apply]
    split_ifs <;> simp only [mul_add, smul_add, add_zero] <;> abel
  have lopSmulV : ∀ (c : K) (x : V) (y : Finset ι → ExteriorAlgebra K V),
      Lop f h (c • x) y = c ^ p • Lop f h x y := by
    intro c x y
    funext t
    simp only [Lop, Pi.smul_apply]
    split_ifs <;>
      simp only [hD.f_smul, hD.h_smul, map_smul, smul_mul_assoc, mul_smul, smul_add, smul_zero,
        smul_comm ((-1 : ℤ) ^ t.card) (c ^ p)]
  have lopSmulY : ∀ (k : K) (x : V) (y : Finset ι → ExteriorAlgebra K V),
      Lop f h x (k • y) = k • Lop f h x y := by
    intro k x y
    funext t
    simp only [Lop, Pi.smul_apply]
    split_ifs <;>
      simp only [mul_smul_comm, smul_add, smul_zero, smul_comm ((-1 : ℤ) ^ t.card) k, smul_comm _ k]
  have hcons : ∀ (x : V) (l : List V), prodL f h (x :: l) = Lop f h x (prodL f h l) := fun _ _ => rfl
  have hupd0 : ∀ {a : ℕ} (v : Fin (a + 1) → V) (z : V),
      (fun k : Fin a => Function.update v 0 z k.succ) = fun k => v k.succ := by
    intro a v z
    funext k
    exact Function.update_of_ne (Fin.succ_ne_zero k) _ _
  have hupds : ∀ {a : ℕ} (v : Fin (a + 1) → V) (j : Fin a) (z : V),
      (fun k : Fin a => Function.update v j.succ z k.succ) = Function.update (fun k => v k.succ) j z := by
    intro a v j z
    funext k
    by_cases hk : k = j
    · subst hk
      simp
    · rw [Function.update_of_ne hk, Function.update_of_ne (fun e => hk (Fin.succ_injective _ e))]
  have hPadd : ∀ (a : ℕ) (v : Fin a → V) (i : Fin a) (x x' : V),
      prodL f h (List.ofFn (Function.update v i (x + x'))) =
        prodL f h (List.ofFn (Function.update v i x)) + prodL f h (List.ofFn (Function.update v i x')) := by
    intro a
    induction a with
    | zero => intro v i; exact i.elim0
    | succ a ih =>
      intro v i x x'
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · simp only [List.ofFn_succ, hcons, Function.update_self, hupd0]
        exact lopAddV _ _ _
      · simp only [List.ofFn_succ, hcons, hupds,
          Function.update_of_ne (Fin.succ_ne_zero j).symm]
        rw [ih, lopAddY]
  have hPsmul : ∀ (a : ℕ) (v : Fin a → V) (i : Fin a) (c : K) (x : V),
      prodL f h (List.ofFn (Function.update v i (c • x))) =
        c ^ p • prodL f h (List.ofFn (Function.update v i x)) := by
    intro a
    induction a with
    | zero => intro v i; exact i.elim0
    | succ a ih =>
      intro v i c x
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · simp only [List.ofFn_succ, hcons, Function.update_self, hupd0]
        exact lopSmulV _ _ _
      · simp only [List.ofFn_succ, hcons, hupds,
          Function.update_of_ne (Fin.succ_ne_zero j).symm]
        rw [ih, lopSmulY]
  have key : ∃ Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V),
      (∀ (c : K) (x : ExteriorAlgebra K V), Φ (c • x) = c ^ p • Φ x) ∧
        ∀ (a : ℕ) (v : Fin a → V), Φ (ExteriorAlgebra.ιMulti K a v) = alt f h a v := by
    letI tw : Module K (Finset ι → ExteriorAlgebra K V) := Module.compHom _ (frobenius K p)
    let P : ∀ a : ℕ, MultilinearMap K (fun _ : Fin a => V) (Finset ι → ExteriorAlgebra K V) := fun a =>
      { toFun := fun v => prodL f h (List.ofFn v)
        map_update_add' := fun v i x x' => by
          obtain rfl : ‹DecidableEq (Fin a)› = instDecidableEqFin a := Subsingleton.elim _ _
          exact hPadd a v i x x'
        map_update_smul' := fun v i c x => by
          obtain rfl : ‹DecidableEq (Fin a)› = instDecidableEqFin a := Subsingleton.elim _ _
          exact hPsmul a v i c x }
    let A : ∀ a : ℕ, V [⋀^Fin a]→ₗ[K] (Finset ι → ExteriorAlgebra K V) := fun a =>
      MultilinearMap.alternatization (P a)
    let Φ0 := ExteriorAlgebra.liftAlternating (R := K) A
    refine ⟨Φ0.toAddMonoidHom, fun c x => ?_, fun a v => ?_⟩
    · exact Φ0.map_smul c x
    · show Φ0 (ExteriorAlgebra.ιMulti K a v) = _
      rw [ExteriorAlgebra.liftAlternating_apply_ιMulti]
      show (MultilinearMap.alternatization (P a)) v = alt f h a v
      rw [MultilinearMap.alternatization_apply]
      unfold alt
      apply Finset.sum_congr rfl
      intro σ _
      rw [Units.smul_def]
      rfl
  obtain ⟨Φ, h1, h2⟩ := key
  exact ⟨Φ, fun c a v => by rw [h1, h2]⟩

end GlobalTheory.DI
