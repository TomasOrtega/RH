import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

/- English proof (translation)
Set `v : ℕ → V` to `fun k => (G ^ k) x`. Establish `hv0 : v 0 = x` using `by simp [v]`. Establish `hv : ∀ k, v (k + 1) = G (v k)`. Introduce `k`. Simplify using `[v, pow_succ', Module.End.mul_apply]`.

Establish `hvS : ∀ k, v k ∈ S`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simpa [hv0] using hxS`. Consider the case `succ k ih => rw [hv]`.

Conclude with `hS _ ih`. Establish `hAk : ∀ k : ℕ, A (v k) = (α - k) • v k`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp [hv0, hA]`.

Consider the case `succ k ih`. Rewrite using `[hv, hAG, ih, map_smul]`. Use `push_cast`. Use `module`. Establish `hBk : ∀ k : ℕ, B (v k) = (β + k) • v k`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp [hv0, hB]`. Consider the case `succ k ih`. Rewrite using `[hv, hBG, ih, map_smul]`.

Use `push_cast`. Use `module`. Establish `hEk : ∀ k : ℕ, E (v (k + 1)) = (((k : ℂ) + 1) * (α - β - k)) • v k`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero`. Rewrite using `[hv, hEG, hv0, hE, hA, hB, map_zero]`. Use `push_cast`. Use `module`. Consider the case `succ k ih`.

Rewrite using `[hv (k + 1), hEG, ih, map_smul, ← hv, hAk, hBk]`. Use `push_cast`. Use `module`. Establish `hex : ∃ k, v k = 0`. Assume the negation of the conclusion as `hne`.

Use `push_neg at hne`. Establish `hli : LinearIndependent ℂ v`. Apply `Module.End.eigenvectors_linearIndependent' A (fun k : ℕ => α - k)` to reduce the goal to its premises. Introduce `i j hij`. Establish `: (i : ℂ) = j` using `by simpa using hij`.

Conclude with `this` after adjusting the coercions. Introduce `i`. Rewrite using `[Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]`. Conclude with `⟨hAk i, hne i⟩`. Set `w : ℕ → S` to `fun k => ⟨v k, hvS k⟩`.

Establish `hliw : LinearIndependent ℂ w`. Apply `LinearIndependent.of_comp S.subtype` to reduce the goal to its premises. Conclude with `hli`. Establish `: Finite ℕ` using `hliw.finite`. Conclude with `not_finite ℕ`.

Establish `hk : v (Nat.find hex) = 0` using `Nat.find_spec hex`. Establish `hk0 : Nat.find hex ≠ 0`. Introduce `h0`. Apply `hx` to reduce the goal to its premises. Rewrite using `[← hv0, ← h0]`.

Conclude with `hk`. Take `⟨m, hm⟩` from `Nat.exists_eq_succ_of_ne_zero hk0`. Establish `hvm : v m ≠ 0` using `Nat.find_min hex (by omega)`. Establish `hvm1 : v (m + 1) = 0`. Rewrite using `[show m + 1 = Nat.find hex by omega]`.

Conclude with `hk`. Establish `h` using `hEk m`. Rewrite `h` using `[hvm1, map_zero]`. Establish `hc : ((m : ℂ) + 1) * (α - β - m) = 0`. Assume the negation of the conclusion as `hc`.

Conclude with `hvm ((smul_eq_zero.mp h.symm).resolve_left hc)`. Establish `hm1 : (m : ℂ) + 1 ≠ 0` using `by exact_mod_cast Nat.succ_ne_zero m`. Use `⟨m, ?_⟩` and prove the remaining obligations. Use `(mul_eq_zero.mp hc).resolve_left hm1` as an intermediate fact. Take the linear combination `this`.
-/
private theorem sl2Core {V : Type} [AddCommGroup V] [Module ℂ V] (E G A B : Module.End ℂ V)
    (S : Submodule ℂ V) (hfin : FiniteDimensional ℂ S)
    (hEG : ∀ v, E (G v) = G (E v) + A v - B v)
    (hAG : ∀ v, A (G v) = G (A v) - G v)
    (hBG : ∀ v, B (G v) = G (B v) + G v)
    (hS : ∀ v ∈ S, G v ∈ S) (α β : ℂ) (x : V) (hxS : x ∈ S) (hx : x ≠ 0)
    (hA : A x = α • x) (hB : B x = β • x) (hE : E x = 0) :
    ∃ m : ℕ, α - β = (m : ℂ) := by
  classical
  let v : ℕ → V := fun k => (G ^ k) x
  have hv0 : v 0 = x := by simp [v]
  have hv : ∀ k, v (k + 1) = G (v k) := by
    intro k
    simp [v, pow_succ', Module.End.mul_apply]
  have hvS : ∀ k, v k ∈ S := by
    intro k
    induction k with
    | zero => simpa [hv0] using hxS
    | succ k ih => rw [hv]; exact hS _ ih
  have hAk : ∀ k : ℕ, A (v k) = (α - k) • v k := by
    intro k
    induction k with
    | zero => simp [hv0, hA]
    | succ k ih =>
      rw [hv, hAG, ih, map_smul]
      push_cast
      module
  have hBk : ∀ k : ℕ, B (v k) = (β + k) • v k := by
    intro k
    induction k with
    | zero => simp [hv0, hB]
    | succ k ih =>
      rw [hv, hBG, ih, map_smul]
      push_cast
      module
  have hEk : ∀ k : ℕ, E (v (k + 1)) = (((k : ℂ) + 1) * (α - β - k)) • v k := by
    intro k
    induction k with
    | zero =>
      rw [hv, hEG, hv0, hE, hA, hB, map_zero]
      push_cast
      module
    | succ k ih =>
      rw [hv (k + 1), hEG, ih, map_smul, ← hv, hAk, hBk]
      push_cast
      module
  have hex : ∃ k, v k = 0 := by
    by_contra hne
    push_neg at hne
    have hli : LinearIndependent ℂ v := by
      apply Module.End.eigenvectors_linearIndependent' A (fun k : ℕ => α - k)
      · intro i j hij
        have : (i : ℂ) = j := by simpa using hij
        exact_mod_cast this
      · intro i
        rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
        exact ⟨hAk i, hne i⟩
    let w : ℕ → S := fun k => ⟨v k, hvS k⟩
    have hliw : LinearIndependent ℂ w := by
      apply LinearIndependent.of_comp S.subtype
      exact hli
    have : Finite ℕ := hliw.finite
    exact not_finite ℕ
  have hk : v (Nat.find hex) = 0 := Nat.find_spec hex
  have hk0 : Nat.find hex ≠ 0 := by
    intro h0
    apply hx
    rw [← hv0, ← h0]
    exact hk
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hvm : v m ≠ 0 := Nat.find_min hex (by omega)
  have hvm1 : v (m + 1) = 0 := by
    rw [show m + 1 = Nat.find hex by omega]
    exact hk
  have h := hEk m
  rw [hvm1, map_zero] at h
  have hc : ((m : ℂ) + 1) * (α - β - m) = 0 := by
    by_contra hc
    exact hvm ((smul_eq_zero.mp h.symm).resolve_left hc)
  have hm1 : (m : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  refine ⟨m, ?_⟩
  have := (mul_eq_zero.mp hc).resolve_left hm1
  linear_combination this

/- English proof (translation)
Introduce `n V _ _ F hUF S hfin hStb ν x hxS hx hxw`. Establish `hk : KHighest (fun _ => true) F ν x` using `hxw`. Establish `hgl : GlRel F` using `hUF.gl`. Introduce `a b hab`. Establish `hne : a ≠ b` using `ne_of_lt hab`.

Establish `hEG : ∀ v, F a b (F b a v) = F b a (F a b v) + F a a v - F b b v`. Introduce `v`. Establish `h` using `LinearMap.congr_fun (hgl a b b a) v`. Simplify using `only [if_true, LinearMap.sub_apply, Module.End.mul_apply] at h`. Rewrite using `[← sub_eq_zero]`.

Rewrite `h` using `[← sub_eq_zero]`. Use `h using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws. Establish `hAG : ∀ v, F a a (F b a v) = F b a (F a a v) - F b a v`. Introduce `v`.

Establish `h` using `LinearMap.congr_fun (hgl a a b a) v`. Simplify using `only [if_neg hne, if_true, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply] at h`. Rewrite using `[← sub_eq_zero]`. Rewrite `h` using `[← sub_eq_zero]`. Use `h using 1` and compare the differences between its conclusion and the goal.

Normalize the expressions using the abelian group laws. Establish `hBG : ∀ v, F b b (F b a v) = F b a (F b b v) + F b a v`. Introduce `v`. Establish `h` using `LinearMap.congr_fun (hgl b b b a) v`. Simplify using `only [if_neg hne, if_neg hne.symm, if_true, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply] at h`.

Rewrite using `[← sub_eq_zero]`. Rewrite `h` using `[← sub_eq_zero]`. Use `h using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws. Establish `hS : ∀ v ∈ S, F b a v ∈ S` using `fun v hv => hStb b a v hv`.

Take `⟨m, hm⟩` from `sl2Core (F a b) (F b a) (F a a) (F b b) S hfin hEG hAG hBG hS (ν a : ℂ) (ν b : ℂ) x hxS hx (hk.1 a) (hk.1 b) (hk.2 a b hab rfl)`. Use `⟨m, ?_⟩` and prove the remaining obligations. Apply `Complex.ofReal_injective` to reduce the goal to its premises. Use `push_cast`. Conclude with `hm`.
-/
theorem UpperTheory.RealTr.hwDom :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F : Fin n → Fin n → Module.End ℂ V), UF F → ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → Stb F S → ∀ (ν : Wt n), ∀ x ∈ S, x ≠ 0 → x ∈ hw F ν → Dom ν := by
  intro n V _ _ F hUF S hfin hStb ν x hxS hx hxw
  have hk : KHighest (fun _ => true) F ν x := hxw
  have hgl : GlRel F := hUF.gl
  intro a b hab
  have hne : a ≠ b := ne_of_lt hab
  have hEG : ∀ v, F a b (F b a v) = F b a (F a b v) + F a a v - F b b v := by
    intro v
    have h := LinearMap.congr_fun (hgl a b b a) v
    simp only [if_true, LinearMap.sub_apply, Module.End.mul_apply] at h
    rw [← sub_eq_zero]
    rw [← sub_eq_zero] at h
    convert h using 1
    abel
  have hAG : ∀ v, F a a (F b a v) = F b a (F a a v) - F b a v := by
    intro v
    have h := LinearMap.congr_fun (hgl a a b a) v
    simp only [if_neg hne, if_true, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply] at h
    rw [← sub_eq_zero]
    rw [← sub_eq_zero] at h
    convert h using 1
    abel
  have hBG : ∀ v, F b b (F b a v) = F b a (F b b v) + F b a v := by
    intro v
    have h := LinearMap.congr_fun (hgl b b b a) v
    simp only [if_neg hne, if_neg hne.symm, if_true, LinearMap.sub_apply, Module.End.mul_apply,
      LinearMap.zero_apply] at h
    rw [← sub_eq_zero]
    rw [← sub_eq_zero] at h
    convert h using 1
    abel
  have hS : ∀ v ∈ S, F b a v ∈ S := fun v hv => hStb b a v hv
  obtain ⟨m, hm⟩ := sl2Core (F a b) (F b a) (F a a) (F b b) S hfin hEG hAG hBG hS
    (ν a : ℂ) (ν b : ℂ) x hxS hx (hk.1 a) (hk.1 b) (hk.2 a b hab rfl)
  refine ⟨m, ?_⟩
  apply Complex.ofReal_injective
  push_cast
  exact hm
