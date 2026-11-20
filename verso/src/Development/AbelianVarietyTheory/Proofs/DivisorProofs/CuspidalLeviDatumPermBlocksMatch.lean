import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BlockProductIsomorphism
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions

open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

namespace GlobalTheory.FinGL.BlockMatch

variable {F : Type} [Field F] {r : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/- English proof (translation)
Set `c : Fin r → ℕ` to `fun k => if k ∈ S then 0 else 1`. Set `U : Subgroup (blockTri (κ` to `F) b) := (levi F b ⊓ GlobalTheory.FiniteGL.unipRadical F c).subgroupOf (blockTri b)`. Establish `hU : ∀ u : blockTri (κ` using `F) b, u ∈ U ↔ ∀ i j, ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j ≠ (1 : Matrix (Fin r) (Fin r) F) i j → b i = b j ∧ i ∈ S ∧ j ∉ S := by`. Introduce `u`. Simplify using `only [U, Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_levi, GlobalTheory.FiniteGL.mem_unipRadical, Matrix.sub_apply, sub_eq_zero]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩ i j hne`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Conclude with `hne (by rw [h1 i j h, Matrix.one_apply_ne (fun e => h (congrArg b e))])`.

Assume the negation of the conclusion as `h`. Use `hne (h2 i j ?_)` and prove the remaining obligations. Apply the tactic sequence `by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp_all [c]`. Introduce `h`. Use `⟨fun i j hij => ?_, fun i j hij => ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `h0`. Conclude with `hij (h i j (by rwa [Matrix.one_apply_ne (fun e => hij (congrArg b e))])).1`. Assume the negation of the conclusion as `h0`. Take `⟨-, hi, hj⟩` from `h i j h0`. Simplify using `[c, hi, hj] at hij`.

Use `letI := Fintype.ofFinite U`. Establish `hc : (Fintype.card U : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 Fintype.card_ne_zero`. Use extensionality with `v`. Establish `h0 : ∑ u : U, σ u v = 0`. Use `hσ.cusp S hS _ fun n hn => ?_` and prove the remaining obligations.

Rewrite using `[map_sum]`. Conclude with `Fintype.sum_equiv (Equiv.mulLeft (⟨n, (hU n).2 hn⟩ : U)) _ _ fun u => by simp`. Establish `h1` using `congrArg T h0`. Establish `h2 : ∀ u : U, T (σ u v) = T v` using `fun u => LinearMap.congr_fun (hT u ((hU u).1 u.2)) v`. Rewrite `h1` using `[map_sum, map_zero, Finset.sum_congr rfl fun u _ => h2 u, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]`.

Conclude with `(smul_eq_zero.1 h1).resolve_left hc`.
-/
theorem eq_zero_of_invariant [Finite F] {b : Fin r → ℕ} {σ : Representation ℂ (blockTri (κ := F) b) V}
    (hσ : IsCuspDatum b σ) (S : Finset (Fin r)) (hS : ∃ i j, b i = b j ∧ i ∈ S ∧ j ∉ S) (T : V →ₗ[ℂ] W)
    (hT : ∀ u : blockTri (κ := F) b, (∀ i j, ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j ≠
      (1 : Matrix (Fin r) (Fin r) F) i j → b i = b j ∧ i ∈ S ∧ j ∉ S) → T ∘ₗ σ u = T) : T = 0 := by
  classical
  let c : Fin r → ℕ := fun k => if k ∈ S then 0 else 1
  let U : Subgroup (blockTri (κ := F) b) :=
    (levi F b ⊓ GlobalTheory.FiniteGL.unipRadical F c).subgroupOf (blockTri b)
  have hU : ∀ u : blockTri (κ := F) b, u ∈ U ↔ ∀ i j, ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j ≠
      (1 : Matrix (Fin r) (Fin r) F) i j → b i = b j ∧ i ∈ S ∧ j ∉ S := by
    intro u
    simp only [U, Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_levi, GlobalTheory.FiniteGL.mem_unipRadical,
      Matrix.sub_apply, sub_eq_zero]
    constructor
    · rintro ⟨h1, h2⟩ i j hne
      refine ⟨?_, ?_⟩
      · by_contra h
        exact hne (by rw [h1 i j h, Matrix.one_apply_ne (fun e => h (congrArg b e))])
      · by_contra h
        refine hne (h2 i j ?_)
        by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp_all [c]
    · intro h
      refine ⟨fun i j hij => ?_, fun i j hij => ?_⟩
      · by_contra h0
        exact hij (h i j (by rwa [Matrix.one_apply_ne (fun e => hij (congrArg b e))])).1
      · by_contra h0
        obtain ⟨-, hi, hj⟩ := h i j h0
        simp [c, hi, hj] at hij
  letI := Fintype.ofFinite U
  have hc : (Fintype.card U : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  ext v
  have h0 : ∑ u : U, σ u v = 0 := by
    refine hσ.cusp S hS _ fun n hn => ?_
    rw [map_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft (⟨n, (hU n).2 hn⟩ : U)) _ _ fun u => by simp
  have h1 := congrArg T h0
  have h2 : ∀ u : U, T (σ u v) = T v := fun u => LinearMap.congr_fun (hT u ((hU u).1 u.2)) v
  rw [map_sum, map_zero, Finset.sum_congr rfl fun u _ => h2 u, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ] at h1
  exact (smul_eq_zero.1 h1).resolve_left hc

/- English proof (translation)
Use `mem_blockTri.2 fun i j hij => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h0`. Use `h i j (by rwa [Matrix.one_apply_ne (fun e => by rw [e] at hij; exact lt_irrefl _ hij)])` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem mem_blockTri_of_ne {b : Fin r → ℕ} {g : GL (Fin r) F}
    (h : ∀ i j, (g : Matrix (Fin r) (Fin r) F) i j ≠ (1 : Matrix (Fin r) (Fin r) F) i j → b i < b j) :
    g ∈ blockTri (κ := F) b := by
  refine mem_blockTri.2 fun i j hij => ?_
  by_contra h0
  have := h i j (by rwa [Matrix.one_apply_ne (fun e => by rw [e] at hij; exact lt_irrefl _ hij)])
  omega

/- English proof (translation)
Introduce `F _ _ r b b' V V' _ _ _ _ σ σ' hσ hσ' w T hT hint`. Establish `hone : ∀ k l : Fin r, (1 : Matrix (Fin r) (Fin r) F) (w k) (w l) = (1 : Matrix (Fin r) (Fin r) F) k l`. Introduce `k l`. Simplify using `[Matrix.one_apply]`. Establish `A : ∀ i j, b i = b j → ¬ b' (w i) < b' (w j)`.

Introduce `i j hij hlt`. Use `hT (eq_zero_of_invariant hσ (Finset.univ.filter fun k => b' (w k) ≤ b' (w i)) ⟨i, j, hij, by simp, by simpa using hlt⟩ T fun u hu => ?_)` and prove the remaining obligations. Establish `key : ∀ k l, ((permGL F w * u * (permGL F w)⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) k l ≠ (1 : Matrix (Fin r) (Fin r) F) k l → b' k < b' l`. Introduce `k l`. Take `⟨k, rfl⟩` from `w.surjective k`.

Take `⟨l, rfl⟩` from `w.surjective l`. Rewrite using `[conj_permGL_apply, hone]`. Introduce `h`. Take `⟨-, h1, h2⟩` from `hu k l h`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2`.

Use linear arithmetic over natural numbers and integers. Establish `h1` using `hint u ⟨_, mem_blockTri_of_ne key⟩ (by simp)`. Rewrite using `[hσ'.infl ⟨_, mem_blockTri_of_ne key⟩ fun k l hkl => by`. Assume the negation of the conclusion as `h0`. Use `key k l h0` as an intermediate fact.

Use the proof step `omega] at h1`. Conclude with `h1.symm`. Establish `B : ∀ i j, b' (w i) = b' (w j) → ¬ b i < b j`. Introduce `i j hij hlt`. Apply `hT` to reduce the goal to its premises.

Use extensionality with `v`. Use `hσ'.cusp (Finset.univ.filter fun k => b (w.symm k) ≤ b i) ⟨w i, w j, hij, by simp, by simpa using hlt⟩ (T v) fun u hu => ?_` and prove the remaining obligations. Establish `key : ∀ k l, (((permGL F w)⁻¹ * u * permGL F w : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) k l ≠ (1 : Matrix (Fin r) (Fin r) F) k l → b k < b l`. Introduce `k l`. Rewrite using `[← conj_permGL_apply w, ← hone]`.

Introduce `h`. Take `⟨-, h1, h2⟩` from `hu (w k) (w l) (by simpa [mul_assoc] using h)`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply] at h1 h2`. Use linear arithmetic over natural numbers and integers. Establish `h1` using `hint ⟨_, mem_blockTri_of_ne key⟩ u (by simp [mul_assoc])`.

Rewrite using `[hσ.infl ⟨_, mem_blockTri_of_ne key⟩ fun k l hkl => by`. Assume the negation of the conclusion as `h0`. Use `key k l h0` as an intermediate fact. Use the proof step `omega] at h1`. Conclude with `LinearMap.congr_fun h1 v`.

Introduce `i j`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `A i j h` as an intermediate fact. Use `A j i h.symm` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Introduce `h`. Use `B i j h` as an intermediate fact. Use `B j i h.symm` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem blocks_match : ∀ (F : Type) [Field F] [Finite F] (r : ℕ) (b b' : Fin r → ℕ) (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (σ : Representation ℂ (blockTri (κ := F) b) V) (σ' : Representation ℂ (blockTri (κ := F) b') V'), IsCuspDatum b σ → IsCuspDatum b' σ' → ∀ (w : Equiv.Perm (Fin r)) (T : V →ₗ[ℂ] V'), T ≠ 0 → (∀ (p : blockTri (κ := F) b) (p' : blockTri (κ := F) b'), (p' : GL (Fin r) F) * permGL F w = permGL F w * (p : GL (Fin r) F) → σ' p' ∘ₗ T = T ∘ₗ σ p) → ∀ i j : Fin r, b i = b j ↔ b' (w i) = b' (w j) := by
  intro F _ _ r b b' V V' _ _ _ _ σ σ' hσ hσ' w T hT hint
  have hone : ∀ k l : Fin r, (1 : Matrix (Fin r) (Fin r) F) (w k) (w l) = (1 : Matrix (Fin r) (Fin r) F) k l := by
    intro k l
    simp [Matrix.one_apply]
  have A : ∀ i j, b i = b j → ¬ b' (w i) < b' (w j) := by
    intro i j hij hlt
    refine hT (eq_zero_of_invariant hσ (Finset.univ.filter fun k => b' (w k) ≤ b' (w i))
      ⟨i, j, hij, by simp, by simpa using hlt⟩ T fun u hu => ?_)
    have key : ∀ k l, ((permGL F w * u * (permGL F w)⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) k l ≠
        (1 : Matrix (Fin r) (Fin r) F) k l → b' k < b' l := by
      intro k l
      obtain ⟨k, rfl⟩ := w.surjective k
      obtain ⟨l, rfl⟩ := w.surjective l
      rw [conj_permGL_apply, hone]
      intro h
      obtain ⟨-, h1, h2⟩ := hu k l h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      omega
    have h1 := hint u ⟨_, mem_blockTri_of_ne key⟩ (by simp)
    rw [hσ'.infl ⟨_, mem_blockTri_of_ne key⟩ fun k l hkl => by
      by_contra h0
      have := key k l h0
      omega] at h1
    exact h1.symm
  have B : ∀ i j, b' (w i) = b' (w j) → ¬ b i < b j := by
    intro i j hij hlt
    apply hT
    ext v
    refine hσ'.cusp (Finset.univ.filter fun k => b (w.symm k) ≤ b i)
      ⟨w i, w j, hij, by simp, by simpa using hlt⟩ (T v) fun u hu => ?_
    have key : ∀ k l, (((permGL F w)⁻¹ * u * permGL F w : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) k l ≠
        (1 : Matrix (Fin r) (Fin r) F) k l → b k < b l := by
      intro k l
      rw [← conj_permGL_apply w, ← hone]
      intro h
      obtain ⟨-, h1, h2⟩ := hu (w k) (w l) (by simpa [mul_assoc] using h)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply] at h1 h2
      omega
    have h1 := hint ⟨_, mem_blockTri_of_ne key⟩ u (by simp [mul_assoc])
    rw [hσ.infl ⟨_, mem_blockTri_of_ne key⟩ fun k l hkl => by
      by_contra h0
      have := key k l h0
      omega] at h1
    exact LinearMap.congr_fun h1 v
  intro i j
  constructor
  · intro h
    have := A i j h
    have := A j i h.symm
    omega
  · intro h
    have := B i j h
    have := B j i h.symm
    omega

end GlobalTheory.FinGL.BlockMatch
