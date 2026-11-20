import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTwistedNormGLBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoboundaryOfNormOneInSubalgebraStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.FlagDesc

def parAlg (K : Type) [Field K] (a n : ℕ) : Subalgebra K (Matrix (Fin n) (Fin n) K) where
  carrier := {M | ∀ i j : Fin n, (j : ℕ) < a → a ≤ (i : ℕ) → M i j = 0}
  mul_mem' {M N} hM hN i j hj hi := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : (k : ℕ) < a
    · rw [hM i k hk hi, zero_mul]
    · rw [hN k j hj (not_lt.1 hk), mul_zero]
  add_mem' {M N} hM hN i j hj hi := by
    rw [Matrix.add_apply, hM i j hj hi, hN i j hj hi, add_zero]
  algebraMap_mem' c i j hj hi := by
    have hij : i ≠ j := fun h => by subst h; omega
    simp [Matrix.algebraMap_matrix_apply, hij]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem inPar_iff_mem {K : Type} [Field K] {a n : ℕ} (x : GL (Fin n) K) :
    InPar a x ↔ (x : Matrix (Fin n) (Fin n) K) ∈ parAlg K a n := Iff.rfl

/- English proof (translation)
Introduce `i j hj hi`. Establish `hij : i ≠ j` using `fun h => by subst h; omega`. Simplify using `[Matrix.one_apply_ne hij]`.
-/
theorem inPar_one {K : Type} [Field K] (a n : ℕ) : InPar a (1 : GL (Fin n) K) := by
  intro i j hj hi
  have hij : i ≠ j := fun h => by subst h; omega
  simp [Matrix.one_apply_ne hij]

/- English proof (translation)
Rewrite using `[inPar_iff_mem, Units.val_mul]`. Conclude with `(parAlg K a n).mul_mem hx hz`.
-/
theorem inPar_mul {K : Type} [Field K] {a n : ℕ} {x z : GL (Fin n) K} (hx : InPar a x) (hz : InPar a z) :
    InPar a (x * z) := by
  rw [inPar_iff_mem, Units.val_mul]
  exact (parAlg K a n).mul_mem hx hz

/- English proof (translation)
Establish `hb : (x : Matrix (Fin n) (Fin n) K).BlockTriangular (fun i : Fin n => if a ≤ (i : ℕ) then (1 : ℕ) else 0)`. Introduce `i j hij`. Apply `h i j` to reduce the goal to its premises. Assume the negation of the conclusion as `hc`. Simplify using `only at hij`.

Apply the tactic sequence `split_ifs at hij <;> omega`. Assume the negation of the conclusion as `hc`. Simplify using `only at hij`. Apply the tactic sequence `split_ifs at hij <;> omega`. Introduce `i j hj hi`.

Rewrite using `[Matrix.coe_units_inv]`. Apply `Matrix.blockTriangular_inv_of_blockTriangular hb` to reduce the goal to its premises. Simplify using `[hi, not_le.2 hj]`.
-/
theorem inPar_inv {K : Type} [Field K] {a n : ℕ} {x : GL (Fin n) K} (h : InPar a x) : InPar a x⁻¹ := by
  have hb : (x : Matrix (Fin n) (Fin n) K).BlockTriangular
      (fun i : Fin n => if a ≤ (i : ℕ) then (1 : ℕ) else 0) := by
    intro i j hij
    apply h i j
    · by_contra hc
      simp only at hij
      split_ifs at hij <;> omega
    · by_contra hc
      simp only at hij
      split_ifs at hij <;> omega
  intro i j hj hi
  rw [Matrix.coe_units_inv]
  apply Matrix.blockTriangular_inv_of_blockTriangular hb
  simp [hi, not_le.2 hj]

/- English proof (translation)
Proceed by induction on `hX using Algebra.adjoin_induction with`. Consider the case `mem x hx => rw [Set.mem_singleton_iff.1 hx]`. Conclude with `hM`. Consider the case `algebraMap r`. Rewrite using `[Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, Units.inv_mul]`.

Conclude with `B.smul_mem B.one_mem r`. Consider the case `add x y _ _ hx hy => rw [mul_add, add_mul]`. Conclude with `B.add_mem hx hy`. Consider the case `mul x y _ _ hx hy`. Establish `e : ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (x * y) * u = (((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * x * u) * (((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * y * u)`.

Simplify using `only [mul_assoc, Units.mul_inv_cancel_left]`. Rewrite using `[e]`. Conclude with `B.mul_mem hx hy`.
-/
theorem conj_adjoin_mem {K : Type} [Field K] {n : ℕ} (B : Subalgebra K (Matrix (Fin n) (Fin n) K))
    (u : GL (Fin n) K) (M X : Matrix (Fin n) (Fin n) K) (hX : X ∈ Algebra.adjoin K {M})
    (hM : ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M * u ∈ B) :
    ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * X * u ∈ B := by
  induction hX using Algebra.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact hM
  | algebraMap r =>
      rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, Units.inv_mul]
      exact B.smul_mem B.one_mem r
  | add x y _ _ hx hy => rw [mul_add, add_mul]; exact B.add_mem hx hy
  | mul x y _ _ hx hy =>
      have e : ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (x * y) * u =
          (((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * x * u) *
          (((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * y * u) := by
        simp only [mul_assoc, Units.mul_inv_cancel_left]
      rw [e]; exact B.mul_mem hx hy

variable {F F' : Type} [Field F] [Field F'] [Algebra F F']

/- English proof (translation)
Simplify using `[galAct_apply, gal]`.
-/
theorem galAct_coe (n : ℕ) (t : F' ≃ₐ[F] F') (x : GL (Fin n) F') (i j : Fin n) :
    (galAct F F' n t x : Matrix (Fin n) (Fin n) F') i j = t ((x : Matrix (Fin n) (Fin n) F') i j) := by
  simp [galAct_apply, gal]

/- English proof (translation)
Simplify using `[incl, gal]`.
-/
theorem incl_coe (n : ℕ) (x : GL (Fin n) F) (i j : Fin n) :
    (incl F F' n x : Matrix (Fin n) (Fin n) F') i j = algebraMap F F' ((x : Matrix (Fin n) (Fin n) F) i j) := by
  simp [incl, gal]

/- English proof (translation)
Introduce `i j hj hi`. Rewrite using `[galAct_coe, h i j hj hi, map_zero]`.
-/
theorem inPar_galAct {a n : ℕ} (t : F' ≃ₐ[F] F') {x : GL (Fin n) F'} (h : InPar a x) :
    InPar a (galAct F F' n t x) := by
  intro i j hj hi
  rw [galAct_coe, h i j hj hi, map_zero]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h i j hj hi`. Use `h i j hj hi` as an intermediate fact. Rewrite `this` using `[incl_coe]`. Conclude with `(FaithfulSMul.algebraMap_injective F F') (by rw [this, map_zero])`.

Introduce `h i j hj hi`. Rewrite using `[incl_coe, h i j hj hi, map_zero]`.
-/
theorem inPar_incl {a n : ℕ} (x : GL (Fin n) F) : InPar a (incl F F' n x) ↔ InPar a x := by
  constructor
  · intro h i j hj hi
    have := h i j hj hi
    rw [incl_coe] at this
    exact (FaithfulSMul.algebraMap_injective F F') (by rw [this, map_zero])
  · intro h i j hj hi
    rw [incl_coe, h i j hj hi, map_zero]

/- English proof (translation)
Unfold `nrm nrmG`. Apply `List.prod_induction (fun z => InPar a z)` to reduce the goal to its premises. Introduce `u v hu hv`. Conclude with `inPar_mul hu hv`. Conclude with `inPar_one a n`.

Introduce `z hz`. Take `⟨i, -, rfl⟩` from `List.mem_map.1 hz`. Conclude with `inPar_galAct _ h`.
-/
theorem inPar_nrm {a n : ℕ} (s : F' ≃ₐ[F] F') {x : GL (Fin n) F'} (h : InPar a x) : InPar a (nrm s x) := by
  unfold nrm nrmG
  apply List.prod_induction (fun z => InPar a z)
  · intro u v hu hv; exact inPar_mul hu hv
  · exact inPar_one a n
  · intro z hz
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hz
    exact inPar_galAct _ h

/- English proof (translation)
Unfold `nrm nrmG`. Apply `List.prod_eq_one` to reduce the goal to its premises. Introduce `x hx`. Take `⟨i, -, rfl⟩` from `List.mem_map.1 hx`. Conclude with `map_one _`.
-/
theorem nrm_one' (s : F' ≃ₐ[F] F') (n : ℕ) : nrm s (1 : GL (Fin n) F') = 1 := by
  unfold nrm nrmG
  apply List.prod_eq_one
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact map_one _

end GlobalTheory.Shin.FlagDesc

open GlobalTheory.Shin.FlagDesc in

/- English proof (translation)
Introduce `F F' _ _ _ _ s hs a n _ γ δ y hδ hN`. Take `⟨hfix, -, hconj, -, -⟩` from `GlobalTheory.T.galoisTwistedNormGL_basic_properties F F' s hs n`. Establish `hB : ∀ x ∈ parAlg F' a n, x.map s ∈ parAlg F' a n`. Introduce `M hM i j hj hi`. Simplify using `only [Matrix.map_apply]`.

Rewrite using `[hM i j hj hi, map_zero]`. Prove the components needed by the constructor for the conclusion. Introduce `hq`. Establish `hγP : InPar a (y⁻¹ * incl F F' n γ * y)`. Rewrite using `[← hN, ← hconj]`.

Conclude with `inPar_nrm s hq`. Establish `hδP : InPar a (y⁻¹ * δ * y)`. Rewrite using `[inPar_iff_mem, Units.val_mul, Units.val_mul]`. Apply `conj_adjoin_mem _ y _ _ hδ` to reduce the goal to its premises. Use `(inPar_iff_mem _).1 hγP` as an intermediate fact.

Rewrite `this` using `[Units.val_mul, Units.val_mul]`. Then use the resulting hypothesis. Establish `hεP : InPar a (y⁻¹ * galAct F F' n s y)`. Establish `e : y⁻¹ * galAct F F' n s y = (y⁻¹ * δ * y)⁻¹ * (y⁻¹ * δ * galAct F F' n s y)` using `by group`. Rewrite using `[e]`. Conclude with `inPar_mul (inPar_inv hδP) hq`.

Establish `hεN : nrm s (y⁻¹ * galAct F F' n s y) = 1`. Use `hconj 1 y` as an intermediate fact. Rewrite `this` using `[nrm_one', mul_one, inv_mul_cancel]`. Conclude with `this`. Take `⟨x, hxB, hε⟩` from `GlobalTheory.T.exists_coboundary_of_norm_one_in_subalgebra F F' s hs n (parAlg F' a n) hB _ hεP hεN`.

Establish `hfx : galAct F F' n s (y * x⁻¹) = y * x⁻¹`. Rewrite using `[map_mul, map_inv]`. Combine the equalities or inequalities in the displayed calculation. Take `⟨y₀, hy₀⟩` from `(hfix _).1 hfx`. Use `⟨y₀, x, hxB, by rw [hy₀]; group, ?_⟩` and prove the remaining obligations.

Rewrite using `[← inPar_incl (F' := F'), map_mul, map_mul, map_inv, hy₀]`. Establish `e : (y * x⁻¹)⁻¹ * incl F F' n γ * (y * x⁻¹) = x * (y⁻¹ * incl F F' n γ * y) * x⁻¹` using `by group`. Rewrite using `[e]`. Conclude with `inPar_mul (inPar_mul hxB hγP) (inPar_inv hxB)`. Introduce and unpack `⟨y₀, p, hp, rfl, hγ0⟩`.

Establish `hs0 : galAct F F' n s (incl F F' n y₀) = incl F F' n y₀` using `(hfix _).2 ⟨y₀, rfl⟩`. Establish `e : (incl F F' n y₀ * p)⁻¹ * δ * galAct F F' n s (incl F F' n y₀ * p) = p⁻¹ * ((incl F F' n y₀)⁻¹ * δ * incl F F' n y₀) * galAct F F' n s p`. Rewrite using `[map_mul, hs0]`. Use `group`. Rewrite using `[e]`.

Establish `hmid : InPar a ((incl F F' n y₀)⁻¹ * δ * incl F F' n y₀)`. Rewrite using `[inPar_iff_mem, Units.val_mul, Units.val_mul]`. Apply `conj_adjoin_mem _ _ _ _ hδ` to reduce the goal to its premises. Use `(inPar_iff_mem _).1 ((inPar_incl (F' := F') _).2 hγ0)` as an intermediate fact. Rewrite `this` using `[map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul]`. Then use the resulting hypothesis.

Conclude with `inPar_mul (inPar_mul (inPar_inv hp) hmid) (inPar_galAct s hp)`.
-/
theorem GlobalTheory.Shin.inPar_twistedConj_iff : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (a n : ℕ), a ≤ n → ∀ (γ : GL (Fin n) F) (δ y : GL (Fin n) F'), (δ : Matrix (Fin n) (Fin n) F') ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} → nrm s δ = incl F F' n γ → (InPar a (y⁻¹ * δ * galAct F F' n s y) ↔ ∃ (y₀ : GL (Fin n) F) (p : GL (Fin n) F'), InPar a p ∧ y = incl F F' n y₀ * p ∧ InPar a (y₀⁻¹ * γ * y₀)) := by
  intro F F' _ _ _ _ s hs a n _ γ δ y hδ hN
  obtain ⟨hfix, -, hconj, -, -⟩ := GlobalTheory.T.galoisTwistedNormGL_basic_properties F F' s hs n
  have hB : ∀ x ∈ parAlg F' a n, x.map s ∈ parAlg F' a n := by
    intro M hM i j hj hi
    simp only [Matrix.map_apply]
    rw [hM i j hj hi, map_zero]
  constructor
  · intro hq
    have hγP : InPar a (y⁻¹ * incl F F' n γ * y) := by
      rw [← hN, ← hconj]; exact inPar_nrm s hq
    have hδP : InPar a (y⁻¹ * δ * y) := by
      rw [inPar_iff_mem, Units.val_mul, Units.val_mul]
      apply conj_adjoin_mem _ y _ _ hδ
      have := (inPar_iff_mem _).1 hγP
      rwa [Units.val_mul, Units.val_mul] at this
    have hεP : InPar a (y⁻¹ * galAct F F' n s y) := by
      have e : y⁻¹ * galAct F F' n s y = (y⁻¹ * δ * y)⁻¹ * (y⁻¹ * δ * galAct F F' n s y) := by group
      rw [e]; exact inPar_mul (inPar_inv hδP) hq
    have hεN : nrm s (y⁻¹ * galAct F F' n s y) = 1 := by
      have := hconj 1 y
      rw [nrm_one', mul_one, inv_mul_cancel] at this
      exact this
    obtain ⟨x, hxB, hε⟩ := GlobalTheory.T.exists_coboundary_of_norm_one_in_subalgebra F F' s hs n (parAlg F' a n) hB _ hεP hεN
    have hfx : galAct F F' n s (y * x⁻¹) = y * x⁻¹ := by
      rw [map_mul, map_inv]
      calc galAct F F' n s y * (galAct F F' n s x)⁻¹
          = y * (y⁻¹ * galAct F F' n s y) * (galAct F F' n s x)⁻¹ := by group
        _ = y * (x⁻¹ * galAct F F' n s x) * (galAct F F' n s x)⁻¹ := by rw [hε]
        _ = y * x⁻¹ := by group
    obtain ⟨y₀, hy₀⟩ := (hfix _).1 hfx
    refine ⟨y₀, x, hxB, by rw [hy₀]; group, ?_⟩
    rw [← inPar_incl (F' := F'), map_mul, map_mul, map_inv, hy₀]
    have e : (y * x⁻¹)⁻¹ * incl F F' n γ * (y * x⁻¹) = x * (y⁻¹ * incl F F' n γ * y) * x⁻¹ := by group
    rw [e]
    exact inPar_mul (inPar_mul hxB hγP) (inPar_inv hxB)
  · rintro ⟨y₀, p, hp, rfl, hγ0⟩
    have hs0 : galAct F F' n s (incl F F' n y₀) = incl F F' n y₀ := (hfix _).2 ⟨y₀, rfl⟩
    have e : (incl F F' n y₀ * p)⁻¹ * δ * galAct F F' n s (incl F F' n y₀ * p) =
        p⁻¹ * ((incl F F' n y₀)⁻¹ * δ * incl F F' n y₀) * galAct F F' n s p := by
      rw [map_mul, hs0]; group
    rw [e]
    have hmid : InPar a ((incl F F' n y₀)⁻¹ * δ * incl F F' n y₀) := by
      rw [inPar_iff_mem, Units.val_mul, Units.val_mul]
      apply conj_adjoin_mem _ _ _ _ hδ
      have := (inPar_iff_mem _).1 ((inPar_incl (F' := F') _).2 hγ0)
      rwa [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul] at this
    exact inPar_mul (inPar_mul (inPar_inv hp) hmid) (inPar_galAct s hp)
