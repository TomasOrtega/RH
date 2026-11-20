import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTwistedNormGLBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoboundaryOfNormOneInSubalgebraStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

/- English proof (translation)
Take `⟨hfix, hinj, hconj, -, -⟩` from `GlobalTheory.T.galoisTwistedNormGL_basic_properties F F' s hs n`. Establish `h90` using `GlobalTheory.T.exists_coboundary_of_norm_one_in_subalgebra F F' s hs n B hB`. Establish `hsB : ∀ x : GL (Fin n) F', (x : Matrix (Fin n) (Fin n) F') ∈ B → ((galAct F F' n s x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B` using `fun x hx => hB _ hx`. Establish `hinv : ∀ x : GL (Fin n) F', (x : Matrix (Fin n) (Fin n) F') ∈ B → ((x⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B`. Introduce `x hx`.

Take `⟨k, hk, hxk⟩` from `(isOfFinOrder_of_finite x).exists_pow_eq_one`. Establish `hx' : x⁻¹ = x ^ (k - 1)`. Rewrite using `[eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel hk, hxk]`. Rewrite using `[hx', Units.val_pow_eq_pow_val]`. Conclude with `pow_mem hx _`.

Establish `hmul : ∀ a b : GL (Fin n) F', (a : Matrix (Fin n) (Fin n) F') ∈ B → (b : Matrix (Fin n) (Fin n) F') ∈ B → ((a * b : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B`. Introduce `a b ha hb`. Rewrite using `[Units.val_mul]`. Conclude with `mul_mem ha hb`. Establish `hn1 : nrm s (1 : GL (Fin n) F') = 1`.

Unfold `nrm nrmG`. Apply `List.prod_eq_one` to reduce the goal to its premises. Introduce `y hy`. Take `⟨i, -, rfl⟩` from `List.mem_map.1 hy`. Conclude with `map_one _`.

Establish `hnorm : ∀ x : GL (Fin n) F', nrm s (x⁻¹ * galAct F F' n s x) = 1`. Introduce `x`. Establish `h` using `hconj 1 x`. Rewrite `h` using `[mul_one, hn1, mul_one, inv_mul_cancel]`. Conclude with `h`.

Set `U` to `{x : GL (Fin n) F' // (x : Matrix (Fin n) (Fin n) F') ∈ B}`. Set `N` to `{ε : GL (Fin n) F' // (ε : Matrix (Fin n) (Fin n) F') ∈ B ∧ nrm s ε = 1}`. Set `U₀` to `{x : GL (Fin n) F // ((incl F F' n x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B}`. Set `φ : U → N` to `fun x => ⟨x.1⁻¹ * galAct F F' n s x.1, hmul _ _ (hinv _ x.2) (hsB _ x.2), hnorm _⟩`. Establish `hsec : ∀ ε : N, ∃ x : U, φ x = ε`.

Introduce `ε`. Take `⟨x, hx, he⟩` from `h90 ε.1 ε.2.1 ε.2.2`. Conclude with `⟨⟨x, hx⟩, Subtype.ext he.symm⟩`. Use `choose sec hsec using hsec`. Establish `hfixI : ∀ z : GL (Fin n) F, galAct F F' n s (incl F F' n z) = incl F F' n z` using `fun z => (hfix _).2 ⟨z, rfl⟩`.

Set `f : ∀ ε : N, U₀ → {x : U // φ x = ε}` to `fun ε z => ⟨⟨incl F F' n z.1 * (sec ε).1, hmul _ _ z.2 (sec ε).2⟩, by`. Use `Eq.trans ?_ (hsec ε)` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Use `show (incl F F' n z.1 * (sec ε).1)⁻¹ * galAct F F' n s (incl F F' n z.1 * (sec ε).1) = (sec ε).1⁻¹ * galAct F F' n s (sec ε).1`. Rewrite using `[map_mul, hfixI]`.

Use the proof step `group⟩`. Establish `hbij : ∀ ε : N, Function.Bijective (f ε)`. Introduce `ε`. Prove the components needed by the constructor for the conclusion. Introduce `z w h`.

Establish `h' : incl F F' n z.1 * (sec ε).1 = incl F F' n w.1 * (sec ε).1` using `congrArg (fun u : {x : U // φ x = ε} => u.1.1) h`. Conclude with `Subtype.ext (hinj (mul_right_cancel h'))`. Introduce and unpack `⟨y, hy⟩ set x := sec ε with hxdef`. Establish `hyx : φ y = φ x` using `by rw [hy, hsec ε]`. Establish `h1 : y.1⁻¹ * galAct F F' n s y.1 = x.1⁻¹ * galAct F F' n s x.1` using `congrArg Subtype.val hyx`.

Establish `h2 : galAct F F' n s (y.1 * x.1⁻¹) = y.1 * x.1⁻¹`. Rewrite using `[map_mul, map_inv]`. Combine the equalities or inequalities in the displayed calculation. Take `⟨z, hz⟩` from `(hfix _).1 h2`. Establish `hzB : ((incl F F' n z : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B`.

Rewrite using `[hz]`. Conclude with `hmul _ _ y.2 (hinv _ x.2)`. Use `⟨⟨z, hzB⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show incl F F' n z * x.1 = y.1`. Rewrite using `[hz]`. Use `group`. Set `E : U ≃ N × U₀` to `(Equiv.sigmaFiberEquiv φ).symm.trans (Equiv.sigmaEquivProdOfEquiv fun ε => (Equiv.ofBijective (f ε) (hbij ε)).symm)`. Rewrite using `[← Nat.card_prod]`.

Conclude with `(Nat.card_congr E).symm`.
-/
theorem card_nrm_one_mul_card_fixed (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F']
    (s : F' ≃ₐ[F] F') (hs : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) (n : ℕ)
    (B : Subalgebra F' (Matrix (Fin n) (Fin n) F')) (hB : ∀ x ∈ B, x.map s ∈ B) :
    Nat.card {ε : GL (Fin n) F' // (ε : Matrix (Fin n) (Fin n) F') ∈ B ∧ nrm s ε = 1} *
      Nat.card {x : GL (Fin n) F // ((incl F F' n x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B} =
      Nat.card {x : GL (Fin n) F' // (x : Matrix (Fin n) (Fin n) F') ∈ B} := by
  obtain ⟨hfix, hinj, hconj, -, -⟩ := GlobalTheory.T.galoisTwistedNormGL_basic_properties F F' s hs n
  have h90 := GlobalTheory.T.exists_coboundary_of_norm_one_in_subalgebra F F' s hs n B hB
  have hsB : ∀ x : GL (Fin n) F', (x : Matrix (Fin n) (Fin n) F') ∈ B →
      ((galAct F F' n s x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B := fun x hx => hB _ hx
  have hinv : ∀ x : GL (Fin n) F', (x : Matrix (Fin n) (Fin n) F') ∈ B →
      ((x⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B := by
    intro x hx
    obtain ⟨k, hk, hxk⟩ := (isOfFinOrder_of_finite x).exists_pow_eq_one
    have hx' : x⁻¹ = x ^ (k - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel hk, hxk]
    rw [hx', Units.val_pow_eq_pow_val]
    exact pow_mem hx _
  have hmul : ∀ a b : GL (Fin n) F', (a : Matrix (Fin n) (Fin n) F') ∈ B → (b : Matrix (Fin n) (Fin n) F') ∈ B →
      ((a * b : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B := by
    intro a b ha hb
    rw [Units.val_mul]
    exact mul_mem ha hb
  have hn1 : nrm s (1 : GL (Fin n) F') = 1 := by
    unfold nrm nrmG
    apply List.prod_eq_one
    intro y hy
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
    exact map_one _
  have hnorm : ∀ x : GL (Fin n) F', nrm s (x⁻¹ * galAct F F' n s x) = 1 := by
    intro x
    have h := hconj 1 x
    rw [mul_one, hn1, mul_one, inv_mul_cancel] at h
    exact h
  let U := {x : GL (Fin n) F' // (x : Matrix (Fin n) (Fin n) F') ∈ B}
  let N := {ε : GL (Fin n) F' // (ε : Matrix (Fin n) (Fin n) F') ∈ B ∧ nrm s ε = 1}
  let U₀ := {x : GL (Fin n) F // ((incl F F' n x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B}
  let φ : U → N := fun x =>
    ⟨x.1⁻¹ * galAct F F' n s x.1, hmul _ _ (hinv _ x.2) (hsB _ x.2), hnorm _⟩
  have hsec : ∀ ε : N, ∃ x : U, φ x = ε := by
    intro ε
    obtain ⟨x, hx, he⟩ := h90 ε.1 ε.2.1 ε.2.2
    exact ⟨⟨x, hx⟩, Subtype.ext he.symm⟩
  choose sec hsec using hsec
  have hfixI : ∀ z : GL (Fin n) F, galAct F F' n s (incl F F' n z) = incl F F' n z :=
    fun z => (hfix _).2 ⟨z, rfl⟩
  let f : ∀ ε : N, U₀ → {x : U // φ x = ε} := fun ε z =>
    ⟨⟨incl F F' n z.1 * (sec ε).1, hmul _ _ z.2 (sec ε).2⟩, by
      refine Eq.trans ?_ (hsec ε)
      apply Subtype.ext
      show (incl F F' n z.1 * (sec ε).1)⁻¹ * galAct F F' n s (incl F F' n z.1 * (sec ε).1) =
        (sec ε).1⁻¹ * galAct F F' n s (sec ε).1
      rw [map_mul, hfixI]
      group⟩
  have hbij : ∀ ε : N, Function.Bijective (f ε) := by
    intro ε
    constructor
    · intro z w h
      have h' : incl F F' n z.1 * (sec ε).1 = incl F F' n w.1 * (sec ε).1 :=
        congrArg (fun u : {x : U // φ x = ε} => u.1.1) h
      exact Subtype.ext (hinj (mul_right_cancel h'))
    · rintro ⟨y, hy⟩
      set x := sec ε with hxdef
      have hyx : φ y = φ x := by rw [hy, hsec ε]
      have h1 : y.1⁻¹ * galAct F F' n s y.1 = x.1⁻¹ * galAct F F' n s x.1 :=
        congrArg Subtype.val hyx
      have h2 : galAct F F' n s (y.1 * x.1⁻¹) = y.1 * x.1⁻¹ := by
        rw [map_mul, map_inv]
        calc galAct F F' n s y.1 * (galAct F F' n s x.1)⁻¹
            = y.1 * (y.1⁻¹ * galAct F F' n s y.1) * (galAct F F' n s x.1)⁻¹ := by group
          _ = y.1 * (x.1⁻¹ * galAct F F' n s x.1) * (galAct F F' n s x.1)⁻¹ := by rw [h1]
          _ = y.1 * x.1⁻¹ := by group
      obtain ⟨z, hz⟩ := (hfix _).1 h2
      have hzB : ((incl F F' n z : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B := by
        rw [hz]; exact hmul _ _ y.2 (hinv _ x.2)
      refine ⟨⟨z, hzB⟩, ?_⟩
      apply Subtype.ext; apply Subtype.ext
      show incl F F' n z * x.1 = y.1
      rw [hz]; group
  let E : U ≃ N × U₀ := (Equiv.sigmaFiberEquiv φ).symm.trans
    (Equiv.sigmaEquivProdOfEquiv fun ε => (Equiv.ofBijective (f ε) (hbij ε)).symm)
  rw [← Nat.card_prod]
  exact (Nat.card_congr E).symm

end GlobalTheory.Shin
