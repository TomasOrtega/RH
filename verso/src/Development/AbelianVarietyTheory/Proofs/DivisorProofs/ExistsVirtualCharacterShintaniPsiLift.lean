import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootPowerSumCharpolyMemVirtualCharactersGLStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorInductionVirtualCharacterPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedHarishChandraInductionGLIsTwistedClassFunStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFunctionCharpolyGLHarishChandraRecursioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EveryElementIsNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVirtualCharacterTwistedHarishChandraInductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniLiftHarishChandraInductionEqTwistedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniLiftCharpolyRootPowerSumEqNormStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

/- English proof (translation)
Unfold `shLift`. Rewrite using `[dif_pos h]`.
-/
theorem shLift_eq_of_exists {F F' : Type} [Field F] [Field F'] [Algebra F F'] (s : F' ≃ₐ[F] F') {n : ℕ}
    (δ : GL (Fin n) F') (h : ∃ γ, IsNorm s δ γ) (f : GL (Fin n) F → ℂ) :
    shLift s f δ = f h.choose := by
  unfold shLift
  rw [dif_pos h]

/- English proof (translation)
Introduce `F F' _ _ _ _ s hp hs ι θ hθ k`. Use `haveI : Finite F := Finite.of_injective (algebraMap F F') (algebraMap F F').injective`. Use `haveI : FiniteDimensional F F' := Module.Finite.of_finite`. Establish `hcard : Nat.card (F' ≃ₐ[F] F') = Module.finrank F F'`. Conclude with `IsGalois.card_aut_eq_finrank F F'`.

Establish `hgen : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s` using `by haveI : Fact (Module.finrank F F').Prime := ⟨hp⟩`. Rewrite using `[zpowers_eq_top_of_prime_card hcard hs]`. Introduce `t`. Discharge the goal by the elementary cases of `trivial`. Establish `hlift1 : ∀ (m : ℕ) (δ : GL (Fin m) F'), shLift s (fun _ : GL (Fin m) F => (1 : ℂ)) δ = 1`.

Introduce `m δ`. Conclude with `shLift_eq_of_exists s δ (GlobalTheory.T.every_element_is_norm F F' s hgen m δ) _`. Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`.

Establish `hZ : ∀ a : Fin n, ∃ Z ∈ Virt ℂ ℂ (GHat F F' n), (∀ δ, Z (inl δ) = hc a (n - a) (psiG (fun P => ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F'))) a) (fun _ => 1) n δ) ∧ ∀ δ, Z (inl δ * inr s) = hcTw (s : F' →+* F') a (n - a) (shLift s (psiG (rootSum (pullθ ι θ) k) a)) (fun _ …`. Introduce `a`. Take `⟨Xa, hXa, h1, h2⟩` from `ih a a.2`. Take `⟨Z, hZv, hZe⟩` from `GlobalTheory.T.exists_virtualCharacter_twistedHarishChandraInductionGL F F' a (n - a) n (by omega) Xa hXa`. Use `⟨Z, hZv, fun δ => ?_, fun δ => ?_⟩` and prove the remaining obligations.

Establish `e` using `hZe 1 δ`. Simplify using `only [map_one, mul_one] at e`. Establish `e2 : (fun d => Xa (inl d)) = psiG (fun P => ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F'))) a`. Use function extensionality and compare the values at `h1`. Rewrite `e` using `[e2]`.

Conclude with `e`. Rewrite using `[hZe s δ]`. Establish `e2 : (fun d => Xa (inl d * inr s)) = shLift s (psiG (rootSum (pullθ ι θ) k) a)` using `funext h2`. Rewrite using `[e2]`. Use `choose Z hZv hZ1 hZ2 using hZ`.

Take `⟨A, hA, hA1, hA2⟩` from `GlobalTheory.T.exists_tensorInduction_virtualCharacter_prime (GL (Fin n) F') (F' ≃ₐ[F] F') (galAct F F' n) s (by rw [hcard]; exact hp) hs (fun x => rootSum θ k (Matrix.charpoly (x : Matrix (Fin n) (Fin n) F'))) (GlobalTheory.T.rootPowerSum_charpoly_mem_virtualCharacters_GL F' θ h …`. Use `⟨A - ∑ a : Fin n, Z a, sub_mem hA (sum_mem fun a _ => hZv a), fun g => ?_, fun δ => ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.sub_apply, Finset.sum_apply, hA1, hZ1]`. Rewrite using `[GlobalTheory.T.primitiveFunctionCharpolyGL_harishChandra_recursion F' _ n g]`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun a => hc a (n - a) (psiG (fun P => ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F'))) a) (fun _ => 1) n g) n]`.

Use `congr 1`. Unfold `chG`. Use `Finset.prod_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[galAct_apply, ← Matrix.charpoly_map]`. Use `congr 2`.

Simplify using `only [Pi.sub_apply, Finset.sum_apply, hA2, hZ2]`. Establish `hex` using `GlobalTheory.T.every_element_is_norm F F' s hgen n δ`. Rewrite using `[shLift_eq_of_exists s δ hex, GlobalTheory.T.primitiveFunctionCharpolyGL_harishChandra_recursion F _ n, ← shLift_eq_of_exists s δ hex (chG _ n), GlobalTheory.T.shintaniLift_charpoly_rootPowerSum_eq_norm F F' s hgen ι θ k n δ]`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun a => hcTw (s : F' →+* F') a (n - a) (shLift s (psiG (rootSum (pullθ ι θ) k) a)) (fun _ => 1) n δ) n]`. Use `congr 1`.

Unfold `chG nrm`. Rewrite using `[hcard]`. Use `Finset.sum_congr rfl fun a ha => ?_` and prove the remaining obligations. Establish `han : n = a + (n - a)` using `by have := Finset.mem_range.1 ha; omega`. Rewrite using `[← shLift_eq_of_exists s δ hex (hc a (n - a) (psiG (rootSum (pullθ ι θ) k) a) (fun _ => 1) n), GlobalTheory.T.shintaniLift_harishChandraInduction_eq_twisted F F' s hgen a (n - a) n han _ _ ((GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F (RingHom.id F) 0 …`.

Use `congr 1`. Use function extensionality and compare the values at `x`. Conclude with `(hlift1 _ x).symm`.
-/
theorem exists_virt_psi_lift : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (Module.finrank F F').Prime → s ≠ 1 → ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F') (θ : AlgebraicClosure F' →* ℂ), (∀ x y : AlgebraicClosure F', x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ k n : ℕ, ∃ X ∈ Virt ℂ ℂ (GHat F F' n), (∀ g, X (inl g) = psiG (fun P => ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F'))) n g) ∧ ∀ δ, X (inl δ * inr s) = shLift s (psiG (rootSum (pullθ ι θ) k) n) δ := by
  intro F F' _ _ _ _ s hp hs ι θ hθ k
  haveI : Finite F := Finite.of_injective (algebraMap F F') (algebraMap F F').injective
  haveI : FiniteDimensional F F' := Module.Finite.of_finite
  have hcard : Nat.card (F' ≃ₐ[F] F') = Module.finrank F F' := by
    exact IsGalois.card_aut_eq_finrank F F'
  have hgen : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s := by
    haveI : Fact (Module.finrank F F').Prime := ⟨hp⟩
    rw [zpowers_eq_top_of_prime_card hcard hs]; intro t; trivial
  have hlift1 : ∀ (m : ℕ) (δ : GL (Fin m) F'), shLift s (fun _ : GL (Fin m) F => (1 : ℂ)) δ = 1 := by
    intro m δ
    exact shLift_eq_of_exists s δ (GlobalTheory.T.every_element_is_norm F F' s hgen m δ) _
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have hZ : ∀ a : Fin n, ∃ Z ∈ Virt ℂ ℂ (GHat F F' n),
      (∀ δ, Z (inl δ) = hc a (n - a)
        (psiG (fun P => ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F'))) a) (fun _ => 1) n δ) ∧
      ∀ δ, Z (inl δ * inr s) = hcTw (s : F' →+* F') a (n - a)
        (shLift s (psiG (rootSum (pullθ ι θ) k) a)) (fun _ => 1) n δ := by
    intro a
    obtain ⟨Xa, hXa, h1, h2⟩ := ih a a.2
    obtain ⟨Z, hZv, hZe⟩ := GlobalTheory.T.exists_virtualCharacter_twistedHarishChandraInductionGL F F' a (n - a) n (by omega) Xa hXa
    refine ⟨Z, hZv, fun δ => ?_, fun δ => ?_⟩
    · have e := hZe 1 δ
      simp only [map_one, mul_one] at e
      have e2 : (fun d => Xa (inl d)) = psiG (fun P => ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F'))) a :=
        funext h1
      rw [e2] at e
      exact e
    · rw [hZe s δ]
      have e2 : (fun d => Xa (inl d * inr s)) = shLift s (psiG (rootSum (pullθ ι θ) k) a) := funext h2
      rw [e2]
  choose Z hZv hZ1 hZ2 using hZ
  obtain ⟨A, hA, hA1, hA2⟩ := GlobalTheory.T.exists_tensorInduction_virtualCharacter_prime (GL (Fin n) F') (F' ≃ₐ[F] F') (galAct F F' n) s
    (by rw [hcard]; exact hp) hs (fun x => rootSum θ k (Matrix.charpoly (x : Matrix (Fin n) (Fin n) F')))
    (GlobalTheory.T.rootPowerSum_charpoly_mem_virtualCharacters_GL F' θ hθ n k)
  refine ⟨A - ∑ a : Fin n, Z a, sub_mem hA (sum_mem fun a _ => hZv a), fun g => ?_, fun δ => ?_⟩
  · simp only [Pi.sub_apply, Finset.sum_apply, hA1, hZ1]
    rw [GlobalTheory.T.primitiveFunctionCharpolyGL_harishChandra_recursion F' _ n g]
    rw [Fin.sum_univ_eq_sum_range (fun a => hc a (n - a)
        (psiG (fun P => ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F'))) a) (fun _ => 1) n g) n]
    congr 1
    unfold chG
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [galAct_apply, ← Matrix.charpoly_map]
    congr 2
  · simp only [Pi.sub_apply, Finset.sum_apply, hA2, hZ2]
    have hex := GlobalTheory.T.every_element_is_norm F F' s hgen n δ
    rw [shLift_eq_of_exists s δ hex, GlobalTheory.T.primitiveFunctionCharpolyGL_harishChandra_recursion F _ n, ← shLift_eq_of_exists s δ hex (chG _ n),
      GlobalTheory.T.shintaniLift_charpoly_rootPowerSum_eq_norm F F' s hgen ι θ k n δ]
    rw [Fin.sum_univ_eq_sum_range (fun a => hcTw (s : F' →+* F') a (n - a)
        (shLift s (psiG (rootSum (pullθ ι θ) k) a)) (fun _ => 1) n δ) n]
    congr 1
    · unfold chG nrm
      rw [hcard]
    · refine Finset.sum_congr rfl fun a ha => ?_
      have han : n = a + (n - a) := by have := Finset.mem_range.1 ha; omega
      rw [← shLift_eq_of_exists s δ hex (hc a (n - a) (psiG (rootSum (pullθ ι θ) k) a) (fun _ => 1) n),
        GlobalTheory.T.shintaniLift_harishChandraInduction_eq_twisted F F' s hgen a (n - a) n han _ _
          ((GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F (RingHom.id F) 0 0 a (fun _ => 1) (fun _ => 1)).2.2 _).1 (fun _ _ => rfl)]
      congr 1
      funext x
      exact (hlift1 _ x).symm

end GlobalTheory.Shin
