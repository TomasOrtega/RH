import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
open IsLocalRing

namespace GlobalTheory

/- English proof (translation)
Introduce `R _ _ _ A B _ _ _ _ _ f hf hreg ψ hψ`. Establish `memA : ∀ a : A, a ∈ (Ideal.span {f}).map (algebraMap R A) → ∃ c : A, a = f • c`. Introduce `a ha`. Rewrite `ha` using `[Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton']`. Take `⟨c, hc⟩` from `ha`.

Conclude with `⟨c, by rw [← hc, Algebra.smul_def, mul_comm]⟩`. Establish `memB : ∀ b : B, f • b ∈ (Ideal.span {f}).map (algebraMap R B)`. Introduce `b`. Rewrite using `[Ideal.map_span, Set.image_singleton, Algebra.smul_def]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)`.

Establish `key : ∀ a : A, ψ a ∈ (Ideal.span {f}).map (algebraMap R B) → ∃ c : A, a = f • c` using `fun a h => memA a (hψ a h)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `set K : Submodule R A := LinearMap.ker ψ.toLinearMap with hK`. Establish `hFG : K.FG` using `IsNoetherian.noetherian K`. Establish `hle : K ≤ Ideal.span {f} • K`.

Introduce `a ha`. Establish `ha0 : ψ a = 0` using `ha`. Take `⟨c, rfl⟩` from `key a (by rw [ha0]; exact Submodule.zero_mem _)`. Establish `hc : ψ c = 0`. Apply `hreg` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `f • ψ c = f • (0 : B)`. Rewrite using `[smul_zero, ← map_smul]`. Conclude with `ha0`. Conclude with `Submodule.smul_mem_smul (Ideal.mem_span_singleton_self f) hc`. Establish `hjac : Ideal.span {f} ≤ Ideal.jacobson (⊥ : Ideal R)`.

Use `le_trans ?_ (maximalIdeal_le_jacobson _)` and prove the remaining obligations. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `hf`. Establish `hK0 : K = ⊥` using `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ K hFG hle hjac`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `a ha`. Establish `: a ∈ K` using `ha`. Rewrite `this` using `[hK0]`. Conclude with `(Submodule.mem_bot R).1 this`. Introduce `b ⟨a, ha'⟩`.

Establish `ha : ψ a = f • b` using `ha'`. Take `⟨c, rfl⟩` from `key a (by rw [ha]; exact memB b)`. Use `⟨c, ?_⟩` and prove the remaining obligations. Apply `hreg` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `f • ψ c = f • b`.

Rewrite using `[← map_smul, ha]`.
-/
theorem injective_and_saturated_of_injective_mod_regular :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (A B : Type) [CommRing A]
      [Algebra R A] [Module.Finite R A] [CommRing B] [Algebra R B] (f : R),
      f ∈ maximalIdeal R → IsSMulRegular B f → ∀ ψ : A →ₐ[R] B,
      (∀ a : A, ψ a ∈ (Ideal.span {f}).map (algebraMap R B) →
        a ∈ (Ideal.span {f}).map (algebraMap R A)) →
      Function.Injective ψ ∧ ∀ b : B, f • b ∈ ψ.range → b ∈ ψ.range := by
  intro R _ _ _ A B _ _ _ _ _ f hf hreg ψ hψ

  have memA : ∀ a : A, a ∈ (Ideal.span {f}).map (algebraMap R A) → ∃ c : A, a = f • c := by
    intro a ha
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at ha
    obtain ⟨c, hc⟩ := ha
    exact ⟨c, by rw [← hc, Algebra.smul_def, mul_comm]⟩
  have memB : ∀ b : B, f • b ∈ (Ideal.span {f}).map (algebraMap R B) := by
    intro b
    rw [Ideal.map_span, Set.image_singleton, Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have key : ∀ a : A, ψ a ∈ (Ideal.span {f}).map (algebraMap R B) → ∃ c : A, a = f • c :=
    fun a h => memA a (hψ a h)
  refine ⟨?_, ?_⟩
  ·
    set K : Submodule R A := LinearMap.ker ψ.toLinearMap with hK
    have hFG : K.FG := IsNoetherian.noetherian K
    have hle : K ≤ Ideal.span {f} • K := by
      intro a ha
      have ha0 : ψ a = 0 := ha
      obtain ⟨c, rfl⟩ := key a (by rw [ha0]; exact Submodule.zero_mem _)
      have hc : ψ c = 0 := by
        apply hreg
        change f • ψ c = f • (0 : B)
        rw [smul_zero, ← map_smul]
        exact ha0
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self f) hc
    have hjac : Ideal.span {f} ≤ Ideal.jacobson (⊥ : Ideal R) := by
      refine le_trans ?_ (maximalIdeal_le_jacobson _)
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hf
    have hK0 : K = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ K hFG hle hjac
    rw [injective_iff_map_eq_zero]
    intro a ha
    have : a ∈ K := ha
    rw [hK0] at this
    exact (Submodule.mem_bot R).1 this
  · intro b ⟨a, ha'⟩
    have ha : ψ a = f • b := ha'
    obtain ⟨c, rfl⟩ := key a (by rw [ha]; exact memB b)
    refine ⟨c, ?_⟩
    apply hreg
    change f • ψ c = f • b
    rw [← map_smul, ha]

end GlobalTheory
