import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
open IsLocalRing

namespace GlobalTheory

/- English proof (translation)
Use `by_contra! hne`. Establish `h0 : Ring.KrullDimLE 0 (R ⧸ Ideal.span {f})`. Use `Ring.krullDimLE_zero_iff.mpr fun Q hQ => ?_` and prove the remaining obligations. Establish `hc : Q.comap (Ideal.Quotient.mk (Ideal.span {f})) = maximalIdeal R`. Use `hne _ (Ideal.comap_isPrime _ _) ?_` and prove the remaining obligations.

Rewrite using `[Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f)]`. Conclude with `Q.zero_mem`. Establish `hmax` using `(maximalIdeal.isMaximal R).map_of_surjective_of_ker_le (f := Ideal.Quotient.mk (Ideal.span {f})) Ideal.Quotient.mk_surjective (by rw [← hc]; exact Ideal.comap_mono bot_le)`. Rewrite `hmax` using `[← hc, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]`. Then use the resulting hypothesis. Use `(Ring.krullDimLE_iff (n := 0)).mp h0` as an intermediate fact.

Establish `h10` using `hdim.trans this`. Evaluate the numerical expressions using `at h10`.
-/
theorem exists_prime_ne_maximalIdeal_of_one_le_ringKrullDim_quot
    (R : Type) [CommRing R] [IsLocalRing R] (f : R)
    (hdim : 1 ≤ ringKrullDim (R ⧸ Ideal.span {f})) :
    ∃ P : Ideal R, P.IsPrime ∧ f ∈ P ∧ P ≠ maximalIdeal R := by
  by_contra! hne
  have h0 : Ring.KrullDimLE 0 (R ⧸ Ideal.span {f}) := by
    refine Ring.krullDimLE_zero_iff.mpr fun Q hQ => ?_
    have hc : Q.comap (Ideal.Quotient.mk (Ideal.span {f})) = maximalIdeal R := by
      refine hne _ (Ideal.comap_isPrime _ _) ?_
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f)]
      exact Q.zero_mem
    have hmax := (maximalIdeal.isMaximal R).map_of_surjective_of_ker_le
      (f := Ideal.Quotient.mk (Ideal.span {f})) Ideal.Quotient.mk_surjective
      (by rw [← hc]; exact Ideal.comap_mono bot_le)
    rwa [← hc, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at hmax
  have := (Ring.krullDimLE_iff (n := 0)).mp h0
  have h10 := hdim.trans this
  norm_num at h10

/- English proof (translation)
Introduce `R _ _ _ f hdim A B _ _ _ _ _ ψ ⟨k, hk⟩`. Take `⟨P, hP, hfP, hPm⟩` from `exists_prime_ne_maximalIdeal_of_one_le_ringKrullDim_quot R f hdim`. Take `⟨x, hxk, hxP⟩ : ∃ x ∈ maximalIdeal R ^ k, x ∉ P` from `by by_contra! h`. Establish `hle : maximalIdeal R ≤ P` using `hP.le_of_pow_le h`. Conclude with `hPm (le_antisymm (le_maximalIdeal hP.ne_top) hle)`.

Use `set N : Submodule R B := LinearMap.range ψ.toLinearMap`. Use `set I : Ideal R := Ideal.span {f}`. Set `φ : Module.End R (B ⧸ N)` to `algebraMap R (Module.End R (B ⧸ N)) x`. Establish `hφ : LinearMap.range φ ≤ I • ⊤`. Introduce and unpack `_ ⟨c, rfl⟩`.

Take `⟨b, rfl⟩` from `Submodule.Quotient.mk_surjective N c`. Take `⟨a, c', hac⟩` from `hk x hxk b`. Establish `: φ (Submodule.Quotient.mk b) = f • Submodule.Quotient.mk c'`. Simplify using `only [φ, Module.algebraMap_end_apply, ← Submodule.Quotient.mk_smul, hac]`. Establish `ha0 : Submodule.Quotient.mk (p` using `N) (ψ a) = 0 := (Submodule.Quotient.mk_eq_zero N).mpr ⟨a, rfl⟩`.

Rewrite using `[Submodule.Quotient.mk_add, ha0, zero_add]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem_smul (Ideal.mem_span_singleton_self f) Submodule.mem_top`. Take `⟨p, hmon, -, hcoeff, hzero⟩` from `LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero R φ I hφ`. Use `⟨p.eval x, ?_, ?_⟩` and prove the remaining obligations.

Introduce `h0`. Apply `hxP` to reduce the goal to its premises. Apply `hP.mem_of_pow_mem p.natDegree` to reduce the goal to its premises. Establish `hs : p.eval x ∈ P` using `h0 ▸ P.zero_mem`. Rewrite `hs` using `[Polynomial.eval_eq_sum_range, Finset.sum_range_succ, hmon.coeff_natDegree, one_mul]`.

Use `(P.add_mem_iff_right ?_).mp hs` and prove the remaining obligations. Use `P.sum_mem fun i hi => P.mul_mem_right _ ?_` and prove the remaining obligations. Establish `hi' : 0 < p.natDegree - i` using `Nat.sub_pos_of_lt (Finset.mem_range.mp hi)`. Establish `hIP : I ≤ P` using `(Ideal.span_singleton_le_iff_mem P).mpr hfP`. Conclude with `hIP (Ideal.pow_le_self hi'.ne' (hcoeff i))`.

Introduce `b`. Establish `h1 : (Polynomial.aeval φ p) (Submodule.Quotient.mk b) = 0` using `by rw [hzero]; rfl`. Rewrite `h1` using `[show φ = algebraMap R _ x from rfl, Polynomial.aeval_algebraMap_apply, Module.algebraMap_end_apply, Polynomial.aeval_def]`. Express the relevant statement in the definitionally equal form `Polynomial.eval x p • Submodule.Quotient.mk (p := N) b = 0 at h1`. Rewrite `h1` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`.

Take `⟨a, ha⟩` from `h1`. Conclude with `⟨a, ha⟩`.
-/
theorem cokernel_torsion_of_finiteLength_mod : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (f : R), 1 ≤ ringKrullDim (R ⧸ Ideal.span {f}) → ∀ (A B : Type) [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] [Module.Finite R B] (ψ : A →ₐ[R] B), (∃ k : ℕ, ∀ x ∈ maximalIdeal R ^ k, ∀ b : B, ∃ a : A, ∃ c : B, x • b = ψ a + f • c) → ∃ s : R, s ≠ 0 ∧ ∀ b : B, s • b ∈ ψ.range := by
  intro R _ _ _ f hdim A B _ _ _ _ _ ψ ⟨k, hk⟩
  obtain ⟨P, hP, hfP, hPm⟩ := exists_prime_ne_maximalIdeal_of_one_le_ringKrullDim_quot R f hdim

  obtain ⟨x, hxk, hxP⟩ : ∃ x ∈ maximalIdeal R ^ k, x ∉ P := by
    by_contra! h
    have hle : maximalIdeal R ≤ P := hP.le_of_pow_le h
    exact hPm (le_antisymm (le_maximalIdeal hP.ne_top) hle)
  set N : Submodule R B := LinearMap.range ψ.toLinearMap
  set I : Ideal R := Ideal.span {f}
  let φ : Module.End R (B ⧸ N) := algebraMap R (Module.End R (B ⧸ N)) x
  have hφ : LinearMap.range φ ≤ I • ⊤ := by
    rintro _ ⟨c, rfl⟩
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective N c
    obtain ⟨a, c', hac⟩ := hk x hxk b
    have : φ (Submodule.Quotient.mk b) = f • Submodule.Quotient.mk c' := by
      simp only [φ, Module.algebraMap_end_apply, ← Submodule.Quotient.mk_smul, hac]
      have ha0 : Submodule.Quotient.mk (p := N) (ψ a) = 0 := (Submodule.Quotient.mk_eq_zero N).mpr ⟨a, rfl⟩
      rw [Submodule.Quotient.mk_add, ha0, zero_add]
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self f) Submodule.mem_top
  obtain ⟨p, hmon, -, hcoeff, hzero⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero R φ I hφ
  refine ⟨p.eval x, ?_, ?_⟩
  · intro h0
    apply hxP
    apply hP.mem_of_pow_mem p.natDegree
    have hs : p.eval x ∈ P := h0 ▸ P.zero_mem
    rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ, hmon.coeff_natDegree, one_mul] at hs
    refine (P.add_mem_iff_right ?_).mp hs
    refine P.sum_mem fun i hi => P.mul_mem_right _ ?_
    have hi' : 0 < p.natDegree - i := Nat.sub_pos_of_lt (Finset.mem_range.mp hi)
    have hIP : I ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr hfP
    exact hIP (Ideal.pow_le_self hi'.ne' (hcoeff i))
  · intro b
    have h1 : (Polynomial.aeval φ p) (Submodule.Quotient.mk b) = 0 := by rw [hzero]; rfl
    rw [show φ = algebraMap R _ x from rfl, Polynomial.aeval_algebraMap_apply,
      Module.algebraMap_end_apply, Polynomial.aeval_def] at h1
    change Polynomial.eval x p • Submodule.Quotient.mk (p := N) b = 0 at h1
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h1
    obtain ⟨a, ha⟩ := h1
    exact ⟨a, ha⟩

end GlobalTheory
