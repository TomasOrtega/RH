import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsStrictDom
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPermWOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemIwUIff
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow

namespace GlobalTheory.CompanionTheory.SatPow

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Treat this case separately. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem functional_eq_zero_of_late_iterates :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (A : V →ₗ[ℂ] V), Function.Injective A → ∀ (l : V →ₗ[ℂ] ℂ) (v : V) (j₀ : ℕ), (∀ j ≥ j₀, l ((A ^ j) v) = 0) → l v = 0 := by
  intro V _ _ _ A hA l v j₀ h
  let U : Submodule ℂ V := Submodule.span ℂ (Set.range fun i : ℕ => (A ^ (i + j₀)) v)
  have hUl : U ≤ LinearMap.ker l := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact LinearMap.mem_ker.mpr (h (i + j₀) (Nat.le_add_left j₀ i))
  have hle : U ≤ U.comap A := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    have e : A ((A ^ (i + j₀)) v) = (A ^ ((i + 1) + j₀)) v := by
      rw [show i + 1 + j₀ = (i + j₀) + 1 by omega, pow_succ', Module.End.mul_apply]
    show A ((A ^ (i + j₀)) v) ∈ U
    rw [e]
    exact Submodule.subset_span ⟨i + 1, rfl⟩
  have hAU : ∀ u ∈ U, A u ∈ U := fun u hu => hle hu
  let B : U →ₗ[ℂ] U := A.restrict hAU
  have hBi : Function.Injective B := by
    intro x y hxy
    apply Subtype.ext
    apply hA
    have := congrArg Subtype.val hxy
    simpa [B, LinearMap.restrict_apply] using this
  have hBs : Function.Surjective B := LinearMap.injective_iff_surjective.mp hBi
  have pull : ∀ x : V, A x ∈ U → x ∈ U := by
    intro x hx
    obtain ⟨u, hu⟩ := hBs ⟨A x, hx⟩
    have hux : A u = A x := congrArg Subtype.val hu
    rw [← hA hux]
    exact u.2
  have key : ∀ k : ℕ, (A ^ (j₀ - k)) v ∈ U := by
    intro k
    induction k with
    | zero =>
      have e0 : (A ^ (j₀ - 0)) v = (A ^ (0 + j₀)) v := by rw [Nat.sub_zero, Nat.zero_add]
      rw [e0]
      exact Submodule.subset_span ⟨0, rfl⟩
    | succ k ih =>
      rcases Nat.eq_zero_or_pos (j₀ - k) with h0 | hpos
      · have e1 : j₀ - (k + 1) = j₀ - k := by omega
        rw [e1]
        exact ih
      · have e : j₀ - k = (j₀ - (k + 1)) + 1 := by omega
        have e2 : (A ^ (j₀ - k)) v = A ((A ^ (j₀ - (k + 1))) v) := by
          rw [e, pow_succ', Module.End.mul_apply]
        rw [e2] at ih
        exact pull _ ih
  have hv : v ∈ U := by
    have h1 := key j₀
    rwa [Nat.sub_self, pow_zero, Module.End.one_apply] at h1
  exact LinearMap.mem_ker.mp (hUl hv)

end GlobalTheory.CompanionTheory.SatPow
