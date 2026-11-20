import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsStrictDom
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPermWOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemIwUIff
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow

namespace GlobalTheory.CompanionTheory.SatPow

/- English proof (translation)
Introduce `V _ _ _ A hA l v j₀ h`. Set `U : Submodule ℂ V` to `Submodule.span ℂ (Set.range fun i : ℕ => (A ^ (i + j₀)) v)`. Establish `hUl : U ≤ LinearMap.ker l`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`.

Conclude with `LinearMap.mem_ker.mpr (h (i + j₀) (Nat.le_add_left j₀ i))`. Establish `hle : U ≤ U.comap A`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Establish `e : A ((A ^ (i + j₀)) v) = (A ^ ((i + 1) + j₀)) v`.

Rewrite using `[show i + 1 + j₀ = (i + j₀) + 1 by omega, pow_succ', Module.End.mul_apply]`. Use `show A ((A ^ (i + j₀)) v) ∈ U`. Rewrite using `[e]`. Conclude with `Submodule.subset_span ⟨i + 1, rfl⟩`. Establish `hAU : ∀ u ∈ U, A u ∈ U` using `fun u hu => hle hu`.

Set `B : U →ₗ[ℂ] U` to `A.restrict hAU`. Establish `hBi : Function.Injective B`. Introduce `x y hxy`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `hA` to reduce the goal to its premises.

Use `congrArg Subtype.val hxy` as an intermediate fact. Simplify `this` using `[B, LinearMap.restrict_apply]`. Establish `hBs : Function.Surjective B` using `LinearMap.injective_iff_surjective.mp hBi`. Establish `pull : ∀ x : V, A x ∈ U → x ∈ U`. Introduce `x hx`.

Take `⟨u, hu⟩` from `hBs ⟨A x, hx⟩`. Establish `hux : A u = A x` using `congrArg Subtype.val hu`. Rewrite using `[← hA hux]`. Conclude with `u.2`. Establish `key : ∀ k : ℕ, (A ^ (j₀ - k)) v ∈ U`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Establish `e0 : (A ^ (j₀ - 0)) v = (A ^ (0 + j₀)) v` using `by rw [Nat.sub_zero, Nat.zero_add]`. Rewrite using `[e0]`.

Conclude with `Submodule.subset_span ⟨0, rfl⟩`. Consider the case `succ k ih`. Break down `Nat.eq_zero_or_pos (j₀ - k) with h0 | hpos` into its components or cases. Establish `e1 : j₀ - (k + 1) = j₀ - k` using `by omega`. Rewrite using `[e1]`.

Conclude with `ih`. Establish `e : j₀ - k = (j₀ - (k + 1)) + 1` using `by omega`. Establish `e2 : (A ^ (j₀ - k)) v = A ((A ^ (j₀ - (k + 1))) v)`. Rewrite using `[e, pow_succ', Module.End.mul_apply]`. Rewrite `ih` using `[e2]`.

Conclude with `pull _ ih`. Establish `hv : v ∈ U`. Establish `h1` using `key j₀`. Rewrite `h1` using `[Nat.sub_self, pow_zero, Module.End.one_apply]`. Then use the resulting hypothesis. Conclude with `LinearMap.mem_ker.mp (hUl hv)`.
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
