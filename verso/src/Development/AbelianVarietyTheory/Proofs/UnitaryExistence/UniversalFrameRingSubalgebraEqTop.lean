import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory

/- English proof (translation)
Introduce `K _ J m R A _ _ _ _ π X s hF A' hπ hX hs hsi hd`. Take `⟨hdet, huniv⟩` from `hF`. Set `ψ : R →ₐ[K] A'` to `π.codRestrict A' hπ`. Set `g : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) A'` to `fun τ => Matrix.of fun i j => ⟨X τ i j, hX τ i j⟩`. Establish `hg : ∀ τ, (g τ).map A'.val = X τ` using `fun τ => by ext i j; rfl`.

Set `a : (A')ˣ` to `⟨⟨s, hs⟩, ⟨_, hsi⟩, Subtype.ext s.mul_inv, Subtype.ext s.inv_mul⟩`. Establish `hgu : ∀ τ, IsUnit (g τ).det`. Introduce `τ`. Take `⟨d, hdA, hd1⟩` from `hd τ`. Use `IsUnit.of_mul_eq_one_right (⟨d, hdA⟩ : A') ?_` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Establish `h1 : A'.val (g τ).det = (X τ).det`. Rewrite using `[← hg τ]`. Conclude with `AlgHom.map_det A'.val (g τ)`. Express the relevant statement in the definitionally equal form `d * A'.val (g τ).det = 1`.

Rewrite using `[h1, hd1]`. Take `⟨k, ⟨hk1, hk2, hk3⟩, -⟩` from `huniv A' ψ g a hgu`. Take `⟨k₀, -, huq⟩` from `huniv A π X s hdet`. Establish `e1 : A'.val.comp k = k₀`. Apply `huq` to reduce the goal to its premises.

Use `⟨?_, fun τ => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[AlgHom.comp_assoc, hk1]`. Use extensionality with `t`. Both sides reduce to the same expression. Rewrite using `[← hg τ, ← hk2 τ] conv_lhs => rw [hk2 τ, hg τ]`.

Use extensionality with `i j`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `A'.val (k s) = s`. Rewrite using `[hk3]`. Both sides reduce to the same expression.

Establish `e2 : AlgHom.id K A = k₀`. Apply `huq` to reduce the goal to its premises. Use `⟨by ext t; rfl, fun τ => by ext i j; rfl, rfl⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff]`. Introduce `x _`.

Establish `: A'.val (k x) = x`. Use `DFunLike.congr_fun (e1.trans e2.symm) x` as an intermediate fact. Simplify using `using this`. Rewrite using `[← this]`. Conclude with `(k x).2`.
-/
theorem frameRing_subalgebra_eq_top : ∀ (K : Type) [Field K] (J : Type) (m : J → ℕ) (R A : Type) [CommRing R] [Algebra K R] [CommRing A] [Algebra K A] (π : R →ₐ[K] A) (X : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) A) (s : Aˣ), FrameRing m π X s → ∀ A' : Subalgebra K A, (∀ t, π t ∈ A') → (∀ τ i j, X τ i j ∈ A') → (s : A) ∈ A' → ((s⁻¹ : Aˣ) : A) ∈ A' → (∀ τ, ∃ d ∈ A', d * (X τ).det = 1) → A' = ⊤ := by
  intro K _ J m R A _ _ _ _ π X s hF A' hπ hX hs hsi hd
  obtain ⟨hdet, huniv⟩ := hF
  let ψ : R →ₐ[K] A' := π.codRestrict A' hπ
  let g : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) A' := fun τ => Matrix.of fun i j => ⟨X τ i j, hX τ i j⟩
  have hg : ∀ τ, (g τ).map A'.val = X τ := fun τ => by ext i j; rfl
  let a : (A')ˣ := ⟨⟨s, hs⟩, ⟨_, hsi⟩, Subtype.ext s.mul_inv, Subtype.ext s.inv_mul⟩
  have hgu : ∀ τ, IsUnit (g τ).det := by
    intro τ
    obtain ⟨d, hdA, hd1⟩ := hd τ
    refine IsUnit.of_mul_eq_one_right (⟨d, hdA⟩ : A') ?_
    apply Subtype.ext
    have h1 : A'.val (g τ).det = (X τ).det := by
      rw [← hg τ]
      exact AlgHom.map_det A'.val (g τ)
    change d * A'.val (g τ).det = 1
    rw [h1, hd1]
  obtain ⟨k, ⟨hk1, hk2, hk3⟩, -⟩ := huniv A' ψ g a hgu
  obtain ⟨k₀, -, huq⟩ := huniv A π X s hdet
  have e1 : A'.val.comp k = k₀ := by
    apply huq
    refine ⟨?_, fun τ => ?_, ?_⟩
    · rw [AlgHom.comp_assoc, hk1]; ext t; rfl
    · rw [← hg τ, ← hk2 τ]
      conv_lhs => rw [hk2 τ, hg τ]
      ext i j; rfl
    · change A'.val (k s) = s
      rw [hk3]; rfl
  have e2 : AlgHom.id K A = k₀ := by
    apply huq
    refine ⟨by ext t; rfl, fun τ => by ext i j; rfl, rfl⟩
  rw [eq_top_iff]
  intro x _
  have : A'.val (k x) = x := by
    have := DFunLike.congr_fun (e1.trans e2.symm) x
    simpa using this
  rw [← this]
  exact (k x).2

end GlobalTheory
