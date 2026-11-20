import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

/- English proof (translation)
Establish `hv : Module.End.HasEigenvector (Matrix.toLin' M) μ x` using `⟨Module.End.mem_eigenspace_iff.2 (by rw [Matrix.toLin'_apply]; exact hM), hx⟩`. Establish `h1` using `Module.End.aeval_apply_of_hasEigenvector hv (p := q)`. Establish `h2 : Polynomial.aeval (Matrix.toLin' M) q = Matrix.toLin' (Polynomial.aeval M q)`. Conclude with `Polynomial.aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin n)).toAlgHom M q`. Rewrite `h1` using `[h2, hq, map_zero, LinearMap.zero_apply]`.

Conclude with `(smul_eq_zero.1 h1.symm).resolve_right hx`.
-/
theorem eval_eq_zero_of_eigenvector {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) (μ : ℂ) (hx : x ≠ 0)
    (hM : M *ᵥ x = μ • x) (q : Polynomial ℂ) (hq : Polynomial.aeval M q = 0) : q.eval μ = 0 := by
  have hv : Module.End.HasEigenvector (Matrix.toLin' M) μ x :=
    ⟨Module.End.mem_eigenspace_iff.2 (by rw [Matrix.toLin'_apply]; exact hM), hx⟩
  have h1 := Module.End.aeval_apply_of_hasEigenvector hv (p := q)
  have h2 : Polynomial.aeval (Matrix.toLin' M) q = Matrix.toLin' (Polynomial.aeval M q) := by
    exact Polynomial.aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin n)).toAlgHom M q
  rw [h2, hq, map_zero, LinearMap.zero_apply] at h1
  exact (smul_eq_zero.1 h1.symm).resolve_right hx

/- English proof (translation)
Introduce `p _ G P μ ha hm v hv`. Take `⟨v₀, hv₀, x, hx, hpos⟩` from `hm`. Establish `hvv : v = v₀`. Unfold `HTGroup.a at ha`. Take `⟨w, hw⟩` from `Fintype.card_eq_one_iff.1 ha`.

Establish `e1` using `hw ⟨v, hv⟩`. Establish `e2` using `hw ⟨v₀, hv₀⟩`. Conclude with `congrArg Subtype.val (e1.trans e2.symm)`. Substitute `hvv` using the available equality. Establish `hx0 : x ≠ 0`.

Introduce and unpack `rfl`. Simplify using `at hpos`. Establish `hq : Polynomial.aeval (G.psi v (P.γ : G.C)) (P.pol.map v.embedding) = 0`. Establish `h0 : G.psi v (Polynomial.aeval (P.γ : G.C) P.pol) = 0`. Rewrite using `[Pair.pol, minpoly.aeval, map_zero]`.

Rewrite using `[Polynomial.aeval_def, Polynomial.eval₂_map]`. Rewrite `h0` using `[Polynomial.aeval_def, Polynomial.hom_eval₂]`. Establish `e : (algebraMap ℂ (Matrix (Fin G.n) (Fin G.n) ℂ)).comp v.embedding = (G.psi v).comp (algebraMap G.F G.C)`. Apply `RingHom.ext` to reduce the goal to its premises. Introduce `a`.

Simplify using `only [RingHom.comp_apply, G.psi_F, Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `h0`. Use `eval_eq_zero_of_eigenvector _ x μ hx0 hx _ hq` as an intermediate fact.

Rewrite `this` using `[Polynomial.eval_map]`. Then use the resulting hypothesis.
-/
theorem mark_isRoot_pol : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ : ℂ), G.a = 1 → P.Mark μ →
    ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → P.pol.eval₂ v.embedding μ = 0 := by
  intro p _ G P μ ha hm v hv
  obtain ⟨v₀, hv₀, x, hx, hpos⟩ := hm
  have hvv : v = v₀ := by
    unfold HTGroup.a at ha
    obtain ⟨w, hw⟩ := Fintype.card_eq_one_iff.1 ha
    have e1 := hw ⟨v, hv⟩
    have e2 := hw ⟨v₀, hv₀⟩
    exact congrArg Subtype.val (e1.trans e2.symm)
  subst hvv
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hpos
  have hq : Polynomial.aeval (G.psi v (P.γ : G.C)) (P.pol.map v.embedding) = 0 := by
    have h0 : G.psi v (Polynomial.aeval (P.γ : G.C) P.pol) = 0 := by
      rw [Pair.pol, minpoly.aeval, map_zero]
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂] at h0
    have e : (algebraMap ℂ (Matrix (Fin G.n) (Fin G.n) ℂ)).comp v.embedding = (G.psi v).comp (algebraMap G.F G.C) := by
      apply RingHom.ext
      intro a
      simp only [RingHom.comp_apply, G.psi_F, Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
      rfl
    rw [e]
    exact h0
  have := eval_eq_zero_of_eigenvector _ x μ hx0 hx _ hq
  rwa [Polynomial.eval_map] at this

end GlobalTheory.LKMid
