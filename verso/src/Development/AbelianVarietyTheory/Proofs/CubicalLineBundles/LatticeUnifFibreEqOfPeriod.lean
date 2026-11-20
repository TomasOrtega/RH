import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HolomorphicUniformisationTangentUnimodularRiemanStatement
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory

/- English proof (translation)
Introduce `hU R _ P v s L c₀ ω hg hv H hc hL P' φ hφ u`. Take `⟨v', hv', -⟩` from `existsUnique_isVecOver hφ.2.1.1 v`. Establish `htan : IsTangent v'` using `IsVecOver.isTangent hφ.2.1 hv' hv`. Take `⟨w, hw, -⟩` from `(GlobalTheory.T.holomorphicUniformisation_tangent_unimodular_riemannForm hU P' u).1 v' htan`. Take `⟨hw0, hwL⟩` from `H P' φ v' u w hφ hv' hw`.

Establish `hg' : P'.g = 1` using `hφ.1.trans hg`. Establish `i0 : Fin P'.g` using `⟨0, by omega⟩`. Establish `: Subsingleton (Fin P'.g)` using `by rw [hg']; infer_instance`. Establish `hwi : w i0 ≠ 0`. Introduce `h`.

Apply `hw0` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Rewrite using `[Subsingleton.elim i i0, h]`. Both sides reduce to the same expression. Use `⟨c₀ * w i0, mul_ne_zero hc hwi, fun z => ?_⟩` and prove the remaining obligations.

Take `⟨t, ht⟩ : ∃ t, t = z i0 / w i0` from `⟨_, rfl⟩`. Establish `hz : z = t • w`. Use function extensionality and compare the values at `i`. Rewrite using `[Subsingleton.elim i i0, Pi.smul_apply, smul_eq_mul, ht, div_mul_cancel₀ _ hwi]`. Prove the components needed by the constructor for the conclusion.

Introduce `hzm`. Rewrite `hzm` using `[hz]`. Take `⟨m, n, hmn⟩` from `(hL t).1 ((hwL t).2 hzm)`. Use `⟨m, n, ?_⟩` and prove the remaining obligations. Rewrite using `[hz]`.

Use function extensionality and compare the values at `i`. Rewrite using `[Subsingleton.elim i i0, Pi.smul_apply, smul_eq_mul, hmn]`. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `⟨m, n, hmn⟩`. Establish `hzi : z i0 = c₀ * w i0 * (m + n * ω)` using `congrFun hmn i0`.

Establish `htL : t ∈ L.lattice`. Rewrite using `[hL]`. Use `⟨m, n, ?_⟩` and prove the remaining obligations. Rewrite using `[ht, hzi]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[hz]`. Conclude with `(hwL t).1 htL`.
-/
theorem lattice_unif_fibre_eq_of_period : ThetaUnifAV → ∀ (R : Type) [CommRing R] (P : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A) (s : R →+* ℂ) (L : PeriodPair) (c₀ ω : ℂ), P.g = 1 → IsTangent v → (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s P P' φ' → IsVecOver s φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ L.lattice ↔ z • w' ∈ u'.Λ) → c₀ ≠ 0 → (∀ z, z ∈ L.lattice ↔ ∃ m n : ℤ, z = c₀ * (m + n * ω)) → ∀ (P' : Out.PolAV (Sp ℂ)) (φ : P'.A.left ⟶ P.A.left), IsPolFibre s P P' φ → ∀ u : HolUnif P'.A P'.L P'.g, ∃ c : ℂ, c ≠ 0 ∧ ∀ z, z ∈ u.Λ ↔ ∃ m n : ℤ, z = fun _ => c * (m + n * ω) := by
  intro hU R _ P v s L c₀ ω hg hv H hc hL P' φ hφ u
  obtain ⟨v', hv', -⟩ := existsUnique_isVecOver hφ.2.1.1 v
  have htan : IsTangent v' := IsVecOver.isTangent hφ.2.1 hv' hv
  obtain ⟨w, hw, -⟩ := (GlobalTheory.T.holomorphicUniformisation_tangent_unimodular_riemannForm hU P' u).1 v' htan
  obtain ⟨hw0, hwL⟩ := H P' φ v' u w hφ hv' hw

  have hg' : P'.g = 1 := hφ.1.trans hg
  have i0 : Fin P'.g := ⟨0, by omega⟩
  have : Subsingleton (Fin P'.g) := by rw [hg']; infer_instance
  have hwi : w i0 ≠ 0 := by
    intro h
    apply hw0
    funext i
    rw [Subsingleton.elim i i0, h]
    rfl
  refine ⟨c₀ * w i0, mul_ne_zero hc hwi, fun z => ?_⟩
  obtain ⟨t, ht⟩ : ∃ t, t = z i0 / w i0 := ⟨_, rfl⟩
  have hz : z = t • w := by
    funext i
    rw [Subsingleton.elim i i0, Pi.smul_apply, smul_eq_mul, ht, div_mul_cancel₀ _ hwi]
  constructor
  · intro hzm
    rw [hz] at hzm
    obtain ⟨m, n, hmn⟩ := (hL t).1 ((hwL t).2 hzm)
    refine ⟨m, n, ?_⟩
    rw [hz]
    funext i
    rw [Subsingleton.elim i i0, Pi.smul_apply, smul_eq_mul, hmn]
    ring
  · rintro ⟨m, n, hmn⟩
    have hzi : z i0 = c₀ * w i0 * (m + n * ω) := congrFun hmn i0
    have htL : t ∈ L.lattice := by
      rw [hL]
      refine ⟨m, n, ?_⟩
      rw [ht, hzi]
      field_simp
    rw [hz]
    exact (hwL t).1 htL

end GlobalTheory
