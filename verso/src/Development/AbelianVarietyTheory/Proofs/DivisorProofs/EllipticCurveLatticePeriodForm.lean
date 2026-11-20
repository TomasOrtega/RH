import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsEllipticCurvePolarisedLatticeFamily
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ModularJExpansionAndPolynomialAndIsIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEqLatticeCurve
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeDeterminedByInvariants
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

open scoped UpperHalfPlane

namespace GlobalTheory.CMModel

/- English proof (translation)
Rewrite using `[WeierstrassCurve.j, ← WeierstrassCurve.coe_Δ', mul_comm]`. Conclude with `_root_.Units.mul_inv_cancel_left W.Δ' _`.
-/
theorem j_mul_Δ_eq (F : Type) [Field F] (W : WeierstrassCurve F) [W.IsElliptic] :
    W.j * W.Δ = W.c₄ ^ 3 := by
  rw [WeierstrassCurve.j, ← WeierstrassCurve.coe_Δ', mul_comm]
  exact _root_.Units.mul_inv_cancel_left W.Δ' _

/- English proof (translation)
Establish `him : τ.im ≠ 0`. Introduce `h0`. Establish `h1` using `congrArg Complex.re h`. Simplify using `[pow_two, h0] at h1`. Establish `: (0 : ℝ) < d` using `by exact_mod_cast hd`.

Use polynomial arithmetic with `[sq_nonneg τ.re]`. Break down `lt_or_gt_of_ne him with hn | hp` into its components or cases. Conclude with `⟨⟨-τ, by simpa using hn⟩, Or.inr rfl⟩`. Conclude with `⟨⟨τ, hp⟩, Or.inl rfl⟩`.
-/
theorem exists_upper_of_sq_eq_neg {d : ℕ} {τ : ℂ} (hd : 0 < d) (h : τ ^ 2 = -(d : ℂ)) :
    ∃ τ₀ : ℍ, (τ₀ : ℂ) = τ ∨ (τ₀ : ℂ) = -τ := by
  have him : τ.im ≠ 0 := by
    intro h0
    have h1 := congrArg Complex.re h
    simp [pow_two, h0] at h1
    have : (0 : ℝ) < d := by exact_mod_cast hd
    nlinarith [sq_nonneg τ.re]
  rcases lt_or_gt_of_ne him with hn | hp
  · exact ⟨⟨-τ, by simpa using hn⟩, Or.inr rfl⟩
  · exact ⟨⟨τ, hp⟩, Or.inl rfl⟩

/- English proof (translation)
Establish `hi : _root_.IsIntegral ℤ (modularJ τ₀)` using `isIntegral_modularJ_of_quadratic (a := 1) (b := 0) (c := d) one_ne_zero (by push_cast; rw [h]; ring)`. Conclude with `mem_algebraicClosure_iff.2 (hi.tower_top (A := ℚ)).isAlgebraic`.
-/
theorem modularJ_mem_Qb {d : ℕ} {τ₀ : ℍ} (h : (τ₀ : ℂ) ^ 2 = -(d : ℂ)) :
    modularJ τ₀ ∈ algebraicClosure ℚ ℂ := by
  have hi : _root_.IsIntegral ℤ (modularJ τ₀) :=
    isIntegral_modularJ_of_quadratic (a := 1) (b := 0) (c := d) one_ne_zero (by push_cast; rw [h]; ring)
  exact mem_algebraicClosure_iff.2 (hi.tower_top (A := ℚ)).isAlgebraic

end GlobalTheory.CMModel

/- English proof (translation)
Introduce `d τ hd hτ`. Take `⟨τ₀, hτ₀⟩` from `GlobalTheory.CMModel.exists_upper_of_sq_eq_neg hd hτ`. Apply the tactic sequence `have hτ₀2 : (τ₀ : ℂ) ^ 2 = -(d : ℂ) := by rcases hτ₀ with e | e <;> rw [e] <;> simp [hτ]`. Set `j : Qb` to `⟨GlobalTheory.modularJ τ₀, GlobalTheory.CMModel.modularJ_mem_Qb hτ₀2⟩`. Set `W : WeierstrassCurve Qb` to `WeierstrassCurve.ofJ j`.

Establish `hWj : W.j = j` using `WeierstrassCurve.ofJ_j j`. Establish `hΔ : IsUnit W.Δ` using `(inferInstance : W.IsElliptic).isUnit`. Take `⟨P, v, Lf, ⟨hg, hv, -, hU'⟩, hLf⟩` from `GlobalTheory.exists_polAV_latticeFamily GlobalTheory.thetaUnifAV_all GlobalTheory.polBaseChange_holds Qb W hΔ`. Set `s : Qb →+* ℂ` to `algebraMap Qb ℂ`. Take `⟨P', φ, h⟩` from `GlobalTheory.exists_isPolFibre GlobalTheory.polBaseChange_holds s P`.

Take `⟨v', hv', -⟩` from `GlobalTheory.existsUnique_isVecOver h.2.1.1 v`. Take `⟨rig, hrig⟩` from `P'.rigid`. Take `⟨u, -, -, -, -, -, hd', -⟩` from `GlobalTheory.thetaUnifAV_all P' rig hrig`. Take `⟨w, hw, -⟩` from `hd' v' (hv'.isTangent h.2.1 (hv.1 0))`. Take `⟨hw0, hmem⟩` from `hU' s P' φ v' u w h hv' hw`.

Establish `hj : s W.j = (GlobalTheory.latticeCurve (GlobalTheory.periodPairOfTau τ₀)).j`. Rewrite using `[hWj, GlobalTheory.latticeCurve_j one_ne_zero (GlobalTheory.mem_lattice_periodPairOfTau τ₀)]`. Both sides reduce to the same expression. Establish `e1` using `congrArg s (GlobalTheory.CMModel.j_mul_Δ_eq Qb W)`. Rewrite `e1` using `[map_mul, map_pow, hj, (hLf s).1, (hLf s).2.2]`.

Establish `e2` using `GlobalTheory.CMModel.j_mul_Δ_eq ℂ (GlobalTheory.latticeCurve (GlobalTheory.periodPairOfTau τ₀))`. Rewrite `e2` using `[GlobalTheory.latticeCurve_Δ, GlobalTheory.latticeCurve_c₄]`. Establish `key : (GlobalTheory.periodPairOfTau τ₀).g₂ ^ 3 * ((Lf s).g₂ ^ 3 - 27 * (Lf s).g₃ ^ 2) = (Lf s).g₂ ^ 3 * ((GlobalTheory.periodPairOfTau τ₀).g₂ ^ 3 - 27 * (GlobalTheory.periodPairOfTau τ₀).g₃ ^ 2)`. Take the linear combination `(((GlobalTheory.periodPairOfTau τ₀).g₂ ^ 3 - 27 * (GlobalTheory.periodPairOfTau τ₀).g₃ ^ 2) * e1 - ((Lf s).g₂ ^ 3 - 27 * (Lf s).g₃ ^ 2) * e2) / 1728`. Take `⟨c, hc0, hc⟩` from `(GlobalTheory.lattice_determined_by_invariants (GlobalTheory.periodPairOfTau τ₀) (Lf s)).2 key`.

Consider the cases of `P' with | mk A' isAb' g' sm' L' isLB' rig' sym' amp' kt' => ?_`. Establish `e : g' = 1` using `h.1.trans hg`. Substitute `e` using the available equality. Establish `hw00 : w 0 ≠ 0` using `fun h0 => hw0 (funext fun i => by fin_cases i; exact h0)`. Use `⟨P.A, inferInstance, A', inferInstance, φ, L', u, w 0 * c, P.isAb, hg ▸ P.smoothDim, h.2.1, isLB', mul_ne_zero hw00 hc0, fun z hz => ?_⟩` and prove the remaining obligations.

Establish `hz' : z = (z 0 / w 0) • w` using `funext fun i => by fin_cases i`. Simplify using `[hw00]`. Take `⟨x, hx, hxz⟩` from `(hc _).1 ((hmem (z 0 / w 0)).2 (hz' ▸ hz))`. Take `⟨m, n, rfl⟩` from `(GlobalTheory.mem_lattice_periodPairOfTau τ₀ x).1 hx`. Establish `hz0 : z 0 = w 0 * c * (1 * (m * (τ₀ : ℂ) + n))`.

Rewrite using `[_root_.mul_assoc, ← hxz]`. Clear the denominators using the available nonvanishing facts. Break down `hτ₀ with e | e` into its components or cases. Conclude with `⟨n, m, by rw [hz0, e]; ring⟩`. Conclude with `⟨n, -m, by rw [hz0, e]; push_cast; ring⟩`.
-/
theorem GlobalTheory.CMModel.exists_curve_lattice :
    ∀ (d : ℕ) (τ : ℂ), 0 < d → τ ^ 2 = -(d : ℂ) →
  ∃ (A₀ : Over (Sp Qb)) (_ : GrpObj A₀) (A : Over (Sp ℂ)) (_ : GrpObj A) (p : A.left ⟶ A₀.left) (L : LB A.left)
    (u : HolUnif A L 1) (c : ℂ), IsAbelianScheme A₀ ∧ SmoothOfRelativeDimension 1 A₀.hom ∧
    IsGrpPullback A A₀ (spMap (algebraMap Qb ℂ)) p ∧ L.IsLB ∧ c ≠ 0 ∧ ∀ z ∈ u.Λ, ∃ a b : ℤ, z 0 = c * (a + b * τ) := by
  classical
  intro d τ hd hτ
  obtain ⟨τ₀, hτ₀⟩ := GlobalTheory.CMModel.exists_upper_of_sq_eq_neg hd hτ
  have hτ₀2 : (τ₀ : ℂ) ^ 2 = -(d : ℂ) := by rcases hτ₀ with e | e <;> rw [e] <;> simp [hτ]
  let j : Qb := ⟨GlobalTheory.modularJ τ₀, GlobalTheory.CMModel.modularJ_mem_Qb hτ₀2⟩
  let W : WeierstrassCurve Qb := WeierstrassCurve.ofJ j
  have hWj : W.j = j := WeierstrassCurve.ofJ_j j
  have hΔ : IsUnit W.Δ := (inferInstance : W.IsElliptic).isUnit
  obtain ⟨P, v, Lf, ⟨hg, hv, -, hU'⟩, hLf⟩ :=
    GlobalTheory.exists_polAV_latticeFamily GlobalTheory.thetaUnifAV_all GlobalTheory.polBaseChange_holds Qb W hΔ
  let s : Qb →+* ℂ := algebraMap Qb ℂ
  obtain ⟨P', φ, h⟩ := GlobalTheory.exists_isPolFibre GlobalTheory.polBaseChange_holds s P
  obtain ⟨v', hv', -⟩ := GlobalTheory.existsUnique_isVecOver h.2.1.1 v
  obtain ⟨rig, hrig⟩ := P'.rigid
  obtain ⟨u, -, -, -, -, -, hd', -⟩ := GlobalTheory.thetaUnifAV_all P' rig hrig
  obtain ⟨w, hw, -⟩ := hd' v' (hv'.isTangent h.2.1 (hv.1 0))
  obtain ⟨hw0, hmem⟩ := hU' s P' φ v' u w h hv' hw
  have hj : s W.j = (GlobalTheory.latticeCurve (GlobalTheory.periodPairOfTau τ₀)).j := by
    rw [hWj, GlobalTheory.latticeCurve_j one_ne_zero (GlobalTheory.mem_lattice_periodPairOfTau τ₀)]
    rfl
  have e1 := congrArg s (GlobalTheory.CMModel.j_mul_Δ_eq Qb W)
  rw [map_mul, map_pow, hj, (hLf s).1, (hLf s).2.2] at e1
  have e2 := GlobalTheory.CMModel.j_mul_Δ_eq ℂ (GlobalTheory.latticeCurve (GlobalTheory.periodPairOfTau τ₀))
  rw [GlobalTheory.latticeCurve_Δ, GlobalTheory.latticeCurve_c₄] at e2
  have key : (GlobalTheory.periodPairOfTau τ₀).g₂ ^ 3 * ((Lf s).g₂ ^ 3 - 27 * (Lf s).g₃ ^ 2) =
      (Lf s).g₂ ^ 3 * ((GlobalTheory.periodPairOfTau τ₀).g₂ ^ 3 - 27 * (GlobalTheory.periodPairOfTau τ₀).g₃ ^ 2) := by
    linear_combination (((GlobalTheory.periodPairOfTau τ₀).g₂ ^ 3 - 27 * (GlobalTheory.periodPairOfTau τ₀).g₃ ^ 2) * e1 -
      ((Lf s).g₂ ^ 3 - 27 * (Lf s).g₃ ^ 2) * e2) / 1728
  obtain ⟨c, hc0, hc⟩ := (GlobalTheory.lattice_determined_by_invariants (GlobalTheory.periodPairOfTau τ₀) (Lf s)).2 key
  cases P' with | mk A' isAb' g' sm' L' isLB' rig' sym' amp' kt' => ?_
  have e : g' = 1 := h.1.trans hg
  subst e
  have hw00 : w 0 ≠ 0 := fun h0 => hw0 (funext fun i => by fin_cases i; exact h0)
  refine ⟨P.A, inferInstance, A', inferInstance, φ, L', u, w 0 * c, P.isAb, hg ▸ P.smoothDim, h.2.1,
    isLB', mul_ne_zero hw00 hc0, fun z hz => ?_⟩
  have hz' : z = (z 0 / w 0) • w := funext fun i => by
    fin_cases i
    simp [hw00]
  obtain ⟨x, hx, hxz⟩ := (hc _).1 ((hmem (z 0 / w 0)).2 (hz' ▸ hz))
  obtain ⟨m, n, rfl⟩ := (GlobalTheory.mem_lattice_periodPairOfTau τ₀ x).1 hx
  have hz0 : z 0 = w 0 * c * (1 * (m * (τ₀ : ℂ) + n)) := by
    rw [_root_.mul_assoc, ← hxz]
    field_simp
  rcases hτ₀ with e | e
  · exact ⟨n, m, by rw [hz0, e]; ring⟩
  · exact ⟨n, -m, by rw [hz0, e]; push_cast; ring⟩
