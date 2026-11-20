import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
import Development.WeilBound.CoreStatements.FlagImmersions.ShiftPowerSumMul
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ExistsFlagDegreeOnePolys

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

/- English proof (translation)
Rewrite using `[← Fintype.card_subtype]`. Rewrite using `[Fintype.card_congr (show {i : Fin N // (i : ℕ) < j} ≃ Fin j from { toFun := fun x => ⟨x.1, x.2⟩ invFun := fun y => ⟨⟨y.1, lt_of_lt_of_le y.2 hj⟩, y.2⟩ left_inv := fun x => rfl right_inv := fun y => rfl })]`. Conclude with `Fintype.card_fin j`.
-/
private theorem card_lt_lemma {N j : ℕ} (hj : j ≤ N) :
    (Finset.univ.filter fun i : Fin N => (i : ℕ) < j).card = j := by
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (show {i : Fin N // (i : ℕ) < j} ≃ Fin j from
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun y => ⟨⟨y.1, lt_of_lt_of_le y.2 hj⟩, y.2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl })]
  exact Fintype.card_fin j

/- English proof (translation)
Establish `hp : (pkLow j τ 0 : RP Ψ N) = C (j : ℝ)`. Unfold `pkLow`. Simplify using `only [pow_zero, Finset.sum_const, card_lt_lemma hj, nsmul_eq_mul, mul_one]`. Conclude with `(map_natCast C j).symm`. Rewrite using `[hp]`.

Unfold `degFl`. Simplify using `only [coeff_C_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem flag_degree_low_zero {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (j : ℕ) (hj : j ≤ N) (τ : Ψ) (Q : RP Ψ N) :
    degFl (pkLow j τ 0 * Q) = j * degFl Q := by
  have hp : (pkLow j τ 0 : RP Ψ N) = C (j : ℝ) := by
    unfold pkLow
    simp only [pow_zero, Finset.sum_const, card_lt_lemma hj, nsmul_eq_mul, mul_one]
    exact (map_natCast C j).symm
  rw [hp]
  unfold degFl
  simp only [coeff_C_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  ring

/- English proof (translation)
Introduce `II Ψ _ _ N T _ hh frob C rd Lval B₀ A₀ b₀ hP hI9 hF hB hbad hId`. Unfold `RootTower.Proportional at hP`. Unfold `I9 at hI9`. Take `⟨τ⟩` from `‹Nonempty Ψ›`. Take `⟨⟨Q, hQ, hdeg⟩, -⟩` from `testForms_sh_tot Ψ N T.j τ T.j_pos T.j_lt`.

Take `⟨h, hPP, hbd⟩` from `hF`. Establish `hN : 1 ≤ N` using `le_trans T.j_pos T.j_lt.le`. Establish `hQ' : Q.IsHomogeneous (dimFl Ψ N + 1 - 1)` using `by simpa using hQ`. Establish `hid` using `hId τ 1 le_rfl hN Q hQ'`. Establish `hhh : hh (pk τ 1 * Q) = 0` using `hI9.2.2 τ Q hQ`.

Establish `hSh : ∀ σ, Sh T.j σ (pk τ 1 * Q) = if σ = τ then (T.j : ℝ) else 0`. Introduce `σ`. Rewrite using `[(RootFieldNumerics.shift_power_sum_mul Ψ N T.j τ σ 1 Q le_rfl).1]`. Simplify using `[flag_degree_low_zero T.j T.j_lt.le τ Q, hdeg]`. Establish `hTot : ∀ σ, Tot σ (pk τ 1 * Q) = if σ = τ then (N : ℝ) else 0`.

Introduce `σ`. Rewrite using `[(RootFieldNumerics.shift_power_sum_mul Ψ N T.j τ σ 1 Q le_rfl).2]`. Simplify using `[hdeg]`. Establish `hrest : restSum T.j T.bad frob B₀ τ 1 Q = 0`. Simplify using `[restSum, restTerm]`.

Establish `hL : T.PPt II B₀ (pk τ 1 * Q) = ∑ c, h B₀ c τ * T.vol c`. Unfold `RootTower.PPt`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[hPP B₀ (by omega) c τ Q hQ, hdeg, mul_one]`. Rewrite `hid` using `[hL, hhh, hrest]`.

Simplify using `only [hSh, hTot, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true] at hid`. Establish `hvol : 0 < T.volT` using `Finset.sum_pos (fun c _ => hP.1 c) Finset.univ_nonempty`. Establish `hv0 : T.volT ≠ 0` using `hvol.ne'`. Establish `key : (T.j : ℝ) * A₀ + N * b₀ = -(∑ c, h B₀ c τ * T.vol c) / T.volT`. Rewrite using `[hid]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key, abs_div, abs_neg, abs_of_pos hvol, div_le_iff₀ hvol]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Rewrite using `[abs_mul, abs_of_pos (hP.1 c)]`. Use `_ ≤ ∑ c, C * N * bigLam B₀ rd Lval * T.vol c := by`. Use `Finset.sum_le_sum fun c _ => ?_` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_right (hbd B₀ hB hbad c τ) (hP.1 c).le`. Use `_ = C * N * bigLam B₀ rd Lval * T.volT := by`.

Rewrite using `[← Finset.mul_sum]`. Both sides reduce to the same expression.
-/
theorem flat_85_bound : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) [Nonempty Ψ] (hh : RP Ψ N →ₗ[ℝ] ℝ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (C rd Lval : ℝ) (B₀ : ℕ) (A₀ b₀ : ℝ), T.Proportional → I9 (Ψ := Ψ) (N := N) hh → T.PropF II C rd Lval → 128 ≤ B₀ → T.bad.card ≤ B₀ → T.IdentAt II hh frob B₀ A₀ b₀ → |T.j * A₀ + N * b₀| ≤ C * N * bigLam B₀ rd Lval := by
  intro II Ψ _ _ N T _ hh frob C rd Lval B₀ A₀ b₀ hP hI9 hF hB hbad hId
  unfold RootTower.Proportional at hP
  unfold I9 at hI9
  obtain ⟨τ⟩ := ‹Nonempty Ψ›
  obtain ⟨⟨Q, hQ, hdeg⟩, -⟩ := testForms_sh_tot Ψ N T.j τ T.j_pos T.j_lt
  obtain ⟨h, hPP, hbd⟩ := hF
  have hN : 1 ≤ N := le_trans T.j_pos T.j_lt.le
  have hQ' : Q.IsHomogeneous (dimFl Ψ N + 1 - 1) := by simpa using hQ
  have hid := hId τ 1 le_rfl hN Q hQ'
  have hhh : hh (pk τ 1 * Q) = 0 := hI9.2.2 τ Q hQ
  have hSh : ∀ σ, Sh T.j σ (pk τ 1 * Q) = if σ = τ then (T.j : ℝ) else 0 := by
    intro σ
    rw [(RootFieldNumerics.shift_power_sum_mul Ψ N T.j τ σ 1 Q le_rfl).1]
    simp [flag_degree_low_zero T.j T.j_lt.le τ Q, hdeg]
  have hTot : ∀ σ, Tot σ (pk τ 1 * Q) = if σ = τ then (N : ℝ) else 0 := by
    intro σ
    rw [(RootFieldNumerics.shift_power_sum_mul Ψ N T.j τ σ 1 Q le_rfl).2]
    simp [hdeg]
  have hrest : restSum T.j T.bad frob B₀ τ 1 Q = 0 := by
    simp [restSum, restTerm]
  have hL : T.PPt II B₀ (pk τ 1 * Q) = ∑ c, h B₀ c τ * T.vol c := by
    unfold RootTower.PPt
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hPP B₀ (by omega) c τ Q hQ, hdeg, mul_one]
  rw [hL, hhh, hrest] at hid
  simp only [hSh, hTot, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true] at hid
  have hvol : 0 < T.volT := Finset.sum_pos (fun c _ => hP.1 c) Finset.univ_nonempty
  have hv0 : T.volT ≠ 0 := hvol.ne'
  have key : (T.j : ℝ) * A₀ + N * b₀ = -(∑ c, h B₀ c τ * T.vol c) / T.volT := by
    rw [hid]
    field_simp
    ring
  rw [key, abs_div, abs_neg, abs_of_pos hvol, div_le_iff₀ hvol]
  calc |∑ c, h B₀ c τ * T.vol c| ≤ ∑ c, |h B₀ c τ * T.vol c| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ c, |h B₀ c τ| * T.vol c := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [abs_mul, abs_of_pos (hP.1 c)]
    _ ≤ ∑ c, C * N * bigLam B₀ rd Lval * T.vol c := by
        refine Finset.sum_le_sum fun c _ => ?_
        exact mul_le_mul_of_nonneg_right (hbd B₀ hB hbad c τ) (hP.1 c).le
    _ = C * N * bigLam B₀ rd Lval * T.volT := by
        rw [← Finset.mul_sum]
        rfl

end GlobalTheory.CompanionTheory.Ar.Top
