import Development.WeilBound.CoreStatements.MultihomogeneousSquares.AntisymmetryFibreSquares
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.EvalRhoAntisymDeltaNe

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace SquareStatements

/- English proof (translation)
Introduce `hA hAg hIn II hII Ψ _ _ N _ T R hSq B hB c τ a b hab hbj lam`. Establish `hN : 2 ≤ N`. Establish `h1` using `T.j_pos`. Establish `h2` using `T.j_lt`. Use linear arithmetic over natural numbers and integers.

Establish `hjN : T.j ≤ N` using `T.j_lt.le`. Establish `hdim : Top.dimFl Ψ N = antisymDegree Ψ N`. Simplify using `[Top.dimFl, antisymDegree, Nat.choose_two_right]`. Establish `harith : IsArithVar (PFl Ψ N) (Top.dimFl Ψ N + 1)` using `hdim ▸ (GlobalTheory.T.flag_variety_boundary_dimension_drop Ψ N hN).1`. Take `⟨m, d, S', K, _, ι, _, P, Re', hm, ⟨F⟩, hPB, hdeg⟩` from `hSq B c`.

Take `⟨⟨c₀, hc₀, hfl⟩, hprop⟩` from `GlobalTheory.T.proportional' hIn Ψ N T.j hN hjN`. Take `⟨-, hv⟩` from `hprop (d + 1) S' F.dim F.unif`. Establish `hnpos : 0 < R.n c` using `(GlobalTheory.T.real_tower_arith_agreement hIn II hII Ψ N (T.M B c) (R.Sys c) (R.n c) (R.tie B c) lam 0).1`. Establish `hn0 : (R.n c : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 hnpos.ne'`. Establish `hvol : m * ((R.n c : ℝ) * T.vol c) = PB.volOf S'`.

Establish `h1` using `GlobalTheory.T.real_tower_geometric_agreement hIn II hII Ψ N (T.M 2 c) (R.Sys c) (R.n c) (R.tie 2 c) (rhoWt : Wt Ψ N) 0`. Establish `h2` using `GlobalTheory.T.flag_degree_polynomial_eval hIn II hII Ψ N (rhoWt : Wt Ψ N) hN`. Establish `hρ : flagDeg (rhoWt : Wt Ψ N) ≠ 0`. Rewrite using `[← h2, hfl, eval_mul, eval_C]`. Conclude with `mul_ne_zero hc₀.ne' eval_rho_antisymDelta_ne`.

Establish `h3 : m * eval (PB.gapS (fun x : Ψ × Fin N => (rhoWt : Wt Ψ N) x.1 x.2) (0 / ((T.M 2 c).kA : ℝ))) (R.Sys c).degPoly = PB.volOf S' * flagDeg (rhoWt : Wt Ψ N)`. Rewrite using `[zero_div]`. Establish `e : PB.gapS (fun x : Ψ × Fin N => (rhoWt : Wt Ψ N) x.1 x.2) 0 = fun o => o.elim 0 (PB.gap fun x : Ψ × Fin N => (rhoWt : Wt Ψ N) x.1 x.2)` using `rfl`. Rewrite using `[e, AnSys_degPoly_gapS_zero, ← smul_eval, ← hdeg, ← PB.eval_toWt_gap, hv, eval_mul, eval_C, h2]`. Rewrite `h1` using `[linA_zero_pow]`.

Unfold `RootTower.vol`. Rewrite using `[← mul_div_assoc, h1, ← mul_div_assoc, h3, mul_div_cancel_right₀ _ hρ]`. Establish `hpos : 0 < (R.Sys c).t₀` using `((R.Sys c).reg none).1`. Establish `hconv : ∀ w, Tendsto (fun t => (R.tie B c).Re.num II t w) (𝓝[>] 0) (𝓝 ((R.tie B c).Re.limNum II w))`. Take `⟨C₃, s₀, -, h⟩` from `hAg hIn (Top.dimFl Ψ N) (Option (Ψ × Fin N)) (R.Sys c) 0 hpos`.

Conclude with `(h II hII _ _ _ (R.tie B c).Re).1`. Establish `hnum : ∀ mu : Wt Ψ N, m * ((R.n c : ℝ) * T.PPc II B c (linRoot mu ^ (Top.dimFl Ψ N + 1))) = eval (fun x : Ψ × Fin N => mu x.1 x.2) (PB.toWt (Re'.PB II))`. Introduce `mu`. Establish `h1` using `((GlobalTheory.T.real_tower_arith_agreement hIn II hII Ψ N (T.M B c) (R.Sys c) (R.n c) (R.tie B c) mu 0).2.2 hconv hpos).2`. Rewrite `h1` using `[zero_div, linA_zero_pow]`.

Establish `e : PB.gapS (fun x : Ψ × Fin N => mu x.1 x.2) 0 = fun o => o.elim 0 (PB.gap fun x : Ψ × Fin N => mu x.1 x.2)` using `rfl`. Rewrite `h1` using `[e, Realis_PB_gapS_zero, ← PB.eval_toWt_gap]`. Rewrite using `[hPB, smul_eval]`. Conclude with `congrArg (m * ·) h1`. Establish `hh : ∀ mu : Wt Ψ N, hhFl Ψ N II (linRoot mu ^ (Top.dimFl Ψ N + 1)) = eval (fun x : Ψ × Fin N => mu x.1 x.2) (PB.hFlPoly Ψ N II)` using `fun mu => GlobalTheory.T.flag_height_polynomial_eval II hII Ψ N mu hN harith`.

Establish `hQ` using `(hA hIn II hII Ψ N T.j d hN S' K ι P Re' F).2 (Equiv.swap (τ, a) (τ, b)) ⟨τ, a, b, hab, by omega, rfl⟩`. Establish `hE` using `congrArg (eval fun x : Ψ × Fin N => lam x.1 x.2) hQ`. Rewrite `hE` using `[eval_rename, ← swapWt_uncurry]`. Simplify using `only [map_sub, map_neg, smul_eval] at hE`. Rewrite `hE` using `[← hnum, ← hnum, ← hh, ← hh, ← hvol]`.

Apply `mul_left_cancel₀ (mul_ne_zero hm.ne' hn0)` to reduce the goal to its premises. Take the linear combination `hE`.
-/
theorem antisymmetry_transposition_factor : AntisymmetryFibreSquares := by
  intro hA hAg hIn II hII Ψ _ _ N _ T R hSq B hB c τ a b hab hbj lam
  have hN : 2 ≤ N := by
    have h1 := T.j_pos
    have h2 := T.j_lt
    omega
  have hjN : T.j ≤ N := T.j_lt.le
  have hdim : Top.dimFl Ψ N = antisymDegree Ψ N := by
    simp [Top.dimFl, antisymDegree, Nat.choose_two_right]
  have harith : IsArithVar (PFl Ψ N) (Top.dimFl Ψ N + 1) := hdim ▸ (GlobalTheory.T.flag_variety_boundary_dimension_drop Ψ N hN).1
  obtain ⟨m, d, S', K, _, ι, _, P, Re', hm, ⟨F⟩, hPB, hdeg⟩ := hSq B c
  obtain ⟨⟨c₀, hc₀, hfl⟩, hprop⟩ := GlobalTheory.T.proportional' hIn Ψ N T.j hN hjN
  obtain ⟨-, hv⟩ := hprop (d + 1) S' F.dim F.unif
  have hnpos : 0 < R.n c := (GlobalTheory.T.real_tower_arith_agreement hIn II hII Ψ N (T.M B c) (R.Sys c) (R.n c) (R.tie B c) lam 0).1
  have hn0 : (R.n c : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hnpos.ne'

  have hvol : m * ((R.n c : ℝ) * T.vol c) = PB.volOf S' := by
    have h1 := GlobalTheory.T.real_tower_geometric_agreement hIn II hII Ψ N (T.M 2 c) (R.Sys c) (R.n c) (R.tie 2 c) (rhoWt : Wt Ψ N) 0
    have h2 := GlobalTheory.T.flag_degree_polynomial_eval hIn II hII Ψ N (rhoWt : Wt Ψ N) hN
    have hρ : flagDeg (rhoWt : Wt Ψ N) ≠ 0 := by
      rw [← h2, hfl, eval_mul, eval_C]
      exact mul_ne_zero hc₀.ne' eval_rho_antisymDelta_ne
    have h3 : m * eval (PB.gapS (fun x : Ψ × Fin N => (rhoWt : Wt Ψ N) x.1 x.2) (0 / ((T.M 2 c).kA : ℝ))) (R.Sys c).degPoly =
        PB.volOf S' * flagDeg (rhoWt : Wt Ψ N) := by
      rw [zero_div]
      have e : PB.gapS (fun x : Ψ × Fin N => (rhoWt : Wt Ψ N) x.1 x.2) 0 =
          fun o => o.elim 0 (PB.gap fun x : Ψ × Fin N => (rhoWt : Wt Ψ N) x.1 x.2) := rfl
      rw [e, AnSys_degPoly_gapS_zero, ← smul_eval, ← hdeg, ← PB.eval_toWt_gap, hv, eval_mul, eval_C, h2]
    rw [linA_zero_pow] at h1
    unfold RootTower.vol
    rw [← mul_div_assoc, h1, ← mul_div_assoc, h3, mul_div_cancel_right₀ _ hρ]

  have hpos : 0 < (R.Sys c).t₀ := ((R.Sys c).reg none).1
  have hconv : ∀ w, Tendsto (fun t => (R.tie B c).Re.num II t w) (𝓝[>] 0) (𝓝 ((R.tie B c).Re.limNum II w)) := by
    obtain ⟨C₃, s₀, -, h⟩ := hAg hIn (Top.dimFl Ψ N) (Option (Ψ × Fin N)) (R.Sys c) 0 hpos
    exact (h II hII _ _ _ (R.tie B c).Re).1
  have hnum : ∀ mu : Wt Ψ N, m * ((R.n c : ℝ) * T.PPc II B c (linRoot mu ^ (Top.dimFl Ψ N + 1))) =
      eval (fun x : Ψ × Fin N => mu x.1 x.2) (PB.toWt (Re'.PB II)) := by
    intro mu
    have h1 := ((GlobalTheory.T.real_tower_arith_agreement hIn II hII Ψ N (T.M B c) (R.Sys c) (R.n c) (R.tie B c) mu 0).2.2 hconv hpos).2
    rw [zero_div, linA_zero_pow] at h1
    have e : PB.gapS (fun x : Ψ × Fin N => mu x.1 x.2) 0 =
        fun o => o.elim 0 (PB.gap fun x : Ψ × Fin N => mu x.1 x.2) := rfl
    rw [e, Realis_PB_gapS_zero, ← PB.eval_toWt_gap] at h1
    rw [hPB, smul_eval]
    exact congrArg (m * ·) h1
  have hh : ∀ mu : Wt Ψ N, hhFl Ψ N II (linRoot mu ^ (Top.dimFl Ψ N + 1)) =
      eval (fun x : Ψ × Fin N => mu x.1 x.2) (PB.hFlPoly Ψ N II) :=
    fun mu => GlobalTheory.T.flag_height_polynomial_eval II hII Ψ N mu hN harith

  have hQ := (hA hIn II hII Ψ N T.j d hN S' K ι P Re' F).2 (Equiv.swap (τ, a) (τ, b))
    ⟨τ, a, b, hab, by omega, rfl⟩
  have hE := congrArg (eval fun x : Ψ × Fin N => lam x.1 x.2) hQ
  rw [eval_rename, ← swapWt_uncurry] at hE
  simp only [map_sub, map_neg, smul_eval] at hE
  rw [← hnum, ← hnum, ← hh, ← hh, ← hvol] at hE
  apply mul_left_cancel₀ (mul_ne_zero hm.ne' hn0)
  linear_combination hE

end SquareStatements
