import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Chapter
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeVOperatorRaisesLevelStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormConjugateCoefficientsInvCharStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormCoeffSeqLinearStructureStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankinDirichletSeriesIdentityHeckeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistedLvalueNeZeroEdgeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffEisensteinSeriesTwistedHeckeUHeckeVStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffEisensteinSeriesTwistedQExpansionDoubleStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepletedCuspEigenformHeckeRelationsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankinMeanSquareCuspFormStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankinUnfoldingPeterssonEisensteinLatticeSumStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankinIntegralTendstoAtZeroStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.RankinZero

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, fun x => DirichletCharacter.norm_le_one ξ _⟩`.
-/
lemma ch_bdd {M : ℕ} (ξ : DirichletCharacter ℂ M) : ∃ C : ℝ, ∀ x, ‖ch ξ x‖ ≤ C :=
  ⟨1, fun x => DirichletCharacter.norm_le_one ξ _⟩

/- English proof (translation)
Establish `hl0 : (l : ℂ) ≠ 0` using `by exact_mod_cast hl.ne'`. Establish `hinj : Function.Injective (fun m : ℕ => l * m)` using `fun a c hac => Nat.eq_of_mul_eq_mul_left hl hac`. Establish `hsupp : Function.support (LSeries.term (fun n => conj (Vo l h n) * b n) W) ⊆ Set.range (fun m : ℕ => l * m)`. Introduce `n hn`. Distinguish the cases in `hd : l ∣ n`.

Take `⟨m, rfl⟩` from `hd`. Conclude with `⟨m, rfl⟩`. It suffices to derive a contradiction. Apply `hn` to reduce the goal to its premises. Simplify using `[LSeries.term, Vo, hd]`.

Unfold `LSeries`. Rewrite using `[← hinj.tsum_eq hsupp, ← tsum_mul_left]`. Use `congr 1`. Use function extensionality and compare the values at `m`. Break down `Nat.eq_zero_or_pos m with rfl | hm` into its components or cases.

Simplify using `[LSeries.term]`. Establish `hm0 : m ≠ 0` using `hm.ne'`. Establish `hlm : l * m ≠ 0` using `Nat.mul_ne_zero hl.ne' hm0`. Rewrite using `[LSeries.term_of_ne_zero hlm, LSeries.term_of_ne_zero hm0]`. Establish `hV : Vo l h (l * m) = h m`.

Simplify using `[Vo, Nat.mul_div_cancel_left m hl]`. Rewrite using `[hV, hb m hm0]`. Use `push_cast`. Rewrite using `[natCast_mul_natCast_cpow]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma lseries_Vo (l : ℕ) (hl : 0 < l) (t : ℂ) (h b : ℕ → ℂ) (hb : ∀ n, n ≠ 0 → b (l * n) = t * b n)
    (W : ℂ) :
    LSeries (fun n => conj (Vo l h n) * b n) W = t / (l : ℂ) ^ W * LSeries (fun n => conj (h n) * b n) W := by
  have hl0 : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  have hinj : Function.Injective (fun m : ℕ => l * m) := fun a c hac => Nat.eq_of_mul_eq_mul_left hl hac
  have hsupp : Function.support (LSeries.term (fun n => conj (Vo l h n) * b n) W) ⊆ Set.range (fun m : ℕ => l * m) := by
    intro n hn
    by_cases hd : l ∣ n
    · obtain ⟨m, rfl⟩ := hd
      exact ⟨m, rfl⟩
    · exfalso
      apply hn
      simp [LSeries.term, Vo, hd]
  unfold LSeries
  rw [← hinj.tsum_eq hsupp, ← tsum_mul_left]
  congr 1
  funext m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [LSeries.term]
  · have hm0 : m ≠ 0 := hm.ne'
    have hlm : l * m ≠ 0 := Nat.mul_ne_zero hl.ne' hm0
    rw [LSeries.term_of_ne_zero hlm, LSeries.term_of_ne_zero hm0]
    have hV : Vo l h (l * m) = h m := by
      simp [Vo, Nat.mul_div_cancel_left m hl]
    rw [hV, hb m hm0]
    push_cast
    rw [natCast_mul_natCast_cpow]
    ring

end GlobalTheory.EisM.RankinZero

namespace GlobalTheory.EisM

/- English proof (translation)
Introduce `e N l χ θ ψ φ g ρ c₀ he hN hl hlN hg hρ hφ hφ1 hb`. Use `haveI : Fact l.Prime := ⟨hl⟩`. Establish `hLpos : 0 < N * l` using `Nat.mul_pos hN hl.pos`. Establish `hNL : N ∣ N * l` using `dvd_mul_right N l`. Use `set b := eis e c₀ (ch ψ) (ch θ) with hbdef`.

Use `set h : ℕ → ℂ := fun n => conj (g n) with hhdef`. Use `set Φ := latF (N * l) (fun _ => 1) φ with hΦdef`. Establish `hCFg : CF (2 * e + 1) N (ch χ) g` using `hg.cf`. Establish `hCFh0 : CF (2 * e + 1) N (ch χ⁻¹) h` using `(GlobalTheory.T.cuspForm_conjugate_coefficients_inv_char (2 * e + 1) N χ g).1 hCFg`. Establish `hCFh : CF (2 * e + 1) (N * l) (ch χ⁻¹) h` using `(GlobalTheory.T.modularFormCoeffSeq_linear_structure (2 * e + 1) N (ch χ⁻¹)).2.2.2.2.2 (N * l) h hNL hCFh0`.

Establish `hCFVh : CF (2 * e + 1) (N * l) (ch χ⁻¹) (Vo l h)` using `(GlobalTheory.T.coeffHeckeVOperator_raises_level (2 * e + 1) N l (ch χ⁻¹) h hl.pos).2 hCFh0`. Take `⟨hPolyb, hbbd, -⟩` from `GlobalTheory.T.coeffEisensteinSeriesTwisted_qExpansion_double e c₀ (ch ψ) (ch θ) (RankinZero.ch_bdd ψ) (RankinZero.ch_bdd θ)`. Establish `hΦbd : ∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C`. Use `⟨1, fun x => ?_⟩` and prove the remaining obligations. Simplify using `only [hΦdef, latF]`.

Use `split_ifs`. Simplify using `using DirichletCharacter.norm_le_one φ _`. Simplify using the standard rewrite rules. Establish `hmult : ∀ d : ℤ, IsCoprime d ((N * l : ℕ) : ℤ) → (fun d => ch ψ d * ch θ d) d = ch φ d * ch χ⁻¹ d`. Introduce `d hd`.

Establish `hd' : IsCoprime d ((N : ℤ) * l)` using `by push_cast at hd; exact hd`. Establish `hdN : IsCoprime d (N : ℤ)` using `hd'.of_mul_right_left`. Take `⟨u, v, huv⟩` from `hdN`. Establish `hunit : IsUnit (d : ZMod N)`. Establish `h1` using `congrArg (Int.cast : ℤ → ZMod N) huv`.

Move the coercions through the operations in `at h1`. Rewrite `h1` using `[ZMod.natCast_self, mul_zero, add_zero]`. Conclude with `⟨⟨(d : ZMod N), (u : ZMod N), by rw [mul_comm]; exact h1, h1⟩, rfl⟩`. Establish `hχ : χ (d : ZMod N) ≠ 0` using `(hunit.map χ).ne_zero`. Use `show ch ψ d * ch θ d = ch φ d * ch χ⁻¹ d`.

Rewrite using `[hφ d]`. Simplify using `only [ch, MulChar.mul_apply, MulChar.inv_apply_eq_inv']`. Clear the denominators using the available nonvanishing facts. Establish `hLφ : (fun n : ℕ => φ n) = fun n : ℕ => χ n * ψ n * θ n`. Use function extensionality and compare the values at `n`.

Use `hφ (n : ℤ)` as an intermediate fact. Simplify using `only [ch, Int.cast_natCast, MulChar.mul_apply] at this`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Establish `hψmul : ∀ m n : ℕ, ψ ((m * n : ℕ) : ZMod l) = ψ (m : ZMod l) * ψ (n : ZMod l)`.

Introduce `m n`. Use `push_cast`. Conclude with `map_mul ψ _ _`. Establish `hθmul : ∀ m n : ℕ, θ ((m * n : ℕ) : ZMod N) = θ (m : ZMod N) * θ (n : ZMod N)`. Introduce `m n`.

Use `push_cast`. Conclude with `map_mul θ _ _`. Establish `hnorm : ∀ n : ℕ, ‖χ (n : ZMod N)‖ ≤ 1 ∧ ‖ψ (n : ZMod l)‖ ≤ 1 ∧ ‖θ (n : ZMod N)‖ ≤ 1` using `fun n => ⟨DirichletCharacter.norm_le_one χ _, DirichletCharacter.norm_le_one ψ _, DirichletCharacter.norm_le_one θ _⟩`. Establish `hhecke : ∀ m n : ℕ, 0 < m → 0 < n → g m * g n = ∑ δ ∈ (Nat.gcd m n).divisors, χ (δ : ZMod N) * (δ : ℂ) ^ (2 * e) * g (m * n / δ ^ 2)`. Use `(GlobalTheory.T.depletedCuspEigenform_heckeRelations (2 * e + 1) N χ g (by omega) hN hg).2.2` as an intermediate fact.

Simplify using `using this`. Establish `hsum : ∀ t : ℝ, 0 < t → Summable fun n : ℕ => ‖g n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + t)` using `fun t ht => (GlobalTheory.T.rankin_mean_square_cuspForm (2 * e + 1) N (ch χ) g (by omega) hCFg).2.2.1 t ht`. Establish `hbform : ∀ n, n ≠ 0 → b n = ∑ p ∈ n.divisorsAntidiagonal, ψ (p.1 : ZMod l) * (p.1 : ℂ) ^ (e - 1) * θ (p.2 : ZMod N)`. Introduce `n hn`. Simplify using `[hbdef, eis, ch, hn]`.

Establish `hbl : ∀ n, n ≠ 0 → b (l * n) = θ (l : ZMod N) * b n`. Establish `hψ0 : ∀ x : ℤ, (l : ℤ) ∣ x → ch ψ x = 0`. Introduce `x hx`. Simplify using `only [ch]`. Rewrite using `[(ZMod.intCast_zmod_eq_zero_iff_dvd x l).mpr hx]`.

Conclude with `MulChar.map_zero ψ`. Establish `hθl : ∀ y : ℤ, ch θ ((l : ℤ) * y) = ch θ (l : ℤ) * ch θ y`. Introduce `y`. Simplify using `only [ch]`. Use `push_cast`.

Conclude with `map_mul θ _ _`. Introduce `n hn`. Use `(GlobalTheory.T.coeffEisensteinSeriesTwisted_heckeU_heckeV e l c₀ (ch θ (l : ℤ)) (ch ψ) (ch θ) hl).1 hψ0 hθl n hn` as an intermediate fact. Simplify `this` using `[ch]`. Establish `hI : ∀ s : ℝ, 0 < s → pet (2 * e + 1) ρ (qs h) (fun τ => qs b τ * lat (e + 1) s (N * l) (0, 1) Φ τ * ((τ.im ^ s : ℝ) : ℂ)) = ((Real.Gamma (2 * (e : ℝ) + s) / (4 * π) ^ (2 * (e : ℝ) + s) : ℝ) : ℂ) * (LSeries (fun n => ψ (n : ZMod l) * g n) ((e + 1 : ℝ) + s : ℝ) * LSeries (fun n => …`.

Introduce `s hs`. Rewrite using `[GlobalTheory.T.rankin_unfolding_petersson_eisensteinLatticeSum e (N * l) N χ⁻¹ φ (fun d => ch ψ d * ch θ d) ρ h b s he hs hLpos hNL hρ hφ1 hCFh hb hmult hbbd]`. Establish `hd` using `GlobalTheory.T.rankin_dirichlet_series_identity_hecke e (fun n => χ (n : ZMod N)) (fun n => ψ (n : ZMod l)) (fun n => θ (n : ZMod N)) g s he hs hψmul hθmul hnorm hhecke hsum b hbform`. Establish `hgb : (fun n => conj (h n) * b n) = fun n => g n * b n`. Use function extensionality and compare the values at `n`.

Simplify using `[hhdef]`. Rewrite using `[hgb, hLφ, ← hd.2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hI' : ∀ s : ℝ, 0 < s → pet (2 * e + 1) ρ (qs (Vo l h)) (fun τ => qs b τ * lat (e + 1) s (N * l) (0, 1) Φ τ * ((τ.im ^ s : ℝ) : ℂ)) = θ (l : ZMod N) / (l : ℂ) ^ (((2 * (e : ℝ) + s : ℝ)) : ℂ) * pet (2 * e + 1) ρ (qs h) (fun τ => qs b τ * lat (e + 1) s (N * l) (0, 1) Φ τ * ((τ.im ^ …`. Introduce `s hs`.

Rewrite using `[GlobalTheory.T.rankin_unfolding_petersson_eisensteinLatticeSum e (N * l) N χ⁻¹ φ (fun d => ch ψ d * ch θ d) ρ (Vo l h) b s he hs hLpos hNL hρ hφ1 hCFVh hb hmult hbbd, GlobalTheory.T.rankin_unfolding_petersson_eisensteinLatticeSum e (N * l) N χ⁻¹ φ (fun d => ch ψ d * ch θ d) ρ h …`. Expand and normalize the polynomial expressions, which then agree. Establish `hlim` using `GlobalTheory.T.rankinIntegral_tendsto_at_zero (2 * e + 1) (e + 1) (N * l) (N * l) N χ⁻¹ Φ ρ h b (by omega) (by omega) hLpos hLpos hNL hρ hCFh hPolyb hΦbd`. Establish `hlim'` using `GlobalTheory.T.rankinIntegral_tendsto_at_zero (2 * e + 1) (e + 1) (N * l) (N * l) N χ⁻¹ Φ ρ (Vo l h) b (by omega) (by omega) hLpos hLpos hNL hρ hCFVh hPolyb hΦbd`. Establish `he1 : (1 : ℝ) ≤ e` using `by exact_mod_cast he`.

Take `⟨-, v₁, hv₁, hL₁⟩` from `GlobalTheory.T.odd_chi_and_tendsto_twisted_LSeries_ne_zero_of_prim (2 * e + 1) N l χ ψ g ((e : ℝ) + 1) (odd_two_mul_add_one e) hN hl.pos hg (by push_cast; linarith)`. Take `⟨-, v₂, hv₂, hL₂⟩` from `GlobalTheory.T.odd_chi_and_tendsto_twisted_LSeries_ne_zero_of_prim (2 * e + 1) N N χ θ g (2 * (e : ℝ)) (odd_two_mul_add_one e) hN hN hg (by push_cast; linarith)`. Establish `hΓ : Tendsto (fun s : ℝ => ((Real.Gamma (2 * (e : ℝ) + s) / (4 * π) ^ (2 * (e : ℝ) + s) : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 ((Real.Gamma (2 * (e : ℝ)) / (4 * π) ^ (2 * (e : ℝ)) : ℝ) : ℂ))`. Apply `tendsto_nhdsWithin_of_tendsto_nhds` to reduce the goal to its premises. Establish `hc : ContinuousAt (fun s : ℝ => ((Real.Gamma (2 * (e : ℝ) + s) / (4 * π) ^ (2 * (e : ℝ) + s) : ℝ) : ℂ)) 0`.

Apply `Complex.continuous_ofReal.continuousAt.comp` to reduce the goal to its premises. Apply `ContinuousAt.div` to reduce the goal to its premises. Apply `ContinuousAt.comp (g := Real.Gamma) _ (continuous_const.add continuous_id).continuousAt` to reduce the goal to its premises. Use `(Real.differentiableAt_Gamma fun m hm => ?_).continuousAt` and prove the remaining obligations. Use `m.cast_nonneg (α := ℝ)` as an intermediate fact.

Establish `hm' : 2 * (e : ℝ) + 0 = -(m : ℝ)` using `hm`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `(Real.continuousAt_const_rpow (by positivity)).comp (continuous_const.add continuous_id).continuousAt`. Check the signs of the components of the expression. Simplify using `using hc.tendsto`.

Use `set P : ℂ := ((Real.Gamma (2 * (e : ℝ)) / (4 * π) ^ (2 * (e : ℝ)) : ℝ) : ℂ) * (v₁ * v₂) with hPdef`. Establish `hprod : Tendsto (fun s : ℝ => pet (2 * e + 1) ρ (qs h) (fun τ => qs b τ * lat (e + 1) s (N * l) (0, 1) Φ τ * ((τ.im ^ s : ℝ) : ℂ))) (𝓝[>] 0) (𝓝 P)`. Use `(hΓ.mul (hL₁.mul hL₂)).congr' ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with s hs`. Conclude with `(hI s hs).symm`.

Establish `hP0` using `tendsto_nhds_unique hlim hprod`. Establish `hPne : P ≠ 0`. Establish `hΓpos : 0 < Real.Gamma (2 * (e : ℝ)) / (4 * π) ^ (2 * (e : ℝ))` using `div_pos (Real.Gamma_pos_of_pos (by linarith)) (by positivity)`. Conclude with `mul_ne_zero (Complex.ofReal_ne_zero.mpr hΓpos.ne') (mul_ne_zero hv₁ hv₂)`. Establish `hl0 : (l : ℂ) ≠ 0` using `by exact_mod_cast hl.ne_zero`.

Establish `hcp : Tendsto (fun s : ℝ => θ (l : ZMod N) / (l : ℂ) ^ (((2 * (e : ℝ) + s : ℝ)) : ℂ)) (𝓝[>] 0) (𝓝 (θ (l : ZMod N) / (l : ℂ) ^ (2 * e)))`. Apply `tendsto_nhdsWithin_of_tendsto_nhds` to reduce the goal to its premises. Establish `hc : Continuous (fun s : ℝ => (l : ℂ) ^ (((2 * (e : ℝ) + s : ℝ)) : ℂ))` using `(Complex.continuous_ofReal.comp (continuous_const.add continuous_id)).const_cpow (Or.inl hl0)`. Establish `h0 : (l : ℂ) ^ (((2 * (e : ℝ) + 0 : ℝ)) : ℂ) = (l : ℂ) ^ (2 * e)`. Rewrite using `[show (((2 * (e : ℝ) + 0 : ℝ)) : ℂ) = ((2 * e : ℕ) : ℂ) by push_cast; ring, Complex.cpow_natCast]`.

Establish `h1 : Tendsto (fun s : ℝ => (l : ℂ) ^ (((2 * (e : ℝ) + s : ℝ)) : ℂ)) (𝓝 0) (𝓝 ((l : ℂ) ^ (2 * e)))`. Rewrite using `[← h0]`. Conclude with `hc.tendsto 0`. Conclude with `tendsto_const_nhds.div h1 (pow_ne_zero _ hl0)`. Establish `hlimP : Tendsto (fun s : ℝ => pet (2 * e + 1) ρ (qs h) (fun τ => qs b τ * lat (e + 1) s (N * l) (0, 1) Φ τ * ((τ.im ^ s : ℝ) : ℂ))) (𝓝[>] 0) (𝓝 P)` using `hprod`.

Establish `hprod' : Tendsto (fun s : ℝ => pet (2 * e + 1) ρ (qs (Vo l h)) (fun τ => qs b τ * lat (e + 1) s (N * l) (0, 1) Φ τ * ((τ.im ^ s : ℝ) : ℂ))) (𝓝[>] 0) (𝓝 (θ (l : ZMod N) / (l : ℂ) ^ (2 * e) * P))`. Use `(hcp.mul hlimP).congr' ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with s hs`. Conclude with `(hI' s hs).symm`. Conclude with `⟨P, hPne, hP0, tendsto_nhds_unique hlim' hprod'⟩`.
-/
theorem rankin_values_at_zero : ∀ (e N l : ℕ) (χ θ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l) (φ : DirichletCharacter ℂ (N * l)) (g : ℕ → ℂ) (ρ : ℍ → ℝ) (c₀ : ℂ), 1 ≤ e → 0 < N → l.Prime → ¬ l ∣ N → Prim (2 * e + 1) N χ g → Wt (N * l) ρ → (∀ d : ℤ, ch φ d = ch (θ * χ) d * ch ψ d) → φ ≠ 1 → MF e (N * l) (fun d => ch ψ d * ch θ d) (eis e c₀ (ch ψ) (ch θ)) → ∃ P : ℂ, P ≠ 0 ∧ pet (2 * e + 1) ρ (qs fun n => conj (g n)) (fun τ => qs (eis e c₀ (ch ψ) (ch θ)) τ * lat (e + 1) 0 (N * l) (0, 1) (latF (N * l) (fun _ => 1) φ) τ) = P ∧ pet (2 * e + 1) ρ (qs (Vo l fun n => conj (g n))) (fun τ => qs (eis e c₀ (ch ψ) (ch θ)) τ * lat (e + 1) 0 (N * l) (0, 1) (latF (N * l) (fun _ => 1) φ) τ) = θ l / (l : ℂ) ^ (2 * e) * P := by
  intro e N l χ θ ψ φ g ρ c₀ he hN hl hlN hg hρ hφ hφ1 hb
  haveI : Fact l.Prime := ⟨hl⟩
  have hLpos : 0 < N * l := Nat.mul_pos hN hl.pos
  have hNL : N ∣ N * l := dvd_mul_right N l
  set b := eis e c₀ (ch ψ) (ch θ) with hbdef
  set h : ℕ → ℂ := fun n => conj (g n) with hhdef
  set Φ := latF (N * l) (fun _ => 1) φ with hΦdef
  have hCFg : CF (2 * e + 1) N (ch χ) g := hg.cf
  have hCFh0 : CF (2 * e + 1) N (ch χ⁻¹) h := (GlobalTheory.T.cuspForm_conjugate_coefficients_inv_char (2 * e + 1) N χ g).1 hCFg
  have hCFh : CF (2 * e + 1) (N * l) (ch χ⁻¹) h :=
    (GlobalTheory.T.modularFormCoeffSeq_linear_structure (2 * e + 1) N (ch χ⁻¹)).2.2.2.2.2 (N * l) h hNL hCFh0
  have hCFVh : CF (2 * e + 1) (N * l) (ch χ⁻¹) (Vo l h) :=
    (GlobalTheory.T.coeffHeckeVOperator_raises_level (2 * e + 1) N l (ch χ⁻¹) h hl.pos).2 hCFh0
  obtain ⟨hPolyb, hbbd, -⟩ := GlobalTheory.T.coeffEisensteinSeriesTwisted_qExpansion_double e c₀ (ch ψ) (ch θ) (RankinZero.ch_bdd ψ) (RankinZero.ch_bdd θ)
  have hΦbd : ∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C := by
    refine ⟨1, fun x => ?_⟩
    simp only [hΦdef, latF]
    split_ifs
    · simpa using DirichletCharacter.norm_le_one φ _
    · simp

  have hmult : ∀ d : ℤ, IsCoprime d ((N * l : ℕ) : ℤ) →
      (fun d => ch ψ d * ch θ d) d = ch φ d * ch χ⁻¹ d := by
    intro d hd
    have hd' : IsCoprime d ((N : ℤ) * l) := by push_cast at hd; exact hd
    have hdN : IsCoprime d (N : ℤ) := hd'.of_mul_right_left
    obtain ⟨u, v, huv⟩ := hdN
    have hunit : IsUnit (d : ZMod N) := by
      have h1 := congrArg (Int.cast : ℤ → ZMod N) huv
      push_cast at h1
      rw [ZMod.natCast_self, mul_zero, add_zero] at h1
      exact ⟨⟨(d : ZMod N), (u : ZMod N), by rw [mul_comm]; exact h1, h1⟩, rfl⟩
    have hχ : χ (d : ZMod N) ≠ 0 := (hunit.map χ).ne_zero
    show ch ψ d * ch θ d = ch φ d * ch χ⁻¹ d
    rw [hφ d]
    simp only [ch, MulChar.mul_apply, MulChar.inv_apply_eq_inv']
    field_simp

  have hLφ : (fun n : ℕ => φ n) = fun n : ℕ => χ n * ψ n * θ n := by
    funext n
    have := hφ (n : ℤ)
    simp only [ch, Int.cast_natCast, MulChar.mul_apply] at this
    rw [this]
    ring
  have hψmul : ∀ m n : ℕ, ψ ((m * n : ℕ) : ZMod l) = ψ (m : ZMod l) * ψ (n : ZMod l) := by
    intro m n; push_cast; exact map_mul ψ _ _
  have hθmul : ∀ m n : ℕ, θ ((m * n : ℕ) : ZMod N) = θ (m : ZMod N) * θ (n : ZMod N) := by
    intro m n; push_cast; exact map_mul θ _ _
  have hnorm : ∀ n : ℕ, ‖χ (n : ZMod N)‖ ≤ 1 ∧ ‖ψ (n : ZMod l)‖ ≤ 1 ∧ ‖θ (n : ZMod N)‖ ≤ 1 :=
    fun n => ⟨DirichletCharacter.norm_le_one χ _, DirichletCharacter.norm_le_one ψ _,
      DirichletCharacter.norm_le_one θ _⟩
  have hhecke : ∀ m n : ℕ, 0 < m → 0 < n → g m * g n =
      ∑ δ ∈ (Nat.gcd m n).divisors, χ (δ : ZMod N) * (δ : ℂ) ^ (2 * e) * g (m * n / δ ^ 2) := by
    have := (GlobalTheory.T.depletedCuspEigenform_heckeRelations (2 * e + 1) N χ g (by omega) hN hg).2.2
    simpa using this
  have hsum : ∀ t : ℝ, 0 < t → Summable fun n : ℕ => ‖g n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + t) :=
    fun t ht => (GlobalTheory.T.rankin_mean_square_cuspForm (2 * e + 1) N (ch χ) g (by omega) hCFg).2.2.1 t ht
  have hbform : ∀ n, n ≠ 0 → b n = ∑ p ∈ n.divisorsAntidiagonal,
      ψ (p.1 : ZMod l) * (p.1 : ℂ) ^ (e - 1) * θ (p.2 : ZMod N) := by
    intro n hn
    simp [hbdef, eis, ch, hn]

  have hbl : ∀ n, n ≠ 0 → b (l * n) = θ (l : ZMod N) * b n := by
    have hψ0 : ∀ x : ℤ, (l : ℤ) ∣ x → ch ψ x = 0 := by
      intro x hx
      simp only [ch]
      rw [(ZMod.intCast_zmod_eq_zero_iff_dvd x l).mpr hx]
      exact MulChar.map_zero ψ
    have hθl : ∀ y : ℤ, ch θ ((l : ℤ) * y) = ch θ (l : ℤ) * ch θ y := by
      intro y; simp only [ch]; push_cast; exact map_mul θ _ _
    intro n hn
    have := (GlobalTheory.T.coeffEisensteinSeriesTwisted_heckeU_heckeV e l c₀ (ch θ (l : ℤ)) (ch ψ) (ch θ) hl).1 hψ0 hθl n hn
    simpa [ch] using this

  have hI : ∀ s : ℝ, 0 < s →
      pet (2 * e + 1) ρ (qs h) (fun τ => qs b τ * lat (e + 1) s (N * l) (0, 1) Φ τ * ((τ.im ^ s : ℝ) : ℂ)) =
        ((Real.Gamma (2 * (e : ℝ) + s) / (4 * π) ^ (2 * (e : ℝ) + s) : ℝ) : ℂ) *
          (LSeries (fun n => ψ (n : ZMod l) * g n) ((e + 1 : ℝ) + s : ℝ) *
            LSeries (fun n => θ (n : ZMod N) * g n) ((2 * (e : ℝ) + s : ℝ) : ℂ)) := by
    intro s hs
    rw [GlobalTheory.T.rankin_unfolding_petersson_eisensteinLatticeSum e (N * l) N χ⁻¹ φ (fun d => ch ψ d * ch θ d) ρ h b s he hs hLpos hNL hρ hφ1 hCFh hb hmult hbbd]
    have hd := GlobalTheory.T.rankin_dirichlet_series_identity_hecke e (fun n => χ (n : ZMod N)) (fun n => ψ (n : ZMod l)) (fun n => θ (n : ZMod N)) g s he hs
      hψmul hθmul hnorm hhecke hsum b hbform
    have hgb : (fun n => conj (h n) * b n) = fun n => g n * b n := by
      funext n; simp [hhdef]
    rw [hgb, hLφ, ← hd.2]
    ring

  have hI' : ∀ s : ℝ, 0 < s →
      pet (2 * e + 1) ρ (qs (Vo l h)) (fun τ => qs b τ * lat (e + 1) s (N * l) (0, 1) Φ τ * ((τ.im ^ s : ℝ) : ℂ)) =
        θ (l : ZMod N) / (l : ℂ) ^ (((2 * (e : ℝ) + s : ℝ)) : ℂ) *
          pet (2 * e + 1) ρ (qs h) (fun τ => qs b τ * lat (e + 1) s (N * l) (0, 1) Φ τ * ((τ.im ^ s : ℝ) : ℂ)) := by
    intro s hs
    rw [GlobalTheory.T.rankin_unfolding_petersson_eisensteinLatticeSum e (N * l) N χ⁻¹ φ (fun d => ch ψ d * ch θ d) ρ (Vo l h) b s he hs hLpos hNL hρ hφ1 hCFVh hb hmult hbbd,
      GlobalTheory.T.rankin_unfolding_petersson_eisensteinLatticeSum e (N * l) N χ⁻¹ φ (fun d => ch ψ d * ch θ d) ρ h b s he hs hLpos hNL hρ hφ1 hCFh hb hmult hbbd,
      RankinZero.lseries_Vo l hl.pos _ h b hbl]
    ring

  have hlim := GlobalTheory.T.rankinIntegral_tendsto_at_zero (2 * e + 1) (e + 1) (N * l) (N * l) N χ⁻¹ Φ ρ h b (by omega) (by omega) hLpos hLpos hNL
    hρ hCFh hPolyb hΦbd
  have hlim' := GlobalTheory.T.rankinIntegral_tendsto_at_zero (2 * e + 1) (e + 1) (N * l) (N * l) N χ⁻¹ Φ ρ (Vo l h) b (by omega) (by omega) hLpos hLpos
    hNL hρ hCFVh hPolyb hΦbd
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  obtain ⟨-, v₁, hv₁, hL₁⟩ := GlobalTheory.T.odd_chi_and_tendsto_twisted_LSeries_ne_zero_of_prim (2 * e + 1) N l χ ψ g ((e : ℝ) + 1) (odd_two_mul_add_one e) hN hl.pos hg
    (by push_cast; linarith)
  obtain ⟨-, v₂, hv₂, hL₂⟩ := GlobalTheory.T.odd_chi_and_tendsto_twisted_LSeries_ne_zero_of_prim (2 * e + 1) N N χ θ g (2 * (e : ℝ)) (odd_two_mul_add_one e) hN hN hg
    (by push_cast; linarith)
  have hΓ : Tendsto (fun s : ℝ => ((Real.Gamma (2 * (e : ℝ) + s) / (4 * π) ^ (2 * (e : ℝ) + s) : ℝ) : ℂ)) (𝓝[>] 0)
      (𝓝 ((Real.Gamma (2 * (e : ℝ)) / (4 * π) ^ (2 * (e : ℝ)) : ℝ) : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have hc : ContinuousAt (fun s : ℝ => ((Real.Gamma (2 * (e : ℝ) + s) / (4 * π) ^ (2 * (e : ℝ) + s) : ℝ) : ℂ)) 0 := by
      apply Complex.continuous_ofReal.continuousAt.comp
      apply ContinuousAt.div
      · apply ContinuousAt.comp (g := Real.Gamma) _ (continuous_const.add continuous_id).continuousAt
        refine (Real.differentiableAt_Gamma fun m hm => ?_).continuousAt
        have := m.cast_nonneg (α := ℝ)
        have hm' : 2 * (e : ℝ) + 0 = -(m : ℝ) := hm
        linarith
      · exact (Real.continuousAt_const_rpow (by positivity)).comp (continuous_const.add continuous_id).continuousAt
      · positivity
    simpa using hc.tendsto
  set P : ℂ := ((Real.Gamma (2 * (e : ℝ)) / (4 * π) ^ (2 * (e : ℝ)) : ℝ) : ℂ) * (v₁ * v₂) with hPdef
  have hprod : Tendsto (fun s : ℝ => pet (2 * e + 1) ρ (qs h)
      (fun τ => qs b τ * lat (e + 1) s (N * l) (0, 1) Φ τ * ((τ.im ^ s : ℝ) : ℂ))) (𝓝[>] 0) (𝓝 P) := by
    refine (hΓ.mul (hL₁.mul hL₂)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (hI s hs).symm
  have hP0 := tendsto_nhds_unique hlim hprod
  have hPne : P ≠ 0 := by
    have hΓpos : 0 < Real.Gamma (2 * (e : ℝ)) / (4 * π) ^ (2 * (e : ℝ)) :=
      div_pos (Real.Gamma_pos_of_pos (by linarith)) (by positivity)
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hΓpos.ne') (mul_ne_zero hv₁ hv₂)
  have hl0 : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hcp : Tendsto (fun s : ℝ => θ (l : ZMod N) / (l : ℂ) ^ (((2 * (e : ℝ) + s : ℝ)) : ℂ)) (𝓝[>] 0)
      (𝓝 (θ (l : ZMod N) / (l : ℂ) ^ (2 * e))) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have hc : Continuous (fun s : ℝ => (l : ℂ) ^ (((2 * (e : ℝ) + s : ℝ)) : ℂ)) :=
      (Complex.continuous_ofReal.comp (continuous_const.add continuous_id)).const_cpow (Or.inl hl0)
    have h0 : (l : ℂ) ^ (((2 * (e : ℝ) + 0 : ℝ)) : ℂ) = (l : ℂ) ^ (2 * e) := by
      rw [show (((2 * (e : ℝ) + 0 : ℝ)) : ℂ) = ((2 * e : ℕ) : ℂ) by push_cast; ring, Complex.cpow_natCast]
    have h1 : Tendsto (fun s : ℝ => (l : ℂ) ^ (((2 * (e : ℝ) + s : ℝ)) : ℂ)) (𝓝 0) (𝓝 ((l : ℂ) ^ (2 * e))) := by
      rw [← h0]; exact hc.tendsto 0
    exact tendsto_const_nhds.div h1 (pow_ne_zero _ hl0)
  have hlimP : Tendsto (fun s : ℝ => pet (2 * e + 1) ρ (qs h)
      (fun τ => qs b τ * lat (e + 1) s (N * l) (0, 1) Φ τ * ((τ.im ^ s : ℝ) : ℂ))) (𝓝[>] 0) (𝓝 P) := hprod
  have hprod' : Tendsto (fun s : ℝ => pet (2 * e + 1) ρ (qs (Vo l h))
      (fun τ => qs b τ * lat (e + 1) s (N * l) (0, 1) Φ τ * ((τ.im ^ s : ℝ) : ℂ))) (𝓝[>] 0)
      (𝓝 (θ (l : ZMod N) / (l : ℂ) ^ (2 * e) * P)) := by
    refine (hcp.mul hlimP).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (hI' s hs).symm
  exact ⟨P, hPne, hP0, tendsto_nhds_unique hlim' hprod'⟩

end GlobalTheory.EisM
