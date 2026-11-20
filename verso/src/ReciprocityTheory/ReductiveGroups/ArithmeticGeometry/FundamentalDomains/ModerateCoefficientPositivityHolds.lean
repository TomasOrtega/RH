import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SliceBounds

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex MajorantConjugateTransfer TwoSidedBoostBounds MinimumGrowthBounds FractionalSliceDomains SliceBounds
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

/- English proof (translation)
Introduce `r X la P C A hP hmod`. Take `⟨ω, hω⟩` from `FlowMeanContinuity.exists_basis X la`. Establish `hωp : ∀ j, ω j ∈ X.periods la`. Introduce `j`. Establish `: ω j ∈ Submodule.span ℤ (Set.range ω)` using `Submodule.subset_span ⟨j, rfl⟩`.

Rewrite `this` using `[hω]`. Conclude with `this`. Establish `hfreq : ∀ (ν : X.Ψ → ℝ) (ξ : Fin r → E) (x : Frame X.Ψ r), ¬ (∀ j, ∃ k : ℤ, 2 * ∑ τ, ν τ * ω j τ = k) → X.fj la ξ ν P x = 0`. Introduce `ν ξ x hj`. Unfold `Data.fj`.

Rewrite using `[if_neg]`. Introduce `hall`. Conclude with `hj fun j => hall _ (hωp j)`. Establish `hsum : ∀ (ν : X.Ψ → ℝ) (k : Fin (Fintype.card X.Ψ) → ℤ), (∀ j, 2 * ∑ τ, ν τ * ω j τ = k j) → ∀ (b : Fin (Fintype.card X.Ψ) → ℝ), ∑ j, (k j : ℝ) * b j = 2 * ∑ τ, ν τ * ∑ j, b j * ω j τ`. Introduce `ν k hk b`.

Simplify using `only [← hk, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hrepr : ∀ (v : X.Ψ → ℝ) τ, ∑ j, ω.repr v j * ω j τ = v τ`.

Introduce `v τ`. Use `conv_rhs => rw [← ω.sum_repr v]`. Simplify using `[Finset.sum_apply, mul_comm]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `ξ hξ ν x hx hne τ0`.

Distinguish the cases in `hf : ∀ j, ∃ k : ℤ, 2 * ∑ τ, ν τ * ω j τ = k`. Use `swap`. Conclude with `absurd (hfreq ν ξ x hf) hne`. Use `choose k hk using hf`. Rewrite `hne` using `[FlowMeanContinuity.fj_eq_fourCoeff X la P hP hξ hx ω hω ν k hk]`.

Express the relevant statement in the definitionally equal form `ReciprocityTheory.L2DbarEstimates.Y.fourCoeff (hfun X P ξ x ω) 0 k ≠ 0 at hne`. Use `set e0 : X.Ψ → ℝ := (Pi.single τ0 (1 : ℝ) : X.Ψ → ℝ) with he0_def`. Use `set κ : Fin (Fintype.card X.Ψ) → ℝ := fun j => ω.repr e0 j with hκ_def`. Establish `hκ : ∀ t : ℝ, ∀ τ, ∑ j, (t * κ j) * ω j τ = t * e0 τ`. Introduce `t τ`.

Rewrite using `[← hrepr e0 τ, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [hκ_def]`. Expand and normalize the polynomial expressions, which then agree. Use `set m : X.Ψ → ℝ := fun τ => X.maj x τ (Data.emb τ.1 ξ)`.

Establish `hm : ∀ τ, 0 < m τ` using `fun τ => X.maj_pos hx τ (emb_ne_zero τ.1 hξ.2.2)`. Establish `hc` using `c_pos X`. Use `set B := Bω X ω`. Establish `hB` using `Bω_nonneg X ω`. Use `set D0 := 1 + X.c τ0 * m τ0`.

Establish `hD0 : 1 ≤ D0` using `by have := hc τ0; have := hm τ0; simp only [D0]; nlinarith`. Use `set K0 := ∑ τ, (1 + X.c τ * B * m τ) ^ 2`. Establish `hK0t : ∀ τ, (1 + X.c τ * B * m τ) ^ 2 ≤ K0` using `fun τ => Finset.single_le_sum (f := fun τ => (1 + X.c τ * B * m τ) ^ 2) (fun τ _ => sq_nonneg _) (Finset.mem_univ τ)`. Establish `hK1 : 1 ≤ K0`. Use `le_trans ?_ (hK0t τ0)` and prove the remaining obligations.

Use `hc τ0` as an intermediate fact. Use `hm τ0` as an intermediate fact. Use polynomial arithmetic with `[mul_nonneg (mul_nonneg (hc τ0).le hB) (hm τ0).le]`. Use `set w := X.spread la τ0`. Establish `hq : ∀ t : ℝ, ∀ τ, 1 + X.c τ * (∑ j, (t * κ j) * ω j τ) * m τ = if τ = τ0 then 1 + X.c τ0 * m τ0 * t else 1`.

Introduce `t τ`. Rewrite using `[hκ]`. Distinguish the cases in `h : τ = τ0`. Substitute `h` using the available equality. Simplify using `[he0_def]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `[he0_def, h]`. Establish `hray : ∀ t : ℝ, 0 ≤ t → (0 : Fin (Fintype.card X.Ψ) → ℝ) + t • κ ∈ Om X ξ x ω`. Introduce `t ht`. Use `show (fun τ => ∑ j, ((0 : Fin (Fintype.card X.Ψ) → ℝ) + t • κ) j * ω j τ) ∈ AdmissibleHermitianColumns.admissibleImaginary X ξ x`.

Rewrite using `[mem_admissibleImaginary_iff X hx hξ]`. Introduce `τ`. Use `hq t τ` as an intermediate fact. Simplify using `only [Pi.add_apply, Pi.zero_apply, zero_add, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[this]`.

Use `split_ifs`. Use `hc τ0` as an intermediate fact. Use `hm τ0` as an intermediate fact. Check the signs of the components of the expression. Evaluate the numerical expressions.

Use `set E' := |A| / 2 + |w| / 2`. Use `set C' := max C 0 * (D0 * K0) ^ (|A| / 2) * D0 ^ (|w| / 2) * X.la1 x ^ (-A) / X.nfac la x`. Establish `hgrow : ∀ t : ℝ, 0 ≤ t → ∀ y : Fin (Fintype.card X.Ψ) → ℝ, ‖hfun X P ξ x ω (fun k => (y k : ℂ) + (((0 : Fin (Fintype.card X.Ψ) → ℝ) + t • κ) k : ℂ) * I)‖ ≤ C' * (1 + t) ^ E'`. Introduce `t ht y`. Establish `hb` using `hray t ht`.

Use `set Z := D0 * K0 * (1 + t)`. Establish `hZ : 1 ≤ Z`. Establish `: 1 ≤ 1 + t` using `by linarith`. Combine the equalities or inequalities in the displayed calculation. Establish `hZ0 : 0 < Z` using `by linarith`.

Establish `hbt : ((0 : Fin (Fintype.card X.Ψ) → ℝ) + t • κ) = fun j => t * κ j`. Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules. Establish `hQ : ∀ τ, 1 ≤ (if τ = τ0 then 1 + X.c τ0 * m τ0 * t else 1) ∧ (if τ = τ0 then 1 + X.c τ0 * m τ0 * t else 1) ≤ D0 * (1 + t)`. Introduce `τ`.

Use `split_ifs`. Use `hc τ0` as an intermediate fact. Use `hm τ0` as an intermediate fact. Prove the components needed by the constructor for the conclusion. Use polynomial arithmetic with `[mul_nonneg (mul_nonneg (hc τ0).le (hm τ0).le) ht]`.

Simplify using `only [D0]`. Use polynomial arithmetic with `[mul_nonneg (mul_nonneg (hc τ0).le (hm τ0).le) ht]`. Prove the components needed by the constructor for the conclusion. Conclude with `le_refl _`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hKρ : ∀ τ (ρ : ℝ), |ρ| ≤ B → (1 + X.c τ * |ρ| * m τ) ^ 2 ≤ K0`. Introduce `τ ρ hρ`. Use `le_trans ?_ (hK0t τ)` and prove the remaining obligations. Establish `h1 : X.c τ * |ρ| * m τ ≤ X.c τ * B * m τ`. Use `hc τ` as an intermediate fact.

Use `hm τ` as an intermediate fact. Conclude with `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hρ (hc τ).le) (hm τ).le`. Establish `h0 : 0 ≤ X.c τ * |ρ| * m τ` using `by have := hc τ; have := hm τ; positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `hsb` using `slice_bound X hx hξ la P hP C A hmod ω hω hb (k1 := Z⁻¹) (k2 := Z) (R := (D0 * (1 + t)) ^ (|w| / 2)) (inv_pos.mpr hZ0) ((inv_le_one_of_one_le₀ hZ).trans hZ) (by`.

Introduce `τ ρ hρ`. Establish `hq' : 1 + X.c τ * (∑ j, ((0 : Fin (Fintype.card X.Ψ) → ℝ) + t • κ) j * ω j τ) * X.maj x τ (Data.emb τ.1 ξ) = if τ = τ0 then 1 + X.c τ0 * m τ0 * t else 1`. Rewrite using `[hbt]`. Conclude with `hq t τ`. Rewrite using `[hq']`.

Take `⟨hQ1, hQ2⟩` from `hQ τ`. Use `set Q := (if τ = τ0 then 1 + X.c τ0 * m τ0 * t else 1)`. Establish `hmin : min Q Q⁻¹ = Q⁻¹` using `min_eq_right (inv_le_one_of_one_le₀ hQ1 |>.trans hQ1)`. Rewrite using `[hmin]`. Establish `hK` using `hKρ τ ρ hρ`.

Establish `hpos : 0 < (1 + X.c τ * |ρ| * m τ) ^ 2`. Use `hc τ` as an intermediate fact. Use `hm τ` as an intermediate fact. Check the signs of the components of the expression. Rewrite using `[le_div_iff₀ hpos]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Z]`. Clear the denominators using the available nonvanishing facts. Use `_ ≤ Q⁻¹ := inv_anti₀ (by linarith) hQ2)`. Use the proof step `(by`.

Introduce `τ ρ hρ`. Establish `hq' : 1 + X.c τ * (∑ j, ((0 : Fin (Fintype.card X.Ψ) → ℝ) + t • κ) j * ω j τ) * X.maj x τ (Data.emb τ.1 ξ) = if τ = τ0 then 1 + X.c τ0 * m τ0 * t else 1`. Rewrite using `[hbt]`. Conclude with `hq t τ`. Rewrite using `[hq']`.

Take `⟨hQ1, hQ2⟩` from `hQ τ`. Use `set Q := (if τ = τ0 then 1 + X.c τ0 * m τ0 * t else 1)`. Establish `hmax : max Q Q⁻¹ = Q` using `max_eq_left (inv_le_one_of_one_le₀ hQ1 |>.trans hQ1)`. Rewrite using `[hmax]`. Establish `hK` using `hKρ τ ρ hρ`.

Combine the equalities or inequalities in the displayed calculation. Use the proof step `(by`. Establish `hq' : ∀ τ, 1 + X.c τ * (∑ j, ((0 : Fin (Fintype.card X.Ψ) → ℝ) + t • κ) j * ω j τ) * X.maj x τ (Data.emb τ.1 ξ) = if τ = τ0 then 1 + X.c τ0 * m τ0 * t else 1`. Introduce `τ`. Rewrite using `[hbt]`.

Conclude with `hq t τ`. Simplify using `only [hq']`. Rewrite using `[Finset.prod_eq_single τ0 (fun τ _ hτ => by simp [hτ]) (fun h => absurd (Finset.mem_univ _) h)]`. Simplify using `only [if_true]`. Take `⟨hQ1, hQ2⟩` from `hQ τ0`.

Simplify using `only [if_true] at hQ1 hQ2`. Rewrite using `[max_eq_left (inv_le_one_of_one_le₀ hQ1 |>.trans hQ1)]`. Combine the equalities or inequalities in the displayed calculation. Establish `hnx` using `nfac_pos X la hx`. Establish `hla0 : 0 ≤ X.la1 x ^ (-A)` using `Real.rpow_nonneg (Real.sqrt_nonneg _) _`.

Establish `hmaxZ : max (Z⁻¹ ^ (-A / 2)) (Z ^ (-A / 2)) ≤ Z ^ (|A| / 2)`. Use `max_le ?_ ?_` and prove the remaining obligations. Rewrite using `[Real.inv_rpow hZ0.le, ← Real.rpow_neg hZ0.le]`. Conclude with `Real.rpow_le_rpow_of_exponent_le hZ (by linarith [le_abs_self A])`. Conclude with `Real.rpow_le_rpow_of_exponent_le hZ (by linarith [neg_abs_le A])`.

Establish `hZsplit : Z ^ (|A| / 2) = (D0 * K0) ^ (|A| / 2) * (1 + t) ^ (|A| / 2)` using `Real.mul_rpow (by nlinarith) (by linarith)`. Establish `hRsplit : (D0 * (1 + t)) ^ (|w| / 2) = D0 ^ (|w| / 2) * (1 + t) ^ (|w| / 2)` using `Real.mul_rpow (by linarith) (by linarith)`. Establish `hE : (1 + t) ^ E' = (1 + t) ^ (|A| / 2) * (1 + t) ^ (|w| / 2)` using `Real.rpow_add (by linarith) _ _`. Establish `hCp : 0 ≤ max C 0` using `le_max_right _ _`. Establish `hRn : 0 ≤ (D0 * (1 + t)) ^ (|w| / 2)` using `Real.rpow_nonneg (mul_nonneg (by linarith) (by linarith)) _`.

Establish `hfinal : ‖hfun X P ξ x ω (fun k => (y k : ℂ) + (((0 : Fin (Fintype.card X.Ψ) → ℝ) + t • κ) k : ℂ) * I)‖ * X.nfac la x ≤ C' * (1 + t) ^ E' * X.nfac la x`. Use `hsb.trans ?_` and prove the remaining obligations. Rewrite using `[hE]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hZsplit, hRsplit]`.

Simplify using `only [C']`. Clear the denominators using the available nonvanishing facts. Conclude with `le_of_mul_le_mul_right hfinal hnx`. Establish `hsign` using `ReciprocityTheory.L2DbarEstimates.Y.four_sign_holds (Fintype.card X.Ψ) (Om X ξ x ω) (hfun X P ξ x ω) 0 κ C' E' (Om_open_conn X ω hx).1 (Om_open_conn X ω hx).2 (hfun_diff X ω P la hP hx hξ) (hfun_periodic X ω P la hP hx hξ hω) hray hgrow k hne`. Rewrite `hsign` using `[hsum ν k hk κ]`.

Establish `h2 : ∑ τ, ν τ * ∑ j, κ j * ω j τ = ν τ0`. Use `fun τ => hκ 1 τ` as an intermediate fact. Simplify using `only [one_mul] at this`. Simplify using `only [this, he0_def, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Rewrite `hsign` using `[h2]`.

Combine the linear equalities and inequalities to obtain the conclusion. Introduce `η hη0 hη1`. Use `set B := Bω X ω`. Establish `hB` using `Bω_nonneg X ω`. Use `set K := (1 + B) ^ 2`.

Establish `hK : 0 < K` using `by positivity`. Use `set Rη := ∏ τ, max η η⁻¹ ^ (X.spread la τ / 2)`. Use `set Cη := max C 0 * max ((η / K) ^ (-A / 2)) ((K / η) ^ (-A / 2)) * Rη`. Establish `hCη : 0 ≤ Cη`. Establish `h1 : 0 ≤ max ((η / K) ^ (-A / 2)) ((K / η) ^ (-A / 2))` using `le_max_of_le_left (Real.rpow_nonneg (by positivity) _)`.

Establish `h2 : 0 ≤ Rη` using `Finset.prod_nonneg fun τ _ => Real.rpow_nonneg (le_max_of_le_left hη0.le) _`. Establish `h3 : 0 ≤ max C 0` using `le_max_right _ _`. Check the signs of the components of the expression. Use `⟨Cη, ?_⟩` and prove the remaining obligations. Introduce `ξ hξ ν x hx hcm`.

Establish `hla0 : 0 ≤ X.la1 x ^ (-A)` using `Real.rpow_nonneg (Real.sqrt_nonneg _) _`. Distinguish the cases in `hf : ∀ j, ∃ k : ℤ, 2 * ∑ τ, ν τ * ω j τ = k`. Use `swap`. Rewrite using `[hfreq ν ξ x hf, norm_zero, zero_mul]`. Conclude with `mul_nonneg (mul_nonneg hCη hla0) (Real.exp_pos _).le`.

Use `choose k hk using hf`. Rewrite using `[FlowMeanContinuity.fj_eq_fourCoeff X la P hP hξ hx ω hω ν k hk]`. Express the relevant statement in the definitionally equal form `‖ReciprocityTheory.L2DbarEstimates.Y.fourCoeff (hfun X P ξ x ω) 0 k‖ * _ ≤ _`. Use `set m : X.Ψ → ℝ := fun τ => X.maj x τ (Data.emb τ.1 ξ)`. Establish `hm : ∀ τ, 0 < m τ` using `fun τ => X.maj_pos hx τ (emb_ne_zero τ.1 hξ.2.2)`.

Establish `hc` using `c_pos X`. Use `set bv : X.Ψ → ℝ := fun τ => -(1 - η) * X.tt ξ x τ`. Use `set b' : Fin (Fintype.card X.Ψ) → ℝ := fun j => ω.repr bv j`. Establish `hb'ω : ∀ τ, ∑ j, b' j * ω j τ = bv τ` using `hrepr bv`. Establish `hqη : ∀ τ, 1 + X.c τ * (∑ j, b' j * ω j τ) * X.maj x τ (Data.emb τ.1 ξ) = η`.

Introduce `τ`. Rewrite using `[hb'ω]`. Simplify using `only [bv, Data.tt]`. Establish `hc'` using `(hc τ).ne'`. Establish `hm' : X.maj x τ (Data.emb τ.1 ξ) ≠ 0` using `(hm τ).ne'`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hb'Ω : b' ∈ Om X ξ x ω` using `by show (fun τ => ∑ j, b' j * ω j τ) ∈ AdmissibleHermitianColumns.admissibleImaginary X ξ x`. Rewrite using `[mem_admissibleImaginary_iff X hx hξ]`. Introduce `τ`.

Rewrite using `[hqη]`. Conclude with `hη0`. Establish `hind` using `ReciprocityTheory.L2DbarEstimates.Y.four_indep (Fintype.card X.Ψ) (Om X ξ x ω) (hfun X P ξ x ω) (Om_open_conn X ω hx).1 (Om_open_conn X ω hx).2 (hfun_diff X ω P la hP hx hξ) (hfun_periodic X ω P la hP hx hξ hω) 0 (zero_mem_Om X ω hx hξ) b' hb'Ω k`. Rewrite using `[hind]`. Establish `hnx` using `nfac_pos X la hx`.

Establish `hmin : min η η⁻¹ = η` using `min_eq_left (hη1.le.trans (one_le_inv₀ hη0 |>.mpr hη1.le))`. Establish `hmax : max η η⁻¹ = η⁻¹` using `max_eq_right (hη1.le.trans (one_le_inv₀ hη0 |>.mpr hη1.le))`. Establish `hKρ : ∀ τ (ρ : ℝ), |ρ| ≤ B → (1 + X.c τ * |ρ| * X.maj x τ (Data.emb τ.1 ξ)) ^ 2 ≤ K`. Introduce `τ ρ hρ`. Establish `h1 : X.c τ * |ρ| * X.maj x τ (Data.emb τ.1 ξ) ≤ B`.

Combine the equalities or inequalities in the displayed calculation. Establish `h0 : 0 ≤ X.c τ * |ρ| * X.maj x τ (Data.emb τ.1 ξ)`. Use `hc τ` as an intermediate fact. Use `hm τ` as an intermediate fact. Simplify using `only [m] at this`.

Check the signs of the components of the expression. Simplify using `only [K]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hslice : ∀ y : Fin (Fintype.card X.Ψ) → ℝ, ‖hfun X P ξ x ω (fun k => (y k : ℂ) + (b' k : ℂ) * I)‖ ≤ Cη * X.la1 x ^ (-A) / X.nfac la x`. Introduce `y`.

Establish `hsb` using `slice_bound X hx hξ la P hP C A hmod ω hω hb'Ω (k1 := η / K) (k2 := K / η) (R := Rη) (by positivity) (by`. Rewrite using `[div_le_div_iff₀ hK hη0]`. Establish `hK1 : 1 ≤ K` using `by simp only [K]; nlinarith [hB]`. Use polynomial arithmetic with `[mul_pos hη0 hη0, mul_pos hK hK, hη1])`. Use the proof step `(by`.

Introduce `τ ρ hρ`. Rewrite using `[hqη, hmin]`. Establish `hpos : 0 < (1 + X.c τ * |ρ| * X.maj x τ (Data.emb τ.1 ξ)) ^ 2`. Use `hc τ` as an intermediate fact. Use `hm τ` as an intermediate fact.

Simplify using `only [m] at this`. Check the signs of the components of the expression. Conclude with `div_le_div_of_nonneg_left hη0.le hpos (hKρ τ ρ hρ))`. Use the proof step `(by`. Introduce `τ ρ hρ`.

Rewrite using `[hqη, hmax, div_eq_inv_mul]`. Conclude with `mul_le_mul_of_nonneg_left (hKρ τ ρ hρ) (inv_nonneg.mpr hη0.le))`. Use the proof step `(by simp only [hqη]; exact le_refl _) y`. Rewrite using `[le_div_iff₀ hnx]`. Conclude with `hsb`.

Establish `hbd` using `ReciprocityTheory.L2DbarEstimates.Y.four_bound (Fintype.card X.Ψ) (hfun X P ξ x ω) b' k _ hslice`. Rewrite `hbd` using `[hsum ν k hk b']`. Establish `hexp : -2 * Real.pi * (2 * ∑ τ, ν τ * ∑ j, b' j * ω j τ) = -(-4 * Real.pi * (1 - η) * ∑ τ, ν τ * X.tt ξ x τ)`. Simplify using `only [hb'ω, bv, Finset.mul_sum]`. Rewrite using `[← Finset.sum_neg_distrib]`.

Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite `hbd` using `[hexp, Real.exp_neg]`. Use `set T := Real.exp (-4 * Real.pi * (1 - η) * ∑ τ, ν τ * X.tt ξ x τ)`. Establish `hT : 0 < T` using `Real.exp_pos _`.

Rewrite `hbd` using `[mul_inv_le_iff₀ hT]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem moderateCoefficientPositivity_holds : ModerateCoefficientPositivity (E := E) := by
  intro r X la P C A hP hmod
  classical
  obtain ⟨ω, hω⟩ := FlowMeanContinuity.exists_basis X la
  have hωp : ∀ j, ω j ∈ X.periods la := by
    intro j
    have : ω j ∈ Submodule.span ℤ (Set.range ω) := Submodule.subset_span ⟨j, rfl⟩
    rw [hω] at this
    exact this
  have hfreq : ∀ (ν : X.Ψ → ℝ) (ξ : Fin r → E) (x : Frame X.Ψ r),
      ¬ (∀ j, ∃ k : ℤ, 2 * ∑ τ, ν τ * ω j τ = k) → X.fj la ξ ν P x = 0 := by
    intro ν ξ x hj
    unfold Data.fj
    rw [if_neg]
    intro hall
    exact hj fun j => hall _ (hωp j)
  have hsum : ∀ (ν : X.Ψ → ℝ) (k : Fin (Fintype.card X.Ψ) → ℤ), (∀ j, 2 * ∑ τ, ν τ * ω j τ = k j) →
      ∀ (b : Fin (Fintype.card X.Ψ) → ℝ), ∑ j, (k j : ℝ) * b j = 2 * ∑ τ, ν τ * ∑ j, b j * ω j τ := by
    intro ν k hk b
    simp only [← hk, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hrepr : ∀ (v : X.Ψ → ℝ) τ, ∑ j, ω.repr v j * ω j τ = v τ := by
    intro v τ
    conv_rhs => rw [← ω.sum_repr v]
    simp [Finset.sum_apply, mul_comm]
  refine ⟨?_, ?_⟩
  ·
    intro ξ hξ ν x hx hne τ0
    by_cases hf : ∀ j, ∃ k : ℤ, 2 * ∑ τ, ν τ * ω j τ = k
    swap
    · exact absurd (hfreq ν ξ x hf) hne
    choose k hk using hf
    rw [FlowMeanContinuity.fj_eq_fourCoeff X la P hP hξ hx ω hω ν k hk] at hne
    change ReciprocityTheory.L2DbarEstimates.Y.fourCoeff (hfun X P ξ x ω) 0 k ≠ 0 at hne
    set e0 : X.Ψ → ℝ := (Pi.single τ0 (1 : ℝ) : X.Ψ → ℝ) with he0_def
    set κ : Fin (Fintype.card X.Ψ) → ℝ := fun j => ω.repr e0 j with hκ_def
    have hκ : ∀ t : ℝ, ∀ τ, ∑ j, (t * κ j) * ω j τ = t * e0 τ := by
      intro t τ
      rw [← hrepr e0 τ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hκ_def]
      ring
    set m : X.Ψ → ℝ := fun τ => X.maj x τ (Data.emb τ.1 ξ)
    have hm : ∀ τ, 0 < m τ := fun τ => X.maj_pos hx τ (emb_ne_zero τ.1 hξ.2.2)
    have hc := c_pos X
    set B := Bω X ω
    have hB := Bω_nonneg X ω
    set D0 := 1 + X.c τ0 * m τ0
    have hD0 : 1 ≤ D0 := by have := hc τ0; have := hm τ0; simp only [D0]; nlinarith
    set K0 := ∑ τ, (1 + X.c τ * B * m τ) ^ 2
    have hK0t : ∀ τ, (1 + X.c τ * B * m τ) ^ 2 ≤ K0 := fun τ =>
      Finset.single_le_sum (f := fun τ => (1 + X.c τ * B * m τ) ^ 2) (fun τ _ => sq_nonneg _)
        (Finset.mem_univ τ)
    have hK1 : 1 ≤ K0 := by
      refine le_trans ?_ (hK0t τ0)
      have := hc τ0; have := hm τ0
      nlinarith [mul_nonneg (mul_nonneg (hc τ0).le hB) (hm τ0).le]
    set w := X.spread la τ0
    have hq : ∀ t : ℝ, ∀ τ, 1 + X.c τ * (∑ j, (t * κ j) * ω j τ) * m τ =
        if τ = τ0 then 1 + X.c τ0 * m τ0 * t else 1 := by
      intro t τ
      rw [hκ]
      by_cases h : τ = τ0
      · subst h; simp [he0_def]; ring
      · simp [he0_def, h]
    have hray : ∀ t : ℝ, 0 ≤ t → (0 : Fin (Fintype.card X.Ψ) → ℝ) + t • κ ∈ Om X ξ x ω := by
      intro t ht
      show (fun τ => ∑ j, ((0 : Fin (Fintype.card X.Ψ) → ℝ) + t • κ) j * ω j τ) ∈ AdmissibleHermitianColumns.admissibleImaginary X ξ x
      rw [mem_admissibleImaginary_iff X hx hξ]
      intro τ
      have := hq t τ
      simp only [Pi.add_apply, Pi.zero_apply, zero_add, Pi.smul_apply, smul_eq_mul]
      rw [this]
      split_ifs
      · have := hc τ0; have := hm τ0; positivity
      · norm_num
    set E' := |A| / 2 + |w| / 2
    set C' := max C 0 * (D0 * K0) ^ (|A| / 2) * D0 ^ (|w| / 2) * X.la1 x ^ (-A) / X.nfac la x
    have hgrow : ∀ t : ℝ, 0 ≤ t → ∀ y : Fin (Fintype.card X.Ψ) → ℝ,
        ‖hfun X P ξ x ω (fun k => (y k : ℂ) + (((0 : Fin (Fintype.card X.Ψ) → ℝ) + t • κ) k : ℂ) * I)‖ ≤
          C' * (1 + t) ^ E' := by
      intro t ht y
      have hb := hray t ht
      set Z := D0 * K0 * (1 + t)
      have hZ : 1 ≤ Z := by
        have : 1 ≤ 1 + t := by linarith
        calc (1 : ℝ) = 1 * 1 * 1 := by ring
          _ ≤ D0 * K0 * (1 + t) := by gcongr
      have hZ0 : 0 < Z := by linarith
      have hbt : ((0 : Fin (Fintype.card X.Ψ) → ℝ) + t • κ) = fun j => t * κ j := by
        funext j; simp
      have hQ : ∀ τ, 1 ≤ (if τ = τ0 then 1 + X.c τ0 * m τ0 * t else 1) ∧
          (if τ = τ0 then 1 + X.c τ0 * m τ0 * t else 1) ≤ D0 * (1 + t) := by
        intro τ
        split_ifs
        · have := hc τ0; have := hm τ0
          constructor
          · nlinarith [mul_nonneg (mul_nonneg (hc τ0).le (hm τ0).le) ht]
          · simp only [D0]; nlinarith [mul_nonneg (mul_nonneg (hc τ0).le (hm τ0).le) ht]
        · constructor
          · exact le_refl _
          · nlinarith
      have hKρ : ∀ τ (ρ : ℝ), |ρ| ≤ B → (1 + X.c τ * |ρ| * m τ) ^ 2 ≤ K0 := by
        intro τ ρ hρ
        refine le_trans ?_ (hK0t τ)
        have h1 : X.c τ * |ρ| * m τ ≤ X.c τ * B * m τ := by
          have := hc τ; have := hm τ
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hρ (hc τ).le) (hm τ).le
        have h0 : 0 ≤ X.c τ * |ρ| * m τ := by have := hc τ; have := hm τ; positivity
        nlinarith
      have hsb := slice_bound X hx hξ la P hP C A hmod ω hω hb (k1 := Z⁻¹) (k2 := Z)
        (R := (D0 * (1 + t)) ^ (|w| / 2)) (inv_pos.mpr hZ0) ((inv_le_one_of_one_le₀ hZ).trans hZ)
        (by
          intro τ ρ hρ
          have hq' : 1 + X.c τ * (∑ j, ((0 : Fin (Fintype.card X.Ψ) → ℝ) + t • κ) j * ω j τ) *
              X.maj x τ (Data.emb τ.1 ξ) = if τ = τ0 then 1 + X.c τ0 * m τ0 * t else 1 := by
            rw [hbt]; exact hq t τ
          rw [hq']
          obtain ⟨hQ1, hQ2⟩ := hQ τ
          set Q := (if τ = τ0 then 1 + X.c τ0 * m τ0 * t else 1)
          have hmin : min Q Q⁻¹ = Q⁻¹ := min_eq_right (inv_le_one_of_one_le₀ hQ1 |>.trans hQ1)
          rw [hmin]
          have hK := hKρ τ ρ hρ
          have hpos : 0 < (1 + X.c τ * |ρ| * m τ) ^ 2 := by
            have := hc τ; have := hm τ; positivity
          rw [le_div_iff₀ hpos]
          calc Z⁻¹ * (1 + X.c τ * |ρ| * m τ) ^ 2 ≤ Z⁻¹ * K0 :=
                mul_le_mul_of_nonneg_left hK (inv_nonneg.mpr hZ0.le)
            _ = (D0 * (1 + t))⁻¹ := by
                simp only [Z]; field_simp
            _ ≤ Q⁻¹ := inv_anti₀ (by linarith) hQ2)
        (by
          intro τ ρ hρ
          have hq' : 1 + X.c τ * (∑ j, ((0 : Fin (Fintype.card X.Ψ) → ℝ) + t • κ) j * ω j τ) *
              X.maj x τ (Data.emb τ.1 ξ) = if τ = τ0 then 1 + X.c τ0 * m τ0 * t else 1 := by
            rw [hbt]; exact hq t τ
          rw [hq']
          obtain ⟨hQ1, hQ2⟩ := hQ τ
          set Q := (if τ = τ0 then 1 + X.c τ0 * m τ0 * t else 1)
          have hmax : max Q Q⁻¹ = Q := max_eq_left (inv_le_one_of_one_le₀ hQ1 |>.trans hQ1)
          rw [hmax]
          have hK := hKρ τ ρ hρ
          calc Q * (1 + X.c τ * |ρ| * m τ) ^ 2 ≤ (D0 * (1 + t)) * K0 :=
                mul_le_mul hQ2 hK (sq_nonneg _) (mul_nonneg (by linarith) (by linarith))
            _ = Z := by simp only [Z]; ring)
        (by
          have hq' : ∀ τ, 1 + X.c τ * (∑ j, ((0 : Fin (Fintype.card X.Ψ) → ℝ) + t • κ) j * ω j τ) *
              X.maj x τ (Data.emb τ.1 ξ) = if τ = τ0 then 1 + X.c τ0 * m τ0 * t else 1 := by
            intro τ; rw [hbt]; exact hq t τ
          simp only [hq']
          rw [Finset.prod_eq_single τ0 (fun τ _ hτ => by simp [hτ]) (fun h => absurd (Finset.mem_univ _) h)]
          simp only [if_true]
          obtain ⟨hQ1, hQ2⟩ := hQ τ0
          simp only [if_true] at hQ1 hQ2
          rw [max_eq_left (inv_le_one_of_one_le₀ hQ1 |>.trans hQ1)]
          calc (1 + X.c τ0 * m τ0 * t) ^ (X.spread la τ0 / 2) ≤ (1 + X.c τ0 * m τ0 * t) ^ (|w| / 2) :=
                Real.rpow_le_rpow_of_exponent_le hQ1 (by simp only [w]; linarith [le_abs_self (X.spread la τ0)])
            _ ≤ (D0 * (1 + t)) ^ (|w| / 2) :=
                Real.rpow_le_rpow (by linarith) hQ2 (by positivity)) y
      have hnx := nfac_pos X la hx
      have hla0 : 0 ≤ X.la1 x ^ (-A) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
      have hmaxZ : max (Z⁻¹ ^ (-A / 2)) (Z ^ (-A / 2)) ≤ Z ^ (|A| / 2) := by
        refine max_le ?_ ?_
        · rw [Real.inv_rpow hZ0.le, ← Real.rpow_neg hZ0.le]
          exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith [le_abs_self A])
        · exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith [neg_abs_le A])
      have hZsplit : Z ^ (|A| / 2) = (D0 * K0) ^ (|A| / 2) * (1 + t) ^ (|A| / 2) :=
        Real.mul_rpow (by nlinarith) (by linarith)
      have hRsplit : (D0 * (1 + t)) ^ (|w| / 2) = D0 ^ (|w| / 2) * (1 + t) ^ (|w| / 2) :=
        Real.mul_rpow (by linarith) (by linarith)
      have hE : (1 + t) ^ E' = (1 + t) ^ (|A| / 2) * (1 + t) ^ (|w| / 2) :=
        Real.rpow_add (by linarith) _ _
      have hCp : 0 ≤ max C 0 := le_max_right _ _
      have hRn : 0 ≤ (D0 * (1 + t)) ^ (|w| / 2) :=
        Real.rpow_nonneg (mul_nonneg (by linarith) (by linarith)) _
      have hfinal : ‖hfun X P ξ x ω (fun k => (y k : ℂ) + (((0 : Fin (Fintype.card X.Ψ) → ℝ) + t • κ) k : ℂ) * I)‖ *
          X.nfac la x ≤ C' * (1 + t) ^ E' * X.nfac la x := by
        refine hsb.trans ?_
        rw [hE]
        calc max C 0 * max (Z⁻¹ ^ (-A / 2)) (Z ^ (-A / 2)) * (D0 * (1 + t)) ^ (|w| / 2) *
              X.la1 x ^ (-A) ≤ max C 0 * Z ^ (|A| / 2) * (D0 * (1 + t)) ^ (|w| / 2) * X.la1 x ^ (-A) := by
              gcongr
          _ = C' * ((1 + t) ^ (|A| / 2) * (1 + t) ^ (|w| / 2)) * X.nfac la x := by
              rw [hZsplit, hRsplit]
              simp only [C']
              field_simp
      exact le_of_mul_le_mul_right hfinal hnx
    have hsign := ReciprocityTheory.L2DbarEstimates.Y.four_sign_holds (Fintype.card X.Ψ) (Om X ξ x ω) (hfun X P ξ x ω) 0 κ C' E'
      (Om_open_conn X ω hx).1 (Om_open_conn X ω hx).2 (hfun_diff X ω P la hP hx hξ)
      (hfun_periodic X ω P la hP hx hξ hω) hray hgrow k hne
    rw [hsum ν k hk κ] at hsign
    have h2 : ∑ τ, ν τ * ∑ j, κ j * ω j τ = ν τ0 := by
      have := fun τ => hκ 1 τ
      simp only [one_mul] at this
      simp only [this, he0_def, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        if_true]
    rw [h2] at hsign
    linarith
  ·
    intro η hη0 hη1
    set B := Bω X ω
    have hB := Bω_nonneg X ω
    set K := (1 + B) ^ 2
    have hK : 0 < K := by positivity
    set Rη := ∏ τ, max η η⁻¹ ^ (X.spread la τ / 2)
    set Cη := max C 0 * max ((η / K) ^ (-A / 2)) ((K / η) ^ (-A / 2)) * Rη
    have hCη : 0 ≤ Cη := by
      have h1 : 0 ≤ max ((η / K) ^ (-A / 2)) ((K / η) ^ (-A / 2)) :=
        le_max_of_le_left (Real.rpow_nonneg (by positivity) _)
      have h2 : 0 ≤ Rη := Finset.prod_nonneg fun τ _ =>
        Real.rpow_nonneg (le_max_of_le_left hη0.le) _
      have h3 : 0 ≤ max C 0 := le_max_right _ _
      positivity
    refine ⟨Cη, ?_⟩
    intro ξ hξ ν x hx hcm
    have hla0 : 0 ≤ X.la1 x ^ (-A) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
    by_cases hf : ∀ j, ∃ k : ℤ, 2 * ∑ τ, ν τ * ω j τ = k
    swap
    · rw [hfreq ν ξ x hf, norm_zero, zero_mul]
      exact mul_nonneg (mul_nonneg hCη hla0) (Real.exp_pos _).le
    choose k hk using hf
    rw [FlowMeanContinuity.fj_eq_fourCoeff X la P hP hξ hx ω hω ν k hk]
    change ‖ReciprocityTheory.L2DbarEstimates.Y.fourCoeff (hfun X P ξ x ω) 0 k‖ * _ ≤ _
    set m : X.Ψ → ℝ := fun τ => X.maj x τ (Data.emb τ.1 ξ)
    have hm : ∀ τ, 0 < m τ := fun τ => X.maj_pos hx τ (emb_ne_zero τ.1 hξ.2.2)
    have hc := c_pos X
    set bv : X.Ψ → ℝ := fun τ => -(1 - η) * X.tt ξ x τ
    set b' : Fin (Fintype.card X.Ψ) → ℝ := fun j => ω.repr bv j
    have hb'ω : ∀ τ, ∑ j, b' j * ω j τ = bv τ := hrepr bv
    have hqη : ∀ τ, 1 + X.c τ * (∑ j, b' j * ω j τ) * X.maj x τ (Data.emb τ.1 ξ) = η := by
      intro τ
      rw [hb'ω]
      simp only [bv, Data.tt]
      have hc' := (hc τ).ne'
      have hm' : X.maj x τ (Data.emb τ.1 ξ) ≠ 0 := (hm τ).ne'
      field_simp
      ring
    have hb'Ω : b' ∈ Om X ξ x ω := by
      show (fun τ => ∑ j, b' j * ω j τ) ∈ AdmissibleHermitianColumns.admissibleImaginary X ξ x
      rw [mem_admissibleImaginary_iff X hx hξ]
      intro τ
      rw [hqη]
      exact hη0
    have hind := ReciprocityTheory.L2DbarEstimates.Y.four_indep (Fintype.card X.Ψ) (Om X ξ x ω) (hfun X P ξ x ω) (Om_open_conn X ω hx).1
      (Om_open_conn X ω hx).2 (hfun_diff X ω P la hP hx hξ) (hfun_periodic X ω P la hP hx hξ hω)
      0 (zero_mem_Om X ω hx hξ) b' hb'Ω k
    rw [hind]
    have hnx := nfac_pos X la hx
    have hmin : min η η⁻¹ = η := min_eq_left (hη1.le.trans (one_le_inv₀ hη0 |>.mpr hη1.le))
    have hmax : max η η⁻¹ = η⁻¹ := max_eq_right (hη1.le.trans (one_le_inv₀ hη0 |>.mpr hη1.le))
    have hKρ : ∀ τ (ρ : ℝ), |ρ| ≤ B → (1 + X.c τ * |ρ| * X.maj x τ (Data.emb τ.1 ξ)) ^ 2 ≤ K := by
      intro τ ρ hρ
      have h1 : X.c τ * |ρ| * X.maj x τ (Data.emb τ.1 ξ) ≤ B := by
        calc X.c τ * |ρ| * X.maj x τ (Data.emb τ.1 ξ) =
            |ρ| * (X.c τ * X.maj x τ (Data.emb τ.1 ξ)) := by ring
          _ ≤ B * 1 := mul_le_mul hρ (hcm τ) (mul_nonneg (hc τ).le (hm τ).le) hB
          _ = B := mul_one B
      have h0 : 0 ≤ X.c τ * |ρ| * X.maj x τ (Data.emb τ.1 ξ) := by
        have := hc τ; have := hm τ; simp only [m] at this; positivity
      simp only [K]
      nlinarith
    have hslice : ∀ y : Fin (Fintype.card X.Ψ) → ℝ, ‖hfun X P ξ x ω (fun k => (y k : ℂ) + (b' k : ℂ) * I)‖ ≤
        Cη * X.la1 x ^ (-A) / X.nfac la x := by
      intro y
      have hsb := slice_bound X hx hξ la P hP C A hmod ω hω hb'Ω (k1 := η / K) (k2 := K / η) (R := Rη)
        (by positivity) (by
          rw [div_le_div_iff₀ hK hη0]
          have hK1 : 1 ≤ K := by simp only [K]; nlinarith [hB]
          nlinarith [mul_pos hη0 hη0, mul_pos hK hK, hη1])
        (by
          intro τ ρ hρ
          rw [hqη, hmin]
          have hpos : 0 < (1 + X.c τ * |ρ| * X.maj x τ (Data.emb τ.1 ξ)) ^ 2 := by
            have := hc τ; have := hm τ; simp only [m] at this; positivity
          exact div_le_div_of_nonneg_left hη0.le hpos (hKρ τ ρ hρ))
        (by
          intro τ ρ hρ
          rw [hqη, hmax, div_eq_inv_mul]
          exact mul_le_mul_of_nonneg_left (hKρ τ ρ hρ) (inv_nonneg.mpr hη0.le))
        (by simp only [hqη]; exact le_refl _) y
      rw [le_div_iff₀ hnx]
      exact hsb
    have hbd := ReciprocityTheory.L2DbarEstimates.Y.four_bound (Fintype.card X.Ψ) (hfun X P ξ x ω) b' k _ hslice
    rw [hsum ν k hk b'] at hbd
    have hexp : -2 * Real.pi * (2 * ∑ τ, ν τ * ∑ j, b' j * ω j τ) =
        -(-4 * Real.pi * (1 - η) * ∑ τ, ν τ * X.tt ξ x τ) := by
      simp only [hb'ω, bv, Finset.mul_sum]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun τ _ => ?_
      ring
    rw [hexp, Real.exp_neg] at hbd
    set T := Real.exp (-4 * Real.pi * (1 - η) * ∑ τ, ν τ * X.tt ξ x τ)
    have hT : 0 < T := Real.exp_pos _
    rw [mul_inv_le_iff₀ hT] at hbd
    calc ‖ReciprocityTheory.L2DbarEstimates.Y.fourCoeff (hfun X P ξ x ω) b' k‖ * X.nfac la x ≤
        (Cη * X.la1 x ^ (-A) / X.nfac la x * T) * X.nfac la x :=
          mul_le_mul_of_nonneg_right hbd hnx.le
      _ = Cη * X.la1 x ^ (-A) * T := by field_simp

end ReciprocityTheory.ChartRestriction.G.FD
