import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace SquareIntegralBound

/- English proof (translation)
Break down `le_total a b with h | h` into its components or cases. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem sqle (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with h | h
  · calc a * b ≤ b * b := by gcongr
      _ = b ^ 2 := (sq b).symm
      _ ≤ a ^ 2 + b ^ 2 := le_add_self
  · calc a * b ≤ a * a := by gcongr
      _ = a ^ 2 := (sq a).symm
      _ ≤ a ^ 2 + b ^ 2 := le_self_add

/- English proof (translation)
Use `⟨hF.mul (Complex.continuous_conj.comp_aestronglyMeasurable hG), ?_⟩` and prove the remaining obligations. Unfold `HasFiniteIntegral`. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_mono fun x => ?_` and prove the remaining obligations. Rewrite using `[enorm_mul]`.

Establish `: ‖conj (G x)‖ₑ = ‖G x‖ₑ`. Rewrite using `[← ofReal_norm, ← ofReal_norm, Complex.norm_conj]`. Rewrite using `[this]`. Conclude with `sqle _ _`. Use `_ = ∫⁻ x, ‖F x‖ₑ ^ 2 ∂ν + ∫⁻ x, ‖G x‖ₑ ^ 2 ∂ν := lintegral_add_left' (hF.enorm.pow_const 2) _`.

Use `_ < ∞ := ENNReal.add_lt_top.2 ⟨hF2, hG2⟩`.
-/
theorem intMul {X : Type} [MeasurableSpace X] {ν : Measure X} {F G : X → ℂ}
    (hF : AEStronglyMeasurable F ν) (hG : AEStronglyMeasurable G ν)
    (hF2 : ∫⁻ x, ‖F x‖ₑ ^ 2 ∂ν < ∞) (hG2 : ∫⁻ x, ‖G x‖ₑ ^ 2 ∂ν < ∞) :
    Integrable (fun x => F x * conj (G x)) ν := by
  refine ⟨hF.mul (Complex.continuous_conj.comp_aestronglyMeasurable hG), ?_⟩
  unfold HasFiniteIntegral
  calc ∫⁻ x, ‖F x * conj (G x)‖ₑ ∂ν ≤ ∫⁻ x, (‖F x‖ₑ ^ 2 + ‖G x‖ₑ ^ 2) ∂ν := by
        refine lintegral_mono fun x => ?_
        rw [enorm_mul]
        have : ‖conj (G x)‖ₑ = ‖G x‖ₑ := by
          rw [← ofReal_norm, ← ofReal_norm, Complex.norm_conj]
        rw [this]; exact sqle _ _
    _ = ∫⁻ x, ‖F x‖ₑ ^ 2 ∂ν + ∫⁻ x, ‖G x‖ₑ ^ 2 ∂ν := lintegral_add_left' (hF.enorm.pow_const 2) _
    _ < ∞ := ENNReal.add_lt_top.2 ⟨hF2, hG2⟩

/- English proof (translation)
Use `set K := max (max C1 C2) 0 with hKdef`. Establish `hK0 : 0 ≤ K` using `le_max_right _ _`. Establish `hC1 : C1 ≤ K` using `le_trans (le_max_left _ _) (le_max_left _ _)`. Establish `hC2 : C2 ≤ K` using `le_trans (le_max_right _ _) (le_max_left _ _)`. Establish `hBs : 0 ≤ B * D ^ s` using `mul_nonneg hB (Real.rpow_nonneg hD.le _)`.

Rewrite using `[Real.rpow_one]`. Break down `le_or_gt D 1 with hD1 | hD1` into its components or cases. Establish `hmin : min D D⁻¹ = D` using `min_eq_left (le_trans hD1 (one_le_inv₀ hD |>.mpr hD1))`. Rewrite using `[hmin]`. Combine the equalities or inequalities in the displayed calculation.

Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Establish `e : D ^ s * D ^ (-1 : ℝ) = D ^ (s - 1)` using `by rw [← Real.rpow_add hD]; ring_nf`. Establish `hP0 : 0 ≤ D ^ (s - 1)` using `Real.rpow_nonneg hD.le _`. Establish `hPD : D ^ (s - 1) ≤ D`. Combine the equalities or inequalities in the displayed calculation.

Combine the equalities or inequalities in the displayed calculation. Establish `hmin : min D D⁻¹ = D⁻¹` using `min_eq_right (le_trans (inv_le_one_of_one_le₀ hD1.le) hD1.le)`. Rewrite using `[hmin]`. Combine the equalities or inequalities in the displayed calculation. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises.

Establish `e : D ^ s * D ^ (-(N : ℝ)) = D ^ (s - N)` using `by rw [← Real.rpow_add hD]; ring_nf`. Establish `hP0 : 0 ≤ D ^ (s - N)` using `Real.rpow_nonneg hD.le _`. Establish `hPD : D ^ (s - N) ≤ D⁻¹`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem bnd (D B C1 C2 s : ℝ) (N : ℕ) (hD : 0 < D) (hB : 0 ≤ B) (hs : 2 ≤ s) (hN : s + 1 ≤ N) (T : ℝ≥0∞)
    (h1 : T ≤ ENNReal.ofReal (C1 * D ^ (-1 : ℝ))) (h2 : T ≤ ENNReal.ofReal (C2 * D ^ (-(N : ℝ)))) :
    ENNReal.ofReal (B * D ^ s) * T ≤ ENNReal.ofReal (B * max (max C1 C2) 0 * min D D⁻¹ ^ (1 : ℝ)) := by
  set K := max (max C1 C2) 0 with hKdef
  have hK0 : 0 ≤ K := le_max_right _ _
  have hC1 : C1 ≤ K := le_trans (le_max_left _ _) (le_max_left _ _)
  have hC2 : C2 ≤ K := le_trans (le_max_right _ _) (le_max_left _ _)
  have hBs : 0 ≤ B * D ^ s := mul_nonneg hB (Real.rpow_nonneg hD.le _)
  rw [Real.rpow_one]
  rcases le_or_gt D 1 with hD1 | hD1
  · have hmin : min D D⁻¹ = D := min_eq_left (le_trans hD1 (one_le_inv₀ hD |>.mpr hD1))
    rw [hmin]
    calc ENNReal.ofReal (B * D ^ s) * T ≤ ENNReal.ofReal (B * D ^ s) * ENNReal.ofReal (C1 * D ^ (-1 : ℝ)) :=
          by gcongr
      _ = ENNReal.ofReal (B * D ^ s * (C1 * D ^ (-1 : ℝ))) := (ENNReal.ofReal_mul hBs).symm
      _ ≤ ENNReal.ofReal (B * K * D) := by
          apply ENNReal.ofReal_le_ofReal
          have e : D ^ s * D ^ (-1 : ℝ) = D ^ (s - 1) := by rw [← Real.rpow_add hD]; ring_nf
          have hP0 : 0 ≤ D ^ (s - 1) := Real.rpow_nonneg hD.le _
          have hPD : D ^ (s - 1) ≤ D := by
            calc D ^ (s - 1) ≤ D ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hD hD1 (by linarith)
              _ = D := Real.rpow_one D
          calc B * D ^ s * (C1 * D ^ (-1 : ℝ)) = B * C1 * (D ^ s * D ^ (-1 : ℝ)) := by ring
            _ = B * C1 * D ^ (s - 1) := by rw [e]
            _ ≤ B * K * D ^ (s - 1) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC1 hB) hP0
            _ ≤ B * K * D := mul_le_mul_of_nonneg_left hPD (mul_nonneg hB hK0)
  · have hmin : min D D⁻¹ = D⁻¹ := min_eq_right (le_trans (inv_le_one_of_one_le₀ hD1.le) hD1.le)
    rw [hmin]
    calc ENNReal.ofReal (B * D ^ s) * T ≤ ENNReal.ofReal (B * D ^ s) * ENNReal.ofReal (C2 * D ^ (-(N : ℝ))) :=
          by gcongr
      _ = ENNReal.ofReal (B * D ^ s * (C2 * D ^ (-(N : ℝ)))) := (ENNReal.ofReal_mul hBs).symm
      _ ≤ ENNReal.ofReal (B * K * D⁻¹) := by
          apply ENNReal.ofReal_le_ofReal
          have e : D ^ s * D ^ (-(N : ℝ)) = D ^ (s - N) := by rw [← Real.rpow_add hD]; ring_nf
          have hP0 : 0 ≤ D ^ (s - N) := Real.rpow_nonneg hD.le _
          have hPD : D ^ (s - N) ≤ D⁻¹ := by
            calc D ^ (s - N) ≤ D ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hD1.le (by linarith)
              _ = D⁻¹ := Real.rpow_neg_one D
          calc B * D ^ s * (C2 * D ^ (-(N : ℝ))) = B * C2 * (D ^ s * D ^ (-(N : ℝ))) := by ring
            _ = B * C2 * D ^ (s - N) := by rw [e]
            _ ≤ B * K * D ^ (s - N) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC2 hB) hP0
            _ ≤ B * K * D⁻¹ := mul_le_mul_of_nonneg_left hPD (mul_nonneg hB hK0)

end SquareIntegralBound

open SquareIntegralBound in
/- English proof (translation)
Introduce `hD0 hN0 hP2 hU0 hU2 hV1 hG4 E _ _ _ k μ _ hk β hβ ψ hψ S m α α' u f φ hd`. Take `⟨β₁, hβ₁, hU0a, hU0b⟩` from `hU0 E k μ hk β hβ`. Take `⟨β', hβ', hU2'⟩` from `hU2 E k μ ψ hψ (k - 1) (by omega) β₁ hβ₁`. Take `⟨hDpos, hDmul, hDcont, hDrat, hDU, -⟩` from `hD0 E k`. Take `⟨-, -, -, -, hPchi, hGoodPre, hLu, hLmir, hLcont, hLsupp⟩` from `hP2 E k ψ hψ`.

Take `⟨C, hC, hfC⟩` from `hd.supp`. Take `⟨a, ε, Cf, hε, hsq⟩` from `hd.sq`. Take `⟨Φ₀, hΦ1, -, hΦc, hΦI⟩` from `exists_continuous_one_zero_of_isCompact hC isClosed_empty (Set.disjoint_empty C)`. Take `⟨-, -, hV1c⟩` from `hV1 E k μ hk β hβ`. Establish `hk1 : k - 1 < k` using `by omega`.

Establish `hDu : ∀ u g : GA E k, UU 0 u → Dt (u * g) = Dt g` using `fun u g hu => by`. Rewrite using `[hDmul, hDU 0 u hu, one_mul]`. Establish `hDr : ∀ γ (g : GA E k), Dt (ratGL E k γ * g) = Dt g` using `fun γ g => by`. Rewrite using `[hDmul, hDrat, one_mul]`. Choose the witnesses or unpack the hypotheses as in `⟨Bφ, hBφ⟩ : ∃ B, ∀ g, ‖φ g‖ ≤ B := by`.

Take `⟨B, hB⟩` from `hd.dec 0`. Establish `hne : (fun _ => (1 : E) : Fin k → E) ≠ 0` using `fun h => by`. Use `congrFun h ⟨0, hk⟩` as an intermediate fact. Simplify using `at this`. Conclude with `⟨B, fun g => by simpa using hB g _ hne⟩`.

Establish `hBφ0 : 0 ≤ Bφ` using `(norm_nonneg _).trans (hBφ 1)`. Use `⟨β', a / 2 + 1, hβ', fun z hz => ?_⟩` and prove the remaining obligations. Use `set χ₁ : GA E k → ℂ := fun g => ((Dt g ^ (a / 2) : ℝ) : ℂ) with hχ₁`. Use `set χ₂ : GA E k → ℂ := fun g => conj ((Dt g : ℂ) ^ (z - ((a / 2 : ℝ) : ℂ))) * (Φ₀ (lastRow g) : ℂ) with hχ₂`. Establish `hχ₁c : Continuous χ₁` using `Complex.continuous_ofReal.comp (hDcont.rpow_const fun g => Or.inl (hDpos g).ne')`.

Establish `hχ₂c : Continuous χ₂`. Use `(Complex.continuous_conj.comp ?_).mul (Complex.continuous_ofReal.comp (Φ₀.continuous.comp hLcont))` and prove the remaining obligations. Conclude with `(Complex.continuous_ofReal.comp hDcont).cpow continuous_const fun g => Complex.ofReal_mem_slitPlane.2 (hDpos g)`. Establish `hχ₁u : ∀ u, UU 0 u → ∀ g, χ₁ (u * g) = χ₁ g` using `fun u hu g => by simp only [hχ₁, hDu u g hu]`. Establish `hχ₁m : ∀ γ, IsMir (k - 1) γ → ∀ g, χ₁ (ratGL E k γ * g) = χ₁ g` using `fun γ _ g => by simp only [hχ₁, hDr]`.

Establish `hχ₂u : ∀ u, UU 0 u → ∀ g, χ₂ (u * g) = χ₂ g` using `fun u hu g => by simp only [hχ₂, hDu u g hu, hLu u g hu]`. Establish `hχ₂m : ∀ γ, IsMir (k - 1) γ → ∀ g, χ₂ (ratGL E k γ * g) = χ₂ g` using `fun γ hγ g => by`. Simplify `hγ)]` using `only [hχ₂, hDr, hLmir γ g (by simpa`. Take `⟨hpre1, hwf, -⟩` from `hPchi (k - 1) hk1 f χ₁ hd.pre hχ₁c hχ₁u hχ₁m`. Take `⟨hpre2, hwφ, hgood2⟩` from `hPchi (k - 1) hk1 φ χ₂ (hGoodPre _ _ hd.good) hχ₂c hχ₂u hχ₂m`.

Establish `hgood2` using `hgood2 hd.good`. Establish `hK : ∀ g, lastRow g ∈ C → χ₁ g * conj (χ₂ g) = (Dt g : ℂ) ^ z` using `fun g hg => by`. Establish `h1 : Φ₀ (lastRow g) = 1` using `hΦ1 hg`. Simplify using `only [hχ₁, hχ₂, map_mul, Complex.conj_conj, Complex.conj_ofReal, h1, Complex.ofReal_one, mul_one]`. Rewrite using `[Complex.ofReal_cpow (hDpos g).le, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 (hDpos g).ne')]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hW : ∀ g, whit ψ (k - 1) (fun g => χ₁ g * f g) g * conj (whit ψ (k - 1) (fun g => χ₂ g * φ g) g) = PW ψ f φ g * (Dt g : ℂ) ^ z` using `fun g => by`. Rewrite using `[hwf, hwφ]`. Distinguish the cases in `h0 : whit ψ (k - 1) f g = 0`.

Simplify using `[PW, h0]`. Rewrite using `[PW, ← hK g (hLsupp (k - 1) hk1 f C hfC g h0), map_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hF : ∀ g, χ₁ g * f g * conj (χ₂ g * φ g) = f g * conj (φ g) * (Dt g : ℂ) ^ z` using `fun g => by`. Distinguish the cases in `h0 : f g = 0`.

Simplify using `[h0]`. Rewrite using `[← hK g (hfC g h0), map_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hL2f : ∫⁻ g, ‖χ₁ g * f g‖ₑ ^ 2 ∂μ.withDensity β₁ < ∞`. Rewrite using `[hU0a (fun g => ‖χ₁ g * f g‖ₑ ^ 2) (hpre1.cont.measurable.enorm.pow_const 2) (fun γ hγ g => congrArg (fun w : ℂ => ‖w‖ₑ ^ 2) (hpre1.left γ hγ g))]`.

Use `lt_of_le_of_lt (lintegral_mono fun g => ?_) (((hV1c ε hε).const_mul Cf).lintegral_lt_top)` and prove the remaining obligations. Establish `hterm : ∀ x, ‖χ₁ x * f x‖ₑ ^ 2 = ENNReal.ofReal (Dt x ^ a) * ‖f x‖ₑ ^ 2` using `fun x => by`. Rewrite using `[enorm_mul, mul_pow]`. Use `congr 1`. Rewrite using `[hχ₁]`.

Simplify using `only`. Rewrite using `[← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (hDpos x).le _), ← ENNReal.ofReal_pow (Real.rpow_nonneg (hDpos x).le _), ← Real.rpow_mul_natCast (hDpos x).le]`. Evaluate the numerical expressions. Simplify using `only [hterm, hDr, ENNReal.tsum_mul_left]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← ENNReal.ofReal_mul (Real.rpow_nonneg (hDpos g).le _)]`. Use `congr 1`. Establish `hp` using `Real.rpow_pos_of_pos (hDpos g) a`. Rewrite using `[Real.rpow_neg (hDpos g).le]`. Clear the denominators using the available nonvanishing facts.

Establish `hL2φ : ∫⁻ g, ‖χ₂ g * φ g‖ₑ ^ 2 ∂μ.withDensity β₁ < ∞`. Take `⟨-, hG4b⟩` from `hG4 E k hk φ hd.dec`. Take `⟨s, hs⟩ : ∃ s, s = 2 * z.re - a` from `⟨_, rfl⟩`. Establish `hs2 : 2 ≤ s` using `by linarith`. Take `⟨N, hN⟩ : ∃ N : ℕ, N = ⌈s⌉₊ + 1` from `⟨_, rfl⟩`.

Establish `hNs : s + 1 ≤ (N : ℝ)` using `by rw [hN]; push_cast; linarith [Nat.le_ceil s]`. Take `⟨C1, hC1⟩` from `hG4b _ hΦc.isCompact k le_rfl`. Take `⟨C2, hC2⟩` from `hG4b _ hΦc.isCompact (k * N) (Nat.le_mul_of_pos_right k (by omega))`. Establish `hkR : (k : ℝ) ≠ 0` using `by exact_mod_cast (by omega : k ≠ 0)`. Establish `e1 : -((k : ℕ) : ℝ) / k = -1` using `by field_simp`.

Establish `e2 : -(((k * N : ℕ)) : ℝ) / k = -(N : ℝ)` using `by push_cast; field_simp`. Rewrite `hC1` using `[e1]`. Rewrite `hC2` using `[e2]`. Rewrite using `[hU0a (fun g => ‖χ₂ g * φ g‖ₑ ^ 2) (hpre2.cont.measurable.enorm.pow_const 2) (fun γ hγ g => congrArg (fun w : ℂ => ‖w‖ₑ ^ 2) (hpre2.left γ hγ g))]`. Use `lt_of_le_of_lt (lintegral_mono fun g => ?_) (((hV1c 1 one_pos).const_mul (Bφ * max (max C1 C2) 0)).lintegral_lt_top)` and prove the remaining obligations.

Use `le_trans ?_ (SquareIntegralBound.bnd (Dt g) Bφ C1 C2 s N (hDpos g) hBφ0 hs2 hNs _ (hC1 g) (hC2 g))` and prove the remaining obligations. Rewrite using `[← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]`. Use `ENNReal.tsum_le_tsum fun ξ => ?_` and prove the remaining obligations. Establish `hφ : ∀ γ g, φ (ratGL E k γ * g) = φ g` using `hd.inv`. Rewrite using `[hφ]`.

Establish `hDx : Dt (ratGL E k (gam ξ) * g) = Dt g` using `hDr _ _`. Distinguish the cases in `hx : lastRow (ratGL E k (gam ξ) * g) ∈ tsupport Φ₀`. Rewrite using `[Set.indicator_of_mem hx, one_mul]`. Rewrite using `[← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (mul_nonneg hBφ0 (Real.rpow_nonneg (hDpos g).le _))]`. Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations.

Establish `hχn : ‖χ₂ (ratGL E k (gam ξ) * g)‖ ≤ Dt g ^ (z.re - a / 2)`. Rewrite using `[hχ₂]`. Simplify using `only`. Rewrite using `[norm_mul, Complex.norm_conj, Complex.norm_cpow_eq_rpow_re_of_pos (hDpos _), Complex.norm_real, hDx]`. Simplify using `only [Complex.sub_re, Complex.ofReal_re]`.

Establish `h0` using `hΦI (lastRow (ratGL E k (gam ξ) * g))`. Rewrite using `[Real.norm_of_nonneg h0.1]`. Conclude with `mul_le_of_le_one_right (Real.rpow_nonneg (hDpos g).le _) h0.2`. Establish `hsq' : Dt g ^ s = (Dt g ^ (z.re - a / 2)) ^ 2`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul (hDpos g).le]`.

Use `congr 1`. Rewrite using `[hs]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[norm_mul, mul_pow, hsq']`.

Establish `hφg` using `hBφ g`. Establish `h3 : ‖χ₂ (ratGL E k (gam ξ) * g)‖ ^ 2 ≤ (Dt g ^ (z.re - a / 2)) ^ 2` using `pow_le_pow_left₀ (norm_nonneg _) hχn 2`. Establish `h4 : 0 ≤ (Dt g ^ (z.re - a / 2)) ^ 2` using `by positivity`. Use polynomial arithmetic with `[norm_nonneg (φ g), mul_le_mul_of_nonneg_right h3 (sq_nonneg ‖φ g‖), mul_le_mul_of_nonneg_left hφg (mul_nonneg h4 (norm_nonneg (φ g)))]`. Establish `: Φ₀ (lastRow (ratGL E k (gam ξ) * g)) = 0` using `image_eq_zero_of_notMem_tsupport hx`.

Simplify using `[hχ₂, this]`. Take `⟨hint, heq⟩` from `hU2' _ _ hpre1 hgood2 hL2f hL2φ`. Establish `hmeas : Measurable fun g => χ₁ g * f g * conj (χ₂ g * φ g)` using `(hpre1.cont.mul (Complex.continuous_conj.comp hpre2.cont)).measurable`. Establish `hinv : ∀ γ, IsMir (k - 1) γ → ∀ g, (fun g => χ₁ g * f g * conj (χ₂ g * φ g)) (ratGL E k γ * g) = (fun g => χ₁ g * f g * conj (χ₂ g * φ g)) g` using `fun γ hγ g => by`. Establish `h1` using `hpre1.left γ hγ g`.

Establish `h2` using `hpre2.left γ hγ g`. Simplify using `only at h1 h2 ⊢`. Rewrite using `[h1, h2]`. Establish `hintF : Integrable (fun g => χ₁ g * f g * conj (χ₂ g * φ g)) (μ.withDensity β₁)` using `intMul hpre1.cont.aestronglyMeasurable hpre2.cont.aestronglyMeasurable hL2f hL2φ`. Establish `hsum : ∀ g, sumF (fun g => χ₁ g * f g * conj (χ₂ g * φ g)) g = sumF f g * conj (φ g) * (Dt g : ℂ) ^ z` using `fun g => by`.

Establish `hφ : ∀ γ g, φ (ratGL E k γ * g) = φ g` using `hd.inv`. Simplify using `only [sumF, hF]`. Simplify using `only [hφ, hDr, tsum_mul_right]`. Use `⟨hint.congr (Filter.Eventually.of_forall hW), ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem moderate_growth_of : D0 → N0 → P2 → U0 → U2 → V1 → ThetaDecaying → M0 := by
  intro hD0 hN0 hP2 hU0 hU2 hV1 hG4 E _ _ _ k μ _ hk β hβ ψ hψ S m α α' u f φ hd
  obtain ⟨β₁, hβ₁, hU0a, hU0b⟩ := hU0 E k μ hk β hβ
  obtain ⟨β', hβ', hU2'⟩ := hU2 E k μ ψ hψ (k - 1) (by omega) β₁ hβ₁
  obtain ⟨hDpos, hDmul, hDcont, hDrat, hDU, -⟩ := hD0 E k
  obtain ⟨-, -, -, -, hPchi, hGoodPre, hLu, hLmir, hLcont, hLsupp⟩ := hP2 E k ψ hψ
  obtain ⟨C, hC, hfC⟩ := hd.supp
  obtain ⟨a, ε, Cf, hε, hsq⟩ := hd.sq
  obtain ⟨Φ₀, hΦ1, -, hΦc, hΦI⟩ :=
    exists_continuous_one_zero_of_isCompact hC isClosed_empty (Set.disjoint_empty C)
  obtain ⟨-, -, hV1c⟩ := hV1 E k μ hk β hβ
  have hk1 : k - 1 < k := by omega
  have hDu : ∀ u g : GA E k, UU 0 u → Dt (u * g) = Dt g := fun u g hu => by
    rw [hDmul, hDU 0 u hu, one_mul]
  have hDr : ∀ γ (g : GA E k), Dt (ratGL E k γ * g) = Dt g := fun γ g => by
    rw [hDmul, hDrat, one_mul]
  obtain ⟨Bφ, hBφ⟩ : ∃ B, ∀ g, ‖φ g‖ ≤ B := by
    obtain ⟨B, hB⟩ := hd.dec 0
    have hne : (fun _ => (1 : E) : Fin k → E) ≠ 0 := fun h => by
      have := congrFun h ⟨0, hk⟩; simp at this
    exact ⟨B, fun g => by simpa using hB g _ hne⟩
  have hBφ0 : 0 ≤ Bφ := (norm_nonneg _).trans (hBφ 1)
  refine ⟨β', a / 2 + 1, hβ', fun z hz => ?_⟩
  set χ₁ : GA E k → ℂ := fun g => ((Dt g ^ (a / 2) : ℝ) : ℂ) with hχ₁
  set χ₂ : GA E k → ℂ := fun g => conj ((Dt g : ℂ) ^ (z - ((a / 2 : ℝ) : ℂ))) * (Φ₀ (lastRow g) : ℂ) with hχ₂
  have hχ₁c : Continuous χ₁ := Complex.continuous_ofReal.comp
    (hDcont.rpow_const fun g => Or.inl (hDpos g).ne')
  have hχ₂c : Continuous χ₂ := by
    refine (Complex.continuous_conj.comp ?_).mul (Complex.continuous_ofReal.comp (Φ₀.continuous.comp hLcont))
    exact (Complex.continuous_ofReal.comp hDcont).cpow continuous_const
      fun g => Complex.ofReal_mem_slitPlane.2 (hDpos g)
  have hχ₁u : ∀ u, UU 0 u → ∀ g, χ₁ (u * g) = χ₁ g := fun u hu g => by simp only [hχ₁, hDu u g hu]
  have hχ₁m : ∀ γ, IsMir (k - 1) γ → ∀ g, χ₁ (ratGL E k γ * g) = χ₁ g := fun γ _ g => by simp only [hχ₁, hDr]
  have hχ₂u : ∀ u, UU 0 u → ∀ g, χ₂ (u * g) = χ₂ g := fun u hu g => by simp only [hχ₂, hDu u g hu, hLu u g hu]
  have hχ₂m : ∀ γ, IsMir (k - 1) γ → ∀ g, χ₂ (ratGL E k γ * g) = χ₂ g := fun γ hγ g => by
    simp only [hχ₂, hDr, hLmir γ g (by simpa using hγ)]
  obtain ⟨hpre1, hwf, -⟩ := hPchi (k - 1) hk1 f χ₁ hd.pre hχ₁c hχ₁u hχ₁m
  obtain ⟨hpre2, hwφ, hgood2⟩ := hPchi (k - 1) hk1 φ χ₂ (hGoodPre _ _ hd.good) hχ₂c hχ₂u hχ₂m
  have hgood2 := hgood2 hd.good
  have hK : ∀ g, lastRow g ∈ C → χ₁ g * conj (χ₂ g) = (Dt g : ℂ) ^ z := fun g hg => by
    have h1 : Φ₀ (lastRow g) = 1 := hΦ1 hg
    simp only [hχ₁, hχ₂, map_mul, Complex.conj_conj, Complex.conj_ofReal, h1, Complex.ofReal_one, mul_one]
    rw [Complex.ofReal_cpow (hDpos g).le, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 (hDpos g).ne')]
    congr 1; ring
  have hW : ∀ g, whit ψ (k - 1) (fun g => χ₁ g * f g) g * conj (whit ψ (k - 1) (fun g => χ₂ g * φ g) g) =
      PW ψ f φ g * (Dt g : ℂ) ^ z := fun g => by
    rw [hwf, hwφ]
    by_cases h0 : whit ψ (k - 1) f g = 0
    · simp [PW, h0]
    · rw [PW, ← hK g (hLsupp (k - 1) hk1 f C hfC g h0), map_mul]; ring
  have hF : ∀ g, χ₁ g * f g * conj (χ₂ g * φ g) = f g * conj (φ g) * (Dt g : ℂ) ^ z := fun g => by
    by_cases h0 : f g = 0
    · simp [h0]
    · rw [← hK g (hfC g h0), map_mul]; ring
  have hL2f : ∫⁻ g, ‖χ₁ g * f g‖ₑ ^ 2 ∂μ.withDensity β₁ < ∞ := by
    rw [hU0a (fun g => ‖χ₁ g * f g‖ₑ ^ 2) (hpre1.cont.measurable.enorm.pow_const 2)
      (fun γ hγ g => congrArg (fun w : ℂ => ‖w‖ₑ ^ 2) (hpre1.left γ hγ g))]
    refine lt_of_le_of_lt (lintegral_mono fun g => ?_) (((hV1c ε hε).const_mul Cf).lintegral_lt_top)
    have hterm : ∀ x, ‖χ₁ x * f x‖ₑ ^ 2 = ENNReal.ofReal (Dt x ^ a) * ‖f x‖ₑ ^ 2 := fun x => by
      rw [enorm_mul, mul_pow]
      congr 1
      rw [hχ₁]
      simp only
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (hDpos x).le _),
        ← ENNReal.ofReal_pow (Real.rpow_nonneg (hDpos x).le _), ← Real.rpow_mul_natCast (hDpos x).le]
      norm_num
    simp only [hterm, hDr, ENNReal.tsum_mul_left]
    calc ENNReal.ofReal (Dt g ^ a) * ∑' ξ : RowT E k k, ‖f (ratGL E k (gam ξ) * g)‖ₑ ^ 2
        ≤ ENNReal.ofReal (Dt g ^ a) * ENNReal.ofReal (Cf * min (Dt g) (Dt g)⁻¹ ^ ε * Dt g ^ (-a)) := by
          gcongr; exact hsq g
      _ = ENNReal.ofReal (Cf * min (Dt g) (Dt g)⁻¹ ^ ε) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (hDpos g).le _)]
        congr 1
        have hp := Real.rpow_pos_of_pos (hDpos g) a
        rw [Real.rpow_neg (hDpos g).le]
        field_simp
  have hL2φ : ∫⁻ g, ‖χ₂ g * φ g‖ₑ ^ 2 ∂μ.withDensity β₁ < ∞ := by
    obtain ⟨-, hG4b⟩ := hG4 E k hk φ hd.dec
    obtain ⟨s, hs⟩ : ∃ s, s = 2 * z.re - a := ⟨_, rfl⟩
    have hs2 : 2 ≤ s := by linarith
    obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌈s⌉₊ + 1 := ⟨_, rfl⟩
    have hNs : s + 1 ≤ (N : ℝ) := by rw [hN]; push_cast; linarith [Nat.le_ceil s]
    obtain ⟨C1, hC1⟩ := hG4b _ hΦc.isCompact k le_rfl
    obtain ⟨C2, hC2⟩ := hG4b _ hΦc.isCompact (k * N) (Nat.le_mul_of_pos_right k (by omega))
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have e1 : -((k : ℕ) : ℝ) / k = -1 := by field_simp
    have e2 : -(((k * N : ℕ)) : ℝ) / k = -(N : ℝ) := by push_cast; field_simp
    rw [e1] at hC1; rw [e2] at hC2
    rw [hU0a (fun g => ‖χ₂ g * φ g‖ₑ ^ 2) (hpre2.cont.measurable.enorm.pow_const 2)
      (fun γ hγ g => congrArg (fun w : ℂ => ‖w‖ₑ ^ 2) (hpre2.left γ hγ g))]
    refine lt_of_le_of_lt (lintegral_mono fun g => ?_)
      (((hV1c 1 one_pos).const_mul (Bφ * max (max C1 C2) 0)).lintegral_lt_top)
    refine le_trans ?_ (SquareIntegralBound.bnd (Dt g) Bφ C1 C2 s N (hDpos g) hBφ0 hs2 hNs _ (hC1 g) (hC2 g))
    rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun ξ => ?_
    have hφ : ∀ γ g, φ (ratGL E k γ * g) = φ g := hd.inv
    rw [hφ]
    have hDx : Dt (ratGL E k (gam ξ) * g) = Dt g := hDr _ _
    by_cases hx : lastRow (ratGL E k (gam ξ) * g) ∈ tsupport Φ₀
    · rw [Set.indicator_of_mem hx, one_mul]
      rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
        ← ENNReal.ofReal_mul (mul_nonneg hBφ0 (Real.rpow_nonneg (hDpos g).le _))]
      refine ENNReal.ofReal_le_ofReal ?_
      have hχn : ‖χ₂ (ratGL E k (gam ξ) * g)‖ ≤ Dt g ^ (z.re - a / 2) := by
        rw [hχ₂]; simp only
        rw [norm_mul, Complex.norm_conj, Complex.norm_cpow_eq_rpow_re_of_pos (hDpos _), Complex.norm_real, hDx]
        simp only [Complex.sub_re, Complex.ofReal_re]
        have h0 := hΦI (lastRow (ratGL E k (gam ξ) * g))
        rw [Real.norm_of_nonneg h0.1]
        exact mul_le_of_le_one_right (Real.rpow_nonneg (hDpos g).le _) h0.2
      have hsq' : Dt g ^ s = (Dt g ^ (z.re - a / 2)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (hDpos g).le]; congr 1; rw [hs]; push_cast; ring
      rw [norm_mul, mul_pow, hsq']
      have hφg := hBφ g
      have h3 : ‖χ₂ (ratGL E k (gam ξ) * g)‖ ^ 2 ≤ (Dt g ^ (z.re - a / 2)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hχn 2
      have h4 : 0 ≤ (Dt g ^ (z.re - a / 2)) ^ 2 := by positivity
      nlinarith [norm_nonneg (φ g), mul_le_mul_of_nonneg_right h3 (sq_nonneg ‖φ g‖),
        mul_le_mul_of_nonneg_left hφg (mul_nonneg h4 (norm_nonneg (φ g)))]
    · have : Φ₀ (lastRow (ratGL E k (gam ξ) * g)) = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [hχ₂, this]
  obtain ⟨hint, heq⟩ := hU2' _ _ hpre1 hgood2 hL2f hL2φ
  have hmeas : Measurable fun g => χ₁ g * f g * conj (χ₂ g * φ g) :=
    (hpre1.cont.mul (Complex.continuous_conj.comp hpre2.cont)).measurable
  have hinv : ∀ γ, IsMir (k - 1) γ → ∀ g, (fun g => χ₁ g * f g * conj (χ₂ g * φ g)) (ratGL E k γ * g) =
      (fun g => χ₁ g * f g * conj (χ₂ g * φ g)) g := fun γ hγ g => by
    have h1 := hpre1.left γ hγ g
    have h2 := hpre2.left γ hγ g
    simp only at h1 h2 ⊢
    rw [h1, h2]
  have hintF : Integrable (fun g => χ₁ g * f g * conj (χ₂ g * φ g)) (μ.withDensity β₁) :=
    intMul hpre1.cont.aestronglyMeasurable hpre2.cont.aestronglyMeasurable hL2f hL2φ
  have hsum : ∀ g, sumF (fun g => χ₁ g * f g * conj (χ₂ g * φ g)) g =
      sumF f g * conj (φ g) * (Dt g : ℂ) ^ z := fun g => by
    have hφ : ∀ γ g, φ (ratGL E k γ * g) = φ g := hd.inv
    simp only [sumF, hF]
    simp only [hφ, hDr, tsum_mul_right]
  refine ⟨hint.congr (Filter.Eventually.of_forall hW), ?_⟩
  calc ∫ g, sumF f g * conj (φ g) * (Dt g : ℂ) ^ z ∂μ.withDensity β
      = ∫ g, sumF (fun g => χ₁ g * f g * conj (χ₂ g * φ g)) g ∂μ.withDensity β := by simp only [hsum]
    _ = ∫ g, χ₁ g * f g * conj (χ₂ g * φ g) ∂μ.withDensity β₁ := (hU0b _ hmeas hinv hintF).symm
    _ = _ := heq
    _ = ∫ g, PW ψ f φ g * (Dt g : ℂ) ^ z ∂μ.withDensity β' := by simp only [hW]

end PositivityTheory.AdelicQuotientData

end
