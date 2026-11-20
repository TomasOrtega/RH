import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionSeparatingTwoPointsAmpleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleAddEffectiveOfNefBigStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosKltAddSmulEffectiveDivisorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltAtLcAtOfLeCoeffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEffQDivAddOfIsQCart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLogCanonicalMultipleAddQWeil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowMulIntersectionLeOfNefClassOnClosed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensOfIsNef
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.NefBigSep

variable {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] {H N A B : LB X} {Z : Closeds X}

/- English proof (translation)
Rewrite using `[hZ.interNumRed_of_cls_eq_add hH hN (isLB_lbPow hA a) (isLB_lbPow hB b) (by rw [cls_lbPow hA, cls_lbPow hB, e]), hZ.interNumRed_lbPow hH hA, hZ.interNumRed_lbPow hH hB]`.
-/
theorem deg_of_cls_eq (hZ : IsCompleteCurve k Z) (hH : IsAmpleLB H) (hN : N.IsLB) (hA : A.IsLB)
    (hB : B.IsLB) (a b : ℕ) (e : cls N hN = a • cls A hA + b • cls B hB) :
    interNumRed k Z ![N] = a * interNumRed k Z ![A] + b * interNumRed k Z ![B] := by
  rw [hZ.interNumRed_of_cls_eq_add hH hN (isLB_lbPow hA a) (isLB_lbPow hB b)
    (by rw [cls_lbPow hA, cls_lbPow hB, e]), hZ.interNumRed_lbPow hH hA,
    hZ.interNumRed_lbPow hH hB]

/- English proof (translation)
Establish `hd : (0 : ℚ) < ρ.den` using `by exact_mod_cast ρ.den_pos`. Establish `hu : (0 : ℤ) ≤ ρ.num` using `(Rat.num_pos.2 hρ).le`. Establish `hρ' : ((ρ.num.toNat : ℕ) : ℚ) = ρ * ρ.den`. Rewrite using `[show ((ρ.num.toNat : ℕ) : ℚ) = ((ρ.num.toNat : ℤ) : ℚ) from rfl, Int.toNat_of_nonneg hu]`. Conclude with `(Rat.mul_den_eq_num ρ).symm`.

Establish `hgap : 0 < (ρ.den : ℚ) * (ρ - S)` using `mul_pos hd (sub_pos.2 hS)`. Take `⟨t, ht⟩` from `exists_nat_gt (max (1 / c) (a / ((ρ.den : ℚ) * (ρ - S))))`. Establish `ht1 : 1 / c < t` using `lt_of_le_of_lt (le_max_left _ _) ht`. Establish `ht2 : a / ((ρ.den : ℚ) * (ρ - S)) < t` using `lt_of_le_of_lt (le_max_right _ _) ht`. Establish `htpos : (0 : ℚ) < t` using `lt_trans (by positivity) ht1`.

Establish `ht2' : (a : ℚ) < t * ((ρ.den : ℚ) * (ρ - S))`. Rewrite `ht2` using `[div_lt_iff₀ hgap]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨ρ.num.toNat * t, ρ.den * t, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Nat.mul_pos ρ.den_pos (by exact_mod_cast htpos)`.

Use `push_cast`. Rewrite using `[hρ']`. Expand and normalize the polynomial expressions, which then agree. Establish `: (a : ℚ) < ((ρ.num.toNat * t : ℕ) : ℚ)` using `by push_cast; rw [hρ']; nlinarith [mul_nonneg (mul_nonneg hd.le htpos.le) hS0]`. Conclude with `this` after adjusting the coercions.

Use `push_cast`. Rewrite using `[div_le_iff₀ (by positivity)]`. Rewrite `ht1` using `[div_lt_iff₀ hc]`. Establish `: (1 : ℚ) ≤ ρ.den` using `by exact_mod_cast ρ.den_pos`. Use the polynomial consequences of the given equalities and inequalities.

Use `push_cast`. Rewrite using `[hρ']`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem exists_budget (ρ S c : ℚ) (a : ℕ) (hρ : 0 < ρ) (hS : S < ρ) (hS0 : 0 ≤ S) (hc : 0 < c) :
    ∃ q m' : ℕ, 0 < m' ∧ (q : ℚ) = ρ * m' ∧ a < q ∧ 1 / (m' : ℚ) ≤ c ∧ (m' : ℚ) * S < q - a := by
  have hd : (0 : ℚ) < ρ.den := by exact_mod_cast ρ.den_pos
  have hu : (0 : ℤ) ≤ ρ.num := (Rat.num_pos.2 hρ).le
  have hρ' : ((ρ.num.toNat : ℕ) : ℚ) = ρ * ρ.den := by
    rw [show ((ρ.num.toNat : ℕ) : ℚ) = ((ρ.num.toNat : ℤ) : ℚ) from rfl, Int.toNat_of_nonneg hu]
    exact (Rat.mul_den_eq_num ρ).symm
  have hgap : 0 < (ρ.den : ℚ) * (ρ - S) := mul_pos hd (sub_pos.2 hS)
  obtain ⟨t, ht⟩ := exists_nat_gt (max (1 / c) (a / ((ρ.den : ℚ) * (ρ - S))))
  have ht1 : 1 / c < t := lt_of_le_of_lt (le_max_left _ _) ht
  have ht2 : a / ((ρ.den : ℚ) * (ρ - S)) < t := lt_of_le_of_lt (le_max_right _ _) ht
  have htpos : (0 : ℚ) < t := lt_trans (by positivity) ht1
  have ht2' : (a : ℚ) < t * ((ρ.den : ℚ) * (ρ - S)) := by
    rw [div_lt_iff₀ hgap] at ht2; linarith
  refine ⟨ρ.num.toNat * t, ρ.den * t, ?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.mul_pos ρ.den_pos (by exact_mod_cast htpos)
  · push_cast; rw [hρ']; ring
  · have : (a : ℚ) < ((ρ.num.toNat * t : ℕ) : ℚ) := by
      push_cast; rw [hρ']; nlinarith [mul_nonneg (mul_nonneg hd.le htpos.le) hS0]
    exact_mod_cast this
  · push_cast
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hc] at ht1
    have : (1 : ℚ) ≤ ρ.den := by exact_mod_cast ρ.den_pos
    nlinarith
  · push_cast; rw [hρ']; nlinarith

end GlobalTheory.NefBigSep

namespace GlobalTheory.NefBigSep

/- English proof (translation)
Introduce `hPr hNad hNef X _ _ _ p n hp hdim M Δ m G N ρ h x₁ x₂ hM hΔ hklt hm hG hNn hNb hcurve hx₁ hx₂ hne hh hz hsum hρ`. Use `letI := algebraΓOfHom p`. Take `⟨a, A, hA, E₀, ha, hAmp, hE₀, hcls⟩` from `GlobalTheory.T.exists_ample_add_effective_of_nef_big hNef X p hp N hNn.isLB hNn hNb`. Take `⟨c, hc, hkltc⟩` from `GlobalTheory.T.exists_pos_klt_add_smul_effective_divisor hPr X p n hp hdim Δ m G (qWeil E₀ 1) hm hG hklt ⟨1, E₀, one_pos, hE₀, rfl⟩`. Establish `hS0 : 0 ≤ ∑ e ∈ Finset.Icc 1 n, h e` using `Finset.sum_nonneg fun e _ => (hh e).le`.

Take `⟨q, m', hm', hq, haq, hmc, hbud⟩` from `exists_budget ρ _ c a hρ hsum hS0 hc`. Establish `hNp` using `isLB_lbPow hNn.isLB (q - a)`. Establish `hN'lb` using `isLB_tens hA hNp`. Establish `hclsN' : cls _ hN'lb = cls A hA + (q - a) • cls N hNn.isLB`. Rewrite using `[cls_tens hA hNp, cls_lbPow hNn.isLB]`.

Establish `hN'amp : IsAmpleLB (tens A (lbPow N (q - a)))` using `IsAmpleLB.tens_of_isNef hNef ℂ X p hp A _ hAmp (hNn.pow hAmp _)`. Establish `hqa : (0 : ℚ) < q - a` using `sub_pos.2 (by exact_mod_cast haq)`. Establish `hqa' : (((q - a : ℕ) : ℚ)) = q - a` using `by rw [Nat.cast_sub haq.le]`. Establish `hB : qWeil E₀ m' = (1 / (m' : ℚ)) • qWeil E₀ 1`. Use function extensionality and compare the values at `z`.

Simplify using `[qWeil]`. Expand and normalize the polynomial expressions, which then agree. Use `GlobalTheory.T.exists_section_separating_two_points_ample hPr hNad hNef X p n hp hdim M (Δ + qWeil E₀ m') (m * m') (m' • G + m • E₀) (tens A (lbPow N (q - a))) (1 / (m' : ℚ)) (fun e => h e / ((q : ℚ) - a)) x₁ x₂ hM (isEffQDiv_add_of_isQCart X p hp Δ _ hΔ ⟨m', E₀, hm', hE₀, rfl⟩) …` and prove the remaining obligations. Introduce `y`. Rewrite using `[hB]`.

Conclude with `(GlobalTheory.T.kltAt_and_lcAt_antitone_coeff X p n hp hdim Δ (qWeil E₀ 1) (1 / (m' : ℚ)) c y ⟨1, E₀, one_pos, hE₀, rfl⟩ hmc).1 (hkltc y)`. Introduce `C hC`. Establish `h1` using `hcurve C hC`. Establish `dN'` using `deg_of_cls_eq hC hAmp hN'lb hA hNn.isLB 1 (q - a) (by rw [hclsN', one_nsmul])`. Establish `dK` using `hC.interNumRed_of_cls_eq_add hAmp (isLB_lbPow hNn.isLB a) hA (isLB_toLB E₀) (by rw [cls_lbPow hNn.isLB, hcls])`.

Rewrite `dK` using `[hC.interNumRed_lbPow hAmp hNn.isLB]`. Establish `dG` using `deg_of_cls_eq hC hAmp (isLB_toLB (m' • G + m • E₀)) (isLB_toLB G) (isLB_toLB E₀) m' m (by rw [← toPic_apply, ← toPic_apply, ← toPic_apply, map_add, map_nsmul, map_nsmul])`. Rewrite using `[h1, dN', dG]`. Establish `dK' : (a : ℚ) * interNumRed ℂ C ![N] = interNumRed ℂ C ![A] + interNumRed ℂ C ![toLB E₀]`. Conclude with `dK` after adjusting the coercions.

Establish `hm0 : (m : ℚ) ≠ 0` using `by exact_mod_cast hm.ne'`. Establish `hm0' : (m' : ℚ) ≠ 0` using `by exact_mod_cast hm'.ne'`. Use `push_cast`. Rewrite using `[hqa']`. Clear the denominators using the available nonvanishing facts.

Take the linear combination `(m : ℚ) * dK' - (m : ℚ) * (interNumRed ℂ C ![N] : ℚ) * hq`. Introduce `z e hze he hdz`. Establish `hmix` using `mixExp_interNumRed hNef ℂ X p hp N A (tens A (lbPow N (q - a))) hNn.isLB hA hN'lb (q - a) 1 (Closeds.closure {z}) e hNn hAmp.isNef (by rw [hclsN', one_nsmul, add_comm]) (by rw [Closeds.coe_closure]; exact hdz)`. Establish `key : ((q : ℚ) - a) ^ e * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N : ℤ) ≤ (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => tens A (lbPow N (q - a)) : ℤ)`. Use `(Int.cast_le (R := ℚ)).2 hmix` as an intermediate fact.

Move the coercions through the operations in `at this`. Rewrite `this` using `[hqa']`. Then use the resulting hypothesis. Establish `h0` using `hz z e hze he hdz`. Establish `e1 : h e ^ e * ((interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N : ℤ) : ℚ) = (h e / ((q : ℚ) - a)) ^ e * (((q : ℚ) - a) ^ e * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N : ℤ))`. Rewrite using `[div_pow]`.

Clear the denominators using the available nonvanishing facts. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Finset.sum_div, div_lt_div_iff₀ hqa (by exact_mod_cast hm')]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem separate_nef_big : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (M : LB X) (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (ρ : ℚ) (h : ℕ → ℚ) (x₁ x₂ : X), M.IsLB → IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsNef ℂ N → IsBig ℂ N → (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![M] : ℚ) = interNumRed ℂ C ![toLB G] / m + ρ * interNumRed ℂ C ![N]) → IsClosed ({x₁} : Set X) → IsClosed ({x₂} : Set X) → x₁ ≠ x₂ → (∀ e, 0 < h e) → (∀ (z : X) (e : ℕ), z ⤳ x₁ ∨ z ⤳ x₂ → 1 ≤ e → topologicalKrullDim (closure ({z} : Set X)) = e → 2 * (e : ℚ) ^ e < h e ^ e * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N : ℤ)) → ∑ e ∈ Finset.Icc 1 n, h e < ρ → 0 < ρ → ∃ s : M.Sec, (x₁ ∈ nonzeroLocus s ∧ x₂ ∉ nonzeroLocus s) ∨ (x₂ ∈ nonzeroLocus s ∧ x₁ ∉ nonzeroLocus s) := by
  intro hPr hNad hNef X _ _ _ p n hp hdim M Δ m G N ρ h x₁ x₂ hM hΔ hklt hm hG hNn hNb
    hcurve hx₁ hx₂ hne hh hz hsum hρ
  letI := algebraΓOfHom p
  obtain ⟨a, A, hA, E₀, ha, hAmp, hE₀, hcls⟩ :=
    GlobalTheory.T.exists_ample_add_effective_of_nef_big hNef X p hp N hNn.isLB hNn hNb
  obtain ⟨c, hc, hkltc⟩ := GlobalTheory.T.exists_pos_klt_add_smul_effective_divisor hPr X p n hp hdim Δ m G (qWeil E₀ 1) hm hG hklt
    ⟨1, E₀, one_pos, hE₀, rfl⟩
  have hS0 : 0 ≤ ∑ e ∈ Finset.Icc 1 n, h e := Finset.sum_nonneg fun e _ => (hh e).le
  obtain ⟨q, m', hm', hq, haq, hmc, hbud⟩ := exists_budget ρ _ c a hρ hsum hS0 hc
  have hNp := isLB_lbPow hNn.isLB (q - a)
  have hN'lb := isLB_tens hA hNp
  have hclsN' : cls _ hN'lb = cls A hA + (q - a) • cls N hNn.isLB := by
    rw [cls_tens hA hNp, cls_lbPow hNn.isLB]
  have hN'amp : IsAmpleLB (tens A (lbPow N (q - a))) :=
    IsAmpleLB.tens_of_isNef hNef ℂ X p hp A _ hAmp (hNn.pow hAmp _)
  have hqa : (0 : ℚ) < q - a := sub_pos.2 (by exact_mod_cast haq)
  have hqa' : (((q - a : ℕ) : ℚ)) = q - a := by rw [Nat.cast_sub haq.le]
  have hB : qWeil E₀ m' = (1 / (m' : ℚ)) • qWeil E₀ 1 := by
    funext z; simp [qWeil]; ring
  refine GlobalTheory.T.exists_section_separating_two_points_ample hPr hNad hNef X p n hp hdim M (Δ + qWeil E₀ m') (m * m') (m' • G + m • E₀)
    (tens A (lbPow N (q - a))) (1 / (m' : ℚ)) (fun e => h e / ((q : ℚ) - a)) x₁ x₂ hM
    (isEffQDiv_add_of_isQCart X p hp Δ _ hΔ ⟨m', E₀, hm', hE₀, rfl⟩) ?_ (Nat.mul_pos hm hm')
    (isLogCanonicalMultiple_add_qWeil X p n Δ m m' G E₀ hm hm' hG) hN'amp ?_ hx₁ hx₂ hne
    (fun e => div_pos (hh e) hqa) ?_ ?_
  · intro y
    rw [hB]
    exact (GlobalTheory.T.kltAt_and_lcAt_antitone_coeff X p n hp hdim Δ (qWeil E₀ 1) (1 / (m' : ℚ)) c y
      ⟨1, E₀, one_pos, hE₀, rfl⟩ hmc).1 (hkltc y)
  · intro C hC
    have h1 := hcurve C hC
    have dN' := deg_of_cls_eq hC hAmp hN'lb hA hNn.isLB 1 (q - a) (by rw [hclsN', one_nsmul])
    have dK := hC.interNumRed_of_cls_eq_add hAmp (isLB_lbPow hNn.isLB a) hA (isLB_toLB E₀)
      (by rw [cls_lbPow hNn.isLB, hcls])
    rw [hC.interNumRed_lbPow hAmp hNn.isLB] at dK
    have dG := deg_of_cls_eq hC hAmp (isLB_toLB (m' • G + m • E₀)) (isLB_toLB G) (isLB_toLB E₀)
      m' m (by rw [← toPic_apply, ← toPic_apply, ← toPic_apply, map_add, map_nsmul, map_nsmul])
    rw [h1, dN', dG]
    have dK' : (a : ℚ) * interNumRed ℂ C ![N] = interNumRed ℂ C ![A] + interNumRed ℂ C ![toLB E₀] := by
      exact_mod_cast dK
    have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    have hm0' : (m' : ℚ) ≠ 0 := by exact_mod_cast hm'.ne'
    push_cast
    rw [hqa']
    field_simp
    linear_combination (m : ℚ) * dK' - (m : ℚ) * (interNumRed ℂ C ![N] : ℚ) * hq
  · intro z e hze he hdz
    have hmix := mixExp_interNumRed hNef ℂ X p hp N A (tens A (lbPow N (q - a))) hNn.isLB hA hN'lb
      (q - a) 1 (Closeds.closure {z}) e hNn hAmp.isNef (by rw [hclsN', one_nsmul, add_comm])
      (by rw [Closeds.coe_closure]; exact hdz)
    have key : ((q : ℚ) - a) ^ e * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N : ℤ)
        ≤ (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => tens A (lbPow N (q - a)) : ℤ) := by
      have := (Int.cast_le (R := ℚ)).2 hmix
      push_cast at this
      rwa [hqa'] at this
    have h0 := hz z e hze he hdz
    have e1 : h e ^ e * ((interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N : ℤ) : ℚ) =
        (h e / ((q : ℚ) - a)) ^ e * (((q : ℚ) - a) ^ e *
          (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N : ℤ)) := by
      rw [div_pow]; field_simp
    calc 2 * (e : ℚ) ^ e < _ := h0
      _ = _ := e1
      _ ≤ _ := mul_le_mul_of_nonneg_left key (pow_nonneg (div_pos (hh e) hqa).le _)
  · rw [← Finset.sum_div, div_lt_div_iff₀ hqa (by exact_mod_cast hm')]
    linarith

end GlobalTheory.NefBigSep
