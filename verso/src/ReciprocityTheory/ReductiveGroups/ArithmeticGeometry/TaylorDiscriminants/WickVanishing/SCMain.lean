import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LiftXEqRename
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeBilinearTermEqNegDoubleSum

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

/- English proof (translation)
Establish `h0 : constantCoeff h = 0`. Establish `e` using `WickVanishing.coeff_ev_zero_left h 0`. Rewrite `e` using `[hc.ax0, Finsupp.embDomain_zero]`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, ← e, map_zero]`. Unfold `FB.hL`.

Rewrite using `[WickVanishing.gt_const_ev_eq _ ?_ h, h0]`. Introduce `j`. Use `fin_cases j`. Conclude with `WickVanishing.gp_pt 0`. Conclude with `WickVanishing.gp_comp1 _ _ (fun i => by simp [FB.actK, B.A.const]) (WickVanishing.gp_pt 0)`.
-/
theorem cc_hL (B : FB R d O) (h : PS k 2 d) (hc : B.IsCanonGauge k h) (w0 : O) :
    constantCoeff (B.hL k h w0) = 0 := by
  have h0 : constantCoeff h = 0 := by
    have e := WickVanishing.coeff_ev_zero_left h 0
    rw [hc.ax0, Finsupp.embDomain_zero] at e
    rw [← coeff_zero_eq_constantCoeff_apply, ← e, map_zero]
  unfold FB.hL
  rw [WickVanishing.gt_const_ev_eq _ ?_ h, h0]
  intro j
  fin_cases j
  · exact WickVanishing.gp_pt 0
  · exact WickVanishing.gp_comp1 _ _ (fun i => by simp [FB.actK, B.A.const]) (WickVanishing.gp_pt 0)

/- English proof (translation)
Introduce `R _ d O _ _ k _ _ _ hRQ J hJ1 B h hcg w0 hw0 m ι π _ _ _ c s ξh ψ hH hψ h11 h21 h12 P hPint e he f hf`. Use `set x := (m : k) • B.hL k h w0 with hx`. Establish `hx0 : constantCoeff x = 0`. Rewrite using `[hx, smul_eq_C_mul, map_mul, constantCoeff_C, cc_hL B h hcg w0, mul_zero]`. Use `set E0 := liftX k (FB.expS k x) with hE0def`.

Use `set E1 := liftX k (FB.expS k (-x)) with hE1def`. Establish `hE : E0 * E1 = 1`. Rewrite using `[hE0def, hE1def, ← liftX_mul, ← WickVanishing.gt_expS_add _ _ hx0 (by rw [map_neg, hx0, neg_zero]), add_neg_cancel, expS_zero', liftX_eq_rename, map_one]`. Establish `hE0 : constantCoeff E0 = 1` using `by rw [hE0def, cc_liftX, cc_expS _ hx0]`. Establish `hgood : ∀ l X, GoodE R E0 X → GoodE R E0 (nablaL B h m (ξh l).1 (ξh l).2 X)`.

Introduce and unpack `l X ⟨G, hG, rfl⟩`. Use `⟨E1 * nabla k B h m (ξh l).1 (ξh l).2 (E0 * G), hN1 R d O k hRQ B h hcg w0 hw0 m (ξh l) (hH l) G hG, ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_assoc, hE, one_mul]`. Both sides reduce to the same expression. Establish `hσ : GoodE R E0 (liftX k (FB.expS k x * f))` using `⟨liftX k f, intAA_liftX f hf, liftX_mul _ _⟩`.

Establish `haa : ∀ l l', s l = s l' → betaH k (ξh l) (ξh l') = 0` using `fun l l' e' => h11 l l' fun hh => hh.2 e'`. Establish `hab : ∀ l l', s l = s l' → betaH k (ξh l) (0, ψ l') = 0` using `fun l l' e' => h12 l l' fun hh => hh.2 e'`. Establish `hκ : ∀ l l', kapW m s ξh (fun l => (0, ψ l)) l l' ≠ 0 → c l = c l' ∧ s l = true ∧ s l' = false`. Introduce `l l' hne`. Take `⟨hs, hs'⟩` from `kapW_supp m s ξh _ l l' hne`.

Use `⟨?_, hs, hs'⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Apply `hne` to reduce the goal to its premises. Unfold `kapW`. Rewrite using `[if_pos ⟨hs, hs'⟩, h21 l l' (fun hh => hc hh.1), mul_zero]`.

Establish `hκJ : ∀ i j, kapE s (kapW m s ξh (fun l => (0, ψ l))) i j ∈ J`. Introduce `i j`. Unfold `kapE kapW`. Use `split_ifs`. Take `⟨u, φ, hu⟩` from `hH ((sideE s).symm (Sum.inr j))`.

Rewrite using `[hu]`. Unfold `betaH`. Simplify using `only [Pi.zero_apply, mul_zero, zero_sub]`. Rewrite using `[← nsmul_eq_mul]`. Use `J.toAddSubmonoid.nsmul_mem (J.sum_mem fun t _ => J.neg_mem ?_) m` and prove the remaining obligations.

Rewrite using `[mul_comm, ← Algebra.smul_def]`. Conclude with `J.smul_mem _ (hψ _ t)`. Conclude with `J.zero_mem`. Choose the witnesses or unpack the hypotheses as in `⟨P0, hP0⟩ : P ∈ Set.range (MvPolynomial.map (algebraMap R k)) := by`. Use `MvPolynomial.mem_range_map_iff_coeffs_subset.mpr fun a ha => ?_` and prove the remaining obligations.

Take `⟨n', _, rfl⟩` from `MvPolynomial.mem_coeffs_iff.mp ha`. Conclude with `RingHom.mem_range.mp (hPint n')`. Rewrite using `[ordNabla_wick hN2 hN3 B h m s ξh (fun l => (0, ψ l)) (fun _ => rfl) haa hab P (FB.expS k x * f), map_sum]`. Use `Submodule.sum_mem _ fun n _ => ?_` and prove the remaining obligations. Use `cc_ordEval_mem J e E0 hE0 (opL B h m s ξh) (opR B h m s ξh) (fun i => hgood _) (fun j => hgood _) _ hσ _ fun mo => ?_` and prove the remaining obligations.

Distinguish the cases in `hne : n ≤ e`. Use `pow_le_pow_right' (Submodule.one_le.mpr hJ1) hne ?_` and prove the remaining obligations. Establish `key` using `(_root_.divided_power_integrality R k _ _ J _ hκJ (MvPolynomial.rename (sideE s) P0) n).1 mo`. Rewrite using `[← delta_pow_rename s _ (kapW_supp m s ξh _) n P, ← hP0, ← MvPolynomial.map_rename]`. Conclude with `key`.

Rewrite using `[secondOrder_iterate_eq_zero c s _ hκ P e he n (by omega), map_zero, smul_zero, MvPolynomial.coeff_zero]`. Conclude with `Submodule.zero_mem _`.
-/
theorem sc_of (hN1 : ConnectionIntegrality) (hN2 : ConnectionCommutator) (hN3 : ConnectionKillsSeries) : SCSt := by
  intro R _ d O _ _ k _ _ _ hRQ J hJ1 B h hcg w0 hw0 m ι π _ _ _ c s ξh ψ hH hψ h11 h21 h12 P hPint e he f hf
  set x := (m : k) • B.hL k h w0 with hx
  have hx0 : constantCoeff x = 0 := by
    rw [hx, smul_eq_C_mul, map_mul, constantCoeff_C, cc_hL B h hcg w0, mul_zero]
  set E0 := liftX k (FB.expS k x) with hE0def
  set E1 := liftX k (FB.expS k (-x)) with hE1def
  have hE : E0 * E1 = 1 := by
    rw [hE0def, hE1def, ← liftX_mul, ← WickVanishing.gt_expS_add _ _ hx0 (by rw [map_neg, hx0, neg_zero]),
      add_neg_cancel, expS_zero', liftX_eq_rename, map_one]
  have hE0 : constantCoeff E0 = 1 := by rw [hE0def, cc_liftX, cc_expS _ hx0]
  have hgood : ∀ l X, GoodE R E0 X → GoodE R E0 (nablaL B h m (ξh l).1 (ξh l).2 X) := by
    rintro l X ⟨G, hG, rfl⟩
    refine ⟨E1 * nabla k B h m (ξh l).1 (ξh l).2 (E0 * G),
      hN1 R d O k hRQ B h hcg w0 hw0 m (ξh l) (hH l) G hG, ?_⟩
    rw [← mul_assoc, hE, one_mul]
    rfl
  have hσ : GoodE R E0 (liftX k (FB.expS k x * f)) := ⟨liftX k f, intAA_liftX f hf, liftX_mul _ _⟩
  have haa : ∀ l l', s l = s l' → betaH k (ξh l) (ξh l') = 0 := fun l l' e' => h11 l l' fun hh => hh.2 e'
  have hab : ∀ l l', s l = s l' → betaH k (ξh l) (0, ψ l') = 0 := fun l l' e' => h12 l l' fun hh => hh.2 e'
  have hκ : ∀ l l', kapW m s ξh (fun l => (0, ψ l)) l l' ≠ 0 → c l = c l' ∧ s l = true ∧ s l' = false := by
    intro l l' hne
    obtain ⟨hs, hs'⟩ := kapW_supp m s ξh _ l l' hne
    refine ⟨?_, hs, hs'⟩
    by_contra hc
    apply hne
    unfold kapW
    rw [if_pos ⟨hs, hs'⟩, h21 l l' (fun hh => hc hh.1), mul_zero]
  have hκJ : ∀ i j, kapE s (kapW m s ξh (fun l => (0, ψ l))) i j ∈ J := by
    intro i j
    unfold kapE kapW
    split_ifs
    · obtain ⟨u, φ, hu⟩ := hH ((sideE s).symm (Sum.inr j))
      rw [hu]
      unfold betaH
      simp only [Pi.zero_apply, mul_zero, zero_sub]
      rw [← nsmul_eq_mul]
      refine J.toAddSubmonoid.nsmul_mem (J.sum_mem fun t _ => J.neg_mem ?_) m
      rw [mul_comm, ← Algebra.smul_def]
      exact J.smul_mem _ (hψ _ t)
    · exact J.zero_mem
  obtain ⟨P0, hP0⟩ : P ∈ Set.range (MvPolynomial.map (algebraMap R k)) := by
    refine MvPolynomial.mem_range_map_iff_coeffs_subset.mpr fun a ha => ?_
    obtain ⟨n', _, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp ha
    exact RingHom.mem_range.mp (hPint n')
  rw [ordNabla_wick hN2 hN3 B h m s ξh (fun l => (0, ψ l)) (fun _ => rfl) haa hab P (FB.expS k x * f), map_sum]
  refine Submodule.sum_mem _ fun n _ => ?_
  refine cc_ordEval_mem J e E0 hE0 (opL B h m s ξh) (opR B h m s ξh) (fun i => hgood _) (fun j => hgood _) _ hσ _
    fun mo => ?_
  by_cases hne : n ≤ e
  · refine pow_le_pow_right' (Submodule.one_le.mpr hJ1) hne ?_
    have key := (_root_.divided_power_integrality R k _ _ J _ hκJ (MvPolynomial.rename (sideE s) P0) n).1 mo
    rw [← delta_pow_rename s _ (kapW_supp m s ξh _) n P, ← hP0, ← MvPolynomial.map_rename]
    exact key
  · rw [secondOrder_iterate_eq_zero c s _ hκ P e he n (by omega), map_zero, smul_zero, MvPolynomial.coeff_zero]
    exact Submodule.zero_mem _

end ReciprocityTheory.ChartRestriction.G.TB.SCPf
