import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LogIntegralMultilinearStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelLogIntegralFormulaStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RationalWeightIntegralCoeffsStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CurveDegreeLinearNefConeStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionDivisorSupportStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionSectionBoundStatement

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace RootFieldNumerics.DegB

section Lines

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Use `contDiffOn_prod fun a _ => ?_` and prove the remaining obligations. Introduce `z hz`. Establish `h0 : (ℓ a).h z ≠ 0` using `((ℓ a).pos z hz).ne'`. Establish `hf` using `hℓ a z hz`. Consider the cases of `n a with`.

Consider the case `ofNat k => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hf.pow k`. Consider the case `negSucc k`. Simplify using `only [zpow_negSucc]`. Conclude with `(hf.pow (k + 1)).inv (pow_ne_zero _ h0)`.
-/
theorem smooth_comb {J : Type} [Fintype J] {ℓ : J → HermLine ι} (hℓ : ∀ j, IsSmoothHerm (ℓ j))
    (n : J → ℤ) : IsSmoothHerm (combLine ℓ n) := by
  refine contDiffOn_prod fun a _ => ?_
  intro z hz
  have h0 : (ℓ a).h z ≠ 0 := ((ℓ a).pos z hz).ne'
  have hf := hℓ a z hz
  cases n a with
  | ofNat k => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hf.pow k
  | negSucc k =>
    simp only [zpow_negSucc]
    exact (hf.pow (k + 1)).inv (pow_ne_zero _ h0)

/- English proof (translation)
Establish `h` using `(GlobalTheory.T.log_integral_multilinear II hII K ι W 1 J ℓ (fun _ => n) hW hℓ).1`. Unfold `geomDeg`. Rewrite using `[h]`. Use `Fintype.sum_equiv (Equiv.funUnique (Fin 1) J) _ _ fun w => ?_` and prove the remaining obligations. Establish `hw : ∀ k : Fin 1, w k = w default` using `fun k => by rw [Subsingleton.elim k default]`.

Simplify using `only [hw, Equiv.funUnique_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one]`.
-/
theorem geomDeg_comb (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) {J : Type} [Fintype J]
    {ℓ : J → HermLine ι} (hℓ : ∀ j, IsSmoothHerm (ℓ j)) (n : J → ℤ) (W : Ideal (MRing ι))
    (hW : IsArithVar W 2) :
    geomDeg W (combLine ℓ n) 1 = ∑ j, (n j : ℝ) * geomDeg W (ℓ j) 1 := by
  classical
  have h := (GlobalTheory.T.log_integral_multilinear II hII K ι W 1 J ℓ (fun _ => n) hW hℓ).1
  unfold geomDeg
  rw [h]
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) J) _ _ fun w => ?_
  have hw : ∀ k : Fin 1, w k = w default := fun k => by rw [Subsingleton.elim k default]
  simp only [hw, Equiv.funUnique_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one]

end Lines

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

/- English proof (translation)
Consider the cases of `r with`. Consider the case `none => exact M.A_smooth`. Consider the case `some r => exact M.x_smooth t r`.
-/
theorem smooth_line (M : RootModel Ψ N) (t : ℝ) (r : Option (Ψ × Fin N)) : IsSmoothHerm (M.line t r) := by
  cases r with
  | none => exact M.A_smooth
  | some r => exact M.x_smooth t r

/- English proof (translation)
Consider the cases of `j with`. Consider the case `none => simp only [RootModel.coef]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `some r => simp only [RootModel.coef, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coef_smul (M : RootModel Ψ N) (lam : Wt Ψ N) (s q : ℝ) (j : Option (Ψ × Fin N)) :
    M.coef (q • lam) (q * s) j = q * M.coef lam s j := by
  cases j with
  | none => simp only [RootModel.coef]; ring
  | some r => simp only [RootModel.coef, Pi.smul_apply, smul_eq_mul]; ring

/- English proof (translation)
Simplify using `only [linRoot, Pi.smul_apply, smul_eq_mul, map_mul, mul_neg, Finset.mul_sum, mul_assoc]`.
-/
theorem linRoot_smul (lam : Wt Ψ N) (q : ℝ) : linRoot (q • lam) = C q * linRoot lam := by
  simp only [linRoot, Pi.smul_apply, smul_eq_mul, map_mul, mul_neg, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Simplify using `only [linRoot, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem linRoot_sub (lam mu : Wt Ψ N) : linRoot (lam - mu) = linRoot lam - linRoot mu := by
  simp only [linRoot, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]
  ring

/- English proof (translation)
Simplify using `only [linA, toA, linRoot_smul, map_mul, rename_C]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem linA_smul (lam : Wt Ψ N) (s q : ℝ) : linA (q • lam) (q * s) = C q * linA lam s := by
  simp only [linA, toA, linRoot_smul, map_mul, rename_C]
  ring

/- English proof (translation)
Simplify using `only [linA, toA, linRoot_sub, linRoot_smul, map_mul, map_sub, rename_C, map_neg, map_one, map_zero]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem linA_diff (lam nu : Wt Ψ N) (s : ℝ) :
    linA lam 0 - linA (lam - s • nu) s = C s * linA nu (-1) := by
  simp only [linA, toA, linRoot_sub, linRoot_smul, map_mul, map_sub, rename_C, map_neg, map_one, map_zero]
  ring

/- English proof (translation)
Substitute `hD` using the available equality. Establish `h` using `GlobalTheory.T.root_model_log_integral_formula II hII Ψ N M 1 (fun k => (q k : ℝ) • lam k) (fun k => q k * s k) 1 n (fun k j => by rw [coef_smul, hn]; simp)`. Rewrite using `[h]`. Simplify using `only [linA_smul, Finset.prod_mul_distrib]`. Rewrite using `[← map_prod C, C_mul', map_smul]`.

Simplify using `only [Nat.cast_one, one_pow, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem geo_mixed (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) (M : RootModel Ψ N) (D : ℕ)
    (hD : dimFl Ψ N = D) (lam : Fin D → Wt Ψ N) (s : Fin D → ℝ) (q : Fin D → ℕ)
    (n : Fin D → Option (Ψ × Fin N) → ℤ) (hn : ∀ k j, (n k j : ℝ) = q k * M.coef (lam k) (s k) j) :
    ptsIntegral M.P (fun k z => Real.log ((combLine (M.line 1) (n k)).h z)) (fun _ => 1) =
      (M.δ * ∏ k, (q k : ℝ)) * M.geoFun (∏ k, linA (lam k) (s k)) := by
  subst hD
  have h := GlobalTheory.T.root_model_log_integral_formula II hII Ψ N M 1 (fun k => (q k : ℝ) • lam k) (fun k => q k * s k) 1 n
    (fun k j => by rw [coef_smul, hn]; simp)
  rw [h]
  simp only [linA_smul, Finset.prod_mul_distrib]
  rw [← map_prod C, C_mul', map_smul]
  simp only [Nat.cast_one, one_pow, smul_eq_mul]
  ring

/- English proof (translation)
Rewrite using `[geomDeg_comb II hII (smooth_line M 1) n W hW]`. Simplify using `only [hn, mul_assoc, ← Finset.mul_sum]`. Conclude with `mul_nonneg (Nat.cast_nonneg q) (h W hW hP)`.
-/
theorem nef_comb (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) (M : RootModel Ψ N)
    {lam : Wt Ψ N} {s : ℝ} {q : ℕ} {n : Option (Ψ × Fin N) → ℤ} (hn : ∀ j, (n j : ℝ) = q * M.coef lam s j)
    (h : M.NefGen lam s) (W : Ideal (MRing M.ι)) (hW : IsArithVar W 2) (hP : M.P ≤ W) :
    0 ≤ geomDeg W (combLine (M.line 1) n) 1 := by
  rw [geomDeg_comb II hII (smooth_line M 1) n W hW]
  simp only [hn, mul_assoc, ← Finset.mul_sum]
  exact mul_nonneg (Nat.cast_nonneg q) (h W hW hP)

/- English proof (translation)
Take `⟨j, rfl⟩` from `Nat.exists_eq_add_of_le hi`. Rewrite using `[Fin.prod_univ_add]`. Simplify using the standard rewrite rules.
-/
theorem prod_ite_lt {R : Type*} [CommMonoid R] (x y : R) (e i : ℕ) (hi : i ≤ e) :
    ∏ k : Fin e, (if (k : ℕ) < i then x else y) = x ^ i * y ^ (e - i) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [Fin.prod_univ_add]
  simp

section Main

variable (hK : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefFStatement)
  (hE : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
    ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement ℚ ι)
  (hS : ReciprocityTheory.ChartRestriction.G.Geo.DivSuppArithStatement) (II : IntersectionSystem) (hII : IsFullIntersectionSystem II)
include hK hE hS hII

/- English proof (translation)
Use `choose q n hq hn using fun k => GlobalTheory.T.rational_weight_integral_coeffs Ψ N M (lam k) (s k) (hr k)`. Establish `h1` using `geo_mixed II hII M _ rfl lam (fun k => s k) q n hn`. Establish `h2` using `GlobalTheory.T.ptsIntegral_log_nonneg hK hE hS II hII M.K M.ι M.P (dimFl Ψ N) (fun k => combLine (M.line 1) (n k)) M.arith (fun k => smooth_comb (smooth_line M 1) _) (fun k W hW hP => nef_comb II hII M (hn k) (hnef k) W hW hP)`. Rewrite `h2` using `[h1]`. Establish `hpos : (0 : ℝ) < M.δ * ∏ k, (q k : ℝ)` using `mul_pos (Nat.cast_pos.mpr M.δ_pos) (Finset.prod_pos fun k _ => Nat.cast_pos.mpr (hq k))`.

Conclude with `le_of_mul_le_mul_left (by simpa using h2) hpos`.
-/
theorem nef_prod (M : RootModel Ψ N) (lam : Fin (dimFl Ψ N) → Wt Ψ N) (s : Fin (dimFl Ψ N) → ℚ)
    (hr : ∀ k, IsRatWt (lam k)) (hnef : ∀ k, M.NefGen (lam k) (s k)) :
    0 ≤ M.geoFun (∏ k, linA (lam k) (s k)) := by
  choose q n hq hn using fun k => GlobalTheory.T.rational_weight_integral_coeffs Ψ N M (lam k) (s k) (hr k)
  have h1 := geo_mixed II hII M _ rfl lam (fun k => s k) q n hn
  have h2 := GlobalTheory.T.ptsIntegral_log_nonneg hK hE hS II hII M.K M.ι M.P (dimFl Ψ N) (fun k => combLine (M.line 1) (n k))
    M.arith (fun k => smooth_comb (smooth_line M 1) _)
    (fun k W hW hP => nef_comb II hII M (hn k) (hnef k) W hW hP)
  rw [h1] at h2
  have hpos : (0 : ℝ) < M.δ * ∏ k, (q k : ℝ) :=
    mul_pos (Nat.cast_pos.mpr M.δ_pos) (Finset.prod_pos fun k _ => Nat.cast_pos.mpr (hq k))
  exact le_of_mul_le_mul_left (by simpa using h2) hpos

/- English proof (translation)
Use `choose q n hq hn using fun k => GlobalTheory.T.rational_weight_integral_coeffs Ψ N M (lam k) (s k) (hr k)`. Take `⟨q0, n0, hq0, hn0, σ, hσ0, hσ⟩` from `hnu`. Establish `h1` using `geo_mixed II hII M (e + 1) he (Fin.snoc lam nu) (Fin.snoc (fun k => (s k : ℝ)) (-1)) (Fin.snoc q q0) (Fin.snoc n n0) (by`. Introduce `k j`. Use `Fin.lastCases ?_ (fun i => ?_) k` and prove the remaining obligations.

Simplify `hn0 j` using `only [Fin.snoc_last]`. Simplify `hn i j)` using `only [Fin.snoc_castSucc]`. Establish `har : IsArithVar (mCoordIdeal M.y) (e + 2)`. Use `M.arith` as an intermediate fact. Rewrite `this` using `[he]`. Then use the resulting hypothesis.

Establish `h2` using `GlobalTheory.T.arith_intersection_section_bound hK hE hS II hII M.K M.ι M.Ω M.y e (fun k => combLine (M.line 1) (n k)) (combLine (M.line 1) n0) σ har M.birational (fun k => smooth_comb (smooth_line M 1) _) (smooth_comb (smooth_line M 1) _) hσ0 hσ (fun k W hW hP => nef_comb II hII …`. Establish `h3 : (Fin.snoc (fun k => combLine (M.line 1) (n k)) (combLine (M.line 1) n0) : Fin (e + 1) → HermLine M.ι) = fun k => combLine (M.line 1) ((Fin.snoc n n0 : Fin (e + 1) → Option (Ψ × Fin N) → ℤ) k)`. Use function extensionality and compare the values at `k`. Use `Fin.lastCases ?_ (fun i => ?_) k` and prove the remaining obligations. Simplify using `only [Fin.snoc_last]`.

Simplify using `only [Fin.snoc_castSucc]`. Rewrite `h2` using `[h3]`. Establish `h4` using `h2.trans_eq h1`. Simplify using `only [Fin.prod_univ_castSucc, Fin.snoc_last, Fin.snoc_castSucc] at h4`. Establish `hpos : (0 : ℝ) < M.δ * ((∏ k, (q k : ℝ)) * q0)` using `mul_pos (Nat.cast_pos.mpr M.δ_pos) (mul_pos (Finset.prod_pos fun k _ => Nat.cast_pos.mpr (hq k)) (Nat.cast_pos.mpr hq0))`.

Conclude with `le_of_mul_le_mul_left (by simpa using h4) hpos`.
-/
theorem eff_prod (M : RootModel Ψ N) (e : ℕ) (he : dimFl Ψ N = e + 1) (lam : Fin e → Wt Ψ N) (s : Fin e → ℚ)
    (hr : ∀ k, IsRatWt (lam k)) (hnef : ∀ k, M.NefGen (lam k) (s k)) (nu : Wt Ψ N) (hnu : M.EffDiff nu) :
    0 ≤ M.geoFun ((∏ k, linA (lam k) (s k)) * linA nu (-1)) := by
  choose q n hq hn using fun k => GlobalTheory.T.rational_weight_integral_coeffs Ψ N M (lam k) (s k) (hr k)
  obtain ⟨q0, n0, hq0, hn0, σ, hσ0, hσ⟩ := hnu
  have h1 := geo_mixed II hII M (e + 1) he (Fin.snoc lam nu) (Fin.snoc (fun k => (s k : ℝ)) (-1))
    (Fin.snoc q q0) (Fin.snoc n n0) (by
      intro k j
      refine Fin.lastCases ?_ (fun i => ?_) k
      · simpa only [Fin.snoc_last] using hn0 j
      · simpa only [Fin.snoc_castSucc] using hn i j)
  have har : IsArithVar (mCoordIdeal M.y) (e + 2) := by
    have := M.arith
    rwa [he] at this
  have h2 := GlobalTheory.T.arith_intersection_section_bound hK hE hS II hII M.K M.ι M.Ω M.y e (fun k => combLine (M.line 1) (n k))
    (combLine (M.line 1) n0) σ har M.birational (fun k => smooth_comb (smooth_line M 1) _)
    (smooth_comb (smooth_line M 1) _) hσ0 hσ
    (fun k W hW hP => nef_comb II hII M (hn k) (hnef k) W hW hP)
  have h3 : (Fin.snoc (fun k => combLine (M.line 1) (n k)) (combLine (M.line 1) n0) :
      Fin (e + 1) → HermLine M.ι) = fun k =>
        combLine (M.line 1) ((Fin.snoc n n0 : Fin (e + 1) → Option (Ψ × Fin N) → ℤ) k) := by
    funext k
    refine Fin.lastCases ?_ (fun i => ?_) k
    · simp only [Fin.snoc_last]
    · simp only [Fin.snoc_castSucc]
  rw [h3] at h2
  have h4 := h2.trans_eq h1
  simp only [Fin.prod_univ_castSucc, Fin.snoc_last, Fin.snoc_castSucc] at h4
  have hpos : (0 : ℝ) < M.δ * ((∏ k, (q k : ℝ)) * q0) :=
    mul_pos (Nat.cast_pos.mpr M.δ_pos)
      (mul_pos (Finset.prod_pos fun k _ => Nat.cast_pos.mpr (hq k)) (Nat.cast_pos.mpr hq0))
  exact le_of_mul_le_mul_left (by simpa using h4) hpos

end Main

end RootFieldNumerics.DegB

open RootFieldNumerics.DegB in
/- English proof (translation)
Introduce `hK hE hS II hII Ψ _ _ N T hP h7 B c lam s hr hs hd hd'`. Take `⟨h71, h72, h73⟩` from `h7 B c`. Establish `hs' : (0 : ℝ) ≤ s` using `by exact_mod_cast hs`. Establish `hr' : IsRatWt (T.lamS lam s)`. Introduce `τ i`.

Take `⟨a, ha⟩` from `hr τ i`. Take `⟨b, hb⟩` from `T.nu_rat τ i`. Use `⟨a - s * b, ?_⟩` and prove the remaining obligations. Simplify using `only [RootTower.lamS, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ha, hb]`. Use `push_cast`.

Both sides reduce to the same expression. Establish `hnM : (T.M B c).NefGen (T.lamS lam s) s` using `(GlobalTheory.T.curve_degree_linear_nef_cone Ψ N (T.M B c) (T.lamS lam s) 0 s 0 0).2.2.2 hs' (h71 _ hd') h72`. Establish `hnL : (T.M B c).NefGen lam ((0 : ℚ) : ℝ)` using `by simpa using h71 _ hd`. Establish `hL : T.vol c * flagDeg lam = (T.M B c).geoFun (linA lam 0 ^ dimFl Ψ N)`. Rewrite using `[flagDeg, ← hP.2.1 B c]`.

Simplify using `[linA, toA]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `nef_prod hK hE hS II hII (T.M B c) (fun _ => T.lamS lam s) (fun _ => s) (fun _ => hr') (fun _ => hnM)` as an intermediate fact. Simplify `this` using `[RootTower.mDeg]`. Rewrite using `[hL, RootTower.mDeg, ← sub_nonneg, ← map_sub]`.

Break down `he : dimFl Ψ N with _ | e` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[← geom_sum₂_mul]`. Establish `hdiff : linA lam 0 - linA (T.lamS lam s) s = C (s : ℝ) * linA T.nu (-1)` using `linA_diff _ _ _`. Rewrite using `[hdiff, Finset.sum_mul, map_sum]`.

Use `Finset.sum_nonneg fun i hi => ?_` and prove the remaining obligations. Establish `hie : i ≤ e` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)`. Apply the tactic sequence `have h := eff_prod hK hE hS II hII (T.M B c) e he (fun k => if (k : ℕ) < i then lam else T.lamS lam s) (fun k => if (k : ℕ) < i then 0 else s) (fun k => by split_ifs <;> assumption) (fun k => by split_ifs <;> assumption) T.nu h73`. Establish `hp : ∏ k : Fin e, linA (if (k : ℕ) < i then lam else T.lamS lam s) ((if (k : ℕ) < i then 0 else s : ℚ) : ℝ) = linA lam 0 ^ i * linA (T.lamS lam s) s ^ (e - i)`. Rewrite using `[← prod_ite_lt _ _ e i hie]`.

Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`. Rewrite `h` using `[hp]`. Rewrite using `[mul_left_comm, C_mul', map_smul, smul_eq_mul]`. Conclude with `mul_nonneg hs' (by simpa using h)`.
-/
theorem RootFieldNumerics.tower_rational_weight_bound : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefFStatement → (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement ℚ ι) → ReciprocityTheory.ChartRestriction.G.Geo.DivSuppArithStatement → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N), T.Proportional → T.I7 → ∀ (B : ℕ) (c : T.Comp) (lam : Wt Ψ N) (s : ℚ), IsRatWt lam → 0 ≤ s → Dominant lam → Dominant (T.lamS lam s) → 0 ≤ T.mDeg B c lam s ∧ T.mDeg B c lam s ≤ T.vol c * flagDeg lam := by
  intro hK hE hS II hII Ψ _ _ N T hP h7 B c lam s hr hs hd hd'
  obtain ⟨h71, h72, h73⟩ := h7 B c
  have hs' : (0 : ℝ) ≤ s := by exact_mod_cast hs
  have hr' : IsRatWt (T.lamS lam s) := by
    intro τ i
    obtain ⟨a, ha⟩ := hr τ i
    obtain ⟨b, hb⟩ := T.nu_rat τ i
    refine ⟨a - s * b, ?_⟩
    simp only [RootTower.lamS, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ha, hb]
    push_cast
    rfl
  have hnM : (T.M B c).NefGen (T.lamS lam s) s :=
    (GlobalTheory.T.curve_degree_linear_nef_cone Ψ N (T.M B c) (T.lamS lam s) 0 s 0 0).2.2.2 hs' (h71 _ hd') h72
  have hnL : (T.M B c).NefGen lam ((0 : ℚ) : ℝ) := by simpa using h71 _ hd
  have hL : T.vol c * flagDeg lam = (T.M B c).geoFun (linA lam 0 ^ dimFl Ψ N) := by
    rw [flagDeg, ← hP.2.1 B c]
    simp [linA, toA]
  refine ⟨?_, ?_⟩
  · have := nef_prod hK hE hS II hII (T.M B c) (fun _ => T.lamS lam s) (fun _ => s) (fun _ => hr')
      (fun _ => hnM)
    simpa [RootTower.mDeg] using this
  · rw [hL, RootTower.mDeg, ← sub_nonneg, ← map_sub]
    rcases he : dimFl Ψ N with _ | e
    · simp
    · rw [← geom_sum₂_mul]
      have hdiff : linA lam 0 - linA (T.lamS lam s) s = C (s : ℝ) * linA T.nu (-1) := linA_diff _ _ _
      rw [hdiff, Finset.sum_mul, map_sum]
      refine Finset.sum_nonneg fun i hi => ?_
      have hie : i ≤ e := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have h := eff_prod hK hE hS II hII (T.M B c) e he
        (fun k => if (k : ℕ) < i then lam else T.lamS lam s) (fun k => if (k : ℕ) < i then 0 else s)
        (fun k => by split_ifs <;> assumption) (fun k => by split_ifs <;> assumption) T.nu h73
      have hp : ∏ k : Fin e, linA (if (k : ℕ) < i then lam else T.lamS lam s)
          ((if (k : ℕ) < i then 0 else s : ℚ) : ℝ) =
          linA lam 0 ^ i * linA (T.lamS lam s) s ^ (e - i) := by
        rw [← prod_ite_lt _ _ e i hie]
        refine Finset.prod_congr rfl fun k _ => ?_
        split_ifs <;> simp
      rw [hp] at h
      rw [mul_left_comm, C_mul', map_smul, smul_eq_mul]
      exact mul_nonneg hs' (by simpa using h)
