import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ApplyLayers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPowSubOneOfNotDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLevelExpansionLawsOfRootsOfUnity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingsCyclotomic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLevelExpansionAtRootOfUnity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachWeierstrassTestAndDensity
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.NL.WachMat

section Series

open PowerSeries

variable {L : Type} [Field L] {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul, coeff_zero_eq_constantCoeff_apply]`.
-/
theorem constantCoeff_rescale' (u : L) (f : L⟦X⟧) : constantCoeff (rescale u f) = constantCoeff f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul, coeff_zero_eq_constantCoeff_apply]

/- English proof (translation)
Rewrite `h`, the goal using `[X_pow_dvd_iff]`. Introduce `m hm`. Rewrite using `[coeff_rescale, h m hm, mul_zero]`.
-/
theorem X_pow_dvd_rescale (u : L) (f : L⟦X⟧) (a : ℕ) (h : X ^ a ∣ f) : X ^ a ∣ rescale u f := by
  rw [X_pow_dvd_iff] at h ⊢
  intro m hm
  rw [coeff_rescale, h m hm, mul_zero]

/- English proof (translation)
Use extensionality with `i j`. Use `X_dvd_iff.1 (hG i j)` as an intermediate fact. Rewrite `this` using `[Matrix.sub_apply, map_sub, sub_eq_zero]`. Rewrite using `[Matrix.map_apply, this, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem map_constantCoeff_eq_one (G : Matrix ι ι L⟦X⟧) (hG : ∀ i j, X ∣ (G - 1) i j) :
    G.map (constantCoeff (R := L)) = 1 := by
  ext i j
  have := X_dvd_iff.1 (hG i j)
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
  rw [Matrix.map_apply, this, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

/- English proof (translation)
Establish `key : ∀ k, k ≤ a → ∀ i j, X ^ k ∣ B i j`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro _ i j`. Simplify using the standard rewrite rules.

Consider the case `succ k ih`. Introduce `hk i j`. Use `choose B' hB' using ih (by omega)`. Establish `hB : B = (X : L⟦X⟧) ^ k • Matrix.of B'` using `by ext1 i j; rw [hB']; rfl`. Establish `hBu : B.map (rescale u) = ((C u) ^ k * (X : L⟦X⟧) ^ k) • (Matrix.of B').map (rescale u)` using `by ext1 i j`.

Rewrite using `[Matrix.map_apply, hB', map_mul, map_pow, rescale_X, mul_pow]`. Both sides reduce to the same expression. Rewrite `h` using `[hBu]`. Rewrite `h` using `[hB]`. Simplify using `only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, map_mul, rescale_X] at h`.

Establish `h1` using `congrFun (congrFun h i) j`. Simplify using `only [Matrix.smul_apply, smul_eq_mul] at h1`. Establish `h2 : w ^ a * C u ^ k * (G * (Matrix.of B').map (rescale u)) i j = C u ^ a * rescale u w ^ a * (Matrix.of B' * G₁) i j`. Apply `mul_left_cancel₀ (pow_ne_zero (a + k) (X_ne_zero (R := L)))` to reduce the goal to its premises. Take the linear combination `h1`.

Establish `h3` using `congrArg (constantCoeff (R := L)) h2`. Establish `e1 : constantCoeff ((G * (Matrix.of B').map (rescale u)) i j) = constantCoeff (B' i j)`. Rewrite using `[← Matrix.map_apply (f := constantCoeff (R := L)), Matrix.map_mul, map_constantCoeff_eq_one G hG, Matrix.one_mul, Matrix.map_apply, Matrix.map_apply, constantCoeff_rescale']`. Both sides reduce to the same expression. Establish `e2 : constantCoeff ((Matrix.of B' * G₁) i j) = constantCoeff (B' i j)`.

Rewrite using `[← Matrix.map_apply (f := constantCoeff (R := L)), Matrix.map_mul, map_constantCoeff_eq_one G₁ hG₁, Matrix.mul_one, Matrix.map_apply]`. Both sides reduce to the same expression. Simplify using `only [map_mul, map_pow, constantCoeff_C, constantCoeff_rescale', e1, e2] at h3`. Establish `hw0 : constantCoeff w ≠ 0` using `(isUnit_iff_constantCoeff.1 hw).ne_zero`. Take `⟨d, rfl⟩ : ∃ d, a = k + (d + 1)` from `⟨a - (k + 1), by omega⟩`.

Establish `h4 : (constantCoeff w ^ (k + (d + 1)) * u ^ k * (u ^ (d + 1) - 1)) * constantCoeff (B' i j) = 0`. Take the linear combination `-h3`. Establish `h5 : constantCoeff (B' i j) = 0` using `(mul_eq_zero.1 h4).resolve_left (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hw0) (pow_ne_zero _ hu0)) (sub_ne_zero.2 (hu _ (by omega))))`. Rewrite using `[hB', pow_succ]`. Conclude with `mul_dvd_mul_left _ (X_dvd_iff.2 h5)`.

Conclude with `key a le_rfl`.
-/
theorem X_pow_dvd_of_rescale (u : L) (hu0 : u ≠ 0) (hu : ∀ n : ℕ, n ≠ 0 → u ^ n ≠ 1) (w : L⟦X⟧) (hw : IsUnit w)
    (a : ℕ) (B G G₁ : Matrix ι ι L⟦X⟧) (hG : ∀ i j, X ∣ (G - 1) i j) (hG₁ : ∀ i j, X ∣ (G₁ - 1) i j)
    (h : (X * w) ^ a • (G * B.map (rescale u)) = (rescale u (X * w)) ^ a • (B * G₁)) :
    ∀ i j, X ^ a ∣ B i j := by
  have key : ∀ k, k ≤ a → ∀ i j, X ^ k ∣ B i j := by
    intro k
    induction k with
    | zero => intro _ i j; simp
    | succ k ih =>
      intro hk i j
      choose B' hB' using ih (by omega)
      have hB : B = (X : L⟦X⟧) ^ k • Matrix.of B' := by
        ext1 i j; rw [hB']; rfl
      have hBu : B.map (rescale u) = ((C u) ^ k * (X : L⟦X⟧) ^ k) • (Matrix.of B').map (rescale u) := by
        ext1 i j
        rw [Matrix.map_apply, hB', map_mul, map_pow, rescale_X, mul_pow]; rfl
      rw [hBu] at h
      rw [hB] at h
      simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, map_mul, rescale_X] at h
      have h1 := congrFun (congrFun h i) j
      simp only [Matrix.smul_apply, smul_eq_mul] at h1
      have h2 : w ^ a * C u ^ k * (G * (Matrix.of B').map (rescale u)) i j
          = C u ^ a * rescale u w ^ a * (Matrix.of B' * G₁) i j := by
        apply mul_left_cancel₀ (pow_ne_zero (a + k) (X_ne_zero (R := L)))
        linear_combination h1
      have h3 := congrArg (constantCoeff (R := L)) h2
      have e1 : constantCoeff ((G * (Matrix.of B').map (rescale u)) i j) = constantCoeff (B' i j) := by
        rw [← Matrix.map_apply (f := constantCoeff (R := L)), Matrix.map_mul, map_constantCoeff_eq_one G hG,
          Matrix.one_mul, Matrix.map_apply, Matrix.map_apply, constantCoeff_rescale']
        rfl
      have e2 : constantCoeff ((Matrix.of B' * G₁) i j) = constantCoeff (B' i j) := by
        rw [← Matrix.map_apply (f := constantCoeff (R := L)), Matrix.map_mul, map_constantCoeff_eq_one G₁ hG₁,
          Matrix.mul_one, Matrix.map_apply]
        rfl
      simp only [map_mul, map_pow, constantCoeff_C, constantCoeff_rescale', e1, e2] at h3
      have hw0 : constantCoeff w ≠ 0 := (isUnit_iff_constantCoeff.1 hw).ne_zero
      obtain ⟨d, rfl⟩ : ∃ d, a = k + (d + 1) := ⟨a - (k + 1), by omega⟩
      have h4 : (constantCoeff w ^ (k + (d + 1)) * u ^ k * (u ^ (d + 1) - 1)) * constantCoeff (B' i j) = 0 := by
        linear_combination -h3
      have h5 : constantCoeff (B' i j) = 0 :=
        (mul_eq_zero.1 h4).resolve_left (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hw0) (pow_ne_zero _ hu0))
          (sub_ne_zero.2 (hu _ (by omega))))
      rw [hB', pow_succ]
      exact mul_dvd_mul_left _ (X_dvd_iff.2 h5)
  exact key a le_rfl

end Series

/- English proof (translation)
Rewrite using `[h2, Matrix.smul_mul, Matrix.mul_assoc, h1, Matrix.mul_smul, Matrix.mul_one, smul_smul, pow_add]`.
-/
theorem pow_smul_eq {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι] (Q : R) (m m' : ℕ)
    (B B' Pm P₁ P₁' : Matrix ι ι R) (h1 : P₁ * P₁' = (Q ^ m') • (1 : Matrix ι ι R))
    (h2 : Pm * B' = (Q ^ m) • (B * P₁)) : Q ^ (m + m') • B = Pm * B' * P₁' := by
  rw [h2, Matrix.smul_mul, Matrix.mul_assoc, h1, Matrix.mul_smul, Matrix.mul_one, smul_smul, pow_add]

/- English proof (translation)
Establish `h1` using `congrArg f (congrFun (congrFun h i) j)`. Rewrite `h1` using `[Matrix.smul_apply, smul_eq_mul, map_mul, map_pow]`. Rewrite using `[← (hQ.pow m).dvd_mul_left, h1, Matrix.mul_apply, map_sum]`. Use `Finset.dvd_sum fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, Matrix.mul_apply, map_sum]`.

Use `Dvd.dvd.mul_right (Finset.dvd_sum fun k' _ => ?_) _` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `(hx _ _).mul_left _`.
-/
theorem dvd_map_of_pow_smul_eq {R S ι : Type} [CommRing R] [CommRing S] [Fintype ι] (f : R →+* S) (Q : R)
    (hQ : IsUnit (f Q)) (m : ℕ) (B B' Pm P₁' : Matrix ι ι R) (h : Q ^ m • B = Pm * B' * P₁') (x : S)
    (hx : ∀ i j, x ∣ f (B' i j)) (i j : ι) : x ∣ f (B i j) := by
  have h1 := congrArg f (congrFun (congrFun h i) j)
  rw [Matrix.smul_apply, smul_eq_mul, map_mul, map_pow] at h1
  rw [← (hQ.pow m).dvd_mul_left, h1, Matrix.mul_apply, map_sum]
  refine Finset.dvd_sum fun k _ => ?_
  rw [map_mul, Matrix.mul_apply, map_sum]
  refine Dvd.dvd.mul_right (Finset.dvd_sum fun k' _ => ?_) _
  rw [map_mul]
  exact (hx _ _).mul_left _

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `D HW l hl K s LL h W r a m m' B G G₁ Pm P₁ P₁' hG hG₁ hγ hP hφ`. Take `⟨Lγ, Lφ⟩ : LevLaws W` from `GlobalTheory.NL.Expansion.levLaws D HW l K s LL h`. Establish `Lp` using `GlobalTheory.NL.lev_at_root_of_unity D HW l K s LL h`. Take `⟨χ, hχ, -, -, -, -, hgam, -⟩` from `GlobalTheory.NL.CycRing.rings_cyclotomic D HW l K s LL h`. Take `⟨-, Wd, -⟩` from `GlobalTheory.NL.WDiv.weierstrass_dense D HW l K s LL h`.

Establish `hp : ((D.loc l).PD K).p = l` using `(D.loc l).PD_p K`. Rewrite `Lγ`, `Lφ` using `[hp]`. Establish `hroot : ∀ (j : ℕ) (ζ : ↥LL.1), ζ ^ (l ^ j) = 1 → ∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)`. Introduce `j ζ h1`. Take `⟨k, -, hk⟩` from `(Nat.dvd_prime_pow hl.out).1 (orderOf_dvd_of_pow_eq_one h1)`.

Conclude with `⟨k, hk ▸ IsPrimitiveRoot.orderOf ζ⟩`. Use `set u : ↥LL.1 := algebraMap ↥(OL LL) ↥LL.1 (W.χΓ W.gam : ↥(OL LL)) with hudef`. Establish `hu0 : u ≠ 0` using `((W.χΓ W.gam).isUnit.map (algebraMap ↥(OL LL) ↥LL.1)).ne_zero`. Establish `hu : ∀ n : ℕ, n ≠ 0 → u ^ n ≠ 1`. Introduce `n hn h1`.

Establish `h2` using `GlobalTheory.Cyc.norm_unit_zpow_sub_one l s (χ W.gam) h.1 h.2.1 hgam n (by exact_mod_cast hn)`. Establish `h3 : ((χ W.gam : ℤ_[l]ˣ) : ℤ_[l]) ^ n = 1`. Establish `inj : Function.Injective (algebraMap ℤ_[l] ↥LL.1)`. Rewrite using `[IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥LL.1]`. Conclude with `(algebraMap ℚ_[l] ↥LL.1).injective.comp Subtype.val_injective`.

Apply `inj` to reduce the goal to its premises. Rewrite using `[map_pow, map_one, IsScalarTower.algebraMap_apply ℤ_[l] ↥(OL LL) ↥LL.1, hχ]`. Conclude with `h1`. Rewrite `h2` using `[zpow_natCast, Units.val_pow_eq_pow_val, h3, sub_self, norm_zero]`. Establish `hl0 : (0 : ℝ) < l` using `by exact_mod_cast hl.out.pos`.

Use `mul_ne_zero (zpow_pos hl0 _).ne' (norm_ne_zero_iff.2 ?_) h2.symm` and prove the remaining obligations. Conclude with `hn` after adjusting the coercions. Establish `base : ∀ (i : Let K) p q, PowerSeries.X ^ a ∣ W.lev i 1 (B p q)`. Introduce `i`. Establish `r1 : IsPrimitiveRoot (1 : ↥LL.1) (l ^ 0)`.

Rewrite using `[pow_zero]`. Conclude with `IsPrimitiveRoot.one`. Take `⟨⟨x, -, hx, w₀, -, hπ⟩, -, hX, -⟩` from `Lp i 1 ⟨0, r1⟩`. Take `⟨⟨w, hw, hX⟩, -⟩` from `hX (one_pow _)`. Rewrite `hπ` using `[hx, sub_self, map_zero, zero_add]`.

Establish `hγ1 : ∀ f, W.lev i 1 (W.γA W.gam f) = PowerSeries.rescale u (W.lev i 1 f)`. Use `Lγ W.gam i 1 1 0 1 r1 ?_ (one_pow _).symm` and prove the remaining obligations. Rewrite using `[Nat.cast_one, W.gam_gen]`. Conclude with `Nat.zero_le _` after adjusting the coercions. Establish `hone : ∀ G : Matrix (Fin r) (Fin r) (AA K LL), (∀ p q, (G - 1) p q ∈ Ideal.span {(letπ : AA K LL)}) → ∀ p q, PowerSeries.X ∣ (G.map (W.lev i 1) - 1) p q`.

Introduce `G hG p q`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton.1 (hG p q)`. Establish `e : (G.map (W.lev i 1) - 1) p q = W.lev i 1 ((G - 1) p q)`. Rewrite using `[Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Rewrite using `[e, hc, map_mul, hπ, mul_assoc]`. Conclude with `dvd_mul_right _ _`. Use `X_pow_dvd_of_rescale u hu0 hu w hw a (B.map (W.lev i 1)) (G.map (W.lev i 1)) (G₁.map (W.lev i 1)) (hone G hG) (hone G₁ hG₁) ?_` and prove the remaining obligations. Use `ext1 p q`. Establish `h1` using `congrArg (W.lev i 1) (congrFun (congrFun hγ p) q)`.

Simplify using `only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.map_apply, map_mul, map_pow, map_sum, hγ1] at h1`. Simplify using `only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.map_apply, ← hX]`. Conclude with `h1`. Establish `hB` using `pow_smul_eq W.Q m m' B (B.map W.φA) Pm P₁ P₁' hP hφ`. Establish `step : ∀ j : ℕ, j ≤ s - 1 → ∀ (i : Let K) (ζ : ↥LL.1), ζ ^ (l ^ j) = 1 → ∀ p q, PowerSeries.X ^ a ∣ W.lev i ζ (B p q)`.

Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`. Introduce `_ i ζ hζ`. Rewrite `hζ` using `[pow_zero, pow_one]`.

Substitute `hζ` using the available equality. Conclude with `base i`. Consider the case `succ j ih`. Introduce `hj i ζ hζ`. Establish `hr` using `hroot _ ζ hζ`.

Establish `hζ' : ζ ^ (l ^ (s - 1)) = 1`. Take `⟨d, hd⟩` from `Nat.exists_eq_add_of_le hj`. Rewrite using `[hd, pow_add, pow_mul, hζ, one_pow]`. Take `⟨-, -, hX, -⟩` from `Lp i ζ hr`. Take `⟨-, hQ⟩` from `hX hζ'`.

Use `dvd_map_of_pow_smul_eq (W.lev i ζ : AA K LL →+* PowerSeries ↥LL.1) W.Q hQ _ B _ Pm P₁' hB _ fun p q => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ ∣ W.lev i ζ (W.φA (B p q))`. Rewrite using `[Lφ i ζ hr]`. Use `X_pow_dvd_rescale _ _ _ (ih (by omega) _ _ ?_ p q)` and prove the remaining obligations. Rewrite using `[← pow_mul, ← pow_succ', hζ]`.

Introduce `p q`. Use `Wd a (B p q) fun i ζ hζ => ?_` and prove the remaining obligations. Conclude with `Ideal.mem_comap.2 (Ideal.mem_span_singleton.2 (step _ le_rfl i ζ hζ p q))`.
-/
theorem X_pow_dvd_entry : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (r a m m' : ℕ) (B G G₁ Pm P₁ P₁' : Matrix (Fin r) (Fin r) (AA K LL)), (∀ i j, (G - 1) i j ∈ Ideal.span {(letπ : AA K LL)}) → (∀ i j, (G₁ - 1) i j ∈ Ideal.span {(letπ : AA K LL)}) → (W.X ^ a) • (G * B.map (W.γA W.gam)) = (W.γA W.gam W.X ^ a) • (B * G₁) → P₁ * P₁' = (W.Q ^ m') • (1 : Matrix (Fin r) (Fin r) (AA K LL)) → Pm * B.map W.φA = (W.Q ^ m) • (B * P₁) → ∀ i j, W.X ^ a ∣ B i j := by
  intro D HW l hl K s LL h W r a m m' B G G₁ Pm P₁ P₁' hG hG₁ hγ hP hφ
  obtain ⟨Lγ, Lφ⟩ : LevLaws W := GlobalTheory.NL.Expansion.levLaws D HW l K s LL h
  have Lp := GlobalTheory.NL.lev_at_root_of_unity D HW l K s LL h
  obtain ⟨χ, hχ, -, -, -, -, hgam, -⟩ := GlobalTheory.NL.CycRing.rings_cyclotomic D HW l K s LL h
  obtain ⟨-, Wd, -⟩ := GlobalTheory.NL.WDiv.weierstrass_dense D HW l K s LL h
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  rw [hp] at Lγ Lφ
  have hroot : ∀ (j : ℕ) (ζ : ↥LL.1), ζ ^ (l ^ j) = 1 → ∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j) := by
    intro j ζ h1
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hl.out).1 (orderOf_dvd_of_pow_eq_one h1)
    exact ⟨k, hk ▸ IsPrimitiveRoot.orderOf ζ⟩
  set u : ↥LL.1 := algebraMap ↥(OL LL) ↥LL.1 (W.χΓ W.gam : ↥(OL LL)) with hudef
  have hu0 : u ≠ 0 := ((W.χΓ W.gam).isUnit.map (algebraMap ↥(OL LL) ↥LL.1)).ne_zero
  have hu : ∀ n : ℕ, n ≠ 0 → u ^ n ≠ 1 := by
    intro n hn h1
    have h2 := GlobalTheory.Cyc.norm_unit_zpow_sub_one l s (χ W.gam) h.1 h.2.1 hgam n (by exact_mod_cast hn)
    have h3 : ((χ W.gam : ℤ_[l]ˣ) : ℤ_[l]) ^ n = 1 := by
      have inj : Function.Injective (algebraMap ℤ_[l] ↥LL.1) := by
        rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥LL.1]
        exact (algebraMap ℚ_[l] ↥LL.1).injective.comp Subtype.val_injective
      apply inj
      rw [map_pow, map_one, IsScalarTower.algebraMap_apply ℤ_[l] ↥(OL LL) ↥LL.1, hχ]
      exact h1
    rw [zpow_natCast, Units.val_pow_eq_pow_val, h3, sub_self, norm_zero] at h2
    have hl0 : (0 : ℝ) < l := by exact_mod_cast hl.out.pos
    refine mul_ne_zero (zpow_pos hl0 _).ne' (norm_ne_zero_iff.2 ?_) h2.symm
    exact_mod_cast hn
  have base : ∀ (i : Let K) p q, PowerSeries.X ^ a ∣ W.lev i 1 (B p q) := by
    intro i
    have r1 : IsPrimitiveRoot (1 : ↥LL.1) (l ^ 0) := by
      rw [pow_zero]; exact IsPrimitiveRoot.one
    obtain ⟨⟨x, -, hx, w₀, -, hπ⟩, -, hX, -⟩ := Lp i 1 ⟨0, r1⟩
    obtain ⟨⟨w, hw, hX⟩, -⟩ := hX (one_pow _)
    rw [hx, sub_self, map_zero, zero_add] at hπ
    have hγ1 : ∀ f, W.lev i 1 (W.γA W.gam f) = PowerSeries.rescale u (W.lev i 1 f) := by
      refine Lγ W.gam i 1 1 0 1 r1 ?_ (one_pow _).symm
      rw [Nat.cast_one, W.gam_gen]
      exact_mod_cast Nat.zero_le _
    have hone : ∀ G : Matrix (Fin r) (Fin r) (AA K LL), (∀ p q, (G - 1) p q ∈ Ideal.span {(letπ : AA K LL)}) →
        ∀ p q, PowerSeries.X ∣ (G.map (W.lev i 1) - 1) p q := by
      intro G hG p q
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (hG p q)
      have e : (G.map (W.lev i 1) - 1) p q = W.lev i 1 ((G - 1) p q) := by
        rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
        split_ifs <;> simp
      rw [e, hc, map_mul, hπ, mul_assoc]
      exact dvd_mul_right _ _
    refine X_pow_dvd_of_rescale u hu0 hu w hw a (B.map (W.lev i 1)) (G.map (W.lev i 1)) (G₁.map (W.lev i 1))
      (hone G hG) (hone G₁ hG₁) ?_
    ext1 p q
    have h1 := congrArg (W.lev i 1) (congrFun (congrFun hγ p) q)
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.map_apply, map_mul, map_pow, map_sum,
      hγ1] at h1
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.map_apply, ← hX]
    exact h1
  have hB := pow_smul_eq W.Q m m' B (B.map W.φA) Pm P₁ P₁' hP hφ
  have step : ∀ j : ℕ, j ≤ s - 1 → ∀ (i : Let K) (ζ : ↥LL.1), ζ ^ (l ^ j) = 1 → ∀ p q,
      PowerSeries.X ^ a ∣ W.lev i ζ (B p q) := by
    intro j
    induction j with
    | zero =>
      intro _ i ζ hζ
      rw [pow_zero, pow_one] at hζ
      subst hζ
      exact base i
    | succ j ih =>
      intro hj i ζ hζ
      have hr := hroot _ ζ hζ
      have hζ' : ζ ^ (l ^ (s - 1)) = 1 := by
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hj
        rw [hd, pow_add, pow_mul, hζ, one_pow]
      obtain ⟨-, -, hX, -⟩ := Lp i ζ hr
      obtain ⟨-, hQ⟩ := hX hζ'
      refine dvd_map_of_pow_smul_eq (W.lev i ζ : AA K LL →+* PowerSeries ↥LL.1) W.Q hQ _ B _ Pm P₁' hB _ fun p q => ?_
      change _ ∣ W.lev i ζ (W.φA (B p q))
      rw [Lφ i ζ hr]
      refine X_pow_dvd_rescale _ _ _ (ih (by omega) _ _ ?_ p q)
      rw [← pow_mul, ← pow_succ', hζ]
  intro p q
  refine Wd a (B p q) fun i ζ hζ => ?_
  exact Ideal.mem_comap.2 (Ideal.mem_span_singleton.2 (step _ le_rfl i ζ hζ p q))

end GlobalTheory.NL.WachMat
