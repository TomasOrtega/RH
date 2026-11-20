import Formalism.EllipticTorsion.WChordSeries

open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL.WeierstrassSubstitution

/- English proof (translation)
Establish `ha' : MvPowerSeries.HasSubst (fun _ : Unit => a)` using `MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => ha`. Unfold `PowerSeries.subst`. Rewrite using `[MvPowerSeries.subst_comp_subst_apply ha' hb]`.
-/
theorem mvsubst_psubst {K : Type u} [Field K] {τ σ : Type} (w : PowerSeries K)
    (a : MvPowerSeries τ K) (ha : MvPowerSeries.constantCoeff a = 0)
    (b : τ → MvPowerSeries σ K) (hb : MvPowerSeries.HasSubst b) :
    MvPowerSeries.subst b (w.subst a) = w.subst (MvPowerSeries.subst b a) := by
  have ha' : MvPowerSeries.HasSubst (fun _ : Unit => a) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => ha
  unfold PowerSeries.subst
  rw [MvPowerSeries.subst_comp_subst_apply ha' hb]

/- English proof (translation)
The claim follows from `eq_inv_of_mul_eq_one_right (by rw [← map_mul, h, map_one])`.
-/
theorem eq_inv_of_map {L F : Type*} [CommRing L] [Field F] (f : L →+* F) {a b : L}
    (h : a * b = 1) : f b = (f a)⁻¹ :=
  eq_inv_of_mul_eq_one_right (by rw [← map_mul, h, map_one])

/- English proof (translation)
Unfold `Formalism.ELL.WEqAt at h`. Simplify using `only [mul_zero, smul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h`. Conclude with `pow_eq_zero_iff (n := 3) (by norm_num) |>.1 h.symm`.
-/
theorem eq_zero_of_weq {K : Type u} [Field K] {W : WeierstrassCurve K} {σ : Type}
    {s : MvPowerSeries σ K} (h : Formalism.ELL.WEqAt W s 0) : s = 0 := by
  unfold Formalism.ELL.WEqAt at h
  simp only [mul_zero, smul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow] at h
  exact pow_eq_zero_iff (n := 3) (by norm_num) |>.1 h.symm

/- English proof (translation)
Introduce and unpack `rfl`. Conclude with `hs (eq_zero_of_weq h)`.
-/
theorem ne_zero_of_weq {K : Type u} [Field K] {W : WeierstrassCurve K} {σ : Type}
    {s v : MvPowerSeries σ K} (h : Formalism.ELL.WEqAt W s v) (hs : s ≠ 0) : v ≠ 0 := by
  rintro rfl
  exact hs (eq_zero_of_weq h)

end Formalism.ELL.WeierstrassSubstitution

open Formalism.ELL.WeierstrassSubstitution in
/- English proof (translation)
Introduce `K _ W w hw F₂ hF0 hch σ _ s t hs ht hs0 ht0 hxst`. Establish `chord_forms : ∀ (L : Type u) [Field L] (V : WeierstrassCurve.Affine L) (x0 x1 w0 w1 D PX : L), w0 ≠ 0 → w1 ≠ 0 → D = x0 * w1 - x1 * w0 → D ≠ 0 → PX = (w0 - w1) ^ 2 * w0 * w1 + V.a₁ * (w0 - w1) * D * w0 * w1 - V.a₂ * D ^ 2 * w0 * w1 - x0 * D ^ 2 * w1 - x1 * D ^ 2 * w0 → V.addX (x0 …`. Introduce `L _ V x0 x1 w0 w1 D PX h0 h1 hD hd hPX`. Establish `hl : (-1 / w0 - -1 / w1) / (x0 / w0 - x1 / w1) = (w0 - w1) / D`. Rewrite using `[hD]`.

Rewrite `hd` using `[hD]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hX : V.addX (x0 / w0) (x1 / w1) ((-1 / w0 - -1 / w1) / (x0 / w0 - x1 / w1)) = PX / (D ^ 2 * w0 * w1)`. Rewrite using `[hl, hPX]`.

Simplify using `only [WeierstrassCurve.Affine.addX]`. Clear the denominators using the available nonvanishing facts. Use `⟨hX, ?_⟩` and prove the remaining obligations. Simplify using `only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.negAddY]`. Rewrite using `[hX, hl]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Apply the tactic sequence `have hv : MvPowerSeries.HasSubst ![s, t] := MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by fin_cases i <;> simp [hs, ht]`. Use `set φ := MvPowerSeries.substAlgHom (R := K) hv with hφ`. Establish `φe : ∀ g, φ g = MvPowerSeries.subst ![s, t] g` using `fun g => by`.

Rewrite using `[hφ, MvPowerSeries.coe_substAlgHom]`. Establish `φX0 : φ (MvPowerSeries.X 0) = s` using `by rw [φe, MvPowerSeries.subst_X hv]; rfl`. Establish `φX1 : φ (MvPowerSeries.X 1) = t` using `by rw [φe, MvPowerSeries.subst_X hv]; rfl`. Establish `φw : ∀ g : MvPowerSeries (Fin 2) K, MvPowerSeries.constantCoeff g = 0 → φ (w.subst g) = w.subst (φ g)` using `fun g hg => by`. Rewrite using `[φe, φe, mvsubst_psubst w g hg _ hv]`.

Establish `φw0 : φ (w.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) = w.subst s`. Rewrite using `[φw _ (MvPowerSeries.constantCoeff_X 0), φX0]`. Establish `φw1 : φ (w.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)) = w.subst t`. Rewrite using `[φw _ (MvPowerSeries.constantCoeff_X 1), φX1]`. Establish `φwF : φ (w.subst F₂) = w.subst (φ F₂)` using `φw F₂ hF0`.

Establish `injA` using `IsFractionRing.injective (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))`. Establish `injB` using `IsFractionRing.injective (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))`. Establish `ws0 : w.subst s ≠ 0` using `ne_zero_of_weq (hU K W w hw σ s hs).1 hs0`. Establish `wt0 : w.subst t ≠ 0` using `ne_zero_of_weq (hU K W w hw σ t ht).1 ht0`. Establish `dB : s * w.subst t - t * w.subst s ≠ 0`.

Introduce `h`. Apply `hxst` to reduce the goal to its premises. Unfold `Formalism.ELL.xOf`. Rewrite using `[div_eq_div_iff ((map_ne_zero_iff _ injB).2 ws0) ((map_ne_zero_iff _ injB).2 wt0), ← map_mul, ← map_mul]`. Use `congr 1`.

Take the linear combination `h`. Establish `w00 : w.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ≠ 0` using `fun h => ws0 (by rw [← φw0, h, map_zero])`. Establish `w10 : w.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ≠ 0` using `fun h => wt0 (by rw [← φw1, h, map_zero])`. Establish `φD : φ (MvPowerSeries.X 0 * w.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) - MvPowerSeries.X 1 * w.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) = s * w.subst t - t * w.subst s`. Simplify using `only [map_sub, map_mul, φX0, φX1, φw0, φw1]`.

Establish `dA : MvPowerSeries.X 0 * w.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) - MvPowerSeries.X 1 * w.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ≠ 0` using `fun h => dB (by rw [← φD, h, map_zero])`. Unfold `Formalism.ELL.ChordAt at hch ⊢`. Simplify using `only at hch ⊢`. Unfold `Formalism.ELL.xOf Formalism.ELL.yOf at hch ⊢`. Rewrite `hch` using `[(chord_forms _ _ _ _ _ _ _ _ ((map_ne_zero_iff _ injA).2 w00) ((map_ne_zero_iff _ injA).2 w10) rfl (by rw [← map_mul, ← map_mul, ← map_sub]; exact (map_ne_zero_iff _ injA).2 dA) rfl).1, (chord_forms _ _ _ _ _ _ _ _ ((map_ne_zero_iff _ injA).2 w00) ((map_ne_zero_iff _ injA).2 w10 …`.

Rewrite using `[(chord_forms _ _ _ _ _ _ _ _ ((map_ne_zero_iff _ injB).2 ws0) ((map_ne_zero_iff _ injB).2 wt0) rfl (by rw [← map_mul, ← map_mul, ← map_sub]; exact (map_ne_zero_iff _ injB).2 dB) rfl).1, (chord_forms _ _ _ _ _ _ _ _ ((map_ne_zero_iff _ injB).2 ws0) ((map_ne_zero_iff _ injB).2 wt0 …`. Simplify using `only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃] at hch ⊢`. Simplify using `only [IsScalarTower.algebraMap_apply K (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))] at hch`. Simplify using `only [IsScalarTower.algebraMap_apply K (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))]`. Establish `iw0` using `(map_ne_zero_iff _ injA).2 w00`.

Establish `iw1` using `(map_ne_zero_iff _ injA).2 w10`. Establish `idA : algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K)) (MvPowerSeries.X 0) * algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K)) (w.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)) - algebraMap (MvPowerSeries (Fin 2) K) ( …`. Rewrite using `[← map_mul, ← map_mul, ← map_sub]`. Conclude with `(map_ne_zero_iff _ injA).2 dA`. Establish `jw0` using `(map_ne_zero_iff _ injB).2 ws0`.

Establish `jw1` using `(map_ne_zero_iff _ injB).2 wt0`. Establish `jdB : algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) s * algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) (w.subst t) - algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) t * algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerS …`. Rewrite using `[← map_mul, ← map_mul, ← map_sub]`. Conclude with `(map_ne_zero_iff _ injB).2 dB`. Take `⟨hx, hy⟩` from `hch`.

Rewrite using `[← φe F₂]`. Distinguish the cases in `hwF : w.subst F₂ = 0`. Establish `hF : F₂ = 0` using `eq_zero_of_weq (hwF ▸ (hU K W w hw (Fin 2) F₂ hF0).1)`. Establish `hr : w.subst (φ F₂) = 0`. Rewrite using `[hF, map_zero]`.

Conclude with `((hU K W w hw σ 0 (map_zero _)).2 0 (map_zero _) (by unfold Formalism.ELL.WEqAt; simp)).symm`. Rewrite `hx`, `hy` using `[hwF, map_zero, div_zero, eq_comm, div_eq_zero_iff]`. Establish `hx'` using `hx.resolve_right (by simp [iw0, iw1, idA])`. Establish `hy'` using `hy.resolve_right (by simp [iw0, iw1, idA])`. Simplify using `only [← map_mul, ← map_sub, ← map_add, ← map_pow, ← map_neg] at hx' hy'`.

Rewrite `hx'`, `hy'` using `[map_eq_zero_iff _ injA]`. Establish `hxB` using `congrArg φ hx'`. Establish `hyB` using `congrArg φ hy'`. Simplify using `only [map_mul, map_sub, map_add, map_pow, map_neg, map_zero, AlgHom.commutes, φX0, φX1, φw0, φw1] at hxB hyB`. Establish `hxF` using `congrArg (algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))) hxB`.

Establish `hyF` using `congrArg (algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))) hyB`. Simplify using `only [map_mul, map_sub, map_add, map_pow, map_neg, map_zero] at hxF hyF`. Rewrite using `[hr, map_zero, div_zero, div_zero]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[hxF, zero_div]`.

Rewrite using `[hyF, zero_div]`. Establish `iwF` using `(map_ne_zero_iff _ injA).2 hwF`. Rewrite `hx` using `[div_eq_div_iff iwF (by simp [iw0, iw1, idA])]`. Rewrite `hy` using `[div_eq_div_iff iwF (by simp [iw0, iw1, idA]), neg_one_mul]`. Simplify using `only [← map_mul, ← map_sub, ← map_add, ← map_pow, ← map_neg] at hx hy`.

Rewrite `hx`, `hy` using `[injA.eq_iff]`. Establish `hxB` using `congrArg φ hx`. Establish `hyB` using `congrArg φ hy`. Simplify using `only [map_mul, map_sub, map_add, map_pow, map_neg, AlgHom.commutes, φX0, φX1, φw0, φw1, φwF] at hxB hyB`. Establish `hxF` using `congrArg (algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))) hxB`.

Establish `hyF` using `congrArg (algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))) hyB`. Simplify using `only [map_mul, map_sub, map_add, map_pow, map_neg] at hxF hyF`. Establish `jwr : algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) (w.subst (φ F₂)) ≠ 0`. Introduce `h0`. Rewrite `hyF` using `[h0, mul_zero, neg_eq_zero]`.

Use `revert hyF`. Simplify using `[jw0, jw1, jdB]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[div_eq_div_iff jwr (by simp [jw0, jw1, jdB])]`. Take the linear combination `hxF`.

Rewrite using `[div_eq_div_iff jwr (by simp [jw0, jw1, jdB]), neg_one_mul]`. Take the linear combination `hyF`.
-/
theorem Formalism.ELL.wChordSubst_of (hU : Formalism.ELL.WSubstUnique.{u}) : Formalism.ELL.WChordSubst.{u} := by
  intro K _ W w hw F₂ hF0 hch σ _ s t hs ht hs0 ht0 hxst
  classical

  have chord_forms : ∀ (L : Type u) [Field L] (V : WeierstrassCurve.Affine L)
      (x0 x1 w0 w1 D PX : L), w0 ≠ 0 → w1 ≠ 0 → D = x0 * w1 - x1 * w0 → D ≠ 0 →
      PX = (w0 - w1) ^ 2 * w0 * w1 + V.a₁ * (w0 - w1) * D * w0 * w1
        - V.a₂ * D ^ 2 * w0 * w1 - x0 * D ^ 2 * w1 - x1 * D ^ 2 * w0 →
      V.addX (x0 / w0) (x1 / w1) ((-1 / w0 - -1 / w1) / (x0 / w0 - x1 / w1)) =
          PX / (D ^ 2 * w0 * w1) ∧
      V.addY (x0 / w0) (x1 / w1) (-1 / w0) ((-1 / w0 - -1 / w1) / (x0 / w0 - x1 / w1)) =
          (-((w0 - w1) * (PX - x0 * D ^ 2 * w1)) + D ^ 3 * w1 - V.a₁ * D * PX
            - V.a₃ * D ^ 3 * w0 * w1) / (D ^ 3 * w0 * w1) := by
    intro L _ V x0 x1 w0 w1 D PX h0 h1 hD hd hPX
    have hl : (-1 / w0 - -1 / w1) / (x0 / w0 - x1 / w1) = (w0 - w1) / D := by
      rw [hD]
      rw [hD] at hd
      field_simp
      ring
    have hX : V.addX (x0 / w0) (x1 / w1) ((-1 / w0 - -1 / w1) / (x0 / w0 - x1 / w1)) =
        PX / (D ^ 2 * w0 * w1) := by
      rw [hl, hPX]
      simp only [WeierstrassCurve.Affine.addX]
      field_simp
    refine ⟨hX, ?_⟩
    simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY]
    rw [hX, hl]
    field_simp
    ring
  have hv : MvPowerSeries.HasSubst ![s, t] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by fin_cases i <;> simp [hs, ht]
  set φ := MvPowerSeries.substAlgHom (R := K) hv with hφ
  have φe : ∀ g, φ g = MvPowerSeries.subst ![s, t] g := fun g => by
    rw [hφ, MvPowerSeries.coe_substAlgHom]
  have φX0 : φ (MvPowerSeries.X 0) = s := by rw [φe, MvPowerSeries.subst_X hv]; rfl
  have φX1 : φ (MvPowerSeries.X 1) = t := by rw [φe, MvPowerSeries.subst_X hv]; rfl
  have φw : ∀ g : MvPowerSeries (Fin 2) K, MvPowerSeries.constantCoeff g = 0 →
      φ (w.subst g) = w.subst (φ g) := fun g hg => by
    rw [φe, φe, mvsubst_psubst w g hg _ hv]
  have φw0 : φ (w.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) = w.subst s := by
    rw [φw _ (MvPowerSeries.constantCoeff_X 0), φX0]
  have φw1 : φ (w.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)) = w.subst t := by
    rw [φw _ (MvPowerSeries.constantCoeff_X 1), φX1]
  have φwF : φ (w.subst F₂) = w.subst (φ F₂) := φw F₂ hF0
  have injA := IsFractionRing.injective (MvPowerSeries (Fin 2) K)
    (FractionRing (MvPowerSeries (Fin 2) K))
  have injB := IsFractionRing.injective (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))

  have ws0 : w.subst s ≠ 0 := ne_zero_of_weq (hU K W w hw σ s hs).1 hs0
  have wt0 : w.subst t ≠ 0 := ne_zero_of_weq (hU K W w hw σ t ht).1 ht0
  have dB : s * w.subst t - t * w.subst s ≠ 0 := by
    intro h
    apply hxst
    unfold Formalism.ELL.xOf
    rw [div_eq_div_iff ((map_ne_zero_iff _ injB).2 ws0) ((map_ne_zero_iff _ injB).2 wt0),
      ← map_mul, ← map_mul]
    congr 1
    linear_combination h
  have w00 : w.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ≠ 0 := fun h =>
    ws0 (by rw [← φw0, h, map_zero])
  have w10 : w.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ≠ 0 := fun h =>
    wt0 (by rw [← φw1, h, map_zero])
  have φD : φ (MvPowerSeries.X 0 * w.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) -
      MvPowerSeries.X 1 * w.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) =
      s * w.subst t - t * w.subst s := by
    simp only [map_sub, map_mul, φX0, φX1, φw0, φw1]
  have dA : MvPowerSeries.X 0 * w.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) -
      MvPowerSeries.X 1 * w.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ≠ 0 := fun h =>
    dB (by rw [← φD, h, map_zero])
  unfold Formalism.ELL.ChordAt at hch ⊢
  simp only at hch ⊢
  unfold Formalism.ELL.xOf Formalism.ELL.yOf at hch ⊢
  rw [(chord_forms _ _ _ _ _ _ _ _ ((map_ne_zero_iff _ injA).2 w00)
      ((map_ne_zero_iff _ injA).2 w10) rfl
      (by rw [← map_mul, ← map_mul, ← map_sub]; exact (map_ne_zero_iff _ injA).2 dA) rfl).1,
    (chord_forms _ _ _ _ _ _ _ _ ((map_ne_zero_iff _ injA).2 w00)
      ((map_ne_zero_iff _ injA).2 w10) rfl
      (by rw [← map_mul, ← map_mul, ← map_sub]; exact (map_ne_zero_iff _ injA).2 dA) rfl).2] at hch
  rw [(chord_forms _ _ _ _ _ _ _ _ ((map_ne_zero_iff _ injB).2 ws0)
      ((map_ne_zero_iff _ injB).2 wt0) rfl
      (by rw [← map_mul, ← map_mul, ← map_sub]; exact (map_ne_zero_iff _ injB).2 dB) rfl).1,
    (chord_forms _ _ _ _ _ _ _ _ ((map_ne_zero_iff _ injB).2 ws0)
      ((map_ne_zero_iff _ injB).2 wt0) rfl
      (by rw [← map_mul, ← map_mul, ← map_sub]; exact (map_ne_zero_iff _ injB).2 dB) rfl).2]
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃] at hch ⊢
  simp only [IsScalarTower.algebraMap_apply K (MvPowerSeries (Fin 2) K)
    (FractionRing (MvPowerSeries (Fin 2) K))] at hch
  simp only [IsScalarTower.algebraMap_apply K (MvPowerSeries σ K)
    (FractionRing (MvPowerSeries σ K))]
  have iw0 := (map_ne_zero_iff _ injA).2 w00
  have iw1 := (map_ne_zero_iff _ injA).2 w10
  have idA : algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K)) (MvPowerSeries.X 0) *
      algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))
        (w.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)) -
      algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K)) (MvPowerSeries.X 1) *
      algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))
        (w.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) ≠ 0 := by
    rw [← map_mul, ← map_mul, ← map_sub]
    exact (map_ne_zero_iff _ injA).2 dA
  have jw0 := (map_ne_zero_iff _ injB).2 ws0
  have jw1 := (map_ne_zero_iff _ injB).2 wt0
  have jdB : algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) s *
      algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) (w.subst t) -
      algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) t *
      algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) (w.subst s) ≠ 0 := by
    rw [← map_mul, ← map_mul, ← map_sub]
    exact (map_ne_zero_iff _ injB).2 dB
  obtain ⟨hx, hy⟩ := hch
  rw [← φe F₂]
  by_cases hwF : w.subst F₂ = 0
  ·
    have hF : F₂ = 0 := eq_zero_of_weq (hwF ▸ (hU K W w hw (Fin 2) F₂ hF0).1)
    have hr : w.subst (φ F₂) = 0 := by
      rw [hF, map_zero]
      exact ((hU K W w hw σ 0 (map_zero _)).2 0 (map_zero _)
        (by unfold Formalism.ELL.WEqAt; simp)).symm
    rw [hwF, map_zero, div_zero, eq_comm, div_eq_zero_iff] at hx hy
    have hx' := hx.resolve_right (by simp [iw0, iw1, idA])
    have hy' := hy.resolve_right (by simp [iw0, iw1, idA])
    simp only [← map_mul, ← map_sub, ← map_add, ← map_pow, ← map_neg] at hx' hy'
    rw [map_eq_zero_iff _ injA] at hx' hy'
    have hxB := congrArg φ hx'
    have hyB := congrArg φ hy'
    simp only [map_mul, map_sub, map_add, map_pow, map_neg, map_zero, AlgHom.commutes,
      φX0, φX1, φw0, φw1] at hxB hyB
    have hxF := congrArg (algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))) hxB
    have hyF := congrArg (algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))) hyB
    simp only [map_mul, map_sub, map_add, map_pow, map_neg, map_zero] at hxF hyF
    rw [hr, map_zero, div_zero, div_zero]
    constructor
    · rw [hxF, zero_div]
    · rw [hyF, zero_div]
  · have iwF := (map_ne_zero_iff _ injA).2 hwF
    rw [div_eq_div_iff iwF (by simp [iw0, iw1, idA])] at hx
    rw [div_eq_div_iff iwF (by simp [iw0, iw1, idA]), neg_one_mul] at hy
    simp only [← map_mul, ← map_sub, ← map_add, ← map_pow, ← map_neg] at hx hy
    rw [injA.eq_iff] at hx hy
    have hxB := congrArg φ hx
    have hyB := congrArg φ hy
    simp only [map_mul, map_sub, map_add, map_pow, map_neg, AlgHom.commutes,
      φX0, φX1, φw0, φw1, φwF] at hxB hyB
    have hxF := congrArg (algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))) hxB
    have hyF := congrArg (algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))) hyB
    simp only [map_mul, map_sub, map_add, map_pow, map_neg] at hxF hyF

    have jwr : algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) (w.subst (φ F₂)) ≠ 0 := by
      intro h0
      rw [h0, mul_zero, neg_eq_zero] at hyF
      revert hyF
      simp [jw0, jw1, jdB]
    constructor
    · rw [div_eq_div_iff jwr (by simp [jw0, jw1, jdB])]
      linear_combination hxF
    · rw [div_eq_div_iff jwr (by simp [jw0, jw1, jdB]), neg_one_mul]
      linear_combination hyF
