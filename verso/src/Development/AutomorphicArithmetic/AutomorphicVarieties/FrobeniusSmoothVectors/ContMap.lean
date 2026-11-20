import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoordGrading
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PartClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PartSpan

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Take `⟨L, hL, rfl⟩` from `hx`. Rewrite using `[← hL]`. Conclude with `SetLike.list_prod_map_mem_graded L _ _ fun s _ => h s.1 s.2.1 s.2.2`.
-/
private theorem mon_part {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {k : Type} [Field k] {F : Frame l k} {n : ℕ}
    {R : Type} [CommRing R] [Algebra O R] (ρ : NRep F n R) (W : WPres O ℤ R)
    (h : ∀ g i j, ρ.r g i j ∈ W.part (w n i - w n j)) {j : ℤ} {x : R} (hx : x ∈ ρ.mon j) : x ∈ W.part j := by
  obtain ⟨L, hL, rfl⟩ := hx
  rw [← hL]
  exact SetLike.list_prod_map_mem_graded L _ _ fun s _ => h s.1 s.2.1 s.2.2

/- English proof (translation)
Take `⟨L1, h1, rfl⟩` from `hx`. Take `⟨L2, h2, rfl⟩` from `hy`. Conclude with `⟨L1 ++ L2, by simp [h1, h2], by simp⟩`.
-/
private theorem mono_lemma {l : ℕ} [Fact l.Prime] {K : Type} [Field K] {F : Frame l K} {n : ℕ}
    {R : Type} [CommRing R] (ρ : NRep F n R) {a b : ℤ} {x y : R} (hx : x ∈ ρ.mon a) (hy : y ∈ ρ.mon b) :
    x * y ∈ ρ.mon (a + b) := by
  obtain ⟨L1, h1, rfl⟩ := hx
  obtain ⟨L2, h2, rfl⟩ := hy
  exact ⟨L1 ++ L2, by simp [h1, h2], by simp⟩

/- English proof (translation)
Proceed by induction on `e with`. Consider the case `zero => exact ⟨1, D.one_mem, 1, ⟨[], by simp, by simp⟩, by simp⟩`. Consider the case `succ e ih`. Take `⟨b, hb, x, hx, hbx⟩` from `ih`. Break down `h s with ⟨g, i, j, hz, hw⟩ | ⟨hw, hz⟩` into its components or cases.

Establish `hs : ρ.r g i j ∈ ρ.mon (W.wt s)` using `⟨[(g, i, j)], by simp [hw], by simp⟩`. Use `⟨b, hb, x * ρ.r g i j, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[succ_nsmul]`. Conclude with `mono_lemma ρ hx hs`. Rewrite using `[pow_succ, hbx, hz]`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨b * W.z s, D.mul_mem hb hz, x, ?_, ?_⟩` and prove the remaining obligations. Simplify `hx` using `[hw]`. Rewrite using `[pow_succ, hbx]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem mono_lemma_2 {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {K : Type} [Field K] {F : Frame l K} {n : ℕ}
    {R : Type} [CommRing R] [Algebra O R] (ρ : NRep F n R) (W : WPres O ℤ R) (D : Subalgebra O R)
    (h : ∀ s, (∃ g i j, W.z s = ρ.r g i j ∧ W.wt s = w n i - w n j) ∨ (W.wt s = 0 ∧ W.z s ∈ D)) (s : W.σ) (e : ℕ) :
    ∃ b ∈ D, ∃ x ∈ ρ.mon (e • W.wt s), W.z s ^ e = b * x := by
  induction e with
  | zero => exact ⟨1, D.one_mem, 1, ⟨[], by simp, by simp⟩, by simp⟩
  | succ e ih =>
    obtain ⟨b, hb, x, hx, hbx⟩ := ih
    rcases h s with ⟨g, i, j, hz, hw⟩ | ⟨hw, hz⟩
    · have hs : ρ.r g i j ∈ ρ.mon (W.wt s) := ⟨[(g, i, j)], by simp [hw], by simp⟩
      refine ⟨b, hb, x * ρ.r g i j, ?_, ?_⟩
      · rw [succ_nsmul]
        exact mono_lemma ρ hx hs
      · rw [pow_succ, hbx, hz]
        ring
    · refine ⟨b * W.z s, D.mul_mem hb hz, x, ?_, ?_⟩
      · simpa [hw] using hx
      · rw [pow_succ, hbx]
        ring

/- English proof (translation)
Proceed by induction on `m using Finsupp.induction with`. Consider the case `zero => exact ⟨1, D.one_mem, 1, ⟨[], by simp, by simp⟩, by simp⟩`. Consider the case `single_add a e f _ _ ih`. Take `⟨b, hb, x, hx, hbx⟩` from `ih`. Take `⟨b', hb', x', hx', hbx'⟩` from `mono_lemma_2 ρ W D h a e`.

Use `⟨b' * b, D.mul_mem hb' hb, x' * x, ?_, ?_⟩` and prove the remaining obligations. Establish `hw : Finsupp.weight W.wt (Finsupp.single a e) = e • W.wt a`. Simplify using `[Finsupp.weight_apply, Finsupp.sum_single_index]`. Rewrite using `[map_add, hw]`. Conclude with `mono_lemma ρ hx' hx`.

Establish `hm : MvPowerSeries.monomial (Finsupp.single a e + f) (1 : O) = MvPowerSeries.X a ^ e * MvPowerSeries.monomial f 1`. Rewrite using `[MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, one_mul]`. Simplify using `only [WPres.z] at hbx'`. Rewrite using `[hm, map_mul, map_pow, hbx, hbx']`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem mono {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {k : Type} [Field k] {F : Frame l k} {n : ℕ}
    {R : Type} [CommRing R] [Algebra O R] (ρ : NRep F n R) (W : WPres O ℤ R) (D : Subalgebra O R)
    (h : ∀ s, (∃ g i j, W.z s = ρ.r g i j ∧ W.wt s = w n i - w n j) ∨ (W.wt s = 0 ∧ W.z s ∈ D)) (m : W.σ →₀ ℕ) :
    ∃ b ∈ D, ∃ x ∈ ρ.mon (Finsupp.weight W.wt m), W.π (MvPowerSeries.monomial m 1) = b * x := by
  induction m using Finsupp.induction with
  | zero => exact ⟨1, D.one_mem, 1, ⟨[], by simp, by simp⟩, by simp⟩
  | single_add a e f _ _ ih =>
    obtain ⟨b, hb, x, hx, hbx⟩ := ih
    obtain ⟨b', hb', x', hx', hbx'⟩ := mono_lemma_2 ρ W D h a e
    refine ⟨b' * b, D.mul_mem hb' hb, x' * x, ?_, ?_⟩
    · have hw : Finsupp.weight W.wt (Finsupp.single a e) = e • W.wt a := by
        simp [Finsupp.weight_apply, Finsupp.sum_single_index]
      rw [map_add, hw]
      exact mono_lemma ρ hx' hx
    · have hm : MvPowerSeries.monomial (Finsupp.single a e + f) (1 : O) =
          MvPowerSeries.X a ^ e * MvPowerSeries.monomial f 1 := by
        rw [MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, one_mul]
      simp only [WPres.z] at hbx'
      rw [hm, map_mul, map_pow, hbx, hbx']
      ring

/- English proof (translation)
Use `haveI := W.fin`. Simplify using `only [WPres.part, Submodule.mem_map] at hy`. Take `⟨f, hf, rfl⟩` from `hy`. Establish `hf' : ∀ m, Finsupp.weight W.wt m ≠ 0 → MvPowerSeries.coeff m f = 0` using `hf`. Establish `key : ∀ m, W.π (MvPowerSeries.monomial m (MvPowerSeries.coeff m f)) ∈ D`.

Introduce `m`. Distinguish the cases in `hm : Finsupp.weight W.wt m = 0`. Establish `e : MvPowerSeries.monomial m (MvPowerSeries.coeff m f) = MvPowerSeries.coeff m f • MvPowerSeries.monomial m (1 : O)`. Rewrite using `[← LinearMap.map_smul, smul_eq_mul, mul_one]`. Rewrite using `[e, map_smul]`.

Conclude with `D.smul_mem (hD m hm) _`. Rewrite using `[hf' m hm, map_zero, map_zero]`. Conclude with `D.zero_mem`. Simplify using `only [AlgHom.toLinearMap_apply]`. Use `show ∀ N : ℕ, ∃ d ∈ D, W.π f - d ∈ maximalIdeal R ^ N`.

Introduce `N`. Set `c : W.σ →₀ ℕ` to `Finsupp.equivFunOnFinite.symm fun _ => N`. Set `low` to `∑ m ∈ Finset.Iic c, MvPowerSeries.monomial m (MvPowerSeries.coeff m f)`. Set `S : Set (W.σ →₀ ℕ)` to `{m | Finsupp.weight W.wt m = 0 ∧ ∃ s, N ≤ m s}`. Establish `hg : ∀ m ∉ S, MvPowerSeries.coeff m (f - low) = 0`.

Introduce `m hm`. Simplify using `only [S, Set.mem_setOf_eq, not_and, not_exists, not_le] at hm`. Establish `hl : MvPowerSeries.coeff m low = if m ∈ Finset.Iic c then MvPowerSeries.coeff m f else 0`. Simplify using `[low, map_sum, MvPowerSeries.coeff_monomial]`. Rewrite using `[map_sub, hl]`.

Distinguish the cases in `hw : Finsupp.weight W.wt m = 0`. Establish `hmc : m ∈ Finset.Iic c`. Rewrite using `[Finset.mem_Iic]`. Introduce `s`. Conclude with `(hm hw s).le.trans_eq (by simp [c])`.

Simplify using `[hmc]`. Simplify using `[hf' m hw]`. Take `⟨μ, hμ, hspan⟩` from `part_span O R ℤ W S 0 (fun m hm => hm.1)`. Take `⟨b, hb, hfb⟩` from `hspan (f - low) hg`. Use `⟨W.π low, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_sum]`. Conclude with `Subalgebra.sum_mem _ fun m _ => key m`. Rewrite using `[← map_sub, hfb, map_sum]`. Use `Ideal.sum_mem _ fun m hm => ?_` and prove the remaining obligations. Take `⟨s, hs⟩` from `(hμ (Finset.mem_coe.mpr hm)).2`.

Establish `e : MvPowerSeries.monomial m (1 : O) = MvPowerSeries.X s ^ N * MvPowerSeries.monomial (m - Finsupp.single s N) 1`. Rewrite using `[MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, one_mul, add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr hs)]`. Rewrite using `[map_mul, e, map_mul, map_pow]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (hz s) N))`.
-/
private theorem dense {O R : Type} [CommRing O] [CommRing R] [IsLocalRing R] [Algebra O R] (W : WPres O ℤ R)
    (hz : ∀ s, W.z s ∈ maximalIdeal R) (D : Subalgebra O R)
    (hD : ∀ m, Finsupp.weight W.wt m = 0 → W.π (MvPowerSeries.monomial m 1) ∈ D) {y : R} (hy : y ∈ W.part 0) :
    y ∈ adicClosure D := by
  haveI := W.fin
  classical
  simp only [WPres.part, Submodule.mem_map] at hy
  obtain ⟨f, hf, rfl⟩ := hy
  have hf' : ∀ m, Finsupp.weight W.wt m ≠ 0 → MvPowerSeries.coeff m f = 0 := hf
  have key : ∀ m, W.π (MvPowerSeries.monomial m (MvPowerSeries.coeff m f)) ∈ D := by
    intro m
    by_cases hm : Finsupp.weight W.wt m = 0
    · have e : MvPowerSeries.monomial m (MvPowerSeries.coeff m f) =
          MvPowerSeries.coeff m f • MvPowerSeries.monomial m (1 : O) := by
        rw [← LinearMap.map_smul, smul_eq_mul, mul_one]
      rw [e, map_smul]
      exact D.smul_mem (hD m hm) _
    · rw [hf' m hm, map_zero, map_zero]
      exact D.zero_mem
  simp only [AlgHom.toLinearMap_apply]
  show ∀ N : ℕ, ∃ d ∈ D, W.π f - d ∈ maximalIdeal R ^ N
  intro N
  let c : W.σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => N
  let low := ∑ m ∈ Finset.Iic c, MvPowerSeries.monomial m (MvPowerSeries.coeff m f)
  let S : Set (W.σ →₀ ℕ) := {m | Finsupp.weight W.wt m = 0 ∧ ∃ s, N ≤ m s}
  have hg : ∀ m ∉ S, MvPowerSeries.coeff m (f - low) = 0 := by
    intro m hm
    simp only [S, Set.mem_setOf_eq, not_and, not_exists, not_le] at hm
    have hl : MvPowerSeries.coeff m low = if m ∈ Finset.Iic c then MvPowerSeries.coeff m f else 0 := by
      simp [low, map_sum, MvPowerSeries.coeff_monomial]
    rw [map_sub, hl]
    by_cases hw : Finsupp.weight W.wt m = 0
    · have hmc : m ∈ Finset.Iic c := by
        rw [Finset.mem_Iic]
        intro s
        exact (hm hw s).le.trans_eq (by simp [c])
      simp [hmc]
    · simp [hf' m hw]
  obtain ⟨μ, hμ, hspan⟩ := part_span O R ℤ W S 0 (fun m hm => hm.1)
  obtain ⟨b, hb, hfb⟩ := hspan (f - low) hg
  refine ⟨W.π low, ?_, ?_⟩
  · rw [map_sum]
    exact Subalgebra.sum_mem _ fun m _ => key m
  · rw [← map_sub, hfb, map_sum]
    refine Ideal.sum_mem _ fun m hm => ?_
    obtain ⟨s, hs⟩ := (hμ (Finset.mem_coe.mpr hm)).2
    have e : MvPowerSeries.monomial m (1 : O) =
        MvPowerSeries.X s ^ N * MvPowerSeries.monomial (m - Finsupp.single s N) 1 := by
      rw [MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, one_mul,
        add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr hs)]
    rw [map_mul, e, map_mul, map_pow]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (hz s) N))

/- English proof (translation)
Establish `hm : Ideal.map f.toRingHom (maximalIdeal R) ≤ maximalIdeal R'`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `x hx`. Use `show f x ∈ maximalIdeal R'`. Rewrite using `[← res_eq_zero_iff O R', res_map, res_eq_zero_iff]`.

Conclude with `hx`. Introduce `N`. Establish `hN : maximalIdeal R ^ N ≤ Ideal.comap f.toRingHom (maximalIdeal R' ^ N)`. Rewrite using `[← Ideal.map_le_iff_le_comap, Ideal.map_pow]`. Conclude with `Ideal.pow_right_mono hm N`.

Establish `e : (fun g => Ideal.Quotient.mk (maximalIdeal R' ^ N) (c * f (a g))) = (fun q => Ideal.Quotient.mk (maximalIdeal R' ^ N) c * Ideal.quotientMap (maximalIdeal R' ^ N) f.toRingHom hN q) ∘ (fun g => Ideal.Quotient.mk (maximalIdeal R ^ N) (a g))`. Use function extensionality and compare the values at `g`. Simplify using `[Ideal.quotientMap_mk]`. Rewrite using `[e]`. Conclude with `(ha N).comp _`.
-/
private theorem cont_map {O Γ R R' : Type} [CommRing O] [IsLocalRing O] [TopologicalSpace Γ] [CommRing R] [Algebra O R]
    [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') (c : R') {a : Γ → R}
    (ha : AdicCont (maximalIdeal R) a) : AdicCont (maximalIdeal R') fun g => c * f (a g) := by
  have hm : Ideal.map f.toRingHom (maximalIdeal R) ≤ maximalIdeal R' := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    show f x ∈ maximalIdeal R'
    rw [← res_eq_zero_iff O R', res_map, res_eq_zero_iff]
    exact hx
  intro N
  have hN : maximalIdeal R ^ N ≤ Ideal.comap f.toRingHom (maximalIdeal R' ^ N) := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono hm N
  have e : (fun g => Ideal.Quotient.mk (maximalIdeal R' ^ N) (c * f (a g))) =
      (fun q => Ideal.Quotient.mk (maximalIdeal R' ^ N) c *
        Ideal.quotientMap (maximalIdeal R' ^ N) f.toRingHom hN q) ∘
        (fun g => Ideal.Quotient.mk (maximalIdeal R ^ N) (a g)) := by
    funext g
    simp [Ideal.quotientMap_mk]
  rw [e]
  exact (ha N).comp _

/- English proof (translation)
Take `⟨⟨hc1, hc2⟩, ⟨hb1, hb2⟩, hd⟩` from `S.lift`. Use `⟨⟨fun i j => ?_, fun v i => ?_⟩, ⟨fun g i => ?_, fun v i g => ?_⟩, fun g i j hij => ?_⟩` and prove the remaining obligations. Simplify `cont_map f (c i j) (hc1 i j)` using `only [hr]`. Simplify `cont_map f 1 (hc2 v i)` using `only [hψ, one_mul]`. Use `show (res O C) (ρ'.r g i i) = _`.

Rewrite using `[hr, hc, one_mul, res_map]`. Conclude with `hb1 g i`. Use `show (res O C) ((ρ'.ψ v i g : Cˣ) : C) = _`. Rewrite using `[hψ, res_map]`. Conclude with `hb2 v i g`.

Use `show (res O C) (ρ'.r g i j) = 0`. Rewrite using `[hr, map_mul, res_map]`. Establish `h0 : (res O S.R) (S.ρ.r g i j) = 0` using `hd g i j hij`. Rewrite using `[h0, mul_zero]`.
-/
private theorem twist_lemma {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)}
    {n : ℕ} (S : Space O F n) (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (f : S.R →ₐ[O] C)
    (c : Fin n → Fin n → C) (hc : ∀ i, c i i = 1) (ρ' : NRep F n C)
    (hr : ∀ g i j, ρ'.r g i j = c i j * f (S.ρ.r g i j)) (hψ : ∀ v i g, (ρ'.ψ v i g : C) = f (S.ρ.ψ v i g)) :
    IsLift O ρ' := by
  obtain ⟨⟨hc1, hc2⟩, ⟨hb1, hb2⟩, hd⟩ := S.lift
  refine ⟨⟨fun i j => ?_, fun v i => ?_⟩, ⟨fun g i => ?_, fun v i g => ?_⟩, fun g i j hij => ?_⟩
  · simpa only [hr] using cont_map f (c i j) (hc1 i j)
  · simpa only [hψ, one_mul] using cont_map f 1 (hc2 v i)
  · show (res O C) (ρ'.r g i i) = _
    rw [hr, hc, one_mul, res_map]
    exact hb1 g i
  · show (res O C) ((ρ'.ψ v i g : Cˣ) : C) = _
    rw [hψ, res_map]
    exact hb2 v i g
  · show (res O C) (ρ'.r g i j) = 0
    rw [hr, map_mul, res_map]
    have h0 : (res O S.R) (S.ρ.r g i j) = 0 := hd g i j hij
    rw [h0, mul_zero]

/- English proof (translation)
Take `⟨ρ', hr, hψ⟩` from `alg_twist u (S.ρ.map (f : S.R →+* C))`. Establish `hl : IsLift O ρ'` using `twist_lemma S C f (fun i j => ((u ^ (w n i - w n j) : Cˣ) : C)) (by simp) ρ' (fun g i j => by rw [hr]; rfl) (fun v i g => by rw [hψ]; rfl)`. Take `⟨f', hf', -⟩` from `S.univ C ρ' hl`. Use `⟨f', fun g i j => ?_, fun v i g => ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Combine the equalities or inequalities in the displayed calculation.
-/
private theorem twist {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)}
    {n : ℕ} (S : Space O F n) (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (f : S.R →ₐ[O] C) (u : Cˣ) :
    ∃ f' : S.R →ₐ[O] C, (∀ g i j, f' (S.ρ.r g i j) = ((u ^ (w n i - w n j) : Cˣ) : C) * f (S.ρ.r g i j)) ∧
      ∀ v i g, f' (S.ρ.ψ v i g) = f (S.ρ.ψ v i g) := by
  obtain ⟨ρ', hr, hψ⟩ := alg_twist u (S.ρ.map (f : S.R →+* C))
  have hl : IsLift O ρ' := twist_lemma S C f (fun i j => ((u ^ (w n i - w n j) : Cˣ) : C)) (by simp) ρ'
    (fun g i j => by rw [hr]; rfl) (fun v i g => by rw [hψ]; rfl)
  obtain ⟨f', hf', -⟩ := S.univ C ρ' hl
  refine ⟨f', fun g i j => ?_, fun v i g => ?_⟩
  · calc f' (S.ρ.r g i j) = (S.ρ.map (f' : S.R →+* C)).r g i j := rfl
      _ = ρ'.r g i j := by rw [hf']
      _ = _ := by rw [hr]; rfl
  · calc f' (S.ρ.ψ v i g : S.R) = (((S.ρ.map (f' : S.R →+* C)).ψ v i g : Cˣ) : C) := rfl
      _ = (ρ'.ψ v i g : C) := by rw [hf']
      _ = _ := by rw [hψ]; rfl

/- English proof (translation)
Establish `hl : IsLift O (S.ρ.map (f : S.R →+* C))` using `twist_lemma S C f (fun _ _ => 1) (fun _ => rfl) _ (fun g i j => by rw [one_mul]; rfl) (fun v i g => rfl)`. Use `(S.univ C _ hl).unique rfl (NRep.ext ?_ ?_)` and prove the remaining obligations. Conclude with `MonoidHom.ext fun g => Matrix.ext fun i j => (h1 g i j).symm`. Use function extensionality and compare the values at `v i`. Conclude with `MonoidHom.ext fun g => Units.ext (h2 v i g).symm`.
-/
private theorem uniq {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)}
    {n : ℕ} (S : Space O F n) (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (f f' : S.R →ₐ[O] C)
    (h1 : ∀ g i j, f (S.ρ.r g i j) = f' (S.ρ.r g i j)) (h2 : ∀ v i g, f (S.ρ.ψ v i g) = f' (S.ρ.ψ v i g)) :
    f = f' := by
  have hl : IsLift O (S.ρ.map (f : S.R →+* C)) := twist_lemma S C f (fun _ _ => 1) (fun _ => rfl) _
    (fun g i j => by rw [one_mul]; rfl) (fun v i g => rfl)
  refine (S.univ C _ hl).unique rfl (NRep.ext ?_ ?_)
  · exact MonoidHom.ext fun g => Matrix.ext fun i j => (h1 g i j).symm
  · funext v i
    exact MonoidHom.ext fun g => Units.ext (h2 v i g).symm

/- English proof (translation)
Set `a : S.R → O` to `fun x => Classical.choose (IsCO.res_surj (O := O) x)`. Establish `ha : ∀ x, x - algebraMap O S.R (a x) ∈ maximalIdeal S.R` using `fun x => Classical.choose_spec (IsCO.res_surj (O := O) x)`. Set `e : (F.G0 × Fin n × Fin n) ⊕ (Σ v : F.V, Fin n × F.Gv v) → S.R` to `Sum.elim (fun p => if p.2.1 = p.2.2 then S.ρ.r p.1 p.2.1 p.2.2 - algebraMap O S.R (a (S.ρ.r p.1 p.2.1 p.2.2)) else S.ρ.r p.1 p.2.1 p.2.2) (fun q => (S.ρ.ψ q.1 q.2.1 q.2.2 : S.R) - algebraMap O S.R (a (S.ρ.ψ q.1 q.2.1 q.2.2)))`. Set `wt : (F.G0 × Fin n × Fin n) ⊕ (Σ v : F.V, Fin n × F.Gv v) → ℤ` to `Sum.elim (fun p => w n p.2.1 - w n p.2.2) (fun _ => 0)`. Establish `eon : ∀ g i, e (Sum.inl (g, i, i)) = S.ρ.r g i i - algebraMap O S.R (a (S.ρ.r g i i))` using `fun g i => if_pos rfl`.

Establish `eoff : ∀ g i j, i ≠ j → e (Sum.inl (g, i, j)) = S.ρ.r g i j` using `fun g i j h => if_neg h`. Establish `eψ : ∀ v i g, e (Sum.inr ⟨v, i, g⟩) = (S.ρ.ψ v i g : S.R) - algebraMap O S.R (a (S.ρ.ψ v i g))` using `fun v i g => rfl`. Establish `hoff : ∀ g i j, i ≠ j → S.ρ.r g i j ∈ maximalIdeal S.R` using `fun g i j h => (res_eq_zero_iff O S.R _).mp (by exact S.lift.2.2 g i j h)`. Establish `he : ∀ s, e s ∈ maximalIdeal S.R`. Introduce and unpack `(⟨g, i, j⟩ | ⟨v, i, g⟩)`.

Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Rewrite using `[eon]`. Conclude with `ha _`. Rewrite using `[eoff g i j h]`.

Conclude with `hoff g i j h`. Rewrite using `[eψ]`. Conclude with `ha _`. Establish `huniq : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f f' : S.R →ₐ[O] R'), (∀ s, f (e s) = f' (e s)) → f = f'`. Introduce `R' _ _ _ f f' h`.

Apply `uniq S R' f f'` to reduce the goal to its premises. Introduce `g i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Establish `h1` using `h (Sum.inl (g, i, i))`.

Rewrite `h1` using `[eon, map_sub, map_sub, AlgHom.commutes, AlgHom.commutes]`. Conclude with `sub_left_injective h1`. Establish `h1` using `h (Sum.inl (g, i, j))`. Rewrite `h1` using `[eoff g i j hij]`. Conclude with `h1`.

Introduce `v i g`. Establish `h1` using `h (Sum.inr ⟨v, i, g⟩)`. Rewrite `h1` using `[eψ, map_sub, map_sub, AlgHom.commutes, AlgHom.commutes]`. Conclude with `sub_left_injective h1`. Establish `htw : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : S.R →ₐ[O] R') (t : Multiplicative ℤ →* R'ˣ), (∀ j, res O R' (t j) = 1) → ∃ f' : S.R →ₐ[O] R', ∀ s, f' (e s) = (t (Multiplicative.ofAdd (wt s)) : R') * f (e s)`.

Introduce `R' _ _ _ f t _`. Take `⟨f', h1, h2⟩` from `twist S R' f (t (Multiplicative.ofAdd 1))`. Establish `ht : ∀ k : ℤ, t (Multiplicative.ofAdd k) = t (Multiplicative.ofAdd 1) ^ k`. Introduce `k`. Rewrite using `[← map_zpow, ← ofAdd_zsmul, smul_eq_mul, mul_one]`.

Use `⟨f', ?_⟩` and prove the remaining obligations. Introduce and unpack `(⟨g, i, j⟩ | ⟨v, i, g⟩)`. Distinguish the cases in `hij : i = j`. Substitute `hij show f' (e (Sum.inl (g, i, i))) = (t (Multiplicative.ofAdd (w n i - w n i)) : R') * _` using the available equality. Rewrite using `[sub_self, eon, map_sub, map_sub, AlgHom.commutes, AlgHom.commutes, h1]`.

Simplify using the standard rewrite rules. Use `show f' (e (Sum.inl (g, i, j))) = (t (Multiplicative.ofAdd (w n i - w n j)) : R') * _`. Rewrite using `[eoff g i j hij, h1, ht (w n i - w n j)]`. Use `show f' (e (Sum.inr ⟨v, i, g⟩)) = (t (Multiplicative.ofAdd 0) : R') * _`. Rewrite using `[eψ, map_sub, map_sub, AlgHom.commutes, AlgHom.commutes, h2]`.

Simplify using the standard rewrite rules. Take `⟨W, u, hWu, hpart⟩` from `coord_grading O ℤ S.R _ e wt he huniq htw`. Establish `h1mem : ∀ c : O, algebraMap O S.R c ∈ W.part 0` using `fun c => by`. Rewrite using `[Algebra.algebraMap_eq_smul_one]`. Conclude with `Submodule.smul_mem _ c SetLike.GradedOne.one_mem`.

Use `⟨W, fun s => by rw [(hWu s).1]; exact he _, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `g i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Establish `hp : S.ρ.r g i i - algebraMap O S.R (a (S.ρ.r g i i)) ∈ W.part 0`.

Use `hpart (Sum.inl (g, i, i))` as an intermediate fact. Rewrite `this` using `[eon]`. Simplify `this` using `[wt]`. Rewrite using `[sub_self, ← sub_add_cancel (S.ρ.r g i i) (algebraMap O S.R (a (S.ρ.r g i i)))]`. Conclude with `add_mem hp (h1mem _)`.

Establish `hp` using `hpart (Sum.inl (g, i, j))`. Rewrite `hp` using `[eoff g i j hij]`. Conclude with `hp`. Introduce `v i g`. Establish `hp : (S.ρ.ψ v i g : S.R) - algebraMap O S.R (a (S.ρ.ψ v i g)) ∈ W.part 0` using `hpart (Sum.inr ⟨v, i, g⟩)`.

Rewrite using `[← sub_add_cancel (S.ρ.ψ v i g : S.R) (algebraMap O S.R (a (S.ρ.ψ v i g)))]`. Conclude with `add_mem hp (h1mem _)`. Introduce `s`. Take `⟨hz, hw⟩` from `hWu s`. Break down `hs : u s with ⟨g, i, j⟩ | ⟨v, i, g⟩` into its components or cases.

Rewrite `hz`, `hw` using `[hs]`. Distinguish the cases in `hij : i = j`. Substitute `hij right` using the available equality. Use `⟨by rw [hw]; exact sub_self _, ?_⟩` and prove the remaining obligations. Rewrite using `[hz, eon]`.

Conclude with `Subalgebra.sub_mem _ (Algebra.subset_adjoin (Or.inl ⟨[(g, i, i)], by simp, by simp⟩)) (Subalgebra.algebraMap_mem _ _)`. Use `left`. Conclude with `⟨g, i, j, by rw [hz, eoff g i j hij], hw⟩`. Rewrite `hz`, `hw`, `right` using `[hs]`. Use `⟨hw, ?_⟩` and prove the remaining obligations.

Rewrite using `[hz, eψ]`. Conclude with `Subalgebra.sub_mem _ (Algebra.subset_adjoin (Or.inr ⟨v, i, g, rfl⟩)) (Subalgebra.algebraMap_mem _ _)`.
-/
private theorem coord {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] {F : Frame l (ResidueField O)} {n : ℕ} (S : Space O F n) :
    ∃ W : WPres O ℤ S.R, (∀ s, W.z s ∈ maximalIdeal S.R) ∧ (∀ g i j, S.ρ.r g i j ∈ W.part (w n i - w n j)) ∧
      (∀ v i g, (S.ρ.ψ v i g : S.R) ∈ W.part 0) ∧
      ∀ s, (∃ g i j, W.z s = S.ρ.r g i j ∧ W.wt s = w n i - w n j) ∨
        (W.wt s = 0 ∧ W.z s ∈ Algebra.adjoin O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)})) := by
  classical
  let a : S.R → O := fun x => Classical.choose (IsCO.res_surj (O := O) x)
  have ha : ∀ x, x - algebraMap O S.R (a x) ∈ maximalIdeal S.R := fun x =>
    Classical.choose_spec (IsCO.res_surj (O := O) x)
  let e : (F.G0 × Fin n × Fin n) ⊕ (Σ v : F.V, Fin n × F.Gv v) → S.R := Sum.elim
    (fun p => if p.2.1 = p.2.2 then S.ρ.r p.1 p.2.1 p.2.2 - algebraMap O S.R (a (S.ρ.r p.1 p.2.1 p.2.2))
      else S.ρ.r p.1 p.2.1 p.2.2)
    (fun q => (S.ρ.ψ q.1 q.2.1 q.2.2 : S.R) - algebraMap O S.R (a (S.ρ.ψ q.1 q.2.1 q.2.2)))
  let wt : (F.G0 × Fin n × Fin n) ⊕ (Σ v : F.V, Fin n × F.Gv v) → ℤ := Sum.elim
    (fun p => w n p.2.1 - w n p.2.2) (fun _ => 0)
  have eon : ∀ g i, e (Sum.inl (g, i, i)) = S.ρ.r g i i - algebraMap O S.R (a (S.ρ.r g i i)) :=
    fun g i => if_pos rfl
  have eoff : ∀ g i j, i ≠ j → e (Sum.inl (g, i, j)) = S.ρ.r g i j := fun g i j h => if_neg h
  have eψ : ∀ v i g, e (Sum.inr ⟨v, i, g⟩) =
      (S.ρ.ψ v i g : S.R) - algebraMap O S.R (a (S.ρ.ψ v i g)) := fun v i g => rfl
  have hoff : ∀ g i j, i ≠ j → S.ρ.r g i j ∈ maximalIdeal S.R := fun g i j h =>
    (res_eq_zero_iff O S.R _).mp (by exact S.lift.2.2 g i j h)
  have he : ∀ s, e s ∈ maximalIdeal S.R := by
    rintro (⟨g, i, j⟩ | ⟨v, i, g⟩)
    · by_cases h : i = j
      · subst h
        rw [eon]
        exact ha _
      · rw [eoff g i j h]
        exact hoff g i j h
    · rw [eψ]
      exact ha _
  have huniq : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f f' : S.R →ₐ[O] R'),
      (∀ s, f (e s) = f' (e s)) → f = f' := by
    intro R' _ _ _ f f' h
    apply uniq S R' f f'
    · intro g i j
      by_cases hij : i = j
      · subst hij
        have h1 := h (Sum.inl (g, i, i))
        rw [eon, map_sub, map_sub, AlgHom.commutes, AlgHom.commutes] at h1
        exact sub_left_injective h1
      · have h1 := h (Sum.inl (g, i, j))
        rw [eoff g i j hij] at h1
        exact h1
    · intro v i g
      have h1 := h (Sum.inr ⟨v, i, g⟩)
      rw [eψ, map_sub, map_sub, AlgHom.commutes, AlgHom.commutes] at h1
      exact sub_left_injective h1
  have htw : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : S.R →ₐ[O] R')
      (t : Multiplicative ℤ →* R'ˣ), (∀ j, res O R' (t j) = 1) →
      ∃ f' : S.R →ₐ[O] R', ∀ s, f' (e s) = (t (Multiplicative.ofAdd (wt s)) : R') * f (e s) := by
    intro R' _ _ _ f t _
    obtain ⟨f', h1, h2⟩ := twist S R' f (t (Multiplicative.ofAdd 1))
    have ht : ∀ k : ℤ, t (Multiplicative.ofAdd k) = t (Multiplicative.ofAdd 1) ^ k := by
      intro k
      rw [← map_zpow, ← ofAdd_zsmul, smul_eq_mul, mul_one]
    refine ⟨f', ?_⟩
    rintro (⟨g, i, j⟩ | ⟨v, i, g⟩)
    · by_cases hij : i = j
      · subst hij
        show f' (e (Sum.inl (g, i, i))) = (t (Multiplicative.ofAdd (w n i - w n i)) : R') * _
        rw [sub_self, eon, map_sub, map_sub, AlgHom.commutes, AlgHom.commutes, h1]
        simp
      · show f' (e (Sum.inl (g, i, j))) = (t (Multiplicative.ofAdd (w n i - w n j)) : R') * _
        rw [eoff g i j hij, h1, ht (w n i - w n j)]
    · show f' (e (Sum.inr ⟨v, i, g⟩)) = (t (Multiplicative.ofAdd 0) : R') * _
      rw [eψ, map_sub, map_sub, AlgHom.commutes, AlgHom.commutes, h2]
      simp
  obtain ⟨W, u, hWu, hpart⟩ := coord_grading O ℤ S.R _ e wt he huniq htw
  have h1mem : ∀ c : O, algebraMap O S.R c ∈ W.part 0 := fun c => by
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ c SetLike.GradedOne.one_mem
  refine ⟨W, fun s => by rw [(hWu s).1]; exact he _, ?_, ?_, ?_⟩
  · intro g i j
    by_cases hij : i = j
    · subst hij
      have hp : S.ρ.r g i i - algebraMap O S.R (a (S.ρ.r g i i)) ∈ W.part 0 := by
        have := hpart (Sum.inl (g, i, i))
        rw [eon] at this
        simpa [wt] using this
      rw [sub_self, ← sub_add_cancel (S.ρ.r g i i) (algebraMap O S.R (a (S.ρ.r g i i)))]
      exact add_mem hp (h1mem _)
    · have hp := hpart (Sum.inl (g, i, j))
      rw [eoff g i j hij] at hp
      exact hp
  · intro v i g
    have hp : (S.ρ.ψ v i g : S.R) - algebraMap O S.R (a (S.ρ.ψ v i g)) ∈ W.part 0 :=
      hpart (Sum.inr ⟨v, i, g⟩)
    rw [← sub_add_cancel (S.ρ.ψ v i g : S.R) (algebraMap O S.R (a (S.ρ.ψ v i g)))]
    exact add_mem hp (h1mem _)
  · intro s
    obtain ⟨hz, hw⟩ := hWu s
    rcases hs : u s with ⟨g, i, j⟩ | ⟨v, i, g⟩
    · rw [hs] at hz hw
      by_cases hij : i = j
      · subst hij
        right
        refine ⟨by rw [hw]; exact sub_self _, ?_⟩
        rw [hz, eon]
        exact Subalgebra.sub_mem _ (Algebra.subset_adjoin (Or.inl ⟨[(g, i, i)], by simp, by simp⟩))
          (Subalgebra.algebraMap_mem _ _)
      · left
        exact ⟨g, i, j, by rw [hz, eoff g i j hij], hw⟩
    · rw [hs] at hz hw
      right
      refine ⟨hw, ?_⟩
      rw [hz, eψ]
      exact Subalgebra.sub_mem _ (Algebra.subset_adjoin (Or.inr ⟨v, i, g, rfl⟩))
        (Subalgebra.algebraMap_mem _ _)

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => simp`. Consider the case `cons a L ih`. Simplify using `only [List.map_cons, List.prod_cons, Subalgebra.coe_mul, ih]`. Both sides reduce to the same expression.
-/
private theorem val_prod {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)}
    {n : ℕ} (S : Space O F n) (L : List (F.G0 × Fin n × Fin n)) :
    (((L.map fun s => S.u.r s.1 s.2.1 s.2.2).prod : S.A) : S.R) = (L.map fun s => S.ρ.r s.1 s.2.1 s.2.2).prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons, Subalgebra.coe_mul, ih]
    rfl

/- English proof (translation)
Introduce `l _ O _ _ _ _ F C₀ n _ _ S`. Take `⟨W, hz, hr, hψ, hgen⟩` from `coord S`. Set `D : Subalgebra O S.R` to `Algebra.adjoin O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)})`. Establish `hmon : ∀ m, ∃ b ∈ D, ∃ x ∈ S.ρ.mon (Finsupp.weight W.wt m), W.π (MvPowerSeries.monomial m 1) = b * x` using `mono S.ρ W D hgen`. Establish `hD : ∀ m, Finsupp.weight W.wt m = 0 → W.π (MvPowerSeries.monomial m 1) ∈ D`.

Introduce `m hm`. Take `⟨b, hb, x, hx, e⟩` from `hmon m`. Rewrite using `[e]`. Rewrite `hx` using `[hm]`. Conclude with `D.mul_mem hb (Algebra.subset_adjoin (Or.inl hx))`.

Establish `P0 : ∀ y, y ∈ W.part 0 → y ∈ S.B` using `fun y hy => dense W hz D hD hy`. Set `P : Subalgebra O S.R` to `(W.part 0).toSubalgebra SetLike.GradedOne.one_mem (fun x y hx hy => by`. Use `SetLike.GradedMul.mul_mem hx hy` as an intermediate fact. Rewrite using `[add_zero] at this)` and apply the resulting hypothesis. Establish `BP : ∀ y, y ∈ S.B → y ∈ W.part 0`.

Introduce `y hy`. Establish `hDP : D ≤ P` using `Algebra.adjoin_le (by`. Introduce and unpack `x (hx | ⟨v, i, g, rfl⟩)`. Conclude with `mon_part S.ρ W hr hx`. Conclude with `hψ v i g)`.

Establish `hy' : ∀ N : ℕ, ∃ d ∈ D, y - d ∈ maximalIdeal S.R ^ N` using `hy`. Use `part_closed O ℤ S.R W hz 0 y fun N => ?_` and prove the remaining obligations. Take `⟨d, hd, hyd⟩` from `hy' N`. Conclude with `⟨d, hDP hd, hyd⟩`. Establish `dec : ∀ j y, y ∈ W.part j → ∃ μ : Finset (W.σ →₀ ℕ), ∃ c x : (W.σ →₀ ℕ) → S.R, (∀ m, c m ∈ S.B) ∧ (∀ m ∈ μ, x m ∈ S.ρ.mon j) ∧ y = ∑ m ∈ μ, c m * x m`.

Introduce `j y hy`. Simplify using `only [WPres.part, Submodule.mem_map] at hy`. Take `⟨f, hf, rfl⟩` from `hy`. Take `⟨μ, hμ, hspan⟩` from `part_span O S.R ℤ W {m | Finsupp.weight W.wt m = j} j (fun m hm => hm)`. Take `⟨b, hb, hfb⟩` from `hspan f (fun m hm => hf m hm)`.

Use `choose B hB X hX hBX using hmon`. Use `⟨μ, fun m => W.π (b m) * B m, X, fun m => S.B.mul_mem (P0 _ (Submodule.mem_map_of_mem (hb m))) (le_adicClosure D (hB m)), fun m hm => ?_, ?_⟩` and prove the remaining obligations. Use `hX m` as an intermediate fact. Establish `hw : Finsupp.weight W.wt m = j` using `hμ (Finset.mem_coe.mpr hm)`. Rewrite `this` using `[hw]`. Then use the resulting hypothesis.

Simplify using `only [AlgHom.toLinearMap_apply]`. Rewrite using `[hfb, map_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, hBX, mul_assoc]`. Use `⟨W, hz, hr, fun y => ⟨BP y, P0 y⟩, ?_, ?_⟩` and prove the remaining obligations.

Apply `le_antisymm` to reduce the goal to its premises. Use `Algebra.adjoin_le ?_` and prove the remaining obligations. Introduce and unpack `x (hx | ⟨g, i, j, rfl⟩)`. Conclude with `W.part_le_A (BP x hx)`. Conclude with `W.part_le_A (hr g i j)`.

Introduce `x hx`. Establish `hx' : x ∈ ⨆ j, W.part j` using `hx`. Establish `hle : (⨆ j, W.part j) ≤ Subalgebra.toSubmodule S.A`. Use `iSup_le fun j y hy => ?_` and prove the remaining obligations. Rewrite using `[Subalgebra.mem_toSubmodule]`.

Take `⟨μ, c, X, hc, hX, rfl⟩` from `dec j y hy`. Use `Subalgebra.sum_mem _ fun m hm => S.A.mul_mem (Algebra.subset_adjoin (Or.inl (hc m))) ?_` and prove the remaining obligations. Take `⟨L, -, hXL⟩` from `hX m hm`. Rewrite using `[hXL, ← val_prod S L]`. Conclude with `SetLike.coe_mem _`.

Conclude with `hle hx'`. Introduce `j a`. Prove the components needed by the constructor for the conclusion. Introduce `ha`. Use `Submodule.span_induction (p := fun (a : S.A) _ => (a : S.R) ∈ W.part j) ?_ ?_ ?_ ?_ (show a ∈ Submodule.span S.B (S.u.mon j) from ha)` and prove the remaining obligations.

Introduce and unpack `x ⟨L, hL, rfl⟩`. Rewrite using `[val_prod]`. Conclude with `mon_part S.ρ W hr ⟨L, hL, rfl⟩`. Simplify using the standard rewrite rules. Introduce `x y _ _ hx hy`.

Simplify using `using add_mem hx hy`. Introduce `b x _ hx`. Use `SetLike.GradedMul.mul_mem (BP b b.2) hx` as an intermediate fact. Rewrite `this` using `[zero_add]`. Apply the tactic sequence `have hbx : ((b • x : S.A) : S.R) = (b : S.R) * (x : S.R) := by first | rfl | simp [Algebra.smul_def] | simp [Subalgebra.smul_def]`.

Rewrite using `[hbx]`. Conclude with `this`. Introduce `ha`. Take `⟨μ, c, X, hc, hX, e⟩` from `dec j _ ha`. Establish `hXu : ∀ m ∈ μ, ∃ a' ∈ S.u.mon j, (a' : S.R) = X m`.

Introduce `m hm`. Take `⟨L, hL, e'⟩` from `hX m hm`. Conclude with `⟨_, ⟨L, hL, rfl⟩, by rw [val_prod, e']⟩`. Use `choose! A' hA' hA'e using hXu`. Establish `hsum : a = ∑ m ∈ μ, (⟨c m, hc m⟩ : S.B) • A' m`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[e]`. Simplify using `only [AddSubmonoidClass.coe_finset_sum]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Rewrite using `[← hA'e m hm]`.

Both sides reduce to the same expression. Rewrite using `[hsum]`. Conclude with `Submodule.sum_mem _ fun m hm => Submodule.smul_mem _ _ (Submodule.subset_span (hA' m hm))`.
-/
theorem UpperTheory.V.Fr.wpres :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∃ W : WPres O ℤ S.R, (∀ s, W.z s ∈ maximalIdeal S.R) ∧ (∀ g i j, S.ρ.r g i j ∈ W.part (w n i - w n j)) ∧ (∀ y, y ∈ S.B ↔ y ∈ W.part 0) ∧ S.A = W.A ∧ ∀ j (a : S.A), a ∈ S.gr j ↔ (a : S.R) ∈ W.part j := by
  intro l _ O _ _ _ _ F C₀ n _ _ S
  obtain ⟨W, hz, hr, hψ, hgen⟩ := coord S
  let D : Subalgebra O S.R := Algebra.adjoin O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)})
  have hmon : ∀ m, ∃ b ∈ D, ∃ x ∈ S.ρ.mon (Finsupp.weight W.wt m),
      W.π (MvPowerSeries.monomial m 1) = b * x := mono S.ρ W D hgen
  have hD : ∀ m, Finsupp.weight W.wt m = 0 → W.π (MvPowerSeries.monomial m 1) ∈ D := by
    intro m hm
    obtain ⟨b, hb, x, hx, e⟩ := hmon m
    rw [e]
    rw [hm] at hx
    exact D.mul_mem hb (Algebra.subset_adjoin (Or.inl hx))
  have P0 : ∀ y, y ∈ W.part 0 → y ∈ S.B := fun y hy => dense W hz D hD hy
  let P : Subalgebra O S.R := (W.part 0).toSubalgebra SetLike.GradedOne.one_mem (fun x y hx hy => by
    have := SetLike.GradedMul.mul_mem hx hy
    rwa [add_zero] at this)
  have BP : ∀ y, y ∈ S.B → y ∈ W.part 0 := by
    intro y hy
    have hDP : D ≤ P := Algebra.adjoin_le (by
      rintro x (hx | ⟨v, i, g, rfl⟩)
      · exact mon_part S.ρ W hr hx
      · exact hψ v i g)
    have hy' : ∀ N : ℕ, ∃ d ∈ D, y - d ∈ maximalIdeal S.R ^ N := hy
    refine part_closed O ℤ S.R W hz 0 y fun N => ?_
    obtain ⟨d, hd, hyd⟩ := hy' N
    exact ⟨d, hDP hd, hyd⟩
  have dec : ∀ j y, y ∈ W.part j → ∃ μ : Finset (W.σ →₀ ℕ), ∃ c x : (W.σ →₀ ℕ) → S.R,
      (∀ m, c m ∈ S.B) ∧ (∀ m ∈ μ, x m ∈ S.ρ.mon j) ∧ y = ∑ m ∈ μ, c m * x m := by
    intro j y hy
    simp only [WPres.part, Submodule.mem_map] at hy
    obtain ⟨f, hf, rfl⟩ := hy
    obtain ⟨μ, hμ, hspan⟩ := part_span O S.R ℤ W {m | Finsupp.weight W.wt m = j} j (fun m hm => hm)
    obtain ⟨b, hb, hfb⟩ := hspan f (fun m hm => hf m hm)
    choose B hB X hX hBX using hmon
    refine ⟨μ, fun m => W.π (b m) * B m, X,
      fun m => S.B.mul_mem (P0 _ (Submodule.mem_map_of_mem (hb m))) (le_adicClosure D (hB m)),
      fun m hm => ?_, ?_⟩
    · have := hX m
      have hw : Finsupp.weight W.wt m = j := hμ (Finset.mem_coe.mpr hm)
      rwa [hw] at this
    · simp only [AlgHom.toLinearMap_apply]
      rw [hfb, map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [map_mul, hBX, mul_assoc]
  refine ⟨W, hz, hr, fun y => ⟨BP y, P0 y⟩, ?_, ?_⟩
  · apply le_antisymm
    · refine Algebra.adjoin_le ?_
      rintro x (hx | ⟨g, i, j, rfl⟩)
      · exact W.part_le_A (BP x hx)
      · exact W.part_le_A (hr g i j)
    · intro x hx
      have hx' : x ∈ ⨆ j, W.part j := hx
      have hle : (⨆ j, W.part j) ≤ Subalgebra.toSubmodule S.A := by
        refine iSup_le fun j y hy => ?_
        rw [Subalgebra.mem_toSubmodule]
        obtain ⟨μ, c, X, hc, hX, rfl⟩ := dec j y hy
        refine Subalgebra.sum_mem _ fun m hm => S.A.mul_mem (Algebra.subset_adjoin (Or.inl (hc m))) ?_
        obtain ⟨L, -, hXL⟩ := hX m hm
        rw [hXL, ← val_prod S L]
        exact SetLike.coe_mem _
      exact hle hx'
  · intro j a
    constructor
    · intro ha
      refine Submodule.span_induction (p := fun (a : S.A) _ => (a : S.R) ∈ W.part j) ?_ ?_ ?_ ?_
        (show a ∈ Submodule.span S.B (S.u.mon j) from ha)
      · rintro x ⟨L, hL, rfl⟩
        rw [val_prod]
        exact mon_part S.ρ W hr ⟨L, hL, rfl⟩
      · simp
      · intro x y _ _ hx hy
        simpa using add_mem hx hy
      · intro b x _ hx
        have := SetLike.GradedMul.mul_mem (BP b b.2) hx
        rw [zero_add] at this
        have hbx : ((b • x : S.A) : S.R) = (b : S.R) * (x : S.R) := by
          first | rfl | simp [Algebra.smul_def] | simp [Subalgebra.smul_def]
        rw [hbx]
        exact this
    · intro ha
      obtain ⟨μ, c, X, hc, hX, e⟩ := dec j _ ha
      have hXu : ∀ m ∈ μ, ∃ a' ∈ S.u.mon j, (a' : S.R) = X m := by
        intro m hm
        obtain ⟨L, hL, e'⟩ := hX m hm
        exact ⟨_, ⟨L, hL, rfl⟩, by rw [val_prod, e']⟩
      choose! A' hA' hA'e using hXu
      have hsum : a = ∑ m ∈ μ, (⟨c m, hc m⟩ : S.B) • A' m := by
        apply Subtype.ext
        rw [e]
        simp only [AddSubmonoidClass.coe_finset_sum]
        refine Finset.sum_congr rfl fun m hm => ?_
        rw [← hA'e m hm]
        rfl
      rw [hsum]
      exact Submodule.sum_mem _ fun m hm => Submodule.smul_mem _ _ (Submodule.subset_span (hA' m hm))
