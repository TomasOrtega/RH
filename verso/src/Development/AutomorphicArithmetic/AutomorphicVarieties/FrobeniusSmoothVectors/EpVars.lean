import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpresDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpBasis
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SgWeight
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSurj
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EvDecomp

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

open MvPowerSeries in
/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qf39.ev_decomp f`.
-/
private theorem ev_decomp {O σ : Type} [CommRing O] [Fintype σ] (f : MvPowerSeries σ O) :
    ∃ h : σ → MvPowerSeries σ O, f = C (constantCoeff f) + ∑ i, MvPowerSeries.X i * h i ∧
      ∀ i, constantCoeff (h i) = coeff (Finsupp.single i 1) f :=
  _root_.UpperTheory.Reformulated.B.Qf39.ev_decomp f

/- English proof (translation)
Rewrite using `[← res_eq_zero_iff O, res_map, res_eq_zero_iff]`.
-/
private theorem ev_max {O : Type} [CommRing O] [IsLocalRing O] {R : Type} [CommRing R] [Algebra O R]
    [IsCO O R] {R' : Type} [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') {x : R} :
    f x ∈ maximalIdeal R' ↔ x ∈ maximalIdeal R := by
  rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]

/- English proof (translation)
Simplify using `[sg]`.
-/
private theorem ev_sg_map {O A B : Type} [CommRing O] [CommRing A] [CommRing B] [Algebra O A] [Algebra O B]
    (f : A →ₐ[O] B) (j : ZMod 2) : f (sg A j) = sg B j := by
  simp [sg]

/- English proof (translation)
Rewrite using `[sg, ← mul_pow]`. Simplify using the standard rewrite rules.
-/
private theorem ev_sg_sq (A : Type) [CommRing A] (j : ZMod 2) : sg A j * sg A j = 1 := by
  rw [sg, ← mul_pow]; simp

/- English proof (translation)
Introduce `O _ _ _ _ h2 R _ _ _ σ hσ`. Establish `h2R : IsUnit (2 : R)`. Use `h2.map (algebraMap O R)` as an intermediate fact. Rewrite `this` using `[map_ofNat]`. Then use the resulting hypothesis. Take `⟨a, g, z, hz, hspan, hind⟩` from `ep_basis O h2 R σ hσ (maximalIdeal R) ((maximalIdeal O).map (algebraMap O R) ⊔ maximalIdeal R ^ 2) (fun y hy => (ev_max σ).2 hy) (by`.

Establish `: (maximalIdeal O).map (algebraMap O R) ⊔ maximalIdeal R ^ 2 ≤ ((maximalIdeal O).map (algebraMap O R) ⊔ maximalIdeal R ^ 2).comap σ`. Use `sup_le ?_ ?_` and prove the remaining obligations. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `c hc`. Rewrite using `[Ideal.mem_comap, Ideal.mem_comap, AlgHom.commutes]`.

Conclude with `Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hc)`. Use `le_trans ?_ (Ideal.comap_mono le_sup_right)` and prove the remaining obligations. Use `le_trans (Ideal.pow_right_mono ?_ 2) (Ideal.le_comap_pow σ 2)` and prove the remaining obligations. Conclude with `fun y hy => (ev_max σ).2 hy`. Conclude with `fun y hy => this hy)`.

Use the proof step `(by rw [← pow_two]; exact le_sup_right)`. Take `⟨τ, -, hτe, hτw⟩` from `ep_ps O h2 (Fin a ⊕ Fin g) (Space.Loc.par a g)`. Use `haveI := co_mvps O O (Fin a ⊕ Fin g)`. Take `⟨p, ⟨-, hpX⟩, -⟩` from `co_ev O O R (Fin a ⊕ Fin g) (Algebra.ofId O R) z fun s => (hz s).1`. Establish `hC : ∀ (H : MvPowerSeries (Fin a ⊕ Fin g) O →ₐ[O] R) (x : O), H (MvPowerSeries.C x) = Algebra.ofId O R x` using `fun H x => by`.

Use `H.commutes x` as an intermediate fact. Rewrite `this` using `[MvPowerSeries.algebraMap_apply]`. Conclude with `this`. Establish `hsurj : Function.Surjective p`. Use `co_surj O _ R p (hspan.trans (sup_le (le_sup_of_le_left ?_) (sup_le_sup_right ?_ _)))` and prove the remaining obligations.

Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨s, rfl⟩`. Rewrite using `[← hpX]`. Use `Ideal.mem_map_of_mem p ((ev_max p).1 ?_)` and prove the remaining obligations. Rewrite using `[hpX]`.

Conclude with `(hz s).1`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `c hc`. Rewrite using `[Ideal.mem_comap, ← p.commutes]`. Use `Ideal.mem_map_of_mem p ?_` and prove the remaining obligations.

Conclude with `(ev_max (Algebra.ofId O _)).2 hc`. Establish `heq : p.comp τ = σ.comp p`. Use `(co_ev O O R (Fin a ⊕ Fin g) (Algebra.ofId O R) (fun s => σ (z s)) fun s => (ev_max σ).2 (hz s).1).unique ⟨hC _, fun s => ?_⟩ ⟨hC _, fun s => ?_⟩` and prove the remaining obligations. Establish `h1 : (MvPowerSeries.X s : MvPowerSeries (Fin a ⊕ Fin g) O) ∈ evp τ (Space.Loc.par a g s)`. Rewrite using `[hτe]`.

Conclude with `X_mem_wtPart O _ s`. Establish `h3 : τ (MvPowerSeries.X s) = _` using `h1`. Establish `h4 : σ (z s) = _` using `(hz s).2`. Rewrite using `[AlgHom.comp_apply, h3, h4, map_mul, ev_sg_map, hpX]`. Rewrite using `[AlgHom.comp_apply, hpX]`.

Establish `heq' : ∀ y, p (τ y) = σ (p y)` using `fun y => DFunLike.congr_fun heq y`. Establish `hw : ∀ j y, 2 * p (wcomp O (Space.Loc.par a g) j y) = p y + sg R j * σ (p y)` using `fun j y => by`. Use `congrArg p (hτw j y)` as an intermediate fact. Rewrite `this` using `[map_mul, map_ofNat, map_add, map_mul, ev_sg_map, heq']`. Then use the resulting hypothesis. Use `⟨a, g, p, hsurj, fun s => by rw [hpX]; exact (hz s).1, fun j => le_antisymm ?_ fun x hx => ?_, fun f hf j => ?_, fun h hh => ?_⟩` and prove the remaining obligations.

Introduce and unpack `_ ⟨f, hf, rfl⟩`. Establish `h1 : f ∈ evp τ j` using `by rw [hτe]; exact hf`. Establish `h3 : τ f = _` using `h1`. Use `show σ (p f) = sg R j * p f`. Rewrite using `[← heq', h3, map_mul, ev_sg_map]`.

Take `⟨y, rfl⟩` from `hsurj x`. Establish `h1 : σ (p y) = _` using `hx`. Use `⟨_, wcomp_mem O _ j y, ?_⟩` and prove the remaining obligations. Use `show p _ = p y`. Use `h2R.mul_left_cancel ?_` and prove the remaining obligations.

Rewrite using `[hw, h1, ← mul_assoc, ev_sg_sq, one_mul, two_mul]`. Establish `h1 : p f = 0` using `hf show p _ = 0`. Use `h2R.mul_left_cancel ?_` and prove the remaining obligations. Rewrite using `[hw, h1]`. Simplify using the standard rewrite rules.

Take `⟨u, hu, hu0⟩` from `ev_decomp h`. Establish `h0 : p h = 0` using `hh`. Establish `h1 : algebraMap O R (MvPowerSeries.constantCoeff h) + ∑ i, z i * p (u i) = 0`. Rewrite `h0` using `[hu, map_add, map_sum, hC]`. Simplify using `only [map_mul, hpX] at h0`.

Conclude with `h0`. Establish `h3 : MvPowerSeries.constantCoeff h ∈ maximalIdeal O`. Rewrite using `[← ev_max (Algebra.ofId O R)]`. Use `show algebraMap O R _ ∈ _`. Rewrite using `[eq_neg_of_add_eq_zero_left h1]`.

Conclude with `neg_mem (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hz i).1)`. Use `hind (fun s => MvPowerSeries.coeff (Finsupp.single s 1) h) ?_` and prove the remaining obligations. Establish `h4 : ∑ s, MvPowerSeries.coeff (Finsupp.single s 1) h • z s = -algebraMap O R (MvPowerSeries.constantCoeff h) + ∑ s, z s * p (MvPowerSeries.C (MvPowerSeries.coeff (Finsupp.single s 1) h) - u s)`. Rewrite using `[eq_neg_of_add_eq_zero_left h1, neg_neg, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations.

Rewrite using `[map_sub, hC, Algebra.smul_def, Algebra.ofId_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h4]`. Use `Submodule.add_mem_sup (neg_mem (Ideal.mem_map_of_mem _ h3)) (Ideal.sum_mem _ fun s _ => ?_)` and prove the remaining obligations. Rewrite using `[pow_two]`.

Use `Ideal.mul_mem_mul (hz s).1 ((ev_max p).2 fun hU => ?_)` and prove the remaining obligations. Establish `h5` using `MvPowerSeries.isUnit_constantCoeff _ hU`. Rewrite `h5` using `[map_sub, hu0, MvPowerSeries.constantCoeff_C, sub_self]`. Conclude with `not_isUnit_zero h5`.
-/
theorem UpperTheory.V.Fr.ep_vars :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O], IsUnit (2 : O) → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (σ : R →ₐ[O] R), (∀ y, σ (σ y) = y) → ∃ (a g : ℕ) (p : MvPowerSeries (Fin a ⊕ Fin g) O →ₐ[O] R), Function.Surjective p ∧ (∀ s, p (MvPowerSeries.X s) ∈ maximalIdeal R) ∧ (∀ j, (wtPart O (Space.Loc.par a g) j).map p.toLinearMap = evp σ j) ∧ IsHomog O (Space.Loc.par a g) (RingHom.ker p) ∧ ∀ h ∈ RingHom.ker p, ∀ s, MvPowerSeries.coeff (Finsupp.single s 1) h ∈ maximalIdeal O := by
  intro O _ _ _ _ h2 R _ _ _ σ hσ
  have h2R : IsUnit (2 : R) := by
    have := h2.map (algebraMap O R)
    rwa [map_ofNat] at this
  obtain ⟨a, g, z, hz, hspan, hind⟩ := ep_basis O h2 R σ hσ (maximalIdeal R)
    ((maximalIdeal O).map (algebraMap O R) ⊔ maximalIdeal R ^ 2) (fun y hy => (ev_max σ).2 hy)
    (by
      have : (maximalIdeal O).map (algebraMap O R) ⊔ maximalIdeal R ^ 2 ≤
          ((maximalIdeal O).map (algebraMap O R) ⊔ maximalIdeal R ^ 2).comap σ := by
        refine sup_le ?_ ?_
        · rw [Ideal.map_le_iff_le_comap]
          intro c hc
          rw [Ideal.mem_comap, Ideal.mem_comap, AlgHom.commutes]
          exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hc)
        · refine le_trans ?_ (Ideal.comap_mono le_sup_right)
          refine le_trans (Ideal.pow_right_mono ?_ 2) (Ideal.le_comap_pow σ 2)
          exact fun y hy => (ev_max σ).2 hy
      exact fun y hy => this hy)
    (by rw [← pow_two]; exact le_sup_right)
  obtain ⟨τ, -, hτe, hτw⟩ := ep_ps O h2 (Fin a ⊕ Fin g) (Space.Loc.par a g)
  haveI := co_mvps O O (Fin a ⊕ Fin g)
  obtain ⟨p, ⟨-, hpX⟩, -⟩ := co_ev O O R (Fin a ⊕ Fin g) (Algebra.ofId O R) z fun s => (hz s).1
  have hC : ∀ (H : MvPowerSeries (Fin a ⊕ Fin g) O →ₐ[O] R) (x : O),
      H (MvPowerSeries.C x) = Algebra.ofId O R x := fun H x => by
    have := H.commutes x
    rw [MvPowerSeries.algebraMap_apply] at this
    exact this
  have hsurj : Function.Surjective p := by
    refine co_surj O _ R p (hspan.trans (sup_le (le_sup_of_le_left ?_) (sup_le_sup_right ?_ _)))
    · rw [Ideal.span_le]
      rintro _ ⟨s, rfl⟩
      rw [← hpX]
      refine Ideal.mem_map_of_mem p ((ev_max p).1 ?_)
      rw [hpX]
      exact (hz s).1
    · rw [Ideal.map_le_iff_le_comap]
      intro c hc
      rw [Ideal.mem_comap, ← p.commutes]
      refine Ideal.mem_map_of_mem p ?_
      exact (ev_max (Algebra.ofId O _)).2 hc
  have heq : p.comp τ = σ.comp p := by
    refine (co_ev O O R (Fin a ⊕ Fin g) (Algebra.ofId O R) (fun s => σ (z s))
      fun s => (ev_max σ).2 (hz s).1).unique ⟨hC _, fun s => ?_⟩ ⟨hC _, fun s => ?_⟩
    · have h1 : (MvPowerSeries.X s : MvPowerSeries (Fin a ⊕ Fin g) O) ∈ evp τ (Space.Loc.par a g s) := by
        rw [hτe]; exact X_mem_wtPart O _ s
      have h3 : τ (MvPowerSeries.X s) = _ := h1
      have h4 : σ (z s) = _ := (hz s).2
      rw [AlgHom.comp_apply, h3, h4, map_mul, ev_sg_map, hpX]
    · rw [AlgHom.comp_apply, hpX]
  have heq' : ∀ y, p (τ y) = σ (p y) := fun y => DFunLike.congr_fun heq y
  have hw : ∀ j y, 2 * p (wcomp O (Space.Loc.par a g) j y) = p y + sg R j * σ (p y) := fun j y => by
    have := congrArg p (hτw j y)
    rwa [map_mul, map_ofNat, map_add, map_mul, ev_sg_map, heq'] at this
  refine ⟨a, g, p, hsurj, fun s => by rw [hpX]; exact (hz s).1, fun j => le_antisymm ?_ fun x hx => ?_,
    fun f hf j => ?_, fun h hh => ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    have h1 : f ∈ evp τ j := by rw [hτe]; exact hf
    have h3 : τ f = _ := h1
    show σ (p f) = sg R j * p f
    rw [← heq', h3, map_mul, ev_sg_map]
  · obtain ⟨y, rfl⟩ := hsurj x
    have h1 : σ (p y) = _ := hx
    refine ⟨_, wcomp_mem O _ j y, ?_⟩
    show p _ = p y
    refine h2R.mul_left_cancel ?_
    rw [hw, h1, ← mul_assoc, ev_sg_sq, one_mul, two_mul]
  · have h1 : p f = 0 := hf
    show p _ = 0
    refine h2R.mul_left_cancel ?_
    rw [hw, h1]
    simp
  · obtain ⟨u, hu, hu0⟩ := ev_decomp h
    have h0 : p h = 0 := hh
    have h1 : algebraMap O R (MvPowerSeries.constantCoeff h) + ∑ i, z i * p (u i) = 0 := by
      rw [hu, map_add, map_sum, hC] at h0
      simp only [map_mul, hpX] at h0
      exact h0
    have h3 : MvPowerSeries.constantCoeff h ∈ maximalIdeal O := by
      rw [← ev_max (Algebra.ofId O R)]
      show algebraMap O R _ ∈ _
      rw [eq_neg_of_add_eq_zero_left h1]
      exact neg_mem (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hz i).1)
    refine hind (fun s => MvPowerSeries.coeff (Finsupp.single s 1) h) ?_
    have h4 : ∑ s, MvPowerSeries.coeff (Finsupp.single s 1) h • z s =
        -algebraMap O R (MvPowerSeries.constantCoeff h) +
          ∑ s, z s * p (MvPowerSeries.C (MvPowerSeries.coeff (Finsupp.single s 1) h) - u s) := by
      rw [eq_neg_of_add_eq_zero_left h1, neg_neg, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [map_sub, hC, Algebra.smul_def, Algebra.ofId_apply]
      ring
    rw [h4]
    refine Submodule.add_mem_sup (neg_mem (Ideal.mem_map_of_mem _ h3)) (Ideal.sum_mem _ fun s _ => ?_)
    rw [pow_two]
    refine Ideal.mul_mem_mul (hz s).1 ((ev_max p).2 fun hU => ?_)
    have h5 := MvPowerSeries.isUnit_constantCoeff _ hU
    rw [map_sub, hu0, MvPowerSeries.constantCoeff_C, sub_self] at h5
    exact not_isUnit_zero h5
