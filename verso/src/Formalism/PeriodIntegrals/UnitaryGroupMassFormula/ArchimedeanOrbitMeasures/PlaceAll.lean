import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DetMulRCReal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PiCoord

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Matrix
open scoped ENNReal NNReal

/- English proof (translation)
Use `Measure.pi_eq fun s hs => ?_` and prove the remaining obligations. Rewrite using `[Measure.smul_apply, Measure.pi_pi, smul_eq_mul, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[Measure.smul_apply]`. Both sides reduce to the same expression.
-/
theorem pi_smul_measure {V : Type} [Fintype V] {X : V → Type} [∀ v, MeasurableSpace (X v)]
    (μ : ∀ v, Measure (X v)) [∀ v, SigmaFinite (μ v)] (c : V → ℝ≥0) :
    Measure.pi (fun v => c v • μ v) = (∏ v, (c v : ℝ≥0∞)) • Measure.pi μ := by
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Measure.smul_apply]
  rfl

/- English proof (translation)
Use `haveI : ∀ v, SigmaFinite (μ v) := fun v => SigmaFinite.of_map (μ v) (hf v).aemeasurable (by rw [hc v]; infer_instance)`. Rewrite using `[← pi_smul_measure]`. Use `symm`. Use `Measure.pi_eq fun s hs => ?_` and prove the remaining obligations. Establish `hmeas : Measurable (fun x : ∀ v, X v => fun v => f v (x v))` using `measurable_pi_lambda _ fun v => (hf v).comp (measurable_pi_apply v)`.

Rewrite using `[Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]`. Establish `hpre : (fun x : ∀ v, X v => fun v => f v (x v)) ⁻¹' Set.univ.pi s = Set.univ.pi (fun v => f v ⁻¹' s v)`. Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite using `[hpre, Measure.pi_pi]`.

Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[← hc v, Measure.map_apply (hf v) (hs v)]`.
-/
theorem pi_map_smul {V : Type} [Fintype V] {X Y : V → Type} [∀ v, MeasurableSpace (X v)]
    [∀ v, MeasurableSpace (Y v)] (μ : ∀ v, Measure (X v)) (ν : ∀ v, Measure (Y v)) [∀ v, SigmaFinite (ν v)]
    (f : ∀ v, X v → Y v) (hf : ∀ v, Measurable (f v)) (c : V → ℝ≥0)
    (hc : ∀ v, (μ v).map (f v) = c v • ν v) :
    (Measure.pi μ).map (fun x v => f v (x v)) = (∏ v, (c v : ℝ≥0∞)) • Measure.pi ν := by
  haveI : ∀ v, SigmaFinite (μ v) := fun v =>
    SigmaFinite.of_map (μ v) (hf v).aemeasurable (by rw [hc v]; infer_instance)
  rw [← pi_smul_measure]
  symm
  refine Measure.pi_eq fun s hs => ?_
  have hmeas : Measurable (fun x : ∀ v, X v => fun v => f v (x v)) :=
    measurable_pi_lambda _ fun v => (hf v).comp (measurable_pi_apply v)
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have hpre : (fun x : ∀ v, X v => fun v => f v (x v)) ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun v => f v ⁻¹' s v) := by
    ext x
    simp
  rw [hpre, Measure.pi_pi]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← hc v, Measure.map_apply (hf v) (hs v)]

/- English proof (translation)
Establish `key : ∀ s : Set F, MeasurableSet s → μ ((f : E → F) ⁻¹' s) = c * ν s`. Introduce `s hs`. Establish `h1` using `congrArg (fun ρ : Measure F => ρ s) h`. Simplify using `only [Measure.smul_apply, smul_eq_mul] at h1`. Rewrite `h1` using `[Measure.map_apply (LinearMap.continuous_of_finiteDimensional f).measurable hs]`. Then use the resulting hypothesis.

Establish `hsurj : Function.Surjective f`. Assume the negation of the conclusion as `hns`. Establish `hr : LinearMap.range f ≠ ⊤` using `fun hh => hns (LinearMap.range_eq_top.mp hh)`. Establish `h0 : ν (LinearMap.range f : Set F) = 0` using `Measure.addHaar_submodule ν _ hr`. Establish `hm : MeasurableSet (LinearMap.range f : Set F)` using `(Submodule.closed_of_finiteDimensional (LinearMap.range f)).measurableSet`.

Establish `h1` using `key _ hm`. Rewrite `h1` using `[h0, mul_zero]`. Establish `hpre : (f : E → F) ⁻¹' (LinearMap.range f : Set F) = Set.univ`. Use extensionality with `x`. Simplify using the standard rewrite rules.

Rewrite `h1` using `[hpre]`. Conclude with `(IsOpen.measure_pos μ isOpen_univ Set.univ_nonempty).ne' h1`. Establish `hdim : Module.finrank ℝ E = Module.finrank ℝ F` using `by set K : Set F := Metric.closedBall 0 1 with hKdef`. Establish `hKc : IsCompact K` using `isCompact_closedBall 0 1`. Establish `hKm : MeasurableSet K` using `hKc.isClosed.measurableSet`.

Establish `hK0 : ν K ≠ 0` using `(Metric.measure_closedBall_pos ν (0 : F) one_pos).ne'`. Establish `hKt : ν K ≠ ⊤` using `hKc.measure_lt_top.ne`. Use `open Pointwise in`. Establish `h2m : MeasurableSet ((2 : ℝ) • K)` using `(hKc.smul (2 : ℝ)).isClosed.measurableSet`. Use `open Pointwise in`.

Establish `hpre : (f : E → F) ⁻¹' ((2 : ℝ) • K) = (2 : ℝ) • ((f : E → F) ⁻¹' K)`. Use extensionality with `x`. Simplify using `only [Set.mem_preimage, Set.mem_smul_set]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, hxy⟩`.

Use `⟨(1 / 2 : ℝ) • x, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, ← hxy, smul_smul]`. Evaluate the numerical expressions. Conclude with `hy`. Rewrite using `[smul_smul]`.

Evaluate the numerical expressions. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `⟨f y, hy, (map_smul f (2 : ℝ) y).symm⟩`. Establish `e1` using `key _ h2m`. Rewrite `e1` using `[hpre, Measure.addHaar_smul, key K hKm, Measure.addHaar_smul]`.

Use `set X := c * ν K with hX`. Establish `hX0 : X ≠ 0` using `mul_ne_zero h0 hK0`. Establish `hXt : X ≠ ⊤` using `ENNReal.mul_ne_top htop hKt`. Establish `e2 : ENNReal.ofReal |(2 : ℝ) ^ Module.finrank ℝ E| * X = ENNReal.ofReal |(2 : ℝ) ^ Module.finrank ℝ F| * X`. Rewrite using `[e1, hX]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hu : IsUnit X` using `isUnit_iff_exists_inv.mpr ⟨X⁻¹, ENNReal.mul_inv_cancel hX0 hXt⟩`. Establish `e3` using `hu.mul_left_inj.mp e2`. Rewrite `e3` using `[ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)]`. Establish `e4 : (2 : ℕ) ^ Module.finrank ℝ E = 2 ^ Module.finrank ℝ F`.

Establish `e5 : ((2 : ℕ) : ℝ) ^ Module.finrank ℝ E = ((2 : ℕ) : ℝ) ^ Module.finrank ℝ F`. Simplify using `using e3`. Conclude with `e5` after adjusting the coercions. Conclude with `Nat.pow_right_injective (le_refl 2) e4`. Conclude with `⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj, hsurj⟩`.
-/
theorem bij_of_map {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] (μ : Measure E) [μ.IsAddHaarMeasure] (ν : Measure F) [ν.IsAddHaarMeasure]
    (f : E →ₗ[ℝ] F) (c : ℝ≥0∞) (h0 : c ≠ 0) (htop : c ≠ ⊤) (h : μ.map f = c • ν) : Function.Bijective f := by
  have key : ∀ s : Set F, MeasurableSet s → μ ((f : E → F) ⁻¹' s) = c * ν s := by
    intro s hs
    have h1 := congrArg (fun ρ : Measure F => ρ s) h
    simp only [Measure.smul_apply, smul_eq_mul] at h1
    rwa [Measure.map_apply (LinearMap.continuous_of_finiteDimensional f).measurable hs] at h1
  have hsurj : Function.Surjective f := by
    by_contra hns
    have hr : LinearMap.range f ≠ ⊤ := fun hh => hns (LinearMap.range_eq_top.mp hh)
    have h0 : ν (LinearMap.range f : Set F) = 0 := Measure.addHaar_submodule ν _ hr
    have hm : MeasurableSet (LinearMap.range f : Set F) :=
      (Submodule.closed_of_finiteDimensional (LinearMap.range f)).measurableSet
    have h1 := key _ hm
    rw [h0, mul_zero] at h1
    have hpre : (f : E → F) ⁻¹' (LinearMap.range f : Set F) = Set.univ := by
      ext x
      simp
    rw [hpre] at h1
    exact (IsOpen.measure_pos μ isOpen_univ Set.univ_nonempty).ne' h1
  have hdim : Module.finrank ℝ E = Module.finrank ℝ F := by
    set K : Set F := Metric.closedBall 0 1 with hKdef
    have hKc : IsCompact K := isCompact_closedBall 0 1
    have hKm : MeasurableSet K := hKc.isClosed.measurableSet
    have hK0 : ν K ≠ 0 := (Metric.measure_closedBall_pos ν (0 : F) one_pos).ne'
    have hKt : ν K ≠ ⊤ := hKc.measure_lt_top.ne
    open Pointwise in
    have h2m : MeasurableSet ((2 : ℝ) • K) := (hKc.smul (2 : ℝ)).isClosed.measurableSet
    open Pointwise in
    have hpre : (f : E → F) ⁻¹' ((2 : ℝ) • K) = (2 : ℝ) • ((f : E → F) ⁻¹' K) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_smul_set]
      constructor
      · rintro ⟨y, hy, hxy⟩
        refine ⟨(1 / 2 : ℝ) • x, ?_, ?_⟩
        · rw [map_smul, ← hxy, smul_smul]
          norm_num
          exact hy
        · rw [smul_smul]
          norm_num
      · rintro ⟨y, hy, rfl⟩
        exact ⟨f y, hy, (map_smul f (2 : ℝ) y).symm⟩
    have e1 := key _ h2m
    rw [hpre, Measure.addHaar_smul, key K hKm, Measure.addHaar_smul] at e1
    set X := c * ν K with hX
    have hX0 : X ≠ 0 := mul_ne_zero h0 hK0
    have hXt : X ≠ ⊤ := ENNReal.mul_ne_top htop hKt
    have e2 : ENNReal.ofReal |(2 : ℝ) ^ Module.finrank ℝ E| * X =
        ENNReal.ofReal |(2 : ℝ) ^ Module.finrank ℝ F| * X := by
      rw [e1, hX]
      ring
    have hu : IsUnit X := isUnit_iff_exists_inv.mpr ⟨X⁻¹, ENNReal.mul_inv_cancel hX0 hXt⟩
    have e3 := hu.mul_left_inj.mp e2
    rw [ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)] at e3
    have e4 : (2 : ℕ) ^ Module.finrank ℝ E = 2 ^ Module.finrank ℝ F := by
      have e5 : ((2 : ℕ) : ℝ) ^ Module.finrank ℝ E = ((2 : ℕ) : ℝ) ^ Module.finrank ℝ F := by
        simpa using e3
      exact_mod_cast e5
    exact Nat.pow_right_injective (le_refl 2) e4
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj, hsurj⟩

/- English proof (translation)
Rewrite using `[EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.sum_bool, Complex.sq_norm, Complex.normSq_apply]`.

Simplify using `[reimE, reim, Real.norm_eq_abs, sq_abs, sq]`.
-/
theorem norm_reimE_sq {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℂ) :
    ‖reimE (r := a) (m := b) M‖ ^ 2 = ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool, Complex.sq_norm, Complex.normSq_apply]
  simp [reimE, reim, Real.norm_eq_abs, sq_abs, sq]

set_option maxHeartbeats 800000 in

/- English proof (translation)
Set `R : Matrix (Fin a) (Fin b) ℂ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin a × Fin b × Bool)` to `reimE (r := a) (m := b)`. Establish `hRn : ∀ M : Matrix (Fin a) (Fin b) ℂ, ‖R M‖ ^ 2 = ∑ i, ∑ j, ‖M i j‖ ^ 2` using `fun M => norm_reimE_sq M`. Set `S : V → Submodule ℝ (EuclideanSpace ℝ (Fin a × Fin b × Bool))` to `fun v => LinearMap.range (R.toLinearMap ∘ₗ (LinearMap.proj v ∘ₗ L))`. Establish `hmem : ∀ v (M : Matrix (Fin a) (Fin b) ℂ), R M ∈ S v ↔ Q v M`. Introduce `v M`.

Prove the components needed by the constructor for the conclusion. Introduce `hM`. Take `⟨x, hx⟩` from `LinearMap.mem_range.mp hM`. Establish `hx' : R (L x v) = R M` using `by simpa using hx`. Rewrite using `[← R.injective hx']`.

Conclude with `hQ x v`. Introduce `hq`. Take `⟨x, hx⟩` from `hs (Pi.single v M) (fun w => by`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality.

Rewrite using `[Pi.single_eq_same]`. Conclude with `hq`. Rewrite using `[Pi.single_eq_of_ne hw]`. Conclude with `hQ0 w)`. Use `LinearMap.mem_range.mpr ⟨x, ?_⟩` and prove the remaining obligations.

Simplify using `[hx]`. Set `n : V → ℕ` to `fun v => Module.finrank ℝ (S v)`. Set `B : ∀ v, OrthonormalBasis (Fin (n v)) ℝ (S v)` to `fun v => stdOrthonormalBasis ℝ (S v)`. Set `Lv : ∀ v, EuclideanSpace ℝ (Fin (n v)) →ₗ[ℝ] Matrix (Fin a) (Fin b) ℂ` to `fun v => R.symm.toLinearMap ∘ₗ (S v).subtype ∘ₗ (B v).repr.symm.toLinearEquiv.toLinearMap`. Establish `hLv_apply : ∀ v y, R (Lv v y) = ((B v).repr.symm y : EuclideanSpace ℝ (Fin a × Fin b × Bool))`.

Introduce `v y`. Simplify using `[Lv]`. Establish `hLv_norm : ∀ v y, ∑ i, ∑ j, ‖Lv v y i j‖ ^ 2 = ‖y‖ ^ 2`. Introduce `v y`. Rewrite using `[← hRn, hLv_apply]`.

Conclude with `congrArg (fun t => t ^ 2) ((B v).repr.symm.norm_map y)`. Establish `hLvQ : ∀ v y, Q v (Lv v y)`. Introduce `v y`. Use `(hmem v _).mp ?_` and prove the remaining obligations. Rewrite using `[hLv_apply]`.

Conclude with `((B v).repr.symm y).2`. Establish `hLvSurj : ∀ v M, Q v M → ∃ y, Lv v y = M`. Introduce `v M hq`. Use `⟨(B v).repr ⟨R M, (hmem v M).mpr hq⟩, ?_⟩` and prove the remaining obligations. Apply `R.injective` to reduce the goal to its premises.

Rewrite using `[hLv_apply, LinearIsometryEquiv.symm_apply_apply]`. Establish `hLvinj : ∀ v, Function.Injective (Lv v)`. Introduce `v`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `y hy`.

Establish `h1` using `hLv_norm v y`. Rewrite `h1` using `[hy]`. Establish `h2 : ‖y‖ ^ 2 = 0`. Rewrite using `[← h1]`. Simplify using the standard rewrite rules.

Conclude with `norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h2)`. Establish `hLinj : Function.Injective L`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `y hy`. Establish `h1` using `hn y`.

Rewrite `h1` using `[hy]`. Establish `h2 : ‖y‖ ^ 2 = 0`. Rewrite using `[← h1]`. Simplify using the standard rewrite rules. Conclude with `norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h2)`.

Set `Tv : ∀ v, EuclideanSpace ℝ ι →ₗ[ℝ] S v` to `fun v => LinearMap.codRestrict (S v) (R.toLinearMap ∘ₗ (LinearMap.proj v ∘ₗ L)) (fun x => LinearMap.mem_range_self _ x)`. Set `T : EuclideanSpace ℝ ι →ₗ[ℝ] ∀ v, EuclideanSpace ℝ (Fin (n v))` to `LinearMap.pi fun v => (B v).repr.toLinearEquiv.toLinearMap ∘ₗ Tv v`. Establish `hTL : ∀ x v, Lv v (T x v) = L x v`. Introduce `x v`. Apply `R.injective` to reduce the goal to its premises.

Rewrite using `[hLv_apply]`. Simplify using `[T, Tv]`. Establish `hTinj : Function.Injective T`. Introduce `x x' hxx`. Apply `hLinj` to reduce the goal to its premises.

Use function extensionality and compare the values at `v`. Rewrite using `[← hTL x v, ← hTL x' v, hxx]`. Establish `hTsurj : Function.Surjective T`. Introduce `y`. Take `⟨x, hx⟩` from `hs (fun v => Lv v (y v)) (fun v => hLvQ v (y v))`.

Use `⟨x, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `v`. Apply `hLvinj v` to reduce the goal to its premises. Rewrite using `[hTL, hx]`. Establish `hTnorm : ∀ x, ∑ v, ‖T x v‖ ^ 2 = ‖x‖ ^ 2`.

Introduce `x`. Rewrite using `[← hn x]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[← hLv_norm v (T x v), hTL]`. Conclude with `⟨fun v => Fin (n v), fun v => inferInstance, Lv, T, hLvQ, hLv_norm, hLvSurj, hTL, ⟨hTinj, hTsurj⟩, hTnorm⟩`.
-/
theorem place_split {V : Type} [Fintype V] {a b : ℕ} {ι : Type} [Fintype ι]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (V → Matrix (Fin a) (Fin b) ℂ)) (Q : V → Matrix (Fin a) (Fin b) ℂ → Prop)
    (hQ : ∀ x v, Q v (L x v)) (hQ0 : ∀ v, Q v 0)
    (hn : ∀ x, ∑ v, ∑ i, ∑ j, ‖L x v i j‖ ^ 2 = ‖x‖ ^ 2)
    (hs : ∀ M : V → Matrix (Fin a) (Fin b) ℂ, (∀ v, Q v (M v)) → ∃ x, L x = M) :
    ∃ (κ : V → Type) (_ : ∀ v, Fintype (κ v)) (Lv : ∀ v, EuclideanSpace ℝ (κ v) →ₗ[ℝ] Matrix (Fin a) (Fin b) ℂ)
      (T : EuclideanSpace ℝ ι →ₗ[ℝ] ∀ v, EuclideanSpace ℝ (κ v)),
      (∀ v y, Q v (Lv v y)) ∧ (∀ v y, ∑ i, ∑ j, ‖Lv v y i j‖ ^ 2 = ‖y‖ ^ 2) ∧
      (∀ v M, Q v M → ∃ y, Lv v y = M) ∧ (∀ x v, Lv v (T x v) = L x v) ∧ Function.Bijective T ∧
      (∀ x, ∑ v, ‖T x v‖ ^ 2 = ‖x‖ ^ 2) := by
  classical
  let R : Matrix (Fin a) (Fin b) ℂ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin a × Fin b × Bool) := reimE (r := a) (m := b)
  have hRn : ∀ M : Matrix (Fin a) (Fin b) ℂ, ‖R M‖ ^ 2 = ∑ i, ∑ j, ‖M i j‖ ^ 2 := fun M => norm_reimE_sq M
  let S : V → Submodule ℝ (EuclideanSpace ℝ (Fin a × Fin b × Bool)) := fun v =>
    LinearMap.range (R.toLinearMap ∘ₗ (LinearMap.proj v ∘ₗ L))
  have hmem : ∀ v (M : Matrix (Fin a) (Fin b) ℂ), R M ∈ S v ↔ Q v M := by
    intro v M
    constructor
    · intro hM
      obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hM
      have hx' : R (L x v) = R M := by simpa using hx
      rw [← R.injective hx']
      exact hQ x v
    · intro hq
      obtain ⟨x, hx⟩ := hs (Pi.single v M) (fun w => by
        by_cases hw : w = v
        · subst hw
          rw [Pi.single_eq_same]
          exact hq
        · rw [Pi.single_eq_of_ne hw]
          exact hQ0 w)
      refine LinearMap.mem_range.mpr ⟨x, ?_⟩
      simp [hx]
  let n : V → ℕ := fun v => Module.finrank ℝ (S v)
  let B : ∀ v, OrthonormalBasis (Fin (n v)) ℝ (S v) := fun v => stdOrthonormalBasis ℝ (S v)
  let Lv : ∀ v, EuclideanSpace ℝ (Fin (n v)) →ₗ[ℝ] Matrix (Fin a) (Fin b) ℂ := fun v =>
    R.symm.toLinearMap ∘ₗ (S v).subtype ∘ₗ (B v).repr.symm.toLinearEquiv.toLinearMap
  have hLv_apply : ∀ v y, R (Lv v y) = ((B v).repr.symm y : EuclideanSpace ℝ (Fin a × Fin b × Bool)) := by
    intro v y
    simp [Lv]
  have hLv_norm : ∀ v y, ∑ i, ∑ j, ‖Lv v y i j‖ ^ 2 = ‖y‖ ^ 2 := by
    intro v y
    rw [← hRn, hLv_apply]
    exact congrArg (fun t => t ^ 2) ((B v).repr.symm.norm_map y)
  have hLvQ : ∀ v y, Q v (Lv v y) := by
    intro v y
    refine (hmem v _).mp ?_
    rw [hLv_apply]
    exact ((B v).repr.symm y).2
  have hLvSurj : ∀ v M, Q v M → ∃ y, Lv v y = M := by
    intro v M hq
    refine ⟨(B v).repr ⟨R M, (hmem v M).mpr hq⟩, ?_⟩
    apply R.injective
    rw [hLv_apply, LinearIsometryEquiv.symm_apply_apply]
  have hLvinj : ∀ v, Function.Injective (Lv v) := by
    intro v
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h1 := hLv_norm v y
    rw [hy] at h1
    have h2 : ‖y‖ ^ 2 = 0 := by
      rw [← h1]
      simp
    exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h2)
  have hLinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h1 := hn y
    rw [hy] at h1
    have h2 : ‖y‖ ^ 2 = 0 := by
      rw [← h1]
      simp
    exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h2)
  let Tv : ∀ v, EuclideanSpace ℝ ι →ₗ[ℝ] S v := fun v =>
    LinearMap.codRestrict (S v) (R.toLinearMap ∘ₗ (LinearMap.proj v ∘ₗ L))
      (fun x => LinearMap.mem_range_self _ x)
  let T : EuclideanSpace ℝ ι →ₗ[ℝ] ∀ v, EuclideanSpace ℝ (Fin (n v)) :=
    LinearMap.pi fun v => (B v).repr.toLinearEquiv.toLinearMap ∘ₗ Tv v
  have hTL : ∀ x v, Lv v (T x v) = L x v := by
    intro x v
    apply R.injective
    rw [hLv_apply]
    simp [T, Tv]
  have hTinj : Function.Injective T := by
    intro x x' hxx
    apply hLinj
    funext v
    rw [← hTL x v, ← hTL x' v, hxx]
  have hTsurj : Function.Surjective T := by
    intro y
    obtain ⟨x, hx⟩ := hs (fun v => Lv v (y v)) (fun v => hLvQ v (y v))
    refine ⟨x, ?_⟩
    funext v
    apply hLvinj v
    rw [hTL, hx]
  have hTnorm : ∀ x, ∑ v, ‖T x v‖ ^ 2 = ‖x‖ ^ 2 := by
    intro x
    rw [← hn x]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← hLv_norm v (T x v), hTL]
  exact ⟨fun v => Fin (n v), fun v => inferInstance, Lv, T, hLvQ, hLv_norm, hLvSurj, hTL, ⟨hTinj, hTsurj⟩, hTnorm⟩

end PI.AprimeInfW
