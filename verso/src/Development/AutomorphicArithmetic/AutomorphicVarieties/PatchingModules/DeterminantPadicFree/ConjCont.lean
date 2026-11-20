import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

/- English proof (translation)
Unfold `UpperTheory.V.Alg.AdicCont`. Simplify using `only [IsLocallyConstant.iff_eventually_eq, Ideal.Quotient.eq]`.
-/
private theorem adicCont_iff_eventually_sub_mem_pow {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R) (f : Γ → R) :
    UpperTheory.V.Alg.AdicCont I f ↔ ∀ (N : ℕ) (x : Γ), ∀ᶠ y in nhds x, f y - f x ∈ I ^ N := by
  unfold UpperTheory.V.Alg.AdicCont
  simp only [IsLocallyConstant.iff_eventually_eq, Ideal.Quotient.eq]

/- English proof (translation)
Introduce `N x`. Use `filter_upwards [hf N x, hg N x] with y h1 h2`. Establish `e : f y * g y - f x * g x = f y * (g y - g x) + (f y - f x) * g x` using `by ring`. Rewrite using `[e]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ h2) (Ideal.mul_mem_right _ _ h1)`.
-/
private theorem eventually_mul_sub_mem_pow_of_eventually_sub_mem {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R) (f g : Γ → R)
    (hf : ∀ (N : ℕ) (x : Γ), ∀ᶠ y in nhds x, f y - f x ∈ I ^ N)
    (hg : ∀ (N : ℕ) (x : Γ), ∀ᶠ y in nhds x, g y - g x ∈ I ^ N) :
    ∀ (N : ℕ) (x : Γ), ∀ᶠ y in nhds x, f y * g y - f x * g x ∈ I ^ N := by
  intro N x
  filter_upwards [hf N x, hg N x] with y h1 h2
  have e : f y * g y - f x * g x = f y * (g y - g x) + (f y - f x) * g x := by ring
  rw [e]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h2) (Ideal.mul_mem_right _ _ h1)

/- English proof (translation)
Introduce `N x`. Use `filter_upwards [Filter.eventually_all.2 (fun i => hf i N x)] with y hy`. Rewrite using `[← Finset.sum_sub_distrib]`. Conclude with `Ideal.sum_mem _ (fun i _ => hy i)`.
-/
private theorem eventually_sum_sub_mem_pow_of_eventually_sub_mem {Γ R ι : Type} [TopologicalSpace Γ] [CommRing R] [Fintype ι] (I : Ideal R)
    (f : ι → Γ → R) (hf : ∀ i (N : ℕ) (x : Γ), ∀ᶠ y in nhds x, f i y - f i x ∈ I ^ N) :
    ∀ (N : ℕ) (x : Γ), ∀ᶠ y in nhds x, (∑ i, f i y) - ∑ i, f i x ∈ I ^ N := by
  intro N x
  filter_upwards [Filter.eventually_all.2 (fun i => hf i N x)] with y hy
  rw [← Finset.sum_sub_distrib]
  exact Ideal.sum_mem _ (fun i _ => hy i)

/- English proof (translation)
Introduce `N x`. Take `⟨k, hk⟩` from `ENat.ne_top_iff_exists.1 (fun h0 => hc (PowerSeries.order_eq_top.1 h0))`. Use `filter_upwards [h (N + k) x] with y hy`. Rewrite `hy`, the goal using `[PowerSeries.maximalIdeal_eq_span_X, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Rewrite `hy` using `[← mul_sub, PowerSeries.X_pow_dvd_iff]`.

Rewrite using `[PowerSeries.X_pow_dvd_iff]`. Introduce `m hm`. Establish `h1 : ((N + k : ℕ) : ℕ∞) ≤ (c * (f y - f x)).order` using `PowerSeries.le_order _ _ (fun i hi => hy i (by exact_mod_cast hi))`. Rewrite `h1` using `[PowerSeries.order_mul, ← hk]`. Apply `PowerSeries.coeff_of_lt_order` to reduce the goal to its premises.

Distinguish the cases in `h3 : (f y - f x).order = ⊤`. Rewrite using `[h3]`. Conclude with `ENat.coe_lt_top m`. Take `⟨r, hr⟩` from `ENat.ne_top_iff_exists.1 h3`. Rewrite `h1`, the goal using `[← hr]`.

Establish `h4 : N + k ≤ k + r` using `by exact_mod_cast h1`. Conclude with `(by omega : m < r)` after adjusting the coercions.
-/
private theorem eventually_sub_mem_maxIdeal_pow_of_const_mul {Γ K' : Type} [TopologicalSpace Γ] [Field K'] (c : PowerSeries K') (hc : c ≠ 0)
    (f : Γ → PowerSeries K')
    (h : ∀ (N : ℕ) (x : Γ), ∀ᶠ y in nhds x, c * f y - c * f x ∈ maximalIdeal (PowerSeries K') ^ N) :
    ∀ (N : ℕ) (x : Γ), ∀ᶠ y in nhds x, f y - f x ∈ maximalIdeal (PowerSeries K') ^ N := by
  intro N x
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (fun h0 => hc (PowerSeries.order_eq_top.1 h0))
  filter_upwards [h (N + k) x] with y hy
  rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hy ⊢
  rw [← mul_sub, PowerSeries.X_pow_dvd_iff] at hy
  rw [PowerSeries.X_pow_dvd_iff]
  intro m hm
  have h1 : ((N + k : ℕ) : ℕ∞) ≤ (c * (f y - f x)).order :=
    PowerSeries.le_order _ _ (fun i hi => hy i (by exact_mod_cast hi))
  rw [PowerSeries.order_mul, ← hk] at h1
  apply PowerSeries.coeff_of_lt_order
  by_cases h3 : (f y - f x).order = ⊤
  · rw [h3]
    exact ENat.coe_lt_top m
  · obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.1 h3
    rw [← hr] at h1 ⊢
    have h4 : N + k ≤ k + r := by exact_mod_cast h1
    exact_mod_cast (by omega : m < r)

/- English proof (translation)
Introduce `K K' G _ _ _ n j ρ Q ρ' hj hρ hQ a b`. Establish `hX : PowerSeries.X ∈ maximalIdeal (PowerSeries K)`. Rewrite using `[PowerSeries.maximalIdeal_eq_span_X]`. Conclude with `Ideal.mem_span_singleton_self _`. Establish `hjX : j PowerSeries.X ∈ maximalIdeal (PowerSeries K')`.

Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu`. Conclude with `(IsLocalRing.mem_maximalIdeal _).1 hX (isUnit_of_map_unit j _ hu)`. Establish `hjr : ∀ k l (N : ℕ) (x : G), ∀ᶠ y in nhds x, j (ρ y k l) - j (ρ x k l) ∈ maximalIdeal (PowerSeries K') ^ N`. Introduce `k l N x`.

Use `filter_upwards [(adicCont_iff_eventually_sub_mem_pow _ _).1 (hρ k l) N x] with y hy`. Rewrite `hy` using `[PowerSeries.maximalIdeal_eq_span_X, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Take `⟨t, ht⟩` from `hy`. Rewrite using `[← map_sub, ht, map_mul, map_pow]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hjX N)`.

Take `⟨b1, hb1⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (PowerSeries K')) (fun p : Fin n × Fin n => (↑(Q⁻¹) : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K'))) p.1 p.2)`. Take `⟨b2, hb2⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (PowerSeries K')) (fun p : Fin n × Fin n => (↑Q : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K'))) p.1 p.2)`. Use `choose P hP using fun p => RingHom.mem_rangeS.1 (hb1 p)`. Use `choose R hR using fun p => RingHom.mem_rangeS.1 (hb2 p)`. Establish `hconj : ∀ g, (ρ' g).map (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) = (↑(Q⁻¹) : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K'))) * (ρ g).map ((algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))).comp j) * (↑Q : Matrix (Fin n) (Fin n) (FractionRin …`.

Introduce `g`. Rewrite using `[Matrix.mul_assoc, hQ g, ← Matrix.mul_assoc, Q.inv_mul, Matrix.one_mul]`. Establish `key : ∀ g, ((b1 : PowerSeries K') * (b2 : PowerSeries K')) * ρ' g a b = ∑ l, ∑ k, P (a, k) * j (ρ g k l) * R (l, b)`. Introduce `g`. Apply `IsFractionRing.injective (PowerSeries K') (FractionRing (PowerSeries K'))` to reduce the goal to its premises.

Establish `e` using `congrFun (congrFun (hconj g) a) b`. Simplify using `only [Matrix.map_apply, Matrix.mul_apply, RingHom.comp_apply] at e`. Rewrite using `[map_mul, e]`. Simplify using `only [map_sum, map_mul, hP, hR, Algebra.smul_def, Finset.mul_sum, Finset.sum_mul]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `l _`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `k _`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[adicCont_iff_eventually_sub_mem_pow]`.

Use `eventually_sub_mem_maxIdeal_pow_of_const_mul ((b1 : PowerSeries K') * (b2 : PowerSeries K')) (mul_ne_zero (nonZeroDivisors.coe_ne_zero b1) (nonZeroDivisors.coe_ne_zero b2)) _ ?_` and prove the remaining obligations. Simplify using `only [key]`. Use `eventually_sum_sub_mem_pow_of_eventually_sub_mem _ (fun l y => ∑ k, P (a, k) * j (ρ y k l) * R (l, b)) ?_` and prove the remaining obligations. Introduce `l`. Use `eventually_sum_sub_mem_pow_of_eventually_sub_mem _ (fun k y => P (a, k) * j (ρ y k l) * R (l, b)) ?_` and prove the remaining obligations.

Introduce `k`. Use `eventually_mul_sub_mem_pow_of_eventually_sub_mem _ (fun y => P (a, k) * j (ρ y k l)) (fun _ => R (l, b)) ?_ (fun N x => by simp)` and prove the remaining obligations. Conclude with `eventually_mul_sub_mem_pow_of_eventually_sub_mem _ (fun _ => P (a, k)) (fun y => j (ρ y k l)) (fun N x => by simp) (hjr k l)`.
-/
theorem UpperTheory.V.Pa.Det.conjCont :
    ∀ {K K' G : Type} [Field K] [Field K'] [TopologicalSpace G] {n : ℕ} (j : PowerSeries K →+* PowerSeries K') (ρ : G → Matrix (Fin n) (Fin n) (PowerSeries K)) (Q : GL (Fin n) (FractionRing (PowerSeries K'))) (ρ' : G → Matrix (Fin n) (Fin n) (PowerSeries K')), IsLocalHom j → (∀ a b, AdicCont (maximalIdeal (PowerSeries K)) fun g => ρ g a b) → (∀ g, (ρ g).map ((algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))).comp j) * (Q : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K'))) = (Q : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K'))) * (ρ' g).map (algebraMap (PowerSeries K') (FractionRing (PowerSeries K')))) → ∀ a b, AdicCont (maximalIdeal (PowerSeries K')) fun g => ρ' g a b := by
  intro K K' G _ _ _ n j ρ Q ρ' hj hρ hQ a b
  have hX : PowerSeries.X ∈ maximalIdeal (PowerSeries K) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    exact Ideal.mem_span_singleton_self _
  have hjX : j PowerSeries.X ∈ maximalIdeal (PowerSeries K') := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (IsLocalRing.mem_maximalIdeal _).1 hX (isUnit_of_map_unit j _ hu)
  have hjr : ∀ k l (N : ℕ) (x : G), ∀ᶠ y in nhds x,
      j (ρ y k l) - j (ρ x k l) ∈ maximalIdeal (PowerSeries K') ^ N := by
    intro k l N x
    filter_upwards [(adicCont_iff_eventually_sub_mem_pow _ _).1 (hρ k l) N x] with y hy
    rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hy
    obtain ⟨t, ht⟩ := hy
    rw [← map_sub, ht, map_mul, map_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hjX N)
  obtain ⟨b1, hb1⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (PowerSeries K'))
    (fun p : Fin n × Fin n => (↑(Q⁻¹) : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K'))) p.1 p.2)
  obtain ⟨b2, hb2⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (PowerSeries K'))
    (fun p : Fin n × Fin n => (↑Q : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K'))) p.1 p.2)
  choose P hP using fun p => RingHom.mem_rangeS.1 (hb1 p)
  choose R hR using fun p => RingHom.mem_rangeS.1 (hb2 p)
  have hconj : ∀ g, (ρ' g).map (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) =
      (↑(Q⁻¹) : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K'))) *
        (ρ g).map ((algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))).comp j) *
        (↑Q : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K'))) := by
    intro g
    rw [Matrix.mul_assoc, hQ g, ← Matrix.mul_assoc, Q.inv_mul, Matrix.one_mul]
  have key : ∀ g, ((b1 : PowerSeries K') * (b2 : PowerSeries K')) * ρ' g a b =
      ∑ l, ∑ k, P (a, k) * j (ρ g k l) * R (l, b) := by
    intro g
    apply IsFractionRing.injective (PowerSeries K') (FractionRing (PowerSeries K'))
    have e := congrFun (congrFun (hconj g) a) b
    simp only [Matrix.map_apply, Matrix.mul_apply, RingHom.comp_apply] at e
    rw [map_mul, e]
    simp only [map_sum, map_mul, hP, hR, Algebra.smul_def, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [adicCont_iff_eventually_sub_mem_pow]
  refine eventually_sub_mem_maxIdeal_pow_of_const_mul ((b1 : PowerSeries K') * (b2 : PowerSeries K'))
    (mul_ne_zero (nonZeroDivisors.coe_ne_zero b1) (nonZeroDivisors.coe_ne_zero b2)) _ ?_
  simp only [key]
  refine eventually_sum_sub_mem_pow_of_eventually_sub_mem _ (fun l y => ∑ k, P (a, k) * j (ρ y k l) * R (l, b)) ?_
  intro l
  refine eventually_sum_sub_mem_pow_of_eventually_sub_mem _ (fun k y => P (a, k) * j (ρ y k l) * R (l, b)) ?_
  intro k
  refine eventually_mul_sub_mem_pow_of_eventually_sub_mem _ (fun y => P (a, k) * j (ρ y k l)) (fun _ => R (l, b)) ?_ (fun N x => by simp)
  exact eventually_mul_sub_mem_pow_of_eventually_sub_mem _ (fun _ => P (a, k)) (fun y => j (ρ y k l)) (fun N x => by simp) (hjr k l)
