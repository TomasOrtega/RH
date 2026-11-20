import Formalism.HermitianCurvature.StatementH

namespace Formalism.FourierDecayAlt.P.Herglotz

open Real Filter Topology Finset

variable {d : ℕ}

noncomputable def ee (x : Fin d → ℝ) (σ : Fin d → ℤ) : ℂ :=
  Complex.exp (2 * π * Complex.I * ∑ j, ((σ j : ℝ) : ℂ) * (x j : ℂ))

/- English proof (translation)
Unfold `ee`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma ee_eq (x : Fin d → ℝ) (σ : Fin d → ℤ) :
    ee x σ = Complex.exp (((2 * π * ∑ j, (σ j : ℝ) * x j : ℝ) : ℂ) * Complex.I) := by
  unfold ee
  congr 1
  push_cast
  ring

/- English proof (translation)
Rewrite using `[ee_eq]`. Conclude with `Complex.norm_exp_ofReal_mul_I _`.
-/
lemma norm_ee (x : Fin d → ℝ) (σ : Fin d → ℤ) : ‖ee x σ‖ = 1 := by
  rw [ee_eq]
  exact Complex.norm_exp_ofReal_mul_I _

/- English proof (translation)
Rewrite using `[ee_eq, ee_eq, ee_eq, ← Complex.exp_conj, ← Complex.exp_add]`. Use `congr 1`. Simplify using `only [map_mul, Complex.conj_ofReal, Complex.conj_I, Pi.sub_apply, Int.cast_sub, sub_mul, Finset.sum_sub_distrib]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma ee_mul_conj (x : Fin d → ℝ) (σ σ' : Fin d → ℤ) :
    ee x σ * starRingEnd ℂ (ee x σ') = ee x (σ - σ') := by
  rw [ee_eq, ee_eq, ee_eq, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Pi.sub_apply, Int.cast_sub, sub_mul,
    Finset.sum_sub_distrib]
  push_cast
  ring

noncomputable def box (d N : ℕ) : Finset (Fin d → ℤ) := Fintype.piFinset (fun _ : Fin d => Finset.Ico (0 : ℤ) N)

/- English proof (translation)
Rewrite using `[tsum_eq_sum (s := (S ×ˢ S).image (fun p => p.1 - p.2))]`. Rewrite using `[← Finset.sum_product' (f := fun σ σ' => F (σ - σ')), ← Finset.sum_fiberwise_of_maps_to (g := fun p : (Fin d → ℤ) × (Fin d → ℤ) => p.1 - p.2) (t := (S ×ˢ S).image (fun p => p.1 - p.2)) (fun p hp => Finset.mem_image_of_mem _ hp)]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_congr rfl (fun p hp => by rw [(Finset.mem_filter.1 hp).2]), Finset.sum_const, nsmul_eq_mul]`. Introduce `τ hτ`.

Establish `: (S ×ˢ S).filter (fun p => p.1 - p.2 = τ) = ∅` using `Finset.filter_eq_empty_iff.2 fun p hp h => hτ (Finset.mem_image.2 ⟨p, hp, h⟩)`. Simplify using `[this]`.
-/
lemma dsum (F : (Fin d → ℤ) → ℂ) (S : Finset (Fin d → ℤ)) :
    ∑ σ ∈ S, ∑ σ' ∈ S, F (σ - σ') =
      ∑' τ, (((S ×ˢ S).filter (fun p => p.1 - p.2 = τ)).card : ℂ) * F τ := by
  rw [tsum_eq_sum (s := (S ×ˢ S).image (fun p => p.1 - p.2))]
  · rw [← Finset.sum_product' (f := fun σ σ' => F (σ - σ')),
      ← Finset.sum_fiberwise_of_maps_to (g := fun p : (Fin d → ℤ) × (Fin d → ℤ) => p.1 - p.2)
        (t := (S ×ˢ S).image (fun p => p.1 - p.2)) (fun p hp => Finset.mem_image_of_mem _ hp)]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_congr rfl (fun p hp => by rw [(Finset.mem_filter.1 hp).2]), Finset.sum_const,
      nsmul_eq_mul]
  · intro τ hτ
    have : (S ×ˢ S).filter (fun p => p.1 - p.2 = τ) = ∅ :=
      Finset.filter_eq_empty_iff.2 fun p hp h => hτ (Finset.mem_image.2 ⟨p, hp, h⟩)
    simp [this]

/- English proof (translation)
Establish `e1 : ((box d N ×ˢ box d N).filter (fun p => p.1 - p.2 = τ)).card = ((box d N).filter (fun s => s + τ ∈ box d N)).card`. Apply `Finset.card_nbij' (fun p => p.2) (fun s => (s + τ, s))` to reduce the goal to its premises. Introduce `p hp`. Simplify using `only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product] at hp ⊢`. Take `⟨⟨h1, h2⟩, h3⟩` from `hp`.

Use `⟨h2, ?_⟩` and prove the remaining obligations. Use `h1 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[← h3]`. Normalize the expressions using the abelian group laws. Introduce `s hs`.

Simplify using `only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product] at hs ⊢`. Conclude with `⟨⟨hs.2, hs.1⟩, by abel⟩`. Introduce `p hp`. Simplify using `only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product] at hp`. Use `Prod.ext ?_ rfl` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[← hp.2]`. Normalize the expressions using the abelian group laws. Introduce `s _`. Both sides reduce to the same expression.

Establish `e2 : (box d N).filter (fun s => s + τ ∈ box d N) = Fintype.piFinset (fun j => (Finset.Ico (0 : ℤ) N).filter (fun u => u + τ j ∈ Finset.Ico (0 : ℤ) N))`. Use extensionality with `s`. Simplify using `[box, Fintype.mem_piFinset, Finset.mem_filter, forall_and]`. Rewrite using `[e1, e2, Fintype.card_piFinset]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations.

Break down `le_total 0 (τ j) with ht | ht` into its components or cases. Rewrite using `[abs_of_nonneg ht]`. Establish `: (Finset.Ico (0 : ℤ) N).filter (fun u => u + τ j ∈ Finset.Ico (0 : ℤ) N) = Finset.Ico 0 ((N : ℤ) - τ j)`. Use extensionality with `u`. Simplify using `only [Finset.mem_filter, Finset.mem_Ico]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[this, Int.card_Ico, sub_zero]`. Rewrite using `[abs_of_nonpos ht]`. Establish `: (Finset.Ico (0 : ℤ) N).filter (fun u => u + τ j ∈ Finset.Ico (0 : ℤ) N) = Finset.Ico (-τ j) N`. Use extensionality with `u`.

Simplify using `only [Finset.mem_filter, Finset.mem_Ico]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[this, Int.card_Ico]`.
-/
lemma count_box (N : ℕ) (τ : Fin d → ℤ) :
    (((box d N ×ˢ box d N).filter (fun p => p.1 - p.2 = τ)).card) =
      ∏ j, ((N : ℤ) - |τ j|).toNat := by
  have e1 : ((box d N ×ˢ box d N).filter (fun p => p.1 - p.2 = τ)).card
      = ((box d N).filter (fun s => s + τ ∈ box d N)).card := by
    apply Finset.card_nbij' (fun p => p.2) (fun s => (s + τ, s))
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product] at hp ⊢
      obtain ⟨⟨h1, h2⟩, h3⟩ := hp
      refine ⟨h2, ?_⟩
      convert h1 using 1
      rw [← h3]
      abel
    · intro s hs
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product] at hs ⊢
      exact ⟨⟨hs.2, hs.1⟩, by abel⟩
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product] at hp
      refine Prod.ext ?_ rfl
      simp only
      rw [← hp.2]
      abel
    · intro s _
      rfl
  have e2 : (box d N).filter (fun s => s + τ ∈ box d N)
      = Fintype.piFinset (fun j => (Finset.Ico (0 : ℤ) N).filter (fun u => u + τ j ∈ Finset.Ico (0 : ℤ) N)) := by
    ext s
    simp [box, Fintype.mem_piFinset, Finset.mem_filter, forall_and]
  rw [e1, e2, Fintype.card_piFinset]
  refine Finset.prod_congr rfl fun j _ => ?_
  rcases le_total 0 (τ j) with ht | ht
  · rw [abs_of_nonneg ht]
    have : (Finset.Ico (0 : ℤ) N).filter (fun u => u + τ j ∈ Finset.Ico (0 : ℤ) N)
        = Finset.Ico 0 ((N : ℤ) - τ j) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_Ico]
      omega
    rw [this, Int.card_Ico, sub_zero]
  · rw [abs_of_nonpos ht]
    have : (Finset.Ico (0 : ℤ) N).filter (fun u => u + τ j ∈ Finset.Ico (0 : ℤ) N)
        = Finset.Ico (-τ j) N := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_Ico]
      omega
    rw [this, Int.card_Ico]

noncomputable def fac (N : ℕ) (t : ℤ) : ℝ := (((N : ℤ) - |t|).toNat : ℝ) / N

noncomputable def wt (N : ℕ) (τ : Fin d → ℤ) : ℝ := ∏ j, fac N (τ j)

/- English proof (translation)
Unfold `fac`. Check the signs of the components of the expression.
-/
lemma fac_nonneg (N : ℕ) (t : ℤ) : 0 ≤ fac N t := by
  unfold fac
  positivity

/- English proof (translation)
Unfold `fac`. Break down `Nat.eq_zero_or_pos N with rfl | hN` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[div_le_one (by exact_mod_cast hN)]`. Establish `: ((N : ℤ) - |t|).toNat ≤ N`.

Use `abs_nonneg t` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `this` after adjusting the coercions.
-/
lemma fac_le_one (N : ℕ) (t : ℤ) : fac N t ≤ 1 := by
  unfold fac
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · rw [div_le_one (by exact_mod_cast hN)]
    have : ((N : ℤ) - |t|).toNat ≤ N := by
      have := abs_nonneg t
      omega
    exact_mod_cast this

/- English proof (translation)
The claim follows from `Finset.prod_nonneg fun j _ => fac_nonneg N (τ j)`.
-/
lemma wt_nonneg (N : ℕ) (τ : Fin d → ℤ) : 0 ≤ wt N τ :=
  Finset.prod_nonneg fun j _ => fac_nonneg N (τ j)

/- English proof (translation)
The claim follows from `Finset.prod_le_one (fun j _ => fac_nonneg N (τ j)) (fun j _ => fac_le_one N (τ j))`.
-/
lemma wt_le_one (N : ℕ) (τ : Fin d → ℤ) : wt N τ ≤ 1 :=
  Finset.prod_le_one (fun j _ => fac_nonneg N (τ j)) (fun j _ => fac_le_one N (τ j))

/- English proof (translation)
Establish `h : ∀ᶠ N : ℕ in atTop, 1 - (|(t : ℝ)|) / N = fac N t` using `by filter_upwards [eventually_ge_atTop (t.natAbs + 1)] with N hN`. Unfold `fac`. Establish `hN0 : (N : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 (by omega)`. Establish `h2 : ((((N : ℤ) - |t|).toNat : ℕ) : ℤ) = (N : ℤ) - |t|`. Apply `Int.toNat_of_nonneg` to reduce the goal to its premises.

Rewrite using `[Int.abs_eq_natAbs]`. Use linear arithmetic over natural numbers and integers. Establish `h3 : ((((N : ℤ) - |t|).toNat : ℕ) : ℝ) = (N : ℝ) - |(t : ℝ)|`. Rewrite using `[← Int.cast_natCast, h2]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h3]`. Clear the denominators using the available nonvanishing facts. Use `Tendsto.congr' h ?_` and prove the remaining obligations. Simplify using `using (tendsto_const_div_atTop_nhds_zero_nat (|(t : ℝ)|)).const_sub 1`.
-/
lemma fac_tendsto (t : ℤ) : Tendsto (fun N : ℕ => fac N t) atTop (𝓝 1) := by
  have h : ∀ᶠ N : ℕ in atTop, 1 - (|(t : ℝ)|) / N = fac N t := by
    filter_upwards [eventually_ge_atTop (t.natAbs + 1)] with N hN
    unfold fac
    have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have h2 : ((((N : ℤ) - |t|).toNat : ℕ) : ℤ) = (N : ℤ) - |t| := by
      apply Int.toNat_of_nonneg
      rw [Int.abs_eq_natAbs]
      omega
    have h3 : ((((N : ℤ) - |t|).toNat : ℕ) : ℝ) = (N : ℝ) - |(t : ℝ)| := by
      rw [← Int.cast_natCast, h2]
      push_cast
      ring
    rw [h3]
    field_simp
  refine Tendsto.congr' h ?_
  simpa using (tendsto_const_div_atTop_nhds_zero_nat (|(t : ℝ)|)).const_sub 1

/- English proof (translation)
Unfold `wt`. Simplify using `using tendsto_finset_prod Finset.univ (fun j _ => fac_tendsto (τ j))`.
-/
lemma wt_tendsto (τ : Fin d → ℤ) : Tendsto (fun N : ℕ => wt N τ) atTop (𝓝 1) := by
  unfold wt
  simpa using tendsto_finset_prod Finset.univ (fun j _ => fac_tendsto (τ j))

/- English proof (translation)
Rewrite using `[count_box]`. Unfold `wt fac`. Rewrite using `[Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Use `push_cast`. Rewrite using `[inv_mul_eq_div]`.
-/
lemma wt_eq (N : ℕ) (hN : N ≠ 0) (τ : Fin d → ℤ) :
    (((N : ℝ) ^ d)⁻¹ * (((box d N ×ˢ box d N).filter (fun p => p.1 - p.2 = τ)).card : ℝ))
      = wt N τ := by
  rw [count_box]
  unfold wt fac
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  push_cast
  rw [inv_mul_eq_div]

end Formalism.FourierDecayAlt.P.Herglotz

namespace Formalism.FourierDecayAlt.P

open Real Filter Topology Finset Formalism.FourierDecayAlt.P.Herglotz

/- English proof (translation)
Introduce `d A hA hpos x`. Express the relevant statement in the definitionally equal form `0 ≤ (∑' σ, A σ * ee x σ).re`. Establish `hN : ∀ N : ℕ, N ≠ 0 → 0 ≤ (∑' τ, ((wt N τ : ℝ) : ℂ) * (A τ * ee x τ)).re`. Introduce `N hN`. Establish `h` using `hpos (box d N) (fun σ => ee x σ)`.

Establish `h2 : ∑ σ ∈ box d N, ∑ σ' ∈ box d N, A (σ - σ') * ee x σ * starRingEnd ℂ (ee x σ') = ∑ σ ∈ box d N, ∑ σ' ∈ box d N, (fun τ => A τ * ee x τ) (σ - σ')`. Use `Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun σ' _ => ?_` and prove the remaining obligations. Simplify using `only`. Rewrite using `[mul_assoc, ee_mul_conj]`. Rewrite `h` using `[h2, dsum (fun τ => A τ * ee x τ) (box d N)]`.

Establish `h3 : ∑' τ, ((wt N τ : ℝ) : ℂ) * (A τ * ee x τ) = ((((N : ℝ) ^ d)⁻¹ : ℝ) : ℂ) * ∑' τ, ((((box d N ×ˢ box d N).filter (fun p => p.1 - p.2 = τ)).card : ℂ) * (A τ * ee x τ))`. Rewrite using `[← tsum_mul_left]`. Use `congr 1`. Use function extensionality and compare the values at `τ`. Rewrite using `[← wt_eq N hN τ]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h3, Complex.re_ofReal_mul]`. Conclude with `mul_nonneg (by positivity) h`. Establish `hlim : Tendsto (fun N : ℕ => ∑' τ, ((wt N τ : ℝ) : ℂ) * (A τ * ee x τ)) atTop (𝓝 (∑' τ, A τ * ee x τ))`.

Use `tendsto_tsum_of_dominated_convergence (bound := fun τ => ‖A τ‖) hA ?_ ?_` and prove the remaining obligations. Introduce `τ`. Use `((Complex.continuous_ofReal.tendsto 1).comp (wt_tendsto τ)).mul_const (A τ * ee x τ)` as an intermediate fact. Simplify using `using this`. Use `Eventually.of_forall fun N τ => ?_` and prove the remaining obligations.

Rewrite using `[norm_mul, norm_mul, norm_ee, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (wt_nonneg N τ)]`. Use polynomial arithmetic with `[wt_le_one N τ, norm_nonneg (A τ)]`. Conclude with `ge_of_tendsto ((Complex.continuous_re.tendsto _).comp hlim) (by filter_upwards [eventually_ne_atTop 0] with N hN' using hN N hN')`.
-/
theorem herglotz_Zd : Formalism.FourierDecayAlt.H.HerglotzZd := by
  intro d A hA hpos x
  change 0 ≤ (∑' σ, A σ * ee x σ).re
  have hN : ∀ N : ℕ, N ≠ 0 → 0 ≤ (∑' τ, ((wt N τ : ℝ) : ℂ) * (A τ * ee x τ)).re := by
    intro N hN
    have h := hpos (box d N) (fun σ => ee x σ)
    have h2 : ∑ σ ∈ box d N, ∑ σ' ∈ box d N, A (σ - σ') * ee x σ * starRingEnd ℂ (ee x σ')
        = ∑ σ ∈ box d N, ∑ σ' ∈ box d N, (fun τ => A τ * ee x τ) (σ - σ') := by
      refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun σ' _ => ?_
      simp only
      rw [mul_assoc, ee_mul_conj]
    rw [h2, dsum (fun τ => A τ * ee x τ) (box d N)] at h
    have h3 : ∑' τ, ((wt N τ : ℝ) : ℂ) * (A τ * ee x τ)
        = ((((N : ℝ) ^ d)⁻¹ : ℝ) : ℂ) * ∑' τ,
            ((((box d N ×ˢ box d N).filter (fun p => p.1 - p.2 = τ)).card : ℂ) * (A τ * ee x τ)) := by
      rw [← tsum_mul_left]
      congr 1
      funext τ
      rw [← wt_eq N hN τ]
      push_cast
      ring
    rw [h3, Complex.re_ofReal_mul]
    exact mul_nonneg (by positivity) h
  have hlim : Tendsto (fun N : ℕ => ∑' τ, ((wt N τ : ℝ) : ℂ) * (A τ * ee x τ)) atTop
      (𝓝 (∑' τ, A τ * ee x τ)) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun τ => ‖A τ‖) hA ?_ ?_
    · intro τ
      have := ((Complex.continuous_ofReal.tendsto 1).comp (wt_tendsto τ)).mul_const (A τ * ee x τ)
      simpa using this
    · refine Eventually.of_forall fun N τ => ?_
      rw [norm_mul, norm_mul, norm_ee, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (wt_nonneg N τ)]
      nlinarith [wt_le_one N τ, norm_nonneg (A τ)]
  exact ge_of_tendsto ((Complex.continuous_re.tendsto _).comp hlim)
    (by filter_upwards [eventually_ne_atTop 0] with N hN' using hN N hN')

end Formalism.FourierDecayAlt.P
