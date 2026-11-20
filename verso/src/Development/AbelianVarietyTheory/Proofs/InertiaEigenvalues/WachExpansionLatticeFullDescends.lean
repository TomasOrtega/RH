import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot

noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.NL.FullDown

section Series

variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]

def Bd (u : ℤ → M) : Prop := ∃ m : ℤ, ∀ k < m, u k = 0

/- English proof (translation)
Take `⟨m, hm⟩` from `hu`. Use `(Set.finite_le_nat (k - m).toNat).subset fun j hj => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Simplify using `only [Set.mem_setOf_eq, not_le] at h`. Apply `hj` to reduce the goal to its premises.

Establish `: k - (j : ℤ) < m` using `by omega`. Simplify using `[hm _ this]`.
-/
theorem conv_finite (e : PowerSeries L) {u : ℤ → M} (hu : Bd u) (k : ℤ) :
    (Function.support fun j : ℕ => PowerSeries.coeff j e • u (k - (j : ℤ))).Finite := by
  obtain ⟨m, hm⟩ := hu
  refine (Set.finite_le_nat (k - m).toNat).subset fun j hj => ?_
  by_contra h
  simp only [Set.mem_setOf_eq, not_le] at h
  apply hj
  have : k - (j : ℤ) < m := by omega
  simp [hm _ this]

/- English proof (translation)
Unfold `conv`. Apply `finsum_eq_sum_of_support_subset` to reduce the goal to its premises. Introduce `j hj`. Assume the negation of the conclusion as `h`. Simplify using `only [Finset.coe_range, Set.mem_Iio, not_lt] at h`.

Apply `hj` to reduce the goal to its premises. Establish `: k - (j : ℤ) < m` using `by omega`. Simplify using `[hm _ this]`.
-/
theorem conv_eq_sum (e : PowerSeries L) {u : ℤ → M} {m : ℤ} (hm : ∀ k < m, u k = 0) (k : ℤ) (N : ℕ)
    (hN : k - m < N) :
    conv e u k = ∑ j ∈ Finset.range N, PowerSeries.coeff j e • u (k - (j : ℤ)) := by
  unfold conv
  apply finsum_eq_sum_of_support_subset
  intro j hj
  by_contra h
  simp only [Finset.coe_range, Set.mem_Iio, not_lt] at h
  apply hj
  have : k - (j : ℤ) < m := by omega
  simp [hm _ this]

/- English proof (translation)
Introduce `k hk`. Apply `finsum_eq_zero_of_forall_eq_zero` to reduce the goal to its premises. Introduce `j`. Rewrite using `[hm _ (by omega), smul_zero]`.
-/
theorem conv_low (e : PowerSeries L) {u : ℤ → M} {m : ℤ} (hm : ∀ k < m, u k = 0) :
    ∀ k < m, conv e u k = 0 := by
  intro k hk
  apply finsum_eq_zero_of_forall_eq_zero
  intro j
  rw [hm _ (by omega), smul_zero]

/- English proof (translation)
Unfold `conv`. Rewrite using `[finsum_eq_sum _ (conv_finite e hu k)]`. Conclude with `D.sum_mem fun j _ => D.smul_mem _ (hD _)`.
-/
theorem conv_mem (e : PowerSeries L) {u : ℤ → M} (hu : Bd u) (D : Submodule L M) (hD : ∀ k, u k ∈ D)
    (k : ℤ) : conv e u k ∈ D := by
  unfold conv
  rw [finsum_eq_sum _ (conv_finite e hu k)]
  exact D.sum_mem fun j _ => D.smul_mem _ (hD _)

/- English proof (translation)
Unfold `conv`. Rewrite using `[finsum_eq_single _ a]`. Simplify using the standard rewrite rules. Introduce `j hj`. Simplify using `[PowerSeries.coeff_X_pow, hj]`.
-/
theorem conv_X_pow (a : ℕ) (u : ℤ → M) (k : ℤ) :
    conv ((PowerSeries.X : PowerSeries L) ^ a) u k = u (k - a) := by
  unfold conv
  rw [finsum_eq_single _ a]
  · simp
  · intro j hj
    simp [PowerSeries.coeff_X_pow, hj]

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `using conv_X_pow (L := L) 0 u k`.
-/
theorem conv_one (u : ℤ → M) : conv (1 : PowerSeries L) u = u := by
  funext k
  simpa using conv_X_pow (L := L) 0 u k

/- English proof (translation)
Take `⟨m, hm⟩` from `hu`. Use function extensionality and compare the values at `k`. Take `⟨N, hN⟩ : ∃ N : ℕ, k - m < N` from `⟨(k - m).toNat + 1, by omega⟩`. Rewrite using `[conv_eq_sum _ hm k N hN, conv_eq_sum _ (conv_low b hm) k N hN]`. Establish `h1 : ∀ x ∈ Finset.range N, PowerSeries.coeff x a • conv b u (k - (x : ℤ)) = ∑ y ∈ Finset.range N, (PowerSeries.coeff x a * PowerSeries.coeff y b) • u (k - ((x + y : ℕ) : ℤ))`.

Introduce `x _`. Rewrite using `[conv_eq_sum _ hm _ N (by omega), Finset.smul_sum]`. Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul]`. Use `congr 3`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_congr rfl h1, ← Finset.sum_product']`. Establish `h2 : ∀ j ∈ Finset.range N, PowerSeries.coeff j (a * b) • u (k - (j : ℤ)) = ∑ p ∈ (Finset.range N ×ˢ Finset.range N) with p.1 + p.2 = j, (PowerSeries.coeff p.1 a * PowerSeries.coeff p.2 b) • u (k - ((p.1 + p.2 : ℕ) : ℤ))`. Introduce `j hj`.

Rewrite using `[PowerSeries.coeff_mul, Finset.sum_smul]`. Use `Finset.sum_congr ?_ fun p hp => ?_` and prove the remaining obligations. Use extensionality with `p`. Simplify using `only [Finset.mem_range] at hj`. Simplify using `only [Finset.HasAntidiagonal.mem_antidiagonal, Finset.mem_filter, Finset.mem_product, Finset.mem_range]`.

Conclude with `⟨fun h => ⟨⟨by omega, by omega⟩, h⟩, fun h => h.2⟩`. Rewrite using `[(Finset.mem_filter.1 hp).2]`. Rewrite using `[Finset.sum_congr rfl h2, Finset.sum_fiberwise_eq_sum_filter]`. Apply `Finset.sum_filter_of_ne` to reduce the goal to its premises. Introduce `p _ hp`.

Assume the negation of the conclusion as `h`. Simplify using `only [Finset.mem_range, not_lt] at h`. Apply `hp` to reduce the goal to its premises. Rewrite using `[hm _ (by push_cast; omega), smul_zero]`.
-/
theorem conv_mul (a b : PowerSeries L) {u : ℤ → M} (hu : Bd u) :
    conv (a * b) u = conv a (conv b u) := by
  obtain ⟨m, hm⟩ := hu
  funext k
  obtain ⟨N, hN⟩ : ∃ N : ℕ, k - m < N := ⟨(k - m).toNat + 1, by omega⟩
  rw [conv_eq_sum _ hm k N hN, conv_eq_sum _ (conv_low b hm) k N hN]
  have h1 : ∀ x ∈ Finset.range N, PowerSeries.coeff x a • conv b u (k - (x : ℤ)) =
      ∑ y ∈ Finset.range N, (PowerSeries.coeff x a * PowerSeries.coeff y b) • u (k - ((x + y : ℕ) : ℤ)) := by
    intro x _
    rw [conv_eq_sum _ hm _ N (by omega), Finset.smul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [mul_smul]
    congr 3
    push_cast; ring
  rw [Finset.sum_congr rfl h1, ← Finset.sum_product']
  have h2 : ∀ j ∈ Finset.range N, PowerSeries.coeff j (a * b) • u (k - (j : ℤ)) =
      ∑ p ∈ (Finset.range N ×ˢ Finset.range N) with p.1 + p.2 = j,
        (PowerSeries.coeff p.1 a * PowerSeries.coeff p.2 b) • u (k - ((p.1 + p.2 : ℕ) : ℤ)) := by
    intro j hj
    rw [PowerSeries.coeff_mul, Finset.sum_smul]
    refine Finset.sum_congr ?_ fun p hp => ?_
    · ext p
      simp only [Finset.mem_range] at hj
      simp only [Finset.HasAntidiagonal.mem_antidiagonal, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨fun h => ⟨⟨by omega, by omega⟩, h⟩, fun h => h.2⟩
    · rw [(Finset.mem_filter.1 hp).2]
  rw [Finset.sum_congr rfl h2, Finset.sum_fiberwise_eq_sum_filter]
  apply Finset.sum_filter_of_ne
  intro p _ hp
  by_contra h
  simp only [Finset.mem_range, not_lt] at h
  apply hp
  rw [hm _ (by push_cast; omega), smul_zero]

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `only [conv, Pi.add_apply, smul_add]`. Conclude with `finsum_add_distrib (conv_finite e hu k) (conv_finite e hw k)`.
-/
theorem conv_add (e : PowerSeries L) {u w : ℤ → M} (hu : Bd u) (hw : Bd w) :
    conv e (u + w) = conv e u + conv e w := by
  funext k
  simp only [conv, Pi.add_apply, smul_add]
  exact finsum_add_distrib (conv_finite e hu k) (conv_finite e hw k)

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `only [conv, Pi.smul_apply]`. Rewrite using `[smul_finsum' c (conv_finite e hu k)]`. Conclude with `finsum_congr fun j => smul_comm _ _ _`.
-/
theorem conv_smul (e : PowerSeries L) (c : L) {u : ℤ → M} (hu : Bd u) :
    conv e (c • u) = c • conv e u := by
  funext k
  simp only [conv, Pi.smul_apply]
  rw [smul_finsum' c (conv_finite e hu k)]
  exact finsum_congr fun j => smul_comm _ _ _

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `[conv]`.
-/
theorem conv_zero (e : PowerSeries L) : conv e (0 : ℤ → M) = 0 := by
  funext k
  simp [conv]

/- English proof (translation)
The claim follows from `let ⟨m, hm⟩ := hu ⟨m, conv_low e hm⟩`.
-/
theorem Bd.conv {u : ℤ → M} (hu : Bd u) (e : PowerSeries L) : Bd (conv e u) :=
  let ⟨m, hm⟩ := hu
  ⟨m, conv_low e hm⟩

/- English proof (translation)
Take `⟨m, hm⟩` from `hu`. Take `⟨m', hm'⟩` from `hw`. Use `⟨min m m', fun k hk => ?_⟩` and prove the remaining obligations. Simplify using `[hm k (lt_of_lt_of_le hk (min_le_left _ _)), hm' k (lt_of_lt_of_le hk (min_le_right _ _))]`.
-/
theorem Bd.add {u w : ℤ → M} (hu : Bd u) (hw : Bd w) : Bd (u + w) := by
  obtain ⟨m, hm⟩ := hu
  obtain ⟨m', hm'⟩ := hw
  refine ⟨min m m', fun k hk => ?_⟩
  simp [hm k (lt_of_lt_of_le hk (min_le_left _ _)), hm' k (lt_of_lt_of_le hk (min_le_right _ _))]

/- English proof (translation)
The claim follows from `let ⟨m, hm⟩ := hu ⟨m, fun k hk => by simp [hm k hk]⟩`.
-/
theorem Bd.smul {u : ℤ → M} (hu : Bd u) (c : L) : Bd (c • u) :=
  let ⟨m, hm⟩ := hu
  ⟨m, fun k hk => by simp [hm k hk]⟩

/- English proof (translation)
Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem f hf`. Take `⟨e, x, rfl⟩` from `hf`. Use `⟨(hs x).conv e, ?_⟩` and prove the remaining obligations. Rewrite using `[← conv_mul _ _ (hs x), mul_comm, conv_mul _ _ (hs x)]`.

Conclude with `hx e x`. Consider the case `zero => exact ⟨⟨0, fun _ _ => rfl⟩, by rw [conv_zero]; exact Λ.zero_mem⟩`. Consider the case `add f g _ _ hf hg => exact ⟨hf.1.add hg.1, by rw [conv_add _ hf.1 hg.1]; exact Λ.add_mem hf.2 hg.2⟩`. Consider the case `smul c f _ hf => exact ⟨hf.1.smul c, by rw [conv_smul _ _ hf.1]; exact Λ.smul_mem c hf.2⟩`.
-/
theorem conv_latSpan {ι : Type} (ex : ι → ℤ → M) (hs : ∀ x, Bd (ex x)) (q : PowerSeries L)
    (Λ : Submodule L (ℤ → M)) (hx : ∀ (e : PowerSeries L) x, conv e (conv q (ex x)) ∈ Λ) (f : ℤ → M)
    (hf : f ∈ latSpan (LL := L) ex) : Bd f ∧ conv q f ∈ Λ := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨e, x, rfl⟩ := hf
    refine ⟨(hs x).conv e, ?_⟩
    rw [← conv_mul _ _ (hs x), mul_comm, conv_mul _ _ (hs x)]
    exact hx e x
  | zero => exact ⟨⟨0, fun _ _ => rfl⟩, by rw [conv_zero]; exact Λ.zero_mem⟩
  | add f g _ _ hf hg => exact ⟨hf.1.add hg.1, by rw [conv_add _ hf.1 hg.1]; exact Λ.add_mem hf.2 hg.2⟩
  | smul c f _ hf => exact ⟨hf.1.smul c, by rw [conv_smul _ _ hf.1]; exact Λ.smul_mem c hf.2⟩

/- English proof (translation)
The claim follows from `conv_latSpan ex hs q (latSpan (LL := L) ex) (fun e x => Submodule.subset_span ⟨e * q, x, (conv_mul _ _ (hs x)).symm⟩) f hf`.
-/
theorem latSpan_conv {ι : Type} (ex : ι → ℤ → M) (hs : ∀ x, Bd (ex x)) (q : PowerSeries L) (f : ℤ → M)
    (hf : f ∈ latSpan (LL := L) ex) : Bd f ∧ conv q f ∈ latSpan (LL := L) ex :=
  conv_latSpan ex hs q (latSpan (LL := L) ex)
    (fun e x => Submodule.subset_span ⟨e * q, x, (conv_mul _ _ (hs x)).symm⟩) f hf

def Tw (p : L) (φ : M →ₗ[L] M) : (ℤ → M) →ₗ[L] (ℤ → M) :=
  LinearMap.pi fun k => (p ^ k) • φ.comp (LinearMap.proj k)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Tw_apply (p : L) (φ : M →ₗ[L] M) (f : ℤ → M) (k : ℤ) : Tw p φ f k = p ^ k • φ (f k) := rfl

/- English proof (translation)
Use function extensionality and compare the values at `k`. Rewrite using `[Tw_apply]`. Unfold `conv`. Establish `h` using `map_finsum ((p ^ k) • φ) (conv_finite e hf k)`. Rewrite `h` using `[LinearMap.smul_apply]`.

Rewrite using `[h]`. Use `finsum_congr fun j => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, map_smul, Tw_apply, PowerSeries.coeff_rescale, smul_smul, smul_smul]`. Use `congr 1`. Rewrite using `[zpow_sub₀ hp, zpow_natCast]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem Tw_conv {p : L} (hp : p ≠ 0) (φ : M →ₗ[L] M) (e : PowerSeries L) {f : ℤ → M} (hf : Bd f) :
    Tw p φ (conv e f) = conv (PowerSeries.rescale p e) (Tw p φ f) := by
  funext k
  rw [Tw_apply]
  unfold conv
  have h := map_finsum ((p ^ k) • φ) (conv_finite e hf k)
  rw [LinearMap.smul_apply] at h
  rw [h]
  refine finsum_congr fun j => ?_
  rw [LinearMap.smul_apply, map_smul, Tw_apply, PowerSeries.coeff_rescale, smul_smul, smul_smul]
  congr 1
  rw [zpow_sub₀ hp, zpow_natCast]
  field_simp

/- English proof (translation)
Take `⟨g, hg, rfl⟩` from `hf`. Take `⟨h1, h2⟩` from `latSpan_conv ex hs (PowerSeries.rescale p⁻¹ e) g hg`. Use `⟨_, h2, ?_⟩` and prove the remaining obligations. Rewrite using `[Tw_conv hp φ _ h1, PowerSeries.rescale_rescale, inv_mul_cancel₀ hp, PowerSeries.rescale_one]`. Both sides reduce to the same expression.
-/
theorem map_conv {ι : Type} (ex : ι → ℤ → M) (hs : ∀ x, Bd (ex x)) {p : L} (hp : p ≠ 0)
    (φ : M →ₗ[L] M) (e : PowerSeries L) (f : ℤ → M)
    (hf : f ∈ (latSpan (LL := L) ex).map (Tw p φ)) : conv e f ∈ (latSpan (LL := L) ex).map (Tw p φ) := by
  obtain ⟨g, hg, rfl⟩ := hf
  obtain ⟨h1, h2⟩ := latSpan_conv ex hs (PowerSeries.rescale p⁻¹ e) g hg
  refine ⟨_, h2, ?_⟩
  rw [Tw_conv hp φ _ h1, PowerSeries.rescale_rescale, inv_mul_cancel₀ hp, PowerSeries.rescale_one]
  rfl

/- English proof (translation)
Take `⟨m, hm⟩` from `hF`. Take `⟨a, w, hw, hqw⟩ : ∃ (a : ℕ) (w : PowerSeries L), IsUnit w ∧ q = PowerSeries.X ^ a * w` from `⟨q.order.toNat, q.divXPowOrder, PowerSeries.isUnit_divided_by_X_pow_order hq, PowerSeries.X_pow_order_mul_divXPowOrder.symm⟩`. Take `⟨w', hw'⟩` from `hw.exists_right_inv`. Use `⟨m + a, fun g hg hg0 => ?_⟩` and prove the remaining obligations. Use `set u : ℤ → M := fun k => Tw p φ g (k + a) with hu`.

Establish `hu0 : ∀ k < (m : ℤ), u k = 0` using `fun k hk => by`. Simplify using `only [hu, Tw_apply]`. Rewrite using `[hg0 _ (by push_cast; omega), map_zero, smul_zero]`. Establish `hB : Bd u` using `⟨m, hu0⟩`. Establish `h1` using `h _ (hm (conv w' u) (conv_mem w' hB D fun k => D.smul_mem _ (hD _ (hg _))) (conv_low w' hu0))`.

Rewrite `h1` using `[← conv_mul _ _ hB, hqw, mul_assoc, hw', mul_one]`. Take `⟨g', hg', he⟩` from `h1`. Establish `: g' = g`. Use function extensionality and compare the values at `k`. Establish `h2` using `congrFun he k`.

Rewrite `h2` using `[conv_X_pow, hu]`. Simplify using `only [sub_add_cancel, Tw_apply] at h2`. Conclude with `hφ (smul_right_injective M (zpow_ne_zero k hp) h2)`. Conclude with `this ▸ hg'`.
-/
theorem full_of_conv {p : L} (hp : p ≠ 0) (φ : M →ₗ[L] M) (hφ : Function.Injective φ)
    (D D' : Submodule L M) (hD : ∀ x ∈ D', φ x ∈ D) (Λ Λ' : Submodule L (ℤ → M))
    (q : PowerSeries L) (hq : q ≠ 0) (h : ∀ f ∈ Λ, conv q f ∈ Λ'.map (Tw p φ)) (hF : Full D Λ) :
    Full D' Λ' := by
  obtain ⟨m, hm⟩ := hF
  obtain ⟨a, w, hw, hqw⟩ : ∃ (a : ℕ) (w : PowerSeries L), IsUnit w ∧ q = PowerSeries.X ^ a * w :=
    ⟨q.order.toNat, q.divXPowOrder, PowerSeries.isUnit_divided_by_X_pow_order hq,
      PowerSeries.X_pow_order_mul_divXPowOrder.symm⟩
  obtain ⟨w', hw'⟩ := hw.exists_right_inv
  refine ⟨m + a, fun g hg hg0 => ?_⟩
  set u : ℤ → M := fun k => Tw p φ g (k + a) with hu
  have hu0 : ∀ k < (m : ℤ), u k = 0 := fun k hk => by
    simp only [hu, Tw_apply]
    rw [hg0 _ (by push_cast; omega), map_zero, smul_zero]
  have hB : Bd u := ⟨m, hu0⟩
  have h1 := h _ (hm (conv w' u) (conv_mem w' hB D fun k => D.smul_mem _ (hD _ (hg _)))
    (conv_low w' hu0))
  rw [← conv_mul _ _ hB, hqw, mul_assoc, hw', mul_one] at h1
  obtain ⟨g', hg', he⟩ := h1
  have : g' = g := by
    funext k
    have h2 := congrFun he k
    rw [conv_X_pow, hu] at h2
    simp only [sub_add_cancel, Tw_apply] at h2
    exact hφ (smul_right_injective M (zpow_ne_zero k hp) h2)
  exact this ▸ hg'

end Series

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

/- English proof (translation)
Introduce `h`. Use `W.v_l` as an intermediate fact. Rewrite `this` using `[h, AddValuation.map_zero]`. Conclude with `WithTop.top_ne_coe this`.
-/
theorem p_ne (W : LocWach PD LL O v n) : (PD.p : LL) ≠ 0 := by
  intro h
  have := W.v_l
  rw [h, AddValuation.map_zero] at this
  exact WithTop.top_ne_coe this

/- English proof (translation)
The claim follows from `Module.Flat.lTensor_preserves_injective_linearMap (M := T.V) PD.φ.toLinearMap PD.φ_inj`.
-/
theorem phi_inj (T : LocLat G Qp LL O) : Function.Injective (φVB PD (LL := LL) (V := T.V)) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := T.V) PD.φ.toLinearMap PD.φ_inj

/- English proof (translation)
Simplify using `only [DcrisL, Dcris, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply, sub_eq_zero] at hx ⊢`. Take `⟨h1, h2⟩` from `hx`. Establish `a1 : ∀ g (y : T.V ⊗[Qp] B), actVB PD T.ρ g (φVB PD (LL` using `LL) (V := T.V) y) = φVB PD (LL := LL) (V := T.V) (actVB PD T.ρ g y) := by`. Introduce `g y`. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul a b => simp [actVB, φVB, PD.φ_comm]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Establish `a2 : ∀ (c : K₀) (y : T.V ⊗[Qp] B), mulVB (K₀` using `K₀) (B := B) (V := T.V) (LL := LL) (PD.σ c) (φVB PD (LL := LL) (V := T.V) y) = φVB PD (LL := LL) (V := T.V) (mulVB (K₀ := K₀) (B := B) (V := T.V) (LL := LL) c y) := by`. Introduce `c y`.

Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp [mulVB, φVB, PD.φ_K₀]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Use `⟨fun g => by rw [a1, h1], fun c => ?_⟩` and prove the remaining obligations.

Take `⟨c, rfl⟩` from `PD.σ_bij.2 c`. Establish `h3` using `DFunLike.congr_fun (W.emb_σ (i - 1)) c`. Rewrite `h3` using `[sub_add_cancel, AlgHom.comp_apply]`. Rewrite using `[a2, h2, map_smul, h3]`.
-/
theorem phi_mem (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (x : T.V ⊗[Qp] B)
    (hx : x ∈ DcrisL PD T.ρ (W.emb (i - 1))) :
    φVB PD (LL := LL) (V := T.V) x ∈ DcrisL PD T.ρ (W.emb i) := by
  simp only [DcrisL, Dcris, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply, sub_eq_zero] at hx ⊢
  obtain ⟨h1, h2⟩ := hx
  have a1 : ∀ g (y : T.V ⊗[Qp] B), actVB PD T.ρ g (φVB PD (LL := LL) (V := T.V) y) =
      φVB PD (LL := LL) (V := T.V) (actVB PD T.ρ g y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [actVB, φVB, PD.φ_comm]
    | add a b ha hb => simp only [map_add, ha, hb]
  have a2 : ∀ (c : K₀) (y : T.V ⊗[Qp] B),
      mulVB (K₀ := K₀) (B := B) (V := T.V) (LL := LL) (PD.σ c) (φVB PD (LL := LL) (V := T.V) y) =
      φVB PD (LL := LL) (V := T.V) (mulVB (K₀ := K₀) (B := B) (V := T.V) (LL := LL) c y) := by
    intro c y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [mulVB, φVB, PD.φ_K₀]
    | add a b ha hb => simp only [map_add, ha, hb]
  refine ⟨fun g => by rw [a1, h1], fun c => ?_⟩
  obtain ⟨c, rfl⟩ := PD.σ_bij.2 c
  have h3 := DFunLike.congr_fun (W.emb_σ (i - 1)) c
  rw [sub_add_cancel, AlgHom.comp_apply] at h3
  rw [a2, h2, map_smul, h3]

/- English proof (translation)
Introduce `h`. Take `⟨E, h0, h1, h2⟩` from `W.lev_π i ζ hζ`. Take `⟨j, hj⟩` from `hζ`. Establish `hz : ζ ≠ 0` using `hj.ne_zero (pow_ne_zero _ PD.hp.ne_zero)`. Establish `h3 : (letπ : LetA O n) * W.q = (1 + letπ) ^ PD.p - 1`.

Use function extensionality and compare the values at `a`. Simplify `W.q₀_def` using `[letπ, LocWach.q]`. Establish `h4` using `congrArg (W.lev i ζ) h3`. Rewrite `h4` using `[map_mul, h, mul_zero, map_sub, map_pow, map_add, map_one, h2]`. Establish `h5` using `congrArg (fun f => PowerSeries.constantCoeff (PowerSeries.derivative LL f)) h4`.

Simplify using `[Derivation.leibniz_pow, h0, h1, hz, p_ne W] at h5`.
-/
theorem lev_q_ne (W : LocWach PD LL O v n) (i : ZMod n) (ζ : LL)
    (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) : W.lev i ζ W.q ≠ 0 := by
  intro h
  obtain ⟨E, h0, h1, h2⟩ := W.lev_π i ζ hζ
  obtain ⟨j, hj⟩ := hζ
  have hz : ζ ≠ 0 := hj.ne_zero (pow_ne_zero _ PD.hp.ne_zero)
  have h3 : (letπ : LetA O n) * W.q = (1 + letπ) ^ PD.p - 1 := by
    funext a
    simpa [letπ, LocWach.q] using W.q₀_def
  have h4 := congrArg (W.lev i ζ) h3
  rw [map_mul, h, mul_zero, map_sub, map_pow, map_add, map_one, h2] at h4
  have h5 := congrArg (fun f => PowerSeries.constantCoeff (PowerSeries.derivative LL f)) h4
  simp [Derivation.leibniz_pow, h0, h1, hz, p_ne W] at h5

/- English proof (translation)
Take `⟨j, hj⟩` from `hζ`. Consider the cases of `j with`. Consider the case `zero`. Use `⟨0, ?_⟩` and prove the remaining obligations. Establish `: ζ = 1` using `by simpa using hj`.

Simplify using `[this]`. Consider the case `succ j => exact ⟨j, hj.pow (pow_pos hp.pos _) (pow_succ' _ _)⟩`.
-/
theorem root_pow {ζ : LL} {p : ℕ} (hp : p.Prime) (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (p ^ j)) :
    ∃ j : ℕ, IsPrimitiveRoot (ζ ^ p) (p ^ j) := by
  obtain ⟨j, hj⟩ := hζ
  cases j with
  | zero =>
    refine ⟨0, ?_⟩
    have : ζ = 1 := by simpa using hj
    simp [this]
  | succ j => exact ⟨j, hj.pow (pow_pos hp.pos _) (pow_succ' _ _)⟩

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero => intro i ζ hζ`. Simplify using `using lev_q_ne W i ζ hζ`. Consider the case `succ r ih`. Introduce `i ζ hζ h`.

Rewrite `h` using `[pow_succ', AlgHom.mul_apply, hφ i ζ hζ]`. Apply `ih _ _ (root_pow PD.hp hζ)` to reduce the goal to its premises. Apply `PowerSeries.rescale_injective (p_ne W)` to reduce the goal to its premises. Rewrite using `[h, map_zero]`.
-/
theorem lev_Q_ne (W : LocWach PD LL O v n)
    (hφ : ∀ (i : ZMod n) (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ f : LetA O n,
      W.lev i ζ (W.φA f) = PowerSeries.rescale (PD.p : LL) (W.lev (i - 1) (ζ ^ PD.p) f))
    (r : ℕ) : ∀ (i : ZMod n) (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) →
      W.lev i ζ ((W.φA ^ r) W.q) ≠ 0 := by
  induction r with
  | zero => intro i ζ hζ; simpa using lev_q_ne W i ζ hζ
  | succ r ih =>
    intro i ζ hζ h
    rw [pow_succ', AlgHom.mul_apply, hφ i ζ hζ] at h
    apply ih _ _ (root_pow PD.hp hζ)
    apply PowerSeries.rescale_injective (p_ne W)
    rw [h, map_zero]

/- English proof (translation)
Establish `hinj : Function.Injective (ιV PD (LL` using `LL) (V := T.V)) := Module.Flat.lTensor_preserves_injective_linearMap (M := T.V) (PD.ι.toLinearMap.restrictScalars Qp) PD.ι_inj`. Use function extensionality and compare the values at `k`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[← he, W.levN_smul]`. Unfold `conv`.

Rewrite using `[map_finsum _ (conv_finite (W.lev i ζ a) (hs x) k)]`. Use `finsum_congr fun j => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.map_smul, he]`.
-/
theorem wachExpansion_smul_compatible (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL)
    (e : ↥(W.N T) → ℤ → T.V ⊗[Qp] B) (hs : ∀ x, Bd (e x))
    (he : ∀ x k, W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (e x k))
    (a : LetA O n) (x : ↥(W.N T)) : e (a • x) = conv (W.lev i ζ a) (e x) := by
  have hinj : Function.Injective (ιV PD (LL := LL) (V := T.V)) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := T.V)
      (PD.ι.toLinearMap.restrictScalars Qp) PD.ι_inj
  funext k
  apply hinj
  rw [← he, W.levN_smul]
  unfold conv
  rw [map_finsum _ (conv_finite (W.lev i ζ a) (hs x) k)]
  refine finsum_congr fun j => ?_
  rw [LinearMap.map_smul, he]

/- English proof (translation)
Establish `hs : ∀ (a : LetA O n) x, e x ∈ Λ → e (a • x) ∈ Λ` using `fun a x hx => by`. Rewrite using `[he]`. Conclude with `hΛ _ _ hx`. Set `U : Submodule (LetA O n) ↥(W.N T)` to `{ carrier := {x | e x ∈ Λ} zero_mem' := by simp add_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_setOf_eq, map_add] at ha hb ⊢`.

Conclude with `Λ.add_mem ha hb`. Use the proof step `smul_mem' := fun a x hx => hs a x hx }`. Set `U' : Submodule (LetA O n) (W.DD T)` to `U.map (W.N T).subtype`. Establish `mono : ∀ (z : W.DD T) (a b : ℕ), W.Q ^ a • z ∈ U' → W.Q ^ (b + a) • z ∈ U'`. Introduce `z a b h`.

Rewrite using `[pow_add, mul_smul]`. Conclude with `U'.smul_mem _ h`. Establish `key : ∀ (S : Set (W.DD T)) (k : ℕ), (∀ z ∈ S, W.Q ^ k • z ∈ U') → ∀ z ∈ Submodule.span (LetA O n) S, W.Q ^ k • z ∈ U'`. Introduce `S k hS z hz`. Establish `: Submodule.span (LetA O n) S ≤ U'.comap (W.Q ^ k • LinearMap.id)` using `Submodule.span_le.2 fun z hz => hS z hz`.

Conclude with `this hz`. Establish `fin : ∀ S : Finset (W.DD T), (∀ z ∈ S, ∃ k : ℕ, W.Q ^ k • z ∈ U') → ∃ k : ℕ, ∀ z ∈ S, W.Q ^ k • z ∈ U'`. Introduce `S hS`. Use `choose! f hf using hS`. Use `⟨S.sup f, fun z hz => ?_⟩` and prove the remaining obligations.

Take `⟨b, hb⟩` from `Nat.exists_eq_add_of_le' (Finset.le_sup (f := f) hz)`. Rewrite using `[hb]`. Conclude with `mono z _ _ (hf z hz)`. Establish `one : ∀ z ∈ W.N T, ∃ k : ℕ, W.Q ^ k • z ∈ U'`. Introduce `z hz`.

Take `⟨k, hk⟩` from `W.N_φinv T z hz`. Take `⟨S, hS, hzS⟩` from `Submodule.mem_span_finite_of_mem_span hk`. Take `⟨k', hk'⟩` from `fin S fun w hw => by`. Take `⟨x, hx, rfl⟩` from `hS hw`. Take `⟨m, hm⟩` from `W.N_φ T x hx`.

Conclude with `⟨m, ⟨_, hm⟩, hφ ⟨x, hx⟩ m hm, rfl⟩`. Use `⟨k' + k, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_add, mul_smul]`. Conclude with `key S k' hk' _ hzS`. Take `⟨S, hS⟩` from `W.N_fg T`.

Take `⟨k, hk⟩` from `fin S fun z hz => one z (hS ▸ Submodule.subset_span hz)`. Use `⟨k, fun y => ?_⟩` and prove the remaining obligations. Take `⟨x, hx, hxy⟩` from `key S k hk y (by rw [hS]; exact y.2)`. Establish `: x = W.Q ^ k • y` using `Subtype.ext hxy`. Conclude with `this ▸ hx`.
-/
theorem pow_mem (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) {M : Type} [AddCommGroup M]
    [Module LL M] (e : ↥(W.N T) →+ (ℤ → M)) (lv : LetA O n → PowerSeries LL)
    (he : ∀ (a : LetA O n) x, e (a • x) = conv (lv a) (e x))
    (Λ : Submodule LL (ℤ → M)) (hΛ : ∀ (a : PowerSeries LL), ∀ f ∈ Λ, conv a f ∈ Λ)
    (hφ : ∀ (x : ↥(W.N T)) (m : ℕ) (hx : W.Q ^ m • W.φD T (x : W.DD T) ∈ W.N T), e ⟨_, hx⟩ ∈ Λ) :
    ∃ k : ℕ, ∀ y : ↥(W.N T), e (W.Q ^ k • y) ∈ Λ := by
  have hs : ∀ (a : LetA O n) x, e x ∈ Λ → e (a • x) ∈ Λ := fun a x hx => by
    rw [he]; exact hΛ _ _ hx
  let U : Submodule (LetA O n) ↥(W.N T) :=
    { carrier := {x | e x ∈ Λ}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢
        exact Λ.add_mem ha hb
      smul_mem' := fun a x hx => hs a x hx }
  let U' : Submodule (LetA O n) (W.DD T) := U.map (W.N T).subtype
  have mono : ∀ (z : W.DD T) (a b : ℕ), W.Q ^ a • z ∈ U' → W.Q ^ (b + a) • z ∈ U' := by
    intro z a b h
    rw [pow_add, mul_smul]
    exact U'.smul_mem _ h
  have key : ∀ (S : Set (W.DD T)) (k : ℕ), (∀ z ∈ S, W.Q ^ k • z ∈ U') →
      ∀ z ∈ Submodule.span (LetA O n) S, W.Q ^ k • z ∈ U' := by
    intro S k hS z hz
    have : Submodule.span (LetA O n) S ≤ U'.comap (W.Q ^ k • LinearMap.id) :=
      Submodule.span_le.2 fun z hz => hS z hz
    exact this hz
  have fin : ∀ S : Finset (W.DD T), (∀ z ∈ S, ∃ k : ℕ, W.Q ^ k • z ∈ U') →
      ∃ k : ℕ, ∀ z ∈ S, W.Q ^ k • z ∈ U' := by
    intro S hS
    choose! f hf using hS
    refine ⟨S.sup f, fun z hz => ?_⟩
    obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := f) hz)
    rw [hb]
    exact mono z _ _ (hf z hz)
  have one : ∀ z ∈ W.N T, ∃ k : ℕ, W.Q ^ k • z ∈ U' := by
    intro z hz
    obtain ⟨k, hk⟩ := W.N_φinv T z hz
    obtain ⟨S, hS, hzS⟩ := Submodule.mem_span_finite_of_mem_span hk
    obtain ⟨k', hk'⟩ := fin S fun w hw => by
      obtain ⟨x, hx, rfl⟩ := hS hw
      obtain ⟨m, hm⟩ := W.N_φ T x hx
      exact ⟨m, ⟨_, hm⟩, hφ ⟨x, hx⟩ m hm, rfl⟩
    refine ⟨k' + k, ?_⟩
    rw [pow_add, mul_smul]
    exact key S k' hk' _ hzS
  obtain ⟨S, hS⟩ := W.N_fg T
  obtain ⟨k, hk⟩ := fin S fun z hz => one z (hS ▸ Submodule.subset_span hz)
  refine ⟨k, fun y => ?_⟩
  obtain ⟨x, hx, hxy⟩ := key S k hk y (by rw [hS]; exact y.2)
  have : x = W.Q ^ k • y := Subtype.ext hxy
  exact this ▸ hx

variable {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]

/- English proof (translation)
Establish `hp` using `p_ne W`. Establish `hs : ∀ x, Bd (C.levB T i ζ x)` using `C.levB_supp T i ζ`. Establish `hs' : ∀ x, Bd (C.levB T (i - 1) (ζ ^ PD.p) x)` using `C.levB_supp T _ _`. Establish `hΛ` using `map_conv (fun x => C.levB T (i - 1) (ζ ^ PD.p) x) hs' hp (φVB PD (LL := LL) (V := T.V))`. Establish `he` using `wachExpansion_smul_compatible W T i ζ (fun x => C.levB T i ζ x) hs (C.levN_eq T i ζ)`.

Take `⟨k, hk⟩` from `pow_mem W T (C.levB T i ζ) (W.lev i ζ) he _ hΛ (fun x m hx => by`. Establish `: C.levB T i ζ ⟨_, hx⟩ = conv (W.lev i ζ (W.Q ^ m)) (Tw (PD.p : LL) (φVB PD (LL` using `LL) (V := T.V)) (C.levB T (i - 1) (ζ ^ PD.p) x)) :=`. Use function extensionality and compare the values at `fun k => C.levB_φ T hT i ζ hζ x m hx k`. Rewrite using `[this]`. Conclude with `hΛ _ _ ⟨_, Submodule.subset_span ⟨1, x, (conv_one _).symm⟩, rfl⟩)`.

Use `full_of_conv hp _ (phi_inj T) _ _ (phi_mem W T i) _ _ (W.lev i ζ (W.Q ^ k)) ?_ ?_ hF` and prove the remaining obligations. Rewrite using `[map_pow]`. Conclude with `pow_ne_zero _ (lev_Q_ne W C.lev_φ _ i ζ hζ)`. Introduce `f hf`. Use `(conv_latSpan _ hs _ _ (fun e x => hΛ _ _ ?_) f hf).2` and prove the remaining obligations.

Rewrite using `[← he]`. Conclude with `hk x`.
-/
theorem full_down_generic (W : LocWach PD LL O v n) {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}
    (C : CmpTie W E ιdR p1 tS zS) (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (i : ZMod n) (ζ : LL)
    (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j))
    (hF : Full (DcrisL PD T.ρ (W.emb i)) (latSpan (LL := LL) fun x => C.levB T i ζ x)) :
    Full (DcrisL PD T.ρ (W.emb (i - 1))) (latSpan (LL := LL) fun x => C.levB T (i - 1) (ζ ^ PD.p) x) := by
  have hp := p_ne W
  have hs : ∀ x, Bd (C.levB T i ζ x) := C.levB_supp T i ζ
  have hs' : ∀ x, Bd (C.levB T (i - 1) (ζ ^ PD.p) x) := C.levB_supp T _ _
  have hΛ := map_conv (fun x => C.levB T (i - 1) (ζ ^ PD.p) x) hs' hp (φVB PD (LL := LL) (V := T.V))
  have he := wachExpansion_smul_compatible W T i ζ (fun x => C.levB T i ζ x) hs (C.levN_eq T i ζ)
  obtain ⟨k, hk⟩ := pow_mem W T (C.levB T i ζ) (W.lev i ζ) he _ hΛ (fun x m hx => by
    have : C.levB T i ζ ⟨_, hx⟩ = conv (W.lev i ζ (W.Q ^ m))
        (Tw (PD.p : LL) (φVB PD (LL := LL) (V := T.V)) (C.levB T (i - 1) (ζ ^ PD.p) x)) :=
      funext fun k => C.levB_φ T hT i ζ hζ x m hx k
    rw [this]
    exact hΛ _ _ ⟨_, Submodule.subset_span ⟨1, x, (conv_one _).symm⟩, rfl⟩)
  refine full_of_conv hp _ (phi_inj T) _ _ (phi_mem W T i) _ _ (W.lev i ζ (W.Q ^ k)) ?_ ?_ hF
  · rw [map_pow]
    exact pow_ne_zero _ (lev_Q_ne W C.lev_φ _ i ζ hζ)
  · intro f hf
    refine (conv_latSpan _ hs _ _ (fun e x => hΛ _ _ ?_) f hf).2
    rw [← he]
    exact hk x

end Generic

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `D HW F Cm l _ K s LL h W E C T hT i ζ hζ hF`. Establish `hp : ((D.loc l).PD K).p = l` using `(D.loc l).PD_p K`. Use `full_down_generic W (C.C K s LL h).tie T hT i ζ (by rw [hp]; exact hζ) hF` as an intermediate fact. Establish `e : ζ ^ ((D.loc l).PD K).p = ζ ^ l` using `by rw [hp]`. Rewrite `this` using `[e]`.

Conclude with `this`.
-/
theorem full_down : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1), (∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) → Full (Di (HW l) h T i) (Lat C h T i ζ) → Full (Di (HW l) h T (i - 1)) (Lat C h T (i - 1) (ζ ^ l)) := by
  intro D HW F Cm l _ K s LL h W E C T hT i ζ hζ hF
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have := full_down_generic W (C.C K s LL h).tie T hT i ζ (by rw [hp]; exact hζ) hF
  have e : ζ ^ ((D.loc l).PD K).p = ζ ^ l := by rw [hp]
  rw [e] at this
  exact this

end GlobalTheory.NL.FullDown
