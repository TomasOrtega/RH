import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGaloisInvariantValuationIntegersEqIntegral
open scoped MatrixGroups NNReal
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.K5.OkBasis

section Abstract

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [Field L] (v : Valuation L ℝ≥0)

/- English proof (translation)
Establish `key : ∀ {a b : ℝ≥0} {k l : ℤ}, c < a → b ≤ 1 → c ^ k * a = c ^ l * b → ¬ k < l`. Introduce `a b k l ha hb1 h hkl`. Establish `h2 : c ^ l ≤ c ^ (k + 1)` using `zpow_le_zpow_right_of_le_one₀ h0 h1.le (by omega)`. Establish `h3 : c ^ l * b ≤ c ^ k * c`. Rewrite `h2` using `[zpow_add_one₀ h0.ne']`.

Conclude with `(mul_le_of_le_one_right' hb1).trans h2`. Establish `h4 : c ^ k * c < c ^ k * a` using `mul_lt_mul_of_pos_left ha (zpow_pos h0 k)`. Conclude with `absurd (h ▸ h4) (not_lt.2 h3)`. Establish `hkl : k = l` using `le_antisymm (not_lt.1 (key hb ha1 h.symm)) (not_lt.1 (key ha hb1 h))`. Substitute `hkl` using the available equality.

Conclude with `mul_left_cancel₀ (zpow_pos h0 k).ne' h`.
-/
theorem eq_of_zpow_mul {c a b : ℝ≥0} (h0 : 0 < c) (h1 : c < 1) (ha : c < a) (ha1 : a ≤ 1) (hb : c < b) (hb1 : b ≤ 1)
    {k l : ℤ} (h : c ^ k * a = c ^ l * b) : a = b := by
  have key : ∀ {a b : ℝ≥0} {k l : ℤ}, c < a → b ≤ 1 → c ^ k * a = c ^ l * b → ¬ k < l := by
    intro a b k l ha hb1 h hkl
    have h2 : c ^ l ≤ c ^ (k + 1) := zpow_le_zpow_right_of_le_one₀ h0 h1.le (by omega)
    have h3 : c ^ l * b ≤ c ^ k * c := by
      rw [zpow_add_one₀ h0.ne'] at h2
      exact (mul_le_of_le_one_right' hb1).trans h2
    have h4 : c ^ k * c < c ^ k * a := mul_lt_mul_of_pos_left ha (zpow_pos h0 k)
    exact absurd (h ▸ h4) (not_lt.2 h3)
  have hkl : k = l := le_antisymm (not_lt.1 (key hb ha1 h.symm)) (not_lt.1 (key ha hb1 h))
  subst hkl
  exact mul_left_cancel₀ (zpow_pos h0 k).ne' h

/- English proof (translation)
Use `⟨z.valuation, ?_⟩` and prove the remaining obligations. Use `set u := PadicInt.unitCoeff hz`. Establish `hu : v (φ u) = 1`. Use `le_antisymm (hφ _) ?_` and prove the remaining obligations. Establish `h1 : v (φ u) * v (φ (u⁻¹ : ℤ_[p]ˣ)) = 1`.

Rewrite using `[← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]`. Combine the equalities or inequalities in the displayed calculation. Use `conv_lhs => rw [PadicInt.unitCoeff_spec hz]`. Rewrite using `[map_mul, map_mul, hu, one_mul, map_pow, map_pow, map_natCast]`.
-/
theorem val_int (φ : ℤ_[p] →+* L) (hφ : ∀ z, v (φ z) ≤ 1) {z : ℤ_[p]} (hz : z ≠ 0) :
    ∃ n : ℕ, v (φ z) = v (p : L) ^ n := by
  refine ⟨z.valuation, ?_⟩
  set u := PadicInt.unitCoeff hz
  have hu : v (φ u) = 1 := by
    refine le_antisymm (hφ _) ?_
    have h1 : v (φ u) * v (φ (u⁻¹ : ℤ_[p]ˣ)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    calc (1 : ℝ≥0) = v (φ u) * v (φ (u⁻¹ : ℤ_[p]ˣ)) := h1.symm
      _ ≤ v (φ u) := mul_le_of_le_one_right' (hφ _)
  conv_lhs => rw [PadicInt.unitCoeff_spec hz]
  rw [map_mul, map_mul, hu, one_mul, map_pow, map_pow, map_natCast]

/- English proof (translation)
Establish `hk : ∀ k : ℕ, ∃ (l : ι → ℤ_[p]) (y : L), v y ≤ 1 ∧ x = ∑ i, b i * φ (l i) + p ^ k * y`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => exact ⟨0, x, hx, by simp⟩`. Consider the case `succ k ih`.

Take `⟨l, y, hy, rfl⟩` from `ih`. Take `⟨l', y', hy', rfl⟩` from `h y hy`. Use `⟨fun i => l i + p ^ k * l' i, y', hy', ?_⟩` and prove the remaining obligations. Simplify using `only [map_add, map_mul, map_pow, map_natCast, mul_add, Finset.sum_add_distrib, Finset.mul_sum]`. Rewrite using `[add_assoc, pow_succ, mul_assoc]`.

Use `congr 2`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Use `choose l y hy hxl using hk`. Take `⟨a, ψ, hψ, hlim⟩` from `CompactSpace.tendsto_subseq l`. Use `⟨a, ?_⟩` and prove the remaining obligations.

Establish `hle : ∀ k : ℕ, v (x - ∑ i, b i * φ (a i)) ≤ v (p : L) ^ k`. Introduce `k`. Establish `hpos : (0 : ℝ) < (p : ℝ) ^ (-(k : ℤ))` using `zpow_pos (by exact_mod_cast hp.out.pos) _`. Take `⟨N, hN⟩` from `Metric.tendsto_atTop.1 hlim _ hpos`. Establish `hn` using `hN (max N k) (le_max_left _ _)`.

Use `set n := ψ (max N k) with hndef`. Establish `hkn : k ≤ n` using `(le_max_right N k).trans (hψ.id_le _)`. Establish `hd : ∀ i, ∃ w, l n i - a i = w * p ^ k` using `fun i => by`. Establish `h2 : ‖l n i - a i‖ ≤ (p : ℝ) ^ (-(k : ℤ))`. Rewrite using `[← dist_eq_norm]`.

Conclude with `(dist_le_pi_dist (l n) a i).trans hn.le`. Take `⟨w, hw⟩` from `Ideal.mem_span_singleton'.1 ((PadicInt.norm_le_pow_iff_mem_span_pow _ k).1 h2)`. Conclude with `⟨w, hw.symm⟩`. Use `choose w hw using hd`. Establish `he : x - ∑ i, b i * φ (a i) = (∑ i, b i * φ (w i) + p ^ (n - k) * y n) * p ^ k`.

Rewrite using `[add_mul, Finset.sum_mul, mul_right_comm, ← pow_add, Nat.sub_add_cancel hkn]`. Use `conv_lhs => rw [hxl n]`. Rewrite using `[add_sub_right_comm, ← Finset.sum_sub_distrib]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← mul_sub, ← map_sub, hw, map_mul, map_pow, map_natCast, mul_assoc]`. Rewrite using `[he, map_mul, map_pow]`. Use `mul_le_of_le_one_left' (v.map_add_le (v.map_sum_le fun i _ => ?_) ?_)` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `mul_le_one' (hb i) (hφ _)`.

Rewrite using `[map_mul, map_pow]`. Conclude with `mul_le_one' (pow_le_one' h1.le _) (hy n)`. Establish `h0` using `ge_of_tendsto' (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one h1) hle`. Conclude with `sub_eq_zero.1 ((Valuation.zero_iff v).1 (le_antisymm h0 zero_le))`.
-/
theorem exists_eq_sum (φ : ℤ_[p] →+* L) (hφ : ∀ z, v (φ z) ≤ 1) (h1 : v (p : L) < 1) {ι : Type} [Fintype ι]
    (b : ι → L) (hb : ∀ i, v (b i) ≤ 1)
    (h : ∀ x, v x ≤ 1 → ∃ (l : ι → ℤ_[p]) (y : L), v y ≤ 1 ∧ x = ∑ i, b i * φ (l i) + p * y)
    (x : L) (hx : v x ≤ 1) : ∃ l : ι → ℤ_[p], x = ∑ i, b i * φ (l i) := by
  have hk : ∀ k : ℕ, ∃ (l : ι → ℤ_[p]) (y : L), v y ≤ 1 ∧ x = ∑ i, b i * φ (l i) + p ^ k * y := by
    intro k
    induction k with
    | zero => exact ⟨0, x, hx, by simp⟩
    | succ k ih =>
      obtain ⟨l, y, hy, rfl⟩ := ih
      obtain ⟨l', y', hy', rfl⟩ := h y hy
      refine ⟨fun i => l i + p ^ k * l' i, y', hy', ?_⟩
      simp only [map_add, map_mul, map_pow, map_natCast, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      rw [add_assoc, pow_succ, mul_assoc]
      congr 2
      exact Finset.sum_congr rfl fun i _ => by ring
  choose l y hy hxl using hk
  obtain ⟨a, ψ, hψ, hlim⟩ := CompactSpace.tendsto_subseq l
  refine ⟨a, ?_⟩
  have hle : ∀ k : ℕ, v (x - ∑ i, b i * φ (a i)) ≤ v (p : L) ^ k := by
    intro k
    have hpos : (0 : ℝ) < (p : ℝ) ^ (-(k : ℤ)) := zpow_pos (by exact_mod_cast hp.out.pos) _
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim _ hpos
    have hn := hN (max N k) (le_max_left _ _)
    set n := ψ (max N k) with hndef
    have hkn : k ≤ n := (le_max_right N k).trans (hψ.id_le _)
    have hd : ∀ i, ∃ w, l n i - a i = w * p ^ k := fun i => by
      have h2 : ‖l n i - a i‖ ≤ (p : ℝ) ^ (-(k : ℤ)) := by
        rw [← dist_eq_norm]
        exact (dist_le_pi_dist (l n) a i).trans hn.le
      obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 ((PadicInt.norm_le_pow_iff_mem_span_pow _ k).1 h2)
      exact ⟨w, hw.symm⟩
    choose w hw using hd
    have he : x - ∑ i, b i * φ (a i) = (∑ i, b i * φ (w i) + p ^ (n - k) * y n) * p ^ k := by
      rw [add_mul, Finset.sum_mul, mul_right_comm, ← pow_add, Nat.sub_add_cancel hkn]
      conv_lhs => rw [hxl n]
      rw [add_sub_right_comm, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← mul_sub, ← map_sub, hw, map_mul, map_pow, map_natCast, mul_assoc]
    rw [he, map_mul, map_pow]
    refine mul_le_of_le_one_left' (v.map_add_le (v.map_sum_le fun i _ => ?_) ?_)
    · rw [map_mul]; exact mul_le_one' (hb i) (hφ _)
    · rw [map_mul, map_pow]; exact mul_le_one' (pow_le_one' h1.le _) (hy n)
  have h0 := ge_of_tendsto' (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one h1) hle
  exact sub_eq_zero.1 ((Valuation.zero_iff v).1 (le_antisymm h0 zero_le))

/- English proof (translation)
Establish `hπne : π ≠ 0` using `(Valuation.pos_iff v).1 hπ0`. Proceed by induction on `m with`. Consider the case `zero => exact fun x hx => ⟨fun _ => Fin.elim0, x, hx, by simp⟩`. Consider the case `succ m ih`. Introduce `x hx`.

Take `⟨μ, hμ⟩` from `hκ x hx`. Take `⟨l, y, hy, he⟩` from `ih ((x - ∑ j, κ j * φ (μ j)) / π) (by`. Rewrite using `[map_div₀]`. Conclude with `(div_le_one hπ0).2 (hπ _ hμ))`. Use `⟨fun j => Fin.cons (μ j) (l j), y, hy, ?_⟩` and prove the remaining obligations.

Rewrite `he` using `[div_eq_iff hπne, sub_eq_iff_eq_add']`. Rewrite using `[he]`. Simplify using `only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ, pow_zero, mul_one, Finset.sum_add_distrib, add_mul, Finset.sum_mul, pow_succ]`. Rewrite using `[add_assoc]`. Use `congr 2`.

Conclude with `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun s _ => by ring`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_expansion (φ : ℤ_[p] →+* L) {F : ℕ} (κ : Fin F → L) {π : L} (hπ0 : 0 < v π)
    (hπ : ∀ x, v x < 1 → v x ≤ v π)
    (hκ : ∀ x, v x ≤ 1 → ∃ μ : Fin F → ℤ_[p], v (x - ∑ j, κ j * φ (μ j)) < 1) (m : ℕ) :
    ∀ x, v x ≤ 1 → ∃ (l : Fin F → Fin m → ℤ_[p]) (y : L), v y ≤ 1 ∧
      x = ∑ j, ∑ s : Fin m, κ j * π ^ (s : ℕ) * φ (l j s) + π ^ m * y := by
  have hπne : π ≠ 0 := (Valuation.pos_iff v).1 hπ0
  induction m with
  | zero => exact fun x hx => ⟨fun _ => Fin.elim0, x, hx, by simp⟩
  | succ m ih =>
    intro x hx
    obtain ⟨μ, hμ⟩ := hκ x hx
    obtain ⟨l, y, hy, he⟩ := ih ((x - ∑ j, κ j * φ (μ j)) / π) (by
      rw [map_div₀]; exact (div_le_one hπ0).2 (hπ _ hμ))
    refine ⟨fun j => Fin.cons (μ j) (l j), y, hy, ?_⟩
    rw [div_eq_iff hπne, sub_eq_iff_eq_add'] at he
    rw [he]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ, pow_zero, mul_one,
      Finset.sum_add_distrib, add_mul, Finset.sum_mul, pow_succ]
    rw [add_assoc]
    congr 2
    · exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun s _ => by ring
    · ring

variable [Algebra ℚ_[p] L]

variable (p L) in

noncomputable def fromInt : ℤ_[p] →+* L := (algebraMap ℚ_[p] L).comp PadicInt.Coe.ringHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fromInt_apply (z : ℤ_[p]) : fromInt p L z = algebraMap ℚ_[p] L z := rfl

/- English proof (translation)
Take `⟨x, y, hy, rfl⟩` from `IsFractionRing.div_surjective (A := ℤ_[p]) a`. Establish `hy0 : y ≠ 0` using `nonZeroDivisors.ne_zero hy`. Establish `hx0 : x ≠ 0` using `by rintro rfl; simp at ha`. Take `⟨m, hm⟩` from `val_int v _ hφ hx0`. Take `⟨n, hn⟩` from `val_int v _ hφ hy0`.

Establish `hp0 : v (p : L) ≠ 0` using `by haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ_[p] L).injective`. Conclude with `(Valuation.ne_zero_iff v).2 (Nat.cast_ne_zero.2 hp.out.ne_zero)`. Use `⟨(m : ℤ) - n, ?_⟩` and prove the remaining obligations. Rewrite using `[map_div₀, map_div₀, zpow_sub₀ hp0, zpow_natCast, zpow_natCast, ← hm, ← hn]`. Both sides reduce to the same expression.
-/
theorem val_rat (hφ : ∀ z, v (fromInt p L z) ≤ 1) {a : ℚ_[p]} (ha : a ≠ 0) :
    ∃ k : ℤ, v (algebraMap ℚ_[p] L a) = v (p : L) ^ k := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := ℤ_[p]) a
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by rintro rfl; simp at ha
  obtain ⟨m, hm⟩ := val_int v _ hφ hx0
  obtain ⟨n, hn⟩ := val_int v _ hφ hy0
  have hp0 : v (p : L) ≠ 0 := by
    haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ_[p] L).injective
    exact (Valuation.ne_zero_iff v).2 (Nat.cast_ne_zero.2 hp.out.ne_zero)
  refine ⟨(m : ℤ) - n, ?_⟩
  rw [map_div₀, map_div₀, zpow_sub₀ hp0, zpow_natCast, zpow_natCast, ← hm, ← hn]
  rfl

variable [FiniteDimensional ℚ_[p] L]

/- English proof (translation)
Use `set S := {γ : ℝ≥0 | (∃ x, v x = γ) ∧ v (p : L) < γ ∧ γ ≤ 1}`. Use `choose x hx using fun γ : S => γ.2.1`. Establish `hli : LinearIndependent ℚ_[p] x`. Rewrite using `[linearIndependent_iff']`. Introduce `s g hg i hi`.

Assume the negation of the conclusion as `hgi`. Take `⟨j, hj, hmax⟩` from `s.exists_max_image (fun i => v (g i • x i)) ⟨i, hi⟩`. Establish `hpos : ∀ k, g k ≠ 0 → 0 < v (g k • x k)` using `fun k hk => by`. Rewrite using `[Algebra.smul_def, map_mul, hx]`. Conclude with `mul_pos ((Valuation.pos_iff v).2 (by simpa using hk)) (h0.trans k.2.2.1)`.

Establish `hj0 : 0 < v (g j • x j)` using `(hpos i hgi).trans_le (hmax i hi)`. Establish `hsum : v (∑ i ∈ s, g i • x i) = v (g j • x j)`. Use `v.map_sum_eq_of_lt hj fun k hk => ?_` and prove the remaining obligations. Rewrite `hk` using `[Finset.mem_sdiff, Finset.mem_singleton]`. Use `lt_of_le_of_ne (hmax k hk.1) fun heq => hk.2 ?_` and prove the remaining obligations.

Establish `hgj : g j ≠ 0` using `by rintro h; simp [h] at hj0`. Establish `hgk : g k ≠ 0` using `by rintro h; rw [← heq] at hj0; simp [h] at hj0`. Take `⟨a, ha⟩` from `val_rat v hφ hgj`. Take `⟨b, hb⟩` from `val_rat v hφ hgk`. Rewrite `heq` using `[Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, ha, hb, hx, hx]`.

Conclude with `Subtype.ext (eq_of_zpow_mul h0 h1 k.2.2.1 k.2.2.2 j.2.2.1 j.2.2.2 heq)`. Rewrite `hsum` using `[hg, map_zero]`. Conclude with `hj0.ne hsum`. Conclude with `Set.finite_coe_iff.1 hli.finite`.
-/
theorem finite_values (hφ : ∀ z, v (fromInt p L z) ≤ 1) (h0 : 0 < v (p : L)) (h1 : v (p : L) < 1) :
    {γ : ℝ≥0 | (∃ x, v x = γ) ∧ v (p : L) < γ ∧ γ ≤ 1}.Finite := by
  classical
  set S := {γ : ℝ≥0 | (∃ x, v x = γ) ∧ v (p : L) < γ ∧ γ ≤ 1}
  choose x hx using fun γ : S => γ.2.1
  have hli : LinearIndependent ℚ_[p] x := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    by_contra hgi
    obtain ⟨j, hj, hmax⟩ := s.exists_max_image (fun i => v (g i • x i)) ⟨i, hi⟩
    have hpos : ∀ k, g k ≠ 0 → 0 < v (g k • x k) := fun k hk => by
      rw [Algebra.smul_def, map_mul, hx]
      exact mul_pos ((Valuation.pos_iff v).2 (by simpa using hk)) (h0.trans k.2.2.1)
    have hj0 : 0 < v (g j • x j) := (hpos i hgi).trans_le (hmax i hi)
    have hsum : v (∑ i ∈ s, g i • x i) = v (g j • x j) := by
      refine v.map_sum_eq_of_lt hj fun k hk => ?_
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hk
      refine lt_of_le_of_ne (hmax k hk.1) fun heq => hk.2 ?_
      have hgj : g j ≠ 0 := by rintro h; simp [h] at hj0
      have hgk : g k ≠ 0 := by rintro h; rw [← heq] at hj0; simp [h] at hj0
      obtain ⟨a, ha⟩ := val_rat v hφ hgj
      obtain ⟨b, hb⟩ := val_rat v hφ hgk
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, ha, hb, hx, hx] at heq
      exact Subtype.ext (eq_of_zpow_mul h0 h1 k.2.2.1 k.2.2.2 j.2.2.1 j.2.2.2 heq)
    rw [hg, map_zero] at hsum
    exact hj0.ne hsum
  exact Set.finite_coe_iff.1 hli.finite

/- English proof (translation)
Establish `hfin : {γ : ℝ≥0 | (∃ x, v x = γ) ∧ v (p : L) ≤ γ ∧ γ < 1}.Finite`. Use `((finite_values v hφ h0 h1).insert (v (p : L))).subset ?_` and prove the remaining obligations. Introduce and unpack `γ ⟨h2, h3, h4⟩`. Break down `h3.eq_or_lt with h | h` into its components or cases. Conclude with `Or.inl h.symm`.

Conclude with `Or.inr ⟨h2, h, h4.le⟩`. Take `⟨γ, ⟨⟨π, rfl⟩, h3, h4⟩, hmax⟩` from `Set.exists_max_image _ id hfin ⟨v (p : L), ⟨p, rfl⟩, le_rfl, h1⟩`. Establish `hπ0 : 0 < v π` using `h0.trans_le h3`. Establish `hπ : ∀ x, v x < 1 → v x ≤ v π` using `fun x hx => by`. Break down `le_total (v (p : L)) (v x) with h | h` into its components or cases.

Conclude with `hmax _ ⟨⟨x, rfl⟩, h, hx⟩`. Conclude with `h.trans h3`. Take `⟨n, hn, hn'⟩` from `exists_nat_pow_near_of_lt_one h0 h1.le hπ0 h4`. Establish `hE : v π ^ n = v (p : L)`. Use `le_antisymm ?_ hn'` and prove the remaining obligations.

Assume the negation of the conclusion as `hlt`. Establish `hpos : 0 < v π ^ n` using `pow_pos hπ0 n`. Establish `h5` using `hπ (p / π ^ n) (by rw [map_div₀, map_pow]; exact (div_lt_one hpos).2 (not_le.1 hlt))`. Rewrite `h5` using `[map_div₀, map_pow, div_le_iff₀ hpos, ← pow_succ']`. Conclude with `absurd hn (not_lt.2 h5)`.

Use `⟨π, n, hπ0, h4, hπ, ?_, hE⟩` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos n with rfl | h` into its components or cases. Rewrite `hE` using `[pow_zero]`. Conclude with `absurd hE h1.ne'`. Conclude with `h`.
-/
theorem exists_uniformiser (hφ : ∀ z, v (fromInt p L z) ≤ 1) (h0 : 0 < v (p : L)) (h1 : v (p : L) < 1) :
    ∃ (π : L) (E : ℕ), 0 < v π ∧ v π < 1 ∧ (∀ x, v x < 1 → v x ≤ v π) ∧ 1 ≤ E ∧ v π ^ E = v (p : L) := by
  have hfin : {γ : ℝ≥0 | (∃ x, v x = γ) ∧ v (p : L) ≤ γ ∧ γ < 1}.Finite := by
    refine ((finite_values v hφ h0 h1).insert (v (p : L))).subset ?_
    rintro γ ⟨h2, h3, h4⟩
    rcases h3.eq_or_lt with h | h
    · exact Or.inl h.symm
    · exact Or.inr ⟨h2, h, h4.le⟩
  obtain ⟨γ, ⟨⟨π, rfl⟩, h3, h4⟩, hmax⟩ := Set.exists_max_image _ id hfin ⟨v (p : L), ⟨p, rfl⟩, le_rfl, h1⟩
  have hπ0 : 0 < v π := h0.trans_le h3
  have hπ : ∀ x, v x < 1 → v x ≤ v π := fun x hx => by
    rcases le_total (v (p : L)) (v x) with h | h
    · exact hmax _ ⟨⟨x, rfl⟩, h, hx⟩
    · exact h.trans h3
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near_of_lt_one h0 h1.le hπ0 h4
  have hE : v π ^ n = v (p : L) := by
    refine le_antisymm ?_ hn'
    by_contra hlt
    have hpos : 0 < v π ^ n := pow_pos hπ0 n
    have h5 := hπ (p / π ^ n) (by rw [map_div₀, map_pow]; exact (div_lt_one hpos).2 (not_le.1 hlt))
    rw [map_div₀, map_pow, div_le_iff₀ hpos, ← pow_succ'] at h5
    exact absurd hn (not_lt.2 h5)
  refine ⟨π, n, hπ0, h4, hπ, ?_, hE⟩
  rcases Nat.eq_zero_or_pos n with rfl | h
  · rw [pow_zero] at hE; exact absurd hE h1.ne'
  · exact h

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hall : ∀ F : ℕ, ∃ κ : Fin F → L, (∀ j, v (κ j) ≤ 1) ∧ (∀ μ : Fin F → ℤ_[p], (∃ j, ¬ (p : ℤ_[p]) ∣ μ j) → v (∑ j, κ j * fromInt p L (μ j)) = 1)`. Introduce `F`. Proceed by induction on `F with`.

Consider the case `zero => exact ⟨Fin.elim0, fun j => j.elim0, fun μ ⟨j, _⟩ => j.elim0⟩`. Consider the case `succ F ih`. Take `⟨κ, hκ, hu⟩` from `ih`. Take `⟨x, hx, hfar⟩` from `hcon F κ hκ hu`. Use `⟨Fin.cons x κ, fun j => Fin.cases hx hκ j, fun μ hμ => ?_⟩` and prove the remaining obligations.

Rewrite using `[Fin.sum_univ_succ]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ]`. Distinguish the cases in `h : (p : ℤ_[p]) ∣ μ 0`. Take `⟨j, hj⟩` from `hμ`. Establish `hs` using `hu (fun j => μ j.succ) (by`.

Use `Fin.cases (fun hj => absurd h hj) (fun j hj => ⟨j, hj⟩) j hj)` and prove the remaining obligations. Take `⟨w, hw⟩` from `h`. Establish `hlt : v (x * fromInt p L (μ 0)) < 1`. Rewrite using `[hw, map_mul, map_mul, map_mul, map_natCast]`. Conclude with `(mul_le_of_le_one_left' hx).trans_lt ((mul_le_of_le_one_right' (hφ w)).trans_lt h1)`.

Rewrite using `[v.map_add_eq_of_lt_right (hs ▸ hlt), hs]`. Establish `hunit : IsUnit (μ 0)`. Rewrite using `[PadicInt.isUnit_iff]`. Conclude with `le_antisymm (μ 0).2 (not_lt.1 fun h' => h ((PadicInt.norm_lt_one_iff_dvd _).1 h'))`. Take `⟨w, hw⟩` from `hunit.exists_left_inv`.

Use `le_antisymm (v.map_add_le ?_ (v.map_sum_le fun j _ => ?_)) ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `mul_le_one' hx (hφ _)`. Rewrite using `[map_mul]`. Conclude with `mul_le_one' (hκ _) (hφ _)`.

Establish `h2` using `hfar fun j => -(w * μ j.succ)`. Establish `h3 : x - ∑ j, κ j * fromInt p L (-(w * μ j.succ)) = fromInt p L w * (x * fromInt p L (μ 0) + ∑ j, κ j * fromInt p L (μ (Fin.succ j)))`. Rewrite using `[mul_add, mul_left_comm, ← map_mul, hw, map_one, mul_one, Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [map_neg, map_mul]; ring`.

Rewrite `h2` using `[h3, map_mul]`. Conclude with `h2.trans (mul_le_of_le_one_left' (hφ w))`. Take `⟨κ, -, hu⟩` from `hall (Module.finrank ℚ_[p] L + 1)`. Establish `hli : LinearIndependent ℚ_[p] κ`. Rewrite using `[Fintype.linearIndependent_iff]`.

Introduce `g hg i`. Assume the negation of the conclusion as `hgi`. Take `⟨j, -, hmax⟩` from `Finset.univ.exists_max_image (fun i => ‖g i‖) ⟨i, Finset.mem_univ i⟩`. Establish `hj0 : 0 < ‖g j‖` using `(norm_pos_iff.2 hgi).trans_le (hmax i (Finset.mem_univ i))`. Establish `hgj : g j ≠ 0` using `norm_pos_iff.1 hj0`.

Set `μ : Fin _ → ℤ_[p]` to `fun k => ⟨g k / g j, by`. Rewrite using `[norm_div]`. Conclude with `(div_le_one hj0).2 (hmax k (Finset.mem_univ k))⟩`. Establish `h2` using `hu μ ⟨j, by`. Establish `: μ j = 1` using `Subtype.ext (div_self hgj)`.

Rewrite using `[this, ← isUnit_iff_dvd_one]`. Conclude with `PadicInt.irreducible_p.not_isUnit⟩`. Establish `h3 : ∑ k, κ k * fromInt p L (μ k) = (g j)⁻¹ • ∑ k, g k • κ k`. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[smul_smul, Algebra.smul_def, mul_comm, fromInt_apply, mul_comm (g j)⁻¹, ← div_eq_mul_inv]`. Rewrite `h2` using `[h3, hg, smul_zero, map_zero]`. Conclude with `zero_ne_one h2`. Use `hli.fintype_card_le_finrank` as an intermediate fact. Simplify using `at this`.
-/
theorem exists_residue_basis (hφ : ∀ z, v (fromInt p L z) ≤ 1) (h1 : v (p : L) < 1) :
    ∃ (F : ℕ) (κ : Fin F → L), (∀ j, v (κ j) ≤ 1) ∧
      (∀ μ : Fin F → ℤ_[p], (∃ j, ¬ (p : ℤ_[p]) ∣ μ j) → v (∑ j, κ j * fromInt p L (μ j)) = 1) ∧
      ∀ x, v x ≤ 1 → ∃ μ : Fin F → ℤ_[p], v (x - ∑ j, κ j * fromInt p L (μ j)) < 1 := by
  by_contra hcon
  push_neg at hcon
  have hall : ∀ F : ℕ, ∃ κ : Fin F → L, (∀ j, v (κ j) ≤ 1) ∧
      (∀ μ : Fin F → ℤ_[p], (∃ j, ¬ (p : ℤ_[p]) ∣ μ j) → v (∑ j, κ j * fromInt p L (μ j)) = 1) := by
    intro F
    induction F with
    | zero => exact ⟨Fin.elim0, fun j => j.elim0, fun μ ⟨j, _⟩ => j.elim0⟩
    | succ F ih =>
      obtain ⟨κ, hκ, hu⟩ := ih
      obtain ⟨x, hx, hfar⟩ := hcon F κ hκ hu
      refine ⟨Fin.cons x κ, fun j => Fin.cases hx hκ j, fun μ hμ => ?_⟩
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      by_cases h : (p : ℤ_[p]) ∣ μ 0
      · obtain ⟨j, hj⟩ := hμ
        have hs := hu (fun j => μ j.succ) (by
          refine Fin.cases (fun hj => absurd h hj) (fun j hj => ⟨j, hj⟩) j hj)
        obtain ⟨w, hw⟩ := h
        have hlt : v (x * fromInt p L (μ 0)) < 1 := by
          rw [hw, map_mul, map_mul, map_mul, map_natCast]
          exact (mul_le_of_le_one_left' hx).trans_lt ((mul_le_of_le_one_right' (hφ w)).trans_lt h1)
        rw [v.map_add_eq_of_lt_right (hs ▸ hlt), hs]
      · have hunit : IsUnit (μ 0) := by
          rw [PadicInt.isUnit_iff]
          exact le_antisymm (μ 0).2 (not_lt.1 fun h' => h ((PadicInt.norm_lt_one_iff_dvd _).1 h'))
        obtain ⟨w, hw⟩ := hunit.exists_left_inv
        refine le_antisymm (v.map_add_le ?_ (v.map_sum_le fun j _ => ?_)) ?_
        · rw [map_mul]; exact mul_le_one' hx (hφ _)
        · rw [map_mul]; exact mul_le_one' (hκ _) (hφ _)
        · have h2 := hfar fun j => -(w * μ j.succ)
          have h3 : x - ∑ j, κ j * fromInt p L (-(w * μ j.succ)) =
              fromInt p L w * (x * fromInt p L (μ 0) + ∑ j, κ j * fromInt p L (μ (Fin.succ j))) := by
            rw [mul_add, mul_left_comm, ← map_mul, hw, map_one, mul_one, Finset.mul_sum, sub_eq_add_neg,
              ← Finset.sum_neg_distrib]
            congr 1
            exact Finset.sum_congr rfl fun j _ => by rw [map_neg, map_mul]; ring
          rw [h3, map_mul] at h2
          exact h2.trans (mul_le_of_le_one_left' (hφ w))
  obtain ⟨κ, -, hu⟩ := hall (Module.finrank ℚ_[p] L + 1)
  have hli : LinearIndependent ℚ_[p] κ := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    by_contra hgi
    obtain ⟨j, -, hmax⟩ := Finset.univ.exists_max_image (fun i => ‖g i‖) ⟨i, Finset.mem_univ i⟩
    have hj0 : 0 < ‖g j‖ := (norm_pos_iff.2 hgi).trans_le (hmax i (Finset.mem_univ i))
    have hgj : g j ≠ 0 := norm_pos_iff.1 hj0
    let μ : Fin _ → ℤ_[p] := fun k => ⟨g k / g j, by
      rw [norm_div]; exact (div_le_one hj0).2 (hmax k (Finset.mem_univ k))⟩
    have h2 := hu μ ⟨j, by
      have : μ j = 1 := Subtype.ext (div_self hgj)
      rw [this, ← isUnit_iff_dvd_one]
      exact PadicInt.irreducible_p.not_isUnit⟩
    have h3 : ∑ k, κ k * fromInt p L (μ k) = (g j)⁻¹ • ∑ k, g k • κ k := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_smul, Algebra.smul_def, mul_comm, fromInt_apply, mul_comm (g j)⁻¹, ← div_eq_mul_inv]
    rw [h3, hg, smul_zero, map_zero] at h2
    exact zero_ne_one h2
  have := hli.fintype_card_le_finrank
  simp at this

/- English proof (translation)
Take `⟨π, E, hπ0, hπ1, hπ, hE, hπE⟩` from `exists_uniformiser v hφ h0 h1`. Take `⟨F, κ, hκ, hu, hsp⟩` from `exists_residue_basis v hφ h1`. Use `⟨E, F, π, κ, hE, hπE, hκ, hu, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hp0 : (p : L) ≠ 0` using `(Valuation.pos_iff v).1 h0`. Take `⟨l, hl⟩` from `exists_eq_sum v (fromInt p L) hφ h1 (fun i : Fin F × Fin E => κ i.1 * π ^ (i.2 : ℕ)) (fun i => by rw [map_mul, map_pow]; exact mul_le_one' (hκ _) (pow_le_one' hπ1.le _)) (fun x hx => by`.

Take `⟨l, y, hy, he⟩` from `exists_expansion v (fromInt p L) κ hπ0 hπ hsp E x hx`. Use `⟨fun i => l i.1 i.2, π ^ E / p * y, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_div₀, map_pow, hπE, div_self h0.ne', one_mul]`. Conclude with `hy`. Rewrite using `[Fintype.sum_prod_type, ← mul_assoc, mul_div_cancel₀ _ hp0]`.

Conclude with `he) x hx`. Conclude with `⟨fun j s => l (j, s), by rw [hl, Fintype.sum_prod_type]⟩`.
-/
theorem exists_basis (hφ : ∀ z, v (fromInt p L z) ≤ 1) (h0 : 0 < v (p : L)) (h1 : v (p : L) < 1) :
    ∃ (E F : ℕ) (π : L) (κ : Fin F → L), 1 ≤ E ∧ v π ^ E = v (p : L) ∧ (∀ j, v (κ j) ≤ 1) ∧
      (∀ μ : Fin F → ℤ_[p], (∃ j, ¬ (p : ℤ_[p]) ∣ μ j) → v (∑ j, κ j * fromInt p L (μ j)) = 1) ∧
      ∀ x, v x ≤ 1 → ∃ l : Fin F → Fin E → ℤ_[p],
        x = ∑ j, ∑ s : Fin E, κ j * π ^ (s : ℕ) * fromInt p L (l j s) := by
  obtain ⟨π, E, hπ0, hπ1, hπ, hE, hπE⟩ := exists_uniformiser v hφ h0 h1
  obtain ⟨F, κ, hκ, hu, hsp⟩ := exists_residue_basis v hφ h1
  refine ⟨E, F, π, κ, hE, hπE, hκ, hu, fun x hx => ?_⟩
  have hp0 : (p : L) ≠ 0 := (Valuation.pos_iff v).1 h0
  obtain ⟨l, hl⟩ := exists_eq_sum v (fromInt p L) hφ h1 (fun i : Fin F × Fin E => κ i.1 * π ^ (i.2 : ℕ))
    (fun i => by rw [map_mul, map_pow]; exact mul_le_one' (hκ _) (pow_le_one' hπ1.le _))
    (fun x hx => by
      obtain ⟨l, y, hy, he⟩ := exists_expansion v (fromInt p L) κ hπ0 hπ hsp E x hx
      refine ⟨fun i => l i.1 i.2, π ^ E / p * y, ?_, ?_⟩
      · rw [map_mul, map_div₀, map_pow, hπE, div_self h0.ne', one_mul]; exact hy
      · rw [Fintype.sum_prod_type, ← mul_assoc, mul_div_cancel₀ _ hp0]; exact he) x hx
  exact ⟨fun j s => l (j, s), by rw [hl, Fintype.sum_prod_type]⟩

end Abstract

/- English proof (translation)
Introduce `p hp Ω _ _ hc v hv h0 h1 d e he`. Use `letI : Algebra ℤ_[p] Ω := ((algebraMap (O0 p) Ω).comp (algebraMap ℤ_[p] (O0 p))).toAlgebra`. Use `haveI : IsScalarTower ℤ_[p] (O0 p) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `hzp : ∀ z, zp Ω z = algebraMap ℤ_[p] Ω z` using `fun z => by`. Establish `h : (HahnSeries.single 0 z : Lau p) = algebraMap ℤ_[p] (Lau p) z`.

Rewrite using `[HahnSeries.algebraMap_apply' ]`. Simplify using the standard rewrite rules. Rewrite using `[zp, h]`. Both sides reduce to the same expression. Establish `halg : ∀ x : Ω, IsAlgZp p x ↔ IsAlgebraic ℤ_[p] x` using `fun x => by`.

Unfold `IsAlgZp IsAlgebraic`. Simplify using `only [Polynomial.aeval_map_algebraMap]`. Establish `hle : ∀ z, v (algebraMap ℤ_[p] Ω z) ≤ 1` using `fun z => (hv _).2 (isIntegral_algebraMap (x := algebraMap ℤ_[p] (O0 p) z))`. Establish `hinj : Function.Injective (algebraMap ℤ_[p] Ω)`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `z hz`. Assume the negation of the conclusion as `hz0`. Take `⟨n, hn⟩` from `val_int v _ hle hz0`. Rewrite `hn` using `[hz, map_zero]`. Conclude with `(pow_pos h0 n).ne hn`.

Use `letI : Algebra ℚ_[p] Ω := (IsFractionRing.lift (K := ℚ_[p]) hinj).toAlgebra`. Use `haveI : IsScalarTower ℤ_[p] ℚ_[p] Ω := IsScalarTower.of_algebraMap_eq fun z => (IsFractionRing.lift_algebraMap hinj z).symm`. Establish `halg' : ∀ x : Ω, IsAlgZp p x ↔ IsAlgebraic ℚ_[p] x` using `fun x => (halg x).trans (IsFractionRing.isAlgebraic_iff ℤ_[p] ℚ_[p] Ω)`. Set `L` to `IntermediateField.adjoin ℚ_[p] (Set.range e)`. Use `haveI : FiniteDimensional ℚ_[p] L := IntermediateField.finiteDimensional_adjoin (by`.

Introduce and unpack `_ ⟨t, rfl⟩`. Conclude with `((halg' _).1 (he t).2).isIntegral)`. Establish `hL : ∀ x : L, IsAlgZp p (x : Ω)` using `fun x => (halg' _).2 (IntermediateField.isAlgebraic_iff.1 (Algebra.IsAlgebraic.isAlgebraic x))`. Establish `hf : ∀ z, ((fromInt p L z : L) : Ω) = zp Ω z` using `fun z => (IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] Ω z).symm.trans (hzp z).symm`. Set `w : Valuation L ℝ≥0` to `v.comap (algebraMap L Ω)`.

Establish `hw : ∀ x : L, w x = v (x : Ω)` using `fun x => rfl`. Establish `hwp : w (p : L) = v (p : Ω)` using `by rw [hw]; simp`. Take `⟨E, F, π, κ, hE, hπ, hκ, hu, hsp⟩` from `exists_basis (p := p) w (fun z => by rw [hw, hf, hzp]; exact hle z) (hwp ▸ h0) (hwp ▸ h1)`. Use `choose lam hlam using fun t => hsp ⟨e t, IntermediateField.subset_adjoin _ _ ⟨t, rfl⟩⟩ ((hv _).2 (he t).1)`. Use `⟨E, F, π, fun j => κ j, lam, hE, hL π, by rw [← hwp, ← hπ, hw], fun j => ⟨(hv _).1 (hκ j), hL _⟩, fun μ hμ => ?_, fun t => ?_⟩` and prove the remaining obligations.

Use `hu μ hμ` as an intermediate fact. Rewrite `this` using `[hw]`. Move the coercions through the operations in `at this`. Simplify `this` using `only [hf]`. Use `congrArg (fun x : L => (x : Ω)) (hlam t)` as an intermediate fact.

Move the coercions through the operations in `at this`. Simplify `this` using `only [hf]`.
-/
theorem okbasis : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (v : Valuation Ω ℝ≥0), (∀ x : Ω, v x ≤ 1 ↔ IsInt p x) → 0 < v (p : Ω) → v (p : Ω) < 1 → ∀ (d : ℕ) (e : Fin d → Ω), (∀ t, IsInt p (e t) ∧ IsAlgZp p (e t)) → ∃ (E F : ℕ) (π : Ω) (κ : Fin F → Ω) (lam : Fin d → Fin F → Fin E → ℤ_[p]), 1 ≤ E ∧ IsAlgZp p π ∧ v π ^ E = v (p : Ω) ∧ (∀ j, IsInt p (κ j) ∧ IsAlgZp p (κ j)) ∧ (∀ μ : Fin F → ℤ_[p], (∃ j, ¬ (p : ℤ_[p]) ∣ μ j) → v (∑ j, κ j * zp Ω (μ j)) = 1) ∧ ∀ t, e t = ∑ j, ∑ s : Fin E, κ j * π ^ (s : ℕ) * zp Ω (lam t j s) := by
  intro p hp Ω _ _ hc v hv h0 h1 d e he
  letI : Algebra ℤ_[p] Ω := ((algebraMap (O0 p) Ω).comp (algebraMap ℤ_[p] (O0 p))).toAlgebra
  haveI : IsScalarTower ℤ_[p] (O0 p) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hzp : ∀ z, zp Ω z = algebraMap ℤ_[p] Ω z := fun z => by
    have h : (HahnSeries.single 0 z : Lau p) = algebraMap ℤ_[p] (Lau p) z := by
      rw [HahnSeries.algebraMap_apply' ]; simp
    rw [zp, h]
    rfl
  have halg : ∀ x : Ω, IsAlgZp p x ↔ IsAlgebraic ℤ_[p] x := fun x => by
    unfold IsAlgZp IsAlgebraic
    simp only [Polynomial.aeval_map_algebraMap]
  have hle : ∀ z, v (algebraMap ℤ_[p] Ω z) ≤ 1 := fun z =>
    (hv _).2 (isIntegral_algebraMap (x := algebraMap ℤ_[p] (O0 p) z))
  have hinj : Function.Injective (algebraMap ℤ_[p] Ω) := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    by_contra hz0
    obtain ⟨n, hn⟩ := val_int v _ hle hz0
    rw [hz, map_zero] at hn
    exact (pow_pos h0 n).ne hn
  letI : Algebra ℚ_[p] Ω := (IsFractionRing.lift (K := ℚ_[p]) hinj).toAlgebra
  haveI : IsScalarTower ℤ_[p] ℚ_[p] Ω := IsScalarTower.of_algebraMap_eq fun z =>
    (IsFractionRing.lift_algebraMap hinj z).symm
  have halg' : ∀ x : Ω, IsAlgZp p x ↔ IsAlgebraic ℚ_[p] x := fun x =>
    (halg x).trans (IsFractionRing.isAlgebraic_iff ℤ_[p] ℚ_[p] Ω)
  let L := IntermediateField.adjoin ℚ_[p] (Set.range e)
  haveI : FiniteDimensional ℚ_[p] L := IntermediateField.finiteDimensional_adjoin (by
    rintro _ ⟨t, rfl⟩
    exact ((halg' _).1 (he t).2).isIntegral)
  have hL : ∀ x : L, IsAlgZp p (x : Ω) := fun x =>
    (halg' _).2 (IntermediateField.isAlgebraic_iff.1 (Algebra.IsAlgebraic.isAlgebraic x))
  have hf : ∀ z, ((fromInt p L z : L) : Ω) = zp Ω z := fun z =>
    (IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] Ω z).symm.trans (hzp z).symm
  let w : Valuation L ℝ≥0 := v.comap (algebraMap L Ω)
  have hw : ∀ x : L, w x = v (x : Ω) := fun x => rfl
  have hwp : w (p : L) = v (p : Ω) := by rw [hw]; simp
  obtain ⟨E, F, π, κ, hE, hπ, hκ, hu, hsp⟩ := exists_basis (p := p) w
    (fun z => by rw [hw, hf, hzp]; exact hle z) (hwp ▸ h0) (hwp ▸ h1)
  choose lam hlam using fun t => hsp ⟨e t, IntermediateField.subset_adjoin _ _ ⟨t, rfl⟩⟩ ((hv _).2 (he t).1)
  refine ⟨E, F, π, fun j => κ j, lam, hE, hL π, by rw [← hwp, ← hπ, hw],
    fun j => ⟨(hv _).1 (hκ j), hL _⟩, fun μ hμ => ?_, fun t => ?_⟩
  · have := hu μ hμ
    rw [hw] at this
    push_cast at this
    simpa only [hf] using this
  · have := congrArg (fun x : L => (x : Ω)) (hlam t)
    push_cast at this
    simpa only [hf] using this

end GlobalTheory.K5.OkBasis
