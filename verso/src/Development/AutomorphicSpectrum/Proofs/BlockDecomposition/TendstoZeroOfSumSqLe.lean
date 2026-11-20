import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsBisTer

open MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa
  GroundTheory.Automorphic.Spherical PositivityTheory.JacquetShalikaLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.Satake

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.DYhd3.main B herm psd x y`.
-/
theorem norm_sq_le_of_psd {V : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (herm : ∀ u u', starRingEnd ℂ (B u u') = B u' u) (psd : ∀ u, 0 ≤ (B u u).re) (x y : V) :
    ‖B x y‖ ^ 2 ≤ (B x x).re * (B y y).re :=
  _root_.UpperTheory.Reformulated.B.DYhd3.main B herm psd x y

/- English proof (translation)
Establish `hs : Summable fun j => ‖g j‖ ^ 2` using `summable_of_sum_range_le (fun _ => sq_nonneg _) hD`. Establish `h0` using `hs.tendsto_atTop_zero`. Establish `h1` using `(Real.continuous_sqrt.tendsto 0).comp h0`. Rewrite `h1` using `[Real.sqrt_zero]`. Use `tendsto_zero_iff_norm_tendsto_zero.2 (h1.congr fun j => ?_)` and prove the remaining obligations.

Simplify using `[Real.sqrt_sq (norm_nonneg _)]`.
-/
theorem tendsto_zero_of_sum_sq_le (g : ℕ → ℂ) (D : ℝ)
    (hD : ∀ T, ∑ j ∈ Finset.range T, ‖g j‖ ^ 2 ≤ D) :
    Filter.Tendsto g Filter.atTop (nhds 0) := by
  have hs : Summable fun j => ‖g j‖ ^ 2 :=
    summable_of_sum_range_le (fun _ => sq_nonneg _) hD
  have h0 := hs.tendsto_atTop_zero
  have h1 := (Real.continuous_sqrt.tendsto 0).comp h0
  rw [Real.sqrt_zero] at h1
  refine tendsto_zero_iff_norm_tendsto_zero.2 (h1.congr fun j => ?_)
  simp [Real.sqrt_sq (norm_nonneg _)]

/- English proof (translation)
Establish `key : ∀ r ∈ Finset.range (j + 1), (-1) ^ r * (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, z i / s) * (h (j - r) / s ^ (j - r)) = ((-1) ^ r * (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, z i) * h (j - r)) / s ^ j`. Introduce `r hr`. Establish `hrj : r ≤ j` using `by simpa [Nat.lt_succ_iff] using hr`. Establish `e1 : (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, z i / s) = (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, z i) / s ^ r`. Rewrite using `[Finset.sum_div]`.

Use `Finset.sum_congr rfl fun S hS => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_div_distrib, Finset.prod_const, (Finset.mem_powersetCard.1 hS).2]`. Establish `e2 : s ^ j = s ^ r * s ^ (j - r)`. Rewrite using `[← pow_add]`. Use `congr 1`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[e1, e2]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[Finset.sum_congr rfl key, ← Finset.sum_div, hrec, zero_div]`.
-/
theorem recursion_scaled {n : ℕ} (s : ℂ) (hs : s ≠ 0) (z : Fin n → ℂ) (h : ℕ → ℂ) (j : ℕ)
    (hrec : ∑ r ∈ Finset.range (j + 1), (-1) ^ r *
      (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, z i) * h (j - r) = 0) :
    ∑ r ∈ Finset.range (j + 1), (-1) ^ r *
      (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, z i / s) *
        (h (j - r) / s ^ (j - r)) = 0 := by
  have key : ∀ r ∈ Finset.range (j + 1), (-1) ^ r *
      (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, z i / s) *
        (h (j - r) / s ^ (j - r)) = ((-1) ^ r *
      (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, z i) * h (j - r)) / s ^ j := by
    intro r hr
    have hrj : r ≤ j := by simpa [Nat.lt_succ_iff] using hr
    have e1 : (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, z i / s) =
        (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, z i) / s ^ r := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun S hS => ?_
      rw [Finset.prod_div_distrib, Finset.prod_const, (Finset.mem_powersetCard.1 hS).2]
    have e2 : s ^ j = s ^ r * s ^ (j - r) := by
      rw [← pow_add]
      congr 1
      omega
    rw [e1, e2]
    field_simp
  rw [Finset.sum_congr rfl key, ← Finset.sum_div, hrec, zero_div]

/- English proof (translation)
Establish `hY : (r ^ 2) ^ (j * m) = (r ^ (j * m)) ^ 2` using `by rw [← pow_mul, ← pow_mul, mul_comm]`. Establish `hXY : r ^ ((m + 1) * j) = r ^ j * r ^ (j * m)`. Rewrite using `[← pow_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `hX : r ^ j ≠ 0` using `(pow_pos hr _).ne'`. Establish `hYn : r ^ (j * m) ≠ 0` using `(pow_pos hr _).ne'`. Establish `e : W ^ 2 * (H / r ^ j) ^ 2 = (r ^ (j * m)) ^ 2 * (W * ((r ^ ((m + 1) * j))⁻¹ * H)) ^ 2`. Rewrite using `[hXY]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e, hY]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem bound_arith (r : ℝ) (hr : 0 < r) (m j : ℕ) (W H a b : ℝ)
    (hcs : (W * ((r ^ ((m + 1) * j))⁻¹ * H)) ^ 2 ≤ a * b) :
    W ^ 2 * (H / r ^ j) ^ 2 ≤ a * ((r ^ 2) ^ (j * m) * b) := by
  have hY : (r ^ 2) ^ (j * m) = (r ^ (j * m)) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
  have hXY : r ^ ((m + 1) * j) = r ^ j * r ^ (j * m) := by
    rw [← pow_add]
    congr 1
    ring
  have hX : r ^ j ≠ 0 := (pow_pos hr _).ne'
  have hYn : r ^ (j * m) ≠ 0 := (pow_pos hr _).ne'
  have e : W ^ 2 * (H / r ^ j) ^ 2 = (r ^ (j * m)) ^ 2 * (W * ((r ^ ((m + 1) * j))⁻¹ * H)) ^ 2 := by
    rw [hXY]
    field_simp
  rw [e, hY]
  calc _ ≤ (r ^ (j * m)) ^ 2 * (a * b) := mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
    _ = _ := by ring

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

/- English proof (translation)
Use `⟨hg, fun i j hj => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Rewrite using `[hg.2 i, Matrix.one_apply_eq]`. Establish `hlt : j < i`.

Establish `: (j : ℕ) < i`. Establish `: (i : ℕ) ≠ j` using `fun h => hij (Fin.ext h)`. Use linear arithmetic over natural numbers and integers. Conclude with `this`. Rewrite using `[hg.1 hlt, Matrix.one_apply_ne hij]`.
-/
theorem inU_zero_of_mem {g : GL (Fin n) F} (hg : g ∈ unipotent F n) : inU 0 g := by
  refine ⟨hg, fun i j hj => ?_⟩
  by_cases hij : i = j
  · subst hij
    rw [hg.2 i, Matrix.one_apply_eq]
  · have hlt : j < i := by
      have : (j : ℕ) < i := by
        have : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
        omega
      exact this
    rw [hg.1 hlt, Matrix.one_apply_ne hij]

/- English proof (translation)
Introduce `a b hab`. Distinguish the cases in `hb : b = ⟨0, hn⟩`. Establish `ha : a = ⟨0, hn⟩`. Substitute `hb` using the available equality. Conclude with `Fin.ext (by have h : (a : ℕ) ≤ 0 := hab; show (a : ℕ) = 0; omega)`.

Rewrite using `[ha, hb]`. Distinguish the cases in `ha : a = ⟨0, hn⟩`. Simplify using `[ha, hb]`. Simplify using `[ha, hb]`.
-/
theorem antitone_single (hn : 0 < n) (j : ℕ) :
    Antitone (Pi.single (⟨0, hn⟩ : Fin n) (j : ℤ) : Fin n → ℤ) := by
  intro a b hab
  by_cases hb : b = ⟨0, hn⟩
  · have ha : a = ⟨0, hn⟩ := by
      subst hb
      exact Fin.ext (by have h : (a : ℕ) ≤ 0 := hab; show (a : ℕ) = 0; omega)
    rw [ha, hb]
  · by_cases ha : a = ⟨0, hn⟩
    · simp [ha, hb]
    · simp [ha, hb]

/- English proof (translation)
Rewrite using `[rhoPair, Finset.sum_eq_single (⟨0, hn⟩ : Fin n) (fun b _ hb => by simp [hb]) (fun h => absurd (Finset.mem_univ _) h)]`. Simplify using the standard rewrite rules.
-/
theorem rhoPair_single_zero (hn : 0 < n) (j : ℕ) :
    rhoPair (Pi.single (⟨0, hn⟩ : Fin n) (j : ℤ) : Fin n → ℤ) = ((n : ℤ) - 1) * j := by
  rw [rhoPair, Finset.sum_eq_single (⟨0, hn⟩ : Fin n) (fun b _ hb => by simp [hb])
    (fun h => absurd (Finset.mem_univ _) h)]
  simp

end

/- English proof (translation)
Introduce `h6 h7 h8 h9`. Introduce `F _ _ _ _ _ _ μ _ ψ hψ n V _ _ ρ hsm hn l B hW hU v z hH hg i`. Take `⟨g₀, hg₀⟩` from `hg`. Establish `hlv : l v ≠ 0`. Introduce `h0`.

Apply `hg₀` to reduce the goal to its premises. Rewrite using `[h7 F ψ hψ n V ρ v z hH l hW g₀, h0, zero_mul]`. Take `⟨B', hI, hbd⟩` from `h6 F μ ψ hψ n V ρ hsm l B hn hW hU`. Take `⟨C, hC⟩` from `hbd v hH.1`. Establish `hn0 : 0 < n` using `by omega`.

Take `⟨m, rfl⟩ : ∃ m, n = m + 2` from `⟨n - 2, by omega⟩`. Use `set s := sqrtQ F with hsdef`. Establish `hs : s ≠ 0` using `sqrtQ_ne_zero`. Use `set r := ‖s‖ with hrdef`. Establish `hr : 0 < r` using `norm_pos_iff.2 hs`.

Establish `hq : (qF F : ℝ) = r ^ 2`. Rewrite using `[hrdef, ← norm_pow, hsdef, sqrtQ_sq, Complex.norm_natCast]`. Use `set w := B' v v with hwdef`. Establish `hw : w ≠ 0` using `fun h => hlv (hI.null v h)`. Establish `hW' : Whit ρ ψ (B' v)` using `fun g hg u => hI.equi g (inU_zero_of_mem hg) u v`.

Set `h : ℕ → ℂ` to `fun j => evalAt z (schur (Pi.single (⟨0, hn0⟩ : Fin (m + 2)) (j : ℤ)))`. Set `a : ℕ → GL (Fin (m + 2)) F` to `fun j => torusPow F (m + 2) (Pi.single ⟨0, hn0⟩ (j : ℤ))`. Establish `hC' : ∀ T : ℕ, ∑ j ∈ Finset.range T, (qF F : ℝ) ^ (j * m) * (B' (ρ (a j) v) (ρ (a j) v)).re ≤ C` using `hC`. Establish `hval : ∀ j, B' v (ρ (a j) v) = w * ((s ^ ((m + 1) * j))⁻¹ * h j)`. Introduce `j`.

Rewrite using `[h7 F ψ hψ (m + 2) V ρ v z hH (B' v) hW', sphericalWhittaker_torusPow hψ.1, if_pos (antitone_single hn0 j), halfModulus_eq, rhoPair_single_zero]`. Use `congr 2`. Rewrite using `[_root_.zpow_neg]`. Use `congr 1`. Rewrite using `[← zpow_natCast]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Set `g : ℕ → ℂ` to `fun j => h j / s ^ j`. Establish `hterm : ∀ j, ‖w‖ ^ 2 * ‖g j‖ ^ 2 ≤ w.re * ((qF F : ℝ) ^ (j * m) * (B' (ρ (a j) v) (ρ (a j) v)).re)`.

Introduce `j`. Establish `hcs` using `norm_sq_le_of_psd B' hI.herm hI.psd v (ρ (a j) v)`. Rewrite `hcs` using `[hval j, norm_mul, norm_mul, norm_inv, norm_pow]`. Use `bound_arith r hr m j ‖w‖ ‖h j‖ w.re _ hcs` as an intermediate fact. Rewrite using `[hq]`.

Simplify `this` using `[g, norm_div, norm_pow]`. Establish `hwpos : 0 < ‖w‖ ^ 2` using `pow_pos (norm_pos_iff.2 hw) 2`. Establish `hsum : ∀ T, ∑ j ∈ Finset.range T, ‖g j‖ ^ 2 ≤ w.re * C / ‖w‖ ^ 2`. Introduce `T`. Rewrite using `[le_div_iff₀ hwpos, Finset.sum_mul]`.

Combine the equalities or inequalities in the displayed calculation. Establish `htend` using `tendsto_zero_of_sum_sq_le g _ hsum`. Take `⟨h80, h8r⟩` from `h8 (m + 2) hn0 z`. Establish `hg0 : g 0 = 1`. Simplify `h80` using `[g, h]`.

Establish `hrec : ∀ j : ℕ, 1 ≤ j → ∑ r ∈ Finset.range (j + 1), (-1) ^ r * (∑ S ∈ (Finset.univ : Finset (Fin (m + 2))).powersetCard r, ∏ i ∈ S, (z i : ℂ) / s) * g (j - r) = 0` using `fun j hj => recursion_scaled s hs (fun i => (z i : ℂ)) h j (h8r j hj)`. Establish `hfin` using `h9 (m + 2) (fun i => (z i : ℂ) / s) g hg0 hrec htend i`. Establish `hsq : Real.sqrt (qF F) = r` using `by rw [hq, Real.sqrt_sq hr.le]`. Rewrite using `[hsq]`. Rewrite `hfin` using `[norm_div, div_lt_one hr]`.

Conclude with `hfin`.
-/
theorem l10 : L6 → L7 → L8 → liftZP_newton → ParameterUpperBound := by
  intro h6 h7 h8 h9
  intro F _ _ _ _ _ _ μ _ ψ hψ n V _ _ ρ hsm hn l B hW hU v z hH hg i
  obtain ⟨g₀, hg₀⟩ := hg
  have hlv : l v ≠ 0 := by
    intro h0
    apply hg₀
    rw [h7 F ψ hψ n V ρ v z hH l hW g₀, h0, zero_mul]
  obtain ⟨B', hI, hbd⟩ := h6 F μ ψ hψ n V ρ hsm l B hn hW hU
  obtain ⟨C, hC⟩ := hbd v hH.1
  have hn0 : 0 < n := by omega
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  set s := sqrtQ F with hsdef
  have hs : s ≠ 0 := sqrtQ_ne_zero
  set r := ‖s‖ with hrdef
  have hr : 0 < r := norm_pos_iff.2 hs
  have hq : (qF F : ℝ) = r ^ 2 := by
    rw [hrdef, ← norm_pow, hsdef, sqrtQ_sq, Complex.norm_natCast]
  set w := B' v v with hwdef
  have hw : w ≠ 0 := fun h => hlv (hI.null v h)
  have hW' : Whit ρ ψ (B' v) := fun g hg u => hI.equi g (inU_zero_of_mem hg) u v
  let h : ℕ → ℂ := fun j => evalAt z (schur (Pi.single (⟨0, hn0⟩ : Fin (m + 2)) (j : ℤ)))
  let a : ℕ → GL (Fin (m + 2)) F := fun j => torusPow F (m + 2) (Pi.single ⟨0, hn0⟩ (j : ℤ))
  have hC' : ∀ T : ℕ, ∑ j ∈ Finset.range T, (qF F : ℝ) ^ (j * m) *
      (B' (ρ (a j) v) (ρ (a j) v)).re ≤ C := hC
  have hval : ∀ j, B' v (ρ (a j) v) = w * ((s ^ ((m + 1) * j))⁻¹ * h j) := by
    intro j
    rw [h7 F ψ hψ (m + 2) V ρ v z hH (B' v) hW', sphericalWhittaker_torusPow hψ.1, if_pos (antitone_single hn0 j),
      halfModulus_eq, rhoPair_single_zero]
    congr 2
    rw [_root_.zpow_neg]
    congr 1
    rw [← zpow_natCast]
    congr 1
    push_cast
    ring
  let g : ℕ → ℂ := fun j => h j / s ^ j
  have hterm : ∀ j, ‖w‖ ^ 2 * ‖g j‖ ^ 2 ≤
      w.re * ((qF F : ℝ) ^ (j * m) * (B' (ρ (a j) v) (ρ (a j) v)).re) := by
    intro j
    have hcs := norm_sq_le_of_psd B' hI.herm hI.psd v (ρ (a j) v)
    rw [hval j, norm_mul, norm_mul, norm_inv, norm_pow] at hcs
    have := bound_arith r hr m j ‖w‖ ‖h j‖ w.re _ hcs
    rw [hq]
    simpa [g, norm_div, norm_pow] using this
  have hwpos : 0 < ‖w‖ ^ 2 := pow_pos (norm_pos_iff.2 hw) 2
  have hsum : ∀ T, ∑ j ∈ Finset.range T, ‖g j‖ ^ 2 ≤ w.re * C / ‖w‖ ^ 2 := by
    intro T
    rw [le_div_iff₀ hwpos, Finset.sum_mul]
    calc _ ≤ ∑ j ∈ Finset.range T,
          w.re * ((qF F : ℝ) ^ (j * m) * (B' (ρ (a j) v) (ρ (a j) v)).re) :=
          Finset.sum_le_sum fun j _ => by rw [mul_comm]; exact hterm j
      _ = w.re * ∑ j ∈ Finset.range T,
          (qF F : ℝ) ^ (j * m) * (B' (ρ (a j) v) (ρ (a j) v)).re := by rw [Finset.mul_sum]
      _ ≤ w.re * C := mul_le_mul_of_nonneg_left (hC' T) (hI.psd v)
  have htend := tendsto_zero_of_sum_sq_le g _ hsum
  obtain ⟨h80, h8r⟩ := h8 (m + 2) hn0 z
  have hg0 : g 0 = 1 := by
    simpa [g, h] using h80
  have hrec : ∀ j : ℕ, 1 ≤ j → ∑ r ∈ Finset.range (j + 1), (-1) ^ r *
      (∑ S ∈ (Finset.univ : Finset (Fin (m + 2))).powersetCard r, ∏ i ∈ S, (z i : ℂ) / s) * g (j - r) = 0 :=
    fun j hj => recursion_scaled s hs (fun i => (z i : ℂ)) h j (h8r j hj)
  have hfin := h9 (m + 2) (fun i => (z i : ℂ) / s) g hg0 hrec htend i
  have hsq : Real.sqrt (qF F) = r := by rw [hq, Real.sqrt_sq hr.le]
  rw [hsq]
  rw [norm_div, div_lt_one hr] at hfin
  exact hfin

end GlobalTheory.CompanionTheory.Satake
