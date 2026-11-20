import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinsupp
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerAnEqSiegelUnitOnComplex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisActionSiegelUnitInTower
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasQExpansionSmoothedEisensteinFxWeightOneStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedEisensteinFxCoefficientSeqOneMemSubringStatement

noncomputable section

open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.Sieg GlobalTheory.QFam GlobalTheory.Sieg.DlogOne GlobalTheory.Sieg.Model

namespace GlobalTheory.SiegTwo

/- English proof (translation)
Simplify using `[smF, eisF, const0, coefPos, apply_ite ε, map_ofNat]`.
-/
theorem map_smF {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K'] (ε : K →+* K') (c : ℤ) (j M : ℕ) (ζ : K)
    (a b : ℤ) (n : ℕ) : ε (smF c j M ζ a b n) = smF c j M (ε ζ) a b n := by
  simp [smF, eisF, const0, coefPos, apply_ite ε, map_ofNat]

/- English proof (translation)
Rewrite using `[finsum_eq_sum_of_support_subset (s := θ.support), map_sum]`. Simplify using `[Finsupp.sum, zpow_mul]`. Introduce `k hk`. Assume the negation of the conclusion as `h`. Establish `: θ k = 0` using `by simpa using h`.

Conclude with `hk (by simp [this, hw])`.
-/
theorem map_finsum_zpow {Ω : Type} [Field Ω] (ε : Ω →+* ℂ) (θ : ℤ →₀ ℤ) (w : ℤ → ℤ → ℤ) (hw : ∀ k, w k 0 = 0) (ζ : Ω)
    (g : ℤ) : ε (∑ᶠ k : ℤ, ((w k (θ k) : ℤ) : Ω) * ζ ^ (g * k)) = θ.sum fun k n => ((w k n : ℤ) : ℂ) * (ε ζ ^ g) ^ k := by
  rw [finsum_eq_sum_of_support_subset (s := θ.support), map_sum]
  · simp [Finsupp.sum, zpow_mul]
  · intro k hk
    by_contra h
    have : θ k = 0 := by simpa using h
    exact hk (by simp [this, hw])

/- English proof (translation)
Establish `hd : (0 : ℤ) < (!![(N : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det` using `by simpa [Matrix.det_fin_two] using hN`. Establish `he : ∀ i k, ent (toGQ !![(N : ℤ), 0; 0, 1]) i k = ((!![(N : ℤ), 0; 0, 1] i k : ℤ) : ℚ)` using `fun i k => by`. Simplify using `only [ent, toGQ, dif_pos hd]`. Both sides reduce to the same expression. Establish `h` using `X.exp_upper (toGQ !![(N : ℤ), 0; 0, 1]) (by rw [he]; simp) (siegel X c ![(a.1 : ℚ) / M, (a.2 : ℚ) / M]) r`.

Rewrite `h` using `[he, he, he]`. Establish `h0 : eOm ε 0 = 1` using `ε.injective (by rw [GalUnits.eps_eOm]; simp [ee])`. Simplify `h` using `[h0, sgN]`.
-/
theorem coeff_sgN {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : GlobalTheory.KZ.Tower Ω ε) (c : ℕ) {N : ℕ}
    (hN : 0 < N) (M : ℕ) (a : ℤ × ℤ) (r : ℚ) :
    (X.exp (sgN X c N M a)).coeff (r * N) = (X.exp (siegel X c ![(a.1 : ℚ) / M, (a.2 : ℚ) / M])).coeff r := by
  have hd : (0 : ℤ) < (!![(N : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by simpa [Matrix.det_fin_two] using hN
  have he : ∀ i k, ent (toGQ !![(N : ℤ), 0; 0, 1]) i k = ((!![(N : ℤ), 0; 0, 1] i k : ℤ) : ℚ) := fun i k => by
    simp only [ent, toGQ, dif_pos hd]; rfl
  have h := X.exp_upper (toGQ !![(N : ℤ), 0; 0, 1]) (by rw [he]; simp) (siegel X c ![(a.1 : ℚ) / M, (a.2 : ℚ) / M]) r
  rw [he, he, he] at h
  have h0 : eOm ε 0 = 1 := ε.injective (by rw [GalUnits.eps_eOm]; simp [ee])
  simpa [h0, sgN] using h

/- English proof (translation)
Introduce `Ω _ _ _ ε X _ p hp _ L N c A₁ a₂ g _ hg hNa hN hNp hc hcop hA`. Use `haveI : CharZero Ω := algebraRat.charZero Ω`. Take `⟨g', rfl⟩` from `hNa`. Use `set M := N * p ^ L with hMd`. Establish `hp0 : 0 < p` using `hp.out.pos`.

Establish `hM : 0 < M` using `by positivity`. Establish `hMq : (M : ℚ) = N * p ^ L` using `by rw [hMd]; push_cast; rfl`. Establish `hMc : (M : ℂ) = N * p ^ L` using `by rw [hMd]; push_cast; rfl`. Establish `hNc : (N : ℂ) ≠ 0` using `by exact_mod_cast hN.ne'`. Establish `hpc : (p : ℂ) ≠ 0` using `by exact_mod_cast hp0.ne'`.

Establish `hNq : (N : ℚ) ≠ 0` using `by exact_mod_cast hN.ne'`. Establish `hpq : (p : ℚ) ≠ 0` using `by exact_mod_cast hp0.ne'`. Establish `hc6 : Nat.Coprime c 6` using `(Nat.Coprime.coprime_mul_right_right hcop).coprime_mul_right_right`. Establish `hcM : Nat.Coprime c M` using `Nat.Coprime.mul_right (Nat.Coprime.coprime_mul_right_right hcop).coprime_mul_left_right (hcop.coprime_mul_left_right.pow_right L)`. Establish `hA2 : ¬ (M : ℤ) ∣ A₁ * c` using `fun h => hA ((Nat.isCoprime_iff_coprime.2 hcM.symm).dvd_of_dvd_mul_right h)`.

Establish `hadm : admitted c ![(A₁ : ℚ) / M, ((N * g' : ℤ) : ℚ) / M]`. Use `⟨hc, hc6, fun ⟨⟨m, hm⟩, _⟩ => hA2 ⟨m, ?_⟩⟩` and prove the remaining obligations. Establish `hM' : (M : ℚ) ≠ 0` using `by exact_mod_cast hM.ne'`. Establish `: (A₁ : ℚ) * c = M * m`. Rewrite using `[hm]`.

Simplify using `only [Matrix.cons_val_zero]`. Clear the denominators using the available nonvanishing facts. Conclude with `this` after adjusting the coercions. Establish `ez : ε (zt ε p L) = ee (1 / (p : ℂ) ^ L)` using `by rw [zt, GalUnits.eps_eOm]; push_cast; rfl`. Establish `eM : ε (eOm ε (1 / (M : ℚ))) = ee (1 / (M : ℂ))` using `by rw [GalUnits.eps_eOm]; push_cast; rfl`.

Establish `hz1 : ee (1 / (p : ℂ) ^ L) ^ ((p : ℤ) ^ L) = 1`. Rewrite using `[← ee_int_mul]`. Use `push_cast`. Rewrite using `[mul_one_div_cancel (pow_ne_zero _ hpc)]`. Simplify using `[ee]`.

Establish `hv : ee (((N * g' : ℤ) : ℂ) / M) = ε (zt ε p L) ^ g`. Establish `hco : IsCoprime ((p : ℤ) ^ L) (N : ℤ)` using `(Nat.isCoprime_iff_coprime.2 hNp.symm).pow_left`. Take `⟨u, hu⟩` from `hco.dvd_of_dvd_mul_left (by simpa only [← mul_sub] using hg.dvd : (p : ℤ) ^ L ∣ N * (g - g'))`. Rewrite using `[ez, show g = g' + (p : ℤ) ^ L * u by linarith, zpow_add₀ (ee_ne_zero _), zpow_mul, hz1, one_zpow, mul_one, ← ee_int_mul, hMc]`. Use `congr 1`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Take `⟨k, a, b, qa, qb, hj, i, hi⟩` from `sg_jets hM hadm hA hA2`. Rewrite `hj`, `hi` using `[hv]`. Take `⟨r1, r2⟩` from `exp_of_hasQ X _ _ hM k a (SiegelMem.an_siegel_eq Ω ε X c _ hadm) qa`.

Use `set y := X.exp (sgN X c N M (A₁, N * g')) with hy`. Establish `hco : ∀ r : ℤ, y.coeff ((r : ℚ) / (p : ℚ) ^ L) = (X.exp (siegel X c ![(A₁ : ℚ) / M, ((N * g' : ℤ) : ℚ) / M])).coeff ((r : ℚ) / M)` using `fun r => by`. Rewrite using `[← coeff_sgN X c hN M (A₁, N * g')]`. Use `congr 1`. Rewrite using `[hMq]`.

Clear the denominators using the available nonvanishing facts. Establish `c1 : ∀ n : ℕ, ε (y.coeff (((k + n : ℤ) : ℚ) / (p : ℚ) ^ L)) = a n` using `fun n => by`. Rewrite using `[hco, ← r1]`. Use `push_cast`. Both sides reduce to the same expression.

Establish `c0 : ∀ r : ℤ, r < k → y.coeff ((r : ℚ) / (p : ℚ) ^ L) = 0` using `fun r hr => by`. Rewrite using `[hco]`. Use `r2 _ fun n h => ?_` and prove the remaining obligations. Rewrite `h` using `[div_left_inj' (by exact_mod_cast hM.ne')]`. Establish `: r = k + n` using `by exact_mod_cast h`.

Use linear arithmetic over natural numbers and integers. Establish `hb` using `HasQ.coeff_unique hM qb (by`. Simplify `((GlobalTheory.T.hasQExpansion_smoothedEisensteinFx_weightOne c M A₁ (N * g') hM).mul_conv qa).const_mul (-1))` using `only [neg_mul, one_mul]`. Use `choose θ t1 t2 t3 using fun n => exists_finsupp (hj n)`. Establish `cases : ∀ r : ℤ, r < k ∨ ∃ n : ℕ, r = k + n` using `fun r => by`.

Break down `lt_or_ge r k with h | h` into its components or cases. Conclude with `Or.inl h`. Conclude with `Or.inr ⟨(r - k).toNat, by omega⟩`. Use `set Θ : ℤ → ℤ → ℤ := fun l r => if r < k then 0 else θ (r - k).toNat l with hΘ`. Establish `T0 : ∀ l r, r < k → Θ l r = 0` using `fun l r h => if_pos h`.

Establish `T1 : ∀ l (n : ℕ), Θ l (k + n) = θ n l` using `fun l n => by`. Simplify using `only [hΘ]`. Rewrite using `[if_neg (by omega), add_sub_cancel_left, Int.toNat_natCast]`. Use `⟨Θ, fun r => ?_, ⟨k, T0⟩, fun l r h => ?_, fun r => ?_, fun r => ?_, ?_, k, g * i, ?_⟩` and prove the remaining obligations. Break down `cases r with h | ⟨n, rfl⟩` into its components or cases.

Conclude with `⟨0, fun l _ => T0 l r h⟩`. Use `⟨(θ n).support.sup Int.natAbs, fun l hl => ?_⟩` and prove the remaining obligations. Rewrite using `[T1]`. Assume the negation of the conclusion as `h`. Use `Finset.le_sup (f := Int.natAbs) (Finsupp.mem_support_iff.2 h)` as an intermediate fact.

Rewrite `hl` using `[Int.abs_eq_natAbs]`. Use linear arithmetic over natural numbers and integers. Break down `cases r with h' | ⟨n, rfl⟩` into its components or cases. Conclude with `absurd (T0 l r h') h`. Rewrite `h` using `[T1]`.

Use `Dvd.dvd.trans ⟨N, ?_⟩ (t1 n l h)` and prove the remaining obligations. Rewrite using `[hMd]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Break down `cases r with h' | ⟨n, rfl⟩` into its components or cases.

Simplify using `[c0 r h', T0 _ r h']`. Simplify using `only [T1]`. Apply `ε.injective` to reduce the goal to its premises. Rewrite using `[c1, map_finsum_zpow ε (θ n) (fun _ m => m) (fun _ => rfl)]`. Conclude with `t2 n`.

Break down `cases r with h' | ⟨n, rfl⟩` into its components or cases. Simplify using `only [T0 _ r h', mul_zero, Int.cast_zero, zero_mul, finsum_zero]`. Rewrite using `[finsum_eq_zero_of_forall_eq_zero, neg_zero]`. Introduce `l`. Use `split_ifs with h`.

Rewrite using `[c0 _ (by omega), mul_zero]`. Rewrite using `[zero_mul]`. Simplify using `only [T1]`. Apply `ε.injective` to reduce the goal to its premises. Rewrite using `[map_finsum_zpow ε (θ n) (fun l m => l * m) (fun _ => mul_zero _), ← t3 n, finsum_eq_sum_of_support_subset (s := (Finset.range (n + 1)).image (Nat.cast : ℕ → ℤ)), Finset.sum_image (fun _ _ _ _ h => by exact_mod_cast h), hb, map_neg, map_sum]`.

Simplify using `only [conv, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, neg_inj]`. Use `Finset.sum_congr rfl fun l hl => ?_` and prove the remaining obligations. Use `Finset.mem_range.1 hl` as an intermediate fact. Rewrite using `[map_mul, if_pos (by omega), Int.toNat_natCast, map_smF, eM, ← c1, show k + n - l = k + ((n - l : ℕ) : ℤ) by omega]`. Introduce `l hl`.

Assume the negation of the conclusion as `h`. Apply `hl` to reduce the goal to its premises. Simplify using `only`. Use `split_ifs with h1`. Rewrite using `[c0, mul_zero]`.

Assume the negation of the conclusion as `h2`. Conclude with `h (Finset.mem_coe.2 (Finset.mem_image.2 ⟨l.toNat, Finset.mem_range.2 (by omega), by omega⟩))`. Rewrite using `[zero_mul]`. Establish `hz : eOm ε (1 / (M : ℚ)) ^ (N * g') = zt ε p L ^ g` using `ε.injective (by`. Rewrite using `[map_zpow₀, map_zpow₀, ← hv, eM, ← ee_int_mul, mul_one_div])`.

Establish `m0 : zt ε p L ∈ Subring.closure {zt ε p L}` using `Subring.subset_closure rfl`. Establish `m1 : (zt ε p L)⁻¹ ∈ Subring.closure {zt ε p L}`. Establish `h1 : zt ε p L ^ (p ^ L) = 1` using `ε.injective (by`. Rewrite using `[map_pow, ez, map_one, ← zpow_natCast]`. Use `push_cast`.

Conclude with `hz1)`. Establish `: (zt ε p L)⁻¹ = zt ε p L ^ (p ^ L - 1)`. Apply `inv_eq_of_mul_eq_one_left` to reduce the goal to its premises. Rewrite using `[← pow_succ, Nat.sub_add_cancel (pow_pos hp0 L), h1]`. Rewrite using `[this]`.

Conclude with `pow_mem m0 _`. Establish `m2 : ∀ m : ℤ, zt ε p L ^ m ∈ Subring.closure {zt ε p L}` using `fun m => by`. Break down `Int.eq_nat_or_neg m with ⟨m, rfl | rfl⟩` into its components or cases. Rewrite using `[zpow_natCast]`. Conclude with `pow_mem m0 _`.

Rewrite using `[zpow_neg, zpow_natCast, ← inv_pow]`. Conclude with `pow_mem m1 _`. Use `GlobalTheory.T.smoothedEisensteinFxCoefficientSeq_one_mem_subring Ω _ c M _ A₁ _ hM hcM hA (by rw [hz]; exact m2 _) ?_` and prove the remaining obligations. Rewrite using `[zpow_neg, hz, ← zpow_neg]`. Conclude with `m2 _`.

Use `c1 0` as an intermediate fact. Rewrite `this` using `[Nat.cast_zero, add_zero]`. Use `hi.imp (fun h => ε.injective ?_) (fun h => ε.injective ?_)` and prove the remaining obligations. Rewrite using `[this, h, map_zpow₀, zpow_mul]`. Rewrite using `[this, h, map_neg, map_zpow₀, zpow_mul]`.
-/
theorem sgN_two_variable : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (L N c : ℕ) (A₁ a₂ g : ℤ), 1 ≤ L → a₂ ≡ N * g [ZMOD (p : ℤ) ^ L] → (N : ℤ) ∣ a₂ → 0 < N → Nat.Coprime N p → 1 < c → Nat.Coprime c (6 * N * p) → ¬ (((N * p ^ L : ℕ) : ℤ) ∣ A₁) →
  ∃ θ : ℤ → ℤ → ℤ,
    (∀ r : ℤ, ∃ B : ℕ, ∀ k : ℤ, (B : ℤ) < |k| → θ k r = 0) ∧
    (∃ r0 : ℤ, ∀ k r : ℤ, r < r0 → θ k r = 0) ∧
    (∀ k r : ℤ, θ k r ≠ 0 → (p : ℤ) ^ L ∣ r - A₁ * k) ∧
    (∀ r : ℤ, (X.exp (sgN X c N (N * p ^ L) (A₁, a₂))).coeff ((r : ℚ) / (p : ℚ) ^ L) = ∑ᶠ k : ℤ, (θ k r : Ω) * zt ε p L ^ (g * k)) ∧
    (∀ r : ℤ, ∑ᶠ k : ℤ, ((k * θ k r : ℤ) : Ω) * zt ε p L ^ (g * k) =
      -∑ᶠ i : ℤ, (if 0 ≤ i then smF c 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) A₁ a₂ i.toNat else 0) *
        (X.exp (sgN X c N (N * p ^ L) (A₁, a₂))).coeff (((r - i : ℤ) : ℚ) / (p : ℚ) ^ L)) ∧
    (∀ n : ℕ, smF c 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) A₁ a₂ n ∈ Subring.closure {zt ε p L}) ∧
    (∃ r m : ℤ, (X.exp (sgN X c N (N * p ^ L) (A₁, a₂))).coeff ((r : ℚ) / (p : ℚ) ^ L) = zt ε p L ^ m ∨
      (X.exp (sgN X c N (N * p ^ L) (A₁, a₂))).coeff ((r : ℚ) / (p : ℚ) ^ L) = -(zt ε p L ^ m)) := by
  intro Ω _ _ _ ε X _ p hp _ L N c A₁ a₂ g _ hg hNa hN hNp hc hcop hA
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨g', rfl⟩ := hNa
  set M := N * p ^ L with hMd
  have hp0 : 0 < p := hp.out.pos
  have hM : 0 < M := by positivity
  have hMq : (M : ℚ) = N * p ^ L := by rw [hMd]; push_cast; rfl
  have hMc : (M : ℂ) = N * p ^ L := by rw [hMd]; push_cast; rfl
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hc6 : Nat.Coprime c 6 := (Nat.Coprime.coprime_mul_right_right hcop).coprime_mul_right_right
  have hcM : Nat.Coprime c M := Nat.Coprime.mul_right (Nat.Coprime.coprime_mul_right_right hcop).coprime_mul_left_right
    (hcop.coprime_mul_left_right.pow_right L)
  have hA2 : ¬ (M : ℤ) ∣ A₁ * c := fun h =>
    hA ((Nat.isCoprime_iff_coprime.2 hcM.symm).dvd_of_dvd_mul_right h)
  have hadm : admitted c ![(A₁ : ℚ) / M, ((N * g' : ℤ) : ℚ) / M] := by
    refine ⟨hc, hc6, fun ⟨⟨m, hm⟩, _⟩ => hA2 ⟨m, ?_⟩⟩
    have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
    have : (A₁ : ℚ) * c = M * m := by
      rw [hm]; simp only [Matrix.cons_val_zero]; field_simp
    exact_mod_cast this
  have ez : ε (zt ε p L) = ee (1 / (p : ℂ) ^ L) := by rw [zt, GalUnits.eps_eOm]; push_cast; rfl
  have eM : ε (eOm ε (1 / (M : ℚ))) = ee (1 / (M : ℂ)) := by rw [GalUnits.eps_eOm]; push_cast; rfl
  have hz1 : ee (1 / (p : ℂ) ^ L) ^ ((p : ℤ) ^ L) = 1 := by
    rw [← ee_int_mul]; push_cast; rw [mul_one_div_cancel (pow_ne_zero _ hpc)]; simp [ee]
  have hv : ee (((N * g' : ℤ) : ℂ) / M) = ε (zt ε p L) ^ g := by
    have hco : IsCoprime ((p : ℤ) ^ L) (N : ℤ) := (Nat.isCoprime_iff_coprime.2 hNp.symm).pow_left
    obtain ⟨u, hu⟩ := hco.dvd_of_dvd_mul_left (by simpa only [← mul_sub] using hg.dvd : (p : ℤ) ^ L ∣ N * (g - g'))
    rw [ez, show g = g' + (p : ℤ) ^ L * u by linarith, zpow_add₀ (ee_ne_zero _), zpow_mul, hz1, one_zpow, mul_one,
      ← ee_int_mul, hMc]
    congr 1
    push_cast
    field_simp
  obtain ⟨k, a, b, qa, qb, hj, i, hi⟩ := sg_jets hM hadm hA hA2
  rw [hv] at hj hi
  obtain ⟨r1, r2⟩ := exp_of_hasQ X _ _ hM k a (SiegelMem.an_siegel_eq Ω ε X c _ hadm) qa
  set y := X.exp (sgN X c N M (A₁, N * g')) with hy
  have hco : ∀ r : ℤ, y.coeff ((r : ℚ) / (p : ℚ) ^ L) =
      (X.exp (siegel X c ![(A₁ : ℚ) / M, ((N * g' : ℤ) : ℚ) / M])).coeff ((r : ℚ) / M) := fun r => by
    rw [← coeff_sgN X c hN M (A₁, N * g')]
    congr 1
    rw [hMq]; field_simp
  have c1 : ∀ n : ℕ, ε (y.coeff (((k + n : ℤ) : ℚ) / (p : ℚ) ^ L)) = a n := fun n => by
    rw [hco, ← r1]; push_cast; rfl
  have c0 : ∀ r : ℤ, r < k → y.coeff ((r : ℚ) / (p : ℚ) ^ L) = 0 := fun r hr => by
    rw [hco]
    refine r2 _ fun n h => ?_
    rw [div_left_inj' (by exact_mod_cast hM.ne')] at h
    have : r = k + n := by exact_mod_cast h
    omega
  have hb := HasQ.coeff_unique hM qb (by
    simpa only [neg_mul, one_mul] using ((GlobalTheory.T.hasQExpansion_smoothedEisensteinFx_weightOne c M A₁ (N * g') hM).mul_conv qa).const_mul (-1))
  choose θ t1 t2 t3 using fun n => exists_finsupp (hj n)
  have cases : ∀ r : ℤ, r < k ∨ ∃ n : ℕ, r = k + n := fun r => by
    rcases lt_or_ge r k with h | h
    · exact Or.inl h
    · exact Or.inr ⟨(r - k).toNat, by omega⟩
  set Θ : ℤ → ℤ → ℤ := fun l r => if r < k then 0 else θ (r - k).toNat l with hΘ
  have T0 : ∀ l r, r < k → Θ l r = 0 := fun l r h => if_pos h
  have T1 : ∀ l (n : ℕ), Θ l (k + n) = θ n l := fun l n => by
    simp only [hΘ]
    rw [if_neg (by omega), add_sub_cancel_left, Int.toNat_natCast]
  refine ⟨Θ, fun r => ?_, ⟨k, T0⟩, fun l r h => ?_, fun r => ?_, fun r => ?_, ?_, k, g * i, ?_⟩
  · rcases cases r with h | ⟨n, rfl⟩
    · exact ⟨0, fun l _ => T0 l r h⟩
    · refine ⟨(θ n).support.sup Int.natAbs, fun l hl => ?_⟩
      rw [T1]
      by_contra h
      have := Finset.le_sup (f := Int.natAbs) (Finsupp.mem_support_iff.2 h)
      rw [Int.abs_eq_natAbs] at hl
      omega
  · rcases cases r with h' | ⟨n, rfl⟩
    · exact absurd (T0 l r h') h
    · rw [T1] at h
      refine Dvd.dvd.trans ⟨N, ?_⟩ (t1 n l h)
      rw [hMd]; push_cast; ring
  · rcases cases r with h' | ⟨n, rfl⟩
    · simp [c0 r h', T0 _ r h']
    · simp only [T1]
      apply ε.injective
      rw [c1, map_finsum_zpow ε (θ n) (fun _ m => m) (fun _ => rfl)]
      exact t2 n
  · rcases cases r with h' | ⟨n, rfl⟩
    · simp only [T0 _ r h', mul_zero, Int.cast_zero, zero_mul, finsum_zero]
      rw [finsum_eq_zero_of_forall_eq_zero, neg_zero]
      intro l
      split_ifs with h
      · rw [c0 _ (by omega), mul_zero]
      · rw [zero_mul]
    · simp only [T1]
      apply ε.injective
      rw [map_finsum_zpow ε (θ n) (fun l m => l * m) (fun _ => mul_zero _), ← t3 n,
        finsum_eq_sum_of_support_subset (s := (Finset.range (n + 1)).image (Nat.cast : ℕ → ℤ)),
        Finset.sum_image (fun _ _ _ _ h => by exact_mod_cast h), hb, map_neg, map_sum]
      · simp only [conv, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, neg_inj]
        refine Finset.sum_congr rfl fun l hl => ?_
        have := Finset.mem_range.1 hl
        rw [map_mul, if_pos (by omega), Int.toNat_natCast, map_smF, eM, ← c1,
          show k + n - l = k + ((n - l : ℕ) : ℤ) by omega]
      · intro l hl
        by_contra h
        apply hl
        dsimp only
        split_ifs with h1
        · rw [c0, mul_zero]
          by_contra h2
          exact h (Finset.mem_coe.2 (Finset.mem_image.2 ⟨l.toNat, Finset.mem_range.2 (by omega), by omega⟩))
        · rw [zero_mul]
  · have hz : eOm ε (1 / (M : ℚ)) ^ (N * g') = zt ε p L ^ g := ε.injective (by
      rw [map_zpow₀, map_zpow₀, ← hv, eM, ← ee_int_mul, mul_one_div])
    have m0 : zt ε p L ∈ Subring.closure {zt ε p L} := Subring.subset_closure rfl
    have m1 : (zt ε p L)⁻¹ ∈ Subring.closure {zt ε p L} := by
      have h1 : zt ε p L ^ (p ^ L) = 1 := ε.injective (by
        rw [map_pow, ez, map_one, ← zpow_natCast]; push_cast; exact hz1)
      have : (zt ε p L)⁻¹ = zt ε p L ^ (p ^ L - 1) := by
        apply inv_eq_of_mul_eq_one_left
        rw [← pow_succ, Nat.sub_add_cancel (pow_pos hp0 L), h1]
      rw [this]
      exact pow_mem m0 _
    have m2 : ∀ m : ℤ, zt ε p L ^ m ∈ Subring.closure {zt ε p L} := fun m => by
      rcases Int.eq_nat_or_neg m with ⟨m, rfl | rfl⟩
      · rw [zpow_natCast]; exact pow_mem m0 _
      · rw [zpow_neg, zpow_natCast, ← inv_pow]; exact pow_mem m1 _
    refine GlobalTheory.T.smoothedEisensteinFxCoefficientSeq_one_mem_subring Ω _ c M _ A₁ _ hM hcM hA (by rw [hz]; exact m2 _) ?_
    rw [zpow_neg, hz, ← zpow_neg]
    exact m2 _
  · have := c1 0
    rw [Nat.cast_zero, add_zero] at this
    refine hi.imp (fun h => ε.injective ?_) (fun h => ε.injective ?_)
    · rw [this, h, map_zpow₀, zpow_mul]
    · rw [this, h, map_neg, map_zpow₀, zpow_mul]

end GlobalTheory.SiegTwo
