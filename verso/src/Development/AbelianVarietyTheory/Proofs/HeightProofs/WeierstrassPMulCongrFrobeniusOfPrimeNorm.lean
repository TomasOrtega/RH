import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeierstrassPComplexMultiplicationCongruenceModPr
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TorsionIntegralDistinctOfPosStatement
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.EisensteinCongruence

/- English proof (translation)
Introduce `L W α p h2 h3 hg₂ hg₃ hΔ hp hpW hαW hα hN`. Establish `hΔ0 : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ≠ 0` using `TorsionIntegral.disc L`. Establish `h0 : α ≠ 0`. Introduce and unpack `rfl`. Simplify using `only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hN`.

Conclude with `hp.ne_zero (by exact_mod_cast hN.symm)`. Use `haveI : Fact p.Prime := ⟨hp⟩`. Use `set ρ := IsLocalRing.residue W with hρ`. Establish `hpk : (p : IsLocalRing.ResidueField W) = 0`. Rewrite using `[← map_natCast ρ, residue_eq_zero_iff']`.

Simplify using `using hpW`. Use `haveI : CharP (IsLocalRing.ResidueField W) p := (CharP.charP_iff_prime_eq_zero hp).mpr hpk`. Establish `hcop : ∀ m : ℕ, 0 < m → (m : ℂ)⁻¹ ∈ W → p.Coprime m`. Introduce `m hm hmW`. Rewrite using `[hp.coprime_iff_not_dvd, ← CharP.cast_eq_zero_iff (IsLocalRing.ResidueField W) p, ← map_natCast ρ]`.

Apply `residue_ne_zero_of_inv_mem` to reduce the goal to its premises. Simplify using `using hm.ne'`. Simplify using `using hmW`. Take `⟨A, D, hD, hAd, hDd, hev, hode⟩` from `exists_weierstrassP_mul_ode L α p h0 hα hN`. Take `⟨c, A₀, D₀, hc, hA₀, hD₀, hne⟩` from `exists_scaling W A D hD`.

Establish `hmul : ∀ (m : ℕ) (t : ℂ), (m : ℂ) * t ∈ L.lattice → (m : ℂ) * (α * t) ∈ L.lattice`. Introduce `m t h`. Use `hα _ h` as an intermediate fact. Rewrite `this` using `[mul_left_comm]`. Then use the resulting hypothesis. Establish `rel : ∀ (m : ℕ) (t : ℂ), 0 < m → (m : ℂ)⁻¹ ∈ W → (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → ∃ x y : W, (x : ℂ) = L.weierstrassP t ∧ (y : ℂ) = L.weierstrassP (α * t) ∧ (A₀.map ρ).eval (ρ x) = ρ y * (D₀.map ρ).eval (ρ x)`.

Introduce `m t hm hmW hmt ht`. Establish `hαt : α * t ∉ L.lattice` using `fun h => ht (mem_of_mul_mem L h0 hα hN (hcop m hm hmW) hmt h)`. Establish `T` using `(GlobalTheory.T.weierstrassP_torsion_mem_and_distinct_mod_nonunits L W m h2 h3 hg₂ hg₃ hΔ hm hmW).1`. Use `⟨⟨_, T t hmt ht⟩, ⟨_, T _ (hmul m t hmt) hαt⟩, rfl, rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[eval_map_apply, eval_map_apply, ← map_mul]`.

Use `congr 1`. Apply `W.subtype_injective` to reduce the goal to its premises. Rewrite using `[map_mul, ← eval_map_apply, ← eval_map_apply, hA₀, hD₀]`. Take `⟨e1, e2⟩` from `hev t hαt`. Simplify using `only [eval_mul, eval_C, ValuationSubring.coe_subtype]`.

Rewrite using `[e2]`. Clear the denominators using the available nonvanishing facts. Establish `h3n : ∀ n : ℕ, ((3 ^ n : ℕ) : ℂ)⁻¹ ∈ W` using `fun n => by`. Rewrite using `[Nat.cast_pow, ← inv_pow]`. Conclude with `pow_mem (by simpa using h3) n`.

Establish `hpos : ∀ n : ℕ, 0 < 3 ^ n` using `fun n => by positivity`. Establish `hpow : ∀ i j : ℕ, i + 1 ≤ j → ((3 ^ j : ℕ) : ℂ) * (L.ω₁ / 3 ^ (i + 1)) ∈ L.lattice`. Introduce `i j hij`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hij`. Use `L.lattice.smul_mem ((3 : ℤ) ^ d) L.ω₁_mem_lattice using 1` and compare the differences between its conclusion and the goal.

Simplify using `only [zsmul_eq_mul]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hthird : ∀ j : ℕ, ((3 ^ j : ℕ) : ℂ) * (L.ω₁ / 3 ^ (j + 1)) = L.ω₁ / 3`.

Introduce `j`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hns : ∀ (n : ℕ) (z : ℂ), z ∈ L.lattice → (n : ℂ) * z ∈ L.lattice` using `fun n z hz => by`.

Simplify using `using L.lattice.smul_mem (n : ℤ) hz`. Establish `hnot : ∀ j : ℕ, L.ω₁ / 3 ^ (j + 1) ∉ L.lattice` using `fun j h => third_notMem L (hthird j ▸ hns _ _ h)`. Establish `h33 : ((3 : ℕ) : ℂ) * (L.ω₁ / 3) ∈ L.lattice` using `by simpa using hpow 0 1 le_rfl`. Establish `hαthird : α * (L.ω₁ / 3) ∉ L.lattice` using `fun h => third_notMem L (mem_of_mul_mem L h0 hα hN (hcop 3 (by decide) (by simpa using h3)) h33 h)`. Establish `dist : ∀ β : ℂ, (∀ l ∈ L.lattice, β * l ∈ L.lattice) → β * (L.ω₁ / 3) ∉ L.lattice → ∀ x : ℕ → W, (∀ j, (x j : ℂ) = L.weierstrassP (β * (L.ω₁ / 3 ^ (j + 1)))) → Function.Injective fun j => ρ (x j)`.

Introduce `β hβ hβ3 x hx`. Establish `hm : ∀ i j : ℕ, i + 1 ≤ j → ((3 ^ j : ℕ) : ℂ) * (β * (L.ω₁ / 3 ^ (i + 1))) ∈ L.lattice`. Introduce `i j hij`. Rewrite using `[mul_left_comm]`. Conclude with `hβ _ (hpow i j hij)`.

Establish `hn : ∀ j : ℕ, ((3 ^ j : ℕ) : ℂ) * (β * (L.ω₁ / 3 ^ (j + 1))) ∉ L.lattice`. Introduce `j`. Rewrite using `[mul_left_comm, hthird]`. Conclude with `hβ3`. Use `Function.Injective.of_lt_imp_ne fun i j hij h => ?_` and prove the remaining obligations.

Establish `T` using `(GlobalTheory.T.weierstrassP_torsion_mem_and_distinct_mod_nonunits L W (3 ^ (j + 1)) h2 h3 hg₂ hg₃ hΔ (hpos _) (h3n _)).2 _ _ (hm i _ (by omega)) (fun h => hn i (hns _ _ h)) (hm j _ le_rfl) (fun h => hn j (hns _ _ h)) (by`. Rewrite using `[← hx, ← hx]`. Establish `: ρ (x i - x j) = 0` using `by rw [map_sub]; exact sub_eq_zero.mpr h`. Conclude with `(residue_eq_zero_iff' W _).mp this)`. Apply `hn j` to reduce the goal to its premises.

Break down `T with T | T` into its components or cases. Use `L.lattice.sub_mem (hm i j hij) (hns (3 ^ j) _ T) using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Use `L.lattice.sub_mem (hns (3 ^ j) _ T) (hm i j hij) using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.

Use `choose x y hx hy hxy using fun j : ℕ => rel (3 ^ (j + 1)) (L.ω₁ / 3 ^ (j + 1)) (hpos _) (h3n _) (hpow j _ le_rfl) (hnot j)`. Establish `hxi` using `dist 1 (by simp) (by simpa using third_notMem L) x (by simpa using hx)`. Establish `hyi` using `dist α hα hαthird y hy`. Set `g₂ : W` to `⟨L.g₂, hg₂⟩`. Set `g₃ : W` to `⟨L.g₃, hg₃⟩`.

Set `α₀ : W` to `⟨α, W.nonunits_subset hαW⟩`. Establish `hode' : C (α ^ 2) * (C c * D) * (4 * (C c * A) ^ 3 - C L.g₂ * (C c * A) * (C c * D) ^ 2 - C L.g₃ * (C c * D) ^ 3) = (derivative (C c * A) * (C c * D) - (C c * A) * derivative (C c * D)) ^ 2 * (4 * X ^ 3 - C L.g₂ * X - C L.g₃)`. Simplify using `only [derivative_C_mul]`. Take the linear combination `C c ^ 4 * hode`. Establish `hode₀ : C (α₀ ^ 2) * D₀ * (4 * A₀ ^ 3 - C g₂ * A₀ * D₀ ^ 2 - C g₃ * D₀ ^ 3) = (derivative A₀ * D₀ - A₀ * derivative D₀) ^ 2 * (4 * X ^ 3 - C g₂ * X - C g₃)`.

Apply `Polynomial.map_injective W.subtype W.subtype_injective` to reduce the goal to its premises. Simplify using `only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, map_C, map_X, Polynomial.map_ofNat, ← derivative_map, hA₀, hD₀]`. Conclude with `hode'`. Establish `hdvd₀ : (4 * X ^ 3 - C g₂ * X - C g₃ : W[X]) ∣ D₀ * (4 * A₀ ^ 3 - C g₂ * A₀ * D₀ ^ 2 - C g₃ * D₀ ^ 3)`. Apply `cubic_dvd W h2` to reduce the goal to its premises.

Simplify using `only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, map_C, Polynomial.map_ofNat, hA₀, hD₀]`. Establish `hu : IsUnit (C (α ^ 2) : ℂ[X])` using `isUnit_C.mpr (Ne.isUnit (pow_ne_zero _ h0))`. Rewrite using `[← hu.dvd_mul_left, ← mul_assoc]`. Conclude with `Dvd.intro_left _ hode'.symm`. Establish `hdeg : ∀ (B₀ : W[X]) (B : ℂ[X]), B₀.map W.subtype = C c * B → (B₀.map ρ).natDegree ≤ B.natDegree`.

Introduce `B₀ B h`. Use `natDegree_map_le.trans ?_` and prove the remaining obligations. Rewrite using `[← natDegree_map_eq_of_injective W.subtype_injective, h, natDegree_C_mul hc]`. Establish `hα₀ : ρ α₀ = 0` using `(residue_eq_zero_iff' W _).mpr hαW`. Take `⟨a, d, ha, hd, eD, eA, e2, e3⟩` from `residue_form p (ρ g₂) (ρ g₃) (A₀.map ρ) (D₀.map ρ) (by`.

Rewrite using `[← map_ofNat ρ 2]`. Conclude with `residue_ne_zero_of_inv_mem W _ (two_ne_zero (α := ℂ)) h2)`. Use the proof step `(by`. Rewrite using `[← map_ofNat ρ 3]`. Conclude with `residue_ne_zero_of_inv_mem W _ (three_ne_zero (α := ℂ)) h3)`.

Use the proof step `(by`. Use `residue_ne_zero_of_inv_mem W (g₂ ^ 3 - 27 * g₃ ^ 2) hΔ0 hΔ` as an intermediate fact. Simplify `this)` using `[map_ofNat]`. Use `hne (hAd ▸ hdeg A₀ A hA₀) (lt_of_le_of_lt (hdeg D₀ D hD₀) (by omega))`. Use `_ _ hxi hyi hxy`.

Use the proof step `(by`. Use `congrArg (Polynomial.map ρ) hode₀` as an intermediate fact. Simplify using `only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, map_C, map_X, Polynomial.map_ofNat, ← derivative_map, map_pow, hα₀, map_zero] at this`. Rewrite using `[← this]`. Use the proof step `ring)`.

Use the proof step `(by`. Use `Polynomial.map_dvd ρ hdvd₀` as an intermediate fact. Simplify `this)` using `only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, map_C, map_X, Polynomial.map_ofNat]`. Take `⟨a₀, rfl⟩` from `IsLocalRing.residue_surjective a`. Establish `ha' : (a₀ : ℂ) ∉ W.nonunits` using `fun h => ha ((residue_eq_zero_iff' W _).mpr h)`.

Rewrite `ha'` using `[W.mem_nonunits_iff_or]`. Use `push Not at ha'`. Use `⟨a₀, a₀.2, ha'.2, ha'.1, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `(residue_eq_zero_iff' W (g₂ - a₀ ^ 2 * g₂ ^ p)).mp ?_` and prove the remaining obligations. Rewrite using `[map_sub, map_mul, map_pow, map_pow]`.

Conclude with `sub_eq_zero.mpr e2`. Use `(residue_eq_zero_iff' W (g₃ - a₀ ^ 3 * g₃ ^ p)).mp ?_` and prove the remaining obligations. Rewrite using `[map_sub, map_mul, map_pow, map_pow]`. Conclude with `sub_eq_zero.mpr e3`. Introduce `m t hm hmW hmt ht`.

Take `⟨u, v, hu, hv, huv⟩` from `rel m t hm hmW hmt ht`. Rewrite using `[← hu, ← hv]`. Use `(residue_eq_zero_iff' W (v - a₀ * u ^ p)).mp ?_` and prove the remaining obligations. Rewrite using `[map_sub, map_mul, map_pow]`. Rewrite `huv` using `[eA, eD]`.

Simplify using `only [eval_mul, eval_C, eval_pow, eval_X] at huv`. Apply `mul_left_cancel₀ hd` to reduce the goal to its premises. Take the linear combination `-huv`.
-/
theorem weierstrassP_mul_congr_pow_of_pos : ∀ (L : PeriodPair) (W : ValuationSubring ℂ) (α : ℂ) (p : ℕ), (2 : ℂ)⁻¹ ∈ W → (3 : ℂ)⁻¹ ∈ W → L.g₂ ∈ W → L.g₃ ∈ W → (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)⁻¹ ∈ W → p.Prime → (p : ℂ) ∈ W.nonunits → α ∈ W.nonunits → (∀ l ∈ L.lattice, α * l ∈ L.lattice) → ‖α‖ ^ 2 = p → ∃ a : ℂ, a ∈ W ∧ a⁻¹ ∈ W ∧ a ≠ 0 ∧ L.g₂ - a ^ 2 * L.g₂ ^ p ∈ W.nonunits ∧ L.g₃ - a ^ 3 * L.g₃ ^ p ∈ W.nonunits ∧ ∀ (m : ℕ) (t : ℂ), 0 < m → (m : ℂ)⁻¹ ∈ W → (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → L.weierstrassP (α * t) - a * L.weierstrassP t ^ p ∈ W.nonunits := by
  intro L W α p h2 h3 hg₂ hg₃ hΔ hp hpW hαW hα hN
  have hΔ0 : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ≠ 0 := TorsionIntegral.disc L
  have h0 : α ≠ 0 := by
    rintro rfl
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hN
    exact hp.ne_zero (by exact_mod_cast hN.symm)
  haveI : Fact p.Prime := ⟨hp⟩
  set ρ := IsLocalRing.residue W with hρ
  have hpk : (p : IsLocalRing.ResidueField W) = 0 := by
    rw [← map_natCast ρ, residue_eq_zero_iff']
    simpa using hpW
  haveI : CharP (IsLocalRing.ResidueField W) p := (CharP.charP_iff_prime_eq_zero hp).mpr hpk
  have hcop : ∀ m : ℕ, 0 < m → (m : ℂ)⁻¹ ∈ W → p.Coprime m := by
    intro m hm hmW
    rw [hp.coprime_iff_not_dvd, ← CharP.cast_eq_zero_iff (IsLocalRing.ResidueField W) p,
      ← map_natCast ρ]
    apply residue_ne_zero_of_inv_mem
    · simpa using hm.ne'
    · simpa using hmW
  obtain ⟨A, D, hD, hAd, hDd, hev, hode⟩ := exists_weierstrassP_mul_ode L α p h0 hα hN
  obtain ⟨c, A₀, D₀, hc, hA₀, hD₀, hne⟩ := exists_scaling W A D hD
  have hmul : ∀ (m : ℕ) (t : ℂ), (m : ℂ) * t ∈ L.lattice → (m : ℂ) * (α * t) ∈ L.lattice := by
    intro m t h
    have := hα _ h
    rwa [mul_left_comm] at this

  have rel : ∀ (m : ℕ) (t : ℂ), 0 < m → (m : ℂ)⁻¹ ∈ W → (m : ℂ) * t ∈ L.lattice →
      t ∉ L.lattice → ∃ x y : W, (x : ℂ) = L.weierstrassP t ∧ (y : ℂ) = L.weierstrassP (α * t) ∧
        (A₀.map ρ).eval (ρ x) = ρ y * (D₀.map ρ).eval (ρ x) := by
    intro m t hm hmW hmt ht
    have hαt : α * t ∉ L.lattice := fun h => ht (mem_of_mul_mem L h0 hα hN (hcop m hm hmW) hmt h)
    have T := (GlobalTheory.T.weierstrassP_torsion_mem_and_distinct_mod_nonunits L W m h2 h3 hg₂ hg₃ hΔ hm hmW).1
    refine ⟨⟨_, T t hmt ht⟩, ⟨_, T _ (hmul m t hmt) hαt⟩, rfl, rfl, ?_⟩
    rw [eval_map_apply, eval_map_apply, ← map_mul]
    congr 1
    apply W.subtype_injective
    rw [map_mul, ← eval_map_apply, ← eval_map_apply, hA₀, hD₀]
    obtain ⟨e1, e2⟩ := hev t hαt
    simp only [eval_mul, eval_C, ValuationSubring.coe_subtype]
    rw [e2]
    field_simp
  have h3n : ∀ n : ℕ, ((3 ^ n : ℕ) : ℂ)⁻¹ ∈ W := fun n => by
    rw [Nat.cast_pow, ← inv_pow]
    exact pow_mem (by simpa using h3) n
  have hpos : ∀ n : ℕ, 0 < 3 ^ n := fun n => by positivity
  have hpow : ∀ i j : ℕ, i + 1 ≤ j → ((3 ^ j : ℕ) : ℂ) * (L.ω₁ / 3 ^ (i + 1)) ∈ L.lattice := by
    intro i j hij
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
    convert L.lattice.smul_mem ((3 : ℤ) ^ d) L.ω₁_mem_lattice using 1
    simp only [zsmul_eq_mul]
    push_cast
    field_simp
    ring
  have hthird : ∀ j : ℕ, ((3 ^ j : ℕ) : ℂ) * (L.ω₁ / 3 ^ (j + 1)) = L.ω₁ / 3 := by
    intro j
    push_cast
    field_simp
    ring
  have hns : ∀ (n : ℕ) (z : ℂ), z ∈ L.lattice → (n : ℂ) * z ∈ L.lattice := fun n z hz => by
    simpa using L.lattice.smul_mem (n : ℤ) hz
  have hnot : ∀ j : ℕ, L.ω₁ / 3 ^ (j + 1) ∉ L.lattice := fun j h =>
    third_notMem L (hthird j ▸ hns _ _ h)
  have h33 : ((3 : ℕ) : ℂ) * (L.ω₁ / 3) ∈ L.lattice := by simpa using hpow 0 1 le_rfl
  have hαthird : α * (L.ω₁ / 3) ∉ L.lattice := fun h => third_notMem L
    (mem_of_mul_mem L h0 hα hN (hcop 3 (by decide) (by simpa using h3)) h33 h)

  have dist : ∀ β : ℂ, (∀ l ∈ L.lattice, β * l ∈ L.lattice) → β * (L.ω₁ / 3) ∉ L.lattice →
      ∀ x : ℕ → W, (∀ j, (x j : ℂ) = L.weierstrassP (β * (L.ω₁ / 3 ^ (j + 1)))) →
      Function.Injective fun j => ρ (x j) := by
    intro β hβ hβ3 x hx
    have hm : ∀ i j : ℕ, i + 1 ≤ j →
        ((3 ^ j : ℕ) : ℂ) * (β * (L.ω₁ / 3 ^ (i + 1))) ∈ L.lattice := by
      intro i j hij
      rw [mul_left_comm]
      exact hβ _ (hpow i j hij)
    have hn : ∀ j : ℕ, ((3 ^ j : ℕ) : ℂ) * (β * (L.ω₁ / 3 ^ (j + 1))) ∉ L.lattice := by
      intro j
      rw [mul_left_comm, hthird]
      exact hβ3
    refine Function.Injective.of_lt_imp_ne fun i j hij h => ?_
    have T := (GlobalTheory.T.weierstrassP_torsion_mem_and_distinct_mod_nonunits L W (3 ^ (j + 1)) h2 h3 hg₂ hg₃ hΔ
      (hpos _) (h3n _)).2 _ _ (hm i _ (by omega)) (fun h => hn i (hns _ _ h))
      (hm j _ le_rfl) (fun h => hn j (hns _ _ h)) (by
        rw [← hx, ← hx]
        have : ρ (x i - x j) = 0 := by rw [map_sub]; exact sub_eq_zero.mpr h
        exact (residue_eq_zero_iff' W _).mp this)
    apply hn j
    rcases T with T | T
    · convert L.lattice.sub_mem (hm i j hij) (hns (3 ^ j) _ T) using 1
      ring
    · convert L.lattice.sub_mem (hns (3 ^ j) _ T) (hm i j hij) using 1
      ring
  choose x y hx hy hxy using fun j : ℕ =>
    rel (3 ^ (j + 1)) (L.ω₁ / 3 ^ (j + 1)) (hpos _) (h3n _) (hpow j _ le_rfl) (hnot j)
  have hxi := dist 1 (by simp) (by simpa using third_notMem L) x (by simpa using hx)
  have hyi := dist α hα hαthird y hy
  let g₂ : W := ⟨L.g₂, hg₂⟩
  let g₃ : W := ⟨L.g₃, hg₃⟩
  let α₀ : W := ⟨α, W.nonunits_subset hαW⟩
  have hode' : C (α ^ 2) * (C c * D) * (4 * (C c * A) ^ 3 - C L.g₂ * (C c * A) * (C c * D) ^ 2 -
      C L.g₃ * (C c * D) ^ 3) = (derivative (C c * A) * (C c * D) -
        (C c * A) * derivative (C c * D)) ^ 2 * (4 * X ^ 3 - C L.g₂ * X - C L.g₃) := by
    simp only [derivative_C_mul]
    linear_combination C c ^ 4 * hode
  have hode₀ : C (α₀ ^ 2) * D₀ * (4 * A₀ ^ 3 - C g₂ * A₀ * D₀ ^ 2 - C g₃ * D₀ ^ 3) =
      (derivative A₀ * D₀ - A₀ * derivative D₀) ^ 2 * (4 * X ^ 3 - C g₂ * X - C g₃) := by
    apply Polynomial.map_injective W.subtype W.subtype_injective
    simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, map_C, map_X,
      Polynomial.map_ofNat, ← derivative_map, hA₀, hD₀]
    exact hode'
  have hdvd₀ : (4 * X ^ 3 - C g₂ * X - C g₃ : W[X]) ∣
      D₀ * (4 * A₀ ^ 3 - C g₂ * A₀ * D₀ ^ 2 - C g₃ * D₀ ^ 3) := by
    apply cubic_dvd W h2
    simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, map_C,
      Polynomial.map_ofNat, hA₀, hD₀]
    have hu : IsUnit (C (α ^ 2) : ℂ[X]) := isUnit_C.mpr (Ne.isUnit (pow_ne_zero _ h0))
    rw [← hu.dvd_mul_left, ← mul_assoc]
    exact Dvd.intro_left _ hode'.symm
  have hdeg : ∀ (B₀ : W[X]) (B : ℂ[X]), B₀.map W.subtype = C c * B →
      (B₀.map ρ).natDegree ≤ B.natDegree := by
    intro B₀ B h
    refine natDegree_map_le.trans ?_
    rw [← natDegree_map_eq_of_injective W.subtype_injective, h, natDegree_C_mul hc]
  have hα₀ : ρ α₀ = 0 := (residue_eq_zero_iff' W _).mpr hαW
  obtain ⟨a, d, ha, hd, eD, eA, e2, e3⟩ := residue_form p (ρ g₂) (ρ g₃) (A₀.map ρ) (D₀.map ρ)
    (by
      rw [← map_ofNat ρ 2]
      exact residue_ne_zero_of_inv_mem W _ (two_ne_zero (α := ℂ)) h2)
    (by
      rw [← map_ofNat ρ 3]
      exact residue_ne_zero_of_inv_mem W _ (three_ne_zero (α := ℂ)) h3)
    (by
      have := residue_ne_zero_of_inv_mem W (g₂ ^ 3 - 27 * g₃ ^ 2) hΔ0 hΔ
      simpa [map_ofNat] using this)
    hne (hAd ▸ hdeg A₀ A hA₀) (lt_of_le_of_lt (hdeg D₀ D hD₀) (by omega))
    _ _ hxi hyi hxy
    (by
      have := congrArg (Polynomial.map ρ) hode₀
      simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, map_C, map_X,
        Polynomial.map_ofNat, ← derivative_map, map_pow, hα₀, map_zero] at this
      rw [← this]
      ring)
    (by
      have := Polynomial.map_dvd ρ hdvd₀
      simpa only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, map_C, map_X,
        Polynomial.map_ofNat] using this)
  obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective a
  have ha' : (a₀ : ℂ) ∉ W.nonunits := fun h => ha ((residue_eq_zero_iff' W _).mpr h)
  rw [W.mem_nonunits_iff_or] at ha'
  push Not at ha'
  refine ⟨a₀, a₀.2, ha'.2, ha'.1, ?_, ?_, ?_⟩
  · refine (residue_eq_zero_iff' W (g₂ - a₀ ^ 2 * g₂ ^ p)).mp ?_
    rw [map_sub, map_mul, map_pow, map_pow]
    exact sub_eq_zero.mpr e2
  · refine (residue_eq_zero_iff' W (g₃ - a₀ ^ 3 * g₃ ^ p)).mp ?_
    rw [map_sub, map_mul, map_pow, map_pow]
    exact sub_eq_zero.mpr e3
  · intro m t hm hmW hmt ht
    obtain ⟨u, v, hu, hv, huv⟩ := rel m t hm hmW hmt ht
    rw [← hu, ← hv]
    refine (residue_eq_zero_iff' W (v - a₀ * u ^ p)).mp ?_
    rw [map_sub, map_mul, map_pow]
    rw [eA, eD] at huv
    simp only [eval_mul, eval_C, eval_pow, eval_X] at huv
    apply mul_left_cancel₀ hd
    linear_combination -huv

end GlobalTheory.EisensteinCongruence
