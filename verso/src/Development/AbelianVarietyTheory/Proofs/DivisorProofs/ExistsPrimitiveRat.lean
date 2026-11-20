import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MemPass
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModLatTau

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal UpperHalfPlane ReciprocityTheory.ChartRestriction.L1
open scoped UpperHalfPlane

namespace GlobalTheory.IdealTheta

/- English proof (translation)
Use `set A : ℤ := r.num * s.den with hA`. Use `set B : ℤ := s.num * r.den with hB`. Establish `hr : (r : K) * (r.den : K) = (r.num : K)`. Use `congrArg (fun t : ℚ => (t : K)) (Rat.mul_den_eq_num r)` as an intermediate fact. Move the coercions through the operations in `at this`.

Conclude with `this`. Establish `hs : (s : K) * (s.den : K) = (s.num : K)`. Use `congrArg (fun t : ℚ => (t : K)) (Rat.mul_den_eq_num s)` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`.

Establish `hAB : (A : K) * a₁ + (B : K) * a₂ = (r.den : K) * (s.den : K)`. Rewrite using `[hA, hB]`. Use `push_cast`. Rewrite using `[← hr, ← hs]`. Take the linear combination `((r.den : K) * (s.den : K)) * h`.

Establish `hN : (r.den : K) * (s.den : K) ≠ 0` using `mul_ne_zero (Nat.cast_ne_zero.mpr r.den_nz) (Nat.cast_ne_zero.mpr s.den_nz)`. Establish `hg : Int.gcd A B ≠ 0`. Introduce `h0`. Rewrite `h0` using `[Int.gcd_eq_zero_iff]`. Rewrite `hAB` using `[h0.1, h0.2]`.

Apply `hN` to reduce the goal to its premises. Rewrite using `[← hAB]`. Simplify using the standard rewrite rules. Take `⟨p, hp⟩ : ((Int.gcd A B : ℕ) : ℤ) ∣ A` from `Int.gcd_dvd_left A B`. Take `⟨q, hq⟩ : ((Int.gcd A B : ℕ) : ℤ) ∣ B` from `Int.gcd_dvd_right A B`.

Establish `hbez` using `Int.gcd_eq_gcd_ab A B`. Use `set g : ℕ := Int.gcd A B with hgdef`. Establish `hgZ : (g : ℤ) ≠ 0` using `Nat.cast_ne_zero.mpr hg`. Establish `hgK : (g : K) ≠ 0` using `Nat.cast_ne_zero.mpr hg`. Use `⟨((r.den : ℚ) * (s.den : ℚ)) / (g : ℚ), p, q, -Int.gcdB A B, Int.gcdA A B, ?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `h1 : (0 : ℚ) < r.den` using `Nat.cast_pos.mpr r.den_pos`. Establish `h2 : (0 : ℚ) < s.den` using `Nat.cast_pos.mpr s.den_pos`. Establish `h3 : (0 : ℚ) < g` using `Nat.cast_pos.mpr (Nat.pos_of_ne_zero hg)`. Check the signs of the components of the expression. Apply `mul_left_cancel₀ hgZ` to reduce the goal to its premises.

Take the linear combination `-hbez - Int.gcdA A B * hp - Int.gcdB A B * hq`. Establish `hpK : (A : K) = (g : K) * (p : K)` using `by exact_mod_cast congrArg (fun t : ℤ => (t : K)) hp`. Establish `hqK : (B : K) = (g : K) * (q : K)` using `by exact_mod_cast congrArg (fun t : ℤ => (t : K)) hq`. Use `push_cast`. Rewrite using `[eq_div_iff hgK, ← hAB, hpK, hqK]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_primitive_rat {K : Type} [Field K] [CharZero K] (a₁ a₂ : K) (r s : ℚ)
    (h : (r : K) * a₁ + (s : K) * a₂ = 1) :
    ∃ (c : ℚ) (p q u v : ℤ), 0 < c ∧ p * v - q * u = 1 ∧ (p : K) * a₁ + (q : K) * a₂ = (c : K) := by
  set A : ℤ := r.num * s.den with hA
  set B : ℤ := s.num * r.den with hB
  have hr : (r : K) * (r.den : K) = (r.num : K) := by
    have := congrArg (fun t : ℚ => (t : K)) (Rat.mul_den_eq_num r)
    push_cast at this; exact this
  have hs : (s : K) * (s.den : K) = (s.num : K) := by
    have := congrArg (fun t : ℚ => (t : K)) (Rat.mul_den_eq_num s)
    push_cast at this; exact this
  have hAB : (A : K) * a₁ + (B : K) * a₂ = (r.den : K) * (s.den : K) := by
    rw [hA, hB]; push_cast
    rw [← hr, ← hs]
    linear_combination ((r.den : K) * (s.den : K)) * h
  have hN : (r.den : K) * (s.den : K) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr r.den_nz) (Nat.cast_ne_zero.mpr s.den_nz)
  have hg : Int.gcd A B ≠ 0 := by
    intro h0
    rw [Int.gcd_eq_zero_iff] at h0
    rw [h0.1, h0.2] at hAB
    apply hN
    rw [← hAB]; simp
  obtain ⟨p, hp⟩ : ((Int.gcd A B : ℕ) : ℤ) ∣ A := Int.gcd_dvd_left A B
  obtain ⟨q, hq⟩ : ((Int.gcd A B : ℕ) : ℤ) ∣ B := Int.gcd_dvd_right A B
  have hbez := Int.gcd_eq_gcd_ab A B
  set g : ℕ := Int.gcd A B with hgdef
  have hgZ : (g : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hg
  have hgK : (g : K) ≠ 0 := Nat.cast_ne_zero.mpr hg
  refine ⟨((r.den : ℚ) * (s.den : ℚ)) / (g : ℚ), p, q, -Int.gcdB A B, Int.gcdA A B, ?_, ?_, ?_⟩
  · have h1 : (0 : ℚ) < r.den := Nat.cast_pos.mpr r.den_pos
    have h2 : (0 : ℚ) < s.den := Nat.cast_pos.mpr s.den_pos
    have h3 : (0 : ℚ) < g := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hg)
    positivity
  · apply mul_left_cancel₀ hgZ
    linear_combination -hbez - Int.gcdA A B * hp - Int.gcdB A B * hq
  · have hpK : (A : K) = (g : K) * (p : K) := by exact_mod_cast congrArg (fun t : ℤ => (t : K)) hp
    have hqK : (B : K) = (g : K) * (q : K) := by exact_mod_cast congrArg (fun t : ℤ => (t : K)) hq
    push_cast
    rw [eq_div_iff hgK, ← hAB, hpK, hqK]
    ring

/- English proof (translation)
Introduce `K _ _ d δ ι 𝔞 Λ hK _ _ _ hΛ`. Take `⟨c₀, τ₀, hc₀, hlat⟩` from `latTau Λ`. Establish `hmem : ∀ z : ℂ, z ∈ Λ.lattice ↔ ∃ y : K, y ∈ 𝔞 ∧ ι y = z`. Introduce `z`. Establish `: z ∈ (Λ.lattice : Set ℂ) ↔ z ∈ ι '' (𝔞 : Set K)` using `by rw [hΛ]`.

Conclude with `this`. Take `⟨a₁, -, ha₁⟩` from `(hmem (c₀ * τ₀)).mp ((hlat _).mpr ⟨1, 0, by simp⟩)`. Take `⟨a₂, -, ha₂⟩` from `(hmem c₀).mp ((hlat _).mpr ⟨0, 1, by simp⟩)`. Establish `hA : ∀ x : K, x ∈ 𝔞 ↔ ∃ m n : ℤ, x = (m : K) * a₁ + (n : K) * a₂`. Introduce `x`.

Establish `h1 : x ∈ 𝔞 ↔ ι x ∈ Λ.lattice`. Rewrite using `[hmem]`. Conclude with `⟨fun h => ⟨x, h, rfl⟩, fun ⟨y, hy, e⟩ => ι.injective e ▸ hy⟩`. Rewrite using `[h1, hlat]`. Use `exists_congr fun m => exists_congr fun n => ?_` and prove the remaining obligations.

Rewrite using `[← ι.injective.eq_iff]`. Simplify using `only [map_add, map_mul, map_intCast, ha₁, ha₂]`. Apply the tactic sequence `constructor <;> intro h <;> rw [h] <;> ring`. Establish `hli : LinearIndependent ℚ ![a₁, a₂]`. Rewrite using `[LinearIndependent.pair_iff]`.

Introduce `r s h`. Rewrite `h` using `[Rat.smul_def, Rat.smul_def]`. Establish `h1` using `congrArg ι h`. Simplify using `only [map_add, map_mul, map_ratCast, ha₁, ha₂, map_zero] at h1`. Establish `h2 : (r : ℂ) * τ₀ + (s : ℂ) = 0`.

Apply `mul_left_cancel₀ hc₀` to reduce the goal to its premises. Take the linear combination `h1`. Establish `h3` using `congrArg Complex.im h2`. Establish `hr : r = 0`. Use `τ₀.im_ne_zero` as an intermediate fact.

Simplify `h3` using `[this]`. Substitute `hr` using the available equality. Simplify using `using h2`. Establish `hspan` using `hli.span_eq_top_of_card_eq_finrank (by simp [hK])`. Take `⟨w, hw⟩` from `(Submodule.mem_span_range_iff_exists_fun ℚ).mp (show (1 : K) ∈ Submodule.span ℚ (Set.range ![a₁, a₂]) by rw [hspan]; trivial)`.

Simplify using `only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Rat.smul_def] at hw`. Take `⟨c, p, q, u, v, hc, hdet, hcK⟩` from `exists_primitive_rat a₁ a₂ (w 0) (w 1) hw`. Establish `hcK0 : (c : K) ≠ 0` using `by exact_mod_cast hc.ne'`. Establish `hcC0 : (c : ℂ) ≠ 0` using `by exact_mod_cast hc.ne'`. Establish `hdetK : (p : K) * v - q * u = 1` using `by exact_mod_cast congrArg (fun t : ℤ => (t : K)) hdet`.

Establish `hdetR : (p : ℝ) * v - q * u = 1` using `by exact_mod_cast hdet`. Use `set θ : K := -((u : K) * a₁ + (v : K) * a₂) / (c : K) with hθ`. Establish `hcθ : (c : K) * θ = -((u : K) * a₁ + (v : K) * a₂)`. Rewrite using `[hθ]`. Clear the denominators using the available nonvanishing facts.

Establish `hcC : (c : ℂ) = c₀ * ((p : ℂ) * τ₀ + q)`. Establish `h1` using `congrArg ι hcK`. Simplify using `only [map_add, map_mul, map_ratCast, map_intCast, ha₁, ha₂] at h1`. Take the linear combination `-h1`. Establish `hz : ((p : ℂ) * τ₀ + q) ≠ 0`.

Introduce `h0`. Apply `hcC0` to reduce the goal to its premises. Rewrite using `[hcC, h0, mul_zero]`. Establish `hιθ : ι θ = -((u : ℂ) * τ₀ + v) / ((p : ℂ) * τ₀ + q)`. Establish `h1` using `congrArg ι hcθ`.

Simplify using `only [map_add, map_mul, map_neg, map_ratCast, map_intCast, ha₁, ha₂] at h1`. Rewrite using `[eq_div_iff hz]`. Apply `mul_left_cancel₀ hc₀` to reduce the goal to its premises. Rewrite `h1` using `[hcC]`. Take the linear combination `h1`.

Establish `him : 0 < (ι θ).im`. Rewrite using `[hιθ, Complex.div_im, ← sub_div]`. Use `div_pos ?_ (Complex.normSq_pos.mpr hz)` and prove the remaining obligations. Establish `hy : 0 < (τ₀ : ℂ).im` using `τ₀.im_pos`. Simplify using `only [Complex.neg_im, Complex.neg_re, Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re, Complex.intCast_im, Complex.intCast_re]`.

Establish `: -(↑u * (τ₀ : ℂ).im + 0 * (τ₀ : ℂ).re + 0) * (↑p * (τ₀ : ℂ).re - 0 * (τ₀ : ℂ).im + ↑q) - -(↑u * (τ₀ : ℂ).re - 0 * (τ₀ : ℂ).im + ↑v) * (↑p * (τ₀ : ℂ).im + 0 * (τ₀ : ℂ).re + 0) = (τ₀ : ℂ).im`. Take the linear combination `(τ₀ : ℂ).im * hdetR`. Rewrite using `[this]`. Conclude with `hy`. Establish `hmain : ∀ x : K, x ∈ 𝔞 ↔ ∃ a b : ℤ, x = (c : K) * ((a : K) * θ + (b : K))`.

Introduce `x`. Rewrite using `[hA]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, n, rfl⟩`. Use `⟨m * q - n * p, m * v - n * u, ?_⟩` and prove the remaining obligations.

Use `push_cast`. Take the linear combination `(-((m : K) * q - n * p)) * hcθ + ((m : K) * v - n * u) * hcK - ((m : K) * a₁ + (n : K) * a₂) * hdetK`. Introduce and unpack `⟨a, b, rfl⟩`. Use `⟨b * p - a * u, b * q - a * v, ?_⟩` and prove the remaining obligations. Use `push_cast`.

Take the linear combination `(a : K) * hcθ - (b : K) * hcK`. Use `⟨c, θ, ⟨ι θ, him⟩, hc, rfl, ⟨hcC0, fun z => ?_⟩, hmain⟩` and prove the remaining obligations. Rewrite using `[hmem]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`.

Take `⟨a, b, rfl⟩` from `(hmain y).mp hy`. Conclude with `⟨a, b, by simp⟩`. Introduce and unpack `⟨a, b, rfl⟩`. Conclude with `⟨_, (hmain _).mpr ⟨a, b, rfl⟩, by simp⟩`.
-/
theorem main : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (Λ : PeriodPair), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) → 𝔞 ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf ι 𝔞 Λ → ∃ (c : ℚ) (θ : K) (τ : ℍ), 0 < c ∧ ι θ = (τ : ℂ) ∧ IsTauOf Λ (c : ℂ) τ ∧ ∀ x : K, x ∈ 𝔞 ↔ ∃ a b : ℤ, x = (c : K) * ((a : K) * θ + (b : K)) := by
  intro K _ _ d δ ι 𝔞 Λ hK _ _ _ hΛ
  obtain ⟨c₀, τ₀, hc₀, hlat⟩ := latTau Λ
  have hmem : ∀ z : ℂ, z ∈ Λ.lattice ↔ ∃ y : K, y ∈ 𝔞 ∧ ι y = z := by
    intro z
    have : z ∈ (Λ.lattice : Set ℂ) ↔ z ∈ ι '' (𝔞 : Set K) := by rw [hΛ]
    exact this
  obtain ⟨a₁, -, ha₁⟩ := (hmem (c₀ * τ₀)).mp ((hlat _).mpr ⟨1, 0, by simp⟩)
  obtain ⟨a₂, -, ha₂⟩ := (hmem c₀).mp ((hlat _).mpr ⟨0, 1, by simp⟩)
  have hA : ∀ x : K, x ∈ 𝔞 ↔ ∃ m n : ℤ, x = (m : K) * a₁ + (n : K) * a₂ := by
    intro x
    have h1 : x ∈ 𝔞 ↔ ι x ∈ Λ.lattice := by
      rw [hmem]
      exact ⟨fun h => ⟨x, h, rfl⟩, fun ⟨y, hy, e⟩ => ι.injective e ▸ hy⟩
    rw [h1, hlat]
    refine exists_congr fun m => exists_congr fun n => ?_
    rw [← ι.injective.eq_iff]
    simp only [map_add, map_mul, map_intCast, ha₁, ha₂]
    constructor <;> intro h <;> rw [h] <;> ring
  have hli : LinearIndependent ℚ ![a₁, a₂] := by
    rw [LinearIndependent.pair_iff]
    intro r s h
    rw [Rat.smul_def, Rat.smul_def] at h
    have h1 := congrArg ι h
    simp only [map_add, map_mul, map_ratCast, ha₁, ha₂, map_zero] at h1
    have h2 : (r : ℂ) * τ₀ + (s : ℂ) = 0 := by
      apply mul_left_cancel₀ hc₀
      linear_combination h1
    have h3 := congrArg Complex.im h2
    have hr : r = 0 := by
      have := τ₀.im_ne_zero
      simpa [this] using h3
    subst hr
    simpa using h2
  have hspan := hli.span_eq_top_of_card_eq_finrank (by simp [hK])
  obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp
    (show (1 : K) ∈ Submodule.span ℚ (Set.range ![a₁, a₂]) by rw [hspan]; trivial)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Rat.smul_def] at hw
  obtain ⟨c, p, q, u, v, hc, hdet, hcK⟩ := exists_primitive_rat a₁ a₂ (w 0) (w 1) hw
  have hcK0 : (c : K) ≠ 0 := by exact_mod_cast hc.ne'
  have hcC0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hdetK : (p : K) * v - q * u = 1 := by exact_mod_cast congrArg (fun t : ℤ => (t : K)) hdet
  have hdetR : (p : ℝ) * v - q * u = 1 := by exact_mod_cast hdet
  set θ : K := -((u : K) * a₁ + (v : K) * a₂) / (c : K) with hθ
  have hcθ : (c : K) * θ = -((u : K) * a₁ + (v : K) * a₂) := by
    rw [hθ]; field_simp
  have hcC : (c : ℂ) = c₀ * ((p : ℂ) * τ₀ + q) := by
    have h1 := congrArg ι hcK
    simp only [map_add, map_mul, map_ratCast, map_intCast, ha₁, ha₂] at h1
    linear_combination -h1
  have hz : ((p : ℂ) * τ₀ + q) ≠ 0 := by
    intro h0; apply hcC0; rw [hcC, h0, mul_zero]
  have hιθ : ι θ = -((u : ℂ) * τ₀ + v) / ((p : ℂ) * τ₀ + q) := by
    have h1 := congrArg ι hcθ
    simp only [map_add, map_mul, map_neg, map_ratCast, map_intCast, ha₁, ha₂] at h1
    rw [eq_div_iff hz]
    apply mul_left_cancel₀ hc₀
    rw [hcC] at h1
    linear_combination h1
  have him : 0 < (ι θ).im := by
    rw [hιθ, Complex.div_im, ← sub_div]
    refine div_pos ?_ (Complex.normSq_pos.mpr hz)
    have hy : 0 < (τ₀ : ℂ).im := τ₀.im_pos
    simp only [Complex.neg_im, Complex.neg_re, Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re,
      Complex.intCast_im, Complex.intCast_re]
    have : -(↑u * (τ₀ : ℂ).im + 0 * (τ₀ : ℂ).re + 0) * (↑p * (τ₀ : ℂ).re - 0 * (τ₀ : ℂ).im + ↑q) -
        -(↑u * (τ₀ : ℂ).re - 0 * (τ₀ : ℂ).im + ↑v) * (↑p * (τ₀ : ℂ).im + 0 * (τ₀ : ℂ).re + 0) = (τ₀ : ℂ).im := by
      linear_combination (τ₀ : ℂ).im * hdetR
    rw [this]; exact hy
  have hmain : ∀ x : K, x ∈ 𝔞 ↔ ∃ a b : ℤ, x = (c : K) * ((a : K) * θ + (b : K)) := by
    intro x
    rw [hA]
    constructor
    · rintro ⟨m, n, rfl⟩
      refine ⟨m * q - n * p, m * v - n * u, ?_⟩
      push_cast
      linear_combination (-((m : K) * q - n * p)) * hcθ + ((m : K) * v - n * u) * hcK
        - ((m : K) * a₁ + (n : K) * a₂) * hdetK
    · rintro ⟨a, b, rfl⟩
      refine ⟨b * p - a * u, b * q - a * v, ?_⟩
      push_cast
      linear_combination (a : K) * hcθ - (b : K) * hcK
  refine ⟨c, θ, ⟨ι θ, him⟩, hc, rfl, ⟨hcC0, fun z => ?_⟩, hmain⟩
  rw [hmem]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨a, b, rfl⟩ := (hmain y).mp hy
    exact ⟨a, b, by simp⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨_, (hmain _).mpr ⟨a, b, rfl⟩, by simp⟩

end GlobalTheory.IdealTheta
