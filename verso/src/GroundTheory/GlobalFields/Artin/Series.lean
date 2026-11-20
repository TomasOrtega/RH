import Mathlib
import GroundTheory.GlobalFields.Artin.MemInvariantsCompSubtypeIff
import GroundTheory.GlobalFields.TateThesis.HeckeLFunction
import GroundTheory.GlobalFields.TateThesis.NonvanishingPrimes
set_option maxSynthPendingDepth 1

noncomputable section

open IsDedekindDomain NumberField Filter Topology ComplexConjugate

namespace GroundTheory.Global

section Average

variable {G : Type*} [Group G]

/- English proof (translation)
Rewrite using `[cosetAverage, finsum_eq_sum_of_fintype]`.
-/
theorem cosetAverage_eq_sum (I : Subgroup G) [Fintype I] (f : G → ℂ) (g : G) :
    cosetAverage I f g = (Nat.card I : ℂ)⁻¹ * ∑ i : I, f (g * i) := by
  rw [cosetAverage, finsum_eq_sum_of_fintype]

/- English proof (translation)
Use `Fintype.ofFinite I` as an intermediate fact. Establish `hI : (0 : ℝ) < Nat.card I` using `Nat.cast_pos.2 Nat.card_pos`. Rewrite using `[cosetAverage_eq_sum, norm_mul, norm_inv, Complex.norm_natCast]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `(norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hC _)`.

Use `_ = C := by`. Rewrite using `[Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul, inv_mul_cancel_left₀ hI.ne']`.
-/
theorem norm_cosetAverage_le (I : Subgroup G) [Finite I] (f : G → ℂ) {C : ℝ}
    (hC : ∀ g, ‖f g‖ ≤ C) (g : G) : ‖cosetAverage I f g‖ ≤ C := by
  have := Fintype.ofFinite I
  have hI : (0 : ℝ) < Nat.card I := Nat.cast_pos.2 Nat.card_pos
  rw [cosetAverage_eq_sum, norm_mul, norm_inv, Complex.norm_natCast]
  calc (Nat.card I : ℝ)⁻¹ * ‖∑ i : I, f (g * i)‖ ≤ (Nat.card I : ℝ)⁻¹ * ∑ _i : I, C := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hC _)
    _ = C := by
        rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul,
          inv_mul_cancel_left₀ hI.ne']

/- English proof (translation)
Use `Fintype.ofFinite I` as an intermediate fact. Simplify using `only [cosetAverage_eq_sum, Pi.add_apply, Finset.sum_add_distrib, mul_add]`.
-/
theorem cosetAverage_add (I : Subgroup G) [Finite I] (f₁ f₂ : G → ℂ) (g : G) :
    cosetAverage I (f₁ + f₂) g = cosetAverage I f₁ g + cosetAverage I f₂ g := by
  have := Fintype.ofFinite I
  simp only [cosetAverage_eq_sum, Pi.add_apply, Finset.sum_add_distrib, mul_add]

/- English proof (translation)
Use `Fintype.ofFinite I` as an intermediate fact. Simplify using `only [cosetAverage_eq_sum, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cosetAverage_smul (I : Subgroup G) [Finite I] (c : ℂ) (f : G → ℂ) (g : G) :
    cosetAverage I (c • f) g = c * cosetAverage I f g := by
  have := Fintype.ofFinite I
  simp only [cosetAverage_eq_sum, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

/- English proof (translation)
Use `Fintype.ofFinite I` as an intermediate fact. Simplify using `only [cosetAverage_eq_sum, map_mul, map_inv₀, map_natCast, map_sum]`.
-/
theorem cosetAverage_conj_apply (I : Subgroup G) [Finite I] (f : G → ℂ) (g : G) :
    cosetAverage I (fun x => conj (f x)) g = conj (cosetAverage I f g) := by
  have := Fintype.ofFinite I
  simp only [cosetAverage_eq_sum, map_mul, map_inv₀, map_natCast, map_sum]

/- English proof (translation)
Use `Fintype.ofFinite I` as an intermediate fact. Establish `hI : (Nat.card I : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 Nat.card_pos.ne'`. Rewrite using `[cosetAverage_eq_sum]`. Simplify using `only [Pi.one_apply, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul, mul_one]`. Conclude with `inv_mul_cancel₀ hI`.
-/
theorem cosetAverage_one (I : Subgroup G) [Finite I] (g : G) : cosetAverage I 1 g = 1 := by
  have := Fintype.ofFinite I
  have hI : (Nat.card I : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rw [cosetAverage_eq_sum]
  simp only [Pi.one_apply, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ hI

end Average

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

section LocalAverage

variable (v : HeightOneSpectrum (𝓞 K))

/- English proof (translation)
The claim follows from `norm_cosetAverage_le _ f hC _`.
-/
theorem norm_localAverage_le (f : Gal(L/K) → ℂ) {C : ℝ} (hC : ∀ g, ‖f g‖ ≤ C) (m : ℕ) :
    ‖localAverage L v f m‖ ≤ C :=
  norm_cosetAverage_le _ f hC _

/- English proof (translation)
The claim follows from `cosetAverage_add _ f₁ f₂ _`.
-/
theorem localAverage_add (f₁ f₂ : Gal(L/K) → ℂ) (m : ℕ) :
    localAverage L v (f₁ + f₂) m = localAverage L v f₁ m + localAverage L v f₂ m :=
  cosetAverage_add _ f₁ f₂ _

/- English proof (translation)
The claim follows from `cosetAverage_smul _ c f _`.
-/
theorem localAverage_smul (c : ℂ) (f : Gal(L/K) → ℂ) (m : ℕ) :
    localAverage L v (c • f) m = c * localAverage L v f m :=
  cosetAverage_smul _ c f _

/- English proof (translation)
The claim follows from `cosetAverage_conj_apply _ f _`.
-/
theorem localAverage_conj (f : Gal(L/K) → ℂ) (m : ℕ) :
    localAverage L v (fun g => conj (f g)) m = conj (localAverage L v f m) :=
  cosetAverage_conj_apply _ f _

/- English proof (translation)
The claim follows from `cosetAverage_one _ _`.
-/
theorem localAverage_one (m : ℕ) : localAverage L v (1 : Gal(L/K) → ℂ) m = 1 :=
  cosetAverage_one _ _

end LocalAverage

variable (K L) in

def artinTerm (f : Gal(L/K) → ℂ) (s : ℂ) (v : HeightOneSpectrum (𝓞 K)) (m : ℕ) : ℂ :=
  localAverage L v f m * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ m / m

variable (K L) in

def artinLocalLog (f : Gal(L/K) → ℂ) (s : ℂ) (v : HeightOneSpectrum (𝓞 K)) : ℂ :=
  ∑' m : ℕ, artinTerm K L f s v m

variable (K L) in

def artinLogL (f : Gal(L/K) → ℂ) (s : ℂ) : ℂ :=
  ∑' v : HeightOneSpectrum (𝓞 K), artinLocalLog K L f s v

variable (K L) in

def artinL (f : Gal(L/K) → ℂ) (s : ℂ) : ℂ :=
  Complex.exp (artinLogL K L f s)

/- English proof (translation)
Simplify using `[artinTerm]`.
-/
theorem artinTerm_zero (f : Gal(L/K) → ℂ) (s : ℂ) (v : HeightOneSpectrum (𝓞 K)) :
    artinTerm K L f s v 0 = 0 := by
  simp [artinTerm]

/- English proof (translation)
Rewrite using `[← Complex.cpow_nat_mul, mul_neg]`.
-/
theorem absNorm_cpow_neg_pow (v : HeightOneSpectrum (𝓞 K)) (s : ℂ) (m : ℕ) :
    ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ m = (Ideal.absNorm v.asIdeal : ℂ) ^ (-(m * s)) := by
  rw [← Complex.cpow_nat_mul, mul_neg]

section Convergence

/- English proof (translation)
Establish `h1` using `one_lt_absNorm_asIdeal v`. Rewrite using `[Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]`. Conclude with `Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast h1.le) (by linarith)`.
-/
theorem norm_absNorm_cpow_neg_le (v : HeightOneSpectrum (𝓞 K)) {s : ℂ} {σ : ℝ} (hσs : σ ≤ s.re) :
    ‖(Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) := by
  have h1 := one_lt_absNorm_asIdeal v
  rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast h1.le) (by linarith)

/- English proof (translation)
Establish `h1` using `one_lt_absNorm_asIdeal v`. Establish `h2 : (2 : ℝ) ≤ Ideal.absNorm v.asIdeal` using `by exact_mod_cast h1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.rpow_neg_one, one_div]`. Conclude with `inv_anti₀ (by norm_num) h2`.
-/
theorem absNorm_rpow_neg_le_half (v : HeightOneSpectrum (𝓞 K)) {σ : ℝ} (hσ : 1 ≤ σ) :
    (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) ≤ 1 / 2 := by
  have h1 := one_lt_absNorm_asIdeal v
  have h2 : (2 : ℝ) ≤ Ideal.absNorm v.asIdeal := by exact_mod_cast h1
  calc (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ ≤ 1 / 2 := by
        rw [Real.rpow_neg_one, one_div]
        exact inv_anti₀ (by norm_num) h2

/- English proof (translation)
Establish `hC0 : 0 ≤ C` using `(norm_nonneg _).trans (hC 1)`. Use `set t : ℝ := (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) with ht`. Establish `ht0 : 0 ≤ t` using `Real.rpow_nonneg (Nat.cast_nonneg _) _`. Establish `ht1 : t ≤ 1 / 2` using `absNorm_rpow_neg_le_half v hσ`. Break down `Nat.eq_zero_or_eq_succ_pred m with rfl | hm` into its components or cases.

Rewrite using `[artinTerm_zero, norm_zero]`. Check the signs of the components of the expression. Use `set k := m.pred`. Rewrite using `[hm]`. Establish `hy` using `norm_absNorm_cpow_neg_le v hσs`.

Rewrite `hy` using `[← ht]`. Establish `hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ)` using `by exact_mod_cast Nat.succ_pos k`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[artinTerm, norm_div, norm_mul, norm_pow, Complex.norm_natCast]`. Use `_ ≤ C * t ^ (k + 1) / 1 := by gcongr`.

Conclude with `norm_localAverage_le v f hC _`. Use `_ = C * (t ^ k * t) := by rw [div_one, pow_succ]`. Use `_ ≤ C * ((1 / 2) ^ k * t) := by gcongr`. Use `_ = 2 * C * t * (1 / 2) ^ (k + 1) := by ring`.
-/
theorem norm_artinTerm_le (f : Gal(L/K) → ℂ) {C : ℝ} (hC : ∀ g, ‖f g‖ ≤ C) {s : ℂ} {σ : ℝ}
    (hσ : 1 ≤ σ) (hσs : σ ≤ s.re) (v : HeightOneSpectrum (𝓞 K)) (m : ℕ) :
    ‖artinTerm K L f s v m‖ ≤ 2 * C * (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) * (1 / 2) ^ m := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1)
  set t : ℝ := (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have ht1 : t ≤ 1 / 2 := absNorm_rpow_neg_le_half v hσ
  rcases Nat.eq_zero_or_eq_succ_pred m with rfl | hm
  · rw [artinTerm_zero, norm_zero]
    positivity
  · set k := m.pred
    rw [hm]
    have hy := norm_absNorm_cpow_neg_le v hσs
    rw [← ht] at hy
    have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
    calc ‖artinTerm K L f s v (k + 1)‖
        = ‖localAverage L v f (k + 1)‖ * ‖(Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ ^ (k + 1) /
            ((k + 1 : ℕ) : ℝ) := by
          rw [artinTerm, norm_div, norm_mul, norm_pow, Complex.norm_natCast]
      _ ≤ C * t ^ (k + 1) / 1 := by
          gcongr
          exact norm_localAverage_le v f hC _
      _ = C * (t ^ k * t) := by rw [div_one, pow_succ]
      _ ≤ C * ((1 / 2) ^ k * t) := by gcongr
      _ = 2 * C * t * (1 / 2) ^ (k + 1) := by ring

/- English proof (translation)
Establish `hinj : Function.Injective fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal` using `fun v w h => HeightOneSpectrum.ext h`. Use `((summable_absNorm_rpow_inv (K := K) hσ).comp_injective hinj).congr fun v => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`. Rewrite using `[Real.rpow_neg (Nat.cast_nonneg _)]`.
-/
theorem summable_absNorm_rpow_neg_place {σ : ℝ} (hσ : 1 < σ) :
    Summable fun v : HeightOneSpectrum (𝓞 K) => (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) := by
  have hinj : Function.Injective fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal :=
    fun v w h => HeightOneSpectrum.ext h
  refine ((summable_absNorm_rpow_inv (K := K) hσ).comp_injective hinj).congr fun v => ?_
  simp only [Function.comp_apply]
  rw [Real.rpow_neg (Nat.cast_nonneg _)]

/- English proof (translation)
The claim follows from `Summable.mul_of_nonneg ((summable_absNorm_rpow_neg_place hσ).mul_left (2 * C)) summable_geometric_two (fun v => by positivity) (fun m => by positivity)`.
-/
theorem summable_artinMajorant {C : ℝ} (hC0 : 0 ≤ C) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun p : HeightOneSpectrum (𝓞 K) × ℕ =>
      2 * C * (Ideal.absNorm p.1.asIdeal : ℝ) ^ (-σ) * (1 / 2) ^ p.2 :=
  Summable.mul_of_nonneg ((summable_absNorm_rpow_neg_place hσ).mul_left (2 * C))
    summable_geometric_two (fun v => by positivity) (fun m => by positivity)

omit [IsGalois K L] in
/- English proof (translation)
Use `Fintype.ofFinite Gal(L/K)` as an intermediate fact. Conclude with `⟨∑ g, ‖f g‖, fun g => Finset.single_le_sum (fun x _ => norm_nonneg (f x)) (Finset.mem_univ g)⟩`.
-/
theorem exists_norm_le (f : Gal(L/K) → ℂ) : ∃ C, ∀ g, ‖f g‖ ≤ C := by
  classical
  have := Fintype.ofFinite Gal(L/K)
  exact ⟨∑ g, ‖f g‖, fun g => Finset.single_le_sum (fun x _ => norm_nonneg (f x))
    (Finset.mem_univ g)⟩

/- English proof (translation)
Take `⟨C, hC⟩` from `exists_norm_le f`. Establish `hC0 : 0 ≤ C` using `(norm_nonneg _).trans (hC 1)`. Conclude with `Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => norm_artinTerm_le f hC hs.le le_rfl p.1 p.2) (summable_artinMajorant hC0 hs)`.
-/
theorem summable_norm_artinTerm (f : Gal(L/K) → ℂ) {s : ℂ} (hs : 1 < s.re) :
    Summable fun p : HeightOneSpectrum (𝓞 K) × ℕ => ‖artinTerm K L f s p.1 p.2‖ := by
  obtain ⟨C, hC⟩ := exists_norm_le f
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1)
  exact Summable.of_nonneg_of_le (fun p => norm_nonneg _)
    (fun p => norm_artinTerm_le f hC hs.le le_rfl p.1 p.2) (summable_artinMajorant hC0 hs)

/- English proof (translation)
The claim follows from `(summable_norm_artinTerm f hs).of_norm`.
-/
theorem summable_artinTerm (f : Gal(L/K) → ℂ) {s : ℂ} (hs : 1 < s.re) :
    Summable fun p : HeightOneSpectrum (𝓞 K) × ℕ => artinTerm K L f s p.1 p.2 :=
  (summable_norm_artinTerm f hs).of_norm

/- English proof (translation)
The claim follows from `((summable_artinTerm f hs).prod_factor v).hasSum`.
-/
theorem hasSum_artinLocalLog (f : Gal(L/K) → ℂ) {s : ℂ} (hs : 1 < s.re)
    (v : HeightOneSpectrum (𝓞 K)) :
    HasSum (fun m => artinTerm K L f s v m) (artinLocalLog K L f s v) :=
  ((summable_artinTerm f hs).prod_factor v).hasSum

/- English proof (translation)
Establish `h` using `(summable_artinTerm f hs).hasSum`. Establish `h2` using `h.prod_fiberwise fun v => hasSum_artinLocalLog f hs v`. Rewrite using `[artinLogL, h2.tsum_eq]`. Conclude with `h`.
-/
theorem hasSum_artinTerm_artinLogL (f : Gal(L/K) → ℂ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun p : HeightOneSpectrum (𝓞 K) × ℕ => artinTerm K L f s p.1 p.2)
      (artinLogL K L f s) := by
  have h := (summable_artinTerm f hs).hasSum
  have h2 := h.prod_fiberwise fun v => hasSum_artinLocalLog f hs v
  rw [artinLogL, h2.tsum_eq]
  exact h

/- English proof (translation)
Establish `h` using `(summable_artinTerm f hs).hasSum.prod_fiberwise fun v => hasSum_artinLocalLog f hs v`. Rewrite `h` using `[(hasSum_artinTerm_artinLogL f hs).tsum_eq]`. Then use the resulting hypothesis.
-/
theorem hasSum_artinLocalLog_artinLogL (f : Gal(L/K) → ℂ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun v => artinLocalLog K L f s v) (artinLogL K L f s) := by
  have h := (summable_artinTerm f hs).hasSum.prod_fiberwise fun v => hasSum_artinLocalLog f hs v
  rwa [(hasSum_artinTerm_artinLogL f hs).tsum_eq] at h

end Convergence

section Holomorphy

/- English proof (translation)
Establish `hN : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 (by have := one_lt_absNorm_asIdeal v; omega)`. Unfold `artinTerm`. Conclude with `(((differentiable_neg.const_cpow (Or.inl hN)).pow m).const_mul _).div_const _`.
-/
theorem differentiable_artinTerm (f : Gal(L/K) → ℂ) (v : HeightOneSpectrum (𝓞 K)) (m : ℕ) :
    Differentiable ℂ fun s => artinTerm K L f s v m := by
  have hN : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (by have := one_lt_absNorm_asIdeal v; omega)
  unfold artinTerm
  exact (((differentiable_neg.const_cpow (Or.inl hN)).pow m).const_mul _).div_const _

/- English proof (translation)
Take `⟨C, hC⟩` from `exists_norm_le f`. Establish `hC0 : 0 ≤ C` using `(norm_nonneg _).trans (hC 1)`. Introduce `s hs`. Establish `hs' : 1 < s.re` using `hs`. Use `set σ : ℝ := (1 + s.re) / 2 with hσdef`.

Establish `hσ : 1 < σ` using `by rw [hσdef]; linarith`. Establish `hσs : σ < s.re` using `by rw [hσdef]; linarith`. Use `set U : Set ℂ := {z | σ < z.re} with hUdef`. Establish `hU : IsOpen U` using `isOpen_lt continuous_const Complex.continuous_re`. Establish `hD : DifferentiableOn ℂ (fun z => ∑' p : HeightOneSpectrum (𝓞 K) × ℕ, artinTerm K L f z p.1 p.2) U` using `Complex.differentiableOn_tsum_of_summable_norm (summable_artinMajorant hC0 hσ) (fun p => (differentiable_artinTerm f p.1 p.2).differentiableOn) hU (fun p z hz => norm_artinTerm_le f hC hσ.le (le_of_lt hz) p.1 p.2)`.

Establish `hEq : Set.EqOn (artinLogL K L f) (fun z => ∑' p : HeightOneSpectrum (𝓞 K) × ℕ, artinTerm K L f z p.1 p.2) U` using `fun z hz => (hasSum_artinTerm_artinLogL f (hσ.trans hz)).tsum_eq.symm`. Conclude with `((hD.congr hEq).differentiableAt (hU.mem_nhds hσs)).differentiableWithinAt`.
-/
theorem differentiableOn_artinLogL (f : Gal(L/K) → ℂ) :
    DifferentiableOn ℂ (artinLogL K L f) {s | 1 < s.re} := by
  obtain ⟨C, hC⟩ := exists_norm_le f
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1)
  intro s hs
  have hs' : 1 < s.re := hs
  set σ : ℝ := (1 + s.re) / 2 with hσdef
  have hσ : 1 < σ := by rw [hσdef]; linarith
  have hσs : σ < s.re := by rw [hσdef]; linarith
  set U : Set ℂ := {z | σ < z.re} with hUdef
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hD : DifferentiableOn ℂ
      (fun z => ∑' p : HeightOneSpectrum (𝓞 K) × ℕ, artinTerm K L f z p.1 p.2) U :=
    Complex.differentiableOn_tsum_of_summable_norm (summable_artinMajorant hC0 hσ)
      (fun p => (differentiable_artinTerm f p.1 p.2).differentiableOn) hU
      (fun p z hz => norm_artinTerm_le f hC hσ.le (le_of_lt hz) p.1 p.2)
  have hEq : Set.EqOn (artinLogL K L f)
      (fun z => ∑' p : HeightOneSpectrum (𝓞 K) × ℕ, artinTerm K L f z p.1 p.2) U :=
    fun z hz => (hasSum_artinTerm_artinLogL f (hσ.trans hz)).tsum_eq.symm
  exact ((hD.congr hEq).differentiableAt (hU.mem_nhds hσs)).differentiableWithinAt

/- English proof (translation)
The claim follows from `(differentiableOn_artinLogL f).cexp`.
-/
theorem differentiableOn_artinL (f : Gal(L/K) → ℂ) :
    DifferentiableOn ℂ (artinL K L f) {s | 1 < s.re} :=
  (differentiableOn_artinLogL f).cexp

/- English proof (translation)
The claim follows from `(differentiableOn_artinL f).analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)`.
-/
theorem analyticOnNhd_artinL (f : Gal(L/K) → ℂ) :
    AnalyticOnNhd ℂ (artinL K L f) {s | 1 < s.re} :=
  (differentiableOn_artinL f).analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

/- English proof (translation)
The claim follows from `Complex.exp_ne_zero _`.
-/
theorem artinL_ne_zero (f : Gal(L/K) → ℂ) (s : ℂ) : artinL K L f s ≠ 0 :=
  Complex.exp_ne_zero _

end Holomorphy

section Additivity

/- English proof (translation)
Rewrite using `[artinTerm, artinTerm, artinTerm, localAverage_add, add_mul, add_div]`.
-/
theorem artinTerm_add (f₁ f₂ : Gal(L/K) → ℂ) (s : ℂ) (v : HeightOneSpectrum (𝓞 K)) (m : ℕ) :
    artinTerm K L (f₁ + f₂) s v m = artinTerm K L f₁ s v m + artinTerm K L f₂ s v m := by
  rw [artinTerm, artinTerm, artinTerm, localAverage_add, add_mul, add_div]

/- English proof (translation)
Use `(hasSum_artinTerm_artinLogL (f₁ + f₂) hs).unique ?_` and prove the remaining obligations. Simplify using `only [artinTerm_add]`. Conclude with `(hasSum_artinTerm_artinLogL f₁ hs).add (hasSum_artinTerm_artinLogL f₂ hs)`.
-/
theorem artinLogL_add (f₁ f₂ : Gal(L/K) → ℂ) {s : ℂ} (hs : 1 < s.re) :
    artinLogL K L (f₁ + f₂) s = artinLogL K L f₁ s + artinLogL K L f₂ s := by
  refine (hasSum_artinTerm_artinLogL (f₁ + f₂) hs).unique ?_
  simp only [artinTerm_add]
  exact (hasSum_artinTerm_artinLogL f₁ hs).add (hasSum_artinTerm_artinLogL f₂ hs)

/- English proof (translation)
Rewrite using `[artinL, artinLogL_add f₁ f₂ hs, Complex.exp_add, artinL, artinL]`.
-/
theorem artinL_add (f₁ f₂ : Gal(L/K) → ℂ) {s : ℂ} (hs : 1 < s.re) :
    artinL K L (f₁ + f₂) s = artinL K L f₁ s * artinL K L f₂ s := by
  rw [artinL, artinLogL_add f₁ f₂ hs, Complex.exp_add, artinL, artinL]

/- English proof (translation)
Establish `h : ∀ v m, artinTerm K L (0 : Gal(L/K) → ℂ) s v m = 0` using `fun v m => by`. Rewrite using `[artinTerm, show (0 : Gal(L/K) → ℂ) = (0 : ℂ) • (0 : Gal(L/K) → ℂ) by simp, localAverage_smul, zero_mul, zero_mul, zero_div]`. Simplify using `[artinL, artinLogL, artinLocalLog, h]`.
-/
theorem artinL_zero (s : ℂ) : artinL K L (0 : Gal(L/K) → ℂ) s = 1 := by
  have h : ∀ v m, artinTerm K L (0 : Gal(L/K) → ℂ) s v m = 0 := fun v m => by
    rw [artinTerm, show (0 : Gal(L/K) → ℂ) = (0 : ℂ) • (0 : Gal(L/K) → ℂ) by simp,
      localAverage_smul, zero_mul, zero_mul, zero_div]
  simp [artinL, artinLogL, artinLocalLog, h]

/- English proof (translation)
Establish `h` using `artinL_add f (-f) hs`. Rewrite `h` using `[add_neg_cancel, artinL_zero]`. Conclude with `eq_inv_of_mul_eq_one_right h.symm`.
-/
theorem artinL_neg (f : Gal(L/K) → ℂ) {s : ℂ} (hs : 1 < s.re) :
    artinL K L (-f) s = (artinL K L f s)⁻¹ := by
  have h := artinL_add f (-f) hs
  rw [add_neg_cancel, artinL_zero] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/- English proof (translation)
Rewrite using `[sub_eq_add_neg, artinL_add _ _ hs, artinL_neg _ hs, div_eq_mul_inv]`.
-/
theorem artinL_sub (f₁ f₂ : Gal(L/K) → ℂ) {s : ℂ} (hs : 1 < s.re) :
    artinL K L (f₁ - f₂) s = artinL K L f₁ s / artinL K L f₂ s := by
  rw [sub_eq_add_neg, artinL_add _ _ hs, artinL_neg _ hs, div_eq_mul_inv]

/- English proof (translation)
Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty => simp [artinL_zero]`. Consider the case `insert i t hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, artinL_add _ _ hs, ih]`.
-/
theorem artinL_sum {ι : Type*} (t : Finset ι) (F : ι → Gal(L/K) → ℂ) {s : ℂ} (hs : 1 < s.re) :
    artinL K L (∑ i ∈ t, F i) s = ∏ i ∈ t, artinL K L (F i) s := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [artinL_zero]
  | insert i t hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, artinL_add _ _ hs, ih]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [artinL_zero]`. Consider the case `succ n ih => rw [succ_nsmul, artinL_add _ _ hs, ih, pow_succ]`.
-/
theorem artinL_nsmul (n : ℕ) (f : Gal(L/K) → ℂ) {s : ℂ} (hs : 1 < s.re) :
    artinL K L (n • f) s = artinL K L f s ^ n := by
  induction n with
  | zero => simp [artinL_zero]
  | succ n ih => rw [succ_nsmul, artinL_add _ _ hs, ih, pow_succ]

/- English proof (translation)
Break down `Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩` into its components or cases. Rewrite using `[natCast_zsmul, artinL_nsmul k f hs, zpow_natCast]`. Rewrite using `[neg_smul, natCast_zsmul, artinL_neg _ hs, artinL_nsmul k f hs, zpow_neg, zpow_natCast]`.
-/
theorem artinL_zsmul (n : ℤ) (f : Gal(L/K) → ℂ) {s : ℂ} (hs : 1 < s.re) :
    artinL K L (n • f) s = artinL K L f s ^ n := by
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · rw [natCast_zsmul, artinL_nsmul k f hs, zpow_natCast]
  · rw [neg_smul, natCast_zsmul, artinL_neg _ hs, artinL_nsmul k f hs, zpow_neg, zpow_natCast]

end Additivity

section Conjugation

/- English proof (translation)
Establish `harg : (Ideal.absNorm v.asIdeal : ℂ).arg ≠ Real.pi`. Rewrite using `[Complex.natCast_arg]`. Conclude with `Real.pi_pos.ne`. Rewrite using `[← map_neg, Complex.cpow_conj _ _ harg, Complex.conj_conj, Complex.conj_natCast]`.
-/
theorem conj_absNorm_cpow_neg_conj (v : HeightOneSpectrum (𝓞 K)) (s : ℂ) :
    conj ((Ideal.absNorm v.asIdeal : ℂ) ^ (-conj s)) = (Ideal.absNorm v.asIdeal : ℂ) ^ (-s) := by
  have harg : (Ideal.absNorm v.asIdeal : ℂ).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]
    exact Real.pi_pos.ne
  rw [← map_neg, Complex.cpow_conj _ _ harg, Complex.conj_conj, Complex.conj_natCast]

/- English proof (translation)
Rewrite using `[artinTerm, artinTerm, map_div₀, map_mul, map_pow, conj_absNorm_cpow_neg_conj, localAverage_conj, map_natCast]`.
-/
theorem conj_artinTerm (f : Gal(L/K) → ℂ) (s : ℂ) (v : HeightOneSpectrum (𝓞 K)) (m : ℕ) :
    conj (artinTerm K L f (conj s) v m) = artinTerm K L (fun g => conj (f g)) s v m := by
  rw [artinTerm, artinTerm, map_div₀, map_mul, map_pow, conj_absNorm_cpow_neg_conj,
    localAverage_conj, map_natCast]

/- English proof (translation)
Rewrite using `[artinL, artinL, ← Complex.exp_conj, artinLogL, artinLogL, Complex.conj_tsum]`. Simplify using `only [artinLocalLog, Complex.conj_tsum, conj_artinTerm]`.
-/
theorem conj_artinL_conj (f : Gal(L/K) → ℂ) (s : ℂ) :
    conj (artinL K L f (conj s)) = artinL K L (fun g => conj (f g)) s := by
  rw [artinL, artinL, ← Complex.exp_conj, artinLogL, artinLogL, Complex.conj_tsum]
  simp only [artinLocalLog, Complex.conj_tsum, conj_artinTerm]

end Conjugation

end GroundTheory.Global
