import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DenominatorPowerSummableStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FourierCoefficientGrowthBoundStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArchimedeanGaussianFourierStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EisensteinLatticeSumBoundStatement

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.Core.EiBound

/- English proof (translation)
Establish `hout : Summable (fun s => ∑' r, h (s, r))` using `Summable.of_nonneg_of_le (fun s => tsum_nonneg fun r => h0 _) (fun s => (hin s).2) (ha.mul_right K)`. Establish `hs : Summable h` using `(summable_prod_of_nonneg (fun p => h0 p)).2 ⟨fun s => (hin s).1, hout⟩`. Use `⟨hs, ?_⟩` and prove the remaining obligations. Rewrite using `[hs.tsum_prod, ← tsum_mul_right]`. Conclude with `Summable.tsum_le_tsum (fun s => (hin s).2) hout (ha.mul_right K)`.
-/
theorem prod_sum_bound {S R : Type} (h : S × R → ℝ) (a : S → ℝ) (K : ℝ) (h0 : ∀ p, 0 ≤ h p)
    (ha : Summable a)
    (hin : ∀ s, Summable (fun r => h (s, r)) ∧ ∑' r, h (s, r) ≤ a s * K) :
    Summable h ∧ ∑' p, h p ≤ (∑' s, a s) * K := by
  have hout : Summable (fun s => ∑' r, h (s, r)) :=
    Summable.of_nonneg_of_le (fun s => tsum_nonneg fun r => h0 _) (fun s => (hin s).2)
      (ha.mul_right K)
  have hs : Summable h := (summable_prod_of_nonneg (fun p => h0 p)).2 ⟨fun s => (hin s).1, hout⟩
  refine ⟨hs, ?_⟩
  rw [hs.tsum_prod, ← tsum_mul_right]
  exact Summable.tsum_le_tsum (fun s => (hin s).2) hout (ha.mul_right K)

/- English proof (translation)
Set `L : AddSubgroup F` to `(algebraMap (𝓞 F) F).toAddMonoidHom.range`. Establish `hL : ∀ x : F, x ∈ L ↔ ∃ r : 𝓞 F, (r : F) = x` using `fun x => by`. Simplify using `[L, AddMonoidHom.mem_range]`. Establish `hsep : ∀ q q' : F ⧸ L, (∃ r : 𝓞 F, (Quotient.out q : F) - Quotient.out q' = (r : F)) → q = q'`. Introduce and unpack `q q' ⟨r, hr⟩`.

Rewrite using `[← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q']`. Use `(QuotientAddGroup.eq).2 ?_` and prove the remaining obligations. Establish `: -(Quotient.out q : F) + Quotient.out q' = ((-r : 𝓞 F) : F)`. Use `push_cast`. Take the linear combination `-hr`.

Conclude with `(hL _).2 ⟨-r, this.symm⟩`. Use `⟨F ⧸ L, Quotient.out, ?_, hsep, ?_, ?_⟩` and prove the remaining obligations. Introduce `q q' h`. Conclude with `hsep q q' ⟨0, by simp [h]⟩`. Introduce and unpack `⟨q, r⟩ ⟨q', r'⟩ h`.

Simplify using `only at h`. Establish `hq : q = q'` using `hsep q q' ⟨r' - r, by push_cast; linear_combination h⟩`. Substitute `hq` using the available equality. Establish `: (r : F) = r'` using `add_left_cancel h`. Establish `: r = r'` using `RingOfIntegers.ext this`.

Rewrite using `[this]`. Introduce `b`. Establish `h1 : (QuotientAddGroup.mk (Quotient.out (QuotientAddGroup.mk b : F ⧸ L)) : F ⧸ L) = QuotientAddGroup.mk b` using `QuotientAddGroup.out_eq' _`. Take `⟨r, hr⟩` from `(hL _).1 ((QuotientAddGroup.eq).1 h1)`. Use `⟨⟨QuotientAddGroup.mk b, r⟩, ?_⟩` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[hr]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_decomp (F : Type) [Field F] [NumberField F] :
    ∃ (Q : Type) (out : Q → F), Function.Injective out ∧
      (∀ q q', (∃ r : 𝓞 F, out q - out q' = (r : F)) → q = q') ∧
      Function.Bijective (fun p : Q × 𝓞 F => out p.1 + (p.2 : F)) := by
  let L : AddSubgroup F := (algebraMap (𝓞 F) F).toAddMonoidHom.range
  have hL : ∀ x : F, x ∈ L ↔ ∃ r : 𝓞 F, (r : F) = x := fun x => by
    simp [L, AddMonoidHom.mem_range]
  have hsep : ∀ q q' : F ⧸ L, (∃ r : 𝓞 F, (Quotient.out q : F) - Quotient.out q' = (r : F)) →
      q = q' := by
    rintro q q' ⟨r, hr⟩
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q']
    refine (QuotientAddGroup.eq).2 ?_
    have : -(Quotient.out q : F) + Quotient.out q' = ((-r : 𝓞 F) : F) := by
      push_cast
      linear_combination -hr
    exact (hL _).2 ⟨-r, this.symm⟩
  refine ⟨F ⧸ L, Quotient.out, ?_, hsep, ?_, ?_⟩
  · intro q q' h
    exact hsep q q' ⟨0, by simp [h]⟩
  · rintro ⟨q, r⟩ ⟨q', r'⟩ h
    simp only at h
    have hq : q = q' := hsep q q' ⟨r' - r, by push_cast; linear_combination h⟩
    subst hq
    have : (r : F) = r' := add_left_cancel h
    have : r = r' := RingOfIntegers.ext this
    rw [this]
  · intro b
    have h1 : (QuotientAddGroup.mk (Quotient.out (QuotientAddGroup.mk b : F ⧸ L)) : F ⧸ L) =
        QuotientAddGroup.mk b := QuotientAddGroup.out_eq' _
    obtain ⟨r, hr⟩ := (hL _).1 ((QuotientAddGroup.eq).1 h1)
    refine ⟨⟨QuotientAddGroup.mk b, r⟩, ?_⟩
    simp only
    rw [hr]; ring

/- English proof (translation)
Take `⟨k, rfl⟩ : ∃ k, M = k + 2` from `⟨M - 2, by omega⟩`. Establish `hy0 : 0 < y` using `ht.trans_le hy`. Establish `hs : 0 < Real.sqrt y` using `Real.sqrt_pos.2 hy0`. Establish `hst : 0 < Real.sqrt t` using `Real.sqrt_pos.2 ht`. Establish `hyy : y = Real.sqrt y ^ 2` using `(Real.sq_sqrt hy0.le).symm`.

Establish `e : Real.sqrt y ^ (k + 2) * (y * (y ^ (k + 2))⁻¹) = (Real.sqrt y ^ k)⁻¹`. Generalize the expression as in `Real.sqrt y = s at hs hyy`. Substitute `hyy` using the available equality. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, Nat.add_sub_cancel]`. Conclude with `inv_anti₀ (by positivity) (pow_le_pow_left₀ hst.le (Real.sqrt_le_sqrt hy) k)`.
-/
theorem place_bound (M : ℕ) (hM : 2 ≤ M) (t y : ℝ) (ht : 0 < t) (hy : t ≤ y) :
    Real.sqrt y ^ M * (y * (y ^ M)⁻¹) ≤ ((Real.sqrt t) ^ (M - 2))⁻¹ := by
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 2 := ⟨M - 2, by omega⟩
  have hy0 : 0 < y := ht.trans_le hy
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy0
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hyy : y = Real.sqrt y ^ 2 := (Real.sq_sqrt hy0.le).symm
  have e : Real.sqrt y ^ (k + 2) * (y * (y ^ (k + 2))⁻¹) = (Real.sqrt y ^ k)⁻¹ := by
    generalize Real.sqrt y = s at hs hyy
    subst hyy
    field_simp
    ring
  rw [e, Nat.add_sub_cancel]
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hst.le (Real.sqrt_le_sqrt hy) k)

/- English proof (translation)
Introduce `F _ _ _ _ lf hlf hO ψ hψ ι _ _ M B ρ P hQ hM φ hφ t ht`. Establish `hTR : IsTotallyReal F` using `hQ.1`. Establish `hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x` using `hQ.2.2.2.2.1`. Take `⟨C1, hC1⟩` from `GlobalTheory.T.fourier_coefficient_growth_bound F lf hlf hO ψ hψ ι M B ρ P hQ φ hφ`. Take `⟨C2, hC2⟩` from `GlobalTheory.T.eisenstein_lattice_sum_bound F hTR ρ hρ M (by omega) t ht`.

Take `⟨Q, out, hinj, hsep, hbij⟩` from `exists_decomp F`. Take `⟨hd1, hd2, hd3⟩` from `GlobalTheory.T.denominator_power_summable F M hM 1 one_pos`. Set `a : Q → ℝ` to `fun q => ((den (out q) : ℝ) ^ M)⁻¹`. Establish `ha0 : ∀ q, 0 ≤ a q` using `fun q => by positivity`. Establish `ha : Summable a`.

Establish `h` using `hd3 (Set.range out) (by`. Introduce and unpack `_ ⟨q, rfl⟩ _ ⟨q', rfl⟩ ⟨r, hr⟩`. Rewrite using `[hsep q q' ⟨r, by simpa using hr⟩])`. Conclude with `(Equiv.ofInjective out hinj).summable_iff.2 h`. Establish `hterm : ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → ∀ b : F, ‖eiTerm ψ lf B ρ P φ τ b‖ ≤ |C1| * ((den b : ℝ) ^ M)⁻¹ * (∏ w, ‖τ w + (ρ w b : ℝ)‖ ^ M)⁻¹`.

Introduce `τ hτ b`. Establish `hc` using `(GlobalTheory.T.archimedean_gaussian_fourier F ι M B ρ P hQ (fun w => τ w + (ρ w b : ℝ)) (fun w => by simpa using hτ w)).2.1`. Unfold `eiTerm`. Rewrite using `[norm_mul, hc]`. Use `mul_le_mul_of_nonneg_right ((hC1 b).trans ?_) (by positivity)` and prove the remaining obligations.

Conclude with `mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)`. Use `⟨(∑' q, a q) * |C1| * |C2| * ∏ _w : InfinitePlace F, ((Real.sqrt t) ^ (M - 2))⁻¹, ?_⟩` and prove the remaining obligations. Introduce `τ hτ`. Establish `hτ0 : ∀ w, 0 < (τ w).im` using `fun w => ht.trans_le (hτ w)`. Use `set Y : ℝ := ∏ w, (τ w).im * ((τ w).im ^ M)⁻¹ with hYdef`.

Establish `hY0 : 0 ≤ Y` using `Finset.prod_nonneg fun w _ => by`. Use `hτ0 w` as an intermediate fact. Check the signs of the components of the expression. Set `e : Q × 𝓞 F ≃ F` to `Equiv.ofBijective _ hbij`. Set `h' : Q × 𝓞 F → ℝ` to `fun p => |C1| * a p.1 * (∏ w, ‖(τ w + (ρ w (out p.1) : ℝ)) + (ρ w (p.2 : F) : ℝ)‖ ^ M)⁻¹`.

Establish `hh'0 : ∀ p, 0 ≤ h' p` using `fun p => by`. Use `ha0 p.1` as an intermediate fact. Check the signs of the components of the expression. Establish `hle : ∀ p, ‖eiTerm ψ lf B ρ P φ τ (e p)‖ ≤ h' p`. Introduce and unpack `⟨q, r⟩`.

Establish `h1` using `hterm τ hτ0 (out q + (r : F))`. Establish `h2 : den (out q + (r : F)) = den (out q)` using `hd1 _ _`. Rewrite `h1` using `[h2]`. Establish `h3 : ∀ w, τ w + ((ρ w (out q + (r : F)) : ℝ) : ℂ) = (τ w + (ρ w (out q) : ℝ)) + (ρ w (r : F) : ℝ)` using `fun w => by`. Rewrite using `[map_add]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [h3] at h1`. Conclude with `h1`. Establish `hin : ∀ q, Summable (fun r => h' (q, r)) ∧ ∑' r, h' (q, r) ≤ a q * (|C1| * (|C2| * Y))`.

Introduce `q`. Take `⟨hs, hb⟩` from `hC2 (fun w => τ w + (ρ w (out q) : ℝ)) (fun w => by simpa using hτ w)`. Establish `him : ∀ w, (τ w + ((ρ w (out q) : ℝ) : ℂ)).im = (τ w).im` using `fun w => by simp`. Simplify using `only [him] at hb`. Establish `hs' : Summable (fun r : 𝓞 F => |C1| * a q * (∏ w, ‖(τ w + (ρ w (out q) : ℝ)) + (ρ w (r : F) : ℝ)‖ ^ M)⁻¹)` using `hs.mul_left _`.

Use `⟨hs', ?_⟩` and prove the remaining obligations. Establish `hq0` using `ha0 q`. Express the relevant statement in the definitionally equal form `∑' r : 𝓞 F, |C1| * a q * (∏ w, ‖(τ w + (ρ w (out q) : ℝ)) + (ρ w (r : F) : ℝ)‖ ^ M)⁻¹ ≤ _`. Rewrite using `[tsum_mul_left]`. Combine the equalities or inequalities in the displayed calculation.

Take `⟨hsum', hbd'⟩` from `prod_sum_bound h' a (|C1| * (|C2| * Y)) hh'0 ha hin`. Establish `hsumc : Summable (fun p => ‖eiTerm ψ lf B ρ P φ τ (e p)‖)` using `Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hsum'`. Establish `hsum : Summable (fun b => ‖eiTerm ψ lf B ρ P φ τ b‖)` using `e.summable_iff.1 hsumc`. Use `⟨hsum, ?_⟩` and prove the remaining obligations. Establish `htot : ∑' b, ‖eiTerm ψ lf B ρ P φ τ b‖ ≤ (∑' q, a q) * (|C1| * (|C2| * Y))`.

Rewrite using `[← e.tsum_eq (fun b => ‖eiTerm ψ lf B ρ P φ τ b‖)]`. Conclude with `(Summable.tsum_le_tsum hle hsumc hsum').trans hbd'`. Establish `hwt0 : 0 ≤ wt M τ` using `Finset.prod_nonneg fun w _ => by positivity`. Establish `hA0 : 0 ≤ ∑' q, a q` using `tsum_nonneg ha0`. Establish `hwY : wt M τ * Y ≤ ∏ _w : InfinitePlace F, ((Real.sqrt t) ^ (M - 2))⁻¹`.

Rewrite using `[hYdef]`. Unfold `wt`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_le_prod (fun w _ => ?_) (fun w _ => place_bound M (by omega) t _ ht (hτ w))` and prove the remaining obligations. Use `hτ0 w` as an intermediate fact.

Check the signs of the components of the expression. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ei_bound : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)]
    (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → 3 ≤ M →
    ∀ φ : (ι → A F) → ℂ, SB φ → ∀ t : ℝ, 0 < t → ∃ C : ℝ, ∀ τ : InfinitePlace F → ℂ,
    (∀ w, t ≤ (τ w).im) → Summable (fun b => ‖eiTerm ψ lf B ρ P φ τ b‖) ∧
      wt M τ * ∑' b, ‖eiTerm ψ lf B ρ P φ τ b‖ ≤ C := by
  intro F _ _ _ _ lf hlf hO ψ hψ ι _ _ M B ρ P hQ hM φ hφ t ht
  have hTR : IsTotallyReal F := hQ.1
  have hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x := hQ.2.2.2.2.1
  obtain ⟨C1, hC1⟩ := GlobalTheory.T.fourier_coefficient_growth_bound F lf hlf hO ψ hψ ι M B ρ P hQ φ hφ
  obtain ⟨C2, hC2⟩ := GlobalTheory.T.eisenstein_lattice_sum_bound F hTR ρ hρ M (by omega) t ht
  obtain ⟨Q, out, hinj, hsep, hbij⟩ := exists_decomp F
  obtain ⟨hd1, hd2, hd3⟩ := GlobalTheory.T.denominator_power_summable F M hM 1 one_pos
  let a : Q → ℝ := fun q => ((den (out q) : ℝ) ^ M)⁻¹
  have ha0 : ∀ q, 0 ≤ a q := fun q => by positivity
  have ha : Summable a := by
    have h := hd3 (Set.range out) (by
      rintro _ ⟨q, rfl⟩ _ ⟨q', rfl⟩ ⟨r, hr⟩
      rw [hsep q q' ⟨r, by simpa using hr⟩])
    exact (Equiv.ofInjective out hinj).summable_iff.2 h
  have hterm : ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → ∀ b : F,
      ‖eiTerm ψ lf B ρ P φ τ b‖ ≤
        |C1| * ((den b : ℝ) ^ M)⁻¹ * (∏ w, ‖τ w + (ρ w b : ℝ)‖ ^ M)⁻¹ := by
    intro τ hτ b
    have hc := (GlobalTheory.T.archimedean_gaussian_fourier F ι M B ρ P hQ (fun w => τ w + (ρ w b : ℝ))
      (fun w => by simpa using hτ w)).2.1
    unfold eiTerm
    rw [norm_mul, hc]
    refine mul_le_mul_of_nonneg_right ((hC1 b).trans ?_) (by positivity)
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  refine ⟨(∑' q, a q) * |C1| * |C2| * ∏ _w : InfinitePlace F, ((Real.sqrt t) ^ (M - 2))⁻¹, ?_⟩
  intro τ hτ
  have hτ0 : ∀ w, 0 < (τ w).im := fun w => ht.trans_le (hτ w)
  set Y : ℝ := ∏ w, (τ w).im * ((τ w).im ^ M)⁻¹ with hYdef
  have hY0 : 0 ≤ Y := Finset.prod_nonneg fun w _ => by
    have := hτ0 w
    positivity
  let e : Q × 𝓞 F ≃ F := Equiv.ofBijective _ hbij
  let h' : Q × 𝓞 F → ℝ := fun p =>
    |C1| * a p.1 * (∏ w, ‖(τ w + (ρ w (out p.1) : ℝ)) + (ρ w (p.2 : F) : ℝ)‖ ^ M)⁻¹
  have hh'0 : ∀ p, 0 ≤ h' p := fun p => by
    have := ha0 p.1
    positivity
  have hle : ∀ p, ‖eiTerm ψ lf B ρ P φ τ (e p)‖ ≤ h' p := by
    rintro ⟨q, r⟩
    have h1 := hterm τ hτ0 (out q + (r : F))
    have h2 : den (out q + (r : F)) = den (out q) := hd1 _ _
    rw [h2] at h1
    have h3 : ∀ w, τ w + ((ρ w (out q + (r : F)) : ℝ) : ℂ) =
        (τ w + (ρ w (out q) : ℝ)) + (ρ w (r : F) : ℝ) := fun w => by
      rw [map_add]; push_cast; ring
    simp only [h3] at h1
    exact h1
  have hin : ∀ q, Summable (fun r => h' (q, r)) ∧
      ∑' r, h' (q, r) ≤ a q * (|C1| * (|C2| * Y)) := by
    intro q
    obtain ⟨hs, hb⟩ := hC2 (fun w => τ w + (ρ w (out q) : ℝ)) (fun w => by simpa using hτ w)
    have him : ∀ w, (τ w + ((ρ w (out q) : ℝ) : ℂ)).im = (τ w).im := fun w => by simp
    simp only [him] at hb
    have hs' : Summable (fun r : 𝓞 F => |C1| * a q *
        (∏ w, ‖(τ w + (ρ w (out q) : ℝ)) + (ρ w (r : F) : ℝ)‖ ^ M)⁻¹) := hs.mul_left _
    refine ⟨hs', ?_⟩
    have hq0 := ha0 q
    change ∑' r : 𝓞 F, |C1| * a q *
        (∏ w, ‖(τ w + (ρ w (out q) : ℝ)) + (ρ w (r : F) : ℝ)‖ ^ M)⁻¹ ≤ _
    rw [tsum_mul_left]
    calc |C1| * a q * ∑' r : 𝓞 F, (∏ w, ‖(τ w + (ρ w (out q) : ℝ)) + (ρ w (r : F) : ℝ)‖ ^ M)⁻¹
        ≤ |C1| * a q * (|C2| * Y) :=
          mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hY0))
            (by positivity)
      _ = a q * (|C1| * (|C2| * Y)) := by ring
  obtain ⟨hsum', hbd'⟩ := prod_sum_bound h' a (|C1| * (|C2| * Y)) hh'0 ha hin
  have hsumc : Summable (fun p => ‖eiTerm ψ lf B ρ P φ τ (e p)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hsum'
  have hsum : Summable (fun b => ‖eiTerm ψ lf B ρ P φ τ b‖) := e.summable_iff.1 hsumc
  refine ⟨hsum, ?_⟩
  have htot : ∑' b, ‖eiTerm ψ lf B ρ P φ τ b‖ ≤ (∑' q, a q) * (|C1| * (|C2| * Y)) := by
    rw [← e.tsum_eq (fun b => ‖eiTerm ψ lf B ρ P φ τ b‖)]
    exact (Summable.tsum_le_tsum hle hsumc hsum').trans hbd'
  have hwt0 : 0 ≤ wt M τ := Finset.prod_nonneg fun w _ => by positivity
  have hA0 : 0 ≤ ∑' q, a q := tsum_nonneg ha0
  have hwY : wt M τ * Y ≤ ∏ _w : InfinitePlace F, ((Real.sqrt t) ^ (M - 2))⁻¹ := by
    rw [hYdef]
    unfold wt
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun w _ => ?_) (fun w _ => place_bound M (by omega) t _ ht (hτ w))
    have := hτ0 w
    positivity
  calc wt M τ * ∑' b, ‖eiTerm ψ lf B ρ P φ τ b‖
      ≤ wt M τ * ((∑' q, a q) * (|C1| * (|C2| * Y))) :=
        mul_le_mul_of_nonneg_left htot hwt0
    _ = (∑' q, a q) * |C1| * |C2| * (wt M τ * Y) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hwY (by positivity)

end GlobalTheory.CompanionTheory.SW.Core.EiBound
