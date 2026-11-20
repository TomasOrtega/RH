import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGoodOfBddAll
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalSectionBoundedNonzeroMultipleStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CdvrExtSt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralFramedPointBaseChangeStable
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFrameAfterExtIffAnd
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts
open scoped WithZero Pointwise TensorProduct

namespace GlobalTheory.SupDescent

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨f, hf⟩ : ∃ f : F →ₗ[k] k, ∀ j, f (b j) = if m = j then 1 else 0 := by`. Take `⟨s, hs⟩` from `LinearMap.exists_leftInverse_of_injective (Finsupp.linearCombination k b) (LinearMap.ker_eq_bot.2 hb)`. Use `⟨(Finsupp.lapply m).comp s, fun j => ?_⟩` and prove the remaining obligations. Use `LinearMap.congr_fun hs (Finsupp.single j 1)` as an intermediate fact. Simplify using `only [LinearMap.comp_apply, Finsupp.linearCombination_single, one_smul, LinearMap.id_apply] at this`.

Simplify using `[this, Finsupp.single_apply, eq_comm]`. Take `⟨c, hc⟩` from `((Algebra.traceForm k F).toDual (traceForm_nondegenerate k F)).surjective f`. Establish `hc' : ∀ j, ∑ g : F ≃ₐ[k] F, g c * g (b j) = if m = j then 1 else 0` using `fun j => by`. Establish `h1 : Algebra.trace k F (c * b j) = f (b j)` using `by rw [← hc]; rfl`. Establish `h2` using `trace_eq_sum_automorphisms (K := k) (c * b j)`.

Simplify using `only [map_mul] at h2`. Rewrite using `[← h2, h1, hf]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `: ∑ g : F ≃ₐ[k] F, τ (g c) * ∑ j, τ (g (b j)) * x j = x m`. Simplify using `only [Finset.mul_sum, ← mul_assoc, ← map_mul τ]`.

Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.sum_mul, ← map_sum τ, hc']`. Apply the tactic sequence `rw [Finset.sum_eq_single m] <;> simp +contextual [eq_comm]`. Rewrite using `[← this]`. Simplify using `[h]`.
-/
theorem eq_zero_of_forall_conj {k F Ω ι : Type} [Field k] [Field F] [Field Ω] [Algebra k F] [FiniteDimensional k F]
    [IsGalois k F] [Fintype ι] (τ : F →+* Ω) {b : ι → F} (hb : LinearIndependent k b) (x : ι → Ω)
    (h : ∀ g : F ≃ₐ[k] F, ∑ j, τ (g (b j)) * x j = 0) (m : ι) : x m = 0 := by
  classical
  obtain ⟨f, hf⟩ : ∃ f : F →ₗ[k] k, ∀ j, f (b j) = if m = j then 1 else 0 := by
    obtain ⟨s, hs⟩ := LinearMap.exists_leftInverse_of_injective (Finsupp.linearCombination k b)
      (LinearMap.ker_eq_bot.2 hb)
    refine ⟨(Finsupp.lapply m).comp s, fun j => ?_⟩
    have := LinearMap.congr_fun hs (Finsupp.single j 1)
    simp only [LinearMap.comp_apply, Finsupp.linearCombination_single, one_smul, LinearMap.id_apply] at this
    simp [this, Finsupp.single_apply, eq_comm]
  obtain ⟨c, hc⟩ := ((Algebra.traceForm k F).toDual (traceForm_nondegenerate k F)).surjective f
  have hc' : ∀ j, ∑ g : F ≃ₐ[k] F, g c * g (b j) = if m = j then 1 else 0 := fun j => by
    have h1 : Algebra.trace k F (c * b j) = f (b j) := by rw [← hc]; rfl
    have h2 := trace_eq_sum_automorphisms (K := k) (c * b j)
    simp only [map_mul] at h2
    rw [← h2, h1, hf]
    split_ifs <;> simp
  have : ∑ g : F ≃ₐ[k] F, τ (g c) * ∑ j, τ (g (b j)) * x j = x m := by
    simp only [Finset.mul_sum, ← mul_assoc, ← map_mul τ]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, ← map_sum τ, hc']
    rw [Finset.sum_eq_single m] <;> simp +contextual [eq_comm]
  rw [← this]
  simp [h]

section Galois

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

/- English proof (translation)
Take `⟨j₀, -, hj₀⟩` from `Finset.exists_max_image Finset.univ (fun j => v (x j)) ⟨m, Finset.mem_univ m⟩`. Use `(hj₀ m (Finset.mem_univ m)).trans (not_lt.1 fun hlt => ?_)` and prove the remaining obligations. Establish `h0 : v (x j₀) ≠ 0` using `(zero_lt_one.trans hlt).ne'`. Establish `hx0 : x j₀ ≠ 0` using `(Valuation.ne_zero_iff v).1 h0`. Establish `hz : ∀ j, x j / x j₀ ∈ v.valuationSubring` using `fun j => by`.

Rewrite using `[Valuation.mem_valuationSubring_iff, map_div₀]`. Conclude with `div_le_one_of_le₀ (hj₀ j (Finset.mem_univ j)) zero_le'`. Set `z : ι → v.valuationSubring` to `fun j => ⟨_, hz j⟩`. Set `ψ : 𝓞 L →+* v.valuationSubring` to `(σ.comp (algebraMap (𝓞 L) L)).codRestrict v.valuationSubring fun a => h1 a`. Set `ρ` to `IsLocalRing.residue v.valuationSubring`.

Establish `hρ : ∀ a, ρ a = 0 ↔ v a < 1` using `fun a => by`. Rewrite using `[IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]`. Use `la.isMaximal` as an intermediate fact. Use `μ.isMaximal` as an intermediate fact. Use `letI := Ideal.Quotient.field la.asIdeal`.

Use `letI := Ideal.Quotient.field μ.asIdeal`. Set `τ : 𝓞 L ⧸ μ.asIdeal →+* IsLocalRing.ResidueField v.valuationSubring` to `Ideal.Quotient.lift _ (ρ.comp ψ) fun a ha => (hρ _).2 ((h2 a).2 ha)`. Establish `: Finite (𝓞 L ⧸ μ.asIdeal)` using `Ideal.finiteQuotientOfFreeOfNeBot _ μ.ne_bot`. Establish `hind : LinearIndependent (𝓞 K ⧸ la.asIdeal) fun j => Ideal.Quotient.mk μ.asIdeal (b j)`. Use `Fintype.linearIndependent_iff.2 fun c hc j => ?_` and prove the remaining obligations.

Use `choose c' hc' using fun j => Ideal.Quotient.mk_surjective (c j)`. Rewrite using `[← hc', Ideal.Quotient.eq_zero_iff_mem]`. Use `hb c' (Ideal.Quotient.eq_zero_iff_mem.1 ?_) j` and prove the remaining obligations. Rewrite using `[← hc, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← hc', Algebra.smul_def, Algebra.smul_def, map_mul]`. Both sides reduce to the same expression. Establish `key` using `eq_zero_of_forall_conj τ hind (fun j => ρ (z j)) (fun g => ?_) j₀`. Establish `h3` using `(hρ _).1 key`. Simplify using `[z, hx0] at h3`.

Take `⟨g, rfl⟩` from `Ideal.Quotient.stabilizerHom_surjective (L ≃ₐ[K] L) la.asIdeal μ.asIdeal g`. Establish `h4 : ∀ j, τ (Ideal.Quotient.stabilizerHom μ.asIdeal la.asIdeal (L ≃ₐ[K] L) g (Ideal.Quotient.mk μ.asIdeal (b j))) = ρ (ψ (g.1 • b j))` using `fun j => rfl`. Simplify using `only [h4, ← map_mul, ← map_sum, hρ]`. Establish `h5 : ((∑ j, ψ (g.1 • b j) * z j : v.valuationSubring) : F) = (∑ j, σ (g.1 (b j)) * x j) / x j₀`. Rewrite using `[Finset.sum_div]`.

Use `push_cast`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[mul_div_assoc]`. Both sides reduce to the same expression. Rewrite using `[h5, map_div₀, div_lt_one₀ (zero_lt_one.trans hlt)]`.

Conclude with `(h g.1 g.2).trans_lt hlt`.
-/
theorem le_one_of_forall_conj {F ι : Type} [Field F] [Fintype ι] (v : Valuation F ℤᵐ⁰)
    (la : HeightOneSpectrum (𝓞 K)) (μ : HeightOneSpectrum (𝓞 L)) [μ.asIdeal.LiesOver la.asIdeal] (σ : L →+* F)
    (h1 : ∀ a : 𝓞 L, v (σ a) ≤ 1) (h2 : ∀ a : 𝓞 L, v (σ a) < 1 ↔ a ∈ μ.asIdeal) (b : ι → 𝓞 L)
    (hb : ∀ x : ι → 𝓞 K, ∑ j, x j • b j ∈ μ.asIdeal → ∀ j, x j ∈ la.asIdeal) (x : ι → F)
    (h : ∀ g : L ≃ₐ[K] L, g • μ.asIdeal = μ.asIdeal → v (∑ j, σ (g (b j)) * x j) ≤ 1) (m : ι) : v (x m) ≤ 1 := by
  classical
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image Finset.univ (fun j => v (x j)) ⟨m, Finset.mem_univ m⟩
  refine (hj₀ m (Finset.mem_univ m)).trans (not_lt.1 fun hlt => ?_)
  have h0 : v (x j₀) ≠ 0 := (zero_lt_one.trans hlt).ne'
  have hx0 : x j₀ ≠ 0 := (Valuation.ne_zero_iff v).1 h0
  have hz : ∀ j, x j / x j₀ ∈ v.valuationSubring := fun j => by
    rw [Valuation.mem_valuationSubring_iff, map_div₀]
    exact div_le_one_of_le₀ (hj₀ j (Finset.mem_univ j)) zero_le'
  let z : ι → v.valuationSubring := fun j => ⟨_, hz j⟩
  let ψ : 𝓞 L →+* v.valuationSubring :=
    (σ.comp (algebraMap (𝓞 L) L)).codRestrict v.valuationSubring fun a => h1 a
  let ρ := IsLocalRing.residue v.valuationSubring
  have hρ : ∀ a, ρ a = 0 ↔ v a < 1 := fun a => by
    rw [IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
  have := la.isMaximal
  have := μ.isMaximal
  letI := Ideal.Quotient.field la.asIdeal
  letI := Ideal.Quotient.field μ.asIdeal
  let τ : 𝓞 L ⧸ μ.asIdeal →+* IsLocalRing.ResidueField v.valuationSubring :=
    Ideal.Quotient.lift _ (ρ.comp ψ) fun a ha => (hρ _).2 ((h2 a).2 ha)
  have : Finite (𝓞 L ⧸ μ.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ μ.ne_bot
  have hind : LinearIndependent (𝓞 K ⧸ la.asIdeal) fun j => Ideal.Quotient.mk μ.asIdeal (b j) := by
    refine Fintype.linearIndependent_iff.2 fun c hc j => ?_
    choose c' hc' using fun j => Ideal.Quotient.mk_surjective (c j)
    rw [← hc', Ideal.Quotient.eq_zero_iff_mem]
    refine hb c' (Ideal.Quotient.eq_zero_iff_mem.1 ?_) j
    rw [← hc, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hc', Algebra.smul_def, Algebra.smul_def, map_mul]
    rfl
  have key := eq_zero_of_forall_conj τ hind (fun j => ρ (z j)) (fun g => ?_) j₀
  · have h3 := (hρ _).1 key
    simp [z, hx0] at h3
  obtain ⟨g, rfl⟩ := Ideal.Quotient.stabilizerHom_surjective (L ≃ₐ[K] L) la.asIdeal μ.asIdeal g
  have h4 : ∀ j, τ (Ideal.Quotient.stabilizerHom μ.asIdeal la.asIdeal (L ≃ₐ[K] L) g
      (Ideal.Quotient.mk μ.asIdeal (b j))) = ρ (ψ (g.1 • b j)) := fun j => rfl
  simp only [h4, ← map_mul, ← map_sum, hρ]
  have h5 : ((∑ j, ψ (g.1 • b j) * z j : v.valuationSubring) : F) = (∑ j, σ (g.1 (b j)) * x j) / x j₀ := by
    rw [Finset.sum_div]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_div_assoc]
    rfl
  rw [h5, map_div₀, div_lt_one₀ (zero_lt_one.trans hlt)]
  exact (h g.1 g.2).trans_lt hlt

end Galois

section Places

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Distinguish the cases in `ha : a = 0`. Substitute `ha` using the available equality. Simplify using the standard rewrite rules. Establish `h` using `ho.2 a`. Establish `he : (0 : ℤ) < e` using `by exact_mod_cast ho.1`.

Establish `h1 : valV T.V (io a) ≠ 0` using `valV_ne_zero ((map_ne_zero io).2 ha)`. Establish `h2 : la.valuation K a ≠ 0` using `by simpa using ha`. Rewrite using `[← WithZero.log_le_log h1 one_ne_zero, ← WithZero.log_le_log h2 one_ne_zero, WithZero.log_one]`. Unfold `vV vLa at h`. Apply the tactic sequence `constructor <;> intro h' <;> nlinarith`.
-/
theorem val_le_one_iff {T : CDVR} {la : HeightOneSpectrum (𝓞 K)} {io : K →+* T.Fr} {e : ℕ}
    (ho : OverLa la T.V io e) (a : K) : valV T.V (io a) ≤ 1 ↔ la.valuation K a ≤ 1 := by
  by_cases ha : a = 0
  · subst ha; simp
  have h := ho.2 a
  have he : (0 : ℤ) < e := by exact_mod_cast ho.1
  have h1 : valV T.V (io a) ≠ 0 := valV_ne_zero ((map_ne_zero io).2 ha)
  have h2 : la.valuation K a ≠ 0 := by simpa using ha
  rw [← WithZero.log_le_log h1 one_ne_zero, ← WithZero.log_le_log h2 one_ne_zero, WithZero.log_one]
  unfold vV vLa at h
  constructor <;> intro h' <;> nlinarith

/- English proof (translation)
Distinguish the cases in `ha : a = 0`. Substitute `ha` using the available equality. Simplify using the standard rewrite rules. Establish `h` using `ho.2 a`. Establish `he : (0 : ℤ) < e` using `by exact_mod_cast ho.1`.

Establish `h1 : valV T.V (io a) ≠ 0` using `valV_ne_zero ((map_ne_zero io).2 ha)`. Establish `h2 : la.valuation K a ≠ 0` using `by simpa using ha`. Rewrite using `[← WithZero.log_lt_log h1 one_ne_zero, ← WithZero.log_lt_log h2 one_ne_zero, WithZero.log_one]`. Unfold `vV vLa at h`. Apply the tactic sequence `constructor <;> intro h' <;> nlinarith`.
-/
theorem val_lt_one_iff {T : CDVR} {la : HeightOneSpectrum (𝓞 K)} {io : K →+* T.Fr} {e : ℕ}
    (ho : OverLa la T.V io e) (a : K) : valV T.V (io a) < 1 ↔ la.valuation K a < 1 := by
  by_cases ha : a = 0
  · subst ha; simp
  have h := ho.2 a
  have he : (0 : ℤ) < e := by exact_mod_cast ho.1
  have h1 : valV T.V (io a) ≠ 0 := valV_ne_zero ((map_ne_zero io).2 ha)
  have h2 : la.valuation K a ≠ 0 := by simpa using ha
  rw [← WithZero.log_lt_log h1 one_ne_zero, ← WithZero.log_lt_log h2 one_ne_zero, WithZero.log_one]
  unfold vV vLa at h
  constructor <;> intro h' <;> nlinarith

/- English proof (translation)
The claim follows from `(val_lt_one_iff ho _).trans (la.valuation_lt_one_iff_mem a)`.
-/
theorem val_lt_one_iff_mem {T : CDVR} {la : HeightOneSpectrum (𝓞 K)} {io : K →+* T.Fr} {e : ℕ}
    (ho : OverLa la T.V io e) (a : 𝓞 K) : valV T.V (io a) < 1 ↔ a ∈ la.asIdeal :=
  (val_lt_one_iff ho _).trans (la.valuation_lt_one_iff_mem a)

/- English proof (translation)
Take `⟨la', e, ho⟩` from `GlobalTheory.AlgLawsCompare.exists_overLa T io hT`. Take `rfl : la' = la` from `HeightOneSpectrum.ext (Ideal.ext fun a => (val_lt_one_iff_mem ho a).symm.trans (h a))`. Conclude with `⟨e, ho⟩`.
-/
theorem exists_overLa_of_mem {T : CDVR} (hT : T.FinRes) {la : HeightOneSpectrum (𝓞 K)} {io : K →+* T.Fr}
    (h : ∀ a : 𝓞 K, valV T.V (io a) < 1 ↔ a ∈ la.asIdeal) : ∃ e, OverLa la T.V io e := by
  obtain ⟨la', e, ho⟩ := GlobalTheory.AlgLawsCompare.exists_overLa T io hT
  obtain rfl : la' = la := HeightOneSpectrum.ext (Ideal.ext fun a => (val_lt_one_iff_mem ho a).symm.trans (h a))
  exact ⟨e, ho⟩

/- English proof (translation)
Use `letI := io.toAlgebra`. Take `⟨m, hm⟩` from `Ideal.exists_maximal (T.Fr ⊗[K] L)`. Use `letI := Ideal.Quotient.field m`. Take `⟨T', κ, e, he, hv, hT'⟩` from `GlobalTheory.PlaceExtField.cdvrExtSt T hT ((T.Fr ⊗[K] L) ⧸ m) (algebraMap T.Fr _) (RingHom.finite_algebraMap.2 inferInstance)`. Use `⟨T', κ.comp (algebraMap T.Fr _), e, κ.comp ((Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight : L →ₐ[K] T.Fr ⊗[K] L).toRingHom), he, hv, hT', fun a => ?_⟩` and prove the remaining obligations.

Use `congrArg κ (congrArg (Ideal.Quotient.mk m) ?_)` and prove the remaining obligations. Conclude with `(Algebra.TensorProduct.includeRight : L →ₐ[K] T.Fr ⊗[K] L).commutes a`.
-/
theorem exists_ext {L : Type} [Field L] [Algebra K L] [FiniteDimensional K L] (T : CDVR) (hT : T.FinRes)
    (io : K →+* T.Fr) : ∃ (T' : CDVR) (i : T.Fr →+* T'.Fr) (e : ℕ) (σ : L →+* T'.Fr), 0 < e ∧
      (∀ a : T.Fr, a ≠ 0 → vV T'.V (i a) = (e : ℤ) * vV T.V a) ∧ T'.FinRes ∧
      ∀ a : K, σ (algebraMap K L a) = i (io a) := by
  letI := io.toAlgebra
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (T.Fr ⊗[K] L)
  letI := Ideal.Quotient.field m
  obtain ⟨T', κ, e, he, hv, hT'⟩ := GlobalTheory.PlaceExtField.cdvrExtSt T hT ((T.Fr ⊗[K] L) ⧸ m)
    (algebraMap T.Fr _) (RingHom.finite_algebraMap.2 inferInstance)
  refine ⟨T', κ.comp (algebraMap T.Fr _), e, κ.comp ((Ideal.Quotient.mk m).comp
    (Algebra.TensorProduct.includeRight : L →ₐ[K] T.Fr ⊗[K] L).toRingHom), he, hv, hT', fun a => ?_⟩
  refine congrArg κ (congrArg (Ideal.Quotient.mk m) ?_)
  exact (Algebra.TensorProduct.includeRight : L →ₐ[K] T.Fr ⊗[K] L).commutes a

end Places

section Unram

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
  {la : HeightOneSpectrum (𝓞 K)} {la' : HeightOneSpectrum (𝓞 K')}

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Simplify using the standard rewrite rules. Establish `h1 : la'.valuation K' (algebraMap K K' x) ≠ 0` using `by simpa using hx`. Establish `h2 : la.valuation K x ≠ 0` using `by simpa using hx`.

Rewrite using `[← WithZero.exp_log h1, ← WithZero.exp_log h2]`. Conclude with `congrArg _ (neg_injective (hv x))`.
-/
theorem valuation_algebraMap (hv : ∀ x : K, vLa la' (algebraMap K K' x) = vLa la x) (x : K) :
    la'.valuation K' (algebraMap K K' x) = la.valuation K x := by
  by_cases hx : x = 0
  · subst hx; simp
  have h1 : la'.valuation K' (algebraMap K K' x) ≠ 0 := by simpa using hx
  have h2 : la.valuation K x ≠ 0 := by simpa using hx
  rw [← WithZero.exp_log h1, ← WithZero.exp_log h2]
  exact congrArg _ (neg_injective (hv x))

/- English proof (translation)
Use `⟨Ideal.ext fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.under_def, Ideal.mem_comap, ← la.valuation_lt_one_iff_mem (K := K), ← la'.valuation_lt_one_iff_mem (K := K'), ← valuation_algebraMap hv]`. Both sides reduce to the same expression.
-/
theorem liesOver (hv : ∀ x : K, vLa la' (algebraMap K K' x) = vLa la x) : la'.asIdeal.LiesOver la.asIdeal := by
  refine ⟨Ideal.ext fun a => ?_⟩
  rw [Ideal.under_def, Ideal.mem_comap, ← la.valuation_lt_one_iff_mem (K := K),
    ← la'.valuation_lt_one_iff_mem (K := K'), ← valuation_algebraMap hv]
  rfl

/- English proof (translation)
Use `la.isMaximal` as an intermediate fact. Use `la'.isMaximal` as an intermediate fact. Use `letI := Ideal.Quotient.field la.asIdeal`. Use `letI := Ideal.Quotient.field la'.asIdeal`. Establish `: Finite (𝓞 K' ⧸ la'.asIdeal)` using `Ideal.finiteQuotientOfFreeOfNeBot _ la'.ne_bot`.

Set `B` to `Module.finBasis (𝓞 K ⧸ la.asIdeal) (𝓞 K' ⧸ la'.asIdeal)`. Use `choose b hb using fun j => Ideal.Quotient.mk_surjective (B j)`. Establish `e : ∀ x : Fin _ → 𝓞 K, Ideal.Quotient.mk la'.asIdeal (∑ j, x j • b j) = ∑ j, Ideal.Quotient.mk la.asIdeal (x j) • B j` using `fun x => by`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← hb, Algebra.smul_def, Algebra.smul_def, map_mul]`. Both sides reduce to the same expression. Use `⟨_, b, fun x hx j => ?_, fun a => ?_⟩` and prove the remaining obligations. Rewrite `hx` using `[← Ideal.Quotient.eq_zero_iff_mem, e]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 (Fintype.linearIndependent_iff.1 B.linearIndependent _ hx j)`.

Use `choose x hx using fun j => Ideal.Quotient.mk_surjective (B.repr (Ideal.Quotient.mk _ a) j)`. Use `⟨x, Ideal.Quotient.eq.1 ?_⟩` and prove the remaining obligations. Rewrite using `[e]`. Simplify using `only [hx, B.sum_repr]`.
-/
theorem exists_residue_basis [la'.asIdeal.LiesOver la.asIdeal] : ∃ (d : ℕ) (b : Fin d → 𝓞 K'),
    (∀ x : Fin d → 𝓞 K, ∑ j, x j • b j ∈ la'.asIdeal → ∀ j, x j ∈ la.asIdeal) ∧
    ∀ a : 𝓞 K', ∃ x : Fin d → 𝓞 K, a - ∑ j, x j • b j ∈ la'.asIdeal := by
  have := la.isMaximal
  have := la'.isMaximal
  letI := Ideal.Quotient.field la.asIdeal
  letI := Ideal.Quotient.field la'.asIdeal
  have : Finite (𝓞 K' ⧸ la'.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ la'.ne_bot
  let B := Module.finBasis (𝓞 K ⧸ la.asIdeal) (𝓞 K' ⧸ la'.asIdeal)
  choose b hb using fun j => Ideal.Quotient.mk_surjective (B j)
  have e : ∀ x : Fin _ → 𝓞 K, Ideal.Quotient.mk la'.asIdeal (∑ j, x j • b j) =
      ∑ j, Ideal.Quotient.mk la.asIdeal (x j) • B j := fun x => by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hb, Algebra.smul_def, Algebra.smul_def, map_mul]
    rfl
  refine ⟨_, b, fun x hx j => ?_, fun a => ?_⟩
  · rw [← Ideal.Quotient.eq_zero_iff_mem, e] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.1 (Fintype.linearIndependent_iff.1 B.linearIndependent _ hx j)
  · choose x hx using fun j => Ideal.Quotient.mk_surjective (B.repr (Ideal.Quotient.mk _ a) j)
    refine ⟨x, Ideal.Quotient.eq.1 ?_⟩
    rw [e]
    simp only [hx, B.sum_repr]

/- English proof (translation)
Take `⟨π, hπ⟩` from `la.valuation_exists_uniformizer K`. Establish `hπ' : la'.valuation K' (algebraMap K K' π) = WithZero.exp (-1 : ℤ)` using `(valuation_algebraMap hv π).trans hπ`. Establish `hπ0 : algebraMap K K' π ≠ 0` using `fun h => by rw [h, map_zero] at hπ'; exact WithZero.exp_ne_zero hπ'.symm`. Establish `base : ∀ a : K', la'.valuation K' a ≤ 1 → ∃ x : Fin d → K, la'.valuation K' (a - ∑ j, algebraMap K K' (x j) * b j) < 1` using `fun a ha => by`. Take `⟨a₀, h₀⟩` from `la'.exists_valuation_sub_lt_of_integer ha 1`.

Take `⟨x, hx⟩` from `hb a₀`. Use `⟨fun j => x j, ?_⟩` and prove the remaining obligations. Establish `h1` using `(la'.valuation_lt_one_iff_mem (K := K') _).2 hx`. Establish `h2 : a - ∑ j, algebraMap K K' (x j) * b j = algebraMap (𝓞 K') K' (a₀ - ∑ j, x j • b j) - (algebraMap (𝓞 K') K' a₀ - a)`. Rewrite using `[map_sub, map_sum]`.

Simplify using `only [Algebra.smul_def, map_mul]`. Establish `: ∀ j, algebraMap (𝓞 K') K' (algebraMap (𝓞 K) (𝓞 K') (x j)) = algebraMap K K' (x j)` using `fun j => rfl`. Simplify using `only [this]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2]`.

Conclude with `Valuation.map_sub_lt _ h1 h₀`. Establish `step : ∀ (n : ℤ) (a : K'), la'.valuation K' a ≤ WithZero.exp (-n) → ∃ x : Fin d → K, la'.valuation K' (a - ∑ j, algebraMap K K' (x j) * b j) ≤ WithZero.exp (-(n + 1))` using `fun n a ha => by`. Establish `hp : la'.valuation K' (algebraMap K K' π ^ n) = WithZero.exp (-n)`. Rewrite using `[map_zpow₀, hπ', ← WithZero.exp_zsmul]`. Simplify using the standard rewrite rules.

Take `⟨x, hx⟩` from `base (a / algebraMap K K' π ^ n) (by`. Rewrite using `[map_div₀, hp]`. Conclude with `div_le_one_of_le₀ ha zero_le')`. Use `⟨fun j => π ^ n * x j, ?_⟩` and prove the remaining obligations. Establish `h2 : a - ∑ j, algebraMap K K' (π ^ n * x j) * b j = algebraMap K K' π ^ n * (a / algebraMap K K' π ^ n - ∑ j, algebraMap K K' (x j) * b j)`.

Rewrite using `[mul_sub, mul_div_cancel₀ _ (zpow_ne_zero n hπ0), Finset.mul_sum]`. Simplify using `only [map_mul, map_zpow₀, mul_assoc]`. Rewrite using `[h2, map_mul, hp, neg_add, WithZero.exp_add]`. Use `mul_le_mul_right ?_ _` and prove the remaining obligations. Generalize the expression as in `la'.valuation K' _ = t at hx`.

Distinguish the cases in `ht : t = 0`. Simplify using `[ht]`. Rewrite `hx` using `[← WithZero.exp_log ht, ← WithZero.exp_zero, WithZero.exp_lt_exp]`. Rewrite using `[← WithZero.exp_log ht, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.

Establish `all : ∀ (N : ℤ), ∃ x : Fin d → K, la'.valuation K' (a - ∑ j, algebraMap K K' (x j) * b j) ≤ WithZero.exp (-N)` using `fun N => by`. Establish `h0 : ∀ N ≤ -WithZero.log (la'.valuation K' a), ∃ x : Fin d → K, la'.valuation K' (a - ∑ j, algebraMap K K' (x j) * b j) ≤ WithZero.exp (-N)` using `fun N hN => ⟨0, by simpa using (WithZero.le_exp_log (x := la'.valuation K' a)).trans (WithZero.exp_le_exp.2 (le_neg.1 hN))⟩`. Break down `le_total N (-WithZero.log (la'.valuation K' a)) with h | h` into its components or cases. Conclude with `h0 N h`. Proceed by induction on `N, h using Int.le_induction with`.

Consider the case `base => exact h0 _ le_rfl`. Consider the case `succ n _ ih`. Take `⟨x, hx⟩` from `ih`. Take `⟨y, hy⟩` from `step n _ hx`. Use `⟨x + y, ?_⟩` and prove the remaining obligations.

Simplify `hy` using `only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib, sub_sub]`. Establish `hκ' : algebraMap K K' κ ≠ 0` using `by simpa using hκ`. Establish `hκv : la'.valuation K' (algebraMap K K' κ) ≠ 0` using `by simpa using hκ`. Take `⟨x, hx⟩` from `all (-WithZero.log (la'.valuation K' (algebraMap K K' κ)))`. Rewrite `hx` using `[neg_neg, WithZero.exp_log hκv]`.

Use `⟨x, (a - ∑ j, algebraMap K K' (x j) * b j) / algebraMap K K' κ, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_div₀]`. Conclude with `div_le_one_of_le₀ hx zero_le'`. Rewrite using `[div_mul_cancel₀ _ hκ', add_sub_cancel]`.
-/
theorem exists_approx (hv : ∀ x : K, vLa la' (algebraMap K K' x) = vLa la x) {d : ℕ} {b : Fin d → 𝓞 K'}
    (hb : ∀ a : 𝓞 K', ∃ x : Fin d → 𝓞 K, a - ∑ j, x j • b j ∈ la'.asIdeal) (a : K') {κ : K} (hκ : κ ≠ 0) :
    ∃ (x : Fin d → K) (r : K'), la'.valuation K' r ≤ 1 ∧
      a = ∑ j, algebraMap K K' (x j) * b j + r * algebraMap K K' κ := by
  obtain ⟨π, hπ⟩ := la.valuation_exists_uniformizer K
  have hπ' : la'.valuation K' (algebraMap K K' π) = WithZero.exp (-1 : ℤ) := (valuation_algebraMap hv π).trans hπ
  have hπ0 : algebraMap K K' π ≠ 0 := fun h => by rw [h, map_zero] at hπ'; exact WithZero.exp_ne_zero hπ'.symm
  have base : ∀ a : K', la'.valuation K' a ≤ 1 → ∃ x : Fin d → K,
      la'.valuation K' (a - ∑ j, algebraMap K K' (x j) * b j) < 1 := fun a ha => by
    obtain ⟨a₀, h₀⟩ := la'.exists_valuation_sub_lt_of_integer ha 1
    obtain ⟨x, hx⟩ := hb a₀
    refine ⟨fun j => x j, ?_⟩
    have h1 := (la'.valuation_lt_one_iff_mem (K := K') _).2 hx
    have h2 : a - ∑ j, algebraMap K K' (x j) * b j =
        algebraMap (𝓞 K') K' (a₀ - ∑ j, x j • b j) - (algebraMap (𝓞 K') K' a₀ - a) := by
      rw [map_sub, map_sum]
      simp only [Algebra.smul_def, map_mul]
      have : ∀ j, algebraMap (𝓞 K') K' (algebraMap (𝓞 K) (𝓞 K') (x j)) = algebraMap K K' (x j) := fun j => rfl
      simp only [this]
      ring
    rw [h2]
    exact Valuation.map_sub_lt _ h1 h₀
  have step : ∀ (n : ℤ) (a : K'), la'.valuation K' a ≤ WithZero.exp (-n) → ∃ x : Fin d → K,
      la'.valuation K' (a - ∑ j, algebraMap K K' (x j) * b j) ≤ WithZero.exp (-(n + 1)) := fun n a ha => by
    have hp : la'.valuation K' (algebraMap K K' π ^ n) = WithZero.exp (-n) := by
      rw [map_zpow₀, hπ', ← WithZero.exp_zsmul]; simp
    obtain ⟨x, hx⟩ := base (a / algebraMap K K' π ^ n) (by
      rw [map_div₀, hp]; exact div_le_one_of_le₀ ha zero_le')
    refine ⟨fun j => π ^ n * x j, ?_⟩
    have h2 : a - ∑ j, algebraMap K K' (π ^ n * x j) * b j = algebraMap K K' π ^ n *
        (a / algebraMap K K' π ^ n - ∑ j, algebraMap K K' (x j) * b j) := by
      rw [mul_sub, mul_div_cancel₀ _ (zpow_ne_zero n hπ0), Finset.mul_sum]
      simp only [map_mul, map_zpow₀, mul_assoc]
    rw [h2, map_mul, hp, neg_add, WithZero.exp_add]
    refine mul_le_mul_right ?_ _
    generalize la'.valuation K' _ = t at hx
    by_cases ht : t = 0
    · simp [ht]
    rw [← WithZero.exp_log ht, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
    rw [← WithZero.exp_log ht, WithZero.exp_le_exp]
    omega
  have all : ∀ (N : ℤ), ∃ x : Fin d → K,
      la'.valuation K' (a - ∑ j, algebraMap K K' (x j) * b j) ≤ WithZero.exp (-N) := fun N => by
    have h0 : ∀ N ≤ -WithZero.log (la'.valuation K' a), ∃ x : Fin d → K,
        la'.valuation K' (a - ∑ j, algebraMap K K' (x j) * b j) ≤ WithZero.exp (-N) := fun N hN =>
      ⟨0, by simpa using (WithZero.le_exp_log (x := la'.valuation K' a)).trans (WithZero.exp_le_exp.2 (le_neg.1 hN))⟩
    rcases le_total N (-WithZero.log (la'.valuation K' a)) with h | h
    · exact h0 N h
    induction N, h using Int.le_induction with
    | base => exact h0 _ le_rfl
    | succ n _ ih =>
      obtain ⟨x, hx⟩ := ih
      obtain ⟨y, hy⟩ := step n _ hx
      refine ⟨x + y, ?_⟩
      simpa only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib, sub_sub] using hy
  have hκ' : algebraMap K K' κ ≠ 0 := by simpa using hκ
  have hκv : la'.valuation K' (algebraMap K K' κ) ≠ 0 := by simpa using hκ
  obtain ⟨x, hx⟩ := all (-WithZero.log (la'.valuation K' (algebraMap K K' κ)))
  rw [neg_neg, WithZero.exp_log hκv] at hx
  refine ⟨x, (a - ∑ j, algebraMap K K' (x j) * b j) / algebraMap K K' κ, ?_, ?_⟩
  · rw [map_div₀]; exact div_le_one_of_le₀ hx zero_le'
  · rw [div_mul_cancel₀ _ hκ', add_sub_cancel]

/- English proof (translation)
Set `L` to `IntermediateField.normalClosure K K' (AlgebraicClosure K')`. Establish `: NumberField L` using `NumberField.of_module_finite K L`. Establish `: IsGalois K L` using `{}`. Take `⟨T', i, e', σ₀, he', hv, hT', hσ₀⟩` from `exists_ext (L := L) T hT io`. Establish `hv' : ∀ a : T.Fr, vV T'.V (i a) = (e' : ℤ) * vV T.V a` using `fun a => by`.

Distinguish the cases in `h : a = 0`. Substitute `h` using the available equality. Simplify using `[vV]`. Conclude with `hv a h`. Take `⟨μ₀, e₀, ho₀⟩` from `GlobalTheory.AlgLawsCompare.exists_overLa T' σ₀ hT'`.

Use `la'.isMaximal` as an intermediate fact. Take `⟨Q, hQ, hQl⟩` from `Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) la'.asIdeal`. Set `μ : HeightOneSpectrum (𝓞 L)` to `⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot la'.ne_bot Q⟩`. Establish `hμ : μ.asIdeal.LiesOver la.asIdeal` using `Ideal.LiesOver.trans Q la'.asIdeal la.asIdeal`. Establish `hu : μ.asIdeal.under (𝓞 K) = μ₀.asIdeal.under (𝓞 K)`.

Rewrite using `[← hμ.over]`. Use `Ideal.ext fun a => ?_` and prove the remaining obligations. Rewrite using `[Ideal.under_def, Ideal.mem_comap, ← val_lt_one_iff_mem ho₀, ← val_lt_one_iff_mem (ho.bc i he' hv')]`. Conclude with `Iff.of_eq (congrArg (fun t => valV T'.V t < 1) (hσ₀ a).symm)`. Use `μ.isPrime` as an intermediate fact.

Use `μ₀.isPrime` as an intermediate fact. Take `⟨g₀, hg₀⟩` from `Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 K) (𝓞 L) (L ≃ₐ[K] L) _ _ hu`. Set `σ₁ : L →+* T'.Fr` to `σ₀.comp (g₀ : L →+* L)`. Establish `h2 : ∀ a : 𝓞 L, valV T'.V (σ₁ a) < 1 ↔ a ∈ μ.asIdeal` using `fun a => by`. Rewrite using `[← Ideal.smul_mem_pointwise_smul_iff (a := g₀), ← hg₀, ← val_lt_one_iff_mem ho₀]`.

Both sides reduce to the same expression. Establish `h1 : ∀ a : 𝓞 L, valV T'.V (σ₁ a) ≤ 1` using `fun a => (val_le_one_iff ho₀ _).2 (μ₀.valuation_le_one (g₀ • a))`. Establish `key` using `le_one_of_forall_conj (valV T'.V) la μ σ₁ h1 h2 (fun j => algebraMap (𝓞 K') (𝓞 L) (b j)) (fun c hc => hb c ?_) (fun j => i (x j)) (fun g hg => ?_) m`. Distinguish the cases in `h0 : x m = 0`. Rewrite using `[h0]`.

Conclude with `zero_mem _`. Establish `h3` using `(GoodPtsModel.inV_iff_vV T' ((map_ne_zero i).2 h0)).1 ((GoodPtsModel.inV_iff_val T' _).2 key)`. Rewrite `h3` using `[hv']`. Conclude with `(GoodPtsModel.inV_iff_vV T h0).2 ((mul_nonneg_iff_of_pos_left (by exact_mod_cast he')).1 h3)`. Rewrite using `[hQl.over, Ideal.under_def, Ideal.mem_comap, map_sum]`.

Simplify `hc` using `only [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]`. Set `σ : K' →+* T'.Fr` to `(σ₁.comp (g : L →+* L)).comp (algebraMap K' L)`. Take `⟨e'', ho''⟩` from `exists_overLa_of_mem (la := la') (io := σ) hT' fun a => by`. Rewrite using `[hQl.over, Ideal.under_def, Ideal.mem_comap, ← Ideal.smul_mem_pointwise_smul_iff (a := g)]`. Conclude with `(h2 (g • algebraMap (𝓞 K') (𝓞 L) a)).trans (by rw [show g • Q = Q from hg])`.

Use `(GoodPtsModel.inV_iff_val T' _).1 (h T' i e' σ e'' he' hv hT' (fun a => ?_) ho'')` and prove the remaining obligations. Use `show σ₀ (g₀ (g (algebraMap K' L (algebraMap K K' a)))) = _`. Rewrite using `[← IsScalarTower.algebraMap_apply, g.commutes, g₀.commutes, hσ₀]`.
-/
theorem inV_of_forall_emb [la'.asIdeal.LiesOver la.asIdeal] {d : ℕ} {b : Fin d → 𝓞 K'}
    (hb : ∀ x : Fin d → 𝓞 K, ∑ j, x j • b j ∈ la'.asIdeal → ∀ j, x j ∈ la.asIdeal)
    {T : CDVR} (hT : T.FinRes) {io : K →+* T.Fr} {e : ℕ} (ho : OverLa la T.V io e) (x : Fin d → T.Fr)
    (h : ∀ (T' : CDVR) (i : T.Fr →+* T'.Fr) (e' : ℕ) (σ : K' →+* T'.Fr) (e'' : ℕ), 0 < e' →
      (∀ a : T.Fr, a ≠ 0 → vV T'.V (i a) = (e' : ℤ) * vV T.V a) → T'.FinRes →
      (∀ a : K, σ (algebraMap K K' a) = i (io a)) → OverLa la' T'.V σ e'' → InV T' (∑ j, σ (b j) * i (x j)))
    (m : Fin d) : InV T (x m) := by
  let L := IntermediateField.normalClosure K K' (AlgebraicClosure K')
  have : NumberField L := NumberField.of_module_finite K L
  have : IsGalois K L := {}
  obtain ⟨T', i, e', σ₀, he', hv, hT', hσ₀⟩ := exists_ext (L := L) T hT io
  have hv' : ∀ a : T.Fr, vV T'.V (i a) = (e' : ℤ) * vV T.V a := fun a => by
    by_cases h : a = 0
    · subst h; simp [vV]
    · exact hv a h
  obtain ⟨μ₀, e₀, ho₀⟩ := GlobalTheory.AlgLawsCompare.exists_overLa T' σ₀ hT'
  have := la'.isMaximal
  obtain ⟨Q, hQ, hQl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) la'.asIdeal
  let μ : HeightOneSpectrum (𝓞 L) := ⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot la'.ne_bot Q⟩
  have hμ : μ.asIdeal.LiesOver la.asIdeal := Ideal.LiesOver.trans Q la'.asIdeal la.asIdeal
  have hu : μ.asIdeal.under (𝓞 K) = μ₀.asIdeal.under (𝓞 K) := by
    rw [← hμ.over]
    refine Ideal.ext fun a => ?_
    rw [Ideal.under_def, Ideal.mem_comap, ← val_lt_one_iff_mem ho₀, ← val_lt_one_iff_mem (ho.bc i he' hv')]
    exact Iff.of_eq (congrArg (fun t => valV T'.V t < 1) (hσ₀ a).symm)
  have := μ.isPrime
  have := μ₀.isPrime
  obtain ⟨g₀, hg₀⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 K) (𝓞 L) (L ≃ₐ[K] L) _ _ hu
  let σ₁ : L →+* T'.Fr := σ₀.comp (g₀ : L →+* L)
  have h2 : ∀ a : 𝓞 L, valV T'.V (σ₁ a) < 1 ↔ a ∈ μ.asIdeal := fun a => by
    rw [← Ideal.smul_mem_pointwise_smul_iff (a := g₀), ← hg₀, ← val_lt_one_iff_mem ho₀]
    rfl
  have h1 : ∀ a : 𝓞 L, valV T'.V (σ₁ a) ≤ 1 := fun a =>
    (val_le_one_iff ho₀ _).2 (μ₀.valuation_le_one (g₀ • a))
  have key := le_one_of_forall_conj (valV T'.V) la μ σ₁ h1 h2 (fun j => algebraMap (𝓞 K') (𝓞 L) (b j))
    (fun c hc => hb c ?_) (fun j => i (x j)) (fun g hg => ?_) m
  · by_cases h0 : x m = 0
    · rw [h0]; exact zero_mem _
    have h3 := (GoodPtsModel.inV_iff_vV T' ((map_ne_zero i).2 h0)).1 ((GoodPtsModel.inV_iff_val T' _).2 key)
    rw [hv'] at h3
    exact (GoodPtsModel.inV_iff_vV T h0).2 ((mul_nonneg_iff_of_pos_left (by exact_mod_cast he')).1 h3)
  · rw [hQl.over, Ideal.under_def, Ideal.mem_comap, map_sum]
    simpa only [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply] using hc
  · let σ : K' →+* T'.Fr := (σ₁.comp (g : L →+* L)).comp (algebraMap K' L)
    obtain ⟨e'', ho''⟩ := exists_overLa_of_mem (la := la') (io := σ) hT' fun a => by
      rw [hQl.over, Ideal.under_def, Ideal.mem_comap, ← Ideal.smul_mem_pointwise_smul_iff (a := g)]
      exact (h2 (g • algebraMap (𝓞 K') (𝓞 L) a)).trans (by rw [show g • Q = Q from hg])
    refine (GoodPtsModel.inV_iff_val T' _).1 (h T' i e' σ e'' he' hv hT' (fun a => ?_) ho'')
    show σ₀ (g₀ (g (algebraMap K' L (algebraMap K K' a)))) = _
    rw [← IsScalarTower.algebraMap_apply, g.commutes, g₀.commutes, hσ₀]

end Unram

section Forms

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l}

/- English proof (translation)
Use `map_sum (evalL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y) (fun i => t i • f i) s` as an intermediate fact. Conclude with `this.trans (Finset.sum_congr rfl fun i _ => evalAt_smul _ _ _ _ _)`.
-/
theorem evR_sum {ι : Type} (s : Finset ι) (t : ι → c.F) (f : ι → Rul Xo c) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) : evR Xo c (∑ i ∈ s, t i • f i) y = ∑ i ∈ s, algebraMap c.F S (t i) * evR Xo c (f i) y := by
  have := map_sum (evalL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y) (fun i => t i • f i) s
  exact this.trans (Finset.sum_congr rfl fun i _ => evalAt_smul _ _ _ _ _)

/- English proof (translation)
Use `letI := io.toAlgebra`. Use `letI := σ.toAlgebra`. Use `⟨⟨y.1.ext hle hσ, GlobalTheory.FlagTan.fromTest_of_isLocalRing _, ?_⟩, rfl⟩` and prove the remaining obligations. Establish `e : ∀ (G : SAB H (Sp T.V)) τ v, IsEigV c' σ G τ v ↔ IsEigV c io G τ v` using `fun G τ v => by`. Unfold `IsEigV`.

Simplify using `only [← embK_incF hle τ, hσ]`. Take `⟨G, t', m1, m2, ⟨ub, h1, h2, h3, h4⟩, h5⟩` from `y.2.2`. Conclude with `⟨G, t', m1, m2, ⟨ub, h1, fun τ i => (e G τ _).2 (h2 τ i), fun τ w hw he => h3 τ w hw ((e G τ w).1 he), h4⟩, h5⟩`.
-/
theorem exists_intFr_ext (hle : c.F ≤ c'.F) {T : CDVR} {io : c.F →+* T.Fr} (σ : c'.F →+* T.Fr)
    (hσ : ∀ a, σ (incF c c' hle a) = io a) (y : IntFr Xo c T io) :
    ∃ y' : IntFr Xo c' T σ, letI := io.toAlgebra; letI := σ.toAlgebra; y'.1.res hle hσ = y.1 := by
  letI := io.toAlgebra
  letI := σ.toAlgebra
  refine ⟨⟨y.1.ext hle hσ, GlobalTheory.FlagTan.fromTest_of_isLocalRing _, ?_⟩, rfl⟩
  have e : ∀ (G : SAB H (Sp T.V)) τ v, IsEigV c' σ G τ v ↔ IsEigV c io G τ v := fun G τ v => by
    unfold IsEigV
    simp only [← embK_incF hle τ, hσ]
  obtain ⟨G, t', m1, m2, ⟨ub, h1, h2, h3, h4⟩, h5⟩ := y.2.2
  exact ⟨G, t', m1, m2, ⟨ub, h1, fun τ i => (e G τ _).2 (h2 τ i), fun τ w hw he => h3 τ w hw ((e G τ w).1 he), h4⟩, h5⟩

end Forms

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c r U hU la p hp hpl hgood c' hle la' hv hBC a n hD _ f' hf' hb`. Take `⟨m, as, fs, hfs, hIs⟩` from `hBC a n f' hf'`. Use `choose κ hκ0 hκ using fun i => GlobalTheory.T.cuspidal_section_bounded_nonzero_multiple E H Dw l Xo c r U hU la p hp hpl hgood a n (fs i) hD (hfs i)`. Use `letI : Algebra c.F c'.F := (incF c c' hle).toAlgebra`. Use `liesOver (K := c.F) (K' := c'.F) hv` as an intermediate fact.

Take `⟨d, b, hb1, hb2⟩` from `exists_residue_basis (la := la) (la' := la')`. Use `choose x ρ hρ hx using fun i => exists_approx (K := c.F) (K' := c'.F) hv hb2 (as i) (hκ0 i)`. Set `F : Fin d → Rul Xo c` to `fun j => ∑ i, x i j • fs i`. Establish `hF : ∀ j, F j ∈ cusp Xo c U a n` using `fun j => Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hfs i)`. Establish `hG : ∀ i, κ i • fs i ∈ supSet Xo c la (cusp Xo c U a n)` using `fun i => ⟨Submodule.smul_mem _ _ (hfs i), (GoodPtsModel.bddAll_iff_smul _ _).1 (hκ i)⟩`.

Establish `key : ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S) (y : FrPt Xo c' S), evR Xo c' f' y = ∑ j, algebraMap c'.F S (b j) * evR Xo c (F j) (y.res hle h) + ∑ i, algebraMap c'.F S (ρ i) * evR Xo c (κ i • fs i) (y.res hle h)`. Introduce `S _ _ _ h y`. Establish `h' : ∀ t : c.F, algebraMap c'.F S (algebraMap c.F c'.F t) = algebraMap c.F S t` using `h`. Establish `hs : ∀ i, evR Xo c (κ i • fs i) (y.res hle h) = algebraMap c.F S (κ i) * evR Xo c (fs i) (y.res hle h)` using `fun i => evalAt_smul _ _ _ _ _`. Rewrite using `[hIs S h y]`.

Simplify using `only [F, evR_sum, hs, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hx i]`. Simplify using `only [map_add, map_sum, map_mul, h', add_mul, Finset.sum_mul, mul_assoc]`.

Use `congr 1`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`. Use `⟨d + m, Fin.append (fun j => (b j : c'.F)) ρ, Fin.append F fun i => κ i • fs i, fun i => ?_, fun i => ?_, ?_⟩` and prove the remaining obligations. Use `Fin.addCases (fun j => ?_) (fun j => ?_) i` and prove the remaining obligations. Rewrite using `[Fin.append_left]`.

Conclude with `la'.valuation_le_one (b j)`. Rewrite using `[Fin.append_right]`. Conclude with `hρ j`. Use `Fin.addCases (fun j => ?_) (fun j => ?_) i swap` and prove the remaining obligations. Rewrite using `[Fin.append_right]`.

Conclude with `hG j`. Rewrite using `[Fin.append_left]`. Use `⟨hF j, fun T io e ho y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[map_one, one_mul]`. Use `inV_of_forall_emb (K := c.F) (K' := c'.F) hb1 hy ho (fun j => evI y (F j)) ?_ j` and prove the remaining obligations.

Introduce `T' i e' σ e'' he' hi hT' hσ ho'`. Take `⟨y₁, φ, hφ, hmap⟩` from `GlobalTheory.IntFrBaseChange.exists_intFr_baseChange E H Dw l Xo c T T' io y i e' he' hi`. Take `⟨y₂, hy₂⟩` from `exists_intFr_ext hle (io := i.comp io) σ hσ y₁`. Establish `hi' : ∀ t : T.Fr, vV T'.V (i t) = (e' : ℤ) * vV T.V t` using `fun t => by`. Distinguish the cases in `h : t = 0`.

Substitute `h` using the available equality. Simplify using `[vV]`. Conclude with `hi t h`. Establish `h1` using `hb T' σ e'' ho' y₂ hT'`. Rewrite `h1` using `[map_one, one_mul]`.

Establish `h2 : InV T' (∑ k, σ (ρ k) * evI y₁ (κ k • fs k))` using `Subring.sum_mem _ fun k _ => by`. Establish `h3` using `(hG k).2 T' _ _ (ho.bc i he' hi') y₁ hT'`. Rewrite `h3` using `[map_one, one_mul]`. Conclude with `Subring.mul_mem _ ((GoodPtsModel.inV_iff_val T' _).2 ((val_le_one_iff ho' _).2 (hρ k))) h3`. Establish `h4 : ∀ j, i (evI y (F j)) = evI y₁ (F j)` using `fun j => by`.

Use `letI := io.toAlgebra`. Use `letI := (i.comp io).toAlgebra`. Conclude with `(DFunLike.congr_fun hφ _).symm.trans (GlobalTheory.FlagTan.evR_frMap (cusp_le_sec Xo c U a n (hF j)).1 hmap).symm`. Establish `h5 : evI y₂ f' = ∑ j, σ (b j) * evI y₁ (F j) + ∑ k, σ (ρ k) * evI y₁ (κ k • fs k)`. Use `letI := (i.comp io).toAlgebra`.

Use `letI := σ.toAlgebra`. Use `key T'.Fr hσ y₂.1` as an intermediate fact. Rewrite `this` using `[hy₂]`. Conclude with `this`. Simplify using `only [h4]`.

Rewrite using `[eq_sub_of_add_eq h5.symm]`. Conclude with `Subring.sub_mem _ h1 h2`. Introduce `S _ _ _ h y`. Rewrite using `[key S h y, Fin.sum_univ_add]`. Simplify using `only [Fin.append_left, Fin.append_right]`.
-/
theorem supSet_descent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ), p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → l.GoodAt p → ∀ (c' : Coeff l) (hle : c.F ≤ c'.F) (la' : HeightOneSpectrum (𝓞 c'.F)), (∀ x : c.F, vLa la' (incF c c' hle x) = vLa la x) → CuspBC hle U → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → FiniteDimensional c.F (cusp Xo c U a n) → ∀ f' ∈ cusp Xo c' (unfBC hle U) a n, BddAll Xo c' la' 1 f' → ∃ (m : ℕ) (as : Fin m → c'.F) (fs : Fin m → Rul Xo c), (∀ i, la'.valuation c'.F (as i) ≤ 1) ∧ (∀ i, fs i ∈ supSet Xo c la (cusp Xo c U a n)) ∧ IsBC hle f' as fs := by
  intro E _ _ _ H Dw l Xo c r U hU la p hp hpl hgood c' hle la' hv hBC a n hD _ f' hf' hb
  obtain ⟨m, as, fs, hfs, hIs⟩ := hBC a n f' hf'
  choose κ hκ0 hκ using fun i => GlobalTheory.T.cuspidal_section_bounded_nonzero_multiple E H Dw l Xo c r U hU la p hp hpl hgood a n (fs i) hD (hfs i)
  letI : Algebra c.F c'.F := (incF c c' hle).toAlgebra
  have := liesOver (K := c.F) (K' := c'.F) hv
  obtain ⟨d, b, hb1, hb2⟩ := exists_residue_basis (la := la) (la' := la')
  choose x ρ hρ hx using fun i => exists_approx (K := c.F) (K' := c'.F) hv hb2 (as i) (hκ0 i)
  let F : Fin d → Rul Xo c := fun j => ∑ i, x i j • fs i
  have hF : ∀ j, F j ∈ cusp Xo c U a n := fun j => Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hfs i)
  have hG : ∀ i, κ i • fs i ∈ supSet Xo c la (cusp Xo c U a n) := fun i =>
    ⟨Submodule.smul_mem _ _ (hfs i), (GoodPtsModel.bddAll_iff_smul _ _).1 (hκ i)⟩
  have key : ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S) (y : FrPt Xo c' S),
      evR Xo c' f' y = ∑ j, algebraMap c'.F S (b j) * evR Xo c (F j) (y.res hle h) +
        ∑ i, algebraMap c'.F S (ρ i) * evR Xo c (κ i • fs i) (y.res hle h) := by
    intro S _ _ _ h y
    have h' : ∀ t : c.F, algebraMap c'.F S (algebraMap c.F c'.F t) = algebraMap c.F S t := h
    have hs : ∀ i, evR Xo c (κ i • fs i) (y.res hle h) = algebraMap c.F S (κ i) * evR Xo c (fs i) (y.res hle h) :=
      fun i => evalAt_smul _ _ _ _ _
    rw [hIs S h y]
    simp only [F, evR_sum, hs, Finset.mul_sum]
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hx i]
    simp only [map_add, map_sum, map_mul, h', add_mul, Finset.sum_mul, mul_assoc]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  refine ⟨d + m, Fin.append (fun j => (b j : c'.F)) ρ, Fin.append F fun i => κ i • fs i, fun i => ?_, fun i => ?_, ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]; exact la'.valuation_le_one (b j)
    · rw [Fin.append_right]; exact hρ j
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    swap
    · rw [Fin.append_right]; exact hG j
    rw [Fin.append_left]
    refine ⟨hF j, fun T io e ho y hy => ?_⟩
    rw [map_one, one_mul]
    refine inV_of_forall_emb (K := c.F) (K' := c'.F) hb1 hy ho (fun j => evI y (F j)) ?_ j
    intro T' i e' σ e'' he' hi hT' hσ ho'
    obtain ⟨y₁, φ, hφ, hmap⟩ := GlobalTheory.IntFrBaseChange.exists_intFr_baseChange E H Dw l Xo c T T' io y i e' he' hi
    obtain ⟨y₂, hy₂⟩ := exists_intFr_ext hle (io := i.comp io) σ hσ y₁
    have hi' : ∀ t : T.Fr, vV T'.V (i t) = (e' : ℤ) * vV T.V t := fun t => by
      by_cases h : t = 0
      · subst h; simp [vV]
      · exact hi t h
    have h1 := hb T' σ e'' ho' y₂ hT'
    rw [map_one, one_mul] at h1
    have h2 : InV T' (∑ k, σ (ρ k) * evI y₁ (κ k • fs k)) := Subring.sum_mem _ fun k _ => by
      have h3 := (hG k).2 T' _ _ (ho.bc i he' hi') y₁ hT'
      rw [map_one, one_mul] at h3
      exact Subring.mul_mem _ ((GoodPtsModel.inV_iff_val T' _).2 ((val_le_one_iff ho' _).2 (hρ k))) h3
    have h4 : ∀ j, i (evI y (F j)) = evI y₁ (F j) := fun j => by
      letI := io.toAlgebra
      letI := (i.comp io).toAlgebra
      exact (DFunLike.congr_fun hφ _).symm.trans
        (GlobalTheory.FlagTan.evR_frMap (cusp_le_sec Xo c U a n (hF j)).1 hmap).symm
    have h5 : evI y₂ f' = ∑ j, σ (b j) * evI y₁ (F j) + ∑ k, σ (ρ k) * evI y₁ (κ k • fs k) := by
      letI := (i.comp io).toAlgebra
      letI := σ.toAlgebra
      have := key T'.Fr hσ y₂.1
      rw [hy₂] at this
      exact this
    simp only [h4]
    rw [eq_sub_of_add_eq h5.symm]
    exact Subring.sub_mem _ h1 h2
  · intro S _ _ _ h y
    rw [key S h y, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]

end GlobalTheory.SupDescent
