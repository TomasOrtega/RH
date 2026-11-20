import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DescentOfPointsKilledStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinOEModPrimeLaurentFieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsResidueTiltInjectiveRetractStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFixFlatOfTiltMapsAgreeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfDivisibilityBreuilKisinFactsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityWittTiltAinf
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.TwoCopy

variable {l : ℕ} [hl : Fact l.Prime]

/- English proof (translation)
Use `haveI := GlobalTheory.FrobInt.valuationRing_tilt l`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Apply `hb` to reduce the goal to its premises. Use `hπ.haus b fun n => ?_` and prove the remaining obligations.

Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : π ^ n ∣ b := by`. Take `⟨c, hc | hc⟩` from `ValuationRing.cond b (π ^ n)`. Conclude with `absurd ⟨c, hc.symm⟩ (h n)`. Conclude with `⟨c, hc.symm⟩`. Rewrite using `[SModEq.zero, hc, ← smul_eq_mul]`.

Conclude with `Submodule.smul_mem_smul (by rw [Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton_self _) Submodule.mem_top`.
-/
theorem dvd_pow_of_ne_zero {π b : OCb l} (hπ : IsHausdorff (Ideal.span {π}) (OCb l)) (hb : b ≠ 0) :
    ∃ n : ℕ, b ∣ π ^ n := by
  haveI := GlobalTheory.FrobInt.valuationRing_tilt l
  by_contra h
  push_neg at h
  apply hb
  refine hπ.haus b fun n => ?_
  obtain ⟨c, hc⟩ : π ^ n ∣ b := by
    obtain ⟨c, hc | hc⟩ := ValuationRing.cond b (π ^ n)
    · exact absurd ⟨c, hc.symm⟩ (h n)
    · exact ⟨c, hc.symm⟩
  rw [SModEq.zero, hc, ← smul_eq_mul]
  exact Submodule.smul_mem_smul (by rw [Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton_self _)
    Submodule.mem_top

/- English proof (translation)
Take `⟨n, c, hc⟩` from `dvd_pow_of_ne_zero hπ hy`. Conclude with `isUnit_of_mul_isUnit_left (y := i c) (by rw [← map_mul, ← hc, map_pow]; exact hu.pow n)`.
-/
theorem isUnit_of_ne_zero {T : Type} [CommRing T] {π : OCb l} (hπ : IsHausdorff (Ideal.span {π}) (OCb l))
    (i : OCb l →+* T) (hu : IsUnit (i π)) (y : OCb l) (hy : y ≠ 0) : IsUnit (i y) := by
  obtain ⟨n, c, hc⟩ := dvd_pow_of_ne_zero hπ hy
  exact isUnit_of_mul_isUnit_left (y := i c) (by rw [← map_mul, ← hc, map_pow]; exact hu.pow n)

/- English proof (translation)
Assemble the required witnesses or components as `⟨IsLocalization.lift (M := nonZeroDivisors (OCb l)) (S := Cb l) (g := i) fun y => isUnit_of_ne_zero hπ i hu y (nonZeroDivisors.ne_zero y.2), fun y => IsLocalization.lift_eq _ y⟩`.
-/
theorem exists_ext {T : Type} [CommRing T] {π : OCb l} (hπ : IsHausdorff (Ideal.span {π}) (OCb l))
    (i : OCb l →+* T) (hu : IsUnit (i π)) :
    ∃ j : Cb l →+* T, ∀ y, j (algebraMap (OCb l) (Cb l) y) = i y :=
  ⟨IsLocalization.lift (M := nonZeroDivisors (OCb l)) (S := Cb l) (g := i)
      fun y => isUnit_of_ne_zero hπ i hu y (nonZeroDivisors.ne_zero y.2),
    fun y => IsLocalization.lift_eq _ y⟩

/- English proof (translation)
Take `⟨⟨a, b⟩, h⟩` from `IsLocalization.surj (nonZeroDivisors (OCb l)) x`. Take `⟨n, c, hc⟩` from `dvd_pow_of_ne_zero hπ (nonZeroDivisors.ne_zero b.2)`. Use `⟨n, c * a, ?_⟩` and prove the remaining obligations. Simplify using `only at h`. Rewrite using `[← map_pow, hc, map_mul, map_mul, ← h]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_clear {π : OCb l} (hπ : IsHausdorff (Ideal.span {π}) (OCb l)) (x : Cb l) :
    ∃ (n : ℕ) (y : OCb l), algebraMap (OCb l) (Cb l) π ^ n * x = algebraMap (OCb l) (Cb l) y := by
  obtain ⟨⟨a, b⟩, h⟩ := IsLocalization.surj (nonZeroDivisors (OCb l)) x
  obtain ⟨n, c, hc⟩ := dvd_pow_of_ne_zero hπ (nonZeroDivisors.ne_zero b.2)
  refine ⟨n, c * a, ?_⟩
  simp only at h
  rw [← map_pow, hc, map_mul, map_mul, ← h]
  ring

/- English proof (translation)
Use `choose n y hy using fun j => exists_clear hπ (x j)`. Use `⟨∑ j, n j, fun j => π ^ (∑ i, n i - n j) * y j, fun j => ?_⟩` and prove the remaining obligations. Establish `hle : n j ≤ ∑ i, n i` using `Finset.single_le_sum (fun i _ => Nat.zero_le (n i)) (Finset.mem_univ j)`. Rewrite using `[map_mul, ← hy j, map_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]`.
-/
theorem exists_clear_family {κ : Type} [Fintype κ] {π : OCb l} (hπ : IsHausdorff (Ideal.span {π}) (OCb l))
    (x : κ → Cb l) : ∃ (m : ℕ) (x' : κ → OCb l), ∀ j,
      algebraMap (OCb l) (Cb l) π ^ m * x j = algebraMap (OCb l) (Cb l) (x' j) := by
  choose n y hy using fun j => exists_clear hπ (x j)
  refine ⟨∑ j, n j, fun j => π ^ (∑ i, n i - n j) * y j, fun j => ?_⟩
  have hle : n j ≤ ∑ i, n i := Finset.single_le_sum (fun i _ => Nat.zero_le (n i)) (Finset.mem_univ j)
  rw [map_mul, ← hy j, map_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

/- English proof (translation)
Assemble the required witnesses or components as `⟨PowerSeries.mk fun n => WittVector.teichmuller l (PowerSeries.coeff n a), by ext n simp [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]⟩`.
-/
theorem map_constantCoeff_surj {F : Type} [CommRing F] (a : F⟦X⟧) :
    ∃ s : (WittVector l F)⟦X⟧, PowerSeries.map (WittVector.constantCoeff (p := l) (R := F)) s = a :=
  ⟨PowerSeries.mk fun n => WittVector.teichmuller l (PowerSeries.coeff n a), by
    ext n
    simp [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]⟩

end GlobalTheory.BSP.TwoCopy

namespace GlobalTheory.BSP.TwoCopy

/- English proof (translation)
Introduce `l _ K bk κ _ x hfix hφ`. Take `⟨ek, prA, hek, hinj, hpr, hpr1⟩` from `GlobalTheory.T.exists_residueTilt_injective_retract l K bk`. Take `⟨hoe, -⟩` from `GlobalTheory.T.breuilKisin_OE_mod_prime_laurent_field l K bk`. Take `⟨-, -, -, h0, -, hc, -⟩` from `GlobalTheory.T.ainf_divisibility_breuilKisin_facts l K bk`. Establish `hH : IsHausdorff (Ideal.span {bk.flat}) (OCb l)` using `hc.toIsHausdorff`.

Establish `hX : ek X = bk.flat`. Use `hek X` as an intermediate fact. Rewrite `this` using `[PowerSeries.map_X, bk.ev_X, WittVector.teichmuller_coeff_zero]`. Then use the resulting hypothesis. Take `⟨m, x', hx'⟩` from `exists_clear_family hH x`. Use `letI : Algebra (Fq l bk.a)⟦X⟧ (OCb l) := ek.toAlgebra`.

Establish `halg : ∀ a, algebraMap (Fq l bk.a)⟦X⟧ (OCb l) a = ek a` using `fun _ => rfl`. Use `haveI : Module.IsTorsionFree (Fq l bk.a)⟦X⟧ (OCb l) := by`. Rewrite using `[Module.isTorsionFree_iff_algebraMap_injective]`. Conclude with `hinj`. Set `pr : OCb l →ₗ[(Fq l bk.a)⟦X⟧] (Fq l bk.a)⟦X⟧` to `{ toFun := prA map_add' := prA.map_add map_smul' := fun a y => by rw [Algebra.smul_def, halg, hpr, RingHom.id_apply, smul_eq_mul] }`.

Establish `hEq : ∀ (T : Type) [CommRing T] (i₁ i₂ : OCb l →+* T), (∀ a, i₁ (algebraMap (Fq l bk.a)⟦X⟧ (OCb l) a) = i₂ (algebraMap (Fq l bk.a)⟦X⟧ (OCb l) a)) → IsUnit (i₁ (algebraMap (Fq l bk.a)⟦X⟧ (OCb l) X)) → ∃ c : κ → κ → T, ∀ j, i₁ (x' j) - i₂ (x' j) = ∑ i, (i₁ (x' i) - i₂ (x' i)) ^ l * …`. Introduce `T _ i₁ i₂ hag hu`. Establish `hag' : ∀ a, i₁ (ek a) = i₂ (ek a)` using `hag`. Rewrite `hu` using `[halg, hX]`. Establish `hf : i₁ bk.flat = i₂ bk.flat` using `by rw [← hX]; exact hag' X`.

Take `⟨j₁, hj₁⟩` from `exists_ext hH i₁ hu`. Take `⟨j₂, hj₂⟩` from `exists_ext hH i₂ (hf ▸ hu)`. Establish `hOE : ∀ y ∈ bk.OE.map (WittVector.constantCoeff (p` using `l) (R := Cb l)), j₁ y = j₂ y := by`. Introduce `y hy`. Take `⟨n, s, hs⟩` from `(hoe y).1 hy`.

Establish `hs' : i₁ ((bk.ev s).coeff 0) = i₂ ((bk.ev s).coeff 0)` using `by rw [← hek s]; exact hag' _`. Establish `e1` using `congrArg j₁ hs`. Establish `e2` using `congrArg j₂ hs`. Rewrite `e1` using `[map_mul, map_pow, hj₁, hj₁, hs']`. Rewrite `e2` using `[map_mul, map_pow, hj₂, hj₂, ← hf]`.

Conclude with `(hu.pow n).mul_left_cancel (e1.trans e2.symm)`. Take `⟨c, hc'⟩` from `hφ T j₁ j₂ hOE`. Take `⟨υ, hυ⟩` from `hu`. Use `⟨fun i j => c i j * (υ : T) ^ m * ((υ⁻¹ : Tˣ) : T) ^ (m * l), fun j => ?_⟩` and prove the remaining obligations. Establish `hx1 : ∀ i, i₁ (x' i) = (υ : T) ^ m * j₁ (x i)` using `fun i => by`.

Rewrite using `[← hj₁, ← hx' i, map_mul, map_pow, hj₁, ← hυ]`. Establish `hx2 : ∀ i, i₂ (x' i) = (υ : T) ^ m * j₂ (x i)` using `fun i => by`. Rewrite using `[← hj₂, ← hx' i, map_mul, map_pow, hj₂, ← hf, ← hυ]`. Establish `hinv : (υ : T) ^ (m * l) * ((υ⁻¹ : Tˣ) : T) ^ (m * l) = 1`. Rewrite using `[← mul_pow, Units.mul_inv, one_pow]`.

Simplify using `only [hx1, hx2]`. Rewrite using `[← mul_sub, hc' j, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_sub, mul_pow, ← pow_mul]`. Take the linear combination `(-((υ : T) ^ m * (j₁ (x i) - j₂ (x i)) ^ l * c i j)) * hinv`.

Establish `hPts : ∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (ψ ψ' : OCb l →+* O), ψ (algebraMap (Fq l bk.a)⟦X⟧ (OCb l) X) ≠ 0 → ¬ IsUnit (ψ (algebraMap (Fq l bk.a)⟦X⟧ (OCb l) X)) → IsAdicComplete (Ideal.span {ψ (algebraMap (Fq l bk.a)⟦X⟧ (OCb l) …`. Introduce `O _ _ _ _ _ ψ ψ' h1 h2 h3 hag j`. Rewrite `h1`, `h2`, `h3` using `[halg, hX]`. Establish `hag' : ∀ a, ψ (ek a) = ψ' (ek a)` using `hag`. Take `⟨g, hg, hψ⟩` from `GlobalTheory.T.exists_fixFlat_of_tilt_maps_agree l K bk O ψ h1 h2 h3 ψ' (fun s => by rw [← hek s]; exact hag' _)`.

Establish `hg' : Per.σF (g : GQ l) bk.flat = bk.flat` using `hg`. Rewrite using `[hψ]`. Use `congr 1`. Apply `IsFractionRing.injective (OCb l) (Cb l)` to reduce the goal to its premises. Rewrite using `[← galTilt_apply, ← autCb_alg, ← hx' j, map_mul, map_pow, autCb_alg, hfix g hg j, galTilt_apply, hg']`.

Establish `hnz : algebraMap (Fq l bk.a)⟦X⟧ (OCb l) X ∈ nonZeroDivisors (OCb l)`. Rewrite using `[halg, hX]`. Conclude with `mem_nonZeroDivisors_of_ne_zero h0`. Establish `hHX : IsHausdorff (Ideal.span {algebraMap (Fq l bk.a)⟦X⟧ (OCb l) X}) (OCb l)`. Rewrite using `[halg, hX]`.

Conclude with `hH`. Establish `key` using `GlobalTheory.T.descent_of_points_killed_alt l (Fq l bk.a)⟦X⟧ (OCb l) X pr (CharP.cast_eq_zero _ _) hnz hHX κ x' hEq hPts hpr1`. Introduce `j`. Take `⟨s, hs⟩` from `map_constantCoeff_surj (l := l) (prA (x' j))`. Use `(hoe (x j)).2 ⟨m, s, ?_⟩` and prove the remaining obligations.

Rewrite using `[hx' j, ← hek s, hs]`. Conclude with `congrArg _ (key j)`.
-/
theorem mem_reduction_of_invariant : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (κ : Type) [Fintype κ]
    (x : κ → Cb l), (∀ g : ↥(GK K), bk.FixFlat g → ∀ j, autCb l (galTilt l (g : GQ l)) (x j) = x j) →
    (∀ (T : Type) [CommRing T] (i₁ i₂ : Cb l →+* T),
      (∀ y ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)), i₁ y = i₂ y) →
      ∃ c : κ → κ → T, ∀ j, i₁ (x j) - i₂ (x j) = ∑ i, (i₁ (x i) - i₂ (x i)) ^ l * c i j) →
    ∀ j, x j ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)) := by
  intro l _ K bk κ _ x hfix hφ
  obtain ⟨ek, prA, hek, hinj, hpr, hpr1⟩ := GlobalTheory.T.exists_residueTilt_injective_retract l K bk
  obtain ⟨hoe, -⟩ := GlobalTheory.T.breuilKisin_OE_mod_prime_laurent_field l K bk
  obtain ⟨-, -, -, h0, -, hc, -⟩ := GlobalTheory.T.ainf_divisibility_breuilKisin_facts l K bk
  have hH : IsHausdorff (Ideal.span {bk.flat}) (OCb l) := hc.toIsHausdorff
  have hX : ek X = bk.flat := by
    have := hek X
    rwa [PowerSeries.map_X, bk.ev_X, WittVector.teichmuller_coeff_zero] at this
  obtain ⟨m, x', hx'⟩ := exists_clear_family hH x
  letI : Algebra (Fq l bk.a)⟦X⟧ (OCb l) := ek.toAlgebra
  have halg : ∀ a, algebraMap (Fq l bk.a)⟦X⟧ (OCb l) a = ek a := fun _ => rfl
  haveI : Module.IsTorsionFree (Fq l bk.a)⟦X⟧ (OCb l) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; exact hinj
  let pr : OCb l →ₗ[(Fq l bk.a)⟦X⟧] (Fq l bk.a)⟦X⟧ :=
    { toFun := prA
      map_add' := prA.map_add
      map_smul' := fun a y => by rw [Algebra.smul_def, halg, hpr, RingHom.id_apply, smul_eq_mul] }
  have hEq : ∀ (T : Type) [CommRing T] (i₁ i₂ : OCb l →+* T),
      (∀ a, i₁ (algebraMap (Fq l bk.a)⟦X⟧ (OCb l) a) = i₂ (algebraMap (Fq l bk.a)⟦X⟧ (OCb l) a)) →
      IsUnit (i₁ (algebraMap (Fq l bk.a)⟦X⟧ (OCb l) X)) →
      ∃ c : κ → κ → T, ∀ j, i₁ (x' j) - i₂ (x' j) = ∑ i, (i₁ (x' i) - i₂ (x' i)) ^ l * c i j := by
    intro T _ i₁ i₂ hag hu
    have hag' : ∀ a, i₁ (ek a) = i₂ (ek a) := hag
    rw [halg, hX] at hu
    have hf : i₁ bk.flat = i₂ bk.flat := by rw [← hX]; exact hag' X
    obtain ⟨j₁, hj₁⟩ := exists_ext hH i₁ hu
    obtain ⟨j₂, hj₂⟩ := exists_ext hH i₂ (hf ▸ hu)
    have hOE : ∀ y ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)), j₁ y = j₂ y := by
      intro y hy
      obtain ⟨n, s, hs⟩ := (hoe y).1 hy
      have hs' : i₁ ((bk.ev s).coeff 0) = i₂ ((bk.ev s).coeff 0) := by rw [← hek s]; exact hag' _
      have e1 := congrArg j₁ hs
      have e2 := congrArg j₂ hs
      rw [map_mul, map_pow, hj₁, hj₁, hs'] at e1
      rw [map_mul, map_pow, hj₂, hj₂, ← hf] at e2
      exact (hu.pow n).mul_left_cancel (e1.trans e2.symm)
    obtain ⟨c, hc'⟩ := hφ T j₁ j₂ hOE
    obtain ⟨υ, hυ⟩ := hu
    refine ⟨fun i j => c i j * (υ : T) ^ m * ((υ⁻¹ : Tˣ) : T) ^ (m * l), fun j => ?_⟩
    have hx1 : ∀ i, i₁ (x' i) = (υ : T) ^ m * j₁ (x i) := fun i => by
      rw [← hj₁, ← hx' i, map_mul, map_pow, hj₁, ← hυ]
    have hx2 : ∀ i, i₂ (x' i) = (υ : T) ^ m * j₂ (x i) := fun i => by
      rw [← hj₂, ← hx' i, map_mul, map_pow, hj₂, ← hf, ← hυ]
    have hinv : (υ : T) ^ (m * l) * ((υ⁻¹ : Tˣ) : T) ^ (m * l) = 1 := by
      rw [← mul_pow, Units.mul_inv, one_pow]
    simp only [hx1, hx2]
    rw [← mul_sub, hc' j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_sub, mul_pow, ← pow_mul]
    linear_combination (-((υ : T) ^ m * (j₁ (x i) - j₂ (x i)) ^ l * c i j)) * hinv
  have hPts : ∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l]
      (ψ ψ' : OCb l →+* O), ψ (algebraMap (Fq l bk.a)⟦X⟧ (OCb l) X) ≠ 0 →
      ¬ IsUnit (ψ (algebraMap (Fq l bk.a)⟦X⟧ (OCb l) X)) →
      IsAdicComplete (Ideal.span {ψ (algebraMap (Fq l bk.a)⟦X⟧ (OCb l) X)}) O →
      (∀ a, ψ (algebraMap (Fq l bk.a)⟦X⟧ (OCb l) a) = ψ' (algebraMap (Fq l bk.a)⟦X⟧ (OCb l) a)) →
      ∀ j, ψ (x' j) = ψ' (x' j) := by
    intro O _ _ _ _ _ ψ ψ' h1 h2 h3 hag j
    rw [halg, hX] at h1 h2 h3
    have hag' : ∀ a, ψ (ek a) = ψ' (ek a) := hag
    obtain ⟨g, hg, hψ⟩ := GlobalTheory.T.exists_fixFlat_of_tilt_maps_agree l K bk O ψ h1 h2 h3 ψ' (fun s => by rw [← hek s]; exact hag' _)
    have hg' : Per.σF (g : GQ l) bk.flat = bk.flat := hg
    rw [hψ]
    congr 1
    apply IsFractionRing.injective (OCb l) (Cb l)
    rw [← galTilt_apply, ← autCb_alg, ← hx' j, map_mul, map_pow, autCb_alg, hfix g hg j, galTilt_apply, hg']
  have hnz : algebraMap (Fq l bk.a)⟦X⟧ (OCb l) X ∈ nonZeroDivisors (OCb l) := by
    rw [halg, hX]; exact mem_nonZeroDivisors_of_ne_zero h0
  have hHX : IsHausdorff (Ideal.span {algebraMap (Fq l bk.a)⟦X⟧ (OCb l) X}) (OCb l) := by
    rw [halg, hX]; exact hH
  have key := GlobalTheory.T.descent_of_points_killed_alt l (Fq l bk.a)⟦X⟧ (OCb l) X pr (CharP.cast_eq_zero _ _) hnz hHX κ x' hEq hPts hpr1
  intro j
  obtain ⟨s, hs⟩ := map_constantCoeff_surj (l := l) (prA (x' j))
  refine (hoe (x j)).2 ⟨m, s, ?_⟩
  rw [hx' j, ← hek s, hs]
  exact congrArg _ (key j)

end GlobalTheory.BSP.TwoCopy
