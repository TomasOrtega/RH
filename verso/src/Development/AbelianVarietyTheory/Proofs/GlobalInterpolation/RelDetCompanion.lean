import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DetIdNormOneMul
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPrimeUnder

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

noncomputable section

namespace GlobalTheory.MomT.ChiMove

open GlobalTheory.CharValCompare GlobalTheory.RelDetIdeal GlobalTheory.IdealTransport

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

omit [StarRing E] in
/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simpa using hsm 0 0 M.zero_mem`. Consider the case `insert k S hk ih`. Rewrite using `[Finset.sum_insert hk, Finset.sum_insert hk, hadd _ (M.smul_mem _ (hv k)) _ (M.sum_mem fun i _ => M.smul_mem _ (hv i)), hsm _ _ (hv k), ih]`.
-/
theorem functional_sum {P : HeightOneSpectrum (𝓞 E)} (M : Submodule (𝓞 E) (Sp E n)) (φ : Sp E n → 𝓞 E ⧸ P.asIdeal)
    (hadd : ∀ x ∈ M, ∀ y ∈ M, φ (x + y) = φ x + φ y)
    (hsm : ∀ (a : 𝓞 E), ∀ x ∈ M, φ (a • x) = Ideal.Quotient.mk P.asIdeal a * φ x)
    {ι : Type} (S : Finset ι) (r : ι → 𝓞 E) (v : ι → Sp E n) (hv : ∀ i, v i ∈ M) :
    φ (∑ i ∈ S, r i • v i) = ∑ i ∈ S, Ideal.Quotient.mk P.asIdeal (r i) * φ (v i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using hsm 0 0 M.zero_mem
  | insert k S hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk,
      hadd _ (M.smul_mem _ (hv k)) _ (M.sum_mem fun i _ => M.smul_mem _ (hv i)), hsm _ _ (hv k), ih]

/- English proof (translation)
Use `choose c hc using fun i : Fin n => Ideal.Quotient.mk_surjective (φ (f (Pi.single i 1)))`. Use `⟨c, fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨s, hs, hsz⟩` from `(mem_locP P _ _).1 hz`. Use `choose r hr using (mem_stdLat _).1 hsz`. Establish `h1 : s • f z = ∑ i, r i • f (Pi.single i 1)`.

Rewrite using `[← algebraMap_smul E s, ← map_smul]`. Simplify using `only [← algebraMap_smul E (r _), ← map_smul, ← map_sum]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Simplify using `[Finset.sum_apply, Pi.single_apply, hr, Algebra.smul_def]`.

Establish `h2 : Ideal.Quotient.mk P.asIdeal s * φ (f z) = Ideal.Quotient.mk P.asIdeal (∑ i, r i * c i)`. Rewrite using `[← hsm s _ ((hf z).2 hz), h1, functional_sum _ φ hadd hsm _ _ _ fun i => (hf _).2 (single_mem_stdAt P i)]`. Simplify using `[hc]`. Establish `h3 : algebraMap (𝓞 E) E (∑ i, r i * c i) = algebraMap (𝓞 E) E s * ∑ i, algebraMap (𝓞 E) E (c i) * z i`. Rewrite using `[map_sum, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, hr, Pi.smul_apply, Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree. Establish `h4 : P.valuation E (∑ i, algebraMap (𝓞 E) E (c i) * z i) = P.intValuation (∑ i, r i * c i)`. Use `congrArg (P.valuation E) h3` as an intermediate fact.

Rewrite `this` using `[Valuation.map_mul, val_of_notMem hs, one_mul, HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `this.symm`. Establish `h5` using `P.intValuation_le_pow_iff_mem (∑ i, r i * c i) 1`. Establish `h6 : Ideal.Quotient.mk P.asIdeal s ≠ 0` using `fun h => hs (Ideal.Quotient.eq_zero_iff_mem.1 h)`. Use `haveI := P.isPrime`.

Rewrite using `[h4, ← mul_eq_zero_iff_left h6, h2, Ideal.Quotient.eq_zero_iff_mem]`. Simplify using `using h5.symm`.
-/
theorem functional_frame {P : HeightOneSpectrum (𝓞 E)} {N : Submodule (𝓞 E) (Sp E n)} {f : Sp E n ≃ₗ[E] Sp E n}
    (hf : IsFr P N f) (φ : Sp E n → 𝓞 E ⧸ P.asIdeal)
    (hadd : ∀ x ∈ localization₂ P.asIdeal N, ∀ y ∈ localization₂ P.asIdeal N, φ (x + y) = φ x + φ y)
    (hsm : ∀ (a : 𝓞 E), ∀ x ∈ localization₂ P.asIdeal N, φ (a • x) = Ideal.Quotient.mk P.asIdeal a * φ x) :
    ∃ c : Fin n → 𝓞 E, ∀ z ∈ stdAt E n P,
      φ (f z) = 0 ↔ P.valuation E (∑ i, algebraMap (𝓞 E) E (c i) * z i) ≤ WithZero.exp (-1 : ℤ) := by
  classical
  choose c hc using fun i : Fin n => Ideal.Quotient.mk_surjective (φ (f (Pi.single i 1)))
  refine ⟨c, fun z hz => ?_⟩
  obtain ⟨s, hs, hsz⟩ := (mem_locP P _ _).1 hz
  choose r hr using (mem_stdLat _).1 hsz
  have h1 : s • f z = ∑ i, r i • f (Pi.single i 1) := by
    rw [← algebraMap_smul E s, ← map_smul]
    simp only [← algebraMap_smul E (r _), ← map_smul, ← map_sum]
    congr 1
    funext j
    simp [Finset.sum_apply, Pi.single_apply, hr, Algebra.smul_def]
  have h2 : Ideal.Quotient.mk P.asIdeal s * φ (f z) = Ideal.Quotient.mk P.asIdeal (∑ i, r i * c i) := by
    rw [← hsm s _ ((hf z).2 hz), h1, functional_sum _ φ hadd hsm _ _ _ fun i => (hf _).2 (single_mem_stdAt P i)]
    simp [hc]
  have h3 : algebraMap (𝓞 E) E (∑ i, r i * c i) = algebraMap (𝓞 E) E s * ∑ i, algebraMap (𝓞 E) E (c i) * z i := by
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hr, Pi.smul_apply, Algebra.smul_def]
    ring
  have h4 : P.valuation E (∑ i, algebraMap (𝓞 E) E (c i) * z i) = P.intValuation (∑ i, r i * c i) := by
    have := congrArg (P.valuation E) h3
    rw [Valuation.map_mul, val_of_notMem hs, one_mul, HeightOneSpectrum.valuation_of_algebraMap] at this
    exact this.symm
  have h5 := P.intValuation_le_pow_iff_mem (∑ i, r i * c i) 1
  have h6 : Ideal.Quotient.mk P.asIdeal s ≠ 0 := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.1 h)
  haveI := P.isPrime
  rw [h4, ← mul_eq_zero_iff_left h6, h2, Ideal.Quotient.eq_zero_iff_mem]
  simpa using h5.symm

/- English proof (translation)
Take `⟨c, hc⟩` from `functional_frame hf φ hadd hsm`. Establish `hstd : ∀ z : Sp E n, z ∈ stdAt E n P ↔ ∀ i, P.valuation E (z i) ≤ 1` using `fun z => by`. Rewrite using `[stdAt, mem_localization_standardLattice]`. Simplify using `only [intAt_iff]`. Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, c j ∉ P.asIdeal := by`.

Assume the negation of the conclusion as `H`. Use `push Not at H`. Take `⟨x, hx, hx0⟩` from `hne`. Take `⟨z, rfl⟩` from `f.surjective x`. Establish `hz` using `(hf z).1 (le_locP P _ hx)`.

Use `hx0 ((hc z hz).2 (Valuation.map_sum_le _ fun i _ => ?_))` and prove the remaining obligations. Rewrite using `[map_mul, HeightOneSpectrum.valuation_of_algebraMap]`. Use `(P.intValuation_le_pow_iff_mem (c i) 1).2 (by simpa using H i)` as an intermediate fact. Conclude with `(mul_le_of_le_one_right' ((hstd z).1 hz i)).trans (by simpa using this)`. Take `⟨π, hπ⟩` from `P.valuation_exists_uniformizer E`.

Establish `hπ0 : π ≠ 0` using `by rintro rfl; rw [map_zero] at hπ; exact WithZero.exp_ne_zero hπ.symm`. Set `M : Matrix (Fin n) (Fin n) E` to `(1 : Matrix (Fin n) (Fin n) E).updateRow j fun i => algebraMap (𝓞 E) E (c i) / π`. Establish `hM : M.det = algebraMap (𝓞 E) E (c j) / π`. Use `Matrix.det_updateRow_sum (1 : Matrix (Fin n) (Fin n) E) j fun i => algebraMap (𝓞 E) E (c i) / π` as an intermediate fact. Rewrite `this` using `[Matrix.det_one, smul_eq_mul, mul_one]`.

Rewrite using `[← this]`. Use `congrArg (fun v => Matrix.det (Matrix.updateRow 1 j v)) (funext fun k => ?_)` and prove the remaining obligations. Simplify using `[Finset.sum_apply, Matrix.one_apply]`. Establish `hMj : ∀ z, M.mulVec z j = (∑ i, algebraMap (𝓞 E) E (c i) * z i) / π` using `fun z => by`. Simplify using `only [M, Matrix.mulVec, dotProduct, Matrix.updateRow_self, Finset.sum_div]`.

Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Establish `hMi : ∀ z i, i ≠ j → M.mulVec z i = z i` using `fun z i hi => by`. Simplify using `[M, Matrix.mulVec, dotProduct, Matrix.updateRow_ne hi, Matrix.one_apply]`. Establish `hle : ∀ a : E, P.valuation E (a / π) ≤ 1 ↔ P.valuation E a ≤ WithZero.exp (-1 : ℤ)` using `fun a => by`. Rewrite using `[map_div₀, div_le_one₀ (val_pos hπ0), hπ]`.

Establish `key : ∀ z, M.mulVec z ∈ stdAt E n P ↔ f z ∈ localization₂ P.asIdeal N''`. Introduce `z`. Rewrite using `[hker, hf]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Rewrite `h` using `[hstd]`. Establish `h1` using `h j`. Rewrite `h1` using `[hMj, hle]`. Establish `hz : z ∈ stdAt E n P`. Rewrite using `[hstd]`.

Introduce `i`. Distinguish the cases in `hi : i = j`. Substitute `hi` using the available equality. Establish `h2 : algebraMap (𝓞 E) E (c i) * z i = ∑ k, algebraMap (𝓞 E) E (c k) * z k - ∑ k ∈ Finset.univ.erase i, algebraMap (𝓞 E) E (c k) * z k`. Rewrite using `[← Finset.add_sum_erase _ _ (Finset.mem_univ i)]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h3 : P.valuation E (algebraMap (𝓞 E) E (c i) * z i) ≤ 1`. Rewrite using `[h2]`. Use `Valuation.map_sub_le _ (h1.trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)) (Valuation.map_sum_le _ fun k hk => ?_)` and prove the remaining obligations. Rewrite using `[map_mul]`.

Conclude with `mul_le_one' (P.valuation_le_one _) (hMi z k (Finset.ne_of_mem_erase hk) ▸ h k)`. Rewrite `h3` using `[map_mul, val_of_notMem hj, one_mul]`. Then use the resulting hypothesis. Conclude with `hMi z i hi ▸ h i`. Conclude with `⟨hz, (hc z hz).2 h1⟩`. Introduce and unpack `⟨hz, h0⟩`.

Rewrite using `[hstd]`. Introduce `i`. Distinguish the cases in `hi : i = j`. Rewrite using `[hi, hMj, hle]`. Conclude with `(hc z hz).1 h0`.

Rewrite using `[hMi z i hi]`. Conclude with `(hstd z).1 hz i`. Establish `hd : LinearMap.det (Matrix.toLin' M ∘ₗ (f.symm : Sp E n →ₗ[E] Sp E n) ∘ₗ (f'' : Sp E n →ₗ[E] Sp E n)) = algebraMap (𝓞 E) E (c j) / π * (dt f'' / dt f)`. Establish `h3` using `LinearEquiv.det_mul_det_symm f`. Establish `h4` using `dt_ne f`.

Rewrite using `[LinearMap.det_comp, LinearMap.det_comp, LinearMap.det_toLin', hM, ← dt_eq f'']`. Rewrite `h3` using `[← dt_eq f]`. Use `congr 1`. Rewrite using `[eq_div_iff h4]`. Take the linear combination `dt f'' * h3`.

Establish `hv` using `val_of_notMem (E := E) hj`. Establish `h0 : LinearMap.det (Matrix.toLin' M ∘ₗ (f.symm : Sp E n →ₗ[E] Sp E n) ∘ₗ (f'' : Sp E n →ₗ[E] Sp E n)) ≠ 0`. Rewrite using `[hd]`. Use `mul_ne_zero (div_ne_zero ?_ hπ0) (div_ne_zero (dt_ne _) (dt_ne _))` and prove the remaining obligations. Introduce `h`.

Simplify using `[h] at hv`. Establish `h1 : P.valuation E (algebraMap (𝓞 E) E (c j) / π * (dt f'' / dt f)) = 1`. Rewrite using `[← hd]`. Conclude with `val_det_eq_one (P := P) (LinearMap.equivOfDetNeZero _ h0) fun x => by`. Rewrite using `[← hf'' x]`.

Use `key (f.symm (f'' x))` as an intermediate fact. Rewrite `this` using `[LinearEquiv.apply_symm_apply]`. Conclude with `this`. Rewrite `h1` using `[map_mul, map_div₀ _ _ π, hv, hπ, one_div, inv_mul_eq_one₀ WithZero.exp_ne_zero]`. Conclude with `h1.symm`.
-/
theorem val_det_ker {P : HeightOneSpectrum (𝓞 E)} {N N'' : Submodule (𝓞 E) (Sp E n)} {f f'' : Sp E n ≃ₗ[E] Sp E n}
    (hf : IsFr P N f) (hf'' : IsFr P N'' f'') (φ : Sp E n → 𝓞 E ⧸ P.asIdeal)
    (hadd : ∀ x ∈ localization₂ P.asIdeal N, ∀ y ∈ localization₂ P.asIdeal N, φ (x + y) = φ x + φ y)
    (hsm : ∀ (a : 𝓞 E), ∀ x ∈ localization₂ P.asIdeal N, φ (a • x) = Ideal.Quotient.mk P.asIdeal a * φ x)
    (hne : ∃ x ∈ N, φ x ≠ 0) (hker : ∀ y, y ∈ localization₂ P.asIdeal N'' ↔ y ∈ localization₂ P.asIdeal N ∧ φ y = 0) :
    P.valuation E (dt f'' / dt f) = WithZero.exp (-1 : ℤ) := by
  classical
  obtain ⟨c, hc⟩ := functional_frame hf φ hadd hsm
  have hstd : ∀ z : Sp E n, z ∈ stdAt E n P ↔ ∀ i, P.valuation E (z i) ≤ 1 := fun z => by
    rw [stdAt, mem_localization_standardLattice]
    simp only [intAt_iff]
  obtain ⟨j, hj⟩ : ∃ j, c j ∉ P.asIdeal := by
    by_contra H
    push Not at H
    obtain ⟨x, hx, hx0⟩ := hne
    obtain ⟨z, rfl⟩ := f.surjective x
    have hz := (hf z).1 (le_locP P _ hx)
    refine hx0 ((hc z hz).2 (Valuation.map_sum_le _ fun i _ => ?_))
    rw [map_mul, HeightOneSpectrum.valuation_of_algebraMap]
    have := (P.intValuation_le_pow_iff_mem (c i) 1).2 (by simpa using H i)
    exact (mul_le_of_le_one_right' ((hstd z).1 hz i)).trans (by simpa using this)
  obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer E
  have hπ0 : π ≠ 0 := by rintro rfl; rw [map_zero] at hπ; exact WithZero.exp_ne_zero hπ.symm
  let M : Matrix (Fin n) (Fin n) E := (1 : Matrix (Fin n) (Fin n) E).updateRow j fun i => algebraMap (𝓞 E) E (c i) / π
  have hM : M.det = algebraMap (𝓞 E) E (c j) / π := by
    have := Matrix.det_updateRow_sum (1 : Matrix (Fin n) (Fin n) E) j fun i => algebraMap (𝓞 E) E (c i) / π
    rw [Matrix.det_one, smul_eq_mul, mul_one] at this
    rw [← this]
    refine congrArg (fun v => Matrix.det (Matrix.updateRow 1 j v)) (funext fun k => ?_)
    simp [Finset.sum_apply, Matrix.one_apply]
  have hMj : ∀ z, M.mulVec z j = (∑ i, algebraMap (𝓞 E) E (c i) * z i) / π := fun z => by
    simp only [M, Matrix.mulVec, dotProduct, Matrix.updateRow_self, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hMi : ∀ z i, i ≠ j → M.mulVec z i = z i := fun z i hi => by
    simp [M, Matrix.mulVec, dotProduct, Matrix.updateRow_ne hi, Matrix.one_apply]
  have hle : ∀ a : E, P.valuation E (a / π) ≤ 1 ↔ P.valuation E a ≤ WithZero.exp (-1 : ℤ) := fun a => by
    rw [map_div₀, div_le_one₀ (val_pos hπ0), hπ]
  have key : ∀ z, M.mulVec z ∈ stdAt E n P ↔ f z ∈ localization₂ P.asIdeal N'' := by
    intro z
    rw [hker, hf]
    constructor
    · intro h
      rw [hstd] at h
      have h1 := h j
      rw [hMj, hle] at h1
      have hz : z ∈ stdAt E n P := by
        rw [hstd]
        intro i
        by_cases hi : i = j
        · subst hi
          have h2 : algebraMap (𝓞 E) E (c i) * z i =
              ∑ k, algebraMap (𝓞 E) E (c k) * z k - ∑ k ∈ Finset.univ.erase i, algebraMap (𝓞 E) E (c k) * z k := by
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]; ring
          have h3 : P.valuation E (algebraMap (𝓞 E) E (c i) * z i) ≤ 1 := by
            rw [h2]
            refine Valuation.map_sub_le _ (h1.trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega))
              (Valuation.map_sum_le _ fun k hk => ?_)
            rw [map_mul]
            exact mul_le_one' (P.valuation_le_one _) (hMi z k (Finset.ne_of_mem_erase hk) ▸ h k)
          rwa [map_mul, val_of_notMem hj, one_mul] at h3
        · exact hMi z i hi ▸ h i
      exact ⟨hz, (hc z hz).2 h1⟩
    · rintro ⟨hz, h0⟩
      rw [hstd]
      intro i
      by_cases hi : i = j
      · rw [hi, hMj, hle]
        exact (hc z hz).1 h0
      · rw [hMi z i hi]
        exact (hstd z).1 hz i
  have hd : LinearMap.det (Matrix.toLin' M ∘ₗ (f.symm : Sp E n →ₗ[E] Sp E n) ∘ₗ (f'' : Sp E n →ₗ[E] Sp E n)) =
      algebraMap (𝓞 E) E (c j) / π * (dt f'' / dt f) := by
    have h3 := LinearEquiv.det_mul_det_symm f
    have h4 := dt_ne f
    rw [LinearMap.det_comp, LinearMap.det_comp, LinearMap.det_toLin', hM, ← dt_eq f'']
    rw [← dt_eq f] at h3
    congr 1
    rw [eq_div_iff h4]
    linear_combination dt f'' * h3
  have hv := val_of_notMem (E := E) hj
  have h0 : LinearMap.det (Matrix.toLin' M ∘ₗ (f.symm : Sp E n →ₗ[E] Sp E n) ∘ₗ (f'' : Sp E n →ₗ[E] Sp E n)) ≠ 0 := by
    rw [hd]
    refine mul_ne_zero (div_ne_zero ?_ hπ0) (div_ne_zero (dt_ne _) (dt_ne _))
    intro h
    simp [h] at hv
  have h1 : P.valuation E (algebraMap (𝓞 E) E (c j) / π * (dt f'' / dt f)) = 1 := by
    rw [← hd]
    exact val_det_eq_one (P := P) (LinearMap.equivOfDetNeZero _ h0) fun x => by
      rw [← hf'' x]
      have := key (f.symm (f'' x))
      rw [LinearEquiv.apply_symm_apply] at this
      exact this
  rw [map_mul, map_div₀ _ _ π, hv, hπ, one_div, inv_mul_eq_one₀ WithZero.exp_ne_zero] at h1
  exact h1.symm

omit [StarRing E] in
/- English proof (translation)
Rewrite using `[HeightOneSpectrum.valuation_of_algebraMap]`. Establish `h0 : a ≠ 0` using `by rintro rfl; exact h2 (zero_mem _)`. Establish `e1` using `(P.intValuation_le_pow_iff_mem a 1).2 (by simpa using h1)`. Establish `e2` using `(P.intValuation_le_pow_iff_mem a 2).not.2 h2`. Rewrite `e1`, `e2` using `[← WithZero.exp_log (P.intValuation_ne_zero a h0), WithZero.exp_le_exp]`.

Rewrite using `[← WithZero.exp_log (P.intValuation_ne_zero a h0)]`. Use `congr 1`. Move the coercions through the operations in `at e1 e2`. Use linear arithmetic over natural numbers and integers.
-/
theorem val_of_simple {P : HeightOneSpectrum (𝓞 E)} {a : 𝓞 E} (h1 : a ∈ P.asIdeal) (h2 : a ∉ P.asIdeal ^ 2) :
    P.valuation E (algebraMap (𝓞 E) E a) = WithZero.exp (-1 : ℤ) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  have h0 : a ≠ 0 := by rintro rfl; exact h2 (zero_mem _)
  have e1 := (P.intValuation_le_pow_iff_mem a 1).2 (by simpa using h1)
  have e2 := (P.intValuation_le_pow_iff_mem a 2).not.2 h2
  rw [← WithZero.exp_log (P.intValuation_ne_zero a h0), WithZero.exp_le_exp] at e1 e2
  rw [← WithZero.exp_log (P.intValuation_ne_zero a h0)]
  congr 1
  push_cast at e1 e2
  omega

/- English proof (translation)
Establish `hN : IsSdLat d.1.N` using `⟨d.2.lat, d.2.uni⟩`. Use `choose f hf using fun P => exists_isFr P hN.1`. Use `choose f'' hf'' using fun P => exists_isFr P hN''.1`. Establish `hϖ : (ϖ : E) ≠ 0` using `by simpa using h0`. Establish `hϖ' : star (ϖ : E) ≠ 0` using `star_ne_zero.2 hϖ`.

Establish `hnot : ∀ P : HeightOneSpectrum (𝓞 E), ϖ ∈ P.asIdeal → cO E ϖ ∉ P.asIdeal` using `fun P a b => by`. Take `⟨u, v, e⟩` from `hcop`. Conclude with `one_notMem P (e ▸ add_mem (P.asIdeal.mul_mem_left _ a) (P.asIdeal.mul_mem_left _ b))`. Establish `hA : ∀ P : HeightOneSpectrum (𝓞 E), ϖ ∈ P.asIdeal → P.valuation E (dt (f'' P) / dt (f P)) = P.valuation E (ϖ : E)` using `fun P hP => by`. Establish `hP'` using `(mem_divs h0 P).2 hP`.

Rewrite using `[val_det_ker (hf P) (hf'' P) (d.1.f ⟨P, hP'⟩) (d.2.f_add ⟨P, hP'⟩) (d.2.f_smul ⟨P, hP'⟩) (d.2.f_ne ⟨P, hP'⟩) (h3 ⟨P, hP'⟩)]`. Conclude with `(val_of_simple hP (hsq P hP')).symm`. Use `eq_of_gen _ (fun _ => (ϖ : E) / star (ϖ : E)) (fun P => gen_relDet hN.1.fg (hf P) (hf'' P)) (fun P => gen_of (div_ne_zero hϖ hϖ') (le_locP P _ (Submodule.mem_span_singleton_self _)) (GlobalTheory.CharVal.maxV_span_singleton _).1) fun P => ?_` and prove the remaining obligations. Distinguish the cases in `hP : ϖ ∈ P.asIdeal`. Establish `: P.valuation E (star (ϖ : E)) = 1` using `val_of_notMem (hnot P hP)`.

Rewrite using `[hA P hP, map_div₀, this, div_one]`. Establish `hv : P.valuation E (ϖ : E) = 1` using `val_of_notMem hP`. Distinguish the cases in `hP' : cO E ϖ ∈ P.asIdeal`. Establish `e1` using `hA (conjPrime₂ P) ((mem_conjP P ϖ).2 hP')`. Establish `e2 : (conjPrime₂ P).valuation E (dt (f'' (conjPrime₂ P)) / dt (f (conjPrime₂ P)) / (ϖ : E)) = 1`.

Rewrite using `[map_div₀, e1, div_self (val_pos hϖ).ne']`. Establish `e3` using `val_star_eq_one e2`. Establish `e4` using `val_dual hN (hf (conjPrime₂ P)) (f' := f P) (by rw [conjP_conjP]; exact hf P)`. Establish `e5` using `val_dual hN'' (hf'' (conjPrime₂ P)) (f' := f'' P) (by rw [conjP_conjP]; exact hf'' P)`. Rewrite `e3`, `e4`, `e5` using `[conjP_conjP]`.

Establish `e6 : dt (f'' P) / dt (f P) = (star (dt (f'' (conjPrime₂ P))) * dt (f'' P)) / (star (dt (f (conjPrime₂ P))) * dt (f P)) / star (dt (f'' (conjPrime₂ P)) / dt (f (conjPrime₂ P)) / (ϖ : E)) / star (ϖ : E)`. Use `star_ne_zero.2 (dt_ne (f'' (conjPrime₂ P)))` as an intermediate fact. Use `star_ne_zero.2 (dt_ne (f (conjPrime₂ P)))` as an intermediate fact. Use `dt_ne (f P)` as an intermediate fact. Rewrite using `[star_div₀, star_div₀]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[e6, map_div₀, map_div₀, map_div₀, e3, e4, e5, map_div₀, hv]`. Simplify using the standard rewrite rules. Establish `hv' : P.valuation E (star (ϖ : E)) = 1` using `val_of_notMem hP'`. Establish `e : IsFr P N'' (f P)` using `fun x => by`.

Rewrite using `[← hf P x, mem_locP, mem_locP]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs, h⟩`. Use `⟨cO E ϖ * s, fun hm => (P.isPrime.mem_or_mem hm).elim hP' hs, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul, ← algebraMap_smul E (cO E ϖ)]`.

Conclude with `h2 _ h`. Introduce and unpack `⟨s, hs, h⟩`. Use `⟨ϖ * s, fun hm => (P.isPrime.mem_or_mem hm).elim hP hs, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul, ← algebraMap_smul E ϖ]`. Conclude with `h1 _ h`.

Rewrite using `[map_div₀, map_div₀, hv, hv', (gen_detI e).val_eq (gen_detI (hf'' P)), div_self (val_pos (dt_ne _)).ne', div_one]`.
-/
theorem relDet_companion {SG : Finset (HeightOneSpectrum (𝓞 E))} {ϖ : 𝓞 E} (d : DecoSet E n (divs ϖ) SG)
    {N'' : Submodule (𝓞 E) (Sp E n)} (h0 : ϖ ≠ 0) (hcop : IsCoprime ϖ (cO E ϖ)) (hsq : ∀ P ∈ divs ϖ, ϖ ∉ P.asIdeal ^ 2)
    (hN'' : IsSdLat N'') (h1 : ∀ y ∈ d.1.N, (ϖ : E) • y ∈ N'') (h2 : ∀ y ∈ N'', star (ϖ : E) • y ∈ d.1.N)
    (h3 : ∀ (P : ↥(divs ϖ)) (y : Sp E n), y ∈ localization₂ P.1.asIdeal N'' ↔ y ∈ d.1.at P.1 ∧ d.1.f P y = 0) :
    relDet d.1.N N'' = Submodule.span (𝓞 E) {(ϖ : E) / star (ϖ : E)} := by
  have hN : IsSdLat d.1.N := ⟨d.2.lat, d.2.uni⟩
  choose f hf using fun P => exists_isFr P hN.1
  choose f'' hf'' using fun P => exists_isFr P hN''.1
  have hϖ : (ϖ : E) ≠ 0 := by simpa using h0
  have hϖ' : star (ϖ : E) ≠ 0 := star_ne_zero.2 hϖ
  have hnot : ∀ P : HeightOneSpectrum (𝓞 E), ϖ ∈ P.asIdeal → cO E ϖ ∉ P.asIdeal := fun P a b => by
    obtain ⟨u, v, e⟩ := hcop
    exact one_notMem P (e ▸ add_mem (P.asIdeal.mul_mem_left _ a) (P.asIdeal.mul_mem_left _ b))
  have hA : ∀ P : HeightOneSpectrum (𝓞 E), ϖ ∈ P.asIdeal →
      P.valuation E (dt (f'' P) / dt (f P)) = P.valuation E (ϖ : E) := fun P hP => by
    have hP' := (mem_divs h0 P).2 hP
    rw [val_det_ker (hf P) (hf'' P) (d.1.f ⟨P, hP'⟩) (d.2.f_add ⟨P, hP'⟩) (d.2.f_smul ⟨P, hP'⟩) (d.2.f_ne ⟨P, hP'⟩)
      (h3 ⟨P, hP'⟩)]
    exact (val_of_simple hP (hsq P hP')).symm
  refine eq_of_gen _ (fun _ => (ϖ : E) / star (ϖ : E)) (fun P => gen_relDet hN.1.fg (hf P) (hf'' P))
    (fun P => gen_of (div_ne_zero hϖ hϖ') (le_locP P _ (Submodule.mem_span_singleton_self _))
      (GlobalTheory.CharVal.maxV_span_singleton _).1) fun P => ?_
  by_cases hP : ϖ ∈ P.asIdeal
  · have : P.valuation E (star (ϖ : E)) = 1 := val_of_notMem (hnot P hP)
    rw [hA P hP, map_div₀, this, div_one]
  have hv : P.valuation E (ϖ : E) = 1 := val_of_notMem hP
  by_cases hP' : cO E ϖ ∈ P.asIdeal
  · have e1 := hA (conjPrime₂ P) ((mem_conjP P ϖ).2 hP')
    have e2 : (conjPrime₂ P).valuation E (dt (f'' (conjPrime₂ P)) / dt (f (conjPrime₂ P)) / (ϖ : E)) = 1 := by
      rw [map_div₀, e1, div_self (val_pos hϖ).ne']
    have e3 := val_star_eq_one e2
    have e4 := val_dual hN (hf (conjPrime₂ P)) (f' := f P) (by rw [conjP_conjP]; exact hf P)
    have e5 := val_dual hN'' (hf'' (conjPrime₂ P)) (f' := f'' P) (by rw [conjP_conjP]; exact hf'' P)
    rw [conjP_conjP] at e3 e4 e5
    have e6 : dt (f'' P) / dt (f P) = (star (dt (f'' (conjPrime₂ P))) * dt (f'' P)) / (star (dt (f (conjPrime₂ P))) * dt (f P)) /
        star (dt (f'' (conjPrime₂ P)) / dt (f (conjPrime₂ P)) / (ϖ : E)) / star (ϖ : E) := by
      have := star_ne_zero.2 (dt_ne (f'' (conjPrime₂ P)))
      have := star_ne_zero.2 (dt_ne (f (conjPrime₂ P)))
      have := dt_ne (f P)
      rw [star_div₀, star_div₀]
      field_simp
    rw [e6, map_div₀, map_div₀, map_div₀, e3, e4, e5, map_div₀, hv]
    simp
  · have hv' : P.valuation E (star (ϖ : E)) = 1 := val_of_notMem hP'
    have e : IsFr P N'' (f P) := fun x => by
      rw [← hf P x, mem_locP, mem_locP]
      constructor
      · rintro ⟨s, hs, h⟩
        refine ⟨cO E ϖ * s, fun hm => (P.isPrime.mem_or_mem hm).elim hP' hs, ?_⟩
        rw [mul_smul, ← algebraMap_smul E (cO E ϖ)]
        exact h2 _ h
      · rintro ⟨s, hs, h⟩
        refine ⟨ϖ * s, fun hm => (P.isPrime.mem_or_mem hm).elim hP hs, ?_⟩
        rw [mul_smul, ← algebraMap_smul E ϖ]
        exact h1 _ h
    rw [map_div₀, map_div₀, hv, hv', (gen_detI e).val_eq (gen_detI (hf'' P)), div_self (val_pos (dt_ne _)).ne', div_one]

omit [StarRing E] in
/- English proof (translation)
Establish `key : ∀ A : Matrix (Fin n) (Fin n) E, (∀ v ∈ trL e L, (A.map e).mulVec v ∈ trL e N) ↔ ∀ v ∈ L, A.mulVec v ∈ N`. Introduce `A`. Prove the components needed by the constructor for the conclusion. Introduce `H v hv`. Use `H (fun i => e (v i)) ((mem_trL e _ _).2 (by simpa using hv))` as an intermediate fact.

Rewrite `this` using `[map_mulVec', mem_trL]`. Simplify using `using this`. Introduce `H v hv`. Use `H (fun i => e.symm (v i)) ((mem_trL e _ _).1 hv)` as an intermediate fact. Establish `hv' : v = fun i => e (e.symm (v i))` using `by simp`.

Rewrite using `[hv', map_mulVec', mem_trL]`. Simplify using `using this`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨A, hA, rfl⟩`.

Establish `hAe : A = (A.map e.symm).map e` using `by ext i j; simp`. Use `⟨_, ⟨A.map e.symm, (key _).1 (hAe ▸ hA), rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← det_map', ← hAe]`. Introduce and unpack `⟨_, ⟨A, hA, rfl⟩, rfl⟩`. Conclude with `⟨A.map e, (key A).2 hA, (det_map' e A).symm⟩`.
-/
theorem det_set_rel {E' : Type} [Field E'] [NumberField E'] (e : E ≃+* E') (L N : Submodule (𝓞 E) (Fin n → E)) :
    {x | ∃ A : Matrix (Fin n) (Fin n) E', (∀ v ∈ trL e L, A.mulVec v ∈ trL e N) ∧ x = A.det} =
      e '' {x | ∃ A : Matrix (Fin n) (Fin n) E, (∀ v ∈ L, A.mulVec v ∈ N) ∧ x = A.det} := by
  have key : ∀ A : Matrix (Fin n) (Fin n) E, (∀ v ∈ trL e L, (A.map e).mulVec v ∈ trL e N) ↔ ∀ v ∈ L, A.mulVec v ∈ N := by
    intro A
    constructor
    · intro H v hv
      have := H (fun i => e (v i)) ((mem_trL e _ _).2 (by simpa using hv))
      rw [map_mulVec', mem_trL] at this
      simpa using this
    · intro H v hv
      have := H (fun i => e.symm (v i)) ((mem_trL e _ _).1 hv)
      have hv' : v = fun i => e (e.symm (v i)) := by simp
      rw [hv', map_mulVec', mem_trL]
      simpa using this
  ext x
  constructor
  · rintro ⟨A, hA, rfl⟩
    have hAe : A = (A.map e.symm).map e := by ext i j; simp
    refine ⟨_, ⟨A.map e.symm, (key _).1 (hAe ▸ hA), rfl⟩, ?_⟩
    rw [← det_map', ← hAe]
  · rintro ⟨_, ⟨A, hA, rfl⟩, rfl⟩
    exact ⟨A.map e, (key A).2 hA, (det_map' e A).symm⟩

end General

/- English proof (translation)
Introduce `D X s χ b SG ϖ d N'' _ hs hχ h0 hcop hsq hN'' ⟨h1, h2, h3⟩`. Establish `hϖ : (ϖ : X.E) ≠ 0` using `by simpa using h0`. Establish `hϖ' : star (ϖ : X.E) ≠ 0` using `star_ne_zero.2 hϖ`. Establish `e : TaylorLogMetric.detId D (s.lat d.1.N) (s.lat N'') = GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.idTo s (relDet d.1.N N'')` using `(congrArg (Submodule.span (𝓞 D.host.E)) (det_set_rel s.iE d.1.N N'')).trans (trI_span s.iE _).symm`. Rewrite using `[e, relDet_companion d h0 hcop hsq hN'' h1 h2 h3]`.

Use `ChiUnit.chi_span hs hχ ?_` and prove the remaining obligations. Rewrite using `[star_div₀, star_star]`. Clear the denominators using the available nonvanishing facts.
-/
theorem chi_move : ∀ (D : D7) (X : Fields) (s : Seam D X) (χ : TaylorLogMetric.IdE D → ℂ) (b : ℕ) (SG : Finset (HeightOneSpectrum (𝓞 X.E))) (ϖ : 𝓞 X.E) (d : DecoSet X.E b (divs ϖ) SG) (N'' : Submodule (𝓞 X.E) (Sp X.E b)), X.Ok → s.Ok → TaylorLogMetric.IsChi D χ → ϖ ≠ 0 → IsCoprime ϖ (X.conjO ϖ) → (∀ P ∈ divs ϖ, ϖ ∉ P.asIdeal ^ 2) → IsSdLat N'' → ((∀ y ∈ d.1.N, (ϖ : X.E) • y ∈ N'') ∧ (∀ y ∈ N'', star (ϖ : X.E) • y ∈ d.1.N) ∧ ∀ (P : ↥(divs ϖ)) (y : Sp X.E b), y ∈ localization₂ P.1.asIdeal N'' ↔ y ∈ d.1.at P.1 ∧ d.1.f P y = 0) → χ (TaylorLogMetric.detId D (s.lat d.1.N) (s.lat N'')) = ∏ τ, (s.σ₀ (X.emb τ ((ϖ : X.E) / star (ϖ : X.E))))⁻¹ := by
  intro D X s χ b SG ϖ d N'' _ hs hχ h0 hcop hsq hN'' ⟨h1, h2, h3⟩
  have hϖ : (ϖ : X.E) ≠ 0 := by simpa using h0
  have hϖ' : star (ϖ : X.E) ≠ 0 := star_ne_zero.2 hϖ
  have e : TaylorLogMetric.detId D (s.lat d.1.N) (s.lat N'') = GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.idTo s (relDet d.1.N N'') :=
    (congrArg (Submodule.span (𝓞 D.host.E)) (det_set_rel s.iE d.1.N N'')).trans (trI_span s.iE _).symm
  rw [e, relDet_companion d h0 hcop hsq hN'' h1 h2 h3]
  refine ChiUnit.chi_span hs hχ ?_
  rw [star_div₀, star_star]
  field_simp

end GlobalTheory.MomT.ChiMove
