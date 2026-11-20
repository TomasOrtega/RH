import Mathlib
import Formalism.HermitianLattices.StatementLat
import Development.AutomorphicSpectrum.Definitions.SemilocalProjection.HidaSetting
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis

open NumberField Matrix IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame

noncomputable def gIdx {W : Type} [AddCommGroup W] (A B : AddSubgroup W) : ℝ :=
  Real.log ((B.relIndex A : ℕ) : ℝ) - Real.log ((A.relIndex B : ℕ) : ℝ)

section Index

variable {W : Type} [AddCommGroup W]

/- English proof (translation)
Simplify using `[gIdx]`.
-/
theorem gIdx_self (A : AddSubgroup W) : gIdx A A = 0 := by
  simp [gIdx]

/- English proof (translation)
Simplify using `[gIdx, AddSubgroup.relIndex_eq_one.2 h]`.
-/
theorem gIdx_of_le {A B : AddSubgroup W} (h : B ≤ A) : gIdx A B = Real.log ((B.relIndex A : ℕ) : ℝ) := by
  simp [gIdx, AddSubgroup.relIndex_eq_one.2 h]

/- English proof (translation)
Simplify using `[gIdx]`.
-/
theorem gIdx_swap (A B : AddSubgroup W) : gIdx A B = - gIdx B A := by
  simp [gIdx]

/- English proof (translation)
Establish `e1 : D.relIndex X = D.relIndex (X ⊓ Y) * Y.relIndex X`. Rewrite using `[← AddSubgroup.inf_relIndex_left X Y, AddSubgroup.relIndex_mul_relIndex _ _ _ hD inf_le_left]`. Establish `e2 : D.relIndex Y = D.relIndex (X ⊓ Y) * X.relIndex Y`. Rewrite using `[← AddSubgroup.inf_relIndex_right X Y, AddSubgroup.relIndex_mul_relIndex _ _ _ hD inf_le_right]`. Establish `hd : D.relIndex (X ⊓ Y) ≠ 0`.

Introduce `h`. Rewrite `hX` using `[e1, h, zero_mul]`. Conclude with `hX rfl`. Establish `h1 : Y.relIndex X ≠ 0`. Introduce `h`.

Rewrite `hX` using `[e1, h, mul_zero]`. Conclude with `hX rfl`. Establish `h2 : X.relIndex Y ≠ 0`. Introduce `h`. Rewrite `hY` using `[e2, h, mul_zero]`.

Conclude with `hY rfl`. Rewrite using `[gIdx, e1, e2]`. Use `push_cast`. Rewrite using `[Real.log_mul (by exact_mod_cast hd) (by exact_mod_cast h1), Real.log_mul (by exact_mod_cast hd) (by exact_mod_cast h2)]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem gIdx_eq_lemma {X Y D : AddSubgroup W} (hD : D ≤ X ⊓ Y) (hX : D.relIndex X ≠ 0)
    (hY : D.relIndex Y ≠ 0) :
    gIdx X Y = Real.log (D.relIndex X : ℝ) - Real.log (D.relIndex Y : ℝ) := by
  have e1 : D.relIndex X = D.relIndex (X ⊓ Y) * Y.relIndex X := by
    rw [← AddSubgroup.inf_relIndex_left X Y, AddSubgroup.relIndex_mul_relIndex _ _ _ hD inf_le_left]
  have e2 : D.relIndex Y = D.relIndex (X ⊓ Y) * X.relIndex Y := by
    rw [← AddSubgroup.inf_relIndex_right X Y, AddSubgroup.relIndex_mul_relIndex _ _ _ hD inf_le_right]
  have hd : D.relIndex (X ⊓ Y) ≠ 0 := by
    intro h
    rw [e1, h, zero_mul] at hX
    exact hX rfl
  have h1 : Y.relIndex X ≠ 0 := by
    intro h
    rw [e1, h, mul_zero] at hX
    exact hX rfl
  have h2 : X.relIndex Y ≠ 0 := by
    intro h
    rw [e2, h, mul_zero] at hY
    exact hY rfl
  rw [gIdx, e1, e2]
  push_cast
  rw [Real.log_mul (by exact_mod_cast hd) (by exact_mod_cast h1),
    Real.log_mul (by exact_mod_cast hd) (by exact_mod_cast h2)]
  ring

/- English proof (translation)
Establish `hCA : C.relIndex A ≠ 0` using `AddSubgroup.relIndex_ne_zero_trans hCB hBA`. Establish `hAC : A.relIndex C ≠ 0` using `AddSubgroup.relIndex_ne_zero_trans hAB hBC`. Establish `hA : (A ⊓ B ⊓ C).relIndex A ≠ 0` using `AddSubgroup.relIndex_inf_ne_zero (AddSubgroup.relIndex_inf_ne_zero (by simp) hBA) hCA`. Establish `hB : (A ⊓ B ⊓ C).relIndex B ≠ 0` using `AddSubgroup.relIndex_inf_ne_zero (AddSubgroup.relIndex_inf_ne_zero hAB (by simp)) hCB`. Establish `hC : (A ⊓ B ⊓ C).relIndex C ≠ 0` using `AddSubgroup.relIndex_inf_ne_zero (AddSubgroup.relIndex_inf_ne_zero hAC hBC) (by simp)`.

Rewrite using `[gIdx_eq_lemma (le_inf (inf_le_left.trans inf_le_left) inf_le_right) hA hC, gIdx_eq_lemma (inf_le_left : A ⊓ B ⊓ C ≤ A ⊓ B) hA hB, gIdx_eq_lemma (le_inf (inf_le_left.trans inf_le_right) inf_le_right) hB hC]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gIdx_add {A B C : AddSubgroup W} (hAB : A.relIndex B ≠ 0) (hBA : B.relIndex A ≠ 0)
    (hBC : B.relIndex C ≠ 0) (hCB : C.relIndex B ≠ 0) : gIdx A C = gIdx A B + gIdx B C := by
  have hCA : C.relIndex A ≠ 0 := AddSubgroup.relIndex_ne_zero_trans hCB hBA
  have hAC : A.relIndex C ≠ 0 := AddSubgroup.relIndex_ne_zero_trans hAB hBC
  have hA : (A ⊓ B ⊓ C).relIndex A ≠ 0 :=
    AddSubgroup.relIndex_inf_ne_zero (AddSubgroup.relIndex_inf_ne_zero (by simp) hBA) hCA
  have hB : (A ⊓ B ⊓ C).relIndex B ≠ 0 :=
    AddSubgroup.relIndex_inf_ne_zero (AddSubgroup.relIndex_inf_ne_zero hAB (by simp)) hCB
  have hC : (A ⊓ B ⊓ C).relIndex C ≠ 0 :=
    AddSubgroup.relIndex_inf_ne_zero (AddSubgroup.relIndex_inf_ne_zero hAC hBC) (by simp)
  rw [gIdx_eq_lemma (le_inf (inf_le_left.trans inf_le_left) inf_le_right) hA hC,
    gIdx_eq_lemma (inf_le_left : A ⊓ B ⊓ C ≤ A ⊓ B) hA hB,
    gIdx_eq_lemma (le_inf (inf_le_left.trans inf_le_right) inf_le_right) hB hC]
  ring

/- English proof (translation)
Simplify using `only [gIdx, AddSubgroup.relIndex_map_map_of_injective _ _ hf]`.
-/
theorem gIdx_map {W' : Type} [AddCommGroup W'] (f : W →+ W') (hf : Function.Injective f)
    (A B : AddSubgroup W) : gIdx (A.map f) (B.map f) = gIdx A B := by
  simp only [gIdx, AddSubgroup.relIndex_map_map_of_injective _ _ hf]

/- English proof (translation)
Establish `hcomm : Λ.map (a.comp M) = (Λ.map a).map M`. Rewrite using `[AddSubgroup.map_map]`. Use `congr 1`. Use extensionality with `x`. Simplify using `[hc]`.

Establish `hsub : Λ.map (a.comp M) ≤ Λ.map M`. Rewrite using `[hcomm]`. Conclude with `AddSubgroup.map_mono h2`. Establish `iB : (Λ.map (a.comp M)).relIndex (Λ.map M) = (Λ.map a).relIndex Λ`. Rewrite using `[hcomm]`.

Conclude with `AddSubgroup.relIndex_map_map_of_injective _ _ hM`. Establish `h3' : (Λ.map a).map M ≤ Λ`. Rewrite using `[← hcomm]`. Conclude with `h3`. Rewrite using `[gIdx_add (B := Λ.map (a.comp M)) (by rw [AddSubgroup.relIndex_eq_one.mpr hsub]; exact one_ne_zero) (by rw [iB]; exact i2) i3 (by rw [AddSubgroup.relIndex_eq_one.mpr h3]; exact one_ne_zero)]`.

Rewrite using `[hcomm, gIdx_map M hM, gIdx_of_le h2, gIdx_swap, gIdx_of_le h3']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gIdx_frac (Λ : AddSubgroup W) (M a : W →+ W) (hM : Function.Injective M)
    (hc : ∀ x, a (M x) = M (a x)) (h2 : Λ.map a ≤ Λ) (i2 : (Λ.map a).relIndex Λ ≠ 0)
    (h3 : Λ.map (a.comp M) ≤ Λ) (i3 : (Λ.map (a.comp M)).relIndex Λ ≠ 0) :
    gIdx (Λ.map M) Λ =
      Real.log (((Λ.map a).relIndex Λ : ℕ) : ℝ) - Real.log (((Λ.map (a.comp M)).relIndex Λ : ℕ) : ℝ) := by
  have hcomm : Λ.map (a.comp M) = (Λ.map a).map M := by
    rw [AddSubgroup.map_map]
    congr 1
    ext x
    simp [hc]
  have hsub : Λ.map (a.comp M) ≤ Λ.map M := by
    rw [hcomm]
    exact AddSubgroup.map_mono h2
  have iB : (Λ.map (a.comp M)).relIndex (Λ.map M) = (Λ.map a).relIndex Λ := by
    rw [hcomm]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hM
  have h3' : (Λ.map a).map M ≤ Λ := by
    rw [← hcomm]
    exact h3
  rw [gIdx_add (B := Λ.map (a.comp M))
    (by rw [AddSubgroup.relIndex_eq_one.mpr hsub]; exact one_ne_zero) (by rw [iB]; exact i2) i3
    (by rw [AddSubgroup.relIndex_eq_one.mpr h3]; exact one_ne_zero)]
  rw [hcomm, gIdx_map M hM, gIdx_of_le h2, gIdx_swap, gIdx_of_le h3']
  ring

end Index

variable {L : Type} [Field L] [NumberField L]

noncomputable def locAt {W : Type} [AddCommGroup W] [Module (𝓞 L) W] (v : FinitePlace L) (A : Submodule (𝓞 L) W) :
    Submodule (𝓞 L) W :=
  haveI := v.maximalIdeal.isPrime
  Formalism.HermitianLatticesTheory.localization₂ v.maximalIdeal.asIdeal A

/- English proof (translation)
The claim follows from `(Iff.rfl)`.
-/
theorem mem_locAt {W : Type} [AddCommGroup W] [Module (𝓞 L) W] {v : FinitePlace L} {A : Submodule (𝓞 L) W}
    {x : W} : x ∈ locAt v A ↔ ∃ t : 𝓞 L, t ∉ v.maximalIdeal.asIdeal ∧ t • x ∈ A := (Iff.rfl)

/- English proof (translation)
Introduce `x hx`. Rewrite using `[mem_locAt]`. Conclude with `⟨1, (Ideal.ne_top_iff_one _).mp v.maximalIdeal.isPrime.ne_top, by simpa using hx⟩`.
-/
theorem le_locAt {W : Type} [AddCommGroup W] [Module (𝓞 L) W] (v : FinitePlace L) (A : Submodule (𝓞 L) W) :
    A ≤ locAt v A := by
  intro x hx
  rw [mem_locAt]
  exact ⟨1, (Ideal.ne_top_iff_one _).mp v.maximalIdeal.isPrime.ne_top, by simpa using hx⟩

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [Submodule.mem_inf, mem_locAt]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, ht, hA, hB⟩`. Conclude with `⟨⟨t, ht, hA⟩, ⟨t, ht, hB⟩⟩`.

Introduce and unpack `⟨⟨s, hs, hA⟩, ⟨t, ht, hB⟩⟩`. Use `⟨s * t, fun h => ?_, ?_, ?_⟩` and prove the remaining obligations. Break down `v.maximalIdeal.isPrime.mem_or_mem h with h | h` into its components or cases. Conclude with `hs h`. Conclude with `ht h`.

Rewrite using `[mul_comm, mul_smul]`. Conclude with `A.smul_mem t hA`. Rewrite using `[mul_smul]`. Conclude with `B.smul_mem s hB`.
-/
theorem locAt_inf {W : Type} [AddCommGroup W] [Module (𝓞 L) W] (v : FinitePlace L) (A B : Submodule (𝓞 L) W) :
    locAt v (A ⊓ B) = locAt v A ⊓ locAt v B := by
  ext x
  simp only [Submodule.mem_inf, mem_locAt]
  constructor
  · rintro ⟨t, ht, hA, hB⟩
    exact ⟨⟨t, ht, hA⟩, ⟨t, ht, hB⟩⟩
  · rintro ⟨⟨s, hs, hA⟩, ⟨t, ht, hB⟩⟩
    refine ⟨s * t, fun h => ?_, ?_, ?_⟩
    · rcases v.maximalIdeal.isPrime.mem_or_mem h with h | h
      · exact hs h
      · exact ht h
    · rw [mul_comm, mul_smul]
      exact A.smul_mem t hA
    · rw [mul_smul]
      exact B.smul_mem s hB

noncomputable def frame {n : ℕ} (T : Matrix (Fin n) (Fin n) L) : Submodule (𝓞 L) (Fin n → L) :=
  Submodule.span (𝓞 L) (Set.range fun k j => T j k)

noncomputable def glued {n : ℕ} (T : FinitePlace L → Matrix (Fin n) (Fin n) L) : Submodule (𝓞 L) (Fin n → L) :=
  ⨅ v, locAt v (frame (T v))

def UnitAt {n : ℕ} (v : FinitePlace L) (T : Matrix (Fin n) (Fin n) L) : Prop :=
  (∀ i j, v (T i j) ≤ 1) ∧ v T.det = 1

/- English proof (translation)
Rewrite using `[← FinitePlace.norm_embedding_eq, FinitePlace.norm_embedding, NumberField.HeightOneSpectrum.adicAbv_def, NNReal.coe_le_one, WithZeroMulInt.toNNReal_le_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal _)]`.
-/
theorem place_le_one_iff (v : FinitePlace L) (x : L) : v x ≤ 1 ↔ v.maximalIdeal.valuation L x ≤ 1 := by
  rw [← FinitePlace.norm_embedding_eq, FinitePlace.norm_embedding, NumberField.HeightOneSpectrum.adicAbv_def,
    NNReal.coe_le_one, WithZeroMulInt.toNNReal_le_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal _)]

/- English proof (translation)
Rewrite `hx` using `[place_le_one_iff]`. Take `⟨n, d, h | h⟩` from `v.maximalIdeal.exists_primeCompl_mul_eq_or_mul_eq (K := L) x`. Conclude with `⟨d, n, d.2, by rw [mul_comm]; exact h⟩`. Use `⟨n, d, fun hn => ?_, by rw [mul_comm]; exact h⟩` and prove the remaining obligations. Establish `h1` using `congrArg (v.maximalIdeal.valuation L) h`.

Rewrite `h1` using `[map_mul]`. Establish `hd : v.maximalIdeal.valuation L (algebraMap (𝓞 L) L d) = 1`. Rewrite using `[IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]`. Conclude with `d.2`. Establish `hn' : v.maximalIdeal.valuation L (algebraMap (𝓞 L) L n) < 1`.

Rewrite using `[IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]`. Conclude with `hn`. Establish `key : v.maximalIdeal.valuation L x * v.maximalIdeal.valuation L (algebraMap (𝓞 L) L n) < 1` using `lt_of_le_of_lt (mul_le_of_le_one_left' hx) hn'`. Rewrite `key` using `[h1, hd]`. Conclude with `lt_irrefl _ key`.
-/
theorem exists_denom (v : FinitePlace L) {x : L} (hx : v x ≤ 1) :
    ∃ (s r : 𝓞 L), s ∉ v.maximalIdeal.asIdeal ∧ (s : L) * x = r := by
  rw [place_le_one_iff] at hx
  obtain ⟨n, d, h | h⟩ := v.maximalIdeal.exists_primeCompl_mul_eq_or_mul_eq (K := L) x
  · exact ⟨d, n, d.2, by rw [mul_comm]; exact h⟩
  · refine ⟨n, d, fun hn => ?_, by rw [mul_comm]; exact h⟩
    have h1 := congrArg (v.maximalIdeal.valuation L) h
    rw [map_mul] at h1
    have hd : v.maximalIdeal.valuation L (algebraMap (𝓞 L) L d) = 1 := by
      rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
        IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
      exact d.2
    have hn' : v.maximalIdeal.valuation L (algebraMap (𝓞 L) L n) < 1 := by
      rw [IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
      exact hn
    have key : v.maximalIdeal.valuation L x * v.maximalIdeal.valuation L (algebraMap (𝓞 L) L n) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_left' hx) hn'
    rw [h1, hd] at key
    exact lt_irrefl _ key

/- English proof (translation)
Rewrite using `[place_le_one_iff]`. Conclude with `IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ r`.
-/
theorem place_int_le_one (v : FinitePlace L) (r : 𝓞 L) : v (r : L) ≤ 1 := by
  rw [place_le_one_iff]
  exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ r

/- English proof (translation)
The claim follows from `(HeightOneSpectrum.valuation_eq_one_iff_notMem _).2 ht`.
-/
theorem place_eq_one_of_notMem (v : FinitePlace L) {t : 𝓞 L} (ht : t ∉ v.maximalIdeal.asIdeal) :
    v.maximalIdeal.valuation L (t : L) = 1 :=
  (HeightOneSpectrum.valuation_eq_one_iff_notMem _).2 ht

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`. Use `(FinitePlace.add_le v _ _).trans (max_le ?_ ?_)` and prove the remaining obligations.

Conclude with `h a (Finset.mem_insert_self a s)`. Conclude with `ih (fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem place_sum_le_one (v : FinitePlace L) {ι : Type} (s : Finset ι) (f : ι → L)
    (h : ∀ i ∈ s, v (f i) ≤ 1) : v (∑ i ∈ s, f i) ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine (FinitePlace.add_le v _ _).trans (max_le ?_ ?_)
    · exact h a (Finset.mem_insert_self a s)
    · exact ih (fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Rewrite using `[FinitePlace.coe_apply, map_mul]`. Rewrite `ha`, `hb` using `[FinitePlace.coe_apply]`. Conclude with `mul_le_one₀ ha (AbsoluteValue.nonneg _ _) hb`.
-/
theorem place_mul_le_one (v : FinitePlace L) {a b : L} (ha : v a ≤ 1) (hb : v b ≤ 1) : v (a * b) ≤ 1 := by
  rw [FinitePlace.coe_apply, map_mul]
  rw [FinitePlace.coe_apply] at ha hb
  exact mul_le_one₀ ha (AbsoluteValue.nonneg _ _) hb

variable {n : ℕ}

/- English proof (translation)
Rewrite using `[frame, Submodule.mem_span_range_iff_exists_fun]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, rfl⟩`. Use `⟨c, ?_⟩` and prove the remaining obligations. Use extensionality with `j`.

Simplify using `[Matrix.mulVec, dotProduct, Finset.sum_apply, Algebra.smul_def, mul_comm]`. Introduce and unpack `⟨z, rfl⟩`. Use `⟨z, ?_⟩` and prove the remaining obligations. Use extensionality with `j`. Simplify using `[Matrix.mulVec, dotProduct, Finset.sum_apply, Algebra.smul_def, mul_comm]`.
-/
theorem mem_frame {T : Matrix (Fin n) (Fin n) L} {x : Fin n → L} :
    x ∈ frame T ↔ ∃ z : Fin n → 𝓞 L, x = T *ᵥ fun i => (z i : L) := by
  rw [frame, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    ext j
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Algebra.smul_def, mul_comm]
  · rintro ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    ext j
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Algebra.smul_def, mul_comm]

/- English proof (translation)
Use `choose s r hs hr using fun i => exists_denom v (hy i)`. Use `haveI := v.maximalIdeal.isPrime`. Use `⟨∏ j, s j, fun i => (∏ j ∈ Finset.univ.erase i, s j) * r i, ?_, fun i => ?_⟩` and prove the remaining obligations. Introduce `hmem`. Take `⟨j, -, hj⟩` from `Ideal.IsPrime.prod_mem_iff.mp hmem`.

Conclude with `hs j hj`. Use `push_cast`. Rewrite using `[← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_assoc, hr i]`.
-/
theorem exists_common_denom (v : FinitePlace L) {y : Fin n → L} (hy : ∀ i, v (y i) ≤ 1) :
    ∃ (t : 𝓞 L) (z : Fin n → 𝓞 L), t ∉ v.maximalIdeal.asIdeal ∧ ∀ i, (t : L) * y i = z i := by
  choose s r hs hr using fun i => exists_denom v (hy i)
  classical
  haveI := v.maximalIdeal.isPrime
  refine ⟨∏ j, s j, fun i => (∏ j ∈ Finset.univ.erase i, s j) * r i, ?_, fun i => ?_⟩
  · intro hmem
    obtain ⟨j, -, hj⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hs j hj
  · push_cast
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_assoc, hr i]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Rewrite `hx` using `[mem_locAt]`. Take `⟨t, ht, htx⟩` from `hx`. Rewrite `htx` using `[mem_frame]`.

Take `⟨z, hz⟩` from `htx`. Establish `ht0 : (t : L) ≠ 0`. Introduce `h0`. Apply `ht` to reduce the goal to its premises. Establish `: t = 0` using `by exact_mod_cast h0`.

Rewrite using `[this]`. Conclude with `Ideal.zero_mem _`. Use `⟨fun i => (t : L)⁻¹ * z i, fun i => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[place_le_one_iff, map_mul, map_inv₀, place_eq_one_of_notMem v ht, inv_one, one_mul]`. Conclude with `IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ _`.

Establish `e : (fun i => (t : L)⁻¹ * (z i : L)) = (t : L)⁻¹ • (fun i => (z i : L))`. Use extensionality with `i`. Simplify using the standard rewrite rules. Rewrite using `[e, Matrix.mulVec_smul, ← hz]`. Use extensionality with `j`.

Simplify using `[Algebra.smul_def, ht0]`. Introduce and unpack `⟨y, hy, rfl⟩`. Take `⟨t, z, ht, hz⟩` from `exists_common_denom v hy`. Rewrite using `[mem_locAt]`. Use `⟨t, ht, ?_⟩` and prove the remaining obligations.

Rewrite using `[mem_frame]`. Use `⟨z, ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.mulVec_smul]`. Use `congr 1`. Use extensionality with `i`.

Rewrite using `[Pi.smul_apply, Algebra.smul_def]`. Conclude with `hz i`.
-/
theorem mem_locAt_frame {v : FinitePlace L} {T : Matrix (Fin n) (Fin n) L} {x : Fin n → L} :
    x ∈ locAt v (frame T) ↔ ∃ y : Fin n → L, (∀ i, v (y i) ≤ 1) ∧ x = T *ᵥ y := by
  constructor
  · intro hx
    rw [mem_locAt] at hx
    obtain ⟨t, ht, htx⟩ := hx
    rw [mem_frame] at htx
    obtain ⟨z, hz⟩ := htx
    have ht0 : (t : L) ≠ 0 := by
      intro h0
      apply ht
      have : t = 0 := by exact_mod_cast h0
      rw [this]
      exact Ideal.zero_mem _
    refine ⟨fun i => (t : L)⁻¹ * z i, fun i => ?_, ?_⟩
    · rw [place_le_one_iff, map_mul, map_inv₀, place_eq_one_of_notMem v ht, inv_one, one_mul]
      exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ _
    · have e : (fun i => (t : L)⁻¹ * (z i : L)) = (t : L)⁻¹ • (fun i => (z i : L)) := by
        ext i
        simp
      rw [e, Matrix.mulVec_smul, ← hz]
      ext j
      simp [Algebra.smul_def, ht0]
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨t, z, ht, hz⟩ := exists_common_denom v hy
    rw [mem_locAt]
    refine ⟨t, ht, ?_⟩
    rw [mem_frame]
    refine ⟨z, ?_⟩
    rw [← Matrix.mulVec_smul]
    congr 1
    ext i
    rw [Pi.smul_apply, Algebra.smul_def]
    exact hz i

/- English proof (translation)
Rewrite using `[mem_locAt_frame]`. Simplify using the standard rewrite rules.
-/
theorem mem_locAt_frame_one {v : FinitePlace L} {x : Fin n → L} :
    x ∈ locAt v (frame (1 : Matrix (Fin n) (Fin n) L)) ↔ ∀ i, v (x i) ≤ 1 := by
  rw [mem_locAt_frame]
  simp

/- English proof (translation)
Rewrite using `[mem_frame]`. Simplify using `only [Matrix.one_mulVec]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, rfl⟩ i`. Conclude with `⟨z i, rfl⟩`.

Introduce `h choose z hz using h`. Conclude with `⟨z, funext hz⟩`.
-/
theorem mem_frame_one {x : Fin n → L} :
    x ∈ frame (1 : Matrix (Fin n) (Fin n) L) ↔ ∀ i, ∃ r : 𝓞 L, x i = r := by
  rw [mem_frame]
  simp only [Matrix.one_mulVec]
  constructor
  · rintro ⟨z, rfl⟩ i
    exact ⟨z i, rfl⟩
  · intro h
    choose z hz using h
    exact ⟨z, funext hz⟩

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[Submodule.mem_iInf, mem_frame_one]`. Simplify using `only [mem_locAt_frame_one]`. Prove the components needed by the constructor for the conclusion. Introduce `h i`.

Take `⟨r, hr⟩` from `IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 L) (K := L) (x := x i) (h := fun w => by`. Use `(place_le_one_iff (FinitePlace.mk w) (x i)).mp (h (FinitePlace.mk w) i)` as an intermediate fact. Rewrite using `[FinitePlace.maximalIdeal_mk] at this)` and apply the resulting hypothesis. Conclude with `⟨r, hr.symm⟩`. Introduce `h w i`.

Take `⟨r, hr⟩` from `h i`. Rewrite using `[hr]`. Conclude with `place_int_le_one w r`.
-/
theorem iInf_locAt_frame_one : ⨅ v : FinitePlace L, locAt v (frame (1 : Matrix (Fin n) (Fin n) L)) = frame 1 := by
  ext x
  rw [Submodule.mem_iInf, mem_frame_one]
  simp only [mem_locAt_frame_one]
  constructor
  · intro h i
    obtain ⟨r, hr⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 L) (K := L)
      (x := x i) (h := fun w => by
        have := (place_le_one_iff (FinitePlace.mk w) (x i)).mp (h (FinitePlace.mk w) i)
        rwa [FinitePlace.maximalIdeal_mk] at this)
    exact ⟨r, hr.symm⟩
  · intro h w i
    obtain ⟨r, hr⟩ := h i
    rw [hr]
    exact place_int_le_one w r

/- English proof (translation)
Use `⟨fun i j => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.one_apply] split_ifs`. Rewrite using `[FinitePlace.coe_apply, map_one]`. Rewrite using `[FinitePlace.coe_apply, map_zero]`. Conclude with `zero_le_one`.

Rewrite using `[Matrix.det_one, FinitePlace.coe_apply, map_one]`.
-/
theorem unitAt_one (v : FinitePlace L) : UnitAt v (1 : Matrix (Fin n) (Fin n) L) := by
  refine ⟨fun i j => ?_, ?_⟩
  · rw [Matrix.one_apply]
    split_ifs
    · rw [FinitePlace.coe_apply, map_one]
    · rw [FinitePlace.coe_apply, map_zero]
      exact zero_le_one
  · rw [Matrix.det_one, FinitePlace.coe_apply, map_one]

/- English proof (translation)
Set `S` to `(v.maximalIdeal.valuation L).valuationSubring`. Set `T' : Matrix (Fin n) (Fin n) S` to `fun a b => ⟨T a b, by rw [Valuation.mem_valuationSubring_iff, ← place_le_one_iff]; exact h a b⟩`. Establish `key : T.adjugate i j = S.subtype (T'.adjugate i j)` using `(congrFun (congrFun (RingHom.map_adjugate S.subtype T') i) j).symm`. Rewrite using `[key, place_le_one_iff]`. Conclude with `(T'.adjugate i j).2`.
-/
private theorem adj_le_lemma (v : FinitePlace L) {T : Matrix (Fin n) (Fin n) L} (h : ∀ i j, v (T i j) ≤ 1)
    (i j : Fin n) : v (T.adjugate i j) ≤ 1 := by
  let S := (v.maximalIdeal.valuation L).valuationSubring
  let T' : Matrix (Fin n) (Fin n) S := fun a b =>
    ⟨T a b, by rw [Valuation.mem_valuationSubring_iff, ← place_le_one_iff]; exact h a b⟩
  have key : T.adjugate i j = S.subtype (T'.adjugate i j) :=
    (congrFun (congrFun (RingHom.map_adjugate S.subtype T') i) j).symm
  rw [key, place_le_one_iff]
  exact (T'.adjugate i j).2

/- English proof (translation)
Rewrite using `[Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']`. Apply `place_mul_le_one v _ (adj_le_lemma v h.1 i j)` to reduce the goal to its premises. Rewrite using `[FinitePlace.coe_apply, map_inv₀, ← FinitePlace.coe_apply, h.2, inv_one]`.
-/
theorem UnitAt.inv_le_one {v : FinitePlace L} {T : Matrix (Fin n) (Fin n) L} (h : UnitAt v T) (i j : Fin n) :
    v (T⁻¹ i j) ≤ 1 := by
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  apply place_mul_le_one v _ (adj_le_lemma v h.1 i j)
  rw [FinitePlace.coe_apply, map_inv₀, ← FinitePlace.coe_apply, h.2, inv_one]

/- English proof (translation)
Establish `hdet : IsUnit T.det`. Rewrite using `[isUnit_iff_ne_zero]`. Introduce `h0`. Establish `h2` using `h.2`. Rewrite `h2` using `[h0, FinitePlace.coe_apply, map_zero]`.

Conclude with `zero_ne_one h2`. Establish `hrow : ∀ (M : Matrix (Fin n) (Fin n) L) (y : Fin n → L), (∀ i j, v (M i j) ≤ 1) → (∀ i, v (y i) ≤ 1) → ∀ i, v ((M *ᵥ y) i) ≤ 1`. Introduce `M y hM hy i`. Simplify using `only [Matrix.mulVec, dotProduct]`. Conclude with `place_sum_le_one v _ _ (fun k _ => place_mul_le_one v (hM i k) (hy k))`.

Use extensionality with `x`. Rewrite using `[mem_locAt_frame, mem_locAt_frame_one]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `hrow T y h.1 hy`.

Introduce `hx`. Use `⟨T⁻¹ *ᵥ x, hrow _ x h.inv_le_one hx, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]`.
-/
theorem UnitAt.locAt_frame {v : FinitePlace L} {T : Matrix (Fin n) (Fin n) L} (h : UnitAt v T) :
    locAt v (frame T) = locAt v (frame 1) := by
  have hdet : IsUnit T.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have h2 := h.2
    rw [h0, FinitePlace.coe_apply, map_zero] at h2
    exact zero_ne_one h2
  have hrow : ∀ (M : Matrix (Fin n) (Fin n) L) (y : Fin n → L), (∀ i j, v (M i j) ≤ 1) →
      (∀ i, v (y i) ≤ 1) → ∀ i, v ((M *ᵥ y) i) ≤ 1 := by
    intro M y hM hy i
    simp only [Matrix.mulVec, dotProduct]
    exact place_sum_le_one v _ _ (fun k _ => place_mul_le_one v (hM i k) (hy k))
  ext x
  rw [mem_locAt_frame, mem_locAt_frame_one]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hrow T y h.1 hy
  · intro hx
    refine ⟨T⁻¹ *ᵥ x, hrow _ x h.inv_le_one hx, ?_⟩
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

end GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame
