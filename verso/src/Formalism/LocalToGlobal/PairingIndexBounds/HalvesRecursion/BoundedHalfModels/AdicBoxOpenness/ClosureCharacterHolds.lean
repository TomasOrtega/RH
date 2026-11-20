import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.BoundedHalfModels.EqOffBound

noncomputable section
open scoped BigOperators
open IsDedekindDomain Topology Filter

namespace Formalism.L2.PairingIndexBounds.Rec

/- English proof (translation)
Rewrite using `[mem_closure_iff_nhds]`. Introduce `U hU`. Take `⟨γ, hγ⟩` from `Valued.mem_nhds.mp hU`. Use `set g := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hgdef`. Establish `hg : g ≠ 0` using `(map_ne_zero _).mpr γ.ne_zero`.

Establish `hV : {y : v.adicCompletion K | Valued.v (y - w) < g} ∈ 𝓝 w`. Rewrite using `[Valued.mem_nhds]`. Conclude with `⟨γ, fun y hy => by`. Simplify using `only [Set.mem_ofPred_eq] at hy ⊢`. Rewrite using `[Valuation.restrict_lt_iff_lt_embedding] at hy⟩` and apply the resulting hypothesis.

Establish `hO : ((v.adicCompletionIntegers K : ValuationSubring _) : Set (v.adicCompletion K)) ∈ 𝓝 w` using `(Valued.isOpen_valuationSubring (v.adicCompletion K)).mem_nhds hw`. Take `⟨_, ⟨k, rfl⟩, hk1, hk2⟩` from `Dense.inter_nhds_nonempty (HeightOneSpectrum.denseRange_algebraMap K v) (inter_mem hV hO)`. Establish `hkv : v.valuation K k ≤ 1`. Use `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k` as an intermediate fact. Rewrite using `[← this]`.

Conclude with `hk2`. Take `⟨a, ha⟩` from `HeightOneSpectrum.exists_valuation_sub_lt_of_integer v hkv (Units.mk0 g hg)`. Use `⟨algebraMap K (v.adicCompletion K) (algebraMap R K a), hγ ?_, a, rfl⟩` and prove the remaining obligations. Simplify using `only [Set.mem_ofPred_eq]`. Rewrite using `[Valuation.restrict_lt_iff_lt_embedding, ← hgdef]`.

Establish `e : algebraMap K (v.adicCompletion K) (algebraMap R K a) - w = algebraMap K (v.adicCompletion K) (algebraMap R K a - k) + (algebraMap K (v.adicCompletion K) k - w)`. Rewrite using `[map_sub]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `Valuation.map_add_lt _ ?_ hk1` and prove the remaining obligations.

Use `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (algebraMap R K a - k)` as an intermediate fact. Rewrite using `[show algebraMap K (v.adicCompletion K) (algebraMap R K a - k) = ((algebraMap R K a - k : K) : v.adicCompletion K) from rfl, this]`. Simplify using `using ha`.
-/
theorem denseInt_adic {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K]
    [IsFractionRing R K] (v : HeightOneSpectrum R) (w : v.adicCompletion K) (hw : Valued.v w ≤ 1) :
    w ∈ closure (Set.range fun r : R => algebraMap K (v.adicCompletion K) (algebraMap R K r)) := by
  rw [mem_closure_iff_nhds]
  intro U hU
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hU
  set g := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hgdef
  have hg : g ≠ 0 := (map_ne_zero _).mpr γ.ne_zero
  have hV : {y : v.adicCompletion K | Valued.v (y - w) < g} ∈ 𝓝 w := by
    rw [Valued.mem_nhds]
    exact ⟨γ, fun y hy => by
      simp only [Set.mem_ofPred_eq] at hy ⊢
      rwa [Valuation.restrict_lt_iff_lt_embedding] at hy⟩
  have hO : ((v.adicCompletionIntegers K : ValuationSubring _) : Set (v.adicCompletion K)) ∈ 𝓝 w :=
    (Valued.isOpen_valuationSubring (v.adicCompletion K)).mem_nhds hw
  obtain ⟨_, ⟨k, rfl⟩, hk1, hk2⟩ := Dense.inter_nhds_nonempty (HeightOneSpectrum.denseRange_algebraMap K v) (inter_mem hV hO)
  have hkv : v.valuation K k ≤ 1 := by
    have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k
    rw [← this]; exact hk2
  obtain ⟨a, ha⟩ := HeightOneSpectrum.exists_valuation_sub_lt_of_integer v hkv (Units.mk0 g hg)
  refine ⟨algebraMap K (v.adicCompletion K) (algebraMap R K a), hγ ?_, a, rfl⟩
  simp only [Set.mem_ofPred_eq]
  rw [Valuation.restrict_lt_iff_lt_embedding, ← hgdef]
  have e : algebraMap K (v.adicCompletion K) (algebraMap R K a) - w =
      algebraMap K (v.adicCompletion K) (algebraMap R K a - k) + (algebraMap K (v.adicCompletion K) k - w) := by
    rw [map_sub]; ring
  rw [e]
  refine Valuation.map_add_lt _ ?_ hk1
  have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (algebraMap R K a - k)
  rw [show algebraMap K (v.adicCompletion K) (algebraMap R K a - k) = ((algebraMap R K a - k : K) : v.adicCompletion K) from rfl, this]
  simpa using ha

/- English proof (translation)
The claim follows from `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k`.
-/
theorem valAlg_adic {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K]
    [IsFractionRing R K] (v : HeightOneSpectrum R) (k : K) :
    Valued.v (algebraMap K (v.adicCompletion K) k) = v.valuation K k :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k

/- English proof (translation)
Establish `e : {ζ : Matrix m n (v.adicCompletion K) | ∀ i j, t * ζ i j ∈ v.adicCompletionIntegers K} = ⋂ i, ⋂ j, (fun ζ : Matrix m n (v.adicCompletion K) => t * ζ i j) ⁻¹' ((v.adicCompletionIntegers K : ValuationSubring _) : Set (v.adicCompletion K))`. Use extensionality with `ζ`. Simplify using `[Set.mem_iInter]`. Rewrite using `[e]`. Conclude with `isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (Valued.isOpen_valuationSubring (v.adicCompletion K)).preimage (continuous_const.mul (continuous_id.matrix_elem i j))`.
-/
theorem isOpen_boxW_adic {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K]
    [IsFractionRing R K] (v : HeightOneSpectrum R) (m n : Type) [Fintype m] [Fintype n] (t : v.adicCompletion K) :
    IsOpen {ζ : Matrix m n (v.adicCompletion K) | ∀ i j, t * ζ i j ∈ v.adicCompletionIntegers K} := by
  have e : {ζ : Matrix m n (v.adicCompletion K) | ∀ i j, t * ζ i j ∈ v.adicCompletionIntegers K} =
      ⋂ i, ⋂ j, (fun ζ : Matrix m n (v.adicCompletion K) => t * ζ i j) ⁻¹'
        ((v.adicCompletionIntegers K : ValuationSubring _) : Set (v.adicCompletion K)) := by
    ext ζ; simp [Set.mem_iInter]
  rw [e]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (Valued.isOpen_valuationSubring (v.adicCompletion K)).preimage
      (continuous_const.mul (continuous_id.matrix_elem i j))

/- English proof (translation)
Introduce `ζ hζ`. Use `set e := algebraMap K (v.adicCompletion K) (algebraMap R K d) with he`. Establish `hne : e ≠ 0` using `(map_ne_zero _).mpr ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hd)`. Set `T : Set (v.adicCompletion K)` to `Set.range fun r : R => e * algebraMap K (v.adicCompletion K) (algebraMap R K r)`. Establish `hT : ∀ i j, ζ i j ∈ closure T`.

Introduce `i j`. Establish `h1` using `denseInt_adic v _ (hζ i j)`. Establish `h2 : ζ i j = e * (e⁻¹ * ζ i j)` using `by rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]`. Rewrite using `[h2]`. Conclude with `map_mem_closure (continuous_const.mul continuous_id) h1 (by rintro _ ⟨r, rfl⟩; exact ⟨r, rfl⟩)`.

Establish `hpi : ζ ∈ closure (Set.univ.pi fun _ : m => Set.univ.pi fun _ : n => T)`. Rewrite using `[closure_pi_set]`. Introduce `i _`. Rewrite using `[closure_pi_set]`. Introduce `j _`.

Conclude with `hT i j`. Use `closure_mono ?_ hpi` and prove the remaining obligations. Introduce `ξ hξ`. Use `choose A hA using fun i j => hξ i (Set.mem_univ _) j (Set.mem_univ _)`. Use `⟨(algebraMap R K d) • (Matrix.of A).map (algebraMap R K), hM (Matrix.of A), ?_⟩` and prove the remaining obligations.

Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Simplify using `only [matI, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, Matrix.of_apply]`. Conclude with `hA i j`.
-/
theorem boxW_sub_closure {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K]
    [IsFractionRing R K] (v : HeightOneSpectrum R) {m n : Type} (M : Set (Matrix m n K)) (d : R) (hd : d ≠ 0)
    (hM : LowB d M) :
    {ζ : Matrix m n (v.adicCompletion K) |
        ∀ i j, (algebraMap K (v.adicCompletion K) (algebraMap R K d))⁻¹ * ζ i j ∈ v.adicCompletionIntegers K} ⊆
      closure (matI v '' M) := by
  intro ζ hζ
  set e := algebraMap K (v.adicCompletion K) (algebraMap R K d) with he
  have hne : e ≠ 0 := (map_ne_zero _).mpr ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hd)
  let T : Set (v.adicCompletion K) := Set.range fun r : R => e * algebraMap K (v.adicCompletion K) (algebraMap R K r)
  have hT : ∀ i j, ζ i j ∈ closure T := by
    intro i j
    have h1 := denseInt_adic v _ (hζ i j)
    have h2 : ζ i j = e * (e⁻¹ * ζ i j) := by rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    rw [h2]
    exact map_mem_closure (continuous_const.mul continuous_id) h1 (by rintro _ ⟨r, rfl⟩; exact ⟨r, rfl⟩)
  have hpi : ζ ∈ closure (Set.univ.pi fun _ : m => Set.univ.pi fun _ : n => T) := by
    rw [closure_pi_set]; intro i _; rw [closure_pi_set]; intro j _; exact hT i j
  refine closure_mono ?_ hpi
  intro ξ hξ
  choose A hA using fun i j => hξ i (Set.mem_univ _) j (Set.mem_univ _)
  refine ⟨(algebraMap R K d) • (Matrix.of A).map (algebraMap R K), hM (Matrix.of A), ?_⟩
  refine Matrix.ext fun i j => ?_
  simp only [matI, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, Matrix.of_apply]
  exact hA i j

/- English proof (translation)
Introduce `R _ _ K _ _ _ v m n _ _ M M' d hd hM' z hz`. Use `set e := algebraMap K (v.adicCompletion K) (algebraMap R K d)`. Establish `hU : {x | z - x ∈ {ζ : Matrix m n (v.adicCompletion K) | ∀ i j, e⁻¹ * ζ i j ∈ v.adicCompletionIntegers K}} ∈ 𝓝 z` using `((isOpen_boxW_adic v m n e⁻¹).preimage (continuous_const.sub continuous_id)).mem_nhds (by show ∀ i j, e⁻¹ * (z - z) i j ∈ v.adicCompletionIntegers K`. Introduce `i j`. Rewrite using `[sub_self, Matrix.zero_apply, mul_zero]`.

Conclude with `zero_mem _)`. Take `⟨_, hx, A, hA, rfl⟩` from `mem_closure_iff_nhds.mp hz _ hU`. Conclude with `⟨A, hA, boxW_sub_closure v _ d hd hM' hx⟩`.
-/
theorem low_approximation_holds : ApproxLow := by
  intro R _ _ K _ _ _ v m n _ _ M M' d hd hM' z hz
  set e := algebraMap K (v.adicCompletion K) (algebraMap R K d)
  have hU : {x | z - x ∈ {ζ : Matrix m n (v.adicCompletion K) | ∀ i j, e⁻¹ * ζ i j ∈ v.adicCompletionIntegers K}} ∈ 𝓝 z :=
    ((isOpen_boxW_adic v m n e⁻¹).preimage (continuous_const.sub continuous_id)).mem_nhds
      (by show ∀ i j, e⁻¹ * (z - z) i j ∈ v.adicCompletionIntegers K
          intro i j; rw [sub_self, Matrix.zero_apply, mul_zero]; exact zero_mem _)
  obtain ⟨_, hx, A, hA, rfl⟩ := mem_closure_iff_nhds.mp hz _ hU
  exact ⟨A, hA, boxW_sub_closure v _ d hd hM' hx⟩

/- English proof (translation)
Introduce `R _ _ K _ _ _ v m n _ _ M d hd hM y`. Use `set e := algebraMap K (v.adicCompletion K) (algebraMap R K d) with he`. Establish `hdK : algebraMap R K d ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hd`. Prove the components needed by the constructor for the conclusion. Introduce `hy`.

Establish `hU : {x | matI v y - x ∈ {ζ : Matrix m n (v.adicCompletion K) | ∀ i j, e⁻¹ * ζ i j ∈ v.adicCompletionIntegers K}} ∈ 𝓝 (matI v y)` using `((isOpen_boxW_adic v m n e⁻¹).preimage (continuous_const.sub continuous_id)).mem_nhds (by show ∀ i j, e⁻¹ * (matI v y - matI v y) i j ∈ v.adicCompletionIntegers K`. Introduce `i j`. Rewrite using `[sub_self, Matrix.zero_apply, mul_zero]`. Conclude with `zero_mem _)`. Take `⟨_, hx, A, hA, rfl⟩` from `mem_closure_iff_nhds.mp hy _ hU`.

Establish `hx' : ∀ p : m × n, v.valuation K ((y p.1 p.2 - A p.1 p.2) / algebraMap R K d) ≤ 1`. Introduce `p`. Rewrite using `[← valAlg_adic v]`. Establish `h` using `hx p.1 p.2`. Establish `e2 : algebraMap K (v.adicCompletion K) ((y p.1 p.2 - A p.1 p.2) / algebraMap R K d) = e⁻¹ * (matI v y - matI v A) p.1 p.2`.

Simplify using `only [matI, Matrix.sub_apply, Matrix.map_apply, map_div₀, map_sub, he]`. Rewrite using `[div_eq_inv_mul]`. Rewrite using `[e2]`. Conclude with `h`. Use `choose nn ss hns using fun p : m × n => HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v _ (hx' p)`.

Use `⟨∏ p, (ss p : R), ?_, ?_⟩` and prove the remaining obligations. Conclude with `Submonoid.prod_mem _ fun p _ => (ss p).2`. Use `choose c hc using fun p : m × n => Finset.dvd_prod_of_mem (fun p => (ss p : R)) (Finset.mem_univ p)`. Establish `key : (∏ p, (ss p : R)) • (y - A) = (algebraMap R K d) • (Matrix.of fun i j => c (i, j) * nn (i, j)).map (algebraMap R K)`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations.

Simplify using `only [Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.of_apply, smul_eq_mul, Algebra.smul_def, map_mul]`. Rewrite using `[← hns (i, j), hc (i, j), map_mul]`. Clear the denominators using the available nonvanishing facts. Establish `: (∏ p, (ss p : R)) • y = (∏ p, (ss p : R)) • (y - A) + (∏ p, (ss p : R)) • A`. Rewrite using `[smul_sub, sub_add_cancel]`.

Rewrite using `[this, key]`. Conclude with `M.add_mem (hM _) (M.smul_mem _ hA)`. Introduce and unpack `⟨s, hs, hsy⟩ set es := algebraMap K (v.adicCompletion K) (algebraMap R K s) with hes`. Establish `hs0 : s ≠ 0` using `by rintro rfl; exact hs (zero_mem _)`. Establish `hne : es ≠ 0` using `(map_ne_zero _).mpr ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hs0)`.

Establish `hval : Valued.v es⁻¹ ≤ 1`. Rewrite using `[map_inv₀, hes, valAlg_adic v, HeightOneSpectrum.valuation_of_algebraMap, (HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl v s).mpr hs, inv_one]`. Establish `h1` using `denseInt_adic v _ hval`. Establish `key` using `map_mem_closure (f := fun c : v.adicCompletion K => c • matI v (s • y)) (t := matI v '' (M : Set (Matrix m n K))) (continuous_id.smul continuous_const) h1 (by`. Introduce and unpack `_ ⟨r, rfl⟩`.

Use `⟨r • s • y, M.smul_mem r hsy, ?_⟩` and prove the remaining obligations. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Simplify using `only [matI, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Algebra.smul_def, map_mul, Algebra.algebraMap_self, RingHom.id_apply])`. Use `key using 1` and compare the differences between its conclusion and the goal. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations.

Simplify using `only [matI, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Algebra.smul_def, map_mul, Algebra.algebraMap_self, RingHom.id_apply, ← hes]`. Rewrite using `[inv_mul_cancel_left₀ hne]`.
-/
theorem closure_character_holds : ClosChar := by
  intro R _ _ K _ _ _ v m n _ _ M d hd hM y
  set e := algebraMap K (v.adicCompletion K) (algebraMap R K d) with he
  have hdK : algebraMap R K d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hd
  constructor
  · intro hy
    have hU : {x | matI v y - x ∈ {ζ : Matrix m n (v.adicCompletion K) | ∀ i j, e⁻¹ * ζ i j ∈ v.adicCompletionIntegers K}} ∈ 𝓝 (matI v y) :=
      ((isOpen_boxW_adic v m n e⁻¹).preimage (continuous_const.sub continuous_id)).mem_nhds
        (by show ∀ i j, e⁻¹ * (matI v y - matI v y) i j ∈ v.adicCompletionIntegers K
            intro i j; rw [sub_self, Matrix.zero_apply, mul_zero]; exact zero_mem _)
    obtain ⟨_, hx, A, hA, rfl⟩ := mem_closure_iff_nhds.mp hy _ hU
    have hx' : ∀ p : m × n, v.valuation K ((y p.1 p.2 - A p.1 p.2) / algebraMap R K d) ≤ 1 := by
      intro p
      rw [← valAlg_adic v]
      have h := hx p.1 p.2
      have e2 : algebraMap K (v.adicCompletion K) ((y p.1 p.2 - A p.1 p.2) / algebraMap R K d) =
          e⁻¹ * (matI v y - matI v A) p.1 p.2 := by
        simp only [matI, Matrix.sub_apply, Matrix.map_apply, map_div₀, map_sub, he]
        rw [div_eq_inv_mul]
      rw [e2]; exact h
    choose nn ss hns using fun p : m × n => HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v _ (hx' p)
    refine ⟨∏ p, (ss p : R), ?_, ?_⟩
    · exact Submonoid.prod_mem _ fun p _ => (ss p).2
    · choose c hc using fun p : m × n => Finset.dvd_prod_of_mem (fun p => (ss p : R)) (Finset.mem_univ p)
      have key : (∏ p, (ss p : R)) • (y - A) =
          (algebraMap R K d) • (Matrix.of fun i j => c (i, j) * nn (i, j)).map (algebraMap R K) := by
        refine Matrix.ext fun i j => ?_
        simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.of_apply, smul_eq_mul,
          Algebra.smul_def, map_mul]
        rw [← hns (i, j), hc (i, j), map_mul]
        field_simp
      have : (∏ p, (ss p : R)) • y = (∏ p, (ss p : R)) • (y - A) + (∏ p, (ss p : R)) • A := by
        rw [smul_sub, sub_add_cancel]
      rw [this, key]
      exact M.add_mem (hM _) (M.smul_mem _ hA)
  · rintro ⟨s, hs, hsy⟩
    set es := algebraMap K (v.adicCompletion K) (algebraMap R K s) with hes
    have hs0 : s ≠ 0 := by rintro rfl; exact hs (zero_mem _)
    have hne : es ≠ 0 := (map_ne_zero _).mpr ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hs0)
    have hval : Valued.v es⁻¹ ≤ 1 := by
      rw [map_inv₀, hes, valAlg_adic v, HeightOneSpectrum.valuation_of_algebraMap,
        (HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl v s).mpr hs, inv_one]
    have h1 := denseInt_adic v _ hval
    have key := map_mem_closure (f := fun c : v.adicCompletion K => c • matI v (s • y))
      (t := matI v '' (M : Set (Matrix m n K))) (continuous_id.smul continuous_const) h1 (by
        rintro _ ⟨r, rfl⟩
        refine ⟨r • s • y, M.smul_mem r hsy, ?_⟩
        refine Matrix.ext fun i j => ?_
        simp only [matI, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Algebra.smul_def, map_mul,
          Algebra.algebraMap_self, RingHom.id_apply])
    convert key using 1
    refine Matrix.ext fun i j => ?_
    simp only [matI, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Algebra.smul_def, map_mul,
      Algebra.algebraMap_self, RingHom.id_apply, ← hes]
    rw [inv_mul_cancel_left₀ hne]

end Formalism.L2.PairingIndexBounds.Rec
