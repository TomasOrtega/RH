import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContinuousHermScal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.LenFib

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R]

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r e => simp [sigR, OneHerm.sigma_sigma hσ]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`.
-/
theorem sigR_sigR {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) (y : R ⊗[F] E) :
    sigR R σ (sigR R σ y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, OneHerm.sigma_sigma hσ]
  | add a b ha hb => simp only [map_add, ha, hb]

/- English proof (translation)
Establish `hJR : ∀ i j, sigR R σ (JR R J i j) = JR R J j i`. Introduce `i j`. Establish `h` using `hJ.1 j i`. Simplify using `only [JR, Matrix.map_apply, inclR, sigR]`. Simplify using `[h]`.

Unfold `hR hform`. Rewrite using `[map_sum, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, map_mul, sigR_sigR R hσ, hJR]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hR_self_fixed {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (x : Fin M → R ⊗[F] E) :
    sigR R σ (hR R σ J x x) = hR R σ J x x := by
  have hJR : ∀ i j, sigR R σ (JR R J i j) = JR R J j i := by
    intro i j
    have h := hJ.1 j i
    simp only [JR, Matrix.map_apply, inclR, sigR]
    simp [h]
  unfold hR hform
  rw [map_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_mul, sigR_sigR R hσ, hJR]
  ring

def gramH {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (X : Fin 1 → Fin M → R ⊗[F] E) :
    HermR R σ 1 :=
  ⟨gramR R σ J X, by
    intro a b
    have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    subst ha hb
    exact hR_self_fixed R hσ hJ (X 0)⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem qR_eq_hermHalf {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (X : Fin 1 → Fin M → R ⊗[F] E) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (X 0) = OneHerm.hermHalf R σ (gramH R hσ hJ X) :=
  rfl

/- English proof (translation)
Rewrite using `[qR_eq_hermHalf R hσ hJ X, OneHerm.hermScal_hermHalf R hσ]`. Both sides reduce to the same expression.
-/
theorem hermScal_qR [TopologicalSpace R] [IsTopologicalRing R] {σ : E →ₐ[F] E}
    (hσ : IsCMExt F E σ) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (X : Fin 1 → Fin M → R ⊗[F] E) :
    ((hermScal R σ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (X 0)) : HermR R σ 1) :
      Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) = gramR R σ J X := by
  rw [qR_eq_hermHalf R hσ hJ X, OneHerm.hermScal_hermHalf R hσ]
  rfl

/- English proof (translation)
Establish `h' : gramH R hσ hJ X = hermScal R σ c` using `Subtype.ext h`. Rewrite using `[qR_eq_hermHalf R hσ hJ X, h', OneHerm.hermHalf_hermScal R hσ]`.
-/
theorem qR_of_gram [TopologicalSpace R] [IsTopologicalRing R] {σ : E →ₐ[F] E}
    (hσ : IsCMExt F E σ) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) {X : Fin 1 → Fin M → R ⊗[F] E} {c : R}
    (h : gramR R σ J X = ((hermScal R σ c : HermR R σ 1) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E))) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (X 0) = c := by
  have h' : gramH R hσ hJ X = hermScal R σ c := Subtype.ext h
  rw [qR_eq_hermHalf R hσ hJ X, h', OneHerm.hermHalf_hermScal R hσ]

/- English proof (translation)
Rewrite using `[Matrix.det_fin_one]`. Conclude with `hc.map (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[F] E)`.
-/
theorem isUnit_det_hermScal (σ : E →ₐ[F] E) {c : R} (hc : IsUnit c) :
    IsUnit ((hermScal R σ c : HermR R σ 1) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det := by
  rw [Matrix.det_fin_one]
  exact hc.map (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[F] E)

/- English proof (translation)
Rewrite using `[← hermScal_qR R hσ hJ X]`. Conclude with `isUnit_det_hermScal R σ h`.
-/
theorem isUnit_det_gramR [TopologicalSpace R] [IsTopologicalRing R] {σ : E →ₐ[F] E}
    (hσ : IsCMExt F E σ) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) {X : Fin 1 → Fin M → R ⊗[F] E}
    (h : IsUnit (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (X 0))) : IsUnit (gramR R σ J X).det := by
  rw [← hermScal_qR R hσ hJ X]
  exact isUnit_det_hermScal R σ h

/- English proof (translation)
Take `⟨-, -, -, -, -, htr, -, -, -, hgr⟩` from `TopK.topTens_props F E σ hσ R`. Establish `h` using `(hgr 1 M J).matrix_elem 0 0`. Conclude with `continuous_const.mul (htr.comp h)`.
-/
theorem continuous_qR {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] :
    Continuous fun X : Fin 1 → Fin M → R ⊗[F] E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (X 0) := by
  obtain ⟨-, -, -, -, -, htr, -, -, -, hgr⟩ := TopK.topTens_props F E σ hσ R
  have h := (hgr 1 M J).matrix_elem 0 0
  exact continuous_const.mul (htr.comp h)

/- English proof (translation)
Take `⟨K, hK, hcK, hKU⟩` from `exists_compact_subset hU hc₀`. Take `⟨f, hf1, -, hfs, -⟩` from `exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU`. Use `⟨f, f.continuous, hfs, ?_⟩` and prove the remaining obligations. Use `filter_upwards [mem_interior_iff_mem_nhds.mp hcK] with c hc using hf1 hc`.
-/
theorem exists_bump [TopologicalSpace R] [LocallyCompactSpace R] [T2Space R]
    (hU : IsOpen {c : R | IsUnit c}) {c₀ : R} (hc₀ : IsUnit c₀) :
    ∃ χ : R → ℝ, Continuous χ ∧ tsupport χ ⊆ {c : R | IsUnit c} ∧ ∀ᶠ c in 𝓝 c₀, χ c = 1 := by
  obtain ⟨K, hK, hcK, hKU⟩ := exists_compact_subset hU hc₀
  obtain ⟨f, hf1, -, hfs, -⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
  refine ⟨f, f.continuous, hfs, ?_⟩
  filter_upwards [mem_interior_iff_mem_nhds.mp hcK] with c hc using hf1 hc

end GlobalTheory.CompanionTheory.SW.LenFib

open GlobalTheory.CompanionTheory.SW.LenFib in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hLoc μ ν _ _ _ hμ0 m hm`. Take `⟨hTR, hLC, hSC, hT2, -, -, hOE, -⟩` from `hLoc`. Use `haveI := hTR`. Use `haveI := hLC`. Use `haveI := hSC`.

Use `haveI := hT2`. Use `haveI : BorelSpace (HermR R σ 1) := ⟨rfl⟩`. Take `⟨hfib, hint, hcont⟩` from `hm`. Use `set q : (Fin 1 → Fin M → R ⊗[F] E) → R := fun X => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (X 0) with hq`. Establish `hqc : Continuous q` using `continuous_qR R hσ J`.

Establish `hUo : IsOpen {c : R | IsUnit c}`. Establish `h` using `hOE.isOpen_range`. Establish `he : Set.range (Units.val : Rˣ → R) = {c : R | IsUnit c}`. Use extensionality with `c`. Conclude with `Iff.rfl`.

Rewrite `h` using `[he]`. Then use the resulting hypothesis. Establish `hemb : MeasurableEmbedding (hermScal R σ)` using `(OneHerm.hermHomeo R hσ).measurableEmbedding`. Establish `hsub : ∀ X, IsUnit (q X) → IsUnit (gramR R σ J X).det` using `fun X h => isUnit_det_gramR R hσ hJ h`. Establish `hres : μ.restrict {X | IsUnit (gramR R σ J X).det} = μ`. Use `Measure.restrict_eq_self_of_ae_mem ?_` and prove the remaining obligations.

Use `measure_mono_null ?_ hμ0` and prove the remaining obligations. Introduce `X hX hXq`. Conclude with `hX (hsub X hXq)`. Establish `hae : ∀ c, ∀ᵐ X ∂(m (hermScal R σ c)), q X = c`. Introduce `c`.

Use `measure_mono_null ?_ (hfib (hermScal R σ c))` and prove the remaining obligations. Introduce `X hX hXm`. Conclude with `hX (qR_of_gram R hσ hJ hXm.1)`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `c`.

Use `measure_mono_null ?_ (hae c)` and prove the remaining obligations. Introduce `X hX hXq`. Conclude with `hX ⟨hXq, Set.mem_univ X⟩`. Introduce `φ hφ`. Establish `h` using `hint φ hφ`.

Rewrite `h` using `[hres, hemb.lintegral_map]`. Rewrite using `[Measure.restrict_univ, h]`. Introduce `φ hφc hφs _`. Establish `key : ∀ c₀, IsUnit c₀ → Integrable φ (m (hermScal R σ c₀)) ∧ ContinuousWithinAt (fun c => ∫ v, φ v ∂(m (hermScal R σ c))) {c | IsUnit c} c₀`. Introduce `c₀ hc₀`.

Take `⟨χ, hχc, hχs, hχ1⟩` from `exists_bump R hUo hc₀`. Establish `hφ'c : Continuous fun X => φ X * χ (q X)` using `hφc.mul (hχc.comp hqc)`. Establish `hφ's : HasCompactSupport fun X => φ X * χ (q X)` using `HasCompactSupport.mul_right hφs`. Establish `hφ't : tsupport (fun X => φ X * χ (q X)) ⊆ {X | IsUnit (gramR R σ J X).det}`. Introduce `X hX`.

Establish `h1 : X ∈ tsupport (χ ∘ q)` using `tsupport_mul_subset_right hX`. Conclude with `hsub X (hχs (tsupport_comp_subset_preimage χ hqc h1))`. Take `⟨hI, hC⟩` from `hcont _ hφ'c hφ's hφ't`. Establish `heq : ∀ c, χ c = 1 → (fun X => φ X * χ (q X)) =ᵐ[m (hermScal R σ c)] φ`. Introduce `c hc`.

Use `filter_upwards [hae c] with X hX`. Rewrite using `[hX, hc, mul_one]`. Establish `hmaps : Set.MapsTo (hermScal R σ) {c : R | IsUnit c} {S : HermR R σ 1 | IsUnit (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det}` using `fun c hc => isUnit_det_hermScal R σ hc`. Establish `hC' : ContinuousOn (fun c => ∫ v, φ v * χ (q v) ∂(m (hermScal R σ c))) {c | IsUnit c}` using `hC.comp (OneHerm.continuous_hermScal R σ).continuousOn hmaps`. Use `⟨(hI _ (hmaps hc₀)).congr (heq c₀ hχ1.self_of_nhds), ?_⟩` and prove the remaining obligations.

Use `(hC' c₀ hc₀).congr_of_eventuallyEq ?_ ?_` and prove the remaining obligations. Use `filter_upwards [mem_nhdsWithin_of_mem_nhds hχ1] with c hc`. Conclude with `(integral_congr_ae (heq c hc)).symm`. Conclude with `(integral_congr_ae (heq c₀ hχ1.self_of_nhds)).symm`. Conclude with `⟨fun c hc => (key c hc).1, fun c hc => (key c hc).2⟩`.
-/
theorem GlobalTheory.CompanionTheory.SW.isFibreFamily_length : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (μ : Measure (Fin 1 → Fin M → R ⊗[F] E)) (ν : Measure R), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ν {c | ¬ IsUnit c} = 0 → μ {X | ¬ IsUnit ((fun X : Fin 1 → Fin M → R ⊗[F] E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (R) σ J (X 0)) X)} = 0 → ∀ m, IsGramFib R σ J 1 μ (ν.map (hermScal R σ)) m → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (fun X : Fin 1 → Fin M → R ⊗[F] E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (R) σ J (X 0)) id Set.univ ν {c | IsUnit c} (fun c => m (hermScal R σ c)) := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hLoc μ ν _ _ _ hμ0 m hm
  obtain ⟨hTR, hLC, hSC, hT2, -, -, hOE, -⟩ := hLoc
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI : BorelSpace (HermR R σ 1) := ⟨rfl⟩
  obtain ⟨hfib, hint, hcont⟩ := hm
  set q : (Fin 1 → Fin M → R ⊗[F] E) → R := fun X => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (X 0) with hq
  have hqc : Continuous q := continuous_qR R hσ J
  have hUo : IsOpen {c : R | IsUnit c} := by
    have h := hOE.isOpen_range
    have he : Set.range (Units.val : Rˣ → R) = {c : R | IsUnit c} := by
      ext c
      exact Iff.rfl
    rwa [he] at h
  have hemb : MeasurableEmbedding (hermScal R σ) := (OneHerm.hermHomeo R hσ).measurableEmbedding
  have hsub : ∀ X, IsUnit (q X) → IsUnit (gramR R σ J X).det := fun X h =>
    isUnit_det_gramR R hσ hJ h
  have hres : μ.restrict {X | IsUnit (gramR R σ J X).det} = μ := by
    refine Measure.restrict_eq_self_of_ae_mem ?_
    refine measure_mono_null ?_ hμ0
    intro X hX hXq
    exact hX (hsub X hXq)
  have hae : ∀ c, ∀ᵐ X ∂(m (hermScal R σ c)), q X = c := by
    intro c
    refine measure_mono_null ?_ (hfib (hermScal R σ c))
    intro X hX hXm
    exact hX (qR_of_gram R hσ hJ hXm.1)
  refine ⟨?_, ?_, ?_⟩
  · intro c
    refine measure_mono_null ?_ (hae c)
    intro X hX hXq
    exact hX ⟨hXq, Set.mem_univ X⟩
  · intro φ hφ
    have h := hint φ hφ
    rw [hres, hemb.lintegral_map] at h
    rw [Measure.restrict_univ, h]
  · intro φ hφc hφs _
    have key : ∀ c₀, IsUnit c₀ → Integrable φ (m (hermScal R σ c₀)) ∧
        ContinuousWithinAt (fun c => ∫ v, φ v ∂(m (hermScal R σ c))) {c | IsUnit c} c₀ := by
      intro c₀ hc₀
      obtain ⟨χ, hχc, hχs, hχ1⟩ := exists_bump R hUo hc₀
      have hφ'c : Continuous fun X => φ X * χ (q X) := hφc.mul (hχc.comp hqc)
      have hφ's : HasCompactSupport fun X => φ X * χ (q X) := HasCompactSupport.mul_right hφs
      have hφ't : tsupport (fun X => φ X * χ (q X)) ⊆ {X | IsUnit (gramR R σ J X).det} := by
        intro X hX
        have h1 : X ∈ tsupport (χ ∘ q) := tsupport_mul_subset_right hX
        exact hsub X (hχs (tsupport_comp_subset_preimage χ hqc h1))
      obtain ⟨hI, hC⟩ := hcont _ hφ'c hφ's hφ't
      have heq : ∀ c, χ c = 1 → (fun X => φ X * χ (q X)) =ᵐ[m (hermScal R σ c)] φ := by
        intro c hc
        filter_upwards [hae c] with X hX
        rw [hX, hc, mul_one]
      have hmaps : Set.MapsTo (hermScal R σ) {c : R | IsUnit c}
          {S : HermR R σ 1 | IsUnit (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det} :=
        fun c hc => isUnit_det_hermScal R σ hc
      have hC' : ContinuousOn (fun c => ∫ v, φ v * χ (q v) ∂(m (hermScal R σ c))) {c | IsUnit c} :=
        hC.comp (OneHerm.continuous_hermScal R σ).continuousOn hmaps
      refine ⟨(hI _ (hmaps hc₀)).congr (heq c₀ hχ1.self_of_nhds), ?_⟩
      refine (hC' c₀ hc₀).congr_of_eventuallyEq ?_ ?_
      · filter_upwards [mem_nhdsWithin_of_mem_nhds hχ1] with c hc
        exact (integral_congr_ae (heq c hc)).symm
      · exact (integral_congr_ae (heq c₀ hχ1.self_of_nhds)).symm
    exact ⟨fun c hc => (key c hc).1, fun c hc => (key c hc).2⟩
