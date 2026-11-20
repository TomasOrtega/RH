import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.HaarCoord

/- English proof (translation)
Set `h : G ≃ₜ H` to `hf.homeomorph f`. Set `e : H ≃+ G` to `(AddEquiv.mk' h.toEquiv hadd).symm`. Establish `hc : Measure.comap f μ = Measure.map e μ` using `(MeasurableEquiv.map_symm (μ := μ) h.toMeasurableEquiv).symm`. Rewrite using `[hc]`. Conclude with `e.isAddHaarMeasure_map μ h.symm.continuous h.continuous`.
-/
theorem haar_comap {G H : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [AddGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    [MeasurableSpace H] [BorelSpace H] (f : G → H) (hadd : ∀ x y, f (x + y) = f x + f y)
    (hf : IsHomeomorph f) (μ : Measure H) [μ.IsAddHaarMeasure] :
    (Measure.comap f μ).IsAddHaarMeasure := by
  let h : G ≃ₜ H := hf.homeomorph f
  let e : H ≃+ G := (AddEquiv.mk' h.toEquiv hadd).symm
  have hc : Measure.comap f μ = Measure.map e μ :=
    (MeasurableEquiv.map_symm (μ := μ) h.toMeasurableEquiv).symm
  rw [hc]
  exact e.isAddHaarMeasure_map μ h.symm.continuous h.continuous

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

/- English proof (translation)
Take `⟨-, htc, -, hτ⟩` from `h`. Take `⟨v⟩ : Nonempty (InfinitePlace E)` from `inferInstance`. Establish `hinv : ∀ x, σ (σ x) = x` using `fun x => v.embedding.injective (by rw [hτ, hτ, star_star])`. Use `⟨hinv, ?_⟩` and prove the remaining obligations. Establish `hne : ∃ x, σ x ≠ x`.

Assume the negation of the conclusion as `hall`. Use `push_neg at hall`. Establish `hc : ¬ ComplexEmbedding.IsReal v.embedding` using `InfinitePlace.isComplex_iff.mp (htc.isComplex v)`. Apply `hc` to reduce the goal to its premises. Rewrite using `[ComplexEmbedding.isReal_iff]`.

Use extensionality with `x`. Use `hτ v.embedding x` as an intermediate fact. Rewrite `this` using `[hall]`. Simplify `this.symm` using `[ComplexEmbedding.conjugate_coe_eq]`. Take `⟨x, hx⟩` from `hne`.

Use `⟨x - σ x, sub_ne_zero.mpr (Ne.symm hx), ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, hinv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem conj_facts [NumberField F] [NumberField E] {σ : E →ₐ[F] E} (h : IsCMExt F E σ) :
    (∀ x, σ (σ x) = x) ∧ ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  obtain ⟨-, htc, -, hτ⟩ := h
  obtain ⟨v⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hinv : ∀ x, σ (σ x) = x := fun x =>
    v.embedding.injective (by rw [hτ, hτ, star_star])
  refine ⟨hinv, ?_⟩
  have hne : ∃ x, σ x ≠ x := by
    by_contra hall
    push_neg at hall
    have hc : ¬ ComplexEmbedding.IsReal v.embedding :=
      InfinitePlace.isComplex_iff.mp (htc.isComplex v)
    apply hc
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have := hτ v.embedding x
    rw [hall] at this
    simpa [ComplexEmbedding.conjugate_coe_eq] using this.symm
  obtain ⟨x, hx⟩ := hne
  refine ⟨x - σ x, sub_ne_zero.mpr (Ne.symm hx), ?_⟩
  rw [map_sub, hinv]
  ring

variable (R : Type) [CommRing R] [Algebra F R]

/- English proof (translation)
Simplify using `[sigR]`.
-/
theorem sigR_tmul (σ : E →ₐ[F] E) (r : R) (e : E) :
    sigR R σ (r ⊗ₜ[F] e) = r ⊗ₜ[F] σ e := by
  simp [sigR]

/- English proof (translation)
Proceed by induction on `y with`. Consider the case `zero => simp`. Consider the case `tmul r e => rw [sigR_tmul, sigR_tmul, hinv]`. Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb]`.
-/
theorem sigR_sigR {σ : E →ₐ[F] E} (hinv : ∀ x, σ (σ x) = x) (y : R ⊗[F] E) :
    sigR R σ (sigR R σ y) = y := by
  induction y with
  | zero => simp
  | tmul r e => rw [sigR_tmul, sigR_tmul, hinv]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

/- English proof (translation)
Establish `h2 : algebraMap F R (1 / 2) * 2 = 1`. Rewrite using `[← map_ofNat (algebraMap F R) 2, ← map_mul]`. Evaluate the numerical expressions. Rewrite using `[← two_mul, ← mul_assoc, h2, one_mul]`.
-/
theorem half_add_self [CharZero F] (r : R) : algebraMap F R (1 / 2) * (r + r) = r := by
  have h2 : algebraMap F R (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap F R) 2, ← map_mul]
    norm_num
  rw [← two_mul, ← mul_assoc, h2, one_mul]

/- English proof (translation)
Establish `hli : LinearIndependent F ![(1 : E), δ]`. Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t hst`. Establish `h'` using `congrArg σ hst`. Simplify using `only [map_add, map_smul, map_one, hσδ, map_zero, smul_neg] at h'`.

Establish `ht2 : (t + t) • δ = 0`. Rewrite using `[add_smul]`. Use `sub_eq_zero.mpr (hst.trans h'.symm)` as an intermediate fact. Rewrite using `[← this]`. Normalize the expressions using the abelian group laws.

Establish `ht : t = 0`. Break down `smul_eq_zero.mp ht2 with h | h` into its components or cases. Establish `: (2 : F) * t = 0` using `by rw [two_mul]; exact h`. Simplify using `using this`. Conclude with `absurd h hδ`.

Substitute `ht` using the available equality. Simplify using `using hst`. Set `B : Module.Basis (Fin 2) F E` to `basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])`. Establish `hB : ⇑B = ![(1 : E), δ]` using `coe_basisOfLinearIndependentOfCardEqFinrank _ _`. Set `C` to `Algebra.TensorProduct.basis R B`.

Establish `hC0 : C 0 = (1 : R) ⊗ₜ[F] (1 : E)`. Simplify using `[C, Algebra.TensorProduct.basis_apply, hB]`. Establish `hC1 : C 1 = (1 : R) ⊗ₜ[F] δ`. Simplify using `[C, Algebra.TensorProduct.basis_apply, hB]`. Take `⟨r0, r1, hy'⟩ : ∃ r0 r1 : R, y = r0 • C 0 + r1 • C 1` from `⟨C.repr y 0, C.repr y 1, by`.

Use `C.sum_repr y` as an intermediate fact. Rewrite `this` using `[Fin.sum_univ_two]`. Conclude with `this.symm⟩`. Establish `hs : sigR R σ y = r0 • C 0 + (-r1) • C 1`. Rewrite using `[hy', hC0, hC1]`.

Simplify using `only [TensorProduct.smul_tmul', smul_eq_mul, mul_one, map_add, sigR_tmul, map_one, hσδ, TensorProduct.tmul_neg, TensorProduct.neg_tmul]`. Rewrite `hs` using `[hy]`. Establish `h1 : r1 = -r1`. Use `congrArg (fun z => C.repr z 1) (hy'.symm.trans hs)` as an intermediate fact. Simplify `this` using `[Finsupp.single_apply]`.

Establish `h0 : r1 = 0`. Establish `: r1 + r1 = 0` using `by nth_rw 1 [h1]; ring`. Rewrite using `[← half_add_self (F := F) R r1, this, mul_zero]`. Use `⟨r0, ?_⟩` and prove the remaining obligations. Rewrite using `[hy', h0, hC0]`.

Simplify using `[TensorProduct.smul_tmul']`.
-/
theorem fixed_eq_tmul [CharZero F] {σ : E →ₐ[F] E} (hinv : ∀ x, σ (σ x) = x)
    (h2 : Module.finrank F E = 2) {δ : E} (hδ : δ ≠ 0) (hσδ : σ δ = -δ)
    (y : R ⊗[F] E) (hy : sigR R σ y = y) : ∃ r : R, y = r ⊗ₜ[F] (1 : E) := by
  have hli : LinearIndependent F ![(1 : E), δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h' := congrArg σ hst
    simp only [map_add, map_smul, map_one, hσδ, map_zero, smul_neg] at h'
    have ht2 : (t + t) • δ = 0 := by
      rw [add_smul]
      have := sub_eq_zero.mpr (hst.trans h'.symm)
      rw [← this]
      abel
    have ht : t = 0 := by
      rcases smul_eq_zero.mp ht2 with h | h
      · have : (2 : F) * t = 0 := by rw [two_mul]; exact h
        simpa using this
      · exact absurd h hδ
    subst ht
    simpa using hst
  let B : Module.Basis (Fin 2) F E := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])
  have hB : ⇑B = ![(1 : E), δ] := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  let C := Algebra.TensorProduct.basis R B
  have hC0 : C 0 = (1 : R) ⊗ₜ[F] (1 : E) := by
    simp [C, Algebra.TensorProduct.basis_apply, hB]
  have hC1 : C 1 = (1 : R) ⊗ₜ[F] δ := by
    simp [C, Algebra.TensorProduct.basis_apply, hB]
  obtain ⟨r0, r1, hy'⟩ : ∃ r0 r1 : R, y = r0 • C 0 + r1 • C 1 :=
    ⟨C.repr y 0, C.repr y 1, by
      have := C.sum_repr y
      rw [Fin.sum_univ_two] at this
      exact this.symm⟩
  have hs : sigR R σ y = r0 • C 0 + (-r1) • C 1 := by
    rw [hy', hC0, hC1]
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one, map_add, sigR_tmul, map_one, hσδ,
      TensorProduct.tmul_neg, TensorProduct.neg_tmul]
  rw [hy] at hs
  have h1 : r1 = -r1 := by
    have := congrArg (fun z => C.repr z 1) (hy'.symm.trans hs)
    simpa [Finsupp.single_apply] using this
  have h0 : r1 = 0 := by
    have : r1 + r1 = 0 := by nth_rw 1 [h1]; ring
    rw [← half_add_self (F := F) R r1, this, mul_zero]
  refine ⟨r0, ?_⟩
  rw [hy', h0, hC0]
  simp [TensorProduct.smul_tmul']

/- English proof (translation)
Establish `hfin : Module.Finite F E` using `Module.finite_of_finrank_pos (by omega)`. Set `B : Module.Basis (Fin 2) F E` to `Module.finBasisOfFinrankEq F E h2`. Establish `: s ⊗ₜ[F] (1 : E) = algebraMap R (R ⊗[F] E) s`. Simplify using `[Algebra.TensorProduct.algebraMap_apply]`. Rewrite using `[this, Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis R B)]`.

Simplify using `only [Fintype.card_fin, two_nsmul]`. Conclude with `half_add_self (F := F) R s`.
-/
theorem half_trace_tmul [CharZero F] (h2 : Module.finrank F E = 2) (s : R) :
    algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (s ⊗ₜ[F] (1 : E)) = s := by
  have hfin : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  let B : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E h2
  have : s ⊗ₜ[F] (1 : E) = algebraMap R (R ⊗[F] E) s := by
    simp [Algebra.TensorProduct.algebraMap_apply]
  rw [this, Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis R B)]
  simp only [Fintype.card_fin, two_nsmul]
  exact half_add_self (F := F) R s

end Alg

section Herm

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R]

def hermMat (σ : E →ₐ[F] E) (n : ℕ) (x : (Fin n → R) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E)) :
    Matrix (Fin n) (Fin n) (R ⊗[F] E) := fun a b =>
  if h : a < b then x.2 ⟨(a, b), h⟩
  else if h' : b < a then sigR R σ (x.2 ⟨(b, a), h'⟩)
  else x.1 a ⊗ₜ[F] (1 : E)

/- English proof (translation)
Introduce `a b`. Break down `lt_trichotomy a b with h | h | h` into its components or cases. Simplify using `only [hermMat, dif_pos h, dif_neg (not_lt_of_gt h)]`. Conclude with `sigR_sigR R hinv _`. Substitute `h` using the available equality.

Simplify using `only [hermMat, lt_irrefl, dite_false]`. Rewrite using `[sigR_tmul, map_one]`. Simplify using `only [hermMat, dif_pos h, dif_neg (not_lt_of_gt h)]`.
-/
theorem hermMat_mem {σ : E →ₐ[F] E} (hinv : ∀ x, σ (σ x) = x) (n : ℕ)
    (x : (Fin n → R) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E)) :
    hermMat R σ n x ∈ HermR R σ n := by
  intro a b
  rcases lt_trichotomy a b with h | h | h
  · simp only [hermMat, dif_pos h, dif_neg (not_lt_of_gt h)]
    exact sigR_sigR R hinv _
  · subst h
    simp only [hermMat, lt_irrefl, dite_false]
    rw [sigR_tmul, map_one]
  · simp only [hermMat, dif_pos h, dif_neg (not_lt_of_gt h)]

variable [TopologicalSpace R]

def hermCoord (σ : E →ₐ[F] E) (n : ℕ) (S : HermR R σ n) :
    (Fin n → R) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E) :=
  ((fun i : Fin n => algebraMap F R (1 / 2) *
      Algebra.trace R (R ⊗[F] E) ((S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i i)),
    (fun p : {p : Fin n × Fin n // p.1 < p.2} => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) p.1.1 p.1.2))

/- English proof (translation)
Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using `[hermCoord, map_add, mul_add]`. Use function extensionality and compare the values at `p`. Simplify using `[hermCoord]`.
-/
theorem hermCoord_add (σ : E →ₐ[F] E) (n : ℕ) (S T : HermR R σ n) :
    hermCoord R σ n (S + T) = hermCoord R σ n S + hermCoord R σ n T := by
  refine Prod.ext ?_ ?_
  · funext i
    simp [hermCoord, map_add, mul_add]
  · funext p
    simp [hermCoord]

/- English proof (translation)
Establish `hincl : Continuous fun r : R => r ⊗ₜ[F] (1 : E)`. Establish `: IsModuleTopology R R` using `inferInstance`. Use `IsModuleTopology.continuous_of_linearMap (R := R) (A := R) (B := R ⊗[F] E) (Algebra.linearMap R (R ⊗[F] E))` as an intermediate fact. Establish `e : (fun r : R => r ⊗ₜ[F] (1 : E)) = ⇑(Algebra.linearMap R (R ⊗[F] E))`. Use function extensionality and compare the values at `r`.

Simplify using `[Algebra.linearMap_apply, Algebra.TensorProduct.algebraMap_apply]`. Rewrite using `[e]`. Conclude with `this`. Set `h : HermR R σ n ≃ₜ (Fin n → R) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E)` to `{ toFun := hermCoord R σ n invFun := fun x => ⟨hermMat R σ n x, hermMat_mem R hinv n x⟩ left_inv := by`. Introduce `S`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `a b`. Break down `lt_trichotomy a b with hab | hab | hab` into its components or cases. Simplify using `[hermMat, dif_pos hab, hermCoord]`. Substitute `hab` using the available equality.

Take `⟨r, hr⟩` from `fixed_eq_tmul R hinv h2 hδ hσδ ((S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) a a) (S.2 a a)`. Simplify using `only [hermMat, lt_irrefl, dite_false, hermCoord]`. Rewrite using `[hr, half_trace_tmul R h2]`. Simplify using `only [hermMat, dif_pos hab, dif_neg (not_lt_of_gt hab), hermCoord]`. Conclude with `S.2 a b`.

Use `right_inv := by`. Introduce `x`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using `only [hermCoord, hermMat, lt_irrefl, dite_false]`.

Conclude with `half_trace_tmul R h2 _`. Use function extensionality and compare the values at `p`. Take `⟨⟨a, b⟩, hp⟩` from `p`. Simplify using `only [hermCoord, hermMat]`. Conclude with `dif_pos hp`.

Use `continuous_toFun := by`. Use `Continuous.prodMk (continuous_pi fun i => ?_) (continuous_pi fun p => ?_)` and prove the remaining obligations. Conclude with `continuous_const.mul (htr.comp ((continuous_apply_apply i i).comp continuous_subtype_val))`. Conclude with `(continuous_apply_apply p.1.1 p.1.2).comp continuous_subtype_val`. Use `continuous_invFun := by`.

Use `Continuous.subtype_mk (continuous_matrix fun a b => ?_) _` and prove the remaining obligations. Distinguish the cases in `hab : a < b`. Simplify using `only [hermMat, dif_pos hab]`. Conclude with `(continuous_apply _).comp continuous_snd`. Distinguish the cases in `hba : b < a`.

Simplify using `only [hermMat, dif_neg hab, dif_pos hba]`. Conclude with `hsig.comp ((continuous_apply _).comp continuous_snd)`. Simplify using `only [hermMat, dif_neg hab, dif_neg hba]`. Conclude with `hincl.comp ((continuous_apply _).comp continuous_fst) }`. Conclude with `h.isHomeomorph`.
-/
theorem hermCoord_isHomeomorph [IsTopologicalRing R] [CharZero F] {σ : E →ₐ[F] E}
    (hinv : ∀ x, σ (σ x) = x) (h2 : Module.finrank F E = 2) {δ : E} (hδ : δ ≠ 0) (hσδ : σ δ = -δ)
    (n : ℕ) [ContinuousAdd (R ⊗[F] E)] [ContinuousSMul R (R ⊗[F] E)]
    (hsig : Continuous (sigR R σ)) (htr : Continuous (Algebra.trace R (R ⊗[F] E))) :
    IsHomeomorph (hermCoord R σ n) := by
  have hincl : Continuous fun r : R => r ⊗ₜ[F] (1 : E) := by
    have : IsModuleTopology R R := inferInstance
    have := IsModuleTopology.continuous_of_linearMap (R := R) (A := R) (B := R ⊗[F] E)
      (Algebra.linearMap R (R ⊗[F] E))
    have e : (fun r : R => r ⊗ₜ[F] (1 : E)) = ⇑(Algebra.linearMap R (R ⊗[F] E)) := by
      funext r
      simp [Algebra.linearMap_apply, Algebra.TensorProduct.algebraMap_apply]
    rw [e]
    exact this
  let h : HermR R σ n ≃ₜ (Fin n → R) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E) :=
    { toFun := hermCoord R σ n
      invFun := fun x => ⟨hermMat R σ n x, hermMat_mem R hinv n x⟩
      left_inv := by
        intro S
        apply Subtype.ext
        funext a b
        rcases lt_trichotomy a b with hab | hab | hab
        · simp [hermMat, dif_pos hab, hermCoord]
        · subst hab
          obtain ⟨r, hr⟩ := fixed_eq_tmul R hinv h2 hδ hσδ
            ((S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) a a) (S.2 a a)
          simp only [hermMat, lt_irrefl, dite_false, hermCoord]
          rw [hr, half_trace_tmul R h2]
        · simp only [hermMat, dif_pos hab, dif_neg (not_lt_of_gt hab), hermCoord]
          exact S.2 a b
      right_inv := by
        intro x
        refine Prod.ext ?_ ?_
        · funext i
          simp only [hermCoord, hermMat, lt_irrefl, dite_false]
          exact half_trace_tmul R h2 _
        · funext p
          obtain ⟨⟨a, b⟩, hp⟩ := p
          simp only [hermCoord, hermMat]
          exact dif_pos hp
      continuous_toFun := by
        refine Continuous.prodMk (continuous_pi fun i => ?_) (continuous_pi fun p => ?_)
        · exact continuous_const.mul (htr.comp
            ((continuous_apply_apply i i).comp continuous_subtype_val))
        · exact (continuous_apply_apply p.1.1 p.1.2).comp continuous_subtype_val
      continuous_invFun := by
        refine Continuous.subtype_mk (continuous_matrix fun a b => ?_) _
        by_cases hab : a < b
        · simp only [hermMat, dif_pos hab]
          exact (continuous_apply _).comp continuous_snd
        · by_cases hba : b < a
          · simp only [hermMat, dif_neg hab, dif_pos hba]
            exact hsig.comp ((continuous_apply _).comp continuous_snd)
          · simp only [hermMat, dif_neg hab, dif_neg hba]
            exact hincl.comp ((continuous_apply _).comp continuous_fst) }
  exact h.isHomeomorph

end Herm

end GlobalTheory.CompanionTheory.SW.HaarCoord

namespace GlobalTheory.CompanionTheory.SW

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hcm R _ _ _ _ _ _ _ _ _ d b lam hlam`. Take `⟨t1, t2, t3, t4, t5, t6, t7, -, -, -⟩` from `GlobalTheory.T.tensor_locally_compact_ring F E σ hcm R`. Establish `h2 : Module.finrank F E = 2` using `hcm.2.2.1`. Take `⟨hinv, δ, hδ, hσδ⟩` from `HaarCoord.conj_facts hcm`. Use `haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩`.

Use `haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩`. Use `haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R _`. Establish `hK : (coordK R b lam).IsAddHaarMeasure`. Use `HaarCoord.haar_comap _ ?_ (t7 d b) _` and prove the remaining obligations. Introduce `x y`.

Use function extensionality and compare the values at `k`. Simplify using the standard rewrite rules. Use `haveI a1 : MeasurableAdd (R ⊗[F] E) := inferInstance`. Use `haveI a2 : SigmaFinite (coordK R b lam) := inferInstance`. Use `⟨hK, ?_, ?_⟩` and prove the remaining obligations.

Introduce `n M`. Unfold `coordW`. Use `haveI a3 : (Measure.pi fun _ : Fin M => coordK R b lam).IsAddHaarMeasure := inferInstance`. Use `infer_instance`. Introduce `n haveI : BorelSpace (HermR R σ n) := ⟨rfl⟩ haveI a3 : (Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => coordK R b lam).IsAddHaarMeasure := inferInstance haveI a4 : (Measure.pi fun _ : Fin n => lam).IsAddHaarMeasure := inferInstance haveI a5 : ((Measure.pi fun _ : Fin n => …`.

Conclude with `HaarCoord.haar_comap (HaarCoord.hermCoord R σ n) (HaarCoord.hermCoord_add R σ n) (HaarCoord.hermCoord_isHomeomorph R hinv h2 hδ hσδ n t5 t6) _`.
-/
theorem coord_measures_haar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → (coordK R b lam).IsAddHaarMeasure ∧ (∀ n M : ℕ, (coordW R b lam n M).IsAddHaarMeasure) ∧ ∀ n : ℕ, (coordHerm R σ b lam n).IsAddHaarMeasure := by
  intro F E _ _ _ _ _ σ hcm R _ _ _ _ _ _ _ _ _ d b lam hlam
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, -, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm R
  have h2 : Module.finrank F E = 2 := hcm.2.2.1
  obtain ⟨hinv, δ, hδ, hσδ⟩ := HaarCoord.conj_facts hcm
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R _
  have hK : (coordK R b lam).IsAddHaarMeasure := by
    refine HaarCoord.haar_comap _ ?_ (t7 d b) _
    intro x y
    funext k
    simp
  haveI a1 : MeasurableAdd (R ⊗[F] E) := inferInstance
  haveI a2 : SigmaFinite (coordK R b lam) := inferInstance
  refine ⟨hK, ?_, ?_⟩
  · intro n M
    unfold coordW
    haveI a3 : (Measure.pi fun _ : Fin M => coordK R b lam).IsAddHaarMeasure := inferInstance
    infer_instance
  · intro n
    haveI : BorelSpace (HermR R σ n) := ⟨rfl⟩
    haveI a3 : (Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => coordK R b lam).IsAddHaarMeasure :=
      inferInstance
    haveI a4 : (Measure.pi fun _ : Fin n => lam).IsAddHaarMeasure := inferInstance
    haveI a5 : ((Measure.pi fun _ : Fin n => lam).prod
        (Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => coordK R b lam)).IsAddHaarMeasure :=
      inferInstance
    exact HaarCoord.haar_comap (HaarCoord.hermCoord R σ n) (HaarCoord.hermCoord_add R σ n)
      (HaarCoord.hermCoord_isHomeomorph R hinv h2 hδ hσδ n t5 t6) _

end GlobalTheory.CompanionTheory.SW
