import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

section FrameBundle

variable (o : Type*) [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω] {σ : Type*}
variable {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]

def frameLat (y : σ → Ω) (b : Module.Basis (Fin N) Ω E) (i : σ) : AddSubgroup E where
  carrier := {e | ∀ q, b.repr e q ∈ chartRing o y i}
  add_mem' := by
    intro e e' he he' q
    simpa using add_mem (he q) (he' q)
  zero_mem' := by
    intro q
    simp
  neg_mem' := by
    intro e he q
    simpa using neg_mem (he q)

variable {o}

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_frameLat {y : σ → Ω} {b : Module.Basis (Fin N) Ω E} {i : σ} {e : E} :
    e ∈ frameLat o y b i ↔ ∀ q, b.repr e q ∈ chartRing o y i :=
  Iff.rfl

/- English proof (translation)
Establish `h` using `congrFun (b.equivFun.apply_symm_apply a) q`. Rewrite `h` using `[b.equivFun_apply, b.equivFun_symm_apply]`. Then use the resulting hypothesis.
-/
theorem repr_sum_smul (b : Module.Basis (Fin N) Ω E) (a : Fin N → Ω) (q : Fin N) :
    b.repr (∑ j, a j • b j) q = a q := by
  have h := congrFun (b.equivFun.apply_symm_apply a) q
  rwa [b.equivFun_apply, b.equivFun_symm_apply] at h

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `he`. Conclude with `⟨fun q => b.repr e q, he, (b.sum_repr e).symm⟩`. Introduce and unpack `⟨a, ha, rfl⟩ q`. Rewrite using `[repr_sum_smul]`.

Conclude with `ha q`.
-/
theorem frameLat_iff (y : σ → Ω) (b : Module.Basis (Fin N) Ω E) (i : σ) (e : E) :
    e ∈ frameLat o y b i ↔ ∃ a : Fin N → Ω, (∀ q, a q ∈ chartRing o y i) ∧ e = ∑ q, a q • b q := by
  constructor
  · intro he
    exact ⟨fun q => b.repr e q, he, (b.sum_repr e).symm⟩
  · rintro ⟨a, ha, rfl⟩ q
    rw [repr_sum_smul]
    exact ha q

variable (o)

def frameBundle (y : σ → Ω) (b : Module.Basis (Fin N) Ω E) : ChartBundle o y N E where
  lat := frameLat o y b
  stable i a ha e he q := by
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact mul_mem ha (he q)
  frame i _ := by
    refine ⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, fun _ => one_mem _, by simp, fun _ => ?_⟩
    refine ⟨b, b.linearIndependent, b.span_eq, fun e => ?_⟩
    simp only [one_pow, one_smul, one_mul, exists_const]
    exact frameLat_iff y b i e
  overlap i j hi hj e he := by
    choose m hm using fun q => exists_pow_mul_mem_chartRing y i j hi (he q)
    refine ⟨∑ q, m q, fun q => ?_⟩
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    have hle : m q ≤ ∑ q, m q :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
    rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc]
    exact mul_mem (pow_mem (div_mem_chartRing y j i) _) (hm q)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem frameBundle_lat (y : σ → Ω) (b : Module.Basis (Fin N) Ω E) (i : σ) :
    (frameBundle o y b).lat i = frameLat o y b i :=
  rfl

end FrameBundle

section GradedFrame

variable (o : Type*) [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]

/- English proof (translation)
Introduce `s _`. Use `⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, fun _ => one_mem _, by simp, fun _ => ?_⟩` and prove the remaining obligations. Use `⟨b, b.linearIndependent, b.span_eq, fun e => ?_, fun i => ⟨1, ⟨one_ne_zero, ⟨0, ?_⟩, ⟨0, ?_⟩⟩, ?_⟩⟩` and prove the remaining obligations. Simplify using `only [one_pow, one_smul, one_mul, exists_const]`. Conclude with `frameLat_iff (mseg x) b s e`.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using `[chartMon]`.
-/
theorem isGradedFrame_frameBundle (x : (Σ k, ι k) → Ω) (b : Module.Basis (Fin N) Ω E)
    (Vs : Fin (N + 1) → Submodule Ω E) :
    IsGradedFrame o x (frameBundle o (mseg x) b) Vs 0 b := by
  intro s _
  refine ⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, fun _ => one_mem _, by simp, fun _ => ?_⟩
  refine ⟨b, b.linearIndependent, b.span_eq, fun e => ?_, fun i => ⟨1, ⟨one_ne_zero, ⟨0, ?_⟩, ⟨0, ?_⟩⟩, ?_⟩⟩
  · simp only [one_pow, one_smul, one_mul, exists_const]
    exact frameLat_iff (mseg x) b s e
  · simp
  · simp
  · simp [chartMon]

end GradedFrame

section Point

variable {R : Type*} [CommRing R] [IsDomain R] {Ω : Type*} [Field Ω] [Algebra R Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Simplify using `[mseg, hy]`.
-/
theorem mseg_of_one {y : (Σ k, ι k) → Ω} (hy : ∀ p, y p = 1) (s : ∀ k, ι k) : mseg y s = 1 := by
  simp [mseg, hy]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `ha`. Establish `hle : chartRing R (mseg y) s ≤ ⊥`. Unfold `chartRing`. Rewrite using `[Algebra.adjoin_le_iff]`.

Introduce and unpack `_ ⟨t, rfl⟩`. Simplify using `only [mseg_of_one hy, div_one]`. Conclude with `one_mem _`. Conclude with `Algebra.mem_bot.mp (hle ha)`. Introduce and unpack `⟨c, rfl⟩`.

Conclude with `Subalgebra.algebraMap_mem _ c`.
-/
theorem mem_chartRing_of_one {y : (Σ k, ι k) → Ω} (hy : ∀ p, y p = 1) (s : ∀ k, ι k) {a : Ω} :
    a ∈ chartRing R (mseg y) s ↔ ∃ c : R, algebraMap R Ω c = a := by
  constructor
  · intro ha
    have hle : chartRing R (mseg y) s ≤ ⊥ := by
      unfold chartRing
      rw [Algebra.adjoin_le_iff]
      rintro _ ⟨t, rfl⟩
      simp only [mseg_of_one hy, div_one]
      exact one_mem _
    exact Algebra.mem_bot.mp (hle ha)
  · rintro ⟨c, rfl⟩
    exact Subalgebra.algebraMap_mem _ c

/- English proof (translation)
Introduce and unpack `⟨a, i⟩ ⟨b, j⟩ h`. Simplify using `only at h`. Substitute `h` using the available equality. Rewrite using `[Subsingleton.elim i j]`.
-/
theorem fst_injective_of_subsingleton (hsub : ∀ k, Subsingleton (ι k)) :
    Function.Injective (Sigma.fst : (Σ k, ι k) → K) := by
  rintro ⟨a, i⟩ ⟨b, j⟩ h
  simp only at h
  subst h
  rw [Subsingleton.elim i j]

/- English proof (translation)
Establish `key : mcMap R y = (MvPolynomial.mapAlgHom (Algebra.ofId R Ω)).comp (MvPolynomial.rename (Sigma.fst : (Σ k, ι k) → K))`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `p`. Simplify using `[mcMap, hy]`. Establish `hi : Function.Injective (mcMap R y)`.

Rewrite using `[key]`. Conclude with `(MvPolynomial.map_injective _ hinj).comp (MvPolynomial.rename_injective _ (fst_injective_of_subsingleton hsub))`. Conclude with `(RingHom.injective_iff_ker_eq_bot _).mp hi`.
-/
theorem mcIdeal_of_one (hinj : Function.Injective (algebraMap R Ω)) (hsub : ∀ k, Subsingleton (ι k))
    {y : (Σ k, ι k) → Ω} (hy : ∀ p, y p = 1) : mcIdeal R y = ⊥ := by
  have key : mcMap R y = (MvPolynomial.mapAlgHom (Algebra.ofId R Ω)).comp
      (MvPolynomial.rename (Sigma.fst : (Σ k, ι k) → K)) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mcMap, hy]
  have hi : Function.Injective (mcMap R y) := by
    rw [key]
    exact (MvPolynomial.map_injective _ hinj).comp
      (MvPolynomial.rename_injective _ (fst_injective_of_subsingleton hsub))
  exact (RingHom.injective_iff_ker_eq_bot _).mp hi

/- English proof (translation)
Use `⟨Ideal.isPrime_bot, ⟨∅, fun f hf => absurd hf (Set.notMem_empty f), Ideal.span_empty.symm⟩, fun k => ⟨(hne k).some, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Ideal.mem_bot]`. Conclude with `MvPolynomial.X_ne_zero _`.
-/
theorem isMultiProjPrime_bot (hne : ∀ k, Nonempty (ι k)) :
    IsMultiProjPrime (⊥ : Ideal (MRingOver R ι)) := by
  refine ⟨Ideal.isPrime_bot, ⟨∅, fun f hf => absurd hf (Set.notMem_empty f), Ideal.span_empty.symm⟩,
    fun k => ⟨(hne k).some, ?_⟩⟩
  rw [Ideal.mem_bot]
  exact MvPolynomial.X_ne_zero _

/- English proof (translation)
Rewrite using `[RingEquiv.ringKrullDim (RingEquiv.quotientBot _), MvPolynomial.ringKrullDim_of_isNoetherianRing]`.
-/
theorem krull_bot [IsNoetherianRing R] :
    ringKrullDim (MRingOver R ι ⧸ (⊥ : Ideal (MRingOver R ι))) =
      ringKrullDim R + Nat.card (Σ k, ι k) := by
  rw [RingEquiv.ringKrullDim (RingEquiv.quotientBot _),
    MvPolynomial.ringKrullDim_of_isNoetherianRing]

/- English proof (translation)
Rewrite using `[Nat.card_eq_fintype_card, Fintype.card_sigma]`. Establish `h1 : ∀ k, Fintype.card (ι k) = 1` using `fun k => Fintype.card_eq_one_iff.mpr ⟨(hne k).some, fun _ => @Subsingleton.elim _ (hsub k) _ _⟩`. Simplify using `[h1]`.
-/
theorem card_sigma_of_point (hsub : ∀ k, Subsingleton (ι k)) (hne : ∀ k, Nonempty (ι k)) :
    Nat.card (Σ k, ι k) = Fintype.card K := by
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  have h1 : ∀ k, Fintype.card (ι k) = 1 := fun k =>
    Fintype.card_eq_one_iff.mpr ⟨(hne k).some, fun _ => @Subsingleton.elim _ (hsub k) _ _⟩
  simp [h1]

end Point

section ModelInhabitants

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Use `⟨inferInstance, isMultiProjPrime_bot hne, Ideal.comap_bot_of_injective _ (C_injective _ _), ?_⟩` and prove the remaining obligations. Rewrite using `[krull_bot, IsDiscreteValuationRing.ringKrullDim_eq_one, hd, show d + 1 + Fintype.card K = 1 + (d + Fintype.card K) by omega]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem isModelOver_bot [Nonempty K] (hne : ∀ k, Nonempty (ι k)) (d : ℕ)
    (hd : Nat.card (Σ k, ι k) = d + Fintype.card K) :
    IsModelOver O (⊥ : Ideal (MRingOver O ι)) d := by
  refine ⟨inferInstance, isMultiProjPrime_bot hne, Ideal.comap_bot_of_injective _ (C_injective _ _), ?_⟩
  rw [krull_bot, IsDiscreteValuationRing.ringKrullDim_eq_one, hd,
    show d + 1 + Fintype.card K = 1 + (d + Fintype.card K) by omega]
  push_cast
  rfl

/- English proof (translation)
The claim follows from `isModelOver_bot O (fun _ => inferInstance) 1 (by simp)`.
-/
theorem line_isModelOver : IsModelOver O (⊥ : Ideal (MRingOver O fun _ : Unit => Fin 2)) 1 :=
  isModelOver_bot O (fun _ => inferInstance) 1 (by simp)

/- English proof (translation)
Introduce `m hm k`. Rewrite `hm` using `[MvPolynomial.mem_support_iff, MvPolynomial.coeff_C]`. Use `split_ifs at hm with h`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Conclude with `absurd rfl hm`.
-/
theorem isMultiHomog_C (c : O) : IsMultiHomog (C c : MRingOver O ι) 0 := by
  classical
  intro m hm k
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at hm
  split_ifs at hm with h
  · subst h
    simp
  · exact absurd rfl hm

/- English proof (translation)
Use `⟨⟨0, 0, isMultiHomog_C O c, by simpa using isMultiHomog_C O (1 : O), by simp⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.mem_bot]`. Conclude with `fun h => hc ((C_injective _ _) (h.trans C_0.symm))`. Rewrite using `[Ideal.mem_bot]`. Conclude with `one_ne_zero`.

Introduce `Q hQ _ hcom`. Use `⟨1, C c, ⟨0, by simpa using isMultiHomog_C O (1 : O)⟩, ⟨0, isMultiHomog_C O c⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `fun h => hQ.1.ne_top ((Ideal.eq_top_iff_one Q).mpr h)`. Introduce `h`. Establish `: c ∈ Q.comap (C : O →+* MRingOver O ι)` using `h`.

Rewrite `this` using `[hcom, Ideal.mem_bot]`. Conclude with `hc this`. Simplify using the standard rewrite rules.
-/
theorem isVertDiv_const (c : O) (hc : c ≠ 0) :
    IsVertDiv O (⊥ : Ideal (MRingOver O ι)) 0 (C c) 1 := by
  refine ⟨⟨0, 0, isMultiHomog_C O c, by simpa using isMultiHomog_C O (1 : O), by simp⟩, ?_, ?_, ?_⟩
  · rw [Ideal.mem_bot]
    exact fun h => hc ((C_injective _ _) (h.trans C_0.symm))
  · rw [Ideal.mem_bot]
    exact one_ne_zero
  · intro Q hQ _ hcom
    refine ⟨1, C c, ⟨0, by simpa using isMultiHomog_C O (1 : O)⟩, ⟨0, isMultiHomog_C O c⟩, ?_, ?_, ?_⟩
    · exact fun h => hQ.1.ne_top ((Ideal.eq_top_iff_one Q).mpr h)
    · intro h
      have : c ∈ Q.comap (C : O →+* MRingOver O ι) := h
      rw [hcom, Ideal.mem_bot] at this
      exact hc this
    · simp

def unif : O :=
  Classical.choose (IsDiscreteValuationRing.exists_irreducible O)

/- English proof (translation)
The claim follows from `(Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible O)).ne_zero`.
-/
theorem unif_ne_zero : unif O ≠ 0 :=
  (Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible O)).ne_zero

/- English proof (translation)
The claim follows from `isVertDiv_const O _ (unif_ne_zero O)`.
-/
theorem line_vert : IsVertDiv O (⊥ : Ideal (MRingOver O fun _ : Unit => Fin 2)) 0 (C (unif O)) 1 :=
  isVertDiv_const O _ (unif_ne_zero O)

end ModelInhabitants

section Flags

variable {Ω : Type*} [Field Ω]

def flag2 : Fin 3 → Submodule Ω (Fin 2 → Ω) := fun i =>
  if (i : ℕ) = 0 then ⊥ else if (i : ℕ) = 1 then Submodule.span Ω {Pi.single 0 1} else ⊤

/- English proof (translation)
Rewrite using `[Fin.monotone_iff_le_succ]`. Introduce `i`. Apply the tactic sequence `fin_cases i <;> simp [flag2]`.
-/
theorem standardFlagTwo_monotone : Monotone (flag2 (Ω := Ω)) := by
  rw [Fin.monotone_iff_le_succ]
  intro i
  fin_cases i <;> simp [flag2]

/- English proof (translation)
Simplify using `[flag2]`.
-/
theorem standardFlagTwo_zero : flag2 (Ω := Ω) 0 = ⊥ := by
  simp [flag2]

/- English proof (translation)
Simplify using `[flag2]`.
-/
theorem standardFlagTwo_one : flag2 (Ω := Ω) 1 = Submodule.span Ω {Pi.single 0 1} := by
  simp [flag2]

/- English proof (translation)
Simplify using `[flag2]`.
-/
theorem standardFlagTwo_two : flag2 (Ω := Ω) 2 = ⊤ := by
  simp [flag2]

/- English proof (translation)
The claim follows from `| 0 => by rw [standardFlagTwo_zero, finrank_bot] rfl | 1 => by rw [standardFlagTwo_one, finrank_span_singleton (by simp : (Pi.single 0 1 : Fin 2 → Ω) ≠ 0)] rfl | 2 => by rw [standardFlagTwo_two, finrank_top, Module.finrank_fin_fun] rfl`.
-/
theorem finrank_standardFlagTwo : ∀ i : Fin 3, Module.finrank Ω (flag2 (Ω := Ω) i) = (i : ℕ)
  | 0 => by
    rw [standardFlagTwo_zero, finrank_bot]
    rfl
  | 1 => by
    rw [standardFlagTwo_one, finrank_span_singleton (by simp : (Pi.single 0 1 : Fin 2 → Ω) ≠ 0)]
    rfl
  | 2 => by
    rw [standardFlagTwo_two, finrank_top, Module.finrank_fin_fun]
    rfl

/- English proof (translation)
Simplify using `[flag2]`.
-/
theorem standardFlagTwo_last : flag2 (Ω := Ω) (Fin.last 2) = ⊤ := by
  simp [flag2]

def bPi (c : Ω) (hc : c ≠ 0) : Module.Basis (Fin 2) Ω (Fin 2 → Ω) :=
  (Pi.basisFun Ω (Fin 2)).isUnitSMul (w := ![1, c]) (by
    intro i
    fin_cases i
    · simp
    · simpa using hc)

/- English proof (translation)
Rewrite using `[bPi, Module.Basis.isUnitSMul_apply, Pi.basisFun_apply]`.
-/
theorem bPi_apply (c : Ω) (hc : c ≠ 0) (i : Fin 2) :
    bPi c hc i = (![1, c] i) • Pi.single i 1 := by
  rw [bPi, Module.Basis.isUnitSMul_apply, Pi.basisFun_apply]

/- English proof (translation)
Rewrite using `[bPi, Module.Basis.repr_isUnitSMul, Units.smul_def, Units.val_inv_eq_inv_val, IsUnit.unit_spec, Pi.basisFun_repr, smul_eq_mul]`.
-/
theorem bPi_repr (c : Ω) (hc : c ≠ 0) (v : Fin 2 → Ω) (q : Fin 2) :
    (bPi c hc).repr v q = (![1, c] q)⁻¹ * v q := by
  rw [bPi, Module.Basis.repr_isUnitSMul, Units.smul_def, Units.val_inv_eq_inv_val,
    IsUnit.unit_spec, Pi.basisFun_repr, smul_eq_mul]

variable (o : Type*) [CommRing o] [Algebra o Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def stdFlag (x : (Σ k, ι k) → Ω) :
    FullFlag o x (frameBundle o (mseg x) (Pi.basisFun Ω (Fin 2))) where
  Vs := flag2
  mono := standardFlagTwo_monotone
  dim := finrank_standardFlagTwo
  top := standardFlagTwo_last
  deg := 0
  gen := Pi.basisFun Ω (Fin 2)
  gen_mem := by
    intro i
    fin_cases i <;> simp [flag2, Submodule.mem_span_singleton_self]
  frame := isGradedFrame_frameBundle o x _ flag2

end Flags

section FlagPairs

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

abbrev stdE (x : (Σ k, ι k) → Ω) : ChartBundle O (mseg x) 2 (Fin 2 → Ω) :=
  frameBundle O (mseg x) (Pi.basisFun Ω (Fin 2))

abbrev cE (x : (Σ k, ι k) → Ω) (c : O) (hc : algebraMap O Ω c ≠ 0) :
    ChartBundle O (mseg x) 2 (Fin 2 → Ω) :=
  frameBundle O (mseg x) (bPi (algebraMap O Ω c) hc)

/- English proof (translation)
Simplify using `[stdE, frameBundle_lat, mem_frameLat]`.
-/
theorem mem_stdE {x : (Σ k, ι k) → Ω} {s : ∀ k, ι k} {v : Fin 2 → Ω} :
    v ∈ (stdE O x).lat s ↔ ∀ q, v q ∈ chartRing O (mseg x) s := by
  simp [stdE, frameBundle_lat, mem_frameLat]

/- English proof (translation)
Simplify using `only [cE, frameBundle_lat, mem_frameLat, bPi_repr, Fin.forall_fin_two]`. Simplify using the standard rewrite rules.
-/
theorem mem_cE {x : (Σ k, ι k) → Ω} {c : O} {hc : algebraMap O Ω c ≠ 0} {s : ∀ k, ι k}
    {v : Fin 2 → Ω} : v ∈ (cE O x c hc).lat s ↔
      v 0 ∈ chartRing O (mseg x) s ∧ (algebraMap O Ω c)⁻¹ * v 1 ∈ chartRing O (mseg x) s := by
  simp only [cE, frameBundle_lat, mem_frameLat, bPi_repr, Fin.forall_fin_two]
  simp

/- English proof (translation)
Introduce `s _ v hv`. Rewrite `hv` using `[mem_cE]`. Rewrite using `[mem_stdE, Fin.forall_fin_two]`. Use `⟨hv.1, ?_⟩` and prove the remaining obligations. Establish `h` using `mul_mem (Subalgebra.algebraMap_mem (chartRing O (mseg x) s) c) hv.2`.

Rewrite `h` using `[← mul_assoc, mul_inv_cancel₀ hc, one_mul]`. Then use the resulting hypothesis.
-/
theorem cE_le_stdE (x : (Σ k, ι k) → Ω) (c : O) (hc : algebraMap O Ω c ≠ 0) :
    LatLE O x (cE O x c hc) (stdE O x) := by
  intro s _ v hv
  rw [mem_cE] at hv
  rw [mem_stdE, Fin.forall_fin_two]
  refine ⟨hv.1, ?_⟩
  have h := mul_mem (Subalgebra.algebraMap_mem (chartRing O (mseg x) s) c) hv.2
  rwa [← mul_assoc, mul_inv_cancel₀ hc, one_mul] at h

/- English proof (translation)
Introduce `s hs`. Prove the components needed by the constructor for the conclusion. Introduce `v hv`. Rewrite `hv` using `[mem_stdE]`. Use `⟨c, hc0, ?_⟩` and prove the remaining obligations.

Rewrite using `[mem_cE]`. Establish `hcm` using `Subalgebra.algebraMap_mem (chartRing O (mseg x) s) c`. Use `⟨by simpa using mul_mem hcm (hv 0), ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Rewrite using `[← mul_assoc, inv_mul_cancel₀ hc, one_mul]`.

Conclude with `hv 1`. Introduce `v hv`. Use `⟨1, one_ne_zero, ?_⟩` and prove the remaining obligations. Rewrite using `[map_one, one_smul]`. Conclude with `cE_le_stdE O x c hc s hs hv`.
-/
theorem sameGeneric_cE (x : (Σ k, ι k) → Ω) (c : O) (hc0 : c ≠ 0) (hc : algebraMap O Ω c ≠ 0) :
    SameGeneric O x (stdE O x) (cE O x c hc) := by
  intro s hs
  constructor
  · intro v hv
    rw [mem_stdE] at hv
    refine ⟨c, hc0, ?_⟩
    rw [mem_cE]
    have hcm := Subalgebra.algebraMap_mem (chartRing O (mseg x) s) c
    refine ⟨by simpa using mul_mem hcm (hv 0), ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    exact hv 1
  · intro v hv
    refine ⟨1, one_ne_zero, ?_⟩
    rw [map_one, one_smul]
    exact cE_le_stdE O x c hc s hs hv

def stdFlagPair (x : (Σ k, ι k) → Ω) (c : O) (hc0 : c ≠ 0) (hc : algebraMap O Ω c ≠ 0)
    (hx : mcIdeal O x = ⊥) : FlagPair O x (stdE O x) (cE O x c hc) where
  toFullFlag := stdFlag O x
  deg' := 0
  gen' := bPi (algebraMap O Ω c) hc
  gen'_mem := by
    intro i
    fin_cases i <;> simp [stdFlag, flag2, bPi_apply, Submodule.mem_span_singleton_self]
  frame' := isGradedFrame_frameBundle O x _ flag2
  f := ![1, C c]
  g := fun _ => 1
  rel := by
    intro i
    fin_cases i <;> simp [stdFlag, flag2, bPi_apply]
  vert := by
    intro i
    rw [hx]
    fin_cases i
    · simpa [stdFlag] using isVertDiv_const O (1 : O) one_ne_zero
    · simpa [stdFlag] using isVertDiv_const O c hc0

end FlagPairs

section PointModel

abbrev ptIdx : Unit → Type := fun _ => Fin 1

abbrev noIdx : Empty → Type := fun e => e.elim

instance instFintypeNoIdx : ∀ k : Empty, Fintype (noIdx k) := fun k => k.elim

variable {Ω : Type*} [Field Ω]

def ptCoord : (Σ k : Unit, ptIdx k) → Ω := fun _ => 1

def noCoord : (Σ k : Empty, noIdx k) → Ω := fun p => p.1.elim

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ptCoord_eq (p : Σ k : Unit, ptIdx k) : ptCoord (Ω := Ω) p = 1 :=
  rfl

/- English proof (translation)
Break down `p with ⟨k | k, i⟩` into its components or cases. Both sides reduce to the same expression. Conclude with `k.elim`.
-/
theorem join_pt_eq (p : Σ k : Unit ⊕ Empty, Sum.elim ptIdx noIdx k) :
    joinCoord (ptCoord (Ω := Ω)) (noCoord (Ω := Ω)) p = 1 := by
  rcases p with ⟨k | k, i⟩
  · rfl
  · exact k.elim

/- English proof (translation)
Introduce `_` and use `inferInstanceAs (Subsingleton (Fin 1))`.
-/
theorem pt_sub : ∀ k, Subsingleton (ptIdx k) := fun _ => inferInstanceAs (Subsingleton (Fin 1))

/- English proof (translation)
Introduce `_` and use `⟨(0 : Fin 1)⟩`.
-/
theorem pt_ne : ∀ k, Nonempty (ptIdx k) := fun _ => ⟨(0 : Fin 1)⟩

/- English proof (translation)
The claim follows from `| .inl _ => inferInstanceAs (Subsingleton (Fin 1)) | .inr k => k.elim`.
-/
theorem join_sub : ∀ k, Subsingleton (Sum.elim ptIdx noIdx k)
  | .inl _ => inferInstanceAs (Subsingleton (Fin 1))
  | .inr k => k.elim

/- English proof (translation)
The claim follows from `| .inl _ => ⟨(0 : Fin 1)⟩ | .inr k => k.elim`.
-/
theorem join_ne : ∀ k, Nonempty (Sum.elim ptIdx noIdx k)
  | .inl _ => ⟨(0 : Fin 1)⟩
  | .inr k => k.elim

/- English proof (translation)
Use extensionality with `a`. Simplify using `only [Set.mem_range, Set.mem_singleton_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨q, rfl⟩`. Simplify using `[hy]`.

Introduce and unpack `rfl`. Conclude with `⟨hne.some, by simp [hy]⟩`.
-/
theorem ratios_of_one {K₀ : Type} {κ : K₀ → Type} {y : (Σ k, κ k) → Ω} (hy : ∀ p, y p = 1)
    (hne : Nonempty (Σ k, κ k × κ k)) :
    Set.range (fun q : (Σ k, κ k × κ k) => y ⟨q.1, q.2.1⟩ / y ⟨q.1, q.2.2⟩) = {1} := by
  ext a
  simp only [Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro ⟨q, rfl⟩
    simp [hy]
  · rintro rfl
    exact ⟨hne.some, by simp [hy]⟩

end PointModel

section PointDVR

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
The claim follows from `IsFractionRing.injective O (FractionRing O)`.
-/
theorem frac_inj : Function.Injective (algebraMap O (FractionRing O)) :=
  IsFractionRing.injective O (FractionRing O)

/- English proof (translation)
The claim follows from `(map_ne_zero_iff _ (frac_inj O)).mpr (unif_ne_zero O)`.
-/
theorem unif_frac_ne : algebraMap O (FractionRing O) (unif O) ≠ 0 :=
  (map_ne_zero_iff _ (frac_inj O)).mpr (unif_ne_zero O)

/- English proof (translation)
Unfold `fnField`. Rewrite using `[ratios_of_one hy hne]`.
-/
theorem fnField_of_one {Ω : Type*} [Field Ω] [Algebra O Ω] {K₀ : Type} {κ : K₀ → Type}
    {y : (Σ k, κ k) → Ω} (hy : ∀ p, y p = 1) (hne : Nonempty (Σ k, κ k × κ k)) :
    fnField O y = Subfield.closure (Set.range (algebraMap O Ω) ∪ {1}) := by
  unfold fnField
  rw [ratios_of_one hy hne]

/- English proof (translation)
Rewrite using `[mcIdeal_of_one (frac_inj O) pt_sub ptCoord_eq]`. Conclude with `isModelOver_bot O pt_ne 0 (by rw [card_sigma_of_point pt_sub pt_ne]; simp)`.
-/
theorem pt_model : IsModelOver O (mcIdeal O (ptCoord (Ω := FractionRing O))) 0 := by
  rw [mcIdeal_of_one (frac_inj O) pt_sub ptCoord_eq]
  exact isModelOver_bot O pt_ne 0 (by rw [card_sigma_of_point pt_sub pt_ne]; simp)

/- English proof (translation)
Rewrite using `[mcIdeal_of_one (frac_inj O) join_sub join_pt_eq]`. Conclude with `isModelOver_bot O join_ne 0 (by rw [card_sigma_of_point join_sub join_ne]; simp)`.
-/
theorem join_model :
    IsModelOver O (mcIdeal O (joinCoord (ptCoord (Ω := FractionRing O)) noCoord)) 0 := by
  rw [mcIdeal_of_one (frac_inj O) join_sub join_pt_eq]
  exact isModelOver_bot O join_ne 0 (by rw [card_sigma_of_point join_sub join_ne]; simp)

variable {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Introduce `s _`. Establish `tr : ∀ a : Ω, a ∈ chartRing O (mseg (joinCoord x z)) s ↔ a ∈ chartRing O (mseg x) (restrictChart s)` using `fun a => by`. Rewrite using `[mem_chartRing_of_one hxz, mem_chartRing_of_one hx]`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `v hv`.

Apply `AddSubgroup.subset_closure` to reduce the goal to its premises. Conclude with `⟨1, one_mem _, v, mem_frameLat.mpr fun q => (tr _).mp (mem_frameLat.mp hv q), (one_smul _ _).symm⟩`. Rewrite using `[AddSubgroup.closure_le]`. Introduce and unpack `_ ⟨a, ha, e, he, rfl⟩`. Use `mem_frameLat.mpr fun q => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, Finsupp.smul_apply, smul_eq_mul]`. Conclude with `mul_mem ha ((tr _).mpr (mem_frameLat.mp he q))`.
-/
theorem isPull_frame_of_one {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    {x : (Σ k, ι k) → Ω} {z : (Σ k, ι' k) → Ω} (hx : ∀ p, x p = 1)
    (hxz : ∀ p, joinCoord x z p = 1) {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]
    (b : Module.Basis (Fin N) Ω E) :
    IsPull O x z (frameBundle O (mseg x) b) (frameBundle O (mseg (joinCoord x z)) b) := by
  intro s _
  have tr : ∀ a : Ω, a ∈ chartRing O (mseg (joinCoord x z)) s ↔
      a ∈ chartRing O (mseg x) (restrictChart s) := fun a => by
    rw [mem_chartRing_of_one hxz, mem_chartRing_of_one hx]
  apply le_antisymm
  · intro v hv
    apply AddSubgroup.subset_closure
    exact ⟨1, one_mem _, v, mem_frameLat.mpr fun q => (tr _).mp (mem_frameLat.mp hv q),
      (one_smul _ _).symm⟩
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨a, ha, e, he, rfl⟩
    refine mem_frameLat.mpr fun q => ?_
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact mul_mem ha ((tr _).mpr (mem_frameLat.mp he q))

def ptFlagModel : FlagModel O (ptCoord (Ω := FractionRing O)) 0 2 (stdE O ptCoord)
    (cE O ptCoord (unif O) (unif_frac_ne O)) where
  K' := Empty
  ι' := noIdx
  z := noCoord
  model := join_model O
  birat := by
    rw [fnField_of_one O join_pt_eq ⟨⟨.inl (), ((0 : Fin 1), (0 : Fin 1))⟩⟩,
      fnField_of_one O ptCoord_eq ⟨⟨(), ((0 : Fin 1), (0 : Fin 1))⟩⟩]
  EB := stdE O (joinCoord ptCoord noCoord)
  E'B := cE O (joinCoord ptCoord noCoord) (unif O) (unif_frac_ne O)
  pull := isPull_frame_of_one O ptCoord_eq join_pt_eq _
  pull' := isPull_frame_of_one O ptCoord_eq join_pt_eq _
  flag := stdFlagPair O _ (unif O) (unif_ne_zero O) (unif_frac_ne O)
    (mcIdeal_of_one (frac_inj O) join_sub join_pt_eq)

end PointDVR

section FieldInhabitants

variable (F : Type*) [Field F]

/- English proof (translation)
Rewrite using `[mcIdeal_of_one (RingHom.injective (algebraMap F F)) pt_sub ptCoord_eq]`. Use `⟨isMultiProjPrime_bot pt_ne, ?_⟩` and prove the remaining obligations. Rewrite using `[krull_bot, ringKrullDim_eq_zero_of_field, card_sigma_of_point pt_sub pt_ne]`. Simplify using the standard rewrite rules.
-/
theorem pt_projVar : IsProjVarF (mcIdeal F (ptCoord (Ω := F))) 0 := by
  rw [mcIdeal_of_one (RingHom.injective (algebraMap F F)) pt_sub ptCoord_eq]
  refine ⟨isMultiProjPrime_bot pt_ne, ?_⟩
  rw [krull_bot, ringKrullDim_eq_zero_of_field, card_sigma_of_point pt_sub pt_ne]
  simp

variable {Ω : Type*} [Field Ω] [Algebra F Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Introduce `s _`. Establish `hmon : chartMon x s 0 = 1` using `by simp [chartMon]`. Use `⟨fun j e he => ⟨e j, by simpa using mem_frameLat.mp he j, by simp [hmon]⟩, fun ψ hψ => ?_⟩` and prove the remaining obligations. Use `⟨fun j => ψ (Pi.single j 1), fun j => hψ _ (mem_frameLat.mpr fun q => ?_), ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.basisFun_repr]`.

Distinguish the cases in `h : q = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`. Apply `LinearMap.pi_ext` to reduce the goal to its premises.

Introduce `i t`. Simplify using `only [hmon, inv_one, mul_one, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]`. Rewrite using `[Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, mul_zero]) (fun h => absurd (Finset.mem_univ i) h)]`. Rewrite using `[show (Pi.single i t : Fin 2 → Ω) = t • Pi.single i 1 by`. Use extensionality with `j`.

Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne h], map_smul, smul_eq_mul]`. Simplify using `[mul_comm]`.
-/
theorem proj_isDualGen (x : (Σ k, ι k) → Ω) :
    IsDualGen F x (frameBundle F (mseg x) (Pi.basisFun Ω (Fin 2))) 0
      (fun j : Fin 2 => (LinearMap.proj j : (Fin 2 → Ω) →ₗ[Ω] Ω)) := by
  intro s _
  have hmon : chartMon x s 0 = 1 := by simp [chartMon]
  refine ⟨fun j e he => ⟨e j, by simpa using mem_frameLat.mp he j, by simp [hmon]⟩, fun ψ hψ => ?_⟩
  refine ⟨fun j => ψ (Pi.single j 1), fun j => hψ _ (mem_frameLat.mpr fun q => ?_), ?_⟩
  · simp only [Pi.basisFun_repr]
    by_cases h : q = j
    · subst h
      simp
    · simp [h]
  · apply LinearMap.pi_ext
    intro i t
    simp only [hmon, inv_one, mul_one, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.proj_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, mul_zero])
      (fun h => absurd (Finset.mem_univ i) h)]
    rw [show (Pi.single i t : Fin 2 → Ω) = t • Pi.single i 1 by
      ext j
      by_cases h : j = i
      · subst h
        simp
      · simp [Pi.single_eq_of_ne h], map_smul, smul_eq_mul]
    simp [mul_comm]

end FieldInhabitants

section SubQuot

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def bSc1 (c : Ω) (hc : c ≠ 0) : Module.Basis (Fin 1) Ω (Fin 1 → Ω) :=
  (Pi.basisFun Ω (Fin 1)).isUnitSMul (w := fun _ => c) (fun _ => IsUnit.mk0 c hc)

/- English proof (translation)
Rewrite using `[bSc1, Module.Basis.repr_isUnitSMul, Units.smul_def, Units.val_inv_eq_inv_val, IsUnit.unit_spec, Pi.basisFun_repr, smul_eq_mul]`.
-/
theorem bSc1_repr (c : Ω) (hc : c ≠ 0) (v : Fin 1 → Ω) (q : Fin 1) :
    (bSc1 c hc).repr v q = c⁻¹ * v q := by
  rw [bSc1, Module.Basis.repr_isUnitSMul, Units.smul_def, Units.val_inv_eq_inv_val,
    IsUnit.unit_spec, Pi.basisFun_repr, smul_eq_mul]

def bG (c : Ω) (hc : c ≠ 0) : Module.Basis (Fin 2) Ω (Fin 2 → Ω) :=
  (Pi.basisFun Ω (Fin 2)).isUnitSMul (w := fun _ => c) (fun _ => IsUnit.mk0 c hc)

/- English proof (translation)
Rewrite using `[bG, Module.Basis.repr_isUnitSMul, Units.smul_def, Units.val_inv_eq_inv_val, IsUnit.unit_spec, Pi.basisFun_repr, smul_eq_mul]`.
-/
theorem bG_repr (c : Ω) (hc : c ≠ 0) (v : Fin 2 → Ω) (q : Fin 2) :
    (bG c hc).repr v q = c⁻¹ * v q := by
  rw [bG, Module.Basis.repr_isUnitSMul, Units.smul_def, Units.val_inv_eq_inv_val,
    IsUnit.unit_spec, Pi.basisFun_repr, smul_eq_mul]

abbrev std1 (x : (Σ k, ι k) → Ω) : ChartBundle O (mseg x) 1 (Fin 1 → Ω) :=
  frameBundle O (mseg x) (Pi.basisFun Ω (Fin 1))

abbrev sc1 (x : (Σ k, ι k) → Ω) (c : O) (hc : algebraMap O Ω c ≠ 0) :
    ChartBundle O (mseg x) 1 (Fin 1 → Ω) :=
  frameBundle O (mseg x) (bSc1 (algebraMap O Ω c) hc)

abbrev gE (x : (Σ k, ι k) → Ω) (c : O) (hc : algebraMap O Ω c ≠ 0) :
    ChartBundle O (mseg x) 2 (Fin 2 → Ω) :=
  frameBundle O (mseg x) (bG (algebraMap O Ω c) hc)

/- English proof (translation)
Simplify using `[std1, frameBundle_lat, mem_frameLat, Fin.forall_fin_one]`.
-/
theorem mem_standardRankOne {x : (Σ k, ι k) → Ω} {s : ∀ k, ι k} {v : Fin 1 → Ω} :
    v ∈ (std1 O x).lat s ↔ v 0 ∈ chartRing O (mseg x) s := by
  simp [std1, frameBundle_lat, mem_frameLat, Fin.forall_fin_one]

/- English proof (translation)
Simplify using `only [sc1, frameBundle_lat, mem_frameLat, bSc1_repr, Fin.forall_fin_one]`.
-/
theorem mem_scaledRankOne {x : (Σ k, ι k) → Ω} {c : O} {hc : algebraMap O Ω c ≠ 0} {s : ∀ k, ι k}
    {v : Fin 1 → Ω} : v ∈ (sc1 O x c hc).lat s ↔ (algebraMap O Ω c)⁻¹ * v 0 ∈ chartRing O (mseg x) s := by
  simp only [sc1, frameBundle_lat, mem_frameLat, bSc1_repr, Fin.forall_fin_one]

/- English proof (translation)
Simplify using `only [gE, frameBundle_lat, mem_frameLat, bG_repr]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨(algebraMap O Ω c)⁻¹ • v, (mem_stdE O).mpr fun q => by simpa using h q, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_smul, mul_inv_cancel₀ hc, one_smul]`.

Introduce and unpack `⟨e, he, rfl⟩ q`. Rewrite using `[Pi.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]`. Conclude with `(mem_stdE O).mp he q`.
-/
theorem mem_gE {x : (Σ k, ι k) → Ω} {c : O} {hc : algebraMap O Ω c ≠ 0} {s : ∀ k, ι k}
    {v : Fin 2 → Ω} : v ∈ (gE O x c hc).lat s ↔
      ∃ e ∈ (stdE O x).lat s, v = algebraMap O Ω c • e := by
  simp only [gE, frameBundle_lat, mem_frameLat, bG_repr]
  constructor
  · intro h
    refine ⟨(algebraMap O Ω c)⁻¹ • v, (mem_stdE O).mpr fun q => by simpa using h q, ?_⟩
    rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
  · rintro ⟨e, he, rfl⟩ q
    rw [Pi.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    exact (mem_stdE O).mp he q

/- English proof (translation)
Introduce `s _ v hv`. Rewrite `hv`, the goal using `[mem_cE]`. Use `⟨hv.1, ?_⟩` and prove the remaining obligations. Establish `h` using `mul_mem (Subalgebra.algebraMap_mem (chartRing O (mseg x) s) d) hv.2`. Establish `hd : algebraMap O Ω d ≠ 0` using `fun h0 => hcd (by rw [map_mul, h0, mul_zero])`.

Rewrite `h` using `[map_mul]`. Rewrite `h` using `[← mul_assoc, mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ hd, one_mul]`. Then use the resulting hypothesis.
-/
theorem cE_le_cE (x : (Σ k, ι k) → Ω) (c d : O) (hc : algebraMap O Ω c ≠ 0)
    (hcd : algebraMap O Ω (c * d) ≠ 0) : LatLE O x (cE O x (c * d) hcd) (cE O x c hc) := by
  intro s _ v hv
  rw [mem_cE] at hv ⊢
  refine ⟨hv.1, ?_⟩
  have h := mul_mem (Subalgebra.algebraMap_mem (chartRing O (mseg x) s) d) hv.2
  have hd : algebraMap O Ω d ≠ 0 := fun h0 => hcd (by rw [map_mul, h0, mul_zero])
  rw [map_mul] at h
  rwa [← mul_assoc, mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ hd, one_mul] at h

def iSub : (Fin 1 → Ω) →ₗ[Ω] (Fin 2 → Ω) where
  toFun v := fun j => if j = 0 then v 0 else 0
  map_add' v w := by
    ext j
    by_cases h : j = 0 <;> simp [h]
  map_smul' c v := by
    ext j
    by_cases h : j = 0 <;> simp [h]

def qSub : (Fin 2 → Ω) →ₗ[Ω] (Fin 1 → Ω) where
  toFun v := fun _ => v 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem iSub_apply (v : Fin 1 → Ω) (j : Fin 2) : iSub v j = if j = 0 then v 0 else 0 :=
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem qSub_apply (v : Fin 2 → Ω) (j : Fin 1) : qSub v j = v 1 :=
  rfl

/- English proof (translation)
Use `⟨?_, ?_, ?_, fun s _ => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Introduce `v w h`. Use function extensionality and compare the values at `k`. Use `fin_cases k`. Simplify `congrFun h 0` using `[iSub_apply]`.

Introduce `w`. Conclude with `⟨fun _ => w 0, by funext k; fin_cases k; rfl⟩`. Use extensionality with `v`. Simplify using `only [LinearMap.mem_range, LinearMap.mem_ker]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨w, rfl⟩`. Use function extensionality and compare the values at `k`. Simplify using `[qSub_apply, iSub_apply]`. Introduce `h`. Use `⟨fun _ => v 0, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `j`. Use `fin_cases j`. Simplify using `[iSub_apply]`. Simplify `(congrFun h 0).symm` using `[iSub_apply, qSub_apply]`. Use extensionality with `v`.

Simplify using `[AddSubgroup.mem_comap, mem_standardRankOne, mem_stdE, Fin.forall_fin_two, iSub_apply]`. Use extensionality with `w`. Rewrite using `[AddSubgroup.mem_map, mem_standardRankOne]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Use `⟨![0, w 0], (mem_stdE O).mpr ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Fin.forall_fin_two]`. Simplify using `using h`. Use function extensionality and compare the values at `k fin_cases k`. Both sides reduce to the same expression.

Introduce and unpack `⟨v, hv, rfl⟩`. Conclude with `(mem_stdE O).mp hv 1`.
-/
theorem subQuot_std (x : (Σ k, ι k) → Ω) :
    IsSubQuot O x (stdE O x) iSub qSub (std1 O x) (std1 O x) := by
  refine ⟨?_, ?_, ?_, fun s _ => ⟨?_, ?_⟩⟩
  · intro v w h
    funext k
    fin_cases k
    simpa [iSub_apply] using congrFun h 0
  · intro w
    exact ⟨fun _ => w 0, by funext k; fin_cases k; rfl⟩
  · ext v
    simp only [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨w, rfl⟩
      funext k
      simp [qSub_apply, iSub_apply]
    · intro h
      refine ⟨fun _ => v 0, ?_⟩
      funext j
      fin_cases j
      · simp [iSub_apply]
      · simpa [iSub_apply, qSub_apply] using (congrFun h 0).symm
  · ext v
    simp [AddSubgroup.mem_comap, mem_standardRankOne, mem_stdE, Fin.forall_fin_two, iSub_apply]
  · ext w
    rw [AddSubgroup.mem_map, mem_standardRankOne]
    constructor
    · intro h
      refine ⟨![0, w 0], (mem_stdE O).mpr ?_, ?_⟩
      · rw [Fin.forall_fin_two]
        simpa using h
      · funext k
        fin_cases k
        rfl
    · rintro ⟨v, hv, rfl⟩
      exact (mem_stdE O).mp hv 1

/- English proof (translation)
Use `⟨(subQuot_std O x).1, (subQuot_std O x).2.1, (subQuot_std O x).2.2.1, fun s _ => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Use extensionality with `v`. Simplify using `[AddSubgroup.mem_comap, mem_standardRankOne, mem_cE, iSub_apply]`. Use extensionality with `w`. Rewrite using `[AddSubgroup.mem_map, mem_scaledRankOne]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨![0, w 0], (mem_cE O).mpr ⟨by simp, by simpa using h⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `k`. Use `fin_cases k`.

Both sides reduce to the same expression. Introduce and unpack `⟨v, hv, rfl⟩`. Conclude with `((mem_cE O).mp hv).2`.
-/
theorem subQuot_c (x : (Σ k, ι k) → Ω) (c : O) (hc : algebraMap O Ω c ≠ 0) :
    IsSubQuot O x (cE O x c hc) iSub qSub (std1 O x) (sc1 O x c hc) := by
  refine ⟨(subQuot_std O x).1, (subQuot_std O x).2.1, (subQuot_std O x).2.2.1, fun s _ => ⟨?_, ?_⟩⟩
  · ext v
    simp [AddSubgroup.mem_comap, mem_standardRankOne, mem_cE, iSub_apply]
  · ext w
    rw [AddSubgroup.mem_map, mem_scaledRankOne]
    constructor
    · intro h
      refine ⟨![0, w 0], (mem_cE O).mpr ⟨by simp, by simpa using h⟩, ?_⟩
      funext k
      fin_cases k
      rfl
    · rintro ⟨v, hv, rfl⟩
      exact ((mem_cE O).mp hv).2

def shearEquiv (V : Type*) [AddCommGroup V] [Module Ω V] : (V × V) ≃ₗ[Ω] (V × V) where
  toFun p := (p.1 + p.2, p.2)
  invFun p := (p.1 - p.2, p.2)
  map_add' p q := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add]
    abel
  map_smul' c p := by
    ext <;> simp [smul_add]
  left_inv p := by
    ext <;> simp
  right_inv p := by
    ext <;> simp

def bGraph (c : Ω) (hc : c ≠ 0) : Module.Basis (Fin (1 + 1)) Ω ((Fin 1 → Ω) × (Fin 1 → Ω)) :=
  (((bSc1 c hc).prod (Pi.basisFun Ω (Fin 1))).map (shearEquiv (Fin 1 → Ω))).reindex finSumFinEquiv

/- English proof (translation)
Rewrite using `[mem_frameLat, finSumFinEquiv.symm.forall_congr_left, Equiv.symm_symm, Sum.forall, Fin.forall_fin_one, Fin.forall_fin_one]`. Simplify using `[bGraph, shearEquiv, bSc1_repr, mul_sub, and_comm]`.
-/
theorem mem_graph {x : (Σ k, ι k) → Ω} {s : ∀ k, ι k} (c : Ω) (hc : c ≠ 0) (v w : Fin 1 → Ω) :
    (v, w) ∈ frameLat O (mseg x) (bGraph c hc) s ↔
      c⁻¹ * (v 0 - w 0) ∈ chartRing O (mseg x) s ∧ w 0 ∈ chartRing O (mseg x) s := by
  rw [mem_frameLat, finSumFinEquiv.symm.forall_congr_left, Equiv.symm_symm, Sum.forall,
    Fin.forall_fin_one, Fin.forall_fin_one]
  simp [bGraph, shearEquiv, bSc1_repr, mul_sub, and_comm]

/- English proof (translation)
Establish `hcm : ∀ s, algebraMap O Ω c ∈ chartRing O (mseg x) s` using `fun s => Subalgebra.algebraMap_mem _ c`. Use `⟨frameBundle O (mseg x) (bGraph (algebraMap O Ω c) hc), fun s _ => ⟨?_, ?_, ?_, ?_⟩⟩` and prove the remaining obligations. Introduce `v`. Rewrite using `[frameBundle_lat, mem_graph, mem_scaledRankOne]`. Simplify using the standard rewrite rules.

Introduce `v`. Rewrite using `[mem_standardRankOne]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw⟩`. Rewrite `hw` using `[frameBundle_lat, mem_graph]`.

Establish `h` using `add_mem (mul_mem (hcm s) hw.1) hw.2`. Rewrite `h` using `[← mul_assoc, mul_inv_cancel₀ hc, one_mul, sub_add_cancel]`. Then use the resulting hypothesis. Introduce `hv`. Use `⟨v, ?_⟩` and prove the remaining obligations. Rewrite using `[frameBundle_lat, mem_graph]`.

Simplify using `[hv]`. Introduce `w`. Rewrite using `[frameBundle_lat, mem_graph, mem_scaledRankOne]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, _⟩`.

Simplify using `using neg_mem h1`. Introduce `h`. Use `⟨by simpa using neg_mem h, ?_⟩` and prove the remaining obligations. Establish `h2` using `mul_mem (hcm s) h`. Rewrite `h2` using `[← mul_assoc, mul_inv_cancel₀ hc, one_mul]`. Then use the resulting hypothesis.

Introduce `w`. Rewrite using `[mem_standardRankOne]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv⟩`. Rewrite `hv` using `[frameBundle_lat, mem_graph]`.

Conclude with `hv.2`. Introduce `hw`. Use `⟨w, ?_⟩` and prove the remaining obligations. Rewrite using `[frameBundle_lat, mem_graph]`. Simplify using `[hw]`.
-/
theorem quotIso_c (x : (Σ k, ι k) → Ω) (c : O) (hc : algebraMap O Ω c ≠ 0) :
    QuotIso O x (std1 O x) (sc1 O x c hc) (std1 O x) (sc1 O x c hc) := by
  have hcm : ∀ s, algebraMap O Ω c ∈ chartRing O (mseg x) s := fun s =>
    Subalgebra.algebraMap_mem _ c
  refine ⟨frameBundle O (mseg x) (bGraph (algebraMap O Ω c) hc), fun s _ => ⟨?_, ?_, ?_, ?_⟩⟩
  · intro v
    rw [frameBundle_lat, mem_graph, mem_scaledRankOne]
    simp
  · intro v
    rw [mem_standardRankOne]
    constructor
    · rintro ⟨w, hw⟩
      rw [frameBundle_lat, mem_graph] at hw
      have h := add_mem (mul_mem (hcm s) hw.1) hw.2
      rwa [← mul_assoc, mul_inv_cancel₀ hc, one_mul, sub_add_cancel] at h
    · intro hv
      refine ⟨v, ?_⟩
      rw [frameBundle_lat, mem_graph]
      simp [hv]
  · intro w
    rw [frameBundle_lat, mem_graph, mem_scaledRankOne]
    constructor
    · rintro ⟨h1, _⟩
      simpa using neg_mem h1
    · intro h
      refine ⟨by simpa using neg_mem h, ?_⟩
      have h2 := mul_mem (hcm s) h
      rwa [← mul_assoc, mul_inv_cancel₀ hc, one_mul] at h2
  · intro w
    rw [mem_standardRankOne]
    constructor
    · rintro ⟨v, hv⟩
      rw [frameBundle_lat, mem_graph] at hv
      exact hv.2
    · intro hw
      refine ⟨w, ?_⟩
      rw [frameBundle_lat, mem_graph]
      simp [hw]

end SubQuot

section PullBC

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Introduce `s _`. Establish `tr : ∀ a : Ω, a ∈ chartRing O (mseg (bcCoord (Ω₁` using `Ω) x z)) s ↔ a ∈ chartRing O (mseg x) (restrictChart s) := fun a => by`. Rewrite using `[mem_chartRing_of_one hxz, mem_chartRing_of_one hx]`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `v hv`.

Apply `AddSubgroup.subset_closure` to reduce the goal to its premises. Conclude with `⟨1, one_mem _, v, mem_frameLat.mpr fun q => (tr _).mp (mem_frameLat.mp hv q), by simp⟩`. Rewrite using `[AddSubgroup.closure_le]`. Introduce and unpack `_ ⟨a, ha, e, he, rfl⟩`. Use `mem_frameLat.mpr fun q => ?_` and prove the remaining obligations.

Rewrite using `[LinearEquiv.coe_toLinearMap, LinearEquiv.refl_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]`. Conclude with `mul_mem ha ((tr _).mpr (mem_frameLat.mp he q))`.
-/
theorem isPullBC_frame_self {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    {x : (Σ k, ι k) → Ω} {z : (Σ k, ι' k) → Ω} (hx : ∀ p, x p = 1)
    (hxz : ∀ p, bcCoord (Ω₁ := Ω) x z p = 1) {N : ℕ} {V : Type*} [AddCommGroup V] [Module Ω V]
    (b : Module.Basis (Fin N) Ω V) :
    IsPullBC O (Ω₁ := Ω) x z (LinearEquiv.refl Ω V).toLinearMap (frameBundle O (mseg x) b)
      (frameBundle O (mseg (bcCoord x z)) b) := by
  intro s _
  have tr : ∀ a : Ω, a ∈ chartRing O (mseg (bcCoord (Ω₁ := Ω) x z)) s ↔
      a ∈ chartRing O (mseg x) (restrictChart s) := fun a => by
    rw [mem_chartRing_of_one hxz, mem_chartRing_of_one hx]
  apply le_antisymm
  · intro v hv
    apply AddSubgroup.subset_closure
    exact ⟨1, one_mem _, v, mem_frameLat.mpr fun q => (tr _).mp (mem_frameLat.mp hv q),
      by simp⟩
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨a, ha, e, he, rfl⟩
    refine mem_frameLat.mpr fun q => ?_
    rw [LinearEquiv.coe_toLinearMap, LinearEquiv.refl_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact mul_mem ha ((tr _).mpr (mem_frameLat.mp he q))

/- English proof (translation)
Break down `p with ⟨k | k, i⟩` into its components or cases. Simplify using `[bcCoord, joinCoord, ptCoord]`. Conclude with `k.elim`.
-/
theorem bc_pt_eq (p : Σ k : Unit ⊕ Empty, Sum.elim ptIdx noIdx k) :
    bcCoord (Ω₁ := Ω) (ptCoord (Ω := Ω)) (noCoord (Ω := Ω)) p = 1 := by
  rcases p with ⟨k | k, i⟩
  · simp [bcCoord, joinCoord, ptCoord]
  · exact k.elim

end PullBC

section RankOne

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Introduce `s _ v hv`. Rewrite `hv` using `[mem_scaledRankOne]`. Rewrite using `[mem_standardRankOne]`. Establish `h` using `mul_mem (Subalgebra.algebraMap_mem (chartRing O (mseg x) s) c) hv`. Rewrite `h` using `[← mul_assoc, mul_inv_cancel₀ hc, one_mul]`. Then use the resulting hypothesis.
-/
theorem scaledRankOne_le_standardRankOne (x : (Σ k, ι k) → Ω) (c : O) (hc : algebraMap O Ω c ≠ 0) :
    LatLE O x (sc1 O x c hc) (std1 O x) := by
  intro s _ v hv
  rw [mem_scaledRankOne] at hv
  rw [mem_standardRankOne]
  have h := mul_mem (Subalgebra.algebraMap_mem (chartRing O (mseg x) s) c) hv
  rwa [← mul_assoc, mul_inv_cancel₀ hc, one_mul] at h

/- English proof (translation)
Introduce `s hs`. Prove the components needed by the constructor for the conclusion. Introduce `v hv`. Use `⟨c, hc0, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_scaledRankOne]`.

Rewrite `hv` using `[mem_standardRankOne]`. Simplify `hv` using `[← mul_assoc, inv_mul_cancel₀ hc]`. Introduce `v hv`. Use `⟨1, one_ne_zero, ?_⟩` and prove the remaining obligations. Rewrite using `[map_one, one_smul]`.

Conclude with `scaledRankOne_le_standardRankOne O x c hc s hs hv`.
-/
theorem sameGeneric_scaledRankOne (x : (Σ k, ι k) → Ω) (c : O) (hc0 : c ≠ 0) (hc : algebraMap O Ω c ≠ 0) :
    SameGeneric O x (std1 O x) (sc1 O x c hc) := by
  intro s hs
  constructor
  · intro v hv
    refine ⟨c, hc0, ?_⟩
    rw [mem_scaledRankOne]
    rw [mem_standardRankOne] at hv
    simpa [← mul_assoc, inv_mul_cancel₀ hc] using hv
  · intro v hv
    refine ⟨1, one_ne_zero, ?_⟩
    rw [map_one, one_smul]
    exact scaledRankOne_le_standardRankOne O x c hc s hs hv

/- English proof (translation)
Rewrite using `[mem_scaledRankOne]`. Rewrite `hv` using `[mem_standardRankOne]`. Simplify `hv` using `[← mul_assoc, inv_mul_cancel₀ hc]`.
-/
theorem smul_mem_scaledRankOne (x : (Σ k, ι k) → Ω) (c : O) (hc : algebraMap O Ω c ≠ 0) (s : ∀ k, ι k)
    (v : Fin 1 → Ω) (hv : v ∈ (std1 O x).lat s) : algebraMap O Ω c • v ∈ (sc1 O x c hc).lat s := by
  rw [mem_scaledRankOne]
  rw [mem_standardRankOne] at hv
  simpa [← mul_assoc, inv_mul_cancel₀ hc] using hv

end RankOne

section Gaussian

def gi : GaussianInt := ⟨1, 1⟩

def gI : GaussianInt := ⟨0, 1⟩

/- English proof (translation)
Simplify using `[gi, Zsqrtd.norm]`.
-/
theorem gi_norm : Zsqrtd.norm gi = 2 := by
  simp [gi, Zsqrtd.norm]

/- English proof (translation)
Introduce `h`. Use `congrArg Zsqrtd.re h` as an intermediate fact. Simplify using `[gi] at this`.
-/
theorem gi_ne_zero : gi ≠ 0 := by
  intro h
  have := congrArg Zsqrtd.re h
  simp [gi] at this

/- English proof (translation)
Use `⟨fun hu => ?_, fun a b hab => ?_⟩` and prove the remaining obligations. Use `(Zsqrtd.norm_eq_one_iff' (by norm_num) gi).mpr hu` as an intermediate fact. Rewrite `this` using `[gi_norm]`. Evaluate the numerical expressions using `at this`. Establish `hn` using `congrArg Zsqrtd.norm hab`.

Rewrite `hn` using `[Zsqrtd.norm_mul, gi_norm]`. Establish `ha` using `Zsqrtd.norm_nonneg (by norm_num) a`. Establish `hb` using `Zsqrtd.norm_nonneg (by norm_num) b`. Break down `le_or_gt (Zsqrtd.norm a) 1 with h | h` into its components or cases. Use `left`.

Use `(Zsqrtd.norm_eq_one_iff' (by norm_num) a).mp ?_` and prove the remaining obligations. Establish `h0 : Zsqrtd.norm a ≠ 0`. Introduce `h0`. Rewrite `hn` using `[h0, zero_mul]`. Evaluate the numerical expressions using `at hn`.

Use linear arithmetic over natural numbers and integers. Use `right`. Use `(Zsqrtd.norm_eq_one_iff' (by norm_num) b).mp ?_` and prove the remaining obligations. Establish `h0 : Zsqrtd.norm b ≠ 0`. Introduce `h0`.

Rewrite `hn` using `[h0, mul_zero]`. Evaluate the numerical expressions using `at hn`. Establish `h1 : Zsqrtd.norm b ≤ 1` using `by nlinarith`. Use linear arithmetic over natural numbers and integers.
-/
theorem gi_irreducible : Irreducible gi := by
  refine ⟨fun hu => ?_, fun a b hab => ?_⟩
  · have := (Zsqrtd.norm_eq_one_iff' (by norm_num) gi).mpr hu
    rw [gi_norm] at this
    norm_num at this
  · have hn := congrArg Zsqrtd.norm hab
    rw [Zsqrtd.norm_mul, gi_norm] at hn
    have ha := Zsqrtd.norm_nonneg (by norm_num) a
    have hb := Zsqrtd.norm_nonneg (by norm_num) b
    rcases le_or_gt (Zsqrtd.norm a) 1 with h | h
    · left
      refine (Zsqrtd.norm_eq_one_iff' (by norm_num) a).mp ?_
      have h0 : Zsqrtd.norm a ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hn
        norm_num at hn
      omega
    · right
      refine (Zsqrtd.norm_eq_one_iff' (by norm_num) b).mp ?_
      have h0 : Zsqrtd.norm b ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hn
        norm_num at hn
      have h1 : Zsqrtd.norm b ≤ 1 := by nlinarith
      omega

/- English proof (translation)
The claim follows from `gi_irreducible.prime`.
-/
theorem gi_prime : Prime gi :=
  gi_irreducible.prime

def gIdeal : Ideal GaussianInt := Ideal.span {gi}

instance gIdeal_isPrime : gIdeal.IsPrime :=
  (Ideal.span_singleton_prime gi_ne_zero).mpr gi_prime

/- English proof (translation)
Rewrite using `[gIdeal, Ne, Ideal.span_singleton_eq_bot]`. Conclude with `gi_ne_zero`.
-/
theorem gIdeal_ne_bot : gIdeal ≠ ⊥ := by
  rw [gIdeal, Ne, Ideal.span_singleton_eq_bot]
  exact gi_ne_zero

abbrev GO := Localization.AtPrime gIdeal

instance GO_dvr : IsDiscreteValuationRing GO :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain GaussianInt gIdeal_ne_bot GO

/- English proof (translation)
The claim follows from `IsLocalization.injective GO gIdeal.primeCompl_le_nonZeroDivisors`.
-/
theorem GO_inj : Function.Injective (algebraMap GaussianInt GO) :=
  IsLocalization.injective GO gIdeal.primeCompl_le_nonZeroDivisors

instance GO_charZero : CharZero GO :=
  charZero_of_injective_algebraMap GO_inj

def gG : GO := algebraMap GaussianInt GO gi

def uG : GO := algebraMap GaussianInt GO gI

/- English proof (translation)
Rewrite using `[Zsqrtd.ext_iff]`. Simplify using `[gi, gI, sq]`.
-/
theorem gi_sq : gi ^ 2 = gI * 2 := by
  rw [Zsqrtd.ext_iff]
  simp [gi, gI, sq]

/- English proof (translation)
Rewrite using `[gG, uG, ← map_pow, gi_sq, map_mul, Nat.cast_ofNat, map_ofNat]`.
-/
theorem gG_sq : gG ^ 2 = uG * ((2 : ℕ) : GO) := by
  rw [gG, uG, ← map_pow, gi_sq, map_mul, Nat.cast_ofNat, map_ofNat]

/- English proof (translation)
Establish `h : IsUnit gI` using `isUnit_iff_exists_inv.mpr ⟨⟨0, -1⟩, by rw [Zsqrtd.ext_iff]; simp [gI]⟩`. Conclude with `h.map _`.
-/
theorem uG_isUnit : IsUnit uG := by
  have h : IsUnit gI := isUnit_iff_exists_inv.mpr ⟨⟨0, -1⟩, by rw [Zsqrtd.ext_iff]; simp [gI]⟩
  exact h.map _

/- English proof (translation)
Rewrite using `[gG, Ne, map_eq_zero_iff _ GO_inj]`. Conclude with `gi_ne_zero`.
-/
theorem gG_ne_zero : gG ≠ 0 := by
  rw [gG, Ne, map_eq_zero_iff _ GO_inj]
  exact gi_ne_zero

end Gaussian

section FrobInhabitant

local notation "ΩG" => FractionRing GaussianInt

/- English proof (translation)
The claim follows from `(map_ne_zero_iff _ (IsFractionRing.injective GO ΩG)).mpr hc`.
-/
theorem GO_frac_ne (c : GO) (hc : c ≠ 0) : algebraMap GO ΩG c ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective GO ΩG)).mpr hc

def frobSq : (∀ k : Unit, ptIdx k) → (Fin 1 → ΩG) → (Fin 1 → ΩG) :=
  fun _ v => fun _ => v 0 ^ 2

def clR (s : ∀ k : Unit, ptIdx k) (t : ΩG) : chartRing GO (mseg (ptCoord (Ω := ΩG))) s := by
  classical
  exact if h : t ∈ chartRing GO (mseg (ptCoord (Ω := ΩG))) s then ⟨t, h⟩ else 0

/- English proof (translation)
Simplify using `[clR, h]`.
-/
theorem clR_coe {s : ∀ k : Unit, ptIdx k} {t : ΩG}
    (h : t ∈ chartRing GO (mseg (ptCoord (Ω := ΩG))) s) : (clR s t : ΩG) = t := by
  simp [clR, h]

/- English proof (translation)
Establish `hT : (algebraMap GO ΩG 2) = 2` using `map_ofNat _ 2`. Establish `h2 : (2 : ΩG) ≠ 0` using `by rw [← hT]; exact GO_frac_ne 2 two_ne_zero`. Establish `hG` using `GO_frac_ne gG gG_ne_zero`. Establish `hG2 : algebraMap GO ΩG gG ^ 2 = algebraMap GO ΩG uG * 2`. Rewrite using `[← map_pow, gG_sq, map_mul, Nat.cast_ofNat, map_ofNat]`.

Use `⟨fun s _ => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `v hv`. Rewrite `hv`, the goal using `[mem_standardRankOne]`. Conclude with `pow_mem hv 2`. Introduce `v hv`.

Rewrite `hv`, the goal using `[mem_scaledRankOne]`. Rewrite using `[hT]`. Establish `hU : algebraMap GO ΩG uG ≠ 0` using `GO_frac_ne uG uG_isUnit.ne_zero`. Establish `key : (2 : ΩG)⁻¹ * frobSq s v 0 = algebraMap GO ΩG uG * ((algebraMap GO ΩG gG)⁻¹ * v 0) ^ 2`. Rewrite using `[mul_pow, inv_pow, hG2]`.

Simplify using `only [frobSq]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[key]`. Conclude with `mul_mem (Subalgebra.algebraMap_mem _ uG) (pow_mem hv 2)`. Introduce `v hv w hw`.

Rewrite `hv`, `hw` using `[mem_standardRankOne]`. Rewrite using `[mem_scaledRankOne, hT]`. Establish `key : (2 : ΩG)⁻¹ * (frobSq s (v + w) - frobSq s v - frobSq s w) 0 = v 0 * w 0`. Simplify using `only [frobSq, Pi.sub_apply, Pi.add_apply]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`. Conclude with `mul_mem hv hw`. Introduce `a _ v _`. Rewrite using `[mem_scaledRankOne, hT]`.

Simplify using `[frobSq, mul_pow]`. Introduce `v hv`. Rewrite `hv` using `[mem_standardRankOne]`. Rewrite using `[mem_scaledRankOne, hT]`. Simplify `hv` using `[← mul_assoc, inv_mul_cancel₀ h2]`.

Introduce `Nm _ _ hkill χ hadd hker hsemi`. Establish `he1 : (fun _ => (1 : ΩG)) ∈ (std1 GO (ptCoord (Ω` using `ΩG))).lat s := (mem_standardRankOne GO).mpr (one_mem _)`. Establish `hk2 : ∀ n : Nm, (2 : chartRing GO (mseg (ptCoord (Ω` using `ΩG))) s) • n = 0 := by`. Introduce `n`. Use `hkill n` as an intermediate fact.

Rewrite `this` using `[Nat.cast_ofNat]`. Then use the resulting hypothesis. Establish `c2 : ((2 : chartRing GO (mseg (ptCoord (Ω` using `ΩG))) s) : ΩG) = 2 := map_ofNat (chartRing GO (mseg (ptCoord (Ω := ΩG))) s).val 2`. Establish `h2R : (2 : ΩG) ∈ chartRing GO (mseg (ptCoord (Ω` using `ΩG))) s := by`. Rewrite using `[← hT]`. Conclude with `Subalgebra.algebraMap_mem _ 2`.

Establish `hψe1 : frobSq s (fun _ => (1 : ΩG)) = fun _ => 1`. Use function extensionality and compare the values at `k`. Simplify using `[frobSq]`. Use `⟨fun w => clR s (w 0) • χ (fun _ => 1), ⟨?_, ?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `v hv w hw`.

Rewrite `hv`, `hw` using `[mem_standardRankOne]`. Simplify using `only`. Rewrite using `[← add_smul]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `only [Pi.add_apply, Subalgebra.coe_add]`. Rewrite using `[clR_coe (add_mem hv hw), clR_coe hv, clR_coe hw]`. Introduce `w hw`. Rewrite `hw` using `[mem_scaledRankOne, hT]`. Establish `hw0 : w 0 ∈ chartRing GO (mseg (ptCoord (Ω` using `ΩG))) s := by`.

Establish `h` using `mul_mem h2R hw`. Rewrite `h` using `[← mul_assoc, mul_inv_cancel₀ h2, one_mul]`. Then use the resulting hypothesis. Establish `hsplit : clR s (w 0) = 2 * clR s ((2 : ΩG)⁻¹ * w 0)`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Subalgebra.coe_mul, c2, clR_coe hw0, clR_coe hw]`.

Clear the denominators using the available nonvanishing facts. Use `show clR s (w 0) • χ _ = 0`. Rewrite using `[hsplit, mul_smul, hk2]`. Introduce `a w hw`. Rewrite `hw` using `[mem_standardRankOne]`.

Establish `hm : ((a : ΩG) • w) 0 ∈ chartRing GO (mseg (ptCoord (Ω` using `ΩG))) s := by`. Simplify using `using mul_mem a.2 hw`. Use `show clR s (((a : ΩG) • w) 0) • χ _ = a • (clR s (w 0) • χ _)`. Rewrite using `[← mul_smul]`. Use `congr 1`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[clR_coe hm, Subalgebra.coe_mul, clR_coe hw]`. Simplify using the standard rewrite rules. Introduce `v hv`. Establish `hv0` using `(mem_standardRankOne GO).mp hv`.

Establish `hv' : v = ((⟨v 0, hv0⟩ : chartRing GO (mseg (ptCoord (Ω` using `ΩG))) s) : ΩG) • (fun _ => (1 : ΩG)) := by`. Use function extensionality and compare the values at `k`. Use `fin_cases k`. Simplify using the standard rewrite rules. Use `show clR s (frobSq s v 0) • χ _ = χ v`.

Use `conv_rhs => rw [hv', hsemi _ _ he1]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[clR_coe (by simpa [frobSq] using pow_mem hv0 2)]`. Simplify using `[frobSq]`.

Introduce `lam' hlam' hcomp w hw`. Establish `hw0` using `(mem_standardRankOne GO).mp hw`. Establish `hw' : w = ((⟨w 0, hw0⟩ : chartRing GO (mseg (ptCoord (Ω` using `ΩG))) s) : ΩG) • (fun _ => (1 : ΩG)) := by`. Use function extensionality and compare the values at `k`. Use `fin_cases k`.

Simplify using the standard rewrite rules. Establish `hl1 : lam' (fun _ => 1) = χ (fun _ => 1)`. Use `hcomp _ he1` as an intermediate fact. Rewrite `this` using `[hψe1]`. Then use the resulting hypothesis. Use `show lam' w = clR s (w 0) • χ _`.

Rewrite using `[hw', hlam'.2.2 _ _ he1, hl1]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[clR_coe (by simpa using hw0)]`. Simplify using the standard rewrite rules.

Introduce `s t _ _ v _ m _`. Use `⟨0, ?_⟩` and prove the remaining obligations. Simplify using `only [mseg_of_one ptCoord_eq, div_one, one_pow, one_smul]`. Rewrite using `[show frobSq t v = frobSq s v from rfl, sub_self]`. Conclude with `zero_mem _`.
-/
theorem frobSq_isFrobPres :
    IsFrobPres GO 2 (ptCoord (Ω := ΩG)) (std1 GO ptCoord) (sc1 GO ptCoord gG (GO_frac_ne gG gG_ne_zero))
      (std1 GO ptCoord) (sc1 GO ptCoord 2 (GO_frac_ne 2 two_ne_zero)) frobSq := by
  have hT : (algebraMap GO ΩG 2) = 2 := map_ofNat _ 2
  have h2 : (2 : ΩG) ≠ 0 := by rw [← hT]; exact GO_frac_ne 2 two_ne_zero
  have hG := GO_frac_ne gG gG_ne_zero
  have hG2 : algebraMap GO ΩG gG ^ 2 = algebraMap GO ΩG uG * 2 := by
    rw [← map_pow, gG_sq, map_mul, Nat.cast_ofNat, map_ofNat]
  refine ⟨fun s _ => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro v hv
    rw [mem_standardRankOne] at hv ⊢
    exact pow_mem hv 2
  · intro v hv
    rw [mem_scaledRankOne] at hv ⊢
    rw [hT]
    have hU : algebraMap GO ΩG uG ≠ 0 := GO_frac_ne uG uG_isUnit.ne_zero
    have key : (2 : ΩG)⁻¹ * frobSq s v 0 =
        algebraMap GO ΩG uG * ((algebraMap GO ΩG gG)⁻¹ * v 0) ^ 2 := by
      rw [mul_pow, inv_pow, hG2]
      simp only [frobSq]
      field_simp
    rw [key]
    exact mul_mem (Subalgebra.algebraMap_mem _ uG) (pow_mem hv 2)
  · intro v hv w hw
    rw [mem_standardRankOne] at hv hw
    rw [mem_scaledRankOne, hT]
    have key : (2 : ΩG)⁻¹ * (frobSq s (v + w) - frobSq s v - frobSq s w) 0 = v 0 * w 0 := by
      simp only [frobSq, Pi.sub_apply, Pi.add_apply]
      field_simp
      ring
    rw [key]
    exact mul_mem hv hw
  · intro a _ v _
    rw [mem_scaledRankOne, hT]
    simp [frobSq, mul_pow]
  · intro v hv
    rw [mem_standardRankOne] at hv
    rw [mem_scaledRankOne, hT]
    simpa [← mul_assoc, inv_mul_cancel₀ h2] using hv
  · intro Nm _ _ hkill χ hadd hker hsemi
    have he1 : (fun _ => (1 : ΩG)) ∈ (std1 GO (ptCoord (Ω := ΩG))).lat s :=
      (mem_standardRankOne GO).mpr (one_mem _)
    have hk2 : ∀ n : Nm, (2 : chartRing GO (mseg (ptCoord (Ω := ΩG))) s) • n = 0 := by
      intro n
      have := hkill n
      rwa [Nat.cast_ofNat] at this
    have c2 : ((2 : chartRing GO (mseg (ptCoord (Ω := ΩG))) s) : ΩG) = 2 :=
      map_ofNat (chartRing GO (mseg (ptCoord (Ω := ΩG))) s).val 2
    have h2R : (2 : ΩG) ∈ chartRing GO (mseg (ptCoord (Ω := ΩG))) s := by
      rw [← hT]
      exact Subalgebra.algebraMap_mem _ 2
    have hψe1 : frobSq s (fun _ => (1 : ΩG)) = fun _ => 1 := by
      funext k
      simp [frobSq]
    refine ⟨fun w => clR s (w 0) • χ (fun _ => 1), ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · intro v hv w hw
      rw [mem_standardRankOne] at hv hw
      dsimp only
      rw [← add_smul]
      congr 1
      apply Subtype.ext
      simp only [Pi.add_apply, Subalgebra.coe_add]
      rw [clR_coe (add_mem hv hw), clR_coe hv, clR_coe hw]
    · intro w hw
      rw [mem_scaledRankOne, hT] at hw
      have hw0 : w 0 ∈ chartRing GO (mseg (ptCoord (Ω := ΩG))) s := by
        have h := mul_mem h2R hw
        rwa [← mul_assoc, mul_inv_cancel₀ h2, one_mul] at h
      have hsplit : clR s (w 0) = 2 * clR s ((2 : ΩG)⁻¹ * w 0) := by
        apply Subtype.ext
        rw [Subalgebra.coe_mul, c2, clR_coe hw0, clR_coe hw]
        field_simp
      show clR s (w 0) • χ _ = 0
      rw [hsplit, mul_smul, hk2]
    · intro a w hw
      rw [mem_standardRankOne] at hw
      have hm : ((a : ΩG) • w) 0 ∈ chartRing GO (mseg (ptCoord (Ω := ΩG))) s := by
        simpa using mul_mem a.2 hw
      show clR s (((a : ΩG) • w) 0) • χ _ = a • (clR s (w 0) • χ _)
      rw [← mul_smul]
      congr 1
      apply Subtype.ext
      rw [clR_coe hm, Subalgebra.coe_mul, clR_coe hw]
      simp
    · intro v hv
      have hv0 := (mem_standardRankOne GO).mp hv
      have hv' : v = ((⟨v 0, hv0⟩ : chartRing GO (mseg (ptCoord (Ω := ΩG))) s) : ΩG) •
          (fun _ => (1 : ΩG)) := by
        funext k
        fin_cases k
        simp
      show clR s (frobSq s v 0) • χ _ = χ v
      conv_rhs => rw [hv', hsemi _ _ he1]
      congr 1
      apply Subtype.ext
      rw [clR_coe (by simpa [frobSq] using pow_mem hv0 2)]
      simp [frobSq]
    · intro lam' hlam' hcomp w hw
      have hw0 := (mem_standardRankOne GO).mp hw
      have hw' : w = ((⟨w 0, hw0⟩ : chartRing GO (mseg (ptCoord (Ω := ΩG))) s) : ΩG) •
          (fun _ => (1 : ΩG)) := by
        funext k
        fin_cases k
        simp
      have hl1 : lam' (fun _ => 1) = χ (fun _ => 1) := by
        have := hcomp _ he1
        rwa [hψe1] at this
      show lam' w = clR s (w 0) • χ _
      rw [hw', hlam'.2.2 _ _ he1, hl1]
      congr 1
      apply Subtype.ext
      rw [clR_coe (by simpa using hw0)]
      simp
  · intro s t _ _ v _ m _
    refine ⟨0, ?_⟩
    simp only [mseg_of_one ptCoord_eq, div_one, one_pow, one_smul]
    rw [show frobSq t v = frobSq s v from rfl, sub_self]
    exact zero_mem _

end FrobInhabitant

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
