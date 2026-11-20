import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MemMinimalPrimesOfMemDivSuppDivSupp
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.PNefOnFibresRelabel
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Heights.Targets.Relabel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights

section Blocks

/- English proof (translation)
Use function extensionality and compare the values at `j`. Use `Fin.lastCases ?_ (fun j => ?_) j` and prove the remaining obligations. Simplify using `only [Fin.snoc_last]`. Simplify using `only [Fin.snoc_castSucc]`.
-/
theorem snoc_comp {K₁ K₂ : Type*} (c : K₁ → K₂) {n : ℕ} (L : Fin n → K₂ → ℤ) (A : K₂ → ℤ) :
    (fun j => Fin.snoc (α := fun _ => K₂ → ℤ) L A j ∘ c) =
      Fin.snoc (α := fun _ => K₁ → ℤ) (fun j => L j ∘ c) (A ∘ c) := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [Fin.snoc_last]
  · simp only [Fin.snoc_castSucc]

end Blocks

variable {F : Type*} [Field F] {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]
  (e : K ≃ K') (h : ∀ k, ι k ≃ ι' (e k))

/- English proof (translation)
Unfold `cycEval`. Conclude with `Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)`.
-/
theorem cycEval_mapDomain (c : Ideal (MRingOver F ι) → Ideal (MRingOver F ι'))
    (N : Ideal (MRingOver F ι') → ℤ) (D : Ideal (MRingOver F ι) →₀ ℤ) :
    cycEval N (Finsupp.mapDomain c D) = cycEval (fun W => N (c W)) D := by
  unfold cycEval
  exact Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

def vars : (Σ k, ι k) ≃ (Σ k', ι' k') :=
  Equiv.sigmaCongr e h

variable (F) in

def ringEquiv : MRingOver F ι ≃+* MRingOver F ι' :=
  (renameEquiv F (vars e h)).toRingEquiv

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ringEquiv_apply (f : MRingOver F ι) : ringEquiv F e h f = rename (vars e h) f :=
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ringEquiv_symm_apply (f : MRingOver F ι') :
    (ringEquiv F e h).symm f = rename (vars e h).symm f :=
  rfl

/- English proof (translation)
Rewrite using `[ringEquiv_apply, rename_X]`. Both sides reduce to the same expression.
-/
theorem ringEquiv_X (k : K) (i : ι k) :
    ringEquiv F e h (X ⟨k, i⟩) = X ⟨e k, h k i⟩ := by
  rw [ringEquiv_apply, rename_X]
  rfl

/- English proof (translation)
Rewrite using `[← ringEquiv_X, mem_map_ringEquiv_iff]`.
-/
theorem X_mem_map_iff (V : Ideal (MRingOver F ι)) (k : K) (i : ι k) :
    (X ⟨e k, h k i⟩ : MRingOver F ι') ∈ V.map (ringEquiv F e h) ↔
      (X ⟨k, i⟩ : MRingOver F ι) ∈ V := by
  rw [← ringEquiv_X, mem_map_ringEquiv_iff]

/- English proof (translation)
Assemble the required witnesses or components as `⟨V'.comap (ringEquiv F e h), (Ideal.map_comap_of_surjective _ (ringEquiv F e h).surjective V').symm⟩`.
-/
theorem exists_map_eq (V' : Ideal (MRingOver F ι')) : ∃ V : Ideal (MRingOver F ι), V' = V.map (ringEquiv F e h) :=
  ⟨V'.comap (ringEquiv F e h),
    (Ideal.map_comap_of_surjective _ (ringEquiv F e h).surjective V').symm⟩

/- English proof (translation)
The claim follows from `Ideal.comap_map_of_bijective _ (ringEquiv F e h).bijective`.
-/
theorem comap_map (V : Ideal (MRingOver F ι)) :
    (V.map (ringEquiv F e h)).comap (ringEquiv F e h) = V :=
  Ideal.comap_map_of_bijective _ (ringEquiv F e h).bijective

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hV k`. Take `⟨i', hi'⟩` from `hV (e k)`. Use `⟨(h k).symm i', fun hmem => hi' ?_⟩` and prove the remaining obligations. Use `(X_mem_map_iff e h V k _).2 hmem` as an intermediate fact.

Rewrite `this` using `[Equiv.apply_symm_apply]`. Then use the resulting hypothesis. Introduce `hV k'`. Take `⟨k, rfl⟩` from `e.surjective k'`. Take `⟨i, hi⟩` from `hV k`. Conclude with `⟨h k i, fun hmem => hi ((X_mem_map_iff e h V k i).1 hmem)⟩`.
-/
theorem isRelevant_map_iff (V : Ideal (MRingOver F ι)) :
    IsRelevant (V.map (ringEquiv F e h)) ↔ IsRelevant V := by
  constructor
  · intro hV k
    obtain ⟨i', hi'⟩ := hV (e k)
    refine ⟨(h k).symm i', fun hmem => hi' ?_⟩
    have := (X_mem_map_iff e h V k _).2 hmem
    rwa [Equiv.apply_symm_apply] at this
  · intro hV k'
    obtain ⟨k, rfl⟩ := e.surjective k'
    obtain ⟨i, hi⟩ := hV k
    exact ⟨h k i, fun hmem => hi ((X_mem_map_iff e h V k i).1 hmem)⟩

/- English proof (translation)
Introduce `m hm k'`. Rewrite `hm` using `[ringEquiv_apply, support_rename_of_injective (vars e h).injective, Finset.mem_image]`. Take `⟨m₀, hm₀, rfl⟩` from `hm`. Take `⟨k, rfl⟩` from `e.surjective k'`. Rewrite using `[Function.comp_apply, e.symm_apply_apply, ← hf m₀ hm₀ k, ← (h k).sum_comp]`.

Conclude with `Finset.sum_congr rfl fun i _ => Finsupp.mapDomain_apply (vars e h).injective m₀ ⟨k, i⟩`.
-/
theorem isMultiHomog_map {f : MRingOver F ι} {d : K → ℕ} (hf : IsMultiHomog f d) :
    IsMultiHomog (ringEquiv F e h f) (d ∘ e.symm) := by
  classical
  intro m hm k'
  rw [ringEquiv_apply, support_rename_of_injective (vars e h).injective, Finset.mem_image] at hm
  obtain ⟨m₀, hm₀, rfl⟩ := hm
  obtain ⟨k, rfl⟩ := e.surjective k'
  rw [Function.comp_apply, e.symm_apply_apply, ← hf m₀ hm₀ k, ← (h k).sum_comp]
  exact Finset.sum_congr rfl fun i _ =>
    Finsupp.mapDomain_apply (vars e h).injective m₀ ⟨k, i⟩

/- English proof (translation)
Introduce `m hm k`. Rewrite `hm` using `[ringEquiv_symm_apply, support_rename_of_injective (vars e h).symm.injective, Finset.mem_image]`. Take `⟨m₀, hm₀, rfl⟩` from `hm`. Rewrite using `[Function.comp_apply, ← hg m₀ hm₀ (e k), ← (h k).sum_comp]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Use `Finsupp.mapDomain_apply (vars e h).symm.injective m₀ (vars e h ⟨k, i⟩)` as an intermediate fact. Rewrite `this` using `[Equiv.symm_apply_apply]`. Conclude with `this`.
-/
theorem isMultiHomog_symm {g : MRingOver F ι'} {d : K' → ℕ} (hg : IsMultiHomog g d) :
    IsMultiHomog ((ringEquiv F e h).symm g) (d ∘ e) := by
  classical
  intro m hm k
  rw [ringEquiv_symm_apply, support_rename_of_injective (vars e h).symm.injective,
    Finset.mem_image] at hm
  obtain ⟨m₀, hm₀, rfl⟩ := hm
  rw [Function.comp_apply, ← hg m₀ hm₀ (e k), ← (h k).sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := Finsupp.mapDomain_apply (vars e h).symm.injective m₀ (vars e h ⟨k, i⟩)
  rw [Equiv.symm_apply_apply] at this
  exact this

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨S, hS, hVS⟩`. Use `⟨(ringEquiv F e h).symm '' S, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨g, hg, rfl⟩`. Take `⟨d, hd⟩` from `hS g hg`.

Conclude with `⟨_, isMultiHomog_symm e h hd⟩`. Rewrite using `[← Ideal.map_span, ← hVS, Ideal.map_symm, comap_map]`. Introduce and unpack `⟨S, hS, rfl⟩`. Use `⟨ringEquiv F e h '' S, ?_, Ideal.map_span _ _⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨f, hf, rfl⟩`.

Take `⟨d, hd⟩` from `hS f hf`. Conclude with `⟨_, isMultiHomog_map e h hd⟩`.
-/
theorem isMultiHomogIdeal_map_iff (V : Ideal (MRingOver F ι)) :
    IsMultiHomogIdeal (V.map (ringEquiv F e h)) ↔ IsMultiHomogIdeal V := by
  constructor
  · rintro ⟨S, hS, hVS⟩
    refine ⟨(ringEquiv F e h).symm '' S, ?_, ?_⟩
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨d, hd⟩ := hS g hg
      exact ⟨_, isMultiHomog_symm e h hd⟩
    · rw [← Ideal.map_span, ← hVS, Ideal.map_symm, comap_map]
  · rintro ⟨S, hS, rfl⟩
    refine ⟨ringEquiv F e h '' S, ?_, Ideal.map_span _ _⟩
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨d, hd⟩ := hS f hf
    exact ⟨_, isMultiHomog_map e h hd⟩

/- English proof (translation)
Unfold `IsProjVarF IsMultiProjPrime`. Rewrite using `[isPrime_map_ringEquiv_iff, isMultiHomogIdeal_map_iff, isRelevant_map_iff, ringKrullDim_quotient_map, Fintype.card_congr e]`.
-/
theorem isProjVarF_map_iff (V : Ideal (MRingOver F ι)) (d : ℕ) :
    IsProjVarF (V.map (ringEquiv F e h)) d ↔ IsProjVarF V d := by
  unfold IsProjVarF IsMultiProjPrime
  rw [isPrime_map_ringEquiv_iff, isMultiHomogIdeal_map_iff, isRelevant_map_iff,
    ringKrullDim_quotient_map, Fintype.card_congr e]

/- English proof (translation)
Introduce `k hk`. Apply `hi' (e k)` to reduce the goal to its premises. Use `(X_mem_map_iff e h V k ((h k).symm (i' (e k)))).2 hk` as an intermediate fact. Rewrite `this` using `[Equiv.apply_symm_apply]`. Then use the resulting hypothesis.
-/
theorem isChart_of_map {V : Ideal (MRingOver F ι)} {i' : ∀ k', ι' k'}
    (hi' : IsChart (V.map (ringEquiv F e h)) i') : IsChart V fun k => (h k).symm (i' (e k)) := by
  intro k hk
  apply hi' (e k)
  have := (X_mem_map_iff e h V k ((h k).symm (i' (e k)))).2 hk
  rwa [Equiv.apply_symm_apply] at this

/- English proof (translation)
Establish `hrange : (Set.range fun k' => (X ⟨k', i' k'⟩ : MRingOver F ι') - 1) = ringEquiv F e h '' Set.range fun k => (X ⟨k, (h k).symm (i' (e k))⟩ : MRingOver F ι) - 1`. Use extensionality with `x`. Simplify using `only [Set.mem_range, Set.mem_image, exists_exists_eq_and]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k', rfl⟩`.

Take `⟨k, rfl⟩` from `e.surjective k'`. Conclude with `⟨k, by rw [map_sub, map_one, ringEquiv_X, Equiv.apply_symm_apply]⟩`. Introduce and unpack `⟨k, rfl⟩`. Conclude with `⟨e k, by rw [map_sub, map_one, ringEquiv_X, Equiv.apply_symm_apply]⟩`. Unfold `chartIdeal`.

Rewrite using `[hrange, Ideal.map_sup, Ideal.map_span]`.
-/
theorem chartIdeal_map (V : Ideal (MRingOver F ι)) (i' : ∀ k', ι' k') :
    chartIdeal (V.map (ringEquiv F e h)) i' =
      (chartIdeal V fun k => (h k).symm (i' (e k))).map (ringEquiv F e h) := by
  have hrange : (Set.range fun k' => (X ⟨k', i' k'⟩ : MRingOver F ι') - 1) =
      ringEquiv F e h '' Set.range fun k => (X ⟨k, (h k).symm (i' (e k))⟩ : MRingOver F ι) - 1 := by
    ext x
    simp only [Set.mem_range, Set.mem_image, exists_exists_eq_and]
    constructor
    · rintro ⟨k', rfl⟩
      obtain ⟨k, rfl⟩ := e.surjective k'
      exact ⟨k, by rw [map_sub, map_one, ringEquiv_X, Equiv.apply_symm_apply]⟩
    · rintro ⟨k, rfl⟩
      exact ⟨e k, by rw [map_sub, map_one, ringEquiv_X, Equiv.apply_symm_apply]⟩
  unfold chartIdeal
  rw [hrange, Ideal.map_sup, Ideal.map_span]

/- English proof (translation)
Unfold `ptDeg`. Rewrite using `[chartIdeal_map]`. Conclude with `(Ideal.quotientEquivAlg (chartIdeal V fun k => (h k).symm (i' (e k))) _ (renameEquiv F (vars e h)) rfl).toLinearEquiv.finrank_eq.symm`.
-/
theorem ptDeg_map (V : Ideal (MRingOver F ι)) (i' : ∀ k', ι' k') :
    ptDeg (V.map (ringEquiv F e h)) i' = ptDeg V fun k => (h k).symm (i' (e k)) := by
  unfold ptDeg
  rw [chartIdeal_map]
  exact (Ideal.quotientEquivAlg (chartIdeal V fun k => (h k).symm (i' (e k))) _
    (renameEquiv F (vars e h)) rfl).toLinearEquiv.finrank_eq.symm

/- English proof (translation)
Rewrite using `[Ideal.map_sup, Ideal.map_span, Set.image_singleton]`.
-/
theorem sup_span_map (V : Ideal (MRingOver F ι)) (f : MRingOver F ι) :
    V.map (ringEquiv F e h) ⊔ Ideal.span {ringEquiv F e h f} =
      (V ⊔ Ideal.span {f}).map (ringEquiv F e h) := by
  rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]

/- English proof (translation)
Simplify using `only [divSupp, Set.mem_ofPred_eq, sup_span_map, minimalPrimes_map_ringEquiv, (map_ringEquiv_injective (ringEquiv F e h)).mem_set_image, isRelevant_map_iff]`.
-/
theorem mem_divSupp_map_iff (V W : Ideal (MRingOver F ι)) (f : MRingOver F ι) :
    W.map (ringEquiv F e h) ∈ divSupp (V.map (ringEquiv F e h)) (ringEquiv F e h f) ↔
      W ∈ divSupp V f := by
  simp only [divSupp, Set.mem_ofPred_eq, sup_span_map, minimalPrimes_map_ringEquiv,
    (map_ringEquiv_injective (ringEquiv F e h)).mem_set_image, isRelevant_map_iff]

/- English proof (translation)
Unfold `multAt`. Distinguish the cases in `hW : W.IsPrime`. Establish `hW' : (W.map (ringEquiv F e h)).IsPrime` using `(isPrime_map_ringEquiv_iff _ W).2 hW`. Rewrite using `[dif_pos hW, dif_pos hW']`. Conclude with `congrArg ENat.toNat (length_localizedModule_quotient_map (ringEquiv F e h) J W)`.

Establish `hW' : ¬ (W.map (ringEquiv F e h)).IsPrime` using `fun h' => hW ((isPrime_map_ringEquiv_iff _ W).1 h')`. Rewrite using `[dif_neg hW, dif_neg hW']`.
-/
theorem multAt_map (J W : Ideal (MRingOver F ι)) :
    multAt (J.map (ringEquiv F e h)) (W.map (ringEquiv F e h)) = multAt J W := by
  unfold multAt
  by_cases hW : W.IsPrime
  · have hW' : (W.map (ringEquiv F e h)).IsPrime := (isPrime_map_ringEquiv_iff _ W).2 hW
    rw [dif_pos hW, dif_pos hW']
    exact congrArg ENat.toNat (length_localizedModule_quotient_map (ringEquiv F e h) J W)
  · have hW' : ¬ (W.map (ringEquiv F e h)).IsPrime :=
      fun h' => hW ((isPrime_map_ringEquiv_iff _ W).1 h')
    rw [dif_neg hW, dif_neg hW']

/- English proof (translation)
Distinguish the cases in `hs : W ∈ divSupp V f`. Rewrite using `[DivisorCycleSwap.divCycle_apply_of_mem hs, DivisorCycleSwap.divCycle_apply_of_mem ((mem_divSupp_map_iff e h V W f).2 hs), sup_span_map, multAt_map]`. Rewrite using `[DivisorCycleSwap.divCycle_apply_of_not_mem hs, DivisorCycleSwap.divCycle_apply_of_not_mem (mt (mem_divSupp_map_iff e h V W f).1 hs)]`.
-/
theorem divCycle_map_apply (V W : Ideal (MRingOver F ι)) (f : MRingOver F ι) :
    divCycle (V.map (ringEquiv F e h)) (ringEquiv F e h f) (W.map (ringEquiv F e h)) =
      divCycle V f W := by
  by_cases hs : W ∈ divSupp V f
  · rw [DivisorCycleSwap.divCycle_apply_of_mem hs,
      DivisorCycleSwap.divCycle_apply_of_mem ((mem_divSupp_map_iff e h V W f).2 hs), sup_span_map, multAt_map]
  · rw [DivisorCycleSwap.divCycle_apply_of_not_mem hs,
      DivisorCycleSwap.divCycle_apply_of_not_mem (mt (mem_divSupp_map_iff e h V W f).1 hs)]

/- English proof (translation)
Use extensionality with `W'`. Take `⟨W, rfl⟩` from `exists_map_eq e h W'`. Rewrite using `[Finsupp.mapDomain_apply (map_ringEquiv_injective (ringEquiv F e h))]`. Simplify using `only [ratDiv, Finsupp.coe_sub, Pi.sub_apply, Finsupp.mapRange_apply, divCycle_map_apply]`.
-/
theorem ratDiv_map (V : Ideal (MRingOver F ι)) (f g : MRingOver F ι) :
    ratDiv (V.map (ringEquiv F e h)) (ringEquiv F e h f) (ringEquiv F e h g) =
      Finsupp.mapDomain (Ideal.map (ringEquiv F e h)) (ratDiv V f g) := by
  ext W'
  obtain ⟨W, rfl⟩ := exists_map_eq e h W'
  rw [Finsupp.mapDomain_apply (map_ringEquiv_injective (ringEquiv F e h))]
  simp only [ratDiv, Finsupp.coe_sub, Pi.sub_apply, Finsupp.mapRange_apply, divCycle_map_apply]

/- English proof (translation)
Take `⟨α, β, hα, hβ, hf, hg, hd⟩` from `hs`. Establish `hα'` using `isMultiHomog_symm e h hα`. Establish `hβ'` using `isMultiHomog_symm e h hβ`. Rewrite `hα'`, `hβ'` using `[RingEquiv.symm_apply_apply]`. Conclude with `⟨α ∘ e, β ∘ e, hα', hβ', fun hf' => hf ((mem_map_ringEquiv_iff _ V f).2 hf'), fun hg' => hg ((mem_map_ringEquiv_iff _ V g).2 hg'), fun k => hd (e k)⟩`.
-/
theorem isRatSection_of_map {V : Ideal (MRingOver F ι)} {A : K' → ℤ} {f g : MRingOver F ι}
    (hs : IsRatSection (V.map (ringEquiv F e h)) A (ringEquiv F e h f) (ringEquiv F e h g)) :
    IsRatSection V (A ∘ e) f g := by
  obtain ⟨α, β, hα, hβ, hf, hg, hd⟩ := hs
  have hα' := isMultiHomog_symm e h hα
  have hβ' := isMultiHomog_symm e h hβ
  rw [RingEquiv.symm_apply_apply] at hα' hβ'
  exact ⟨α ∘ e, β ∘ e, hα', hβ', fun hf' => hf ((mem_map_ringEquiv_iff _ V f).2 hf'),
    fun hg' => hg ((mem_map_ringEquiv_iff _ V g).2 hg'), fun k => hd (e k)⟩

def pullFamily (I : IFamily F ι) : IFamily F ι' :=
  fun W n L => I (W.comap (ringEquiv F e h)) n fun j => L j ∘ e

def pushFamily (I' : IFamily F ι') : IFamily F ι :=
  fun W n L => I' (W.map (ringEquiv F e h)) n fun j => L j ∘ e.symm

/- English proof (translation)
Use `⟨fun V' L i' hV' hi' => ?_, fun V' n L A f' g' hV' hs => ?_⟩` and prove the remaining obligations. Take `⟨V, rfl⟩` from `exists_map_eq e h V' show I _ 0 _ = _`. Rewrite using `[comap_map, ptDeg_map]`. Conclude with `hI.1 V _ _ ((isProjVarF_map_iff e h V 0).1 hV') (isChart_of_map e h hi')`. Take `⟨V, rfl⟩` from `exists_map_eq e h V'`.

Take `⟨f, rfl⟩` from `(ringEquiv F e h).surjective f'`. Take `⟨g, rfl⟩` from `(ringEquiv F e h).surjective g'`. Use `show I _ (n + 1) _ = _`. Rewrite using `[comap_map, snoc_comp e L A, hI.2 V n _ (A ∘ e) f g ((isProjVarF_map_iff e h V _).1 hV') (isRatSection_of_map e h hs), ratDiv_map, cycEval_mapDomain]`. Simplify using `only [pullFamily, comap_map]`.
-/
theorem isFieldIntersection_pull {I : IFamily F ι} (hI : IsFieldIntersection I) :
    IsFieldIntersection (pullFamily e h I) := by
  refine ⟨fun V' L i' hV' hi' => ?_, fun V' n L A f' g' hV' hs => ?_⟩
  · obtain ⟨V, rfl⟩ := exists_map_eq e h V'
    show I _ 0 _ = _
    rw [comap_map, ptDeg_map]
    exact hI.1 V _ _ ((isProjVarF_map_iff e h V 0).1 hV') (isChart_of_map e h hi')
  · obtain ⟨V, rfl⟩ := exists_map_eq e h V'
    obtain ⟨f, rfl⟩ := (ringEquiv F e h).surjective f'
    obtain ⟨g, rfl⟩ := (ringEquiv F e h).surjective g'
    show I _ (n + 1) _ = _
    rw [comap_map, snoc_comp e L A,
      hI.2 V n _ (A ∘ e) f g ((isProjVarF_map_iff e h V _).1 hV') (isRatSection_of_map e h hs),
      ratDiv_map, cycEval_mapDomain]
    simp only [pullFamily, comap_map]

end GroundTheory.Heights₂.Heights.Targets.Relabel
