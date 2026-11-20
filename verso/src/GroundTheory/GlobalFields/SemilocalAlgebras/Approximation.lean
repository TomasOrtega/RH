import Mathlib

namespace GroundTheory.Global

open IsDedekindDomain NumberField WithZeroMulInt WithZero Topology Filter

noncomputable section

namespace SemiLocal

variable {L : Type*} [Field L] [NumberField L]

/- English proof (translation)
Take `⟨y, hy⟩` from `IsDedekindDomain.exists_forall_sub_mem_ideal (s := Finset.univ) (fun j ↦ (w j).asIdeal) (fun _ ↦ n) (fun j _ ↦ (w j).prime) (fun j _ k _ hjk h ↦ hjk (hw (HeightOneSpectrum.ext h))) (fun j ↦ if j.1 = i then 1 else 0)`. Conclude with `⟨y, fun j ↦ hy j (Finset.mem_univ j)⟩`.
-/
theorem exists_sub_mem_pow_of_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → HeightOneSpectrum (𝓞 L)) (hw : Function.Injective w) (i : ι) (n : ℕ) :
    ∃ a : 𝓞 L, ∀ j, a - (if j = i then 1 else 0) ∈ (w j).asIdeal ^ n := by
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := Finset.univ)
    (fun j ↦ (w j).asIdeal) (fun _ ↦ n) (fun j _ ↦ (w j).prime)
    (fun j _ k _ hjk h ↦ hjk (hw (HeightOneSpectrum.ext h)))
    (fun j ↦ if j.1 = i then 1 else 0)
  exact ⟨y, fun j ↦ hy j (Finset.mem_univ j)⟩

/- English proof (translation)
Rewrite using `[IsScalarTower.algebraMap_apply (𝓞 L) L (w.adicCompletion L), HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply, ← FinitePlace.embedding_apply, FinitePlace.norm_embedding_int, ← NNReal.coe_pow, NNReal.coe_le_coe, ← map_pow …`. Apply `(toNNReal_strictMono (HeightOneSpectrum.one_lt_absNorm_nnreal w)).monotone` to reduce the goal to its premises. Rewrite using `[← exp_nsmul, smul_neg, nsmul_one]`. Conclude with `(w.intValuation_le_pow_iff_mem a n).2 ha`.
-/
theorem norm_algebraMap_le_of_mem_pow (w : HeightOneSpectrum (𝓞 L)) (a : 𝓞 L) (n : ℕ)
    (ha : a ∈ w.asIdeal ^ n) :
    ‖algebraMap (𝓞 L) (w.adicCompletion L) a‖ ≤
      ((toNNReal (HeightOneSpectrum.absNorm_ne_zero w) (exp (-1 : ℤ)) : ℝ)) ^ n := by
  rw [IsScalarTower.algebraMap_apply (𝓞 L) L (w.adicCompletion L),
    HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
    Algebra.algebraMap_self, RingHom.id_apply, ← FinitePlace.embedding_apply, FinitePlace.norm_embedding_int, ← NNReal.coe_pow,
    NNReal.coe_le_coe, ← map_pow]
  apply (toNNReal_strictMono (HeightOneSpectrum.one_lt_absNorm_nnreal w)).monotone
  rw [← exp_nsmul, smul_neg, nsmul_one]
  exact (w.intValuation_le_pow_iff_mem a n).2 ha

/- English proof (translation)
Rewrite using `[← NNReal.coe_one, NNReal.coe_lt_coe, toNNReal_lt_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal w)]`. Rewrite using `[← exp_zero, exp_lt_exp]`. Evaluate the numerical expressions.
-/
theorem toNNReal_exp_neg_one_lt_one (w : HeightOneSpectrum (𝓞 L)) :
    ((toNNReal (HeightOneSpectrum.absNorm_ne_zero w) (exp (-1 : ℤ)) : ℝ)) < 1 := by
  rw [← NNReal.coe_one, NNReal.coe_lt_coe,
    toNNReal_lt_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal w)]
  rw [← exp_zero, exp_lt_exp]
  norm_num

/- English proof (translation)
Use `Fintype.ofFinite ι` as an intermediate fact. Set `f : L →+* ((i : ι) → (w i).adicCompletion L)` to `RingHom.pi fun i ↦ algebraMap L _`. Set `S : Subring ((i : ι) → (w i).adicCompletion L)` to `f.range.topologicalClosure`. Establish `hδ : ∀ i, Pi.single i 1 ∈ S`. Introduce `i`.

Use `choose a ha using fun n ↦ exists_sub_mem_pow_of_injective w hw i n`. Use `mem_closure_of_tendsto (b := atTop) (f := fun n ↦ f (algebraMap (𝓞 L) L (a n))) ?_ (Eventually.of_forall fun n ↦ ⟨_, rfl⟩)` and prove the remaining obligations. Rewrite using `[tendsto_pi_nhds]`. Introduce `j`. Rewrite using `[tendsto_iff_norm_sub_tendsto_zero]`.

Use `squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_) (tendsto_pow_atTop_nhds_zero_of_lt_one (NNReal.coe_nonneg _) (toNNReal_exp_neg_one_lt_one (w j)))` and prove the remaining obligations. Establish `h` using `norm_algebraMap_le_of_mem_pow (w j) _ n (ha n j)`. Use `le_of_eq_of_le ?_ h` and prove the remaining obligations. Use `congr 1`. Distinguish the cases in `hji : j = i`.

Substitute `hji` using the available equality. Simplify using `[f, ← IsScalarTower.algebraMap_apply]`. Simplify using `[f, hji, ← IsScalarTower.algebraMap_apply]`. Establish `hE : ∀ y : ι → L, (fun i ↦ algebraMap L ((w i).adicCompletion L) (y i)) ∈ S`. Introduce `y`.

Establish `: (fun i ↦ algebraMap L ((w i).adicCompletion L) (y i)) = ∑ i, Pi.single i 1 * f (y i)`. Use function extensionality and compare the values at `j`. Simplify using `only [Finset.sum_apply, Pi.mul_apply, f, RingHom.pi_apply]`. Rewrite using `[Finset.sum_eq_single j]`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Simplify using `[Pi.single_eq_of_ne hb.symm]`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `S.sum_mem fun i _ ↦ S.mul_mem (hδ i) (f.range.le_topologicalClosure ⟨y i, rfl⟩)`.

Establish `hdense : DenseRange (fun y : ι → L ↦ fun i ↦ algebraMap L ((w i).adicCompletion L) (y i))` using `DenseRange.piMap fun i ↦ HeightOneSpectrum.denseRange_algebraMap L (w i)`. Establish `hsub : Set.range (fun y : ι → L ↦ fun i ↦ algebraMap L ((w i).adicCompletion L) (y i)) ⊆ closure (Set.range f)`. Introduce and unpack `_ ⟨y, rfl⟩`. Conclude with `hE y`. Conclude with `dense_closure.1 (hdense.mono hsub)`.
-/
theorem denseRange_algebraMap_pi {ι : Type*} [Finite ι] (w : ι → HeightOneSpectrum (𝓞 L))
    (hw : Function.Injective w) :
    DenseRange (fun x : L ↦ fun i ↦ algebraMap L ((w i).adicCompletion L) x) := by
  classical
  have := Fintype.ofFinite ι
  let f : L →+* ((i : ι) → (w i).adicCompletion L) := RingHom.pi fun i ↦ algebraMap L _
  let S : Subring ((i : ι) → (w i).adicCompletion L) := f.range.topologicalClosure
  have hδ : ∀ i, Pi.single i 1 ∈ S := by
    intro i
    choose a ha using fun n ↦ exists_sub_mem_pow_of_injective w hw i n
    refine mem_closure_of_tendsto (b := atTop) (f := fun n ↦ f (algebraMap (𝓞 L) L (a n))) ?_
      (Eventually.of_forall fun n ↦ ⟨_, rfl⟩)
    rw [tendsto_pi_nhds]
    intro j
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (NNReal.coe_nonneg _)
        (toNNReal_exp_neg_one_lt_one (w j)))
    have h := norm_algebraMap_le_of_mem_pow (w j) _ n (ha n j)
    refine le_of_eq_of_le ?_ h
    congr 1
    by_cases hji : j = i
    · subst hji
      simp [f, ← IsScalarTower.algebraMap_apply]
    · simp [f, hji, ← IsScalarTower.algebraMap_apply]
  have hE : ∀ y : ι → L, (fun i ↦ algebraMap L ((w i).adicCompletion L) (y i)) ∈ S := by
    intro y
    have : (fun i ↦ algebraMap L ((w i).adicCompletion L) (y i)) =
        ∑ i, Pi.single i 1 * f (y i) := by
      funext j
      simp only [Finset.sum_apply, Pi.mul_apply, f, RingHom.pi_apply]
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb.symm]
      · simp
    rw [this]
    exact S.sum_mem fun i _ ↦ S.mul_mem (hδ i) (f.range.le_topologicalClosure ⟨y i, rfl⟩)
  have hdense : DenseRange (fun y : ι → L ↦ fun i ↦ algebraMap L ((w i).adicCompletion L) (y i)) :=
    DenseRange.piMap fun i ↦ HeightOneSpectrum.denseRange_algebraMap L (w i)
  have hsub : Set.range (fun y : ι → L ↦ fun i ↦ algebraMap L ((w i).adicCompletion L) (y i)) ⊆
      closure (Set.range f) := by
    rintro _ ⟨y, rfl⟩
    exact hE y
  exact dense_closure.1 (hdense.mono hsub)

end SemiLocal

end

end GroundTheory.Global
