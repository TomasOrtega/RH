import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.LinEmbedSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CurvePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MemMinimalPrimesOfMemDivSuppDivSupp
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialMultAt
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.LinEmbed

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

set_option linter.unusedSectionVars false

section General

variable {F : Type} [Field F] {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
  [∀ k, Fintype (ι k)] [∀ k', Fintype (ι' k')]

/- English proof (translation)
Introduce `m hm k`. Rewrite `hm` using `[mem_support_iff, coeff_C]`. Use `split_ifs at hm with h`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Conclude with `absurd rfl hm`.
-/
theorem isMultiHomog_C (c : F) : IsMultiHomog (C c : MRingOver F ι) 0 := by
  classical
  intro m hm k
  rw [mem_support_iff, coeff_C] at hm
  split_ifs at hm with h
  · subst h
    simp
  · exact absurd rfl hm

/- English proof (translation)
Introduce `m hm`. Rewrite `hm` using `[support_neg]`. Conclude with `hg m hm`.
-/
theorem isMultiHomog_neg {g : MRingOver F ι} {a : K → ℕ} (hg : IsMultiHomog g a) :
    IsMultiHomog (-g) a := by
  intro m hm
  rw [support_neg] at hm
  exact hg m hm

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `isMultiHomog_add hf (isMultiHomog_neg hg)`.
-/
theorem isMultiHomog_sub {f g : MRingOver F ι} {a : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g a) : IsMultiHomog (f - g) a := by
  rw [sub_eq_add_neg]
  exact isMultiHomog_add hf (isMultiHomog_neg hg)

open Classical in

/- English proof (translation)
Use `conv_lhs => rw [s.as_sum]`. Rewrite using `[map_sum]`. Use `isMultiHomog_sum _ _ fun m hm => ?_` and prove the remaining obligations. Establish `hm'` using `hs m hm`. Establish `hdeg : (0 + ∑ p ∈ m.support, m p • (Pi.single (τ p.1) 1 : K' → ℕ)) = a ∘ τ.symm`.

Use function extensionality and compare the values at `k'`. Rewrite using `[zero_add, Finset.sum_apply, Function.comp_apply, ← hm' (τ.symm k')]`. Rewrite using `[Finset.sum_subset (Finset.subset_univ _) (fun p _ hp => by`. Rewrite using `[Finsupp.notMem_support_iff.mp hp, zero_smul, Pi.zero_apply])]`. Rewrite using `[Fintype.sum_sigma, Finset.sum_eq_single (τ.symm k')]`.

Simplify using the standard rewrite rules. Introduce `k _ hk`. Establish `hk' : k' ≠ τ k` using `fun h => hk (by rw [h, Equiv.symm_apply_apply])`. Simplify using `[Pi.single_eq_of_ne hk']`. Simplify using the standard rewrite rules.

Establish `h` using `isMultiHomog_mul (isMultiHomog_C (ι := ι') (coeff m s)) (isMultiHomog_prod m.support _ _ fun p _ => isMultiHomog_pow (hg p) (m p))`. Rewrite `h` using `[hdeg]`. Rewrite using `[aeval_monomial, MvPolynomial.algebraMap_eq]` and apply the resulting hypothesis.
-/
theorem isMultiHomog_aeval (τ : K ≃ K') (g : (Σ k, ι k) → MRingOver F ι')
    (hg : ∀ p, IsMultiHomog (g p) (Pi.single (τ p.1) 1)) {s : MRingOver F ι} {a : K → ℕ}
    (hs : IsMultiHomog s a) : IsMultiHomog (aeval g s) (a ∘ τ.symm) := by
  classical
  conv_lhs => rw [s.as_sum]
  rw [map_sum]
  refine isMultiHomog_sum _ _ fun m hm => ?_
  have hm' := hs m hm
  have hdeg : (0 + ∑ p ∈ m.support, m p • (Pi.single (τ p.1) 1 : K' → ℕ)) = a ∘ τ.symm := by
    funext k'
    rw [zero_add, Finset.sum_apply, Function.comp_apply, ← hm' (τ.symm k')]
    rw [Finset.sum_subset (Finset.subset_univ _) (fun p _ hp => by
      rw [Finsupp.notMem_support_iff.mp hp, zero_smul, Pi.zero_apply])]
    rw [Fintype.sum_sigma, Finset.sum_eq_single (τ.symm k')]
    · simp
    · intro k _ hk
      have hk' : k' ≠ τ k := fun h => hk (by rw [h, Equiv.symm_apply_apply])
      simp [Pi.single_eq_of_ne hk']
    · simp
  have h := isMultiHomog_mul (isMultiHomog_C (ι := ι') (coeff m s))
    (isMultiHomog_prod m.support _ _ fun p _ => isMultiHomog_pow (hg p) (m p))
  rw [hdeg] at h
  rwa [aeval_monomial, MvPolynomial.algebraMap_eq]

/- English proof (translation)
Unfold `cycEval`. Conclude with `Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)`.
-/
theorem cycEval_mapDomain (c : Ideal (MRingOver F ι) → Ideal (MRingOver F ι'))
    (N : Ideal (MRingOver F ι') → ℤ) (D : Ideal (MRingOver F ι) →₀ ℤ) :
    cycEval N (Finsupp.mapDomain c D) = cycEval (fun W => N (c W)) D := by
  unfold cycEval
  exact Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

/- English proof (translation)
Use `(injective_iff_map_eq_zero f).mpr fun x hx => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Take `⟨y, hy⟩` from `hR.mul_inv_cancel hne`. Establish `h : f (x * y) = 1` using `by rw [hy, map_one]`. Rewrite `h` using `[map_mul, hx, zero_mul]`.

Conclude with `zero_ne_one h`.
-/
theorem injective_of_isField {R S : Type*} [CommRing R] [CommRing S] [Nontrivial S] (hR : IsField R)
    (f : R →+* S) : Function.Injective f := by
  refine (injective_iff_map_eq_zero f).mpr fun x hx => ?_
  by_contra hne
  obtain ⟨y, hy⟩ := hR.mul_inv_cancel hne
  have h : f (x * y) = 1 := by rw [hy, map_one]
  rw [map_mul, hx, zero_mul] at h
  exact zero_ne_one h

def linChartMap {V : Ideal (MRingOver F ι)} (hV : IsMultiHomogIdeal V) (i : ∀ k, ι k) {B : Type*}
    [CommRing B] [Algebra F B] (θ : MRingOver F ι →ₐ[F] B) (hθ : ∀ g ∈ V, θ g = 0)
    (hu : ∀ k, IsUnit (θ (X ⟨k, i k⟩))) : (MRingOver F ι ⧸ chartIdeal V i) →ₐ[F] B :=
  Ideal.Quotient.liftₐ (chartIdeal V i) (aeval fun p => ↑(hu p.1).unit⁻¹ * θ (X p)) (by
    intro a ha
    have h : chartIdeal V i ≤
        RingHom.ker (aeval fun p => ↑(hu p.1).unit⁻¹ * θ (X p) : MRingOver F ι →ₐ[F] B) := by
      refine sup_le (fun g hg => ?_) (Ideal.span_le.mpr ?_)
      · have := aeval_blockScale_eq_zero hV (fun k => ↑(hu k).unit⁻¹) θ hθ hg
        exact RingHom.mem_ker.mpr this
      rintro _ ⟨k, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, aeval_X, IsUnit.val_inv_mul, sub_self]
    exact RingHom.mem_ker.mp (h ha))

end General

section Embed

variable {F : Type} [Field F] {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
  [∀ k, Fintype (ι k)] [∀ k', Fintype (ι' k')] {e : K' ≃ K} {A : ∀ k', ι' k' → ι (e k') → F}

/- English proof (translation)
Unfold `blockLinSubst`. Conclude with `aeval_X _ _`.
-/
theorem blockLinSubst_X (q : Σ k', ι' k') :
    blockLinSubst e A (X q) = ∑ i, C (A q.1 q.2 i) * X ⟨e q.1, i⟩ := by
  unfold blockLinSubst
  exact aeval_X _ _

open Classical in
/- English proof (translation)
Rewrite using `[blockLinSubst_X]`. Use `isMultiHomog_sum _ _ fun i _ => ?_` and prove the remaining obligations. Simplify using `using isMultiHomog_mul (isMultiHomog_C (ι := ι) (A q.1 q.2 i)) (isMultiHomog_X (e q.1) i)`.
-/
theorem isMultiHomog_blockLinSubst_X (q : Σ k', ι' k') :
    IsMultiHomog (blockLinSubst e A (X q)) (Pi.single (e q.1) 1) := by
  rw [blockLinSubst_X]
  refine isMultiHomog_sum _ _ fun i _ => ?_
  simpa using isMultiHomog_mul (isMultiHomog_C (ι := ι) (A q.1 q.2 i)) (isMultiHomog_X (e q.1) i)

open Classical in

/- English proof (translation)
Establish `hg : ∀ q : Σ k', ι' k', IsMultiHomog (∑ i, C (A q.1 q.2 i) * X ⟨e q.1, i⟩ : MRingOver F ι) (Pi.single (e q.1) 1)` using `fun q => by`. Rewrite using `[← blockLinSubst_X]`. Conclude with `isMultiHomog_blockLinSubst_X q`. Unfold `blockLinSubst`. Conclude with `isMultiHomog_aeval e _ hg hs`.
-/
theorem isMultiHomog_blockLinSubst {s : MRingOver F ι'} {a : K' → ℕ} (hs : IsMultiHomog s a) :
    IsMultiHomog (blockLinSubst e A s) (a ∘ e.symm) := by
  have hg : ∀ q : Σ k', ι' k', IsMultiHomog (∑ i, C (A q.1 q.2 i) * X ⟨e q.1, i⟩ : MRingOver F ι)
      (Pi.single (e q.1) 1) := fun q => by
    rw [← blockLinSubst_X]
    exact isMultiHomog_blockLinSubst_X q
  unfold blockLinSubst
  exact isMultiHomog_aeval e _ hg hs

variable (hA : ∀ k', Function.Injective (Matrix.of (A k')).mulVec)
include hA

/- English proof (translation)
Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective (Matrix.toLin' (Matrix.of (A k'))) (LinearMap.ker_eq_bot.mpr fun x y h => hA k' (by simpa [Matrix.toLin'_apply] using h))`. Establish `hBA' : LinearMap.toMatrix' g * Matrix.of (A k') = 1`. Rewrite using `[← LinearMap.toMatrix'_toLin' (Matrix.of (A k')), ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]`. Choose the witnesses or unpack the hypotheses as in `⟨B, hij⟩ : ∃ B : ι (e k') → ι' k' → F, ∀ j, ∑ q, B i q * A k' q j = if i = j then 1 else 0 := by`. Use `⟨fun i q => LinearMap.toMatrix' g i q, fun j => ?_⟩` and prove the remaining obligations.

Use `congrFun (congrFun hBA' i) j` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, Matrix.one_apply]`. Use `⟨fun q => B i q, ?_⟩` and prove the remaining obligations. Simplify using `only [map_sum, map_mul, algHom_C, MvPolynomial.algebraMap_eq]`. Repeatedly rewrite using `[blockLinSubst_X, Finset.mul_sum, ← mul_assoc, ← C_mul]`.

Combine the equalities or inequalities in the displayed calculation. Repeatedly rewrite using `[map_sum, Finset.sum_mul]`. Use `_ = X ⟨e k', i⟩ := by`. Repeatedly rewrite using `[hij]`. Simplify using the standard rewrite rules.
-/
theorem exists_linear_preimage (k' : K') (i : ι (e k')) :
    ∃ c : ι' k' → F, blockLinSubst e A (∑ q, C (c q) * X ⟨k', q⟩) = X ⟨e k', i⟩ := by
  classical
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' (Matrix.of (A k')))
    (LinearMap.ker_eq_bot.mpr fun x y h => hA k' (by simpa [Matrix.toLin'_apply] using h))
  have hBA' : LinearMap.toMatrix' g * Matrix.of (A k') = 1 := by
    rw [← LinearMap.toMatrix'_toLin' (Matrix.of (A k')), ← LinearMap.toMatrix'_comp, hg,
      LinearMap.toMatrix'_id]
  obtain ⟨B, hij⟩ : ∃ B : ι (e k') → ι' k' → F,
      ∀ j, ∑ q, B i q * A k' q j = if i = j then 1 else 0 := by
    refine ⟨fun i q => LinearMap.toMatrix' g i q, fun j => ?_⟩
    have := congrFun (congrFun hBA' i) j
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  refine ⟨fun q => B i q, ?_⟩
  simp only [map_sum, map_mul, algHom_C, MvPolynomial.algebraMap_eq]
  simp_rw [blockLinSubst_X, Finset.mul_sum, ← mul_assoc, ← C_mul]
  calc (∑ q : ι' k', ∑ j : ι (e k'), C (B i q * A k' q j) * (X ⟨e k', j⟩ : MRingOver F ι))
      = ∑ j : ι (e k'), ∑ q : ι' k', C (B i q * A k' q j) * (X ⟨e k', j⟩ : MRingOver F ι) :=
        Finset.sum_comm
    _ = ∑ j : ι (e k'), C (∑ q, B i q * A k' q j) * (X ⟨e k', j⟩ : MRingOver F ι) := by
        simp_rw [map_sum, Finset.sum_mul]
    _ = X ⟨e k', i⟩ := by
        simp_rw [hij]
        simp

open Classical in
/- English proof (translation)
Take `⟨k, i⟩` from `p`. Take `⟨k', rfl⟩` from `e.surjective k`. Take `⟨c, hc⟩` from `exists_linear_preimage hA k' i`. Use `⟨_, ?_, hc⟩` and prove the remaining obligations. Use `show IsMultiHomog _ (Pi.single (e.symm (e k')) 1)`.

Rewrite using `[Equiv.symm_apply_apply]`. Conclude with `isMultiHomog_sum _ _ fun q _ => by`. Simplify using `using isMultiHomog_mul (isMultiHomog_C (ι := ι') (c q)) (isMultiHomog_X k' q)`.
-/
theorem exists_pre (p : Σ k, ι k) :
    ∃ g : MRingOver F ι', IsMultiHomog g (Pi.single (e.symm p.1) 1) ∧ blockLinSubst e A g = X p := by
  obtain ⟨k, i⟩ := p
  obtain ⟨k', rfl⟩ := e.surjective k
  obtain ⟨c, hc⟩ := exists_linear_preimage hA k' i
  refine ⟨_, ?_, hc⟩
  show IsMultiHomog _ (Pi.single (e.symm (e k')) 1)
  rw [Equiv.symm_apply_apply]
  exact isMultiHomog_sum _ _ fun q _ => by
    simpa using isMultiHomog_mul (isMultiHomog_C (ι := ι') (c q)) (isMultiHomog_X k' q)

open Classical in

def sect : MRingOver F ι →ₐ[F] MRingOver F ι' :=
  aeval fun p => (exists_pre hA p).choose

open Classical in
/- English proof (translation)
Establish `h : (blockLinSubst e A).comp (sect hA) = AlgHom.id F _` using `algHom_ext fun p => by`. Simplify using `only [AlgHom.comp_apply, AlgHom.id_apply, sect, aeval_X]`. Conclude with `(exists_pre hA p).choose_spec.2`. Conclude with `AlgHom.congr_fun h s`.
-/
theorem blockLinSubst_sect (s : MRingOver F ι) : blockLinSubst e A (sect hA s) = s := by
  have h : (blockLinSubst e A).comp (sect hA) = AlgHom.id F _ := algHom_ext fun p => by
    simp only [AlgHom.comp_apply, AlgHom.id_apply, sect, aeval_X]
    exact (exists_pre hA p).choose_spec.2
  exact AlgHom.congr_fun h s

/- English proof (translation)
Introduce `s` and use `⟨sect hA s, blockLinSubst_sect hA s⟩`.
-/
theorem surj : Function.Surjective (blockLinSubst e A) :=
  fun s => ⟨sect hA s, blockLinSubst_sect hA s⟩

open Classical in
/- English proof (translation)
Establish `h` using `isMultiHomog_aeval e.symm (fun p => (exists_pre hA p).choose) (fun p => (exists_pre hA p).choose_spec.1) hs`. Rewrite `h` using `[Equiv.symm_symm]`. Conclude with `h`.
-/
theorem isMultiHomog_sect {s : MRingOver F ι} {a : K → ℕ} (hs : IsMultiHomog s a) :
    IsMultiHomog (sect hA s) (a ∘ e) := by
  have h := isMultiHomog_aeval e.symm (fun p => (exists_pre hA p).choose)
    (fun p => (exists_pre hA p).choose_spec.1) hs
  rw [Equiv.symm_symm] at h
  exact h

open Classical in

/- English proof (translation)
Use `set J := Ideal.span (Set.range fun q => (X q : MRingOver F ι') - sect hA (blockLinSubst e A (X q)))`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `g hg`. Establish `hJ : g - sect hA (blockLinSubst e A g) ∈ J`. Rewrite using `[← Ideal.Quotient.eq]`.

Establish `h : (Ideal.Quotient.mkₐ F J).comp ((sect hA).comp (blockLinSubst e A)) = Ideal.Quotient.mkₐ F J` using `algHom_ext fun q => by`. Simplify using `only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]`. Rewrite using `[Ideal.Quotient.eq, ← neg_sub, neg_mem_iff]`. Conclude with `Ideal.subset_span ⟨q, rfl⟩`. Conclude with `(AlgHom.congr_fun h g).symm`.

Establish `hg' : g = (g - sect hA (blockLinSubst e A g)) + sect hA (blockLinSubst e A g)` using `by ring`. Rewrite using `[hg']`. Conclude with `Ideal.add_mem _ (Ideal.mem_sup_left hJ) (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hg))`. Use `sup_le (Ideal.span_le.mpr ?_) (Ideal.map_le_iff_le_comap.mpr fun v hv => ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨q, rfl⟩`.

Simplify using `[blockLinSubst_sect]`. Simplify using `[Ideal.mem_comap, blockLinSubst_sect, hv]`.
-/
theorem comap_eq (V : Ideal (MRingOver F ι)) :
    V.comap (blockLinSubst e A).toRingHom =
      Ideal.span (Set.range fun q => (X q : MRingOver F ι') - sect hA (blockLinSubst e A (X q))) ⊔
        V.map (sect hA) := by
  set J := Ideal.span (Set.range fun q => (X q : MRingOver F ι') - sect hA (blockLinSubst e A (X q)))
  apply le_antisymm
  · intro g hg
    have hJ : g - sect hA (blockLinSubst e A g) ∈ J := by
      rw [← Ideal.Quotient.eq]
      have h : (Ideal.Quotient.mkₐ F J).comp ((sect hA).comp (blockLinSubst e A)) =
          Ideal.Quotient.mkₐ F J := algHom_ext fun q => by
        simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
        rw [Ideal.Quotient.eq, ← neg_sub, neg_mem_iff]
        exact Ideal.subset_span ⟨q, rfl⟩
      exact (AlgHom.congr_fun h g).symm
    have hg' : g = (g - sect hA (blockLinSubst e A g)) + sect hA (blockLinSubst e A g) := by ring
    rw [hg']
    exact Ideal.add_mem _ (Ideal.mem_sup_left hJ) (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hg))
  · refine sup_le (Ideal.span_le.mpr ?_) (Ideal.map_le_iff_le_comap.mpr fun v hv => ?_)
    · rintro _ ⟨q, rfl⟩
      simp [blockLinSubst_sect]
    · simp [Ideal.mem_comap, blockLinSubst_sect, hv]

open Classical in
/- English proof (translation)
Take `⟨S, hS, rfl⟩` from `hV`. Use `⟨Set.range (fun q => (X q : MRingOver F ι') - sect hA (blockLinSubst e A (X q))) ∪ sect hA '' S, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `f (⟨q, rfl⟩ | ⟨s, hs, rfl⟩)`. Use `⟨Pi.single q.1 1, isMultiHomog_sub (isMultiHomog_X (F := F) q.1 q.2) ?_⟩` and prove the remaining obligations. Establish `h2` using `isMultiHomog_sect hA (isMultiHomog_blockLinSubst_X (A := A) q)`.

Establish `hd : ((Pi.single (e q.1) 1 : K → ℕ) ∘ e) = Pi.single q.1 1`. Use function extensionality and compare the values at `k'`. Simplify using `only [Function.comp_apply, Pi.single_apply, e.apply_eq_iff_eq]`. Rewrite `h2` using `[hd]`. Then use the resulting hypothesis. Take `⟨a, ha⟩` from `hS s hs`.

Conclude with `⟨a ∘ e, isMultiHomog_sect hA ha⟩`. Rewrite using `[comap_eq hA, Ideal.map_span, Ideal.span_union]`.
-/
theorem isMultiHomogIdeal_comap {V : Ideal (MRingOver F ι)} (hV : IsMultiHomogIdeal V) :
    IsMultiHomogIdeal (V.comap (blockLinSubst e A).toRingHom) := by
  obtain ⟨S, hS, rfl⟩ := hV
  refine ⟨Set.range (fun q => (X q : MRingOver F ι') - sect hA (blockLinSubst e A (X q))) ∪
    sect hA '' S, ?_, ?_⟩
  · rintro f (⟨q, rfl⟩ | ⟨s, hs, rfl⟩)
    · refine ⟨Pi.single q.1 1, isMultiHomog_sub (isMultiHomog_X (F := F) q.1 q.2) ?_⟩
      have h2 := isMultiHomog_sect hA (isMultiHomog_blockLinSubst_X (A := A) q)
      have hd : ((Pi.single (e q.1) 1 : K → ℕ) ∘ e) = Pi.single q.1 1 := by
        funext k'
        simp only [Function.comp_apply, Pi.single_apply, e.apply_eq_iff_eq]
      rwa [hd] at h2
    · obtain ⟨a, ha⟩ := hS s hs
      exact ⟨a ∘ e, isMultiHomog_sect hA ha⟩
  · rw [comap_eq hA, Ideal.map_span, Ideal.span_union]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h k`. Take `⟨k', rfl⟩` from `e.surjective k`. Take `⟨q, hq⟩` from `h k'`. Assume the negation of the conclusion as `hall`.

Use `push Not at hall`. Apply `hq` to reduce the goal to its premises. Rewrite using `[Ideal.mem_comap]`. Simplify using `only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, blockLinSubst_X]`. Conclude with `Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hall i)`.

Introduce `h k'`. Take `⟨i, hi⟩` from `h (e k')`. Assume the negation of the conclusion as `hall`. Use `push Not at hall`. Take `⟨c, hc⟩` from `exists_linear_preimage hA k' i`.

Apply `hi` to reduce the goal to its premises. Rewrite using `[← hc, map_sum]`. Conclude with `Ideal.sum_mem _ fun q _ => by`. Rewrite using `[map_mul]`. Conclude with `Ideal.mul_mem_left _ _ (hall q)`.
-/
theorem isRelevant_comap_iff (W : Ideal (MRingOver F ι)) :
    IsRelevant (W.comap (blockLinSubst e A).toRingHom) ↔ IsRelevant W := by
  constructor
  · intro h k
    obtain ⟨k', rfl⟩ := e.surjective k
    obtain ⟨q, hq⟩ := h k'
    by_contra hall
    push Not at hall
    apply hq
    rw [Ideal.mem_comap]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, blockLinSubst_X]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hall i)
  · intro h k'
    obtain ⟨i, hi⟩ := h (e k')
    by_contra hall
    push Not at hall
    obtain ⟨c, hc⟩ := exists_linear_preimage hA k' i
    apply hi
    rw [← hc, map_sum]
    exact Ideal.sum_mem _ fun q _ => by
      rw [map_mul]
      exact Ideal.mul_mem_left _ _ (hall q)

def quotEquiv (J : Ideal (MRingOver F ι)) :
    (MRingOver F ι' ⧸ J.comap (blockLinSubst e A).toRingHom) ≃ₐ[F] (MRingOver F ι ⧸ J) :=
  (Ideal.quotientEquivAlgOfEq F (by
    ext x
    simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem])).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := (Ideal.Quotient.mkₐ F J).comp (blockLinSubst e A))
      (Ideal.Quotient.mkₐ_surjective F J |>.comp (surj hA)))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem quotEquiv_mk (J : Ideal (MRingOver F ι)) (x : MRingOver F ι') :
    quotEquiv hA J (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk J (blockLinSubst e A x) :=
  rfl

/- English proof (translation)
Take `⟨⟨hp, hh, hr⟩, hdim⟩` from `hV`. Use `⟨⟨(by have := hp; exact Ideal.comap_isPrime _ _), isMultiHomogIdeal_comap hA hh, (isRelevant_comap_iff hA V).mpr hr⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[ringKrullDim_eq_of_ringEquiv (quotEquiv hA V).toRingEquiv, hdim, Fintype.card_congr e]`.
-/
theorem isProjVarF_comap {V : Ideal (MRingOver F ι)} {d : ℕ} (hV : IsProjVarF V d) :
    IsProjVarF (V.comap (blockLinSubst e A).toRingHom) d := by
  obtain ⟨⟨hp, hh, hr⟩, hdim⟩ := hV
  refine ⟨⟨(by have := hp; exact Ideal.comap_isPrime _ _), isMultiHomogIdeal_comap hA hh,
    (isRelevant_comap_iff hA V).mpr hr⟩, ?_⟩
  rw [ringKrullDim_eq_of_ringEquiv (quotEquiv hA V).toRingEquiv, hdim, Fintype.card_congr e]

/- English proof (translation)
Establish `hs : Function.Surjective (blockLinSubst e A).toRingHom` using `surj hA`. Establish `h : V ⊔ Ideal.span {blockLinSubst e A f} = (V.comap (blockLinSubst e A).toRingHom ⊔ Ideal.span {f}).map (blockLinSubst e A).toRingHom`. Rewrite using `[Ideal.map_sup, Ideal.map_comap_of_surjective _ hs, Ideal.map_span, Set.image_singleton]`. Both sides reduce to the same expression. Rewrite using `[h, Ideal.comap_map_of_surjective _ hs]`.

Conclude with `(sup_eq_left.mpr (le_trans (Ideal.comap_mono bot_le) le_sup_left)).symm`.
-/
theorem comap_sup_span (V : Ideal (MRingOver F ι)) (f : MRingOver F ι') :
    V.comap (blockLinSubst e A).toRingHom ⊔ Ideal.span {f} =
      (V ⊔ Ideal.span {blockLinSubst e A f}).comap (blockLinSubst e A).toRingHom := by
  have hs : Function.Surjective (blockLinSubst e A).toRingHom := surj hA
  have h : V ⊔ Ideal.span {blockLinSubst e A f} =
      (V.comap (blockLinSubst e A).toRingHom ⊔ Ideal.span {f}).map (blockLinSubst e A).toRingHom := by
    rw [Ideal.map_sup, Ideal.map_comap_of_surjective _ hs, Ideal.map_span, Set.image_singleton]
    rfl
  rw [h, Ideal.comap_map_of_surjective _ hs]
  exact (sup_eq_left.mpr (le_trans (Ideal.comap_mono bot_le) le_sup_left)).symm

/- English proof (translation)
Establish `hW' : (W.comap (blockLinSubst e A).toRingHom).IsPrime` using `Ideal.comap_isPrime _ _`. Unfold `multAt`. Rewrite using `[dif_pos hW', dif_pos hW]`. Use `congr 1`. Use `GroundTheory.Heights₂.Heights.NumbersDVR.length_localizedModule_eq_of_surjective (blockLinSubst e A).toRingHom (surj hA) W _ rfl _ _ (quotEquiv hA J).toRingEquiv.toAddEquiv fun s x => ?_` and prove the remaining obligations.

Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Express the relevant statement in the definitionally equal form `quotEquiv hA J (Ideal.Quotient.mk _ (s * y)) = Ideal.Quotient.mk J (blockLinSubst e A s) * quotEquiv hA J (Ideal.Quotient.mk _ y)`. Rewrite using `[quotEquiv_mk, quotEquiv_mk, map_mul, map_mul]`.
-/
theorem multAt_comap (J W : Ideal (MRingOver F ι)) [hW : W.IsPrime] :
    multAt (J.comap (blockLinSubst e A).toRingHom) (W.comap (blockLinSubst e A).toRingHom) =
      multAt J W := by
  have hW' : (W.comap (blockLinSubst e A).toRingHom).IsPrime := Ideal.comap_isPrime _ _
  unfold multAt
  rw [dif_pos hW', dif_pos hW]
  congr 1
  refine GroundTheory.Heights₂.Heights.NumbersDVR.length_localizedModule_eq_of_surjective
    (blockLinSubst e A).toRingHom (surj hA) W _ rfl _ _ (quotEquiv hA J).toRingEquiv.toAddEquiv
    fun s x => ?_
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  change quotEquiv hA J (Ideal.Quotient.mk _ (s * y)) =
    Ideal.Quotient.mk J (blockLinSubst e A s) * quotEquiv hA J (Ideal.Quotient.mk _ y)
  rw [quotEquiv_mk, quotEquiv_mk, map_mul, map_mul]

/- English proof (translation)
The claim follows from `Ideal.comap_injective_of_surjective _ (surj hA)`.
-/
theorem comap_injective :
    Function.Injective (Ideal.comap (blockLinSubst e A).toRingHom :
      Ideal (MRingOver F ι) → Ideal (MRingOver F ι')) :=
  Ideal.comap_injective_of_surjective _ (surj hA)

/- English proof (translation)
Simplify using `only [divSupp, Set.mem_ofPred_eq, comap_sup_span hA, Ideal.comap_minimalPrimes_eq_of_surjective (surj hA), isRelevant_comap_iff hA, (comap_injective hA).mem_set_image]`.
-/
theorem mem_divSupp_comap_iff (V W : Ideal (MRingOver F ι)) (f : MRingOver F ι') :
    W.comap (blockLinSubst e A).toRingHom ∈ divSupp (V.comap (blockLinSubst e A).toRingHom) f ↔
      W ∈ divSupp V (blockLinSubst e A f) := by
  simp only [divSupp, Set.mem_ofPred_eq, comap_sup_span hA,
    Ideal.comap_minimalPrimes_eq_of_surjective (surj hA), isRelevant_comap_iff hA,
    (comap_injective hA).mem_set_image]

/- English proof (translation)
Use extensionality with `W'`. Distinguish the cases in `hW : W' ∈ Set.range (Ideal.comap (blockLinSubst e A).toRingHom)`. Take `⟨W, rfl⟩` from `hW`. Rewrite using `[Finsupp.mapDomain_apply (comap_injective hA)]`. Distinguish the cases in `hs : W ∈ divSupp V (blockLinSubst e A f)`.

Rewrite using `[DivisorCycleSwap.divCycle_apply_of_mem hs, DivisorCycleSwap.divCycle_apply_of_mem ((mem_divSupp_comap_iff hA V W f).mpr hs), comap_sup_span hA]`. Establish `: W.IsPrime` using `hs.1.1.1`. Conclude with `multAt_comap hA _ _`. Rewrite using `[DivisorCycleSwap.divCycle_apply_of_not_mem hs, DivisorCycleSwap.divCycle_apply_of_not_mem (mt (mem_divSupp_comap_iff hA V W f).mp hs)]`. Rewrite using `[Finsupp.mapDomain_of_notMem_range _ _ hW, DivisorCycleSwap.divCycle_apply_of_not_mem]`.

Introduce `h`. Apply `hW` to reduce the goal to its premises. Establish `h1` using `h.1`. Rewrite `h1` using `[comap_sup_span hA, Ideal.comap_minimalPrimes_eq_of_surjective (surj hA)]`. Take `⟨W, -, rfl⟩` from `h1`.

Conclude with `⟨W, rfl⟩`.
-/
theorem divCycle_comap (V : Ideal (MRingOver F ι)) (f : MRingOver F ι') :
    divCycle (V.comap (blockLinSubst e A).toRingHom) f =
      Finsupp.mapDomain (Ideal.comap (blockLinSubst e A).toRingHom) (divCycle V (blockLinSubst e A f)) := by
  ext W'
  by_cases hW : W' ∈ Set.range (Ideal.comap (blockLinSubst e A).toRingHom)
  · obtain ⟨W, rfl⟩ := hW
    rw [Finsupp.mapDomain_apply (comap_injective hA)]
    by_cases hs : W ∈ divSupp V (blockLinSubst e A f)
    · rw [DivisorCycleSwap.divCycle_apply_of_mem hs, DivisorCycleSwap.divCycle_apply_of_mem ((mem_divSupp_comap_iff hA V W f).mpr hs),
        comap_sup_span hA]
      have : W.IsPrime := hs.1.1.1
      exact multAt_comap hA _ _
    · rw [DivisorCycleSwap.divCycle_apply_of_not_mem hs,
        DivisorCycleSwap.divCycle_apply_of_not_mem (mt (mem_divSupp_comap_iff hA V W f).mp hs)]
  · rw [Finsupp.mapDomain_of_notMem_range _ _ hW, DivisorCycleSwap.divCycle_apply_of_not_mem]
    intro h
    apply hW
    have h1 := h.1
    rw [comap_sup_span hA, Ideal.comap_minimalPrimes_eq_of_surjective (surj hA)] at h1
    obtain ⟨W, -, rfl⟩ := h1
    exact ⟨W, rfl⟩

/- English proof (translation)
Use extensionality with `W'`. Distinguish the cases in `hW : W' ∈ Set.range (Ideal.comap (blockLinSubst e A).toRingHom)`. Take `⟨W, rfl⟩` from `hW`. Simplify using `only [ratDiv, Finsupp.coe_sub, Pi.sub_apply, Finsupp.mapRange_apply, divCycle_comap hA, Finsupp.mapDomain_apply (comap_injective hA)]`. Simplify using `only [ratDiv, Finsupp.coe_sub, Pi.sub_apply, Finsupp.mapRange_apply, divCycle_comap hA, Finsupp.mapDomain_of_notMem_range _ _ hW, Nat.cast_zero, sub_zero]`.
-/
theorem ratDiv_comap (V : Ideal (MRingOver F ι)) (f g : MRingOver F ι') :
    ratDiv (V.comap (blockLinSubst e A).toRingHom) f g =
      Finsupp.mapDomain (Ideal.comap (blockLinSubst e A).toRingHom)
        (ratDiv V (blockLinSubst e A f) (blockLinSubst e A g)) := by
  ext W'
  by_cases hW : W' ∈ Set.range (Ideal.comap (blockLinSubst e A).toRingHom)
  · obtain ⟨W, rfl⟩ := hW
    simp only [ratDiv, Finsupp.coe_sub, Pi.sub_apply, Finsupp.mapRange_apply, divCycle_comap hA,
      Finsupp.mapDomain_apply (comap_injective hA)]
  · simp only [ratDiv, Finsupp.coe_sub, Pi.sub_apply, Finsupp.mapRange_apply, divCycle_comap hA,
      Finsupp.mapDomain_of_notMem_range _ _ hW, Nat.cast_zero, sub_zero]

/- English proof (translation)
Establish `hV' : IsProjVarF (V.comap (blockLinSubst e A).toRingHom) 0` using `isProjVarF_comap hA hV`. Set `θ : MRingOver F ι' →ₐ[F] MRingOver F ι ⧸ chartIdeal V i` to `(Ideal.Quotient.mkₐ F (chartIdeal V i)).comp (blockLinSubst e A)`. Set `θ' : MRingOver F ι →ₐ[F] MRingOver F ι' ⧸ chartIdeal (V.comap (blockLinSubst e A).toRingHom) i'` to `(Ideal.Quotient.mkₐ F (chartIdeal (V.comap (blockLinSubst e A).toRingHom) i')).comp (sect hA)`. Establish `hθ : ∀ g ∈ V.comap (blockLinSubst e A).toRingHom, θ g = 0` using `fun g hg => Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left hg)`. Establish `hθ' : ∀ g ∈ V, θ' g = 0` using `fun g hg => by`.

Use `Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left ?_)` and prove the remaining obligations. Rewrite using `[Ideal.mem_comap]`. Simplify `hg` using `[blockLinSubst_sect]`. Establish `hu : ∀ k', IsUnit (θ (X ⟨k', i' k'⟩))` using `fun k' => isUnit_mk_chartIdeal_form hV i (isMultiHomog_blockLinSubst_X _) (hi' k')`. Establish `hw : ∀ k, IsUnit (θ' (X ⟨k, i k⟩))` using `fun k => isUnit_mk_chartIdeal_form hV' i' (isMultiHomog_sect hA (isMultiHomog_X k (i k))) (by`.

Rewrite using `[Ideal.mem_comap]`. Simplify `hi k)` using `[blockLinSubst_sect]`. Set `α` to `linChartMap hV'.1.2.1 i' θ hθ hu`. Set `β` to `linChartMap hV.1.2.1 i θ' hθ' hw`. Establish `hF` using `chart_isField hV hi`.

Establish `hF'` using `chart_isField hV' hi'`. Establish `: Nontrivial (MRingOver F ι ⧸ chartIdeal V i)` using `⟨hF.exists_pair_ne⟩`. Establish `: Nontrivial (MRingOver F ι' ⧸ chartIdeal (V.comap (blockLinSubst e A).toRingHom) i')` using `⟨hF'.exists_pair_ne⟩`. Use `chart_finite hV hi` as an intermediate fact. Use `chart_finite hV' hi'` as an intermediate fact.

Conclude with `le_antisymm (LinearMap.finrank_le_finrank_of_injective (f := α.toLinearMap) (injective_of_isField hF' α.toRingHom)) (LinearMap.finrank_le_finrank_of_injective (f := β.toLinearMap) (injective_of_isField hF β.toRingHom))`.
-/
theorem ptDeg_comap {V : Ideal (MRingOver F ι)} (hV : IsProjVarF V 0) {i : ∀ k, ι k}
    (hi : IsChart V i) {i' : ∀ k', ι' k'} (hi' : IsChart (V.comap (blockLinSubst e A).toRingHom) i') :
    ptDeg (V.comap (blockLinSubst e A).toRingHom) i' = ptDeg V i := by
  have hV' : IsProjVarF (V.comap (blockLinSubst e A).toRingHom) 0 := isProjVarF_comap hA hV
  let θ : MRingOver F ι' →ₐ[F] MRingOver F ι ⧸ chartIdeal V i :=
    (Ideal.Quotient.mkₐ F (chartIdeal V i)).comp (blockLinSubst e A)
  let θ' : MRingOver F ι →ₐ[F] MRingOver F ι' ⧸ chartIdeal (V.comap (blockLinSubst e A).toRingHom) i' :=
    (Ideal.Quotient.mkₐ F (chartIdeal (V.comap (blockLinSubst e A).toRingHom) i')).comp (sect hA)
  have hθ : ∀ g ∈ V.comap (blockLinSubst e A).toRingHom, θ g = 0 := fun g hg =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left hg)
  have hθ' : ∀ g ∈ V, θ' g = 0 := fun g hg => by
    refine Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left ?_)
    rw [Ideal.mem_comap]
    simpa [blockLinSubst_sect] using hg
  have hu : ∀ k', IsUnit (θ (X ⟨k', i' k'⟩)) :=
    fun k' => isUnit_mk_chartIdeal_form hV i (isMultiHomog_blockLinSubst_X _) (hi' k')
  have hw : ∀ k, IsUnit (θ' (X ⟨k, i k⟩)) := fun k =>
    isUnit_mk_chartIdeal_form hV' i' (isMultiHomog_sect hA (isMultiHomog_X k (i k))) (by
      rw [Ideal.mem_comap]
      simpa [blockLinSubst_sect] using hi k)
  let α := linChartMap hV'.1.2.1 i' θ hθ hu
  let β := linChartMap hV.1.2.1 i θ' hθ' hw
  have hF := chart_isField hV hi
  have hF' := chart_isField hV' hi'
  have : Nontrivial (MRingOver F ι ⧸ chartIdeal V i) := ⟨hF.exists_pair_ne⟩
  have : Nontrivial (MRingOver F ι' ⧸ chartIdeal (V.comap (blockLinSubst e A).toRingHom) i') :=
    ⟨hF'.exists_pair_ne⟩
  have := chart_finite hV hi
  have := chart_finite hV' hi'
  exact le_antisymm
    (LinearMap.finrank_le_finrank_of_injective (f := α.toLinearMap)
      (injective_of_isField hF' α.toRingHom))
    (LinearMap.finrank_le_finrank_of_injective (f := β.toLinearMap)
      (injective_of_isField hF β.toRingHom))

end Embed

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.LinEmbed
