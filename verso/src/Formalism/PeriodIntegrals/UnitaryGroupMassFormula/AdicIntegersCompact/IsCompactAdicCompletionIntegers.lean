import Mathlib
import Formalism.LocalToGlobal.AdelicCompactOpens.IntAdelesCompactOpen

namespace PI.IntAdCpctOpenWork

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Establish `h1 : IsOpen {z : v.adicCompletion F | Valued.v z < 1}`. Use `Valued.isOpen_ball (v.adicCompletion F) 1` as an intermediate fact. Simplify `this` using `only [Valuation.restrict_lt_one_iff]`. Conclude with `h1.preimage (continuous_id.sub continuous_const)`.
-/
theorem isOpen_lt_one (x : v.adicCompletion F) :
    IsOpen {y : v.adicCompletion F | Valued.v (y - x) < 1} := by
  have h1 : IsOpen {z : v.adicCompletion F | Valued.v z < 1} := by
    have := Valued.isOpen_ball (v.adicCompletion F) 1
    simpa only [Valuation.restrict_lt_one_iff] using this
  exact h1.preimage (continuous_id.sub continuous_const)

/- English proof (translation)
Use `first`. Consider the case `exact valuedAdicCompletion_eq_valuation' v k`. Consider the case `rfl`.
-/
theorem valued_algebraMap (k : F) :
    Valued.v (algebraMap F (v.adicCompletion F) k) = v.valuation F k := by
  first
  | exact valuedAdicCompletion_eq_valuation' v k
  | rfl

/- English proof (translation)
Conclude with `denseRange_algebraMap F v`.
-/
theorem denseRange : DenseRange (algebraMap F (v.adicCompletion F)) := by
  exact denseRange_algebraMap F v

/- English proof (translation)
Take `⟨k, hk⟩ : ∃ k : F, algebraMap F (v.adicCompletion F) k ∈ {y : v.adicCompletion F | Valued.v (y - x) < 1}` from `(denseRange v).exists_mem_open (isOpen_lt_one v x) ⟨x, by simp⟩`. Simplify using `only [Set.mem_setOf_eq] at hk`. Establish `hk1 : v.valuation F k ≤ 1`. Rewrite using `[← valued_algebraMap]`. Establish `e : algebraMap F (v.adicCompletion F) k = (algebraMap F (v.adicCompletion F) k - x) + x` using `by ring`.

Rewrite using `[e]`. Conclude with `Valuation.map_add_le _ hk.le hx`. Choose the witnesses or unpack the hypotheses as in `⟨r, s, hs, hrs⟩ : ∃ r s : 𝓞 F, s ∉ v.asIdeal ∧ algebraMap (𝓞 F) F s * k = algebraMap (𝓞 F) F r := by`. Establish `hmem : k ∈ valuationSubringAtPrime F v`. Rewrite using `[valuationSubringAtPrime_eq_valuationSubring]`.

Conclude with `(Valuation.mem_valuationSubring_iff _ _).mpr hk1`. Take `⟨⟨r, s⟩, h⟩` from `IsLocalization.surj v.asIdeal.primeCompl (⟨k, hmem⟩ : valuationSubringAtPrime F v)`. Use `⟨r, s, s.2, ?_⟩` and prove the remaining obligations. Establish `e : ∀ y : 𝓞 F, ((algebraMap (𝓞 F) (valuationSubringAtPrime F v) y : valuationSubringAtPrime F v) : F) = algebraMap (𝓞 F) F y`. Introduce `y`.

Use `first`. Consider the case `rfl`. Consider the case `simp`. Consider the case `exact (IsScalarTower.algebraMap_apply (𝓞 F) (valuationSubringAtPrime F v) F y).symm`. Establish `h'` using `congrArg Subtype.val h`.

Establish `h'' : k * ((algebraMap (𝓞 F) (valuationSubringAtPrime F v) s : valuationSubringAtPrime F v) : F) = ((algebraMap (𝓞 F) (valuationSubringAtPrime F v) r : valuationSubringAtPrime F v) : F)`. Simplify using `using h'`. Rewrite `h''` using `[e, e]`. Rewrite using `[mul_comm]`. Conclude with `h''`.

Take `⟨t, ht⟩ : ∃ t : 𝓞 F, s * t - 1 ∈ v.asIdeal` from `by haveI := v.isMaximal`. Establish `hs0 : (Ideal.Quotient.mk v.asIdeal s) ≠ 0`. Rewrite using `[Ne, Ideal.Quotient.eq_zero_iff_mem]` and apply the resulting hypothesis. Take `⟨b, hb⟩` from `Ideal.Quotient.exists_inv hs0`. Take `⟨t, rfl⟩` from `Ideal.Quotient.mk_surjective b`.

Use `⟨t, ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hb, map_one, sub_self]`. Use `⟨r * t, ?_⟩` and prove the remaining obligations. Establish `hkrt : v.valuation F (k - algebraMap (𝓞 F) F (r * t)) < 1`. Establish `e : k - algebraMap (𝓞 F) F (r * t) = k * (1 - algebraMap (𝓞 F) F (s * t))`.

Rewrite using `[map_mul, map_mul, ← hrs]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, map_mul]`. Establish `h1 : v.valuation F (1 - algebraMap (𝓞 F) F (s * t)) < 1`. Establish `e1 : (1 : F) - algebraMap (𝓞 F) F (s * t) = algebraMap (𝓞 F) F (-(s * t - 1))`.

Rewrite using `[map_neg, map_sub, map_one]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, valuation_lt_one_iff_mem]`. Conclude with `v.asIdeal.neg_mem_iff.mpr ht`. Combine the equalities or inequalities in the displayed calculation.

Consider the case `exact mul_le_mul_of_nonneg_right hk1 zero_le'`. Consider the case `gcongr`. Use `_ < 1 := by rw [one_mul]; exact h1`. Establish `e2 : x - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (r * t)) = (x - algebraMap F (v.adicCompletion F) k) + algebraMap F (v.adicCompletion F) (k - algebraMap (𝓞 F) F (r * t))`. Rewrite using `[map_sub]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2]`. Apply `Valuation.map_add_lt` to reduce the goal to its premises. Rewrite using `[Valuation.map_sub_swap]`. Conclude with `hk`.

Rewrite using `[valued_algebraMap]`. Conclude with `hkrt`.
-/
theorem exists_close (x : v.adicCompletion F) (hx : Valued.v x ≤ 1) :
    ∃ a : 𝓞 F, Valued.v (x - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) < 1 := by
  obtain ⟨k, hk⟩ : ∃ k : F, algebraMap F (v.adicCompletion F) k ∈
      {y : v.adicCompletion F | Valued.v (y - x) < 1} :=
    (denseRange v).exists_mem_open (isOpen_lt_one v x) ⟨x, by simp⟩
  simp only [Set.mem_setOf_eq] at hk
  have hk1 : v.valuation F k ≤ 1 := by
    rw [← valued_algebraMap]
    have e : algebraMap F (v.adicCompletion F) k = (algebraMap F (v.adicCompletion F) k - x) + x := by ring
    rw [e]
    exact Valuation.map_add_le _ hk.le hx
  obtain ⟨r, s, hs, hrs⟩ : ∃ r s : 𝓞 F, s ∉ v.asIdeal ∧
      algebraMap (𝓞 F) F s * k = algebraMap (𝓞 F) F r := by
    have hmem : k ∈ valuationSubringAtPrime F v := by
      rw [valuationSubringAtPrime_eq_valuationSubring]
      exact (Valuation.mem_valuationSubring_iff _ _).mpr hk1
    obtain ⟨⟨r, s⟩, h⟩ := IsLocalization.surj v.asIdeal.primeCompl
      (⟨k, hmem⟩ : valuationSubringAtPrime F v)
    refine ⟨r, s, s.2, ?_⟩
    have e : ∀ y : 𝓞 F, ((algebraMap (𝓞 F) (valuationSubringAtPrime F v) y :
        valuationSubringAtPrime F v) : F) = algebraMap (𝓞 F) F y := by
      intro y
      first
      | rfl
      | simp
      | exact (IsScalarTower.algebraMap_apply (𝓞 F) (valuationSubringAtPrime F v) F y).symm
    have h' := congrArg Subtype.val h
    have h'' : k * ((algebraMap (𝓞 F) (valuationSubringAtPrime F v) s : valuationSubringAtPrime F v) : F) =
        ((algebraMap (𝓞 F) (valuationSubringAtPrime F v) r : valuationSubringAtPrime F v) : F) := by
      simpa using h'
    rw [e, e] at h''
    rw [mul_comm]
    exact h''
  obtain ⟨t, ht⟩ : ∃ t : 𝓞 F, s * t - 1 ∈ v.asIdeal := by
    haveI := v.isMaximal
    have hs0 : (Ideal.Quotient.mk v.asIdeal s) ≠ 0 := by
      rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv hs0
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective b
    refine ⟨t, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hb, map_one, sub_self]
  refine ⟨r * t, ?_⟩
  have hkrt : v.valuation F (k - algebraMap (𝓞 F) F (r * t)) < 1 := by
    have e : k - algebraMap (𝓞 F) F (r * t) = k * (1 - algebraMap (𝓞 F) F (s * t)) := by
      rw [map_mul, map_mul, ← hrs]; ring
    rw [e, map_mul]
    have h1 : v.valuation F (1 - algebraMap (𝓞 F) F (s * t)) < 1 := by
      have e1 : (1 : F) - algebraMap (𝓞 F) F (s * t) = algebraMap (𝓞 F) F (-(s * t - 1)) := by
        rw [map_neg, map_sub, map_one]; ring
      rw [e1, valuation_lt_one_iff_mem]
      exact v.asIdeal.neg_mem_iff.mpr ht
    calc v.valuation F k * v.valuation F (1 - algebraMap (𝓞 F) F (s * t))
        ≤ 1 * v.valuation F (1 - algebraMap (𝓞 F) F (s * t)) := by
          first
          | exact mul_le_mul_of_nonneg_right hk1 zero_le'
          | gcongr
      _ < 1 := by rw [one_mul]; exact h1
  have e2 : x - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (r * t)) =
      (x - algebraMap F (v.adicCompletion F) k) +
        algebraMap F (v.adicCompletion F) (k - algebraMap (𝓞 F) F (r * t)) := by
    rw [map_sub]; ring
  rw [e2]
  apply Valuation.map_add_lt
  · rw [Valuation.map_sub_swap]; exact hk
  · rw [valued_algebraMap]; exact hkrt

/- English proof (translation)
Use `show ¬IsUnit x ↔ _`. Conclude with `Valuation.Integer.not_isUnit_iff_valuation_lt_one`.
-/
theorem mem_maximalIdeal_iff (x : Valued.integer (v.adicCompletion F)) :
    x ∈ IsLocalRing.maximalIdeal (Valued.integer (v.adicCompletion F)) ↔
      Valued.v (x : v.adicCompletion F) < 1 := by
  show ¬IsUnit x ↔ _
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one

noncomputable def toInt : 𝓞 F →+* Valued.integer (v.adicCompletion F) :=
  ((algebraMap F (v.adicCompletion F)).comp (algebraMap (𝓞 F) F)).codRestrict
    (Valued.integer (v.adicCompletion F)) (fun a => by
      show Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) ≤ 1
      rw [valued_algebraMap]
      exact valuation_le_one v a)

noncomputable def resHom :
    𝓞 F →+* IsLocalRing.ResidueField (Valued.integer (v.adicCompletion F)) :=
  (IsLocalRing.residue _).comp (toInt v)

/- English proof (translation)
Introduce `y`. Take `⟨x, rfl⟩` from `IsLocalRing.residue_surjective y`. Take `⟨a, ha⟩` from `exists_close v x x.2`. Use `⟨a, ?_⟩` and prove the remaining obligations. Unfold `resHom`.

Rewrite using `[RingHom.comp_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff]`. Establish `e : ((toInt v a - x : Valued.integer (v.adicCompletion F)) : v.adicCompletion F) = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) - x` using `rfl`. Rewrite using `[e, Valuation.map_sub_swap]`. Conclude with `ha`.
-/
theorem resHom_surjective : Function.Surjective (resHom v) := by
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨a, ha⟩ := exists_close v x x.2
  refine ⟨a, ?_⟩
  unfold resHom
  rw [RingHom.comp_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff]
  have e : ((toInt v a - x : Valued.integer (v.adicCompletion F)) : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) - x := rfl
  rw [e, Valuation.map_sub_swap]
  exact ha

/- English proof (translation)
Unfold `resHom`. Rewrite using `[RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff]`. Use `show Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) < 1`. Rewrite using `[valued_algebraMap]`. Conclude with `(valuation_lt_one_iff_mem v a).mpr ha`.
-/
theorem resHom_eq_zero (a : 𝓞 F) (ha : a ∈ v.asIdeal) : resHom v a = 0 := by
  unfold resHom
  rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff]
  show Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) < 1
  rw [valued_algebraMap]
  exact (valuation_lt_one_iff_mem v a).mpr ha

/- English proof (translation)
Use `haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot`. Set `g` to `Ideal.Quotient.lift v.asIdeal (resHom v) (fun a ha => resHom_eq_zero v a ha)`. Establish `hg : Function.Surjective g`. Introduce `y`. Take `⟨a, rfl⟩` from `resHom_surjective v y`.

Conclude with `⟨Ideal.Quotient.mk _ a, rfl⟩`. Conclude with `Finite.of_surjective g hg`.
-/
theorem finite_residueField : Finite (Valued.ResidueField (v.adicCompletion F)) := by
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  let g := Ideal.Quotient.lift v.asIdeal (resHom v) (fun a ha => resHom_eq_zero v a ha)
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨a, rfl⟩ := resHom_surjective v y
    exact ⟨Ideal.Quotient.mk _ a, rfl⟩
  exact Finite.of_surjective g hg

/- English proof (translation)
Rewrite using `[Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField]`. Use `⟨?_, ?_, finite_residueField v⟩` and prove the remaining obligations. Conclude with `((Valued.v.integer.toAddSubgroup).isClosed_of_isOpen (Valued.isOpen_integer _)).completeSpace_coe`. Conclude with `(inferInstance : IsDiscreteValuationRing (v.adicCompletionIntegers F))`.
-/
theorem compactSpace_integer : CompactSpace (Valued.integer (v.adicCompletion F)) := by
  rw [Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField]
  refine ⟨?_, ?_, finite_residueField v⟩
  · exact ((Valued.v.integer.toAddSubgroup).isClosed_of_isOpen (Valued.isOpen_integer _)).completeSpace_coe
  · exact (inferInstance : IsDiscreteValuationRing (v.adicCompletionIntegers F))

/- English proof (translation)
Use `haveI := compactSpace_integer v`. Conclude with `isCompact_iff_compactSpace.mpr this`.
-/
theorem isCompact_adicCompletionIntegers :
    IsCompact ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
  haveI := compactSpace_integer v
  exact isCompact_iff_compactSpace.mpr this

instance compactSpace_set : CompactSpace ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
  isCompact_iff_compactSpace.mp (isCompact_adicCompletionIntegers v)

instance compactSpace_sub : CompactSpace (v.adicCompletionIntegers F) :=
  isCompact_iff_compactSpace.mp (isCompact_adicCompletionIntegers v)

/- English proof (translation)
Introduce `F _ _`. Establish `hO : ∀ w : HeightOneSpectrum (𝓞 F), IsOpen ((w.adicCompletionIntegers F : Set (w.adicCompletion F)))` using `fun w => Valued.isOpen_valuationSubring _`. Use `⟨RestrictedProduct.isOpen_forall_mem hO, ?_⟩` and prove the remaining obligations. Establish `h` using `isCompact_range (RestrictedProduct.isOpenEmbedding_structureMap hO).continuous`. Rewrite `h` using `[RestrictedProduct.range_structureMap]`.

Conclude with `h`.
-/
theorem main : Formalism.L2.Props.IntAdelesCompactOpen := by
  intro F _ _
  have hO : ∀ w : HeightOneSpectrum (𝓞 F),
      IsOpen ((w.adicCompletionIntegers F : Set (w.adicCompletion F))) :=
    fun w => Valued.isOpen_valuationSubring _
  refine ⟨RestrictedProduct.isOpen_forall_mem hO, ?_⟩
  have h := isCompact_range (RestrictedProduct.isOpenEmbedding_structureMap hO).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

end PI.IntAdCpctOpenWork
