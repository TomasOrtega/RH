import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMRegularElement
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.CMDepthAssoc
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing RingTheory.Sequence CategoryTheory Abelian Limits Pointwise

universe u

/- English proof (translation)
Take `⟨rs, hm, hreg, hdim⟩` from `IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := B)`. Take `⟨hprime, m, hpm⟩` from `isAssociatedPrime_iff.mp hp`. Establish `hm0 : m ≠ 0`. Introduce and unpack `rfl`. Apply `hprime.ne_top` to reduce the goal to its premises.

Rewrite using `[hpm, eq_top_iff]`. Introduce `r _`. Rewrite using `[Submodule.mem_colon_singleton, smul_zero]`. Conclude with `Submodule.zero_mem _`. Establish `hD` using `length_le_ringKrullDim_quotient_colon rs m hm0 hm hreg`.

Rewrite `hD` using `[← hpm]`. Take `⟨q, hq, hqp⟩` from `Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal B)) (J := p) bot_le`. Distinguish the cases in `hqp' : q = p`. Conclude with `hqp' ▸ hq`. It suffices to derive a contradiction.

Take `⟨a, hap, haq⟩` from `SetLike.exists_of_lt (lt_of_le_of_ne hqp hqp')`. Establish `: q.IsPrime` using `hq.1.1`. Establish `hnzd : Ideal.Quotient.mk q a ∈ nonZeroDivisors (B ⧸ q)` using `mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])`. Establish `hd2` using `ringKrullDim_quotient_succ_le_of_nonZeroDivisor hnzd`. Establish `heq : (B ⧸ q) ⧸ Ideal.span {Ideal.Quotient.mk q a} ≃+* B ⧸ (q ⊔ Ideal.span {a})`.

Establish `: Ideal.span {Ideal.Quotient.mk q a} = (Ideal.span {a}).map (Ideal.Quotient.mk q)`. Rewrite using `[Ideal.map_span, Set.image_singleton]`. Rewrite using `[this]`. Conclude with `DoubleQuot.quotQuotEquivQuotSup q (Ideal.span {a})`. Rewrite `hd2` using `[ringKrullDim_eq_of_ringEquiv heq]`.

Establish `hle : q ⊔ Ideal.span {a} ≤ p` using `sup_le hqp ((Ideal.span_singleton_le_iff_mem p).mpr hap)`. Establish `h1 : ringKrullDim (B ⧸ p) ≤ ringKrullDim (B ⧸ (q ⊔ Ideal.span {a}))` using `ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hle)`. Establish `h2 : ringKrullDim (B ⧸ q) ≤ ringKrullDim B` using `ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective`. Establish `h3 : ringKrullDim (B ⧸ p) ≤ ringKrullDim B` using `ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective`. Rewrite `h2`, `h3` using `[hdim]`.

Establish `h4 : ringKrullDim (B ⧸ p) = (rs.length : WithBot ℕ∞)` using `le_antisymm h3 hD`. Establish `h5 : ringKrullDim (B ⧸ p) + 1 ≤ (rs.length : WithBot ℕ∞)` using `((by gcongr : ringKrullDim (B ⧸ p) + 1 ≤ ringKrullDim (B ⧸ (q ⊔ Ideal.span {a})) + 1).trans hd2).trans h2`. Rewrite `h5` using `[h4]`. Normalize the coercions in `at h5`. Use linear arithmetic over natural numbers and integers.
-/
theorem mem_minimalPrimes_of_mem_associatedPrimes {B : Type*} [CommRing B] [IsCohenMacaulayLocalRing B]
    {p : Ideal B} (hp : p ∈ associatedPrimes B B) : p ∈ minimalPrimes B := by
  obtain ⟨rs, hm, hreg, hdim⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := B)
  obtain ⟨hprime, m, hpm⟩ := isAssociatedPrime_iff.mp hp
  have hm0 : m ≠ 0 := by
    rintro rfl
    apply hprime.ne_top
    rw [hpm, eq_top_iff]
    intro r _
    rw [Submodule.mem_colon_singleton, smul_zero]
    exact Submodule.zero_mem _
  have hD := length_le_ringKrullDim_quotient_colon rs m hm0 hm hreg
  rw [← hpm] at hD
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal B)) (J := p) bot_le
  by_cases hqp' : q = p
  · exact hqp' ▸ hq
  exfalso
  obtain ⟨a, hap, haq⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hqp hqp')
  have : q.IsPrime := hq.1.1
  have hnzd : Ideal.Quotient.mk q a ∈ nonZeroDivisors (B ⧸ q) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  have hd2 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hnzd
  have heq : (B ⧸ q) ⧸ Ideal.span {Ideal.Quotient.mk q a} ≃+* B ⧸ (q ⊔ Ideal.span {a}) := by
    have : Ideal.span {Ideal.Quotient.mk q a} = (Ideal.span {a}).map (Ideal.Quotient.mk q) := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [this]
    exact DoubleQuot.quotQuotEquivQuotSup q (Ideal.span {a})
  rw [ringKrullDim_eq_of_ringEquiv heq] at hd2
  have hle : q ⊔ Ideal.span {a} ≤ p := sup_le hqp ((Ideal.span_singleton_le_iff_mem p).mpr hap)
  have h1 : ringKrullDim (B ⧸ p) ≤ ringKrullDim (B ⧸ (q ⊔ Ideal.span {a})) :=
    ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hle)
  have h2 : ringKrullDim (B ⧸ q) ≤ ringKrullDim B := ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective
  have h3 : ringKrullDim (B ⧸ p) ≤ ringKrullDim B := ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective
  rw [hdim] at h2 h3
  have h4 : ringKrullDim (B ⧸ p) = (rs.length : WithBot ℕ∞) := le_antisymm h3 hD
  have h5 : ringKrullDim (B ⧸ p) + 1 ≤ (rs.length : WithBot ℕ∞) :=
    ((by gcongr : ringKrullDim (B ⧸ p) + 1 ≤ ringKrullDim (B ⧸ (q ⊔ Ideal.span {a})) + 1).trans hd2).trans h2
  rw [h4] at h5
  norm_cast at h5
  omega

/- English proof (translation)
Assume the negation of the conclusion as `h`. Establish `h' : y ∈ (nonZeroDivisors B : Set B)ᶜ` using `h`. Rewrite `h'` using `[← biUnion_associatedPrimes_eq_compl_nonZeroDivisors, Set.mem_iUnion₂]`. Take `⟨p, hp, hyp⟩` from `h'`. Conclude with `hy p (mem_minimalPrimes_of_mem_associatedPrimes hp) hyp`.
-/
theorem mem_nonZeroDivisors_of_not_mem_minimalPrimes {B : Type*} [CommRing B] [IsCohenMacaulayLocalRing B] {y : B}
    (hy : ∀ p ∈ minimalPrimes B, y ∉ p) : y ∈ nonZeroDivisors B := by
  by_contra h
  have h' : y ∈ (nonZeroDivisors B : Set B)ᶜ := h
  rw [← biUnion_associatedPrimes_eq_compl_nonZeroDivisors, Set.mem_iUnion₂] at h'
  obtain ⟨p, hp, hyp⟩ := h'
  exact hy p (mem_minimalPrimes_of_mem_associatedPrimes hp) hyp

/- English proof (translation)
Establish `key : ∀ (X : Type u) [AddCommGroup X] [Module B X] [Module.Finite B X] [Nontrivial X], maximalIdeal B • (⊤ : Submodule B X) < ⊤` using `fun X _ _ _ _ => by`. Use `(Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator ?_).symm.lt_top` and prove the remaining obligations. Establish `H : Module.annihilator B X ≠ ⊤` using `fun h => not_subsingleton X (Module.annihilator_eq_top_iff.mp h)`. Conclude with `(jacobson_eq_maximalIdeal _ H).ge`. Establish `hne : (y • (⊤ : Submodule B B)) ≠ ⊤`.

Introduce `h`. Establish `h1 : (1 : B) ∈ y • (⊤ : Submodule B B)` using `by rw [h]; exact Submodule.mem_top`. Take `⟨b, -, hb⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h1`. Conclude with `(mem_maximalIdeal _).mp hym (IsUnit.of_mul_eq_one b (by simpa [smul_eq_mul] using hb))`. Establish `: Nontrivial (QuotSMulTop y B)` using `Submodule.Quotient.nontrivial_iff.mpr hne`.

Set `M : ModuleCat.{u} B` to `ModuleCat.of B B`. Set `S` to `ModuleCat.smulShortComplex M y`. Establish `hS : S.ShortExact` using `IsSMulRegular.smulShortComplex_shortExact (M := M) hy`. Set `N : ModuleCat.{u} B` to `ModuleCat.of B (Shrink.{u} (B ⧸ maximalIdeal B))`. Establish `hregB : IsRegular B rs` using `(isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hm).mpr hreg`.

Establish `hextB : ∀ i < rs.length, Subsingleton (Ext N M i)` using `((ModuleCat.exists_isRegular_tfae (maximalIdeal B) rs.length M (key B)).out 1 3).mpr (⟨rs, rfl, hm, hregB⟩ : ∃ rs' : List B, rs'.length = rs.length ∧ (∀ r ∈ rs', r ∈ maximalIdeal B) ∧ IsRegular M rs')`. Establish `hext3 : ∀ i < rs.length - 1, Subsingleton (Ext N S.X₃ i)`. Introduce `i hi`. Establish `hex` using `Ext.covariant_sequence_exact₃' N hS i (i + 1) rfl`. Establish `h1 : IsZero (AddCommGrpCat.of (Abelian.Ext N S.X₂ i))` using `AddCommGrpCat.isZero_of_iff_subsingleton.mpr (hextB i (by omega))`.

Establish `h3 : IsZero (AddCommGrpCat.of (Abelian.Ext N S.X₁ (i + 1)))` using `AddCommGrpCat.isZero_of_iff_subsingleton.mpr (hextB (i + 1) (by omega))`. Conclude with `AddCommGrpCat.subsingleton_of_isZero (hex.isZero_of_both_zeros (h1.eq_of_src _ _) (h3.eq_of_tgt _ _))`. Establish `: Module.Finite B S.X₃` using `inferInstanceAs (Module.Finite B (QuotSMulTop y B))`. Establish `: Nontrivial S.X₃` using `inferInstanceAs (Nontrivial (QuotSMulTop y B))`. Take `⟨rs', hlen, hm', hreg'⟩` from `((ModuleCat.exists_isRegular_tfae (maximalIdeal B) (rs.length - 1) S.X₃ (key S.X₃)).out 1 3).mp hext3`.

Conclude with `⟨rs', hlen, hm', hreg'⟩`.
-/
theorem exists_isRegular_quotSMulTop {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    {rs : List B} (hm : ∀ r ∈ rs, r ∈ maximalIdeal B) (hreg : IsWeaklyRegular B rs)
    {y : B} (hy : IsSMulRegular B y) (hym : y ∈ maximalIdeal B) :
    ∃ rs' : List B, rs'.length = rs.length - 1 ∧ (∀ r ∈ rs', r ∈ maximalIdeal B) ∧
      IsRegular (QuotSMulTop y B) rs' := by
  have key : ∀ (X : Type u) [AddCommGroup X] [Module B X] [Module.Finite B X] [Nontrivial X],
      maximalIdeal B • (⊤ : Submodule B X) < ⊤ := fun X _ _ _ _ => by
    refine (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator ?_).symm.lt_top
    have H : Module.annihilator B X ≠ ⊤ := fun h => not_subsingleton X (Module.annihilator_eq_top_iff.mp h)
    exact (jacobson_eq_maximalIdeal _ H).ge
  have hne : (y • (⊤ : Submodule B B)) ≠ ⊤ := by
    intro h
    have h1 : (1 : B) ∈ y • (⊤ : Submodule B B) := by rw [h]; exact Submodule.mem_top
    obtain ⟨b, -, hb⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h1
    exact (mem_maximalIdeal _).mp hym (IsUnit.of_mul_eq_one b (by simpa [smul_eq_mul] using hb))
  have : Nontrivial (QuotSMulTop y B) := Submodule.Quotient.nontrivial_iff.mpr hne
  let M : ModuleCat.{u} B := ModuleCat.of B B
  let S := ModuleCat.smulShortComplex M y
  have hS : S.ShortExact := IsSMulRegular.smulShortComplex_shortExact (M := M) hy
  let N : ModuleCat.{u} B := ModuleCat.of B (Shrink.{u} (B ⧸ maximalIdeal B))
  have hregB : IsRegular B rs := (isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hm).mpr hreg
  have hextB : ∀ i < rs.length, Subsingleton (Ext N M i) :=
    ((ModuleCat.exists_isRegular_tfae (maximalIdeal B) rs.length M (key B)).out 1 3).mpr
      (⟨rs, rfl, hm, hregB⟩ : ∃ rs' : List B, rs'.length = rs.length ∧ (∀ r ∈ rs', r ∈ maximalIdeal B) ∧ IsRegular M rs')
  have hext3 : ∀ i < rs.length - 1, Subsingleton (Ext N S.X₃ i) := by
    intro i hi
    have hex := Ext.covariant_sequence_exact₃' N hS i (i + 1) rfl
    have h1 : IsZero (AddCommGrpCat.of (Abelian.Ext N S.X₂ i)) :=
      AddCommGrpCat.isZero_of_iff_subsingleton.mpr (hextB i (by omega))
    have h3 : IsZero (AddCommGrpCat.of (Abelian.Ext N S.X₁ (i + 1))) :=
      AddCommGrpCat.isZero_of_iff_subsingleton.mpr (hextB (i + 1) (by omega))
    exact AddCommGrpCat.subsingleton_of_isZero (hex.isZero_of_both_zeros (h1.eq_of_src _ _) (h3.eq_of_tgt _ _))
  have : Module.Finite B S.X₃ := inferInstanceAs (Module.Finite B (QuotSMulTop y B))
  have : Nontrivial S.X₃ := inferInstanceAs (Nontrivial (QuotSMulTop y B))
  obtain ⟨rs', hlen, hm', hreg'⟩ :=
    ((ModuleCat.exists_isRegular_tfae (maximalIdeal B) (rs.length - 1) S.X₃ (key S.X₃)).out 1 3).mp hext3
  exact ⟨rs', hlen, hm', hreg'⟩

/- English proof (translation)
Introduce `B _ _ y hym hy`. Establish `hnzd` using `mem_nonZeroDivisors_of_not_mem_minimalPrimes hy`. Use `⟨hnzd, ?_⟩` and prove the remaining obligations. Take `⟨rs, hm, hreg, hdim⟩` from `IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := B)`. Establish `hyreg : IsSMulRegular B y` using `Module.Flat.isSMulRegular_of_nonZeroDivisors hnzd`.

Take `⟨rs', hlen, hm', hreg'⟩` from `exists_isRegular_quotSMulTop hm hreg hyreg hym`. Use `set I := Ideal.span {y} with hIdef`. Establish `hI : I ≠ ⊤` using `Ideal.span_singleton_ne_top ((mem_maximalIdeal _).mp hym)`. Establish `: Nontrivial (B ⧸ I)` using `Ideal.Quotient.nontrivial_iff.mpr hI`. Establish `: IsLocalRing (B ⧸ I)` using `IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective`.

Establish `hloc : IsLocalHom (Ideal.Quotient.mk I)` using `isLocalHom_of_le_jacobson_bot I (by`. Rewrite using `[jacobson_eq_maximalIdeal ⊥ bot_ne_top]`. Conclude with `(Ideal.span_singleton_le_iff_mem _).mpr hym)`. Establish `hsub : (y • (⊤ : Submodule B B)) = I`. Rewrite using `[hIdef, ← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]`.

Set `e : QuotSMulTop y B ≃ₗ[B] B ⧸ I` to `Submodule.quotEquivOfEq _ _ hsub`. Establish `hw : IsWeaklyRegular (B ⧸ I) (rs'.map (algebraMap B (B ⧸ I)))` using `(isWeaklyRegular_map_algebraMap_iff (S := B ⧸ I) (M := B ⧸ I) rs').mpr ((e.isWeaklyRegular_congr rs').mp hreg'.toIsWeaklyRegular)`. Establish `hdimq` using `ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors hnzd hym`. Use `{ exists_isWeaklyRegular := ⟨rs'.map (algebraMap B (B ⧸ I)), ?_, hw, ?_⟩ }` and prove the remaining obligations. Introduce `r hr`.

Take `⟨s, hs, rfl⟩` from `List.mem_map.mp hr`. Conclude with `map_nonunit (Ideal.Quotient.mk I) s (hm' s hs)`. Rewrite using `[List.length_map, hlen]`. Establish `h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (B ⧸ I)` using `ringKrullDim_nonneg_of_nontrivial`. Rewrite `hdimq` using `[hdim]`.

Take `⟨d, hd⟩ : ∃ d : ℕ∞, ringKrullDim (B ⧸ I) = d` from `(WithBot.ne_bot_iff_exists.mp (ne_bot_of_le_ne_bot WithBot.zero_ne_bot h0)).imp fun _ h => h.symm`. Rewrite `hdimq`, the goal using `[hd]`. Establish `h2 : d + 1 = (rs.length : ℕ∞)` using `by exact_mod_cast hdimq`. Proceed by induction on `d using ENat.recTopCoe with`. Consider the case `top => simp at h2`.

Consider the case `coe k`. Normalize the coercions in `at h2 ⊢`. Rewrite using `[show k = rs.length - 1 by omega]`.
-/
theorem CMRegularElement.proof : CMRegularElement.Statement.{u} := by
  intro B _ _ y hym hy
  have hnzd := mem_nonZeroDivisors_of_not_mem_minimalPrimes hy
  refine ⟨hnzd, ?_⟩
  obtain ⟨rs, hm, hreg, hdim⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := B)
  have hyreg : IsSMulRegular B y := Module.Flat.isSMulRegular_of_nonZeroDivisors hnzd
  obtain ⟨rs', hlen, hm', hreg'⟩ := exists_isRegular_quotSMulTop hm hreg hyreg hym
  set I := Ideal.span {y} with hIdef
  have hI : I ≠ ⊤ := Ideal.span_singleton_ne_top ((mem_maximalIdeal _).mp hym)
  have : Nontrivial (B ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have : IsLocalRing (B ⧸ I) := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hloc : IsLocalHom (Ideal.Quotient.mk I) := isLocalHom_of_le_jacobson_bot I (by
    rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact (Ideal.span_singleton_le_iff_mem _).mpr hym)
  have hsub : (y • (⊤ : Submodule B B)) = I := by
    rw [hIdef, ← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
  let e : QuotSMulTop y B ≃ₗ[B] B ⧸ I := Submodule.quotEquivOfEq _ _ hsub
  have hw : IsWeaklyRegular (B ⧸ I) (rs'.map (algebraMap B (B ⧸ I))) :=
    (isWeaklyRegular_map_algebraMap_iff (S := B ⧸ I) (M := B ⧸ I) rs').mpr
      ((e.isWeaklyRegular_congr rs').mp hreg'.toIsWeaklyRegular)
  have hdimq := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors hnzd hym
  refine { exists_isWeaklyRegular := ⟨rs'.map (algebraMap B (B ⧸ I)), ?_, hw, ?_⟩ }
  · intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    exact map_nonunit (Ideal.Quotient.mk I) s (hm' s hs)
  · rw [List.length_map, hlen]
    have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (B ⧸ I) := ringKrullDim_nonneg_of_nontrivial
    rw [hdim] at hdimq
    obtain ⟨d, hd⟩ : ∃ d : ℕ∞, ringKrullDim (B ⧸ I) = d :=
      (WithBot.ne_bot_iff_exists.mp (ne_bot_of_le_ne_bot WithBot.zero_ne_bot h0)).imp fun _ h => h.symm
    rw [hd] at hdimq ⊢
    have h2 : d + 1 = (rs.length : ℕ∞) := by exact_mod_cast hdimq
    induction d using ENat.recTopCoe with
    | top => simp at h2
    | coe k =>
      norm_cast at h2 ⊢
      rw [show k = rs.length - 1 by omega]

end GroundTheory.Heights₂.Heights
