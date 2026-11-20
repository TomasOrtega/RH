import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalIffEtaProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdeleEquivOfLocal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsTensorFiniteAdeleEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseElementNegativeAtTwoEmbeddingsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdeleSqSubMulSqStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

open IsDedekindDomain

noncomputable section

namespace GlobalTheory.NormSign

/- English proof (translation)
Establish `hli : LinearIndependent K ![(1 : L), t]`. Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s c hsc`. Distinguish the cases in `hc : c = 0`. Substitute `hc` using the available equality.

Simplify using `only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hsc`. Conclude with `⟨hsc, rfl⟩`. It suffices to derive a contradiction. Establish `ht : t = algebraMap K L (-s / c)`. Rewrite `hsc` using `[Algebra.smul_def, Algebra.smul_def, mul_one]`.

Establish `hc' : algebraMap K L c ≠ 0` using `(map_ne_zero _).2 hc`. Rewrite using `[map_div₀, map_neg, eq_div_iff hc']`. Take the linear combination `hsc`. Establish `h2 : σ t = t` using `by rw [ht, hσK]`. Rewrite `h2` using `[hσt]`.

Establish `: (2 : L) * t = 0` using `by linear_combination -h2`. Break down `mul_eq_zero.1 this with h | h` into its components or cases. Establish `h2' : (2 : L) = algebraMap K L 2` using `(map_ofNat (algebraMap K L) 2).symm`. Rewrite `h` using `[h2']`. Conclude with `two_ne_zero ((map_eq_zero _).1 h)`.

Conclude with `ht0 h`. Set `e : Module.Basis (Fin 2) K L` to `basisOfLinearIndependentOfCardEqFinrank hli (by simp [hrank])`. Establish `e0 : e 0 = 1` using `by simp [e]`. Establish `e1 : e 1 * e 1 = algebraMap K L δ` using `by simp [e, htt]`. Establish `hu : IsUnit (algebraMap K (v.adicCompletion K) h)` using `(map_ne_zero _).2 h0 |>.isUnit`.

Use `haveI : FiniteDimensional K L := Module.finite_of_finrank_pos (by omega)`. Establish `hm : hu.unit ∈ GlobalTheory.QuadSymbol.normGroup K L (v.adicCompletion K)`. Rewrite using `[GlobalTheory.QuadSymbol.mem_normGroup_iff]`. Take `⟨z, hz⟩` from `hz`. Conclude with `⟨z, by rw [hz]; rfl⟩`.

Take `⟨x, y, hxy⟩` from `(GlobalTheory.QuadSymbol.mem_normGroup_iff_form e e0 e1).1 hm`. Conclude with `⟨x, y, by rw [← hxy]; rfl⟩`.
-/
theorem form_of_norm {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L]
    (hrank : Module.finrank K L = 2) (σ : L →+* L) (hσK : ∀ x : K, σ (algebraMap K L x) = algebraMap K L x)
    {t : L} {δ : K} (ht0 : t ≠ 0) (hσt : σ t = -t) (htt : t * t = algebraMap K L δ)
    (v : HeightOneSpectrum (𝓞 K)) {h : K} (h0 : h ≠ 0)
    (hz : ∃ z : v.adicCompletion K ⊗[K] L, Algebra.norm (v.adicCompletion K) z = algebraMap K (v.adicCompletion K) h) :
    ∃ x y : v.adicCompletion K, x ^ 2 - algebraMap K (v.adicCompletion K) δ * y ^ 2 =
      algebraMap K (v.adicCompletion K) h := by
  have hli : LinearIndependent K ![(1 : L), t] := by
    rw [LinearIndependent.pair_iff]
    intro s c hsc
    by_cases hc : c = 0
    · subst hc
      simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hsc
      exact ⟨hsc, rfl⟩
    · exfalso
      have ht : t = algebraMap K L (-s / c) := by
        rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hsc
        have hc' : algebraMap K L c ≠ 0 := (map_ne_zero _).2 hc
        rw [map_div₀, map_neg, eq_div_iff hc']
        linear_combination hsc
      have h2 : σ t = t := by rw [ht, hσK]
      rw [hσt] at h2
      have : (2 : L) * t = 0 := by linear_combination -h2
      rcases mul_eq_zero.1 this with h | h
      · have h2' : (2 : L) = algebraMap K L 2 := (map_ofNat (algebraMap K L) 2).symm
        rw [h2'] at h
        exact two_ne_zero ((map_eq_zero _).1 h)
      · exact ht0 h
  let e : Module.Basis (Fin 2) K L := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hrank])
  have e0 : e 0 = 1 := by simp [e]
  have e1 : e 1 * e 1 = algebraMap K L δ := by simp [e, htt]
  have hu : IsUnit (algebraMap K (v.adicCompletion K) h) := (map_ne_zero _).2 h0 |>.isUnit
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos (by omega)
  have hm : hu.unit ∈ GlobalTheory.QuadSymbol.normGroup K L (v.adicCompletion K) := by
    rw [GlobalTheory.QuadSymbol.mem_normGroup_iff]
    obtain ⟨z, hz⟩ := hz
    exact ⟨z, by rw [hz]; rfl⟩
  obtain ⟨x, y, hxy⟩ := (GlobalTheory.QuadSymbol.mem_normGroup_iff_form e e0 e1).1 hm
  exact ⟨x, y, by rw [← hxy]; rfl⟩

/- English proof (translation)
Take `⟨ι, hι, -⟩` from `GlobalTheory.AdeleBaseChange.exists_tensor_finiteAdele_equiv ℚ K`. Take `⟨e, -⟩` from `GlobalTheory.NormLevelCompare.exists_adele_equiv`. Set `g : FiniteAdeleRing (𝓞 ℚ) ℚ →ₐ[ℚ] AfP p` to `((AfP.restr p).comp (e : FiniteAdeleRing (𝓞 ℚ) ℚ →+* FiniteAdeleRing ℤ ℚ)).toRatAlgHom`. Set `m : FiniteAdeleRing (𝓞 ℚ) ℚ ⊗[ℚ] K →ₐ[ℚ] AfP p ⊗[ℚ] K` to `Algebra.TensorProduct.map g (AlgHom.id ℚ K)`. Use `⟨m.toRingHom.comp ι.symm.toRingHom, fun k => ?_⟩` and prove the remaining obligations.

Establish `: ι.symm (algebraMap K _ k) = 1 ⊗ₜ k` using `by rw [← hι, RingEquiv.symm_apply_apply]`. Simplify using `only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, this]`. Simplify using `[m]`.
-/
theorem exists_toAfP (K : Type) [Field K] [NumberField K] (p : ℕ) :
    ∃ Φ : FiniteAdeleRing (𝓞 K) K →+* AfP p ⊗[ℚ] K, ∀ k : K, Φ (algebraMap K _ k) = 1 ⊗ₜ k := by
  obtain ⟨ι, hι, -⟩ := GlobalTheory.AdeleBaseChange.exists_tensor_finiteAdele_equiv ℚ K
  obtain ⟨e, -⟩ := GlobalTheory.NormLevelCompare.exists_adele_equiv
  let g : FiniteAdeleRing (𝓞 ℚ) ℚ →ₐ[ℚ] AfP p :=
    ((AfP.restr p).comp (e : FiniteAdeleRing (𝓞 ℚ) ℚ →+* FiniteAdeleRing ℤ ℚ)).toRatAlgHom
  let m : FiniteAdeleRing (𝓞 ℚ) ℚ ⊗[ℚ] K →ₐ[ℚ] AfP p ⊗[ℚ] K :=
    Algebra.TensorProduct.map g (AlgHom.id ℚ K)
  refine ⟨m.toRingHom.comp ι.symm.toRingHom, fun k => ?_⟩
  have : ι.symm (algebraMap K _ k) = 1 ⊗ₜ k := by rw [← hι, RingEquiv.symm_apply_apply]
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, this]
  simp [m]

/- English proof (translation)
Introduce `M _ _ σ hσ hconj ε ε' hεε' hεc p _`. Establish `hinv : ∀ x, σ (σ x) = x`. Introduce `x`. Take `⟨φ⟩ : Nonempty (M →+* ℂ)` from `inferInstance`. Apply `φ.injective` to reduce the goal to its premises.

Rewrite using `[hconj, hconj, Complex.conj_conj]`. Set `σe : M ≃ₐ[ℚ] M` to `{ σ.toRatAlgHom with invFun := σ, left_inv := hinv, right_inv := hinv }`. Establish `hσe : ∀ x, σe x = σ x` using `fun _ => rfl`. Establish `hσe2 : σe ^ 2 = 1`. Use extensionality with `x`.

Rewrite using `[pow_two, AlgEquiv.mul_apply, hσe, hσe, hinv]`. Both sides reduce to the same expression. Establish `hσe1 : σe ≠ 1`. Introduce `h`. Apply `hσ` to reduce the goal to its premises.

Use extensionality with `x`. Use `congrArg (fun f : M ≃ₐ[ℚ] M => f x) h` as an intermediate fact. Simplify `this` using `[hσe]`. Establish `hσinv : σe⁻¹ = σe` using `inv_eq_of_mul_eq_one_right (by rw [← pow_two, hσe2])`. Set `K` to `IntermediateField.fixedField (Subgroup.zpowers σe)`.

Establish `hmem : ∀ x : M, x ∈ K ↔ σ x = x`. Introduce `x`. Rewrite using `[IntermediateField.mem_fixedField_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Conclude with `h σe (Subgroup.mem_zpowers σe)`. Introduce `h f hf`. Take `⟨k, rfl⟩` from `Subgroup.mem_zpowers_iff.1 hf`. Use `clear hf`. Proceed by induction on `k using Int.induction_on with`.

Consider the case `zero => simp`. Consider the case `succ n ih => rw [_root_.zpow_add_one, AlgEquiv.mul_apply, hσe, h, ih]`. Consider the case `pred n ih => rw [_root_.zpow_sub_one, AlgEquiv.mul_apply, hσinv, hσe, h, ih]`. Establish `hrank : Module.finrank K M = 2`. Rewrite using `[IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers]`.

Conclude with `orderOf_eq_prime hσe2 hσe1`. Establish `hσK : ∀ x : K, σ (algebraMap K M x) = algebraMap K M x` using `fun x => (hmem _).1 x.2`. Take `⟨h, h0, hε, hε', hpos, hloc⟩` from `GlobalTheory.T.exists_base_element_negative_at_two_embeddings K M hrank σ hσ hσK hconj ε ε' hεε' hεc`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs⟩ : ∃ s, σ s ≠ s := by`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Conclude with `hσ (RingHom.ext hc)`. Use `set t := s - σ s with ht`. Establish `hσt : σ t = -t` using `by rw [ht, map_sub, hinv]; ring`. Establish `ht0 : t ≠ 0` using `sub_ne_zero.2 (Ne.symm hs)`.

Establish `htK : t * t ∈ K` using `(hmem _).2 (by rw [map_mul, hσt]; ring)`. Set `δ : K` to `⟨t * t, htK⟩`. Establish `htt : t * t = algebraMap K M δ` using `rfl`. Establish `hδ0 : δ ≠ 0`. Introduce `hd`.

Apply `ht0` to reduce the goal to its premises. Establish `: t * t = 0` using `by rw [htt, hd, map_zero]`. Conclude with `mul_self_eq_zero.1 this`. Establish `hform` using `fun v => form_of_norm hrank σ hσK ht0 hσt htt v h0 (hloc v)`. Take `⟨x, y, hxy⟩` from `GlobalTheory.T.exists_finiteAdele_sq_sub_mul_sq_eq_of_local K δ h hδ0 h0 hform`.

Take `⟨Φ, hΦ⟩` from `exists_toAfP K p`. Set `j : AfP p ⊗[ℚ] K →ₐ[ℚ] AfP p ⊗[ℚ] M` to `Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) (IsScalarTower.toAlgHom ℚ K M)`. Set `S : AfP p ⊗[ℚ] M →ₐ[ℚ] AfP p ⊗[ℚ] M` to `Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom`. Establish `hSj' : ∀ w, S (j w) = j w`. Introduce `w`.

Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a k => show a ⊗ₜ σ (algebraMap K M k) = a ⊗ₜ algebraMap K M k`. Rewrite using `[hσK]`. Consider the case `add w w' hw hw' => rw [map_add, map_add, hw, hw']`.

Use `set X := j (Φ x) with hX`. Use `set Y := j (Φ y) with hY`. Use `set T : AfP p ⊗[ℚ] M := 1 ⊗ₜ t with hT`. Establish `hST : S T = -T` using `by simp [S, T, hσt, TensorProduct.tmul_neg]`. Establish `hTT : T * T = j (Φ (algebraMap K _ δ))`.

Rewrite using `[hΦ, hT, Algebra.TensorProduct.tmul_mul_tmul, mul_one, htt]`. Simplify using `[j]`. Establish `hkey : (X + Y * T) * S (X + Y * T) = 1 ⊗ₜ (algebraMap K M h)`. Rewrite using `[map_add, map_mul, hX, hY, hSj', hSj', hST]`. Establish `: (j (Φ x) + j (Φ y) * T) * (j (Φ x) + j (Φ y) * -T) = j (Φ (x ^ 2 - algebraMap K _ δ * y ^ 2))`.

Rewrite using `[map_sub, map_mul, map_pow, map_pow, map_sub, map_mul, map_pow, map_pow, ← hTT]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, hxy, hΦ]`. Simplify using `[j]`. Establish `hunit : IsUnit (X + Y * T)`.

Establish `ha : IsUnit ((1 : AfP p) ⊗ₜ[ℚ] (algebraMap K M h))` using `((map_ne_zero (algebraMap K M)).2 h0).isUnit.map (Algebra.TensorProduct.includeRight : M →ₐ[ℚ] AfP p ⊗[ℚ] M)`. Rewrite `ha` using `[← hkey]`. Conclude with `isUnit_of_mul_isUnit_left ha`. Conclude with `⟨algebraMap K M h, (map_ne_zero _).2 h0, hσK h, hε, hε', hpos, hunit.unit, hkey⟩`.
-/
theorem exists_neg_two_norm_away : ∀ (M : Type) [Field M] [NumberField M] (σ : M →+* M), σ ≠ RingHom.id M → (∀ (φ : M →+* ℂ) (x : M), φ (σ x) = (starRingEnd ℂ) (φ x)) → ∀ ε ε' : M →+* ℂ, ε ≠ ε' → ε ≠ ComplexEmbedding.conjugate ε' → ∀ (p : ℕ) [Fact p.Prime], ∃ a : M, a ≠ 0 ∧ σ a = a ∧ (ε a).re < 0 ∧ (ε' a).re < 0 ∧ (∀ φ : M →+* ℂ, φ ≠ ε → φ ≠ ComplexEmbedding.conjugate ε → φ ≠ ε' → φ ≠ ComplexEmbedding.conjugate ε' → 0 < (φ a).re) ∧ ∃ u : (AfP p ⊗[ℚ] M)ˣ, (u : AfP p ⊗[ℚ] M) * Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom u = 1 ⊗ₜ a := by
  intro M _ _ σ hσ hconj ε ε' hεε' hεc p _
  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    obtain ⟨φ⟩ : Nonempty (M →+* ℂ) := inferInstance
    apply φ.injective
    rw [hconj, hconj, Complex.conj_conj]
  let σe : M ≃ₐ[ℚ] M :=
    { σ.toRatAlgHom with invFun := σ, left_inv := hinv, right_inv := hinv }
  have hσe : ∀ x, σe x = σ x := fun _ => rfl
  have hσe2 : σe ^ 2 = 1 := by
    ext x; rw [pow_two, AlgEquiv.mul_apply, hσe, hσe, hinv]; rfl
  have hσe1 : σe ≠ 1 := by
    intro h; apply hσ; ext x
    have := congrArg (fun f : M ≃ₐ[ℚ] M => f x) h
    simpa [hσe] using this
  have hσinv : σe⁻¹ = σe := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hσe2])
  let K := IntermediateField.fixedField (Subgroup.zpowers σe)
  have hmem : ∀ x : M, x ∈ K ↔ σ x = x := by
    intro x
    rw [IntermediateField.mem_fixedField_iff]
    constructor
    · intro h; exact h σe (Subgroup.mem_zpowers σe)
    · intro h f hf
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hf
      clear hf
      induction k using Int.induction_on with
      | zero => simp
      | succ n ih => rw [_root_.zpow_add_one, AlgEquiv.mul_apply, hσe, h, ih]
      | pred n ih => rw [_root_.zpow_sub_one, AlgEquiv.mul_apply, hσinv, hσe, h, ih]
  have hrank : Module.finrank K M = 2 := by
    rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers]
    exact orderOf_eq_prime hσe2 hσe1
  have hσK : ∀ x : K, σ (algebraMap K M x) = algebraMap K M x := fun x => (hmem _).1 x.2
  obtain ⟨h, h0, hε, hε', hpos, hloc⟩ := GlobalTheory.T.exists_base_element_negative_at_two_embeddings K M hrank σ hσ hσK hconj ε ε' hεε' hεc
  obtain ⟨s, hs⟩ : ∃ s, σ s ≠ s := by
    by_contra hc; push_neg at hc; exact hσ (RingHom.ext hc)
  set t := s - σ s with ht
  have hσt : σ t = -t := by rw [ht, map_sub, hinv]; ring
  have ht0 : t ≠ 0 := sub_ne_zero.2 (Ne.symm hs)
  have htK : t * t ∈ K := (hmem _).2 (by rw [map_mul, hσt]; ring)
  let δ : K := ⟨t * t, htK⟩
  have htt : t * t = algebraMap K M δ := rfl
  have hδ0 : δ ≠ 0 := by
    intro hd; apply ht0
    have : t * t = 0 := by rw [htt, hd, map_zero]
    exact mul_self_eq_zero.1 this
  have hform := fun v => form_of_norm hrank σ hσK ht0 hσt htt v h0 (hloc v)
  obtain ⟨x, y, hxy⟩ := GlobalTheory.T.exists_finiteAdele_sq_sub_mul_sq_eq_of_local K δ h hδ0 h0 hform
  obtain ⟨Φ, hΦ⟩ := exists_toAfP K p
  let j : AfP p ⊗[ℚ] K →ₐ[ℚ] AfP p ⊗[ℚ] M :=
    Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) (IsScalarTower.toAlgHom ℚ K M)
  let S : AfP p ⊗[ℚ] M →ₐ[ℚ] AfP p ⊗[ℚ] M :=
    Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom
  have hSj' : ∀ w, S (j w) = j w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a k =>
      show a ⊗ₜ σ (algebraMap K M k) = a ⊗ₜ algebraMap K M k
      rw [hσK]
    | add w w' hw hw' => rw [map_add, map_add, hw, hw']
  set X := j (Φ x) with hX
  set Y := j (Φ y) with hY
  set T : AfP p ⊗[ℚ] M := 1 ⊗ₜ t with hT
  have hST : S T = -T := by simp [S, T, hσt, TensorProduct.tmul_neg]
  have hTT : T * T = j (Φ (algebraMap K _ δ)) := by
    rw [hΦ, hT, Algebra.TensorProduct.tmul_mul_tmul, mul_one, htt]; simp [j]
  have hkey : (X + Y * T) * S (X + Y * T) = 1 ⊗ₜ (algebraMap K M h) := by
    rw [map_add, map_mul, hX, hY, hSj', hSj', hST]
    have : (j (Φ x) + j (Φ y) * T) * (j (Φ x) + j (Φ y) * -T) =
        j (Φ (x ^ 2 - algebraMap K _ δ * y ^ 2)) := by
      rw [map_sub, map_mul, map_pow, map_pow, map_sub, map_mul, map_pow, map_pow, ← hTT]; ring
    rw [this, hxy, hΦ]; simp [j]
  have hunit : IsUnit (X + Y * T) := by
    have ha : IsUnit ((1 : AfP p) ⊗ₜ[ℚ] (algebraMap K M h)) :=
      ((map_ne_zero (algebraMap K M)).2 h0).isUnit.map
        (Algebra.TensorProduct.includeRight : M →ₐ[ℚ] AfP p ⊗[ℚ] M)
    rw [← hkey] at ha
    exact isUnit_of_mul_isUnit_left ha
  exact ⟨algebraMap K M h, (map_ne_zero _).2 h0, hσK h, hε, hε', hpos, hunit.unit, hkey⟩

end GlobalTheory.NormSign
