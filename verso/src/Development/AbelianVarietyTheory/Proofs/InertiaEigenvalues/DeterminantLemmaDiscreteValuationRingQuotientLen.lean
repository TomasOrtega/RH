import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthCommensurableSpanSpanOfDetNeZero

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut
open IsDiscreteValuationRing

namespace GlobalTheory.DetGen

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
Use `(Module.length_le_of_surjective (Submodule.factor h) (Submodule.factor_surjective h)).trans ?_` and prove the remaining obligations. Use `Module.length_le_of_injective ((LinearMap.ker f).liftQ f le_rfl) ?_` and prove the remaining obligations. Rewrite using `[← LinearMap.ker_eq_bot]`. Conclude with `Submodule.ker_liftQ_eq_bot _ _ _ le_rfl`.
-/
theorem length_quot_le_of_ker_le' {R X S : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup S]
    [Module R S] (f : X →ₗ[R] S) (P : Submodule R X) (h : LinearMap.ker f ≤ P) :
    Module.length R (X ⧸ P) ≤ Module.length R S := by
  refine (Module.length_le_of_surjective (Submodule.factor h) (Submodule.factor_surjective h)).trans ?_
  refine Module.length_le_of_injective ((LinearMap.ker f).liftQ f le_rfl) ?_
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl

/- English proof (translation)
Distinguish the cases in `hF : F = 0`. Conclude with `⟨0, 1, by simp [hF], by simp⟩`. Take `⟨m, hm, hmin⟩` from `Finset.exists_min_image F.support (fun m => addVal O (F.coeff m)) (MvPolynomial.support_nonempty.2 hF)`. Establish `hc : F.coeff m ≠ 0` using `MvPolynomial.mem_support_iff.1 hm`. Establish `hd : MvPolynomial.C (F.coeff m) ∣ F`.

Rewrite using `[MvPolynomial.C_dvd_iff_dvd_coeff]`. Introduce `i`. Distinguish the cases in `hi : i ∈ F.support`. Conclude with `addVal_le_iff_dvd.1 (hmin i hi)`. Rewrite using `[MvPolynomial.notMem_support_iff.1 hi]`.

Conclude with `dvd_zero _`. Take `⟨G, hG⟩` from `hd`. Use `⟨F.coeff m, G, hG, fun h0 => ?_⟩` and prove the remaining obligations. Establish `h1 : F.coeff m = F.coeff m * G.coeff m` using `by conv_lhs => rw [hG]`. Rewrite using `[MvPolynomial.coeff_C_mul]`.

Establish `h2 : G.coeff m = 1`. Apply `mul_left_cancel₀ hc` to reduce the goal to its premises. Rewrite using `[← h1, mul_one]`. Establish `h3` using `congrArg (MvPolynomial.coeff m) h0`. Rewrite `h3` using `[MvPolynomial.coeff_map, h2]`.

Simplify using `at h3`.
-/
theorem exists_C_mul_primitive {σ : Type} (F : MvPolynomial σ O) :
    ∃ (c : O) (G : MvPolynomial σ O), F = MvPolynomial.C c * G ∧
      MvPolynomial.map (IsLocalRing.residue O) G ≠ 0 := by
  classical
  by_cases hF : F = 0
  · exact ⟨0, 1, by simp [hF], by simp⟩
  obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image F.support (fun m => addVal O (F.coeff m))
    (MvPolynomial.support_nonempty.2 hF)
  have hc : F.coeff m ≠ 0 := MvPolynomial.mem_support_iff.1 hm
  have hd : MvPolynomial.C (F.coeff m) ∣ F := by
    rw [MvPolynomial.C_dvd_iff_dvd_coeff]
    intro i
    by_cases hi : i ∈ F.support
    · exact addVal_le_iff_dvd.1 (hmin i hi)
    · rw [MvPolynomial.notMem_support_iff.1 hi]; exact dvd_zero _
  obtain ⟨G, hG⟩ := hd
  refine ⟨F.coeff m, G, hG, fun h0 => ?_⟩
  have h1 : F.coeff m = F.coeff m * G.coeff m := by
    conv_lhs => rw [hG]
    rw [MvPolynomial.coeff_C_mul]
  have h2 : G.coeff m = 1 := by
    apply mul_left_cancel₀ hc
    rw [← h1, mul_one]
  have h3 := congrArg (MvPolynomial.coeff m) h0
  rw [MvPolynomial.coeff_map, h2] at h3
  simp at h3

/- English proof (translation)
Use `choose c G hF hG using fun j => exists_C_mul_primitive (F j)`. Establish `h1 : MvPolynomial.map (IsLocalRing.residue O) (∏ j, G j) ≠ 0`. Rewrite using `[map_prod]`. Conclude with `Finset.prod_ne_zero_iff.2 fun j _ => hG j`. Take `⟨m, hm⟩ : ∃ m, MvPolynomial.coeff m (MvPolynomial.map (IsLocalRing.residue O) (∏ j, G j)) ≠ 0` from `by by_contra! hh`.

Conclude with `h1 (MvPolynomial.ext _ _ fun m => by simpa using hh m)`. Rewrite `hm` using `[MvPolynomial.coeff_map]`. Establish `hu : IsUnit (MvPolynomial.coeff m (∏ j, G j))`. Assume the negation of the conclusion as `hn`. Conclude with `hm ((IsLocalRing.residue_eq_zero_iff _).2 hn)`.

Establish `h2 : (∏ j, F j) = MvPolynomial.C (∏ j, c j) * ∏ j, G j`. Rewrite using `[map_prod, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun j _ => hF j`. Establish `h3` using `h m`. Rewrite `h3` using `[h2, MvPolynomial.coeff_C_mul]`.

Establish `h4 : (∏ j, c j) ∈ I` using `(Ideal.mul_unit_mem_iff_mem I hu).1 h3`. Establish `h5 : Ideal.span {∏ j, c j} ≤ I` using `(Ideal.span_singleton_le_iff_mem I).2 h4`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hF j]`. Use the proof step `simp⟩`.
-/
theorem length_quot_le_of_coeff_prod {σ J : Type} [Fintype J] (F : J → MvPolynomial σ O) (x : J → σ → O)
    (I : Ideal O) (h : ∀ m, MvPolynomial.coeff m (∏ j, F j) ∈ I) :
    Module.length O (O ⧸ I) ≤ ∑ j, addVal O (MvPolynomial.eval (x j) (F j)) := by
  classical
  choose c G hF hG using fun j => exists_C_mul_primitive (F j)
  have h1 : MvPolynomial.map (IsLocalRing.residue O) (∏ j, G j) ≠ 0 := by
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.2 fun j _ => hG j
  obtain ⟨m, hm⟩ : ∃ m, MvPolynomial.coeff m (MvPolynomial.map (IsLocalRing.residue O) (∏ j, G j)) ≠ 0 := by
    by_contra! hh
    exact h1 (MvPolynomial.ext _ _ fun m => by simpa using hh m)
  rw [MvPolynomial.coeff_map] at hm
  have hu : IsUnit (MvPolynomial.coeff m (∏ j, G j)) := by
    by_contra hn
    exact hm ((IsLocalRing.residue_eq_zero_iff _).2 hn)
  have h2 : (∏ j, F j) = MvPolynomial.C (∏ j, c j) * ∏ j, G j := by
    rw [map_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => hF j
  have h3 := h m
  rw [h2, MvPolynomial.coeff_C_mul] at h3
  have h4 : (∏ j, c j) ∈ I := (Ideal.mul_unit_mem_iff_mem I hu).1 h3
  have h5 : Ideal.span {∏ j, c j} ≤ I := (Ideal.span_singleton_le_iff_mem I).2 h4
  calc Module.length O (O ⧸ I) ≤ Module.length O (O ⧸ Ideal.span {∏ j, c j}) :=
        Module.length_le_of_surjective (Submodule.factor h5) (Submodule.factor_surjective h5)
    _ = addVal O (∏ j, c j) := Ring.ord_eq_addVal _
    _ = ∑ j, addVal O (c j) := GlobalTheory.addVal_finset_prod _ _
    _ ≤ _ := Finset.sum_le_sum fun j _ => addVal_le_iff_dvd.2 ⟨MvPolynomial.eval (x j) (G j), by
        rw [hF j]; simp⟩

/- English proof (translation)
Establish `hinj : Function.Injective (algebraMap O (FractionRing O))` using `IsFractionRing.injective O _`. Use `set M' := M.map (algebraMap O (FractionRing O)) with hM'`. Distinguish the cases in `h0 : M.det = 0`. Take `⟨v, hv0, hv⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h0`. Take `⟨i, hi⟩ : ∃ i, v i ≠ 0` from `by by_contra! hh`.

Conclude with `hv0 (funext hh)`. Take `⟨ϖ, hϖ⟩` from `exists_irreducible O`. Establish `key : ∀ n : ℕ, (n : ℕ∞) ≤ Module.length O S`. Introduce `n`. Set `y : ι → FractionRing O` to `fun k => (algebraMap O (FractionRing O) (v i * ϖ ^ n))⁻¹ * algebraMap O (FractionRing O) (v k)`.

Establish `hy : M'.mulVec y = 0`. Establish `: y = (algebraMap O (FractionRing O) (v i * ϖ ^ n))⁻¹ • (algebraMap O (FractionRing O) ∘ v)` using `rfl`. Rewrite using `[this, Matrix.mulVec_smul]`. Use function extensionality and compare the values at `p`. Establish `h1` using `RingHom.map_mulVec (algebraMap O (FractionRing O)) M v p`.

Rewrite `h1` using `[hv]`. Simplify using `only [Pi.smul_apply, hM', ← h1]`. Simplify using the standard rewrite rules. Establish `hyS : π y ∈ S` using `hS y fun p => ⟨0, by rw [hy]; simp⟩`. Establish `h2` using `length_quot_le_of_ker_le' (LinearMap.toSpanSingleton O S ⟨π y, hyS⟩) (Ideal.span {ϖ ^ n}) (by`.

Introduce `a ha`. Establish `h3 : π (a • y) = 0`. Rewrite using `[map_smul]`. Conclude with `congrArg Subtype.val (LinearMap.mem_ker.1 ha)`. Take `⟨b, hb⟩` from `hπ _ h3 i`.

Use `Ideal.mem_span_singleton'.2 ⟨b, hinj ?_⟩` and prove the remaining obligations. Establish `h4 : algebraMap O (FractionRing O) (v i) ≠ 0` using `fun h => hi (hinj (by simpa using h))`. Establish `h5 : algebraMap O (FractionRing O) ϖ ≠ 0` using `fun h => hϖ.ne_zero (hinj (by simpa using h))`. Rewrite using `[map_mul, hb]`. Simplify using `only [y, Pi.smul_apply, Algebra.smul_def, map_mul, map_pow]`.

Use the proof step `field_simp)`. Establish `h6 : Module.length O (O ⧸ Ideal.span {ϖ ^ n}) = addVal O (ϖ ^ n)` using `Ring.ord_eq_addVal _`. Rewrite `h2` using `[h6, addVal_pow, addVal_uniformizer hϖ]`. Simplify using `using h2`. Establish `: Module.length O S = ⊤`.

Assume the negation of the conclusion as `hne`. Take `⟨k, hk⟩` from `ENat.ne_top_iff_exists.1 hne`. Use `key (k + 1)` as an intermediate fact. Rewrite `this` using `[← hk]`. Conclude with `absurd (ENat.coe_le_coe.1 this) (by omega)`.

Rewrite using `[this]`. Conclude with `le_top`. Establish `hdet : IsUnit M'.det`. Establish `: M'.det = algebraMap O (FractionRing O) M.det` using `(RingHom.map_det _ M).symm`. Rewrite using `[this]`.

Conclude with `Ne.isUnit fun h => h0 (hinj (by simpa using h))`. Set `φ : (ι → O) →ₗ[O] (ι → FractionRing O)` to `((M'⁻¹).mulVecLin.restrictScalars O).comp (LinearMap.compLeft (Algebra.linearMap O (FractionRing O)) ι)`. Establish `hφ : ∀ u, M'.mulVec (φ u) = algebraMap O (FractionRing O) ∘ u`. Introduce `u`. Express the relevant statement in the definitionally equal form `M'.mulVec ((M'⁻¹).mulVec (algebraMap O (FractionRing O) ∘ u)) = _`.

Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]`. Establish `hφS : ∀ u, (π.comp φ) u ∈ S` using `fun u => hS (φ u) fun p => ⟨u p, by rw [hφ]; rfl⟩`. Rewrite using `[← GlobalTheory.length_quotient_range_mulVecLin_eq_addVal_det]`. Use `length_quot_le_of_ker_le' (LinearMap.codRestrict S (π.comp φ) hφS) _ ?_` and prove the remaining obligations. Introduce `u hu`.

Establish `h3 : π (φ u) = 0` using `congrArg Subtype.val (LinearMap.mem_ker.1 hu)`. Use `choose w hw using hπ _ h3`. Use `⟨w, funext fun p => hinj ?_⟩` and prove the remaining obligations. Establish `h4 : φ u = algebraMap O (FractionRing O) ∘ w` using `funext fun i => (hw i).symm`. Establish `h5` using `congrFun (hφ u) p`.

Rewrite `h5` using `[h4]`. Rewrite using `[Matrix.mulVecLin_apply, RingHom.map_mulVec]`. Conclude with `h5`.
-/
theorem addVal_det_le_length {ι V : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module O V]
    (M : Matrix ι ι O) (π : (ι → FractionRing O) →ₗ[O] V)
    (hπ : ∀ y, π y = 0 → ∀ i, ∃ a, algebraMap O (FractionRing O) a = y i) (S : Submodule O V)
    (hS : ∀ y, (∀ p, ∃ a, algebraMap O (FractionRing O) a =
      (M.map (algebraMap O (FractionRing O))).mulVec y p) → π y ∈ S) :
    addVal O M.det ≤ Module.length O S := by
  have hinj : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective O _
  set M' := M.map (algebraMap O (FractionRing O)) with hM'
  by_cases h0 : M.det = 0
  · obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra! hh
      exact hv0 (funext hh)
    obtain ⟨ϖ, hϖ⟩ := exists_irreducible O
    have key : ∀ n : ℕ, (n : ℕ∞) ≤ Module.length O S := by
      intro n
      let y : ι → FractionRing O := fun k =>
        (algebraMap O (FractionRing O) (v i * ϖ ^ n))⁻¹ * algebraMap O (FractionRing O) (v k)
      have hy : M'.mulVec y = 0 := by
        have : y = (algebraMap O (FractionRing O) (v i * ϖ ^ n))⁻¹ • (algebraMap O (FractionRing O) ∘ v) := rfl
        rw [this, Matrix.mulVec_smul]
        funext p
        have h1 := RingHom.map_mulVec (algebraMap O (FractionRing O)) M v p
        rw [hv] at h1
        simp only [Pi.smul_apply, hM', ← h1]
        simp
      have hyS : π y ∈ S := hS y fun p => ⟨0, by rw [hy]; simp⟩
      have h2 := length_quot_le_of_ker_le' (LinearMap.toSpanSingleton O S ⟨π y, hyS⟩)
        (Ideal.span {ϖ ^ n}) (by
          intro a ha
          have h3 : π (a • y) = 0 := by
            rw [map_smul]
            exact congrArg Subtype.val (LinearMap.mem_ker.1 ha)
          obtain ⟨b, hb⟩ := hπ _ h3 i
          refine Ideal.mem_span_singleton'.2 ⟨b, hinj ?_⟩
          have h4 : algebraMap O (FractionRing O) (v i) ≠ 0 := fun h => hi (hinj (by simpa using h))
          have h5 : algebraMap O (FractionRing O) ϖ ≠ 0 := fun h => hϖ.ne_zero (hinj (by simpa using h))
          rw [map_mul, hb]
          simp only [y, Pi.smul_apply, Algebra.smul_def, map_mul, map_pow]
          field_simp)
      have h6 : Module.length O (O ⧸ Ideal.span {ϖ ^ n}) = addVal O (ϖ ^ n) := Ring.ord_eq_addVal _
      rw [h6, addVal_pow, addVal_uniformizer hϖ] at h2
      simpa using h2
    have : Module.length O S = ⊤ := by
      by_contra hne
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hne
      have := key (k + 1)
      rw [← hk] at this
      exact absurd (ENat.coe_le_coe.1 this) (by omega)
    rw [this]; exact le_top
  · have hdet : IsUnit M'.det := by
      have : M'.det = algebraMap O (FractionRing O) M.det := (RingHom.map_det _ M).symm
      rw [this]
      exact Ne.isUnit fun h => h0 (hinj (by simpa using h))
    let φ : (ι → O) →ₗ[O] (ι → FractionRing O) :=
      ((M'⁻¹).mulVecLin.restrictScalars O).comp (LinearMap.compLeft (Algebra.linearMap O (FractionRing O)) ι)
    have hφ : ∀ u, M'.mulVec (φ u) = algebraMap O (FractionRing O) ∘ u := by
      intro u
      change M'.mulVec ((M'⁻¹).mulVec (algebraMap O (FractionRing O) ∘ u)) = _
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
    have hφS : ∀ u, (π.comp φ) u ∈ S := fun u => hS (φ u) fun p => ⟨u p, by rw [hφ]; rfl⟩
    rw [← GlobalTheory.length_quotient_range_mulVecLin_eq_addVal_det]
    refine length_quot_le_of_ker_le' (LinearMap.codRestrict S (π.comp φ) hφS) _ ?_
    intro u hu
    have h3 : π (φ u) = 0 := congrArg Subtype.val (LinearMap.mem_ker.1 hu)
    choose w hw using hπ _ h3
    refine ⟨w, funext fun p => hinj ?_⟩
    have h4 : φ u = algebraMap O (FractionRing O) ∘ w := funext fun i => (hw i).symm
    have h5 := congrFun (hφ u) p
    rw [h4] at h5
    rw [Matrix.mulVecLin_apply, RingHom.map_mulVec]
    exact h5

omit [IsDiscreteValuationRing O] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem matKO_mk {k : ℕ} (A : Matrix (Fin k) (Fin k) O) (y : Fin k → FractionRing O) :
    matKO A (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ((A.map (algebraMap O (FractionRing O))).mulVec y) := rfl

omit [IsDiscreteValuationRing O] in
/- English proof (translation)
Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, rfl⟩ i`. Conclude with `⟨u i, rfl⟩`. Introduce `h choose u hu using h`.

Conclude with `⟨u, funext hu⟩`.
-/
theorem mk_eq_zero_iff {k : ℕ} (y : Fin k → FractionRing O) :
    (Submodule.Quotient.mk y : KOG O k) = 0 ↔ ∀ i, ∃ a, algebraMap O (FractionRing O) a = y i := by
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨u, rfl⟩ i
    exact ⟨u i, rfl⟩
  · intro h
    choose u hu using h
    exact ⟨u, funext hu⟩

/- English proof (translation)
Take `⟨n, snf⟩` from `N.smithNormalForm (Pi.basisFun O ι)`. Use `⟨Function.extend snf.f (fun i => (snf.bN i : ι → O)) 0, fun p => ?_, fun P hP => ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : ∃ i, snf.f i = p`. Take `⟨i, rfl⟩` from `h`. Rewrite using `[snf.f.injective.extend_apply]`.

Conclude with `(snf.bN i).2`. Rewrite using `[Function.extend_apply' _ _ _ h]`. Conclude with `N.zero_mem`. Introduce `v hv`. Establish `h1 : (⟨v, hv⟩ : N) ∈ P.comap N.subtype`.

Establish `: Submodule.span O (Set.range snf.bN) ≤ P.comap N.subtype`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Use `hP (snf.f i)` as an intermediate fact. Rewrite `this` using `[snf.f.injective.extend_apply]`.

Conclude with `this`. Conclude with `this (by rw [snf.bN.span_eq]; trivial)`. Conclude with `h1`.
-/
theorem exists_family_span {ι : Type} [Fintype ι] [DecidableEq ι] (N : Submodule O (ι → O)) :
    ∃ r : ι → ι → O, (∀ p, r p ∈ N) ∧ ∀ P : Submodule O (ι → O), (∀ p, r p ∈ P) → N ≤ P := by
  classical
  obtain ⟨n, snf⟩ := N.smithNormalForm (Pi.basisFun O ι)
  refine ⟨Function.extend snf.f (fun i => (snf.bN i : ι → O)) 0, fun p => ?_, fun P hP => ?_⟩
  · by_cases h : ∃ i, snf.f i = p
    · obtain ⟨i, rfl⟩ := h
      rw [snf.f.injective.extend_apply]
      exact (snf.bN i).2
    · rw [Function.extend_apply' _ _ _ h]
      exact N.zero_mem
  · intro v hv
    have h1 : (⟨v, hv⟩ : N) ∈ P.comap N.subtype := by
      have : Submodule.span O (Set.range snf.bN) ≤ P.comap N.subtype := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        have := hP (snf.f i)
        rw [snf.f.injective.extend_apply] at this
        exact this
      exact this (by rw [snf.bN.span_eq]; trivial)
    exact h1

/- English proof (translation)
Set `N : Submodule O (Fin g × Fin d → O)` to `{ carrier := {v | ∀ a, ∃ θ ∈ Rel, ∀ q a' b, ψ (θ q) a' b = if a' = a then v (q, b) else 0} add_mem' := by`. Introduce `v w hv hw a`. Take `⟨θ, hθ, h⟩` from `hv a`. Take `⟨θ', hθ', h'⟩` from `hw a`. Use `⟨θ + θ', Rel.add_mem hθ hθ', fun q a' b => ?_⟩` and prove the remaining obligations.

Rewrite using `[Pi.add_apply, map_add, Matrix.add_apply, h, h']`. Apply the tactic sequence `split_ifs <;> simp`. Use the proof step `zero_mem' := fun a => ⟨0, Rel.zero_mem, fun q a' b => by simp⟩`. Use the proof step `smul_mem' := by`. Introduce `c v hv a`.

Take `⟨θ, hθ, h⟩` from `hv a`. Use `⟨c • θ, Rel.smul_of_tower_mem c hθ, fun q a' b => ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, map_smul, Matrix.smul_apply, h]`. Apply the tactic sequence `split_ifs <;> simp }`. Establish `hrow : ∀ θ ∈ Rel, ∀ a₀, (fun qb : Fin g × Fin d => ψ (θ qb.1) a₀ qb.2) ∈ N`.

Introduce `θ hθ a₀ a`. Take `⟨e, he⟩` from `hψ (Matrix.single a a₀ 1)`. Use `⟨e • θ, Rel.smul_mem e hθ, fun q a' b => ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, smul_eq_mul, map_mul, he]`. Use `split_ifs with h`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Conclude with `Matrix.single_mul_apply_of_ne _ _ _ _ _ h _`. Take `⟨r, hrN, hr⟩` from `exists_family_span N`. Use `choose θ hθ hθr using fun (p : Fin g) (a : Fin d) => hrN (p, a) a`.

Establish `hM : (Matrix.of fun (pa qb : Fin g × Fin d) => ψ ((∑ a, θ pa.1 a) qb.1) pa.2 qb.2) = Matrix.of r`. Use extensionality with `⟨p, a⟩ ⟨q, b⟩`. Simplify using `[Finset.sum_apply, map_sum, Matrix.sum_apply, hθr]`. Use `⟨fun p => ∑ a, θ p a, fun p => Rel.sum_mem fun a _ => hθ p a, ?_⟩` and prove the remaining obligations. Rewrite using `[hM]`.

Set `π : (Fin g × Fin d → FractionRing O) →ₗ[O] (Fin g → KOG O d)` to `LinearMap.pi fun q => (stdG O (FractionRing O) d).mkQ.comp (LinearMap.funLeft O (FractionRing O) fun b => (q, b))`. Establish `hπ : ∀ y q, π y q = Submodule.Quotient.mk (fun b => y (q, b))` using `fun _ _ => rfl`. Use `addVal_det_le_length (Matrix.of r) π (fun y hy i => ?_) _ (fun y hy => ?_)` and prove the remaining obligations. Use `congrFun hy i.1` as an intermediate fact. Rewrite `this` using `[hπ]`.

Conclude with `(mk_eq_zero_iff _).1 this i.2`. Set `P : Submodule O (Fin g × Fin d → O)` to `{ carrier := {v | ∃ a, algebraMap O (FractionRing O) a = ∑ i, algebraMap O (FractionRing O) (v i) * y i} add_mem' := by`. Introduce and unpack `v w ⟨a, ha⟩ ⟨b, hb⟩`. Conclude with `⟨a + b, by simp [ha, hb, add_mul, Finset.sum_add_distrib]⟩`. Use the proof step `zero_mem' := ⟨0, by simp⟩`.

Use the proof step `smul_mem' := by`. Introduce and unpack `c v ⟨a, ha⟩`. Conclude with `⟨c * a, by simp [ha, Finset.mul_sum, mul_assoc]⟩ }`. Establish `hNP : N ≤ P` using `hr P fun p => hy p`. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker]`.

Introduce `t ht`. Establish `h1 : (∑ q : Fin g, (matKO (ψ (t q))).comp (LinearMap.proj q : (Fin g → KOG O d) →ₗ[O] KOG O d)) (π y) = (stdG O (FractionRing O) d).mkQ (∑ q, ((ψ (t q)).map (algebraMap O (FractionRing O))).mulVec fun b => y (q, b))`. Rewrite using `[LinearMap.sum_apply, map_sum]`. Both sides reduce to the same expression. Rewrite using `[h1, Submodule.mkQ_apply, mk_eq_zero_iff]`.

Introduce `a`. Take `⟨c, hc⟩` from `hNP (hrow t ht a)`. Use `⟨c, ?_⟩` and prove the remaining obligations. Rewrite using `[hc, Fintype.sum_prod_type, Finset.sum_apply]`. Both sides reduce to the same expression.
-/
theorem exists_relations {A : Type} [Ring A] [Algebra O A] {d : ℕ} (ψ : A →ₐ[O] Matrix (Fin d) (Fin d) O)
    (hψ : Function.Surjective ψ) {g : ℕ} (Rel : Submodule A (Fin g → A)) :
    ∃ Θ : Fin g → Fin g → A, (∀ p, Θ p ∈ Rel) ∧
      addVal O (Matrix.det (Matrix.of fun (pa qb : Fin g × Fin d) => ψ (Θ pa.1 qb.1) pa.2 qb.2)) ≤
        Module.length O ↥(⨅ θ ∈ Rel, LinearMap.ker (∑ q : Fin g, (matKO (ψ (θ q))).comp
          (LinearMap.proj q : (Fin g → KOG O d) →ₗ[O] KOG O d))) := by
  classical
  let N : Submodule O (Fin g × Fin d → O) :=
    { carrier := {v | ∀ a, ∃ θ ∈ Rel, ∀ q a' b, ψ (θ q) a' b = if a' = a then v (q, b) else 0}
      add_mem' := by
        intro v w hv hw a
        obtain ⟨θ, hθ, h⟩ := hv a
        obtain ⟨θ', hθ', h'⟩ := hw a
        refine ⟨θ + θ', Rel.add_mem hθ hθ', fun q a' b => ?_⟩
        rw [Pi.add_apply, map_add, Matrix.add_apply, h, h']
        split_ifs <;> simp
      zero_mem' := fun a => ⟨0, Rel.zero_mem, fun q a' b => by simp⟩
      smul_mem' := by
        intro c v hv a
        obtain ⟨θ, hθ, h⟩ := hv a
        refine ⟨c • θ, Rel.smul_of_tower_mem c hθ, fun q a' b => ?_⟩
        rw [Pi.smul_apply, map_smul, Matrix.smul_apply, h]
        split_ifs <;> simp }
  have hrow : ∀ θ ∈ Rel, ∀ a₀, (fun qb : Fin g × Fin d => ψ (θ qb.1) a₀ qb.2) ∈ N := by
    intro θ hθ a₀ a
    obtain ⟨e, he⟩ := hψ (Matrix.single a a₀ 1)
    refine ⟨e • θ, Rel.smul_mem e hθ, fun q a' b => ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, map_mul, he]
    split_ifs with h
    · subst h
      simp
    · exact Matrix.single_mul_apply_of_ne _ _ _ _ _ h _
  obtain ⟨r, hrN, hr⟩ := exists_family_span N
  choose θ hθ hθr using fun (p : Fin g) (a : Fin d) => hrN (p, a) a
  have hM : (Matrix.of fun (pa qb : Fin g × Fin d) => ψ ((∑ a, θ pa.1 a) qb.1) pa.2 qb.2) = Matrix.of r := by
    ext ⟨p, a⟩ ⟨q, b⟩
    simp [Finset.sum_apply, map_sum, Matrix.sum_apply, hθr]
  refine ⟨fun p => ∑ a, θ p a, fun p => Rel.sum_mem fun a _ => hθ p a, ?_⟩
  rw [hM]
  let π : (Fin g × Fin d → FractionRing O) →ₗ[O] (Fin g → KOG O d) :=
    LinearMap.pi fun q => (stdG O (FractionRing O) d).mkQ.comp
      (LinearMap.funLeft O (FractionRing O) fun b => (q, b))
  have hπ : ∀ y q, π y q = Submodule.Quotient.mk (fun b => y (q, b)) := fun _ _ => rfl
  refine addVal_det_le_length (Matrix.of r) π (fun y hy i => ?_) _ (fun y hy => ?_)
  · have := congrFun hy i.1
    rw [hπ] at this
    exact (mk_eq_zero_iff _).1 this i.2
  · let P : Submodule O (Fin g × Fin d → O) :=
      { carrier := {v | ∃ a, algebraMap O (FractionRing O) a = ∑ i, algebraMap O (FractionRing O) (v i) * y i}
        add_mem' := by
          rintro v w ⟨a, ha⟩ ⟨b, hb⟩
          exact ⟨a + b, by simp [ha, hb, add_mul, Finset.sum_add_distrib]⟩
        zero_mem' := ⟨0, by simp⟩
        smul_mem' := by
          rintro c v ⟨a, ha⟩
          exact ⟨c * a, by simp [ha, Finset.mul_sum, mul_assoc]⟩ }
    have hNP : N ≤ P := hr P fun p => hy p
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    intro t ht
    have h1 : (∑ q : Fin g, (matKO (ψ (t q))).comp
          (LinearMap.proj q : (Fin g → KOG O d) →ₗ[O] KOG O d)) (π y) =
        (stdG O (FractionRing O) d).mkQ
          (∑ q, ((ψ (t q)).map (algebraMap O (FractionRing O))).mulVec fun b => y (q, b)) := by
      rw [LinearMap.sum_apply, map_sum]
      rfl
    rw [h1, Submodule.mkQ_apply, mk_eq_zero_iff]
    intro a
    obtain ⟨c, hc⟩ := hNP (hrow t ht a)
    refine ⟨c, ?_⟩
    rw [hc, Fintype.sum_prod_type, Finset.sum_apply]
    rfl

/- English proof (translation)
Introduce `O _ _ _ A _ _ J _ d ψ hψ g Rel I hI`. Use `choose Θ hΘ hle using fun j => exists_relations (ψ j) (hψ j) Rel`. Set `e` to `Fintype.equivFin J`. Establish `h1` using `length_quot_le_of_coeff_prod _ (fun j => Pi.single (e j) (1 : O)) I (hI (Fintype.card J) (fun k => Θ (e.symm k)) fun k p => hΘ _ p)`. Use `h1.trans (Finset.sum_le_sum fun j _ => le_trans (le_of_eq ?_) (hle j))` and prove the remaining obligations.

Use `congr 1`. Rewrite using `[RingHom.map_det]`. Use `congr 1`. Use extensionality with `pa qb`. Simplify using `[Pi.single_apply]`.
-/
theorem length_quot_le_sum_length : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (A : Type) [Ring A] [Algebra O A] (J : Type) [Fintype J] (d : J → ℕ) (ψ : ∀ j, A →ₐ[O] Matrix (Fin (d j)) (Fin (d j)) O), (∀ j, Function.Surjective (ψ j)) → ∀ (g : ℕ) (Rel : Submodule A (Fin g → A)) (I : Ideal O), (∀ (n : ℕ) (θ : Fin n → Fin g → Fin g → A), (∀ k p, θ k p ∈ Rel) → ∀ m : Fin n →₀ ℕ, MvPolynomial.coeff m (∏ j, Matrix.det (Matrix.of fun (pa qb : Fin g × Fin (d j)) => ∑ k, (MvPolynomial.X k : MvPolynomial (Fin n) O) * MvPolynomial.C (ψ j (θ k pa.1 qb.1) pa.2 qb.2))) ∈ I) → Module.length O (O ⧸ I) ≤ ∑ j, Module.length O ↥(⨅ θ ∈ Rel, LinearMap.ker (∑ q : Fin g, (matKO (ψ j (θ q))).comp (LinearMap.proj q : (Fin g → KOG O (d j)) →ₗ[O] KOG O (d j)))) := by
  intro O _ _ _ A _ _ J _ d ψ hψ g Rel I hI
  classical
  choose Θ hΘ hle using fun j => exists_relations (ψ j) (hψ j) Rel
  let e := Fintype.equivFin J
  have h1 := length_quot_le_of_coeff_prod _ (fun j => Pi.single (e j) (1 : O)) I
    (hI (Fintype.card J) (fun k => Θ (e.symm k)) fun k p => hΘ _ p)
  refine h1.trans (Finset.sum_le_sum fun j _ => le_trans (le_of_eq ?_) (hle j))
  congr 1
  rw [RingHom.map_det]
  congr 1
  ext pa qb
  simp [Pi.single_apply]

end GlobalTheory.DetGen
