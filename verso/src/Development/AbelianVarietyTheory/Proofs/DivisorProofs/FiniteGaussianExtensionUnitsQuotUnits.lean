import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEisensteinConstantTermPartDifferentiableOn
import ReciprocityTheory.Chebotarev.EulerSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleXSqAddOne
open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.GaussExt.UnitIdx

variable (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F]

/- English proof (translation)
Simplify using `only [map_add, map_pow, aeval_X, map_one, neg_sq, ii_sq F]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem aeval_neg_ii : aeval (-ii F) (X ^ 2 + 1 : F[X]) = 0 := by
  simp only [map_add, map_pow, aeval_X, map_one, neg_sq, ii_sq F]; ring

def conj : Ext F →ₐ[F] Ext F := AdjoinRoot.liftAlgHom (X ^ 2 + 1 : F[X]) (Algebra.ofId F (Ext F)) (-ii F)
  (by have := aeval_neg_ii F; rwa [aeval_def] at this)

/- English proof (translation)
Simplify using `[conj, ii]`.
-/
theorem conj_ii : conj F (ii F) = -ii F := by
  simp [conj, ii]

/- English proof (translation)
The claim follows from `(conj F).commutes a`.
-/
theorem conj_algebraMap (a : F) : conj F (algebraMap F (Ext F) a) = algebraMap F (Ext F) a :=
  (conj F).commutes a

/- English proof (translation)
Take `⟨p, rfl⟩` from `AdjoinRoot.mk_surjective x`. Establish `hm : (X ^ 2 + 1 : F[X]).Monic` using `by monicity!`. Establish `hdeg : (X ^ 2 + 1 : F[X]).natDegree = 2` using `by compute_degree!`. Use `set r := p %ₘ (X ^ 2 + 1 : F[X])`. Establish `hr : AdjoinRoot.mk (X ^ 2 + 1 : F[X]) p = AdjoinRoot.mk _ r`.

Rewrite using `[AdjoinRoot.mk_eq_mk]`. Conclude with `⟨p /ₘ (X ^ 2 + 1), by have := modByMonic_add_div p (X ^ 2 + 1 : F[X]); linear_combination -this⟩`. Establish `hrd : r.natDegree ≤ 1`. Use `natDegree_modByMonic_lt p hm (by intro h; have := congrArg natDegree h; rw [hdeg] at this; simp at this)` as an intermediate fact. Express the relevant statement in the definitionally equal form `(p %ₘ (X ^ 2 + 1 : F[X])).natDegree ≤ 1`.

Use linear arithmetic over natural numbers and integers. Use `⟨r.coeff 0, r.coeff 1, ?_⟩` and prove the remaining obligations. Rewrite using `[hr, eq_X_add_C_of_natDegree_le_one hrd]`. Simplify using `[ii, AdjoinRoot.algebraMap_eq, add_comm]`.
-/
theorem exists_repr (x : Ext F) : ∃ a b : F, x = algebraMap F (Ext F) a + algebraMap F (Ext F) b * ii F := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  have hm : (X ^ 2 + 1 : F[X]).Monic := by monicity!
  have hdeg : (X ^ 2 + 1 : F[X]).natDegree = 2 := by compute_degree!
  set r := p %ₘ (X ^ 2 + 1 : F[X])
  have hr : AdjoinRoot.mk (X ^ 2 + 1 : F[X]) p = AdjoinRoot.mk _ r := by
    rw [AdjoinRoot.mk_eq_mk]
    exact ⟨p /ₘ (X ^ 2 + 1), by have := modByMonic_add_div p (X ^ 2 + 1 : F[X]); linear_combination -this⟩
  have hrd : r.natDegree ≤ 1 := by
    have := natDegree_modByMonic_lt p hm (by intro h; have := congrArg natDegree h; rw [hdeg] at this; simp at this)
    change (p %ₘ (X ^ 2 + 1 : F[X])).natDegree ≤ 1
    omega
  refine ⟨r.coeff 0, r.coeff 1, ?_⟩
  rw [hr, eq_X_add_C_of_natDegree_le_one hrd]
  simp [ii, AdjoinRoot.algebraMap_eq, add_comm]

/- English proof (translation)
Introduce `h`. Use `ii_sq F` as an intermediate fact. Rewrite `this` using `[h]`. Evaluate the numerical expressions using `at this`.
-/
theorem ii_ne_zero : ii F ≠ 0 := by
  intro h
  have := ii_sq F
  rw [h] at this
  norm_num at this

/- English proof (translation)
Take `⟨a, b, rfl⟩` from `exists_repr F x`. Use `⟨a, ?_⟩` and prove the remaining obligations. Simplify using `only [map_add, map_mul, conj_algebraMap, conj_ii] at hx`. Establish `h2 : (2 : Ext F) * algebraMap F (Ext F) b * ii F = 0` using `by linear_combination -hx`. Establish `hb : algebraMap F (Ext F) b = 0`.

Break down `mul_eq_zero.1 h2 with h | h` into its components or cases. Break down `mul_eq_zero.1 h with h | h` into its components or cases. Conclude with `absurd h two_ne_zero`. Conclude with `h`. Conclude with `absurd h (ii_ne_zero F)`.

Rewrite using `[hb]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mem_range_of_conj_eq (x : Ext F) (hx : conj F x = x) : ∃ a : F, algebraMap F (Ext F) a = x := by
  obtain ⟨a, b, rfl⟩ := exists_repr F x
  refine ⟨a, ?_⟩
  simp only [map_add, map_mul, conj_algebraMap, conj_ii] at hx
  have h2 : (2 : Ext F) * algebraMap F (Ext F) b * ii F = 0 := by linear_combination -hx
  have hb : algebraMap F (Ext F) b = 0 := by
    rcases mul_eq_zero.1 h2 with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h two_ne_zero
      · exact h
    · exact absurd h (ii_ne_zero F)
  rw [hb]; ring

/- English proof (translation)
Establish `key : φ.comp (conj F).toRingHom = (starRingEnd ℂ).comp φ`. Apply `AdjoinRoot.ringHom_ext` to reduce the goal to its premises. Use extensionality with `a`. Establish `hre` using `NumberField.IsTotallyReal.complexEmbedding_isReal (φ.comp (algebraMap F (Ext F)))`. Establish `h1` using `hre.coe_embedding_apply a`.

Simplify using `only [RingHom.comp_apply, AdjoinRoot.algebraMap_eq] at h1 ⊢`. Establish `h3 : (conj F).toRingHom (AdjoinRoot.of _ a) = AdjoinRoot.of _ a`. Rewrite using `[← AdjoinRoot.algebraMap_eq]`. Conclude with `conj_algebraMap F a`. Rewrite using `[h3, ← h1, Complex.conj_ofReal]`.

Establish `h` using `congrArg φ (ii_sq F)`. Simplify using `only [map_pow, map_neg, map_one] at h`. Establish `hc : (φ (ii F) - I) * (φ (ii F) + I) = 0` using `by linear_combination h - I_sq`. Simplify using `only [RingHom.comp_apply]`. Express the relevant statement in the definitionally equal form `φ (conj F (ii F)) = starRingEnd ℂ (φ (ii F))`.

Rewrite using `[conj_ii, map_neg]`. Break down `mul_eq_zero.1 hc with h' | h'` into its components or cases. Rewrite using `[sub_eq_zero.1 h']`. Simplify using the standard rewrite rules. Rewrite using `[eq_neg_of_add_eq_zero_left h']`.

Simplify using the standard rewrite rules. Conclude with `congrArg (fun f => f x) key`.
-/
theorem embedding_conj (φ : Ext F →+* ℂ) (x : Ext F) : φ (conj F x) = starRingEnd ℂ (φ x) := by
  have key : φ.comp (conj F).toRingHom = (starRingEnd ℂ).comp φ := by
    apply AdjoinRoot.ringHom_ext
    · ext a
      have hre := NumberField.IsTotallyReal.complexEmbedding_isReal (φ.comp (algebraMap F (Ext F)))
      have h1 := hre.coe_embedding_apply a
      simp only [RingHom.comp_apply, AdjoinRoot.algebraMap_eq] at h1 ⊢
      have h3 : (conj F).toRingHom (AdjoinRoot.of _ a) = AdjoinRoot.of _ a := by
        rw [← AdjoinRoot.algebraMap_eq]; exact conj_algebraMap F a
      rw [h3, ← h1, Complex.conj_ofReal]
    · have h := congrArg φ (ii_sq F)
      simp only [map_pow, map_neg, map_one] at h
      have hc : (φ (ii F) - I) * (φ (ii F) + I) = 0 := by linear_combination h - I_sq
      simp only [RingHom.comp_apply]
      change φ (conj F (ii F)) = starRingEnd ℂ (φ (ii F))
      rw [conj_ii, map_neg]
      rcases mul_eq_zero.1 hc with h' | h'
      · rw [sub_eq_zero.1 h']; simp
      · rw [eq_neg_of_add_eq_zero_left h']; simp
  exact congrArg (fun f => f x) key

/- English proof (translation)
The claim follows from `hx.map ((conj F).toRingHom.toIntAlgHom)`.
-/
theorem isIntegral_conj {x : Ext F} (hx : IsIntegral ℤ x) : IsIntegral ℤ (conj F x) :=
  hx.map ((conj F).toRingHom.toIntAlgHom)

/- English proof (translation)
Use `set x : Ext F := ((u : 𝓞 (Ext F)) : Ext F)`. Use `set y : Ext F := (((u⁻¹ : (𝓞 (Ext F))ˣ) : 𝓞 (Ext F)) : Ext F)`. Establish `hxy : x * y = 1`. Use `congrArg (fun z : 𝓞 (Ext F) => (z : Ext F)) u.mul_inv` as an intermediate fact. Simplify `this` using `[x, y]`.

Establish `hx0 : x ≠ 0` using `left_ne_zero_of_mul_eq_one hxy`. Establish `hint : IsIntegral ℤ (x * conj F y)` using `(RingOfIntegers.isIntegral_coe _).mul (isIntegral_conj F (RingOfIntegers.isIntegral_coe _))`. Take `⟨m, hm, hpow⟩` from `NumberField.Embeddings.pow_eq_one_of_norm_eq_one (Ext F) ℂ hint fun φ => by`. Establish `h1 : φ x * φ y = 1` using `by rw [← map_mul, hxy, map_one]`. Rewrite using `[map_mul, embedding_conj, norm_mul, Complex.norm_conj, ← norm_mul, h1, norm_one]`.

Use `⟨m, hm, ?_⟩` and prove the remaining obligations. Establish `hcxy : conj F x * conj F y = 1` using `by rw [← map_mul, hxy, map_one]`. Establish `hfix : conj F (x ^ m) = x ^ m`. Establish `: (x * conj F y) ^ m * (conj F x) ^ m = (conj F x) ^ m` using `by rw [hpow, one_mul]`. Rewrite using `[map_pow, ← this, ← mul_pow, mul_assoc, mul_comm (conj F y), hcxy, mul_one]`.

Take `⟨a, ha⟩` from `mem_range_of_conj_eq F _ hfix`. Establish `hai : IsIntegral ℤ a`. Use `(isIntegral_algebraMap_iff (algebraMap F (Ext F)).injective).1 ?_` and prove the remaining obligations. Rewrite using `[ha]`. Conclude with `(RingOfIntegers.isIntegral_coe _).pow m`.

Establish `hfix' : conj F (y ^ m) = y ^ m`. Establish `e : y ^ m = (x ^ m)⁻¹` using `by rw [← inv_pow, inv_eq_of_mul_eq_one_right hxy]`. Rewrite using `[e, map_inv₀, hfix]`. Take `⟨b, hb⟩` from `mem_range_of_conj_eq F _ hfix'`. Establish `hbi : IsIntegral ℤ b`.

Use `(isIntegral_algebraMap_iff (algebraMap F (Ext F)).injective).1 ?_` and prove the remaining obligations. Rewrite using `[hb]`. Conclude with `(RingOfIntegers.isIntegral_coe _).pow m`. Establish `hab : a * b = 1`. Apply `(algebraMap F (Ext F)).injective` to reduce the goal to its premises.

Rewrite using `[map_mul, ha, hb, ← mul_pow, hxy, one_pow, map_one]`. Set `A : 𝓞 F` to `⟨a, hai⟩`. Set `B : 𝓞 F` to `⟨b, hbi⟩`. Establish `hAB : A * B = 1` using `RingOfIntegers.ext hab`. Use `⟨⟨A, B, hAB, by rw [mul_comm]; exact hAB⟩, ?_⟩` and prove the remaining obligations.

Apply `Units.ext` to reduce the goal to its premises. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Simplify using `only [RingHom.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_coe, Units.val_pow_eq_pow_val]`. Rewrite using `[show (((u : 𝓞 (Ext F)) ^ m : 𝓞 (Ext F)) : Ext F) = x ^ m by simp [x], ← ha]`. Both sides reduce to the same expression.
-/
theorem pow_mem_range (u : (𝓞 (Ext F))ˣ) :
    ∃ m : ℕ, 0 < m ∧ u ^ m ∈ (Units.map (algebraMap (𝓞 F) (𝓞 (Ext F))).toMonoidHom).range := by
  set x : Ext F := ((u : 𝓞 (Ext F)) : Ext F)
  set y : Ext F := (((u⁻¹ : (𝓞 (Ext F))ˣ) : 𝓞 (Ext F)) : Ext F)
  have hxy : x * y = 1 := by
    have := congrArg (fun z : 𝓞 (Ext F) => (z : Ext F)) u.mul_inv
    simpa [x, y] using this
  have hx0 : x ≠ 0 := left_ne_zero_of_mul_eq_one hxy
  have hint : IsIntegral ℤ (x * conj F y) :=
    (RingOfIntegers.isIntegral_coe _).mul (isIntegral_conj F (RingOfIntegers.isIntegral_coe _))
  obtain ⟨m, hm, hpow⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one (Ext F) ℂ hint fun φ => by
    have h1 : φ x * φ y = 1 := by rw [← map_mul, hxy, map_one]
    rw [map_mul, embedding_conj, norm_mul, Complex.norm_conj, ← norm_mul, h1, norm_one]
  refine ⟨m, hm, ?_⟩

  have hcxy : conj F x * conj F y = 1 := by rw [← map_mul, hxy, map_one]
  have hfix : conj F (x ^ m) = x ^ m := by
    have : (x * conj F y) ^ m * (conj F x) ^ m = (conj F x) ^ m := by rw [hpow, one_mul]
    rw [map_pow, ← this, ← mul_pow, mul_assoc, mul_comm (conj F y), hcxy, mul_one]
  obtain ⟨a, ha⟩ := mem_range_of_conj_eq F _ hfix
  have hai : IsIntegral ℤ a := by
    refine (isIntegral_algebraMap_iff (algebraMap F (Ext F)).injective).1 ?_
    rw [ha]; exact (RingOfIntegers.isIntegral_coe _).pow m

  have hfix' : conj F (y ^ m) = y ^ m := by
    have e : y ^ m = (x ^ m)⁻¹ := by rw [← inv_pow, inv_eq_of_mul_eq_one_right hxy]
    rw [e, map_inv₀, hfix]
  obtain ⟨b, hb⟩ := mem_range_of_conj_eq F _ hfix'
  have hbi : IsIntegral ℤ b := by
    refine (isIntegral_algebraMap_iff (algebraMap F (Ext F)).injective).1 ?_
    rw [hb]; exact (RingOfIntegers.isIntegral_coe _).pow m
  have hab : a * b = 1 := by
    apply (algebraMap F (Ext F)).injective
    rw [map_mul, ha, hb, ← mul_pow, hxy, one_pow, map_one]
  let A : 𝓞 F := ⟨a, hai⟩
  let B : 𝓞 F := ⟨b, hbi⟩
  have hAB : A * B = 1 := RingOfIntegers.ext hab
  refine ⟨⟨A, B, hAB, by rw [mul_comm]; exact hAB⟩, ?_⟩
  apply Units.ext
  apply RingOfIntegers.ext
  simp only [RingHom.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_coe, Units.val_pow_eq_pow_val]
  rw [show (((u : 𝓞 (Ext F)) ^ m : 𝓞 (Ext F)) : Ext F) = x ^ m by simp [x], ← ha]
  rfl

/- English proof (translation)
Use `haveI : Group.FG (𝓞 (Ext F))ˣ := Group.fg_iff_monoid_fg.2 inferInstance`. Use `CommGroup.finite_of_fg_torsion _ fun q => ?_` and prove the remaining obligations. Take `⟨u, rfl⟩` from `QuotientGroup.mk_surjective q`. Take `⟨m, hm, hu⟩` from `pow_mem_range F u`. Use `isOfFinOrder_iff_pow_eq_one.2 ⟨m, hm, ?_⟩` and prove the remaining obligations.

Rewrite using `[← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]`. Conclude with `hu`.
-/
theorem finite_quot : Finite ((NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))ˣ ⧸
    (Units.map (algebraMap (NumberField.RingOfIntegers F)
      (NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))).toMonoidHom).range) := by
  haveI : Group.FG (𝓞 (Ext F))ˣ := Group.fg_iff_monoid_fg.2 inferInstance
  refine CommGroup.finite_of_fg_torsion _ fun q => ?_
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨m, hm, hu⟩ := pow_mem_range F u
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨m, hm, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact hu

end GlobalTheory.GaussExt.UnitIdx

/- English proof (translation)
Introduce `F _ _ _` and use `GlobalTheory.GaussExt.UnitIdx.finite_quot F`.
-/
theorem GlobalTheory.GaussExt.finite_units_quot_units : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F],
    Finite ((NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))ˣ ⧸
      (Units.map (algebraMap (NumberField.RingOfIntegers F)
        (NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))).toMonoidHom).range) :=
  fun F _ _ _ => GlobalTheory.GaussExt.UnitIdx.finite_quot F
