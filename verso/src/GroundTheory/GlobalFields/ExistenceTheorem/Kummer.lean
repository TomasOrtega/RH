import Mathlib
import GroundTheory.GlobalFields.ExistenceTheorem.KummerNorm
import GroundTheory.GlobalFields.ClassFieldConsequences.OpenSubgroup

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IdeleGroup IntermediateField
  GroundTheory.ProfCoh
open scoped NumberField.AdeleRing

noncomputable section

universe u

section Galois

variable {K : Type*} [Field K] [NumberField K] {M : Type*} [Field M] [NumberField M] [Algebra K M]
  [IsAbelianGalois K M]

/- English proof (translation)
Take `⟨x, rfl⟩` from `IdeleClassGroup.mk_surjective K c`. Rewrite using `[reciprocityMap_mk, reciprocityMap_mk, restrictNormal_ideleSymbol]`.
-/
theorem reciprocityMap_intermediateField (L : IntermediateField K M) (c : IdeleClassGroup K) :
    reciprocityMap K L c = (reciprocityMap K M c).restrictNormal L := by
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K c
  rw [reciprocityMap_mk, reciprocityMap_mk, restrictNormal_ideleSymbol]

/- English proof (translation)
Use extensionality with `c`. Rewrite using `[← ker_reciprocityMap, MonoidHom.mem_ker, reciprocityMap_intermediateField, AlgEquiv.restrictNormal_eq_one_iff]`. Rewrite using `[← IntermediateField.mem_fixingSubgroup_iff, IntermediateField.fixingSubgroup_fixedField]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨d, hd, hdc⟩`.

Establish `hk : d⁻¹ * c ∈ (reciprocityMap K M).ker`. Rewrite using `[MonoidHom.mem_ker, map_mul, map_inv, hdc, inv_mul_cancel]`. Rewrite `hk` using `[ker_reciprocityMap]`. Simplify using `using N.mul_mem hd (hN hk)`. Introduce `hc`.

Conclude with `⟨c, hc, rfl⟩`.
-/
theorem range_ideleClassNorm_fixedField (N : Subgroup (IdeleClassGroup K))
    (hN : (ideleClassNorm K M).range ≤ N) :
    (ideleClassNorm K (fixedField (N.map (reciprocityMap K M)))).range = N := by
  ext c
  rw [← ker_reciprocityMap, MonoidHom.mem_ker, reciprocityMap_intermediateField,
    AlgEquiv.restrictNormal_eq_one_iff]
  rw [← IntermediateField.mem_fixingSubgroup_iff, IntermediateField.fixingSubgroup_fixedField]
  constructor
  · rintro ⟨d, hd, hdc⟩
    have hk : d⁻¹ * c ∈ (reciprocityMap K M).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hdc, inv_mul_cancel]
    rw [ker_reciprocityMap] at hk
    simpa using N.mul_mem hd (hN hk)
  · intro hc
    exact ⟨c, hc, rfl⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨_, range_ideleClassNorm_fixedField N hN⟩`.
-/
theorem exists_intermediateField_range_ideleClassNorm_eq_of_le (N : Subgroup (IdeleClassGroup K))
    (hN : (ideleClassNorm K M).range ≤ N) :
    ∃ L : IntermediateField K M, (ideleClassNorm K L).range = N :=
  ⟨_, range_ideleClassNorm_fixedField N hN⟩

end Galois

section Open

variable {K : Type u} [Field K] [NumberField K] {n : ℕ} [NeZero n]

/- English proof (translation)
Rewrite using `[coe_finiteProj, ← WithZero.exp_log (valued_ne_zero v x)]`. Establish `h' : WithZero.log (Valued.v ((x : 𝔸[K]).2 v)) = 0`. Rewrite `h` using `[ord]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[h', WithZero.exp_zero]`.
-/
theorem IdeleGroup.valued_finiteProj_eq_one_of_ord_eq_zero {v : HeightOneSpectrum (𝓞 K)}
    {x : IdeleGroup K} (h : ord v x = 0) :
    Valued.v ((finiteProj v x : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
  rw [coe_finiteProj, ← WithZero.exp_log (valued_ne_zero v x)]
  have h' : WithZero.log (Valued.v ((x : 𝔸[K]).2 v)) = 0 := by
    rw [ord] at h
    omega
  rw [h', WithZero.exp_zero]

/- English proof (translation)
Use `𝔪.mem_congruenceSubgroup.2 ⟨fun v ↦ ?_, fun w _ ↦ ?_⟩` and prove the remaining obligations. Distinguish the cases in `hv : v ∈ S`. Rewrite using `[hzS v hv]`. Conclude with `one_mem _`. Establish `he : 𝔪.exponent v = 0`.

Assume the negation of the conclusion as `h`. Conclude with `hv (hS v h)`. Establish `h1` using `valued_finiteProj_eq_one_of_ord_eq_zero (hzo v hv)`. Rewrite using `[he, mem_unitsLevel]`. Use `⟨h1, ?_⟩` and prove the remaining obligations.

Rewrite using `[Nat.cast_zero, neg_zero, WithZero.exp_zero]`. Conclude with `Valuation.map_sub_le _ h1.le (by simp)`. Rewrite using `[hzi w.1]`. Simplify using the standard rewrite rules.
-/
theorem mem_congruenceSubgroup_of_eq_one (𝔪 : Modulus K) {S : Set (HeightOneSpectrum (𝓞 K))}
    (hS : ∀ v, 𝔪.exponent v ≠ 0 → v ∈ S) {z : IdeleGroup K} (hzS : ∀ v ∈ S, finiteProj v z = 1)
    (hzo : ∀ v ∉ S, ord v z = 0) (hzi : ∀ w, infiniteProj w z = 1) :
    z ∈ 𝔪.congruenceSubgroup := by
  refine 𝔪.mem_congruenceSubgroup.2 ⟨fun v ↦ ?_, fun w _ ↦ ?_⟩
  · by_cases hv : v ∈ S
    · rw [hzS v hv]
      exact one_mem _
    · have he : 𝔪.exponent v = 0 := by
        by_contra h
        exact hv (hS v h)
      have h1 := valued_finiteProj_eq_one_of_ord_eq_zero (hzo v hv)
      rw [he, mem_unitsLevel]
      refine ⟨h1, ?_⟩
      rw [Nat.cast_zero, neg_zero, WithZero.exp_zero]
      exact Valuation.map_sub_le _ h1.le (by simp)
  · rw [hzi w.1]
    simp

/- English proof (translation)
Take `⟨𝔪, -, h𝔪⟩` from `Modulus.exists_congruenceSubgroup_le (N.comap (IdeleClassGroup.mk K)) (hN.preimage (IdeleClassGroup.continuous_mk K))`. Take `⟨S₀, hS₀⟩` from `exists_finset_sup_sIdeles_eq_top (K := K)`. Establish `hn0 : Ideal.span {(n : 𝓞 K)} ≠ 0`. Rewrite using `[Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]`. Conclude with `NeZero.ne n` after adjusting the coercions.

Use `set P := (Ideal.finite_factors hn0).toFinset`. Use `set T := 𝔪.finite_support_exponent.toFinset`. Use `set S := S₀ ∪ T ∪ P with hSdef`. Establish `hsub : (S₀ : Set (HeightOneSpectrum (𝓞 K))) ⊆ S`. Introduce `v hv`.

Simplify using `[hSdef, Finset.mem_coe.1 hv]`. Use `⟨S, fun v hv ↦ ?_, sup_sIdeles_eq_top_of_subset hsub hS₀, ?_⟩` and prove the remaining obligations. Establish `: v ∈ P`. Rewrite using `[Set.Finite.mem_toFinset]`. Conclude with `Ideal.dvd_span_singleton.2 hv`.

Simplify using `[hSdef, this]`. Rewrite using `[Subgroup.map_le_iff_le_comap]`. Introduce `x hx`. Use `choose α hα using fun v : S ↦ hx.1 v.1 (Finset.mem_coe.2 v.2)`. Use `choose β hβ using fun w ↦ hx.2.1 w`.

Set `y : IdeleGroup K` to `(∏ v : S, finiteEmbedding v.1 (α v)) * ∏ w, infiniteEmbedding w (β w)`. Establish `hyS : ∀ v : S, finiteProj v.1 y = α v`. Introduce `v`. Simplify using `only [y, map_mul, map_prod, finiteProj_infiniteEmbedding, Finset.prod_const_one, mul_one]`. Rewrite using `[Finset.prod_eq_single v (fun u _ hu ↦ finiteProj_finiteEmbedding_of_ne (fun h ↦ hu (Subtype.ext h.symm)) _) (by simp), finiteProj_finiteEmbedding]`.

Establish `hyo : ∀ v ∉ S, finiteProj v y = 1`. Introduce `v hv`. Simplify using `only [y, map_mul, map_prod, finiteProj_infiniteEmbedding, Finset.prod_const_one, mul_one]`. Conclude with `Finset.prod_eq_one fun u _ ↦ finiteProj_finiteEmbedding_of_ne (fun h ↦ hv (by rw [h]; exact u.2)) _`. Establish `hyi : ∀ w, infiniteProj w y = β w`.

Introduce `w`. Simplify using `only [y, map_mul, map_prod, infiniteProj_finiteEmbedding, Finset.prod_const_one, one_mul]`. Rewrite using `[Finset.prod_eq_single w (fun u _ hu ↦ infiniteProj_infiniteEmbedding_of_ne (fun h ↦ hu h.symm) _) (by simp), infiniteProj_infiniteEmbedding]`. Use `set z := (y ^ n)⁻¹ * x with hz`. Establish `hzS : ∀ v ∈ (S : Set (HeightOneSpectrum (𝓞 K))), finiteProj v z = 1`.

Introduce `v hv`. Rewrite using `[hz, map_mul, map_inv, map_pow, hyS ⟨v, hv⟩, ← hα ⟨v, hv⟩, powMonoidHom_apply, inv_mul_cancel]`. Establish `hzo : ∀ v ∉ (S : Set (HeightOneSpectrum (𝓞 K))), ord v z = 0`. Introduce `v hv`. Establish `hyv : ord v y = 0`.

Rewrite using `[ord, ← coe_finiteProj, hyo v hv, Units.val_one, map_one, WithZero.log_one, neg_zero]`. Establish `hxv : ord v x = 0` using `hx.2.2 v (by simpa using hv)`. Rewrite using `[hz, ord_mul, ord_inv]`. Establish `hpow' : ∀ k : ℕ, ord v (y ^ k) = 0`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [pow_succ, ord_mul, ih, hyv, add_zero]`. Rewrite using `[hpow' n, hxv]`. Simplify using the standard rewrite rules.

Establish `hzi : ∀ w, infiniteProj w z = 1`. Introduce `w`. Rewrite using `[hz, map_mul, map_inv, map_pow, hyi w, ← hβ w, powMonoidHom_apply, inv_mul_cancel]`. Establish `hzU : z ∈ 𝔪.congruenceSubgroup` using `mem_congruenceSubgroup_of_eq_one 𝔪 (S := (S : Set (HeightOneSpectrum (𝓞 K)))) (fun v hv ↦ by`. Establish `: v ∈ T`.

Rewrite using `[Set.Finite.mem_toFinset]`. Conclude with `hv`. Simplify using `[hSdef, this]) hzS hzo hzi`. Establish `hxyz : x = y ^ n * z` using `by rw [hz, mul_inv_cancel_left]`. Rewrite using `[hxyz]`.

Use `Subgroup.mul_mem _ ?_ (h𝔪 hzU)` and prove the remaining obligations. Rewrite using `[Subgroup.mem_comap, map_pow]`. Conclude with `hpow _`.
-/
theorem exists_map_powerSubgroup_le (N : Subgroup (IdeleClassGroup K))
    (hN : IsOpen (N : Set (IdeleClassGroup K))) (hpow : ∀ c, c ^ n ∈ N) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      (∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S) ∧
      (diagonal K).range ⊔ sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) = ⊤ ∧
      (powerSubgroup n (S : Set (HeightOneSpectrum (𝓞 K))) ∅).map (IdeleClassGroup.mk K) ≤ N := by
  classical
  obtain ⟨𝔪, -, h𝔪⟩ := Modulus.exists_congruenceSubgroup_le (N.comap (IdeleClassGroup.mk K))
    (hN.preimage (IdeleClassGroup.continuous_mk K))
  obtain ⟨S₀, hS₀⟩ := exists_finset_sup_sIdeles_eq_top (K := K)
  have hn0 : Ideal.span {(n : 𝓞 K)} ≠ 0 := by
    rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast NeZero.ne n
  set P := (Ideal.finite_factors hn0).toFinset
  set T := 𝔪.finite_support_exponent.toFinset
  set S := S₀ ∪ T ∪ P with hSdef
  have hsub : (S₀ : Set (HeightOneSpectrum (𝓞 K))) ⊆ S := by
    intro v hv
    simp [hSdef, Finset.mem_coe.1 hv]
  refine ⟨S, fun v hv ↦ ?_, sup_sIdeles_eq_top_of_subset hsub hS₀, ?_⟩
  · have : v ∈ P := by
      rw [Set.Finite.mem_toFinset]
      exact Ideal.dvd_span_singleton.2 hv
    simp [hSdef, this]
  rw [Subgroup.map_le_iff_le_comap]
  intro x hx
  choose α hα using fun v : S ↦ hx.1 v.1 (Finset.mem_coe.2 v.2)
  choose β hβ using fun w ↦ hx.2.1 w
  let y : IdeleGroup K := (∏ v : S, finiteEmbedding v.1 (α v)) * ∏ w, infiniteEmbedding w (β w)
  have hyS : ∀ v : S, finiteProj v.1 y = α v := by
    intro v
    simp only [y, map_mul, map_prod, finiteProj_infiniteEmbedding, Finset.prod_const_one, mul_one]
    rw [Finset.prod_eq_single v (fun u _ hu ↦
      finiteProj_finiteEmbedding_of_ne (fun h ↦ hu (Subtype.ext h.symm)) _) (by simp),
      finiteProj_finiteEmbedding]
  have hyo : ∀ v ∉ S, finiteProj v y = 1 := by
    intro v hv
    simp only [y, map_mul, map_prod, finiteProj_infiniteEmbedding, Finset.prod_const_one, mul_one]
    exact Finset.prod_eq_one fun u _ ↦
      finiteProj_finiteEmbedding_of_ne (fun h ↦ hv (by rw [h]; exact u.2)) _
  have hyi : ∀ w, infiniteProj w y = β w := by
    intro w
    simp only [y, map_mul, map_prod, infiniteProj_finiteEmbedding, Finset.prod_const_one, one_mul]
    rw [Finset.prod_eq_single w (fun u _ hu ↦
      infiniteProj_infiniteEmbedding_of_ne (fun h ↦ hu h.symm) _) (by simp),
      infiniteProj_infiniteEmbedding]
  set z := (y ^ n)⁻¹ * x with hz
  have hzS : ∀ v ∈ (S : Set (HeightOneSpectrum (𝓞 K))), finiteProj v z = 1 := by
    intro v hv
    rw [hz, map_mul, map_inv, map_pow, hyS ⟨v, hv⟩, ← hα ⟨v, hv⟩, powMonoidHom_apply,
      inv_mul_cancel]
  have hzo : ∀ v ∉ (S : Set (HeightOneSpectrum (𝓞 K))), ord v z = 0 := by
    intro v hv
    have hyv : ord v y = 0 := by
      rw [ord, ← coe_finiteProj, hyo v hv, Units.val_one, map_one, WithZero.log_one, neg_zero]
    have hxv : ord v x = 0 := hx.2.2 v (by simpa using hv)
    rw [hz, ord_mul, ord_inv]
    have hpow' : ∀ k : ℕ, ord v (y ^ k) = 0 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, ord_mul, ih, hyv, add_zero]
    rw [hpow' n, hxv]
    simp
  have hzi : ∀ w, infiniteProj w z = 1 := by
    intro w
    rw [hz, map_mul, map_inv, map_pow, hyi w, ← hβ w, powMonoidHom_apply, inv_mul_cancel]
  have hzU : z ∈ 𝔪.congruenceSubgroup :=
    mem_congruenceSubgroup_of_eq_one 𝔪 (S := (S : Set (HeightOneSpectrum (𝓞 K))))
      (fun v hv ↦ by
        have : v ∈ T := by
          rw [Set.Finite.mem_toFinset]
          exact hv
        simp [hSdef, this]) hzS hzo hzi
  have hxyz : x = y ^ n * z := by rw [hz, mul_inv_cancel_left]
  rw [hxyz]
  refine Subgroup.mul_mem _ ?_ (h𝔪 hzU)
  rw [Subgroup.mem_comap, map_pow]
  exact hpow _

end Open

section Existence

variable {K : Type u} [Field K] [NumberField K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]

/- English proof (translation)
Take `⟨S, hS, hJ, hle⟩` from `exists_map_powerSubgroup_le N hN hpow`. Use `⟨S, hS, hJ, exists_intermediateField_range_ideleClassNorm_eq_of_le N ?_⟩` and prove the remaining obligations. Rewrite using `[range_ideleClassNorm_sUnitKummerField S hS hJ]`. Conclude with `hle`.
-/
theorem exists_intermediateField_range_ideleClassNorm_eq (N : Subgroup (IdeleClassGroup K))
    (hN : IsOpen (N : Set (IdeleClassGroup K))) (hpow : ∀ c, c ^ n ∈ N) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      (∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S) ∧
      (diagonal K).range ⊔ sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) = ⊤ ∧
      ∃ L : IntermediateField K (sUnitKummerField K n (S : Set (HeightOneSpectrum (𝓞 K)))),
        (ideleClassNorm K L).range = N := by
  obtain ⟨S, hS, hJ, hle⟩ := exists_map_powerSubgroup_le N hN hpow
  refine ⟨S, hS, hJ, exists_intermediateField_range_ideleClassNorm_eq_of_le N ?_⟩
  rw [range_ideleClassNorm_sUnitKummerField S hS hJ]
  exact hle

/- English proof (translation)
Take `⟨S, -, -, L, hL⟩` from `exists_intermediateField_range_ideleClassNorm_eq N hN hpow`. Use `⟨L, inferInstance, inferInstance, inferInstance, inferInstance, ?_, hL⟩` and prove the remaining obligations. Establish `hexpM : ∀ τ : Gal(sUnitKummerField K n (S : Set (HeightOneSpectrum (𝓞 K)))/K), τ ^ n = 1` using `Monoid.exponent_dvd_iff_forall_pow_eq_one.1 (kummerExtension_exponent_dvd K n _ _)`. Use `Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun τ ↦ ?_` and prove the remaining obligations. Take `⟨τ', rfl⟩` from `AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) (E := sUnitKummerField K n (S : Set (HeightOneSpectrum (𝓞 K)))) τ`.

Rewrite using `[← map_pow, hexpM, map_one]`.
-/
theorem exists_isAbelianGalois_range_ideleClassNorm_eq (N : Subgroup (IdeleClassGroup K))
    (hN : IsOpen (N : Set (IdeleClassGroup K))) (hpow : ∀ c, c ^ n ∈ N) :
    ∃ (L : Type u) (_ : Field L) (_ : NumberField L) (_ : Algebra K L),
      IsAbelianGalois K L ∧ Monoid.exponent Gal(L/K) ∣ n ∧ (ideleClassNorm K L).range = N := by
  obtain ⟨S, -, -, L, hL⟩ := exists_intermediateField_range_ideleClassNorm_eq N hN hpow
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, ?_, hL⟩
  have hexpM : ∀ τ : Gal(sUnitKummerField K n (S : Set (HeightOneSpectrum (𝓞 K)))/K), τ ^ n = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.1 (kummerExtension_exponent_dvd K n _ _)
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun τ ↦ ?_
  obtain ⟨τ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L)
    (E := sUnitKummerField K n (S : Set (HeightOneSpectrum (𝓞 K)))) τ
  rw [← map_pow, hexpM, map_one]

end Existence

end

end GroundTheory.Global
