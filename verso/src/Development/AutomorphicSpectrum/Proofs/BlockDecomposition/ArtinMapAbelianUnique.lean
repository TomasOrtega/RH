import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import GroundTheory.GlobalFields.ComplexMultiplication.MainTheorem
import ReciprocityTheory.ClassFieldTheory.GlobalClassField.IsFrobAtMulOfMemInertiaGroup
import ReciprocityTheory.ClassFieldTheory.GlobalClassField.AsGabLimB
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsDiagMulRayMulUnif
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.InvMemUFin
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo

noncomputable section

open NumberField IsDedekindDomain Neutral.B1
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.ArtinUniq

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Use `⟨(differentIdeal (𝓞 K) (𝓞 L)).under (𝓞 K), ?_, fun v hv Q hQ hl => ?_⟩` and prove the remaining obligations. Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot (differentIdeal_ne_bot (A := 𝓞 K) (B := 𝓞 L))`. Conclude with `Ideal.comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x)`. Establish `hnd : ¬ Q ∣ differentIdeal (𝓞 K) (𝓞 L)` using `fun hd => hv (Ideal.dvd_iff_le.2 (by`. Rewrite using `[hl.over]`.

Conclude with `Ideal.comap_mono (Ideal.dvd_iff_le.1 hd)))`. Conclude with `Ideal.ramificationIdx_eq_one_iff.2 (not_dvd_differentIdeal_iff.1 hnd)`.
-/
theorem exists_ideal_unramified (L : Type) [Field L] [NumberField L] [Algebra K L] :
    ∃ 𝔡 : Ideal (𝓞 K), 𝔡 ≠ ⊥ ∧
      ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔡 → IsUnramifiedIn K v L := by
  refine ⟨(differentIdeal (𝓞 K) (𝓞 L)).under (𝓞 K), ?_, fun v hv Q hQ hl => ?_⟩
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (differentIdeal_ne_bot (A := 𝓞 K) (B := 𝓞 L))
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x)
  · have hnd : ¬ Q ∣ differentIdeal (𝓞 K) (𝓞 L) := fun hd => hv (Ideal.dvd_iff_le.2 (by
      rw [hl.over]
      exact Ideal.comap_mono (Ideal.dvd_iff_le.1 hd)))
    exact Ideal.ramificationIdx_eq_one_iff.2 (not_dvd_differentIdeal_iff.1 hnd)

/- English proof (translation)
Establish `key : ∀ x : (v.adicCompletion K)ˣ, Valued.v (x : v.adicCompletion K) ≤ 1 → x ∈ M`. Introduce `x hx`. Take `⟨hπ1, hirr⟩` from `hπ`. Establish `hxm : (x : v.adicCompletion K) ∈ v.adicCompletionIntegers K` using `hx`. Establish `hx0 : (⟨x, hxm⟩ : v.adicCompletionIntegers K) ≠ 0` using `fun h0 => x.ne_zero (congrArg Subtype.val h0)`.

Take `⟨n, u, e⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hirr`. Establish `e' : (x : v.adicCompletion K) = ((u : v.adicCompletionIntegers K) : v.adicCompletion K) * (π : v.adicCompletion K) ^ n` using `congrArg Subtype.val e`. Establish `h1 : Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) ≤ 1` using `(u : v.adicCompletionIntegers K).2`. Establish `h2 : Valued.v (((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) : v.adicCompletion K) ≤ 1` using `((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K).2`. Establish `h3 : Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) * Valued.v (((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) : v.adicCompletion K) = 1`.

Rewrite using `[← map_mul]`. Establish `: ((u : v.adicCompletionIntegers K) : v.adicCompletion K) * (((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) : v.adicCompletion K) = 1` using `congrArg Subtype.val u.mul_inv`. Rewrite using `[this, map_one]`. Establish `h4 : Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) = 1` using `le_antisymm h1 (h3 ▸ mul_le_of_le_one_right' h2)`. Establish `hy : x * (π ^ n)⁻¹ ∈ M`.

Use `hu _ ?_` and prove the remaining obligations. Establish `: ((x * (π ^ n)⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) = ((u : v.adicCompletionIntegers K) : v.adicCompletion K)`. Rewrite using `[Units.val_mul, e', Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]`. Conclude with `mul_inv_cancel_right₀ (pow_ne_zero n π.ne_zero) _`. Rewrite using `[this, h4]`.

Use `M.mul_mem hy (M.pow_mem hM n)` as an intermediate fact. Rewrite `this` using `[inv_mul_cancel_right]`. Then use the resulting hypothesis. Break down `le_total (Valued.v (x : v.adicCompletion K)) 1 with h | h` into its components or cases. Conclude with `key x h`. Use `inv_mem_iff.1 (key x⁻¹ ?_)` and prove the remaining obligations.

Rewrite using `[Units.val_inv_eq_inv_val, map_inv₀]`. Conclude with `inv_le_one_of_one_le₀ h`.
-/
theorem mem_of_units_of_unif (v : HeightOneSpectrum (𝓞 K)) (M : Subgroup (v.adicCompletion K)ˣ)
    (hu : ∀ x : (v.adicCompletion K)ˣ, Valued.v (x : v.adicCompletion K) = 1 → x ∈ M)
    (π : (v.adicCompletion K)ˣ) (hπ : IsUniformiserAt K v (π : v.adicCompletion K)) (hM : π ∈ M)
    (x : (v.adicCompletion K)ˣ) : x ∈ M := by
  have key : ∀ x : (v.adicCompletion K)ˣ, Valued.v (x : v.adicCompletion K) ≤ 1 → x ∈ M := by
    intro x hx
    obtain ⟨hπ1, hirr⟩ := hπ
    have hxm : (x : v.adicCompletion K) ∈ v.adicCompletionIntegers K := hx
    have hx0 : (⟨x, hxm⟩ : v.adicCompletionIntegers K) ≠ 0 := fun h0 =>
      x.ne_zero (congrArg Subtype.val h0)
    obtain ⟨n, u, e⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hirr
    have e' : (x : v.adicCompletion K) =
        ((u : v.adicCompletionIntegers K) : v.adicCompletion K) * (π : v.adicCompletion K) ^ n :=
      congrArg Subtype.val e
    have h1 : Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) ≤ 1 :=
      (u : v.adicCompletionIntegers K).2
    have h2 : Valued.v (((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) :
        v.adicCompletion K) ≤ 1 := ((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K).2
    have h3 : Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) *
        Valued.v (((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) :
        v.adicCompletion K) = 1 := by
      rw [← map_mul]
      have : ((u : v.adicCompletionIntegers K) : v.adicCompletion K) *
          (((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) :
          v.adicCompletion K) = 1 := congrArg Subtype.val u.mul_inv
      rw [this, map_one]
    have h4 : Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) = 1 :=
      le_antisymm h1 (h3 ▸ mul_le_of_le_one_right' h2)
    have hy : x * (π ^ n)⁻¹ ∈ M := by
      refine hu _ ?_
      have : ((x * (π ^ n)⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
          ((u : v.adicCompletionIntegers K) : v.adicCompletion K) := by
        rw [Units.val_mul, e', Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
        exact mul_inv_cancel_right₀ (pow_ne_zero n π.ne_zero) _
      rw [this, h4]
    have := M.mul_mem hy (M.pow_mem hM n)
    rwa [inv_mul_cancel_right] at this
  rcases le_total (Valued.v (x : v.adicCompletion K)) 1 with h | h
  · exact key x h
  · refine inv_mem_iff.1 (key x⁻¹ ?_)
    rw [Units.val_inv_eq_inv_val, map_inv₀]
    exact inv_le_one_of_one_le₀ h

/- English proof (translation)
Use `haveI := h.finiteDimensional`. Use `haveI : NumberField L := NumberField.of_module_finite K L`. Take `⟨π, hπ⟩` from `exists_isUniformiserAt K v`. Take `⟨Q, hQ, hQv⟩` from `ReciprocityTheory.DiscreteGroups.GlobalClassField.exists_liesOver (K := K) L v`. Use `mem_of_units_of_unif v (MonoidHom.eqLocus (localComposite K Art L h v) (localComposite K Art' L h v)) (fun y hy => ?_) π hπ ?_ x` and prove the remaining obligations.

Establish `hy' : Valued.v ((localIdele K v y : AdeleRing (𝓞 K) K).2 v) = 1`. Rewrite using `[localIdele_snd_self]`. Conclude with `hy`. Conclude with `((hA.2.2.2.1 L h v hv _ (localIdele_isSupportedAt K v y)).2 hy').trans ((hA'.2.2.2.1 L h v hv _ (localIdele_isSupportedAt K v y)).2 hy').symm`. Establish `hπ' : IsUniformiserAt K v ((localIdele K v π : AdeleRing (𝓞 K) K).2 v)`.

Rewrite using `[localIdele_snd_self]`. Conclude with `hπ`. Conclude with `ReciprocityTheory.DiscreteGroups.GlobalClassField.isFrobAt_unique v Q hv _ _ ((hA.2.2.2.1 L h v hv _ (localIdele_isSupportedAt K v π)).1 hπ' Q hQ hQv) ((hA'.2.2.2.1 L h v hv _ (localIdele_isSupportedAt K v π)).1 hπ' Q hQ hQv)`.
-/
theorem localIdele_eq {Art Art' : IdeleClassGroup K →* Field.absoluteGaloisGroupAbelianization K}
    (hA : IsGlobalArtinMap K Art) (hA' : IsGlobalArtinMap K Art')
    (L : IntermediateField K (AlgebraicClosure K)) (h : IsFiniteAbelian K L)
    (v : HeightOneSpectrum (𝓞 K)) (hv : IsUnramifiedIn K v L) (x : (v.adicCompletion K)ˣ) :
    abRestrict K L h (Art (QuotientGroup.mk (localIdele K v x))) =
      abRestrict K L h (Art' (QuotientGroup.mk (localIdele K v x))) := by
  haveI := h.finiteDimensional
  haveI : NumberField L := NumberField.of_module_finite K L
  obtain ⟨π, hπ⟩ := exists_isUniformiserAt K v
  obtain ⟨Q, hQ, hQv⟩ := ReciprocityTheory.DiscreteGroups.GlobalClassField.exists_liesOver (K := K) L v
  refine mem_of_units_of_unif v (MonoidHom.eqLocus (localComposite K Art L h v)
    (localComposite K Art' L h v)) (fun y hy => ?_) π hπ ?_ x
  · have hy' : Valued.v ((localIdele K v y : AdeleRing (𝓞 K) K).2 v) = 1 := by
      rw [localIdele_snd_self]
      exact hy
    exact ((hA.2.2.2.1 L h v hv _ (localIdele_isSupportedAt K v y)).2 hy').trans
      ((hA'.2.2.2.1 L h v hv _ (localIdele_isSupportedAt K v y)).2 hy').symm
  · have hπ' : IsUniformiserAt K v ((localIdele K v π : AdeleRing (𝓞 K) K).2 v) := by
      rw [localIdele_snd_self]
      exact hπ
    exact ReciprocityTheory.DiscreteGroups.GlobalClassField.isFrobAt_unique v Q hv _ _
      ((hA.2.2.2.1 L h v hv _ (localIdele_isSupportedAt K v π)).1 hπ' Q hQ hQv)
      ((hA'.2.2.2.1 L h v hv _ (localIdele_isSupportedAt K v π)).1 hπ' Q hQ hQv)

def infI : (InfiniteAdeleRing K)ˣ →* Ideles K :=
  Units.map (MonoidHom.inl (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) : _ →* _)

/- English proof (translation)
Use `haveI : ∀ w : InfinitePlace K, IsAlgClosed w.Completion := fun w => IsAlgClosed.of_ringEquiv ℂ _ (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm`. Use `choose r hr using fun w : InfinitePlace K => IsAlgClosed.exists_pow_nat_eq ((y : InfiniteAdeleRing K) w) hm`. Take `⟨r', hb⟩ : ∃ r' : InfiniteAdeleRing K, r' ^ m = (y : InfiniteAdeleRing K)` from `⟨r, funext hr⟩`. Take `⟨z, rfl⟩ : IsUnit r'` from `(isUnit_pow_iff hm.ne').1 (hb ▸ y.isUnit)`. Establish `e : z ^ m = y` using `Units.ext (by rw [Units.val_pow_eq_pow_val, hb])`.

Rewrite using `[← e, map_pow]`. Conclude with `hpow _`.
-/
theorem inf_mem [IsTotallyComplex K] (N : Subgroup (Ideles K)) (m : ℕ) (hm : 0 < m)
    (hpow : ∀ x : Ideles K, x ^ m ∈ N) (y : (InfiniteAdeleRing K)ˣ) :
    infI y ∈ N := by
  haveI : ∀ w : InfinitePlace K, IsAlgClosed w.Completion := fun w =>
    IsAlgClosed.of_ringEquiv ℂ _
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm
  choose r hr using fun w : InfinitePlace K =>
    IsAlgClosed.exists_pow_nat_eq ((y : InfiniteAdeleRing K) w) hm
  obtain ⟨r', hb⟩ : ∃ r' : InfiniteAdeleRing K, r' ^ m = (y : InfiniteAdeleRing K) :=
    ⟨r, funext hr⟩
  obtain ⟨z, rfl⟩ : IsUnit r' := (isUnit_pow_iff hm.ne').1 (hb ▸ y.isUnit)
  have e : z ^ m = y := Units.ext (by rw [Units.val_pow_eq_pow_val, hb])
  rw [← e, map_pow]
  exact hpow _

/- English proof (translation)
Establish `e2 : algebraMap K (v.adicCompletion K) (x : K) = ((algebraMap (𝓞 K) K x : K) : v.adicCompletion K)` using `rfl`. Rewrite using `[e2, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `(v.intValuation_le_pow_iff_mem x n).2 hx`.
-/
theorem valued_le_of_mem (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) {x : 𝓞 K}
    (hx : x ∈ v.asIdeal ^ n) :
    Valued.v (algebraMap K (v.adicCompletion K) (x : K)) ≤ WithZero.exp (-(n : ℤ)) := by
  have e2 : algebraMap K (v.adicCompletion K) (x : K) =
      ((algebraMap (𝓞 K) K x : K) : v.adicCompletion K) := rfl
  rw [e2, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    HeightOneSpectrum.valuation_of_algebraMap]
  exact (v.intValuation_le_pow_iff_mem x n).2 hx

/- English proof (translation)
Use `⟨𝔡 * ∏ v ∈ S, v.asIdeal ^ n, mul_ne_zero h𝔡 (Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero n v.ne_bot), dvd_mul_right _ _, fun v hv => ?_⟩` and prove the remaining obligations. Conclude with `Ideal.le_of_dvd ((Finset.dvd_prod_of_mem (fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal ^ n) hv).mul_left _)`.
-/
theorem exists_modulus (𝔡 : Ideal (𝓞 K)) (h𝔡 : 𝔡 ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (n : ℕ) : ∃ 𝔮 : Ideal (𝓞 K), 𝔮 ≠ ⊥ ∧ 𝔡 ∣ 𝔮 ∧ ∀ v ∈ S, 𝔮 ≤ v.asIdeal ^ n := by
  refine ⟨𝔡 * ∏ v ∈ S, v.asIdeal ^ n,
    mul_ne_zero h𝔡 (Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero n v.ne_bot),
    dvd_mul_right _ _, fun v hv => ?_⟩
  exact Ideal.le_of_dvd ((Finset.dvd_prod_of_mem (fun v : HeightOneSpectrum (𝓞 K) =>
    v.asIdeal ^ n) hv).mul_left _)

/- English proof (translation)
Introduce `K _ _ _ Art Art' hA hA' L h c`. Use `haveI := h.finiteDimensional`. Use `haveI := h.isGalois`. Use `haveI : NumberField L := NumberField.of_module_finite K L`. Set `f : Ideles K →* (L ≃ₐ[K] L)` to `(abRestrict K L h).comp (Art.comp (QuotientGroup.mk' (diagUnits K).range))`.

Set `f' : Ideles K →* (L ≃ₐ[K] L)` to `(abRestrict K L h).comp (Art'.comp (QuotientGroup.mk' (diagUnits K).range))`. Set `N : Subgroup (Ideles K)` to `MonoidHom.eqLocus f f'`. Establish `hfib : ∀ (B : IdeleClassGroup K →* Field.absoluteGaloisGroupAbelianization K), Continuous B → ∀ τ : L ≃ₐ[K] L, IsOpen {a : Ideles K | abRestrict K L h (B (QuotientGroup.mk a)) = τ}` using `fun B hB τ => (ReciprocityTheory.DiscreteGroups.GlobalClassField.isOpen_abRestrict_fiber h τ).preimage (hB.comp continuous_quot_mk)`. Establish `hopen : IsOpen (N : Set (Ideles K))`. Establish `e : (N : Set (Ideles K)) = ⋃ τ : L ≃ₐ[K] L, {a : Ideles K | abRestrict K L h (Art (QuotientGroup.mk a)) = τ} ∩ {a : Ideles K | abRestrict K L h (Art' (QuotientGroup.mk a)) = τ}`.

Use extensionality with `a`. Simplify using `only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]`. Conclude with `⟨fun ha => ⟨_, rfl, ha.symm⟩, fun ⟨τ, h1, h2⟩ => h1.trans h2.symm⟩`. Rewrite using `[e]`. Conclude with `isOpen_iUnion fun τ => (hfib Art hA.1 τ).inter (hfib Art' hA'.1 τ)`.

Take `⟨𝔡, h𝔡, hun⟩` from `exists_ideal_unramified (K := K) L`. Take `⟨S, n, hS⟩` from `PI.AlgValsFin.W.exists_nbhd (N : Set (Ideles K)) hopen N.one_mem`. Take `⟨𝔮, h𝔮, hd𝔮, hS𝔮⟩` from `exists_modulus 𝔡 h𝔡 S n`. Establish `hpow : ∀ x : Ideles K, x ^ Nat.card (L ≃ₐ[K] L) ∈ N` using `fun x => by show f _ = f' _`. Rewrite using `[map_pow, map_pow, pow_card_eq_one', pow_card_eq_one']`.

Establish `hray : ∀ u ∈ rayUnits K 𝔮 {w | w.IsReal}, u ∈ N`. Introduce and unpack `u ⟨-, hu⟩`. Establish `e : u = infI (Units.map (MonoidHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) : _ →* _) u) * GlobalTheory.Mem.Chr.finPartI K u` using `Units.ext (Prod.ext (mul_one _).symm (one_mul _).symm)`. Rewrite using `[e]`. Use `N.mul_mem (inf_mem N _ Nat.card_pos hpow _) (hS _ ⟨rfl, fun v => (hu v).1⟩ fun v hv => ?_)` and prove the remaining obligations.

Take `⟨-, x, hx, hle⟩` from `hu v`. Conclude with `hle.trans (valued_le_of_mem v n (hS𝔮 v hv hx))`. Establish `hloc : Subgroup.closure {x : Ideles K | ∃ (v : HeightOneSpectrum (𝓞 K)) (π : (v.adicCompletion K)ˣ), ¬ v.asIdeal ∣ 𝔮 ∧ IsUniformiserAt K v (π : v.adicCompletion K) ∧ x = localIdele K v π} ≤ N`. Use `(Subgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨v, π, hv, -, rfl⟩`.

Conclude with `localIdele_eq hA hA' L h v (hun v fun hd => hv (hd.trans hd𝔮)) π`. Establish `hdiag : (diagUnits K).range ≤ N`. Introduce and unpack `_ ⟨k, rfl⟩`. Establish `e : QuotientGroup.mk' (diagUnits K).range (diagUnits K k) = 1` using `(QuotientGroup.eq_one_iff _).2 ⟨k, rfl⟩`. Use `show abRestrict K L h (Art (QuotientGroup.mk' (diagUnits K).range (diagUnits K k))) = abRestrict K L h (Art' (QuotientGroup.mk' (diagUnits K).range (diagUnits K k)))`.

Simplify using `only [e, map_one]`. Take `⟨a, rfl⟩` from `QuotientGroup.mk_surjective c`. Take `⟨k, u, hu, b, hb, e⟩` from `GlobalTheory.RayGen.exists_diag_mul_ray_mul_unif K 𝔮 h𝔮 a`. Establish `ha : a ∈ N` using `e ▸ N.mul_mem (N.mul_mem (hdiag ⟨k, rfl⟩) (hray u hu)) (hloc hb)`. Conclude with `ha`.
-/
theorem abRestrict_eq : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (Art Art' : IdeleClassGroup K →* Field.absoluteGaloisGroupAbelianization K),
    IsGlobalArtinMap K Art → IsGlobalArtinMap K Art' →
    ∀ (L : IntermediateField K (AlgebraicClosure K)) (h : IsFiniteAbelian K L)
      (c : IdeleClassGroup K),
      abRestrict K L h (Art c) = abRestrict K L h (Art' c) := by
  intro K _ _ _ Art Art' hA hA' L h c
  haveI := h.finiteDimensional
  haveI := h.isGalois
  haveI : NumberField L := NumberField.of_module_finite K L
  let f : Ideles K →* (L ≃ₐ[K] L) :=
    (abRestrict K L h).comp (Art.comp (QuotientGroup.mk' (diagUnits K).range))
  let f' : Ideles K →* (L ≃ₐ[K] L) :=
    (abRestrict K L h).comp (Art'.comp (QuotientGroup.mk' (diagUnits K).range))
  let N : Subgroup (Ideles K) := MonoidHom.eqLocus f f'
  have hfib : ∀ (B : IdeleClassGroup K →* Field.absoluteGaloisGroupAbelianization K),
      Continuous B → ∀ τ : L ≃ₐ[K] L,
      IsOpen {a : Ideles K | abRestrict K L h (B (QuotientGroup.mk a)) = τ} := fun B hB τ =>
    (ReciprocityTheory.DiscreteGroups.GlobalClassField.isOpen_abRestrict_fiber h τ).preimage (hB.comp continuous_quot_mk)
  have hopen : IsOpen (N : Set (Ideles K)) := by
    have e : (N : Set (Ideles K)) = ⋃ τ : L ≃ₐ[K] L,
        {a : Ideles K | abRestrict K L h (Art (QuotientGroup.mk a)) = τ} ∩
        {a : Ideles K | abRestrict K L h (Art' (QuotientGroup.mk a)) = τ} := by
      ext a
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
      exact ⟨fun ha => ⟨_, rfl, ha.symm⟩, fun ⟨τ, h1, h2⟩ => h1.trans h2.symm⟩
    rw [e]
    exact isOpen_iUnion fun τ => (hfib Art hA.1 τ).inter (hfib Art' hA'.1 τ)
  obtain ⟨𝔡, h𝔡, hun⟩ := exists_ideal_unramified (K := K) L
  obtain ⟨S, n, hS⟩ := PI.AlgValsFin.W.exists_nbhd (N : Set (Ideles K)) hopen N.one_mem
  obtain ⟨𝔮, h𝔮, hd𝔮, hS𝔮⟩ := exists_modulus 𝔡 h𝔡 S n
  have hpow : ∀ x : Ideles K, x ^ Nat.card (L ≃ₐ[K] L) ∈ N := fun x => by
    show f _ = f' _
    rw [map_pow, map_pow, pow_card_eq_one', pow_card_eq_one']
  have hray : ∀ u ∈ rayUnits K 𝔮 {w | w.IsReal}, u ∈ N := by
    rintro u ⟨-, hu⟩
    have e : u = infI
        (Units.map (MonoidHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) : _ →* _) u) *
        GlobalTheory.Mem.Chr.finPartI K u :=
      Units.ext (Prod.ext (mul_one _).symm (one_mul _).symm)
    rw [e]
    refine N.mul_mem (inf_mem N _ Nat.card_pos hpow _) (hS _ ⟨rfl, fun v => (hu v).1⟩ fun v hv => ?_)
    obtain ⟨-, x, hx, hle⟩ := hu v
    exact hle.trans (valued_le_of_mem v n (hS𝔮 v hv hx))
  have hloc : Subgroup.closure {x : Ideles K | ∃ (v : HeightOneSpectrum (𝓞 K))
      (π : (v.adicCompletion K)ˣ), ¬ v.asIdeal ∣ 𝔮 ∧
        IsUniformiserAt K v (π : v.adicCompletion K) ∧ x = localIdele K v π} ≤ N := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨v, π, hv, -, rfl⟩
    exact localIdele_eq hA hA' L h v (hun v fun hd => hv (hd.trans hd𝔮)) π
  have hdiag : (diagUnits K).range ≤ N := by
    rintro _ ⟨k, rfl⟩
    have e : QuotientGroup.mk' (diagUnits K).range (diagUnits K k) = 1 :=
      (QuotientGroup.eq_one_iff _).2 ⟨k, rfl⟩
    show abRestrict K L h (Art (QuotientGroup.mk' (diagUnits K).range (diagUnits K k))) =
      abRestrict K L h (Art' (QuotientGroup.mk' (diagUnits K).range (diagUnits K k)))
    simp only [e, map_one]
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨k, u, hu, b, hb, e⟩ := GlobalTheory.RayGen.exists_diag_mul_ray_mul_unif K 𝔮 h𝔮 a
  have ha : a ∈ N := e ▸ N.mul_mem (N.mul_mem (hdiag ⟨k, rfl⟩) (hray u hu)) (hloc hb)
  exact ha

end GlobalTheory.CompanionTheory.ArtinUniq
