import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorsionParamLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscFieldEqTorsionField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvdDiscrTorsionField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramInIffDifferentIdealEqTop
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AbelianUnramIn
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIsRayIntermediateField
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsImagQuadraticHost
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NatCastMulFinrankMemDifferentIdeal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.LogRootDiscrLeOfNatCastMemDifferentIdeal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HeckeIdealEqOfRay
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimeDvdNatCastMem
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.Mem.Fld.TorsionSize

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.PrimeDvdNatCastMem.exists_prime_dvd_natCast_mem`. Consider the case `exact _root_.GlobalTheory.PrimeDvdNatCastMem.exists_prime_dvd_natCast_mem`. Consider the case `(apply _root_.GlobalTheory.PrimeDvdNatCastMem.exists_prime_dvd_natCast_mem <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.PrimeDvdNatCastMem.exists_prime_dvd_natCast_mem <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.PrimeDvdNatCastMem.exists_prime_dvd_natCast_mem <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.PrimeDvdNatCastMem.exists_prime_dvd_natCast_mem ..)`.
-/
theorem exists_prime_dvd_mem {O : Type} [CommRing O] (P : Ideal O) [hP : P.IsPrime] (m : ℕ) :
    m ≠ 0 → (m : O) ∈ P → ∃ p : ℕ, p.Prime ∧ p ∣ m ∧ (p : O) ∈ P := by
  first
  | exact @_root_.GlobalTheory.PrimeDvdNatCastMem.exists_prime_dvd_natCast_mem
  | exact _root_.GlobalTheory.PrimeDvdNatCastMem.exists_prime_dvd_natCast_mem
  | (apply _root_.GlobalTheory.PrimeDvdNatCastMem.exists_prime_dvd_natCast_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrimeDvdNatCastMem.exists_prime_dvd_natCast_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrimeDvdNatCastMem.exists_prime_dvd_natCast_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrimeDvdNatCastMem.exists_prime_dvd_natCast_mem ..)

/- English proof (translation)
Introduce and unpack `σ ⟨P, hP, hPo, hσ⟩`. Establish `hP0 : P ≠ ⊥` using `Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P`. Establish `hnd : ¬ P ∣ differentIdeal (𝓞 H) (𝓞 M)`. Introduce `hd`. Establish `h1 : Ideal.absNorm P ∣ (discr M).natAbs`.

Rewrite using `[natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow H (𝓞 H) M (𝓞 M)]`. Conclude with `(map_dvd Ideal.absNorm hd).mul_right _`. Take `⟨p, hp, hpd, hpP⟩` from `exists_prime_dvd_mem P (Ideal.absNorm P) (by rwa [Ne, Ideal.absNorm_eq_zero_iff]) (Ideal.absNorm_mem P)`. Take `⟨k, hk⟩` from `h p hp (hpd.trans h1)`. Apply `hn` to reduce the goal to its premises.

Rewrite using `[hPo.over, Ideal.mem_comap, map_natCast, hk, Nat.cast_mul]`. Conclude with `P.mul_mem_right _ hpP`. Establish `hI` using `(GlobalTheory.UnramDiscr.not_dvd_iff_inertia H M P hP0).1 hnd`. Establish `: σ ∈ Ideal.inertia Gal(M/H) P` using `fun x => hσ x`. Rewrite `this` using `[hI]`.

Conclude with `Subgroup.mem_bot.1 this`.
-/
theorem unramIn_of_discr (H M : Type) [Field H] [NumberField H] [Field M] [NumberField M]
    [Algebra H M] [IsGalois H M] (n : ℕ)
    (h : ∀ p : ℕ, p.Prime → p ∣ (discr M).natAbs → p ∣ n)
    (𝔭 : HeightOneSpectrum (𝓞 H)) (hn : (n : 𝓞 H) ∉ 𝔭.asIdeal) : UnramIn M 𝔭 := by
  rintro σ ⟨P, hP, hPo, hσ⟩
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P
  have hnd : ¬ P ∣ differentIdeal (𝓞 H) (𝓞 M) := by
    intro hd
    have h1 : Ideal.absNorm P ∣ (discr M).natAbs := by
      rw [natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow H (𝓞 H) M (𝓞 M)]
      exact (map_dvd Ideal.absNorm hd).mul_right _
    obtain ⟨p, hp, hpd, hpP⟩ := exists_prime_dvd_mem P (Ideal.absNorm P)
      (by rwa [Ne, Ideal.absNorm_eq_zero_iff]) (Ideal.absNorm_mem P)
    obtain ⟨k, hk⟩ := h p hp (hpd.trans h1)
    apply hn
    rw [hPo.over, Ideal.mem_comap, map_natCast, hk, Nat.cast_mul]
    exact P.mul_mem_right _ hpP
  have hI := (GlobalTheory.UnramDiscr.not_dvd_iff_inertia H M P hP0).1 hnd
  have : σ ∈ Ideal.inertia Gal(M/H) P := fun x => hσ x
  rw [hI] at this
  exact Subgroup.mem_bot.1 this

/- English proof (translation)
Establish `hH` using `(GlobalTheory.UnramDiscr.unramIn_iff_natAbs_discr K H).1 hu`. Rewrite `hH` using `[hdK]`. Establish `h' : ∀ p : ℕ, p.Prime → p ∣ (discr M).natAbs → p ∣ 6 * d`. Introduce `p hp hpd`. Break down `h p hp hpd with h1 | h1` into its components or cases.

Conclude with `h1`. Rewrite `h1` using `[hH]`. Conclude with `(hp.dvd_of_dvd_pow h1).mul_left 6`. Establish `h1` using `GlobalTheory.DifferentBound.natCast_mul_finrank_mem_differentIdeal H M (6 * d) (by omega) (unramIn_of_discr H M (6 * d) h')`. Establish `h2` using `GlobalTheory.log_rootDiscr_le_of_natCast_mem_differentIdeal H M _ (Nat.mul_pos (by omega) Module.finrank_pos) h1`.

Use `h2.trans (add_le_add_left (le_of_eq ?_) _)` and prove the remaining obligations. Establish `h3 : |((discr H : ℤ) : ℝ)| = (d : ℝ) ^ Module.finrank K H`. Rewrite using `[← Int.cast_abs, ← Int.natCast_natAbs, hH]`. Use `push_cast`. Both sides reduce to the same expression.

Establish `h4 : (Module.finrank K H : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 Module.finrank_pos.ne'`. Rewrite using `[h3, Real.log_pow, ← Module.finrank_mul_finrank ℚ K H, hK]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem log_rootDiscr_le (K H M : Type) [Field K] [NumberField K] [Field H] [NumberField H]
    [Field M] [NumberField M] [Algebra K H] [Algebra H M] [IsGalois K H] [IsGalois H M] (d : ℕ)
    (hd : 0 < d) (hK : Module.finrank ℚ K = 2) (hdK : (discr K).natAbs = d)
    (hu : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), UnramIn H 𝔭)
    (h : ∀ p : ℕ, p.Prime → p ∣ (discr M).natAbs → p ∣ 6 * d ∨ p ∣ (discr H).natAbs) :
    Real.log |((discr M : ℤ) : ℝ)| / Module.finrank ℚ M ≤
      Real.log d / 2 + Real.log ((6 * d * Module.finrank H M : ℕ) : ℝ) := by
  have hH := (GlobalTheory.UnramDiscr.unramIn_iff_natAbs_discr K H).1 hu
  rw [hdK] at hH
  have h' : ∀ p : ℕ, p.Prime → p ∣ (discr M).natAbs → p ∣ 6 * d := by
    intro p hp hpd
    rcases h p hp hpd with h1 | h1
    · exact h1
    · rw [hH] at h1
      exact (hp.dvd_of_dvd_pow h1).mul_left 6
  have h1 := GlobalTheory.DifferentBound.natCast_mul_finrank_mem_differentIdeal H M (6 * d) (by omega)
    (unramIn_of_discr H M (6 * d) h')
  have h2 := GlobalTheory.log_rootDiscr_le_of_natCast_mem_differentIdeal H M _
    (Nat.mul_pos (by omega) Module.finrank_pos) h1
  refine h2.trans (add_le_add_left (le_of_eq ?_) _)
  have h3 : |((discr H : ℤ) : ℝ)| = (d : ℝ) ^ Module.finrank K H := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, hH]; push_cast; rfl
  have h4 : (Module.finrank K H : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  rw [h3, Real.log_pow, ← Module.finrank_mul_finrank ℚ K H, hK]
  push_cast
  field_simp

/- English proof (translation)
Establish `hn : Ideal.span {(n : 𝓞 K)} ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `Nat.cast_ne_zero.2 (by omega)`. Take `⟨R, _, _, hRay⟩` from `SmallField.exists_isRay_intermediateField hR K _ hn`. Establish `hsub` using `InRay.weberSet_subset K hK hd L hL n ho h3 R hRay`.

Establish `hle : H ≤ R.restrictScalars ℚ`. Rewrite using `[hH]`. Use `sup_le (fun x hx => R.algebraMap_mem (⟨x, hx⟩ : K)) ?_` and prove the remaining obligations. Rewrite using `[IntermediateField.adjoin_simple_le_iff, GlobalTheory.Published.latticeCurve_j_eq, mul_div_assoc]`. Conclude with `mul_mem (ofNat_mem _ 1728) (hsub (Set.mem_insert _ _))`.

Conclude with `⟨R, inferInstance, inferInstance, hRay, ⟨{ toRingHom := (IntermediateField.inclusion hle).toRingHom commutes' := fun x => Subtype.ext (hKH x) }⟩⟩`.
-/
theorem exists_algHom_ray (hR : RayField) (K : IntermediateField ℚ ℂ) [NumberField K]
    [IsTotallyComplex K] (hK : Module.finrank ℚ K = 2) (hd : discr K < -4) (L : PeriodPair)
    (hL : ∀ z : ℂ, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) (H : IntermediateField ℚ ℂ)
    (hH : H = K ⊔ ℚ⟮(GlobalTheory.latticeCurve L).j⟯) [Algebra K H]
    (hKH : ∀ x : K, ((algebraMap K H x : H) : ℂ) = x) (n : ℕ) (ho : Odd n) (h3 : 3 ≤ n) :
    ∃ (R : IntermediateField K ℂ) (_ : NumberField R) (_ : IsAbelianGalois K R),
      IsRay R (Ideal.span {(n : 𝓞 K)}) ∧ Nonempty (H →ₐ[K] R) := by
  have hn : Ideal.span {(n : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 (by omega)
  obtain ⟨R, _, _, hRay⟩ := SmallField.exists_isRay_intermediateField hR K _ hn
  have hsub := InRay.weberSet_subset K hK hd L hL n ho h3 R hRay
  have hle : H ≤ R.restrictScalars ℚ := by
    rw [hH]
    refine sup_le (fun x hx => R.algebraMap_mem (⟨x, hx⟩ : K)) ?_
    rw [IntermediateField.adjoin_simple_le_iff, GlobalTheory.Published.latticeCurve_j_eq, mul_div_assoc]
    exact mul_mem (ofNat_mem _ 1728) (hsub (Set.mem_insert _ _))
  exact ⟨R, inferInstance, inferInstance, hRay,
    ⟨{ toRingHom := (IntermediateField.inclusion hle).toRingHom
       commutes' := fun x => Subtype.ext (hKH x) }⟩⟩

/- English proof (translation)
Take `⟨R, _, _, hRay, ⟨f⟩⟩` from `exists_algHom_ray hR K hK hd L hL H hH hKH 3 (by decide) le_rfl`. Take `⟨S, _, _, hSay, ⟨g⟩⟩` from `exists_algHom_ray hR K hK hd L hL H hH hKH 5 (by decide) (by norm_num)`. Take `⟨hN, hA, hf⟩` from `WeberUnram.of_algHom f`. Take `⟨-, -, hg⟩` from `WeberUnram.of_algHom g`. Use `⟨hN, inferInstance, fun 𝔭 => ?_, ?_⟩` and prove the remaining obligations.

Distinguish the cases in `h : 𝔭.asIdeal ∣ Ideal.span {((3 : ℕ) : 𝓞 K)}`. Use `hg 𝔭 (hSay.1 𝔭 fun h' => 𝔭.isPrime.ne_top ?_)` and prove the remaining obligations. Rewrite `h`, `h'` using `[Ideal.dvd_span_singleton]`. Rewrite using `[Ideal.eq_top_iff_one]`. Use `sub_mem (𝔭.asIdeal.mul_mem_left 2 h) h'` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Evaluate the numerical expressions. Conclude with `hf 𝔭 (hRay.1 𝔭 h)`. Establish `hn : Ideal.span {((3 : ℕ) : 𝓞 K)} ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`.

Conclude with `Nat.cast_ne_zero.2 (by omega)`. Establish `h1` using `RayDegree.finrank_le K R _ hn hRay`. Establish `he : IsEmpty (K →+* ℝ)` using `⟨fun φ => by`. Use `IsTotallyComplex.complexEmbedding_not_isReal (Complex.ofRealHom.comp φ) ?_` and prove the remaining obligations. Rewrite using `[ComplexEmbedding.isReal_iff]`.

Use extensionality with `x`. Use the proof step `simp⟩`. Rewrite `h1` using `[Fintype.card_eq_zero, Ideal.absNorm_span_natCast, RingOfIntegers.rank, hK]`. Establish `h2 : Module.finrank K H ≤ Module.finrank K R` using `LinearMap.finrank_le_finrank_of_injective (f := f.toLinearMap) f.toRingHom.injective`. Establish `h3` using `GlobalTheory.classNumber_le_abs_discr_of_finrank_eq_two K hK`.

Establish `h4 : classNumber K ≤ (discr K).natAbs`. Rewrite `h3` using `[← Int.cast_abs, ← Int.natCast_natAbs]`. Conclude with `h3` after adjusting the coercions. Use linear arithmetic over natural numbers and integers.
-/
theorem invariantField (hR : RayField) (K : IntermediateField ℚ ℂ) [NumberField K]
    [IsTotallyComplex K] (hK : Module.finrank ℚ K = 2) (hd : discr K < -4) (L : PeriodPair)
    (hL : ∀ z : ℂ, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) (H : IntermediateField ℚ ℂ)
    (hH : H = K ⊔ ℚ⟮(GlobalTheory.latticeCurve L).j⟯) [Algebra K H]
    (hKH : ∀ x : K, ((algebraMap K H x : H) : ℂ) = x) :
    ∃ (_ : NumberField H) (_ : IsGalois K H), (∀ 𝔭 : HeightOneSpectrum (𝓞 K), UnramIn H 𝔭) ∧
      Module.finrank K H ≤ 9 * (discr K).natAbs := by
  obtain ⟨R, _, _, hRay, ⟨f⟩⟩ := exists_algHom_ray hR K hK hd L hL H hH hKH 3 (by decide) le_rfl
  obtain ⟨S, _, _, hSay, ⟨g⟩⟩ :=
    exists_algHom_ray hR K hK hd L hL H hH hKH 5 (by decide) (by norm_num)
  obtain ⟨hN, hA, hf⟩ := WeberUnram.of_algHom f
  obtain ⟨-, -, hg⟩ := WeberUnram.of_algHom g
  refine ⟨hN, inferInstance, fun 𝔭 => ?_, ?_⟩
  · by_cases h : 𝔭.asIdeal ∣ Ideal.span {((3 : ℕ) : 𝓞 K)}
    · refine hg 𝔭 (hSay.1 𝔭 fun h' => 𝔭.isPrime.ne_top ?_)
      rw [Ideal.dvd_span_singleton] at h h'
      rw [Ideal.eq_top_iff_one]
      have := sub_mem (𝔭.asIdeal.mul_mem_left 2 h) h'
      convert this using 1
      norm_num
    · exact hf 𝔭 (hRay.1 𝔭 h)
  · have hn : Ideal.span {((3 : ℕ) : 𝓞 K)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact Nat.cast_ne_zero.2 (by omega)
    have h1 := RayDegree.finrank_le K R _ hn hRay
    have he : IsEmpty (K →+* ℝ) := ⟨fun φ => by
      refine IsTotallyComplex.complexEmbedding_not_isReal (Complex.ofRealHom.comp φ) ?_
      rw [ComplexEmbedding.isReal_iff]
      ext x
      simp⟩
    rw [Fintype.card_eq_zero, Ideal.absNorm_span_natCast, RingOfIntegers.rank, hK] at h1
    have h2 : Module.finrank K H ≤ Module.finrank K R :=
      LinearMap.finrank_le_finrank_of_injective (f := f.toLinearMap) f.toRingHom.injective
    have h3 := GlobalTheory.classNumber_le_abs_discr_of_finrank_eq_two K hK
    have h4 : classNumber K ≤ (discr K).natAbs := by
      rw [← Int.cast_abs, ← Int.natCast_natAbs] at h3
      exact_mod_cast h3
    omega

/- English proof (translation)
Use `letI : Algebra H M := (IntermediateField.inclusion hHM).toAlgebra`. Use `letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra`. Use `letI : Algebra F M := (IntermediateField.inclusion (hFH.trans hHM)).toAlgebra`. Use `haveI : IsScalarTower F H M := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Use `haveI : IsScalarTower F M ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl`.

Use `haveI : IsScalarTower H M ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Use `haveI : IsScalarTower F H ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Use `TorsionRam.isGalois A (fun z hz => ⟨⟨z, ?_⟩, rfl⟩) fun T h1 h2 z => ?_` and prove the remaining obligations. Rewrite using `[hM]`. Conclude with `(le_sup_right : _ ≤ H ⊔ _) (IntermediateField.subset_adjoin ℚ _ hz)`.

Set `T' : IntermediateField ℚ ℂ` to `(T.map (algebraMap M ℂ)).toIntermediateField fun q => by simp`. Establish `hT : M ≤ T'`. Use `hM.le.trans (sup_le (fun x hx => ⟨_, h1 ⟨x, hx⟩, rfl⟩) ?_)` and prove the remaining obligations. Rewrite using `[IntermediateField.adjoin_le_iff]`. Introduce `x hx`.

Establish `hxM : x ∈ M`. Rewrite using `[hM]`. Conclude with `(le_sup_right : _ ≤ H ⊔ _) (IntermediateField.subset_adjoin ℚ _ hx)`. Conclude with `⟨⟨x, hxM⟩, h2 _ hx, rfl⟩`. Take `⟨y, hy, hyz⟩` from `hT z.2`.

Establish `: y = z` using `Subtype.ext hyz`. Conclude with `this ▸ hy`.
-/
theorem isGalois_torsion (F H M : IntermediateField ℚ ℂ) [NumberField F] [NumberField H]
    [NumberField M] (A : WeierstrassCurve F) (hFH : F ≤ H) (hHM : H ≤ M)
    (hM : M = H ⊔ IntermediateField.adjoin ℚ (torsionCoords (A.baseChange ℂ) 12)) :
    letI : Algebra H M := (IntermediateField.inclusion hHM).toAlgebra
    IsGalois H M := by
  letI : Algebra H M := (IntermediateField.inclusion hHM).toAlgebra
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Algebra F M := (IntermediateField.inclusion (hFH.trans hHM)).toAlgebra
  haveI : IsScalarTower F H M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower F M ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower H M ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower F H ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine TorsionRam.isGalois A (fun z hz => ⟨⟨z, ?_⟩, rfl⟩) fun T h1 h2 z => ?_
  · rw [hM]
    exact (le_sup_right : _ ≤ H ⊔ _) (IntermediateField.subset_adjoin ℚ _ hz)
  · let T' : IntermediateField ℚ ℂ := (T.map (algebraMap M ℂ)).toIntermediateField
      fun q => by simp
    have hT : M ≤ T' := by
      refine hM.le.trans (sup_le (fun x hx => ⟨_, h1 ⟨x, hx⟩, rfl⟩) ?_)
      rw [IntermediateField.adjoin_le_iff]
      intro x hx
      have hxM : x ∈ M := by
        rw [hM]
        exact (le_sup_right : _ ≤ H ⊔ _) (IntermediateField.subset_adjoin ℚ _ hx)
      exact ⟨⟨x, hxM⟩, h2 _ hx, rfl⟩
    obtain ⟨y, hy, hyz⟩ := hT z.2
    have : y = z := Subtype.ext hyz
    exact this ▸ hy

/- English proof (translation)
Establish `h` using `Nat.card_le_card_of_injective (fun g : GL (Fin 2) (ZMod 12) => (g : Matrix (Fin 2) (Fin 2) (ZMod 12))) Units.val_injective`. Use `h.trans (le_of_eq ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Nat.card (Fin 2 → Fin 2 → ZMod 12) = _`. Simplify using the standard rewrite rules.
-/
theorem card_GL_le : Nat.card (GL (Fin 2) (ZMod 12)) ≤ 20736 := by
  have h := Nat.card_le_card_of_injective
    (fun g : GL (Fin 2) (ZMod 12) => (g : Matrix (Fin 2) (Fin 2) (ZMod 12))) Units.val_injective
  refine h.trans (le_of_eq ?_)
  change Nat.card (Fin 2 → Fin 2 → ZMod 12) = _
  simp

/- English proof (translation)
Establish `h1 : Real.log x ≤ Real.log (2 ^ 20)` using `Real.log_le_log h0 hx`. Rewrite `h1` using `[Real.log_pow]`. Use `Real.log_two_lt_d9` as an intermediate fact. Move the coercions through the operations in `at h1`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem log_le_twenty {x : ℝ} (h0 : 0 < x) (hx : x ≤ 2 ^ 20) : Real.log x ≤ 20 := by
  have h1 : Real.log x ≤ Real.log (2 ^ 20) := Real.log_le_log h0 hx
  rw [Real.log_pow] at h1
  have := Real.log_two_lt_d9
  push_cast at h1
  linarith

/- English proof (translation)
Introduce `hR P δ`. Take `⟨K, _, _, hK, hdK, hd4, -, hO, -⟩` from `exists_hostK P.R P.host`. Take `⟨_, _, L, hL, hF, -, hg⟩` from `δ.good`. Unfold `FieldDat.M'`. Use `set d := P.host.d with hd`.

Use `set A := δ.curve`. Establish `hd0 : 0 < d` using `by omega`. Establish `hs : P.host.φ₀ P.host.sqrtMinusD ∈ K`. Take `⟨a, ha⟩` from `(hO _).1 ⟨(-1, 2), rfl⟩`. Establish `: P.host.φ₀ P.host.sqrtMinusD = ((a : K) : ℂ)`.

Rewrite using `[ha]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `(a : K).2`.

Establish `hKe : ℚ⟮GlobalTheory.Published.sqrtNegNat d⟯ = K`. Use extensionality with `z`. Rewrite using `[GlobalTheory.Published.mem_adjoin_sqrtNegNat_iff (K := K) hd0 hK (x := ⟨_, hs⟩) (Subtype.ext (by`. Use `push_cast`. Rewrite using `[← map_pow, P.host.sqrtMinusD_sq]`.

Simplify using `[hd]))]`. Conclude with `⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun h => ⟨⟨z, h⟩, rfl⟩⟩`. Establish `hL' : ∀ z : ℂ, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z`. Introduce `z`. Rewrite using `[hL z, hKe]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨⟨⟨z, h1⟩, (isIntegral_algHom_iff (K.val.toRingHom.toIntAlgHom) Subtype.val_injective).1 h2⟩, rfl⟩`. Introduce and unpack `⟨a, rfl⟩`. Conclude with `⟨(a : K).2, (isIntegral_algHom_iff (K.val.toRingHom.toIntAlgHom) Subtype.val_injective).2 a.2⟩`.

Establish `hH : hilbertField d δ.jField = K ⊔ ℚ⟮(GlobalTheory.latticeCurve L).j⟯`. Rewrite using `[hilbertField, hKe, ← hF]`. Rewrite using `[DiscRoot.discField_eq_torsionField]`. Establish `hKH : K ≤ hilbertField d δ.jField` using `hH ▸ le_sup_left`. Use `letI : Algebra K (hilbertField d δ.jField) := (IntermediateField.inclusion hKH).toAlgebra`.

Take `⟨_, _, hu, hdeg⟩` from `invariantField hR K hK hd4 L hL' _ hH fun _ => rfl`. Take `⟨hfin, hM⟩` from `TorsionDegree.finrank_torsionField_le d δ.jField A`. Use `haveI : NumberField (torsionField d A) := ⟨⟩`. Establish `hHM` using `hilbertField_le_torsionField d A`. Use `letI : Algebra (hilbertField d δ.jField) (torsionField d A) := (IntermediateField.inclusion hHM).toAlgebra`.

Use `haveI : IsGalois (hilbertField d δ.jField) (torsionField d A) := isGalois_torsion δ.jField (hilbertField d δ.jField) (torsionField d A) A le_sup_right hHM rfl`. Establish `hdn : (discr K).natAbs = d` using `by rw [hdK]; simp`. Establish `hrd` using `log_rootDiscr_le K (hilbertField d δ.jField) (torsionField d A) d hd0 hK hdn hu (TorsionRam.dvd_discr_torsionField d δ.jField A hg)`. Establish `hM'` using `hM.trans (Nat.mul_le_mul_left _ card_GL_le)`. Establish `hrel : Module.finrank (hilbertField d δ.jField) (torsionField d A) ≤ 20736`.

Rewrite `hM'` using `[← Module.finrank_mul_finrank ℚ (hilbertField d δ.jField) (torsionField d A)]`. Conclude with `Nat.le_of_mul_le_mul_left hM' Module.finrank_pos`. Rewrite `hM'` using `[← Module.finrank_mul_finrank ℚ K (hilbertField d δ.jField), hK]`. Rewrite `hdeg` using `[hdn]`. Establish `hdR : (0 : ℝ) < d` using `Nat.cast_pos.2 hd0`.

Establish `hlog : 0 ≤ Real.log d` using `Real.log_natCast_nonneg d`. Establish `key : ∀ m : ℕ, 0 < m → m ≤ d * 2 ^ 20 → Real.log m ≤ Real.log d + 20`. Introduce `m h0 hm`. Establish `h1 : Real.log m ≤ Real.log (d * 2 ^ 20)` using `Real.log_le_log (Nat.cast_pos.2 h0) (by exact_mod_cast hm)`. Rewrite `h1` using `[Real.log_mul hdR.ne' (by positivity)]`.

Use `log_le_twenty (x := 2 ^ 20) (by positivity) le_rfl` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hM2 : Module.finrank ℚ (torsionField d A) ≤ d * 2 ^ 20` using `hM'.trans ((Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hdeg)).trans (by clear * -; omega))`. Use `⟨hfin, key _ Module.finrank_pos hM2, hrd.trans ?_⟩` and prove the remaining obligations. Use `key (6 * d * Module.finrank (hilbertField d δ.jField) (torsionField d A)) (Nat.mul_pos (by omega) Module.finrank_pos) ((Nat.mul_le_mul_left _ hrel).trans (by clear * -; omega))` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sz_discField : RayField → ∀ (P : Pre) (δ : FieldDat P),
    Sz δ.M' (Real.log P.host.d + 20) (3 * Real.log P.host.d + 20) := by
  intro hR P δ
  obtain ⟨K, _, _, hK, hdK, hd4, -, hO, -⟩ := exists_hostK P.R P.host
  obtain ⟨_, _, L, hL, hF, -, hg⟩ := δ.good
  unfold FieldDat.M'
  set d := P.host.d with hd
  set A := δ.curve
  have hd0 : 0 < d := by omega
  have hs : P.host.φ₀ P.host.sqrtMinusD ∈ K := by
    obtain ⟨a, ha⟩ := (hO _).1 ⟨(-1, 2), rfl⟩
    have : P.host.φ₀ P.host.sqrtMinusD = ((a : K) : ℂ) := by
      rw [ha]; push_cast; ring
    rw [this]; exact (a : K).2
  have hKe : ℚ⟮GlobalTheory.Published.sqrtNegNat d⟯ = K := by
    ext z
    rw [GlobalTheory.Published.mem_adjoin_sqrtNegNat_iff (K := K) hd0 hK (x := ⟨_, hs⟩)
      (Subtype.ext (by
        push_cast
        rw [← map_pow, P.host.sqrtMinusD_sq]; simp [hd]))]
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun h => ⟨⟨z, h⟩, rfl⟩⟩
  have hL' : ∀ z : ℂ, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z := by
    intro z
    rw [hL z, hKe]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨⟨z, h1⟩, (isIntegral_algHom_iff (K.val.toRingHom.toIntAlgHom)
        Subtype.val_injective).1 h2⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨(a : K).2, (isIntegral_algHom_iff (K.val.toRingHom.toIntAlgHom)
        Subtype.val_injective).2 a.2⟩
  have hH : hilbertField d δ.jField = K ⊔ ℚ⟮(GlobalTheory.latticeCurve L).j⟯ := by
    rw [hilbertField, hKe, ← hF]
  rw [DiscRoot.discField_eq_torsionField]
  have hKH : K ≤ hilbertField d δ.jField := hH ▸ le_sup_left
  letI : Algebra K (hilbertField d δ.jField) := (IntermediateField.inclusion hKH).toAlgebra
  obtain ⟨_, _, hu, hdeg⟩ := invariantField hR K hK hd4 L hL' _ hH fun _ => rfl
  obtain ⟨hfin, hM⟩ := TorsionDegree.finrank_torsionField_le d δ.jField A
  haveI : NumberField (torsionField d A) := ⟨⟩
  have hHM := hilbertField_le_torsionField d A
  letI : Algebra (hilbertField d δ.jField) (torsionField d A) :=
    (IntermediateField.inclusion hHM).toAlgebra
  haveI : IsGalois (hilbertField d δ.jField) (torsionField d A) :=
    isGalois_torsion δ.jField (hilbertField d δ.jField) (torsionField d A) A le_sup_right hHM rfl
  have hdn : (discr K).natAbs = d := by rw [hdK]; simp
  have hrd := log_rootDiscr_le K (hilbertField d δ.jField) (torsionField d A) d hd0 hK hdn hu
    (TorsionRam.dvd_discr_torsionField d δ.jField A hg)
  have hM' := hM.trans (Nat.mul_le_mul_left _ card_GL_le)
  have hrel : Module.finrank (hilbertField d δ.jField) (torsionField d A) ≤ 20736 := by
    rw [← Module.finrank_mul_finrank ℚ (hilbertField d δ.jField) (torsionField d A)] at hM'
    exact Nat.le_of_mul_le_mul_left hM' Module.finrank_pos
  rw [← Module.finrank_mul_finrank ℚ K (hilbertField d δ.jField), hK] at hM'
  rw [hdn] at hdeg
  have hdR : (0 : ℝ) < d := Nat.cast_pos.2 hd0
  have hlog : 0 ≤ Real.log d := Real.log_natCast_nonneg d
  have key : ∀ m : ℕ, 0 < m → m ≤ d * 2 ^ 20 → Real.log m ≤ Real.log d + 20 := by
    intro m h0 hm
    have h1 : Real.log m ≤ Real.log (d * 2 ^ 20) :=
      Real.log_le_log (Nat.cast_pos.2 h0) (by exact_mod_cast hm)
    rw [Real.log_mul hdR.ne' (by positivity)] at h1
    have := log_le_twenty (x := 2 ^ 20) (by positivity) le_rfl
    linarith
  have hM2 : Module.finrank ℚ (torsionField d A) ≤ d * 2 ^ 20 :=
    hM'.trans ((Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hdeg)).trans
      (by clear * -; omega))
  refine ⟨hfin, key _ Module.finrank_pos hM2, hrd.trans ?_⟩
  have := key (6 * d * Module.finrank (hilbertField d δ.jField) (torsionField d A))
    (Nat.mul_pos (by omega) Module.finrank_pos)
    ((Nat.mul_le_mul_left _ hrel).trans (by clear * -; omega))
  linarith

end GlobalTheory.Mem.Fld.TorsionSize
