import Mathlib
import GroundTheory.GlobalFields.TateThesis.Conductor

open Topology Filter NumberField IsDedekindDomain Function
open scoped NumberField.AdeleRing

namespace GroundTheory.Global

noncomputable section

section Ideals

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

omit [IsDedekindDomain R] in

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Assume the negation of the conclusion as `hk`. Establish `hle : v.asIdeal ^ k ≤ v.asIdeal` using `Ideal.pow_le_self hk`. Rewrite `hle` using `[h, Ideal.one_eq_top, top_le_iff]`.

Conclude with `v.isPrime.ne_top hle`. Introduce and unpack `rfl`. Conclude with `pow_zero _`.
-/
theorem asIdeal_pow_eq_one_iff (v : HeightOneSpectrum R) {k : ℕ} : v.asIdeal ^ k = 1 ↔ k = 0 := by
  constructor
  · intro h
    by_contra hk
    have hle : v.asIdeal ^ k ≤ v.asIdeal := Ideal.pow_le_self hk
    rw [h, Ideal.one_eq_top, top_le_iff] at hle
    exact v.isPrime.ne_top hle
  · rintro rfl
    exact pow_zero _

omit [IsDedekindDomain R] in
/- English proof (translation)
Use extensionality with `v`. Simplify using `only [mem_mulSupport, mem_support, ne_eq, asIdeal_pow_eq_one_iff]`.
-/
theorem mulSupport_asIdeal_pow (a : HeightOneSpectrum R → ℕ) :
    mulSupport (fun v : HeightOneSpectrum R ↦ v.asIdeal ^ a v) = support a := by
  ext v
  simp only [mem_mulSupport, mem_support, ne_eq, asIdeal_pow_eq_one_iff]

/- English proof (translation)
The claim follows from `finprod_induction (fun I : Ideal R ↦ I ≠ ⊥) one_ne_zero (fun _ _ hx hy ↦ mul_ne_zero hx hy) fun v ↦ pow_ne_zero _ v.ne_bot`.
-/
theorem finprod_asIdeal_pow_ne_bot (a : HeightOneSpectrum R → ℕ) :
    (∏ᶠ v : HeightOneSpectrum R, v.asIdeal ^ a v) ≠ ⊥ :=
  finprod_induction (fun I : Ideal R ↦ I ≠ ⊥) one_ne_zero (fun _ _ hx hy ↦ mul_ne_zero hx hy)
    fun v ↦ pow_ne_zero _ v.ne_bot

/- English proof (translation)
Establish `hfa : HasFiniteMulSupport fun v : HeightOneSpectrum R ↦ v.asIdeal ^ a v`. Rewrite using `[HasFiniteMulSupport, mulSupport_asIdeal_pow]`. Conclude with `ha`. Prove the components needed by the constructor for the conclusion. Introduce `h v`.

Establish `h1 : v.asIdeal ^ a v ∣ I` using `(finprod_mem_dvd v hfa).trans h`. Establish `h2` using `HeightOneSpectrum.multiplicity_le_of_ideal_ge v (Ideal.le_of_dvd h1) hI`. Rewrite `h2` using `[multiplicity_pow_self_of_prime (HeightOneSpectrum.prime v)]`. Then use the resulting hypothesis. Introduce `h`. Establish `hm : HasFiniteMulSupport fun v : HeightOneSpectrum R ↦ v.asIdeal ^ multiplicity v.asIdeal I`.

Simplify `Ideal.hasFiniteMulSupport hI` using `only [HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity hI]`. Establish `hmb : HasFiniteMulSupport fun v : HeightOneSpectrum R ↦ v.asIdeal ^ (multiplicity v.asIdeal I - a v)`. Rewrite `hm`, the goal using `[HasFiniteMulSupport, mulSupport_asIdeal_pow]`. Use `hm.subset fun v hv ↦ ?_` and prove the remaining obligations. Simplify using `only [mem_support, ne_eq] at hv ⊢`.

Use linear arithmetic over natural numbers and integers. Establish `hsplit : (fun v : HeightOneSpectrum R ↦ v.asIdeal ^ multiplicity v.asIdeal I) = fun v ↦ v.asIdeal ^ a v * v.asIdeal ^ (multiplicity v.asIdeal I - a v)`. Use function extensionality and compare the values at `fun v ↦ by rw [← pow_add, Nat.add_sub_cancel' (h v)]`. Use `conv_rhs => rw [← Ideal.finprod_heightOneSpectrum_pow_multiplicity hI]`. Rewrite using `[hsplit, finprod_mul_distrib hfa hmb]`.

Conclude with `dvd_mul_right _ _`.
-/
theorem finprod_asIdeal_pow_dvd_iff {a : HeightOneSpectrum R → ℕ} (ha : (support a).Finite)
    {I : Ideal R} (hI : I ≠ ⊥) :
    (∏ᶠ v : HeightOneSpectrum R, v.asIdeal ^ a v) ∣ I ↔
      ∀ v : HeightOneSpectrum R, a v ≤ multiplicity v.asIdeal I := by
  have hfa : HasFiniteMulSupport fun v : HeightOneSpectrum R ↦ v.asIdeal ^ a v := by
    rw [HasFiniteMulSupport, mulSupport_asIdeal_pow]
    exact ha
  constructor
  · intro h v
    have h1 : v.asIdeal ^ a v ∣ I := (finprod_mem_dvd v hfa).trans h
    have h2 := HeightOneSpectrum.multiplicity_le_of_ideal_ge v (Ideal.le_of_dvd h1) hI
    rwa [multiplicity_pow_self_of_prime (HeightOneSpectrum.prime v)] at h2
  · intro h
    have hm : HasFiniteMulSupport fun v : HeightOneSpectrum R ↦
        v.asIdeal ^ multiplicity v.asIdeal I := by
      simpa only [HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity hI] using
        Ideal.hasFiniteMulSupport hI
    have hmb : HasFiniteMulSupport fun v : HeightOneSpectrum R ↦
        v.asIdeal ^ (multiplicity v.asIdeal I - a v) := by
      rw [HasFiniteMulSupport, mulSupport_asIdeal_pow] at hm ⊢
      refine hm.subset fun v hv ↦ ?_
      simp only [mem_support, ne_eq] at hv ⊢
      omega
    have hsplit : (fun v : HeightOneSpectrum R ↦ v.asIdeal ^ multiplicity v.asIdeal I) =
        fun v ↦ v.asIdeal ^ a v * v.asIdeal ^ (multiplicity v.asIdeal I - a v) :=
      funext fun v ↦ by rw [← pow_add, Nat.add_sub_cancel' (h v)]
    conv_rhs => rw [← Ideal.finprod_heightOneSpectrum_pow_multiplicity hI]
    rw [hsplit, finprod_mul_distrib hfa hmb]
    exact dvd_mul_right _ _

/- English proof (translation)
Establish `hfa : HasFiniteMulSupport fun v : HeightOneSpectrum R ↦ v.asIdeal ^ a v`. Rewrite using `[HasFiniteMulSupport, mulSupport_asIdeal_pow]`. Conclude with `ha`. Prove the components needed by the constructor for the conclusion. Introduce `h classical`.

Rewrite `h` using `[finprod_eq_prod_of_mulSupport_subset _ (s := ha.toFinset) (by rw [mulSupport_asIdeal_pow, ha.coe_toFinset])]`. Take `⟨w, hw, hvw⟩` from `((HeightOneSpectrum.prime v).dvd_finsetProd_iff _).1 h`. Establish `hvw'` using `(HeightOneSpectrum.prime v).dvd_of_dvd_pow hvw`. Establish `heq : v = w` using `HeightOneSpectrum.ext (associated_iff_eq.1 ((HeightOneSpectrum.prime v).associated_of_dvd (HeightOneSpectrum.prime w) hvw'))`. Substitute `heq` using the available equality.

Rewrite `hw` using `[Set.Finite.mem_toFinset, mem_support]`. Use linear arithmetic over natural numbers and integers. Introduce `h`. Conclude with `(dvd_pow_self _ (by omega)).trans (finprod_mem_dvd v hfa)`.
-/
theorem asIdeal_dvd_finprod_iff {a : HeightOneSpectrum R → ℕ} (ha : (support a).Finite)
    (v : HeightOneSpectrum R) :
    v.asIdeal ∣ ∏ᶠ w : HeightOneSpectrum R, w.asIdeal ^ a w ↔ 1 ≤ a v := by
  have hfa : HasFiniteMulSupport fun v : HeightOneSpectrum R ↦ v.asIdeal ^ a v := by
    rw [HasFiniteMulSupport, mulSupport_asIdeal_pow]
    exact ha
  constructor
  · intro h
    classical
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := ha.toFinset)
      (by rw [mulSupport_asIdeal_pow, ha.coe_toFinset])] at h
    obtain ⟨w, hw, hvw⟩ := ((HeightOneSpectrum.prime v).dvd_finsetProd_iff _).1 h
    have hvw' := (HeightOneSpectrum.prime v).dvd_of_dvd_pow hvw
    have heq : v = w := HeightOneSpectrum.ext (associated_iff_eq.1
      ((HeightOneSpectrum.prime v).associated_of_dvd (HeightOneSpectrum.prime w) hvw'))
    subst heq
    rw [Set.Finite.mem_toFinset, mem_support] at hw
    omega
  · intro h
    exact (dvd_pow_self _ (by omega)).trans (finprod_mem_dvd v hfa)

end Ideals

namespace IdeleGroup

variable {K : Type*} [Field K] [NumberField K] {H : Type*} [Group H] [TopologicalSpace H]

def conductor (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H) : Ideal (𝓞 K) :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K), v.asIdeal ^ conductorExponentAt χ v

omit [TopologicalSpace H] in
/- English proof (translation)
The claim follows from `finprod_asIdeal_pow_ne_bot _`.
-/
theorem conductor_ne_bot (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H) : conductor χ ≠ ⊥ :=
  finprod_asIdeal_pow_ne_bot _

def idealLevel (𝔪 : Ideal (𝓞 K)) : Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ :=
  finiteLevel fun v ↦ multiplicity v.asIdeal 𝔪

/- English proof (translation)
Rewrite using `[idealLevel, finiteLevel_le_ker_iff hH χ hχ, conductor, finprod_asIdeal_pow_dvd_iff (finite_support_conductorExponentAt hH χ hχ) h𝔪]`.
-/
theorem idealLevel_le_ker_iff (hH : NoSmallSubgroups H) (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H)
    (hχ : Continuous χ) {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) :
    idealLevel 𝔪 ≤ χ.ker ↔ conductor χ ∣ 𝔪 := by
  rw [idealLevel, finiteLevel_le_ker_iff hH χ hχ, conductor,
    finprod_asIdeal_pow_dvd_iff (finite_support_conductorExponentAt hH χ hχ) h𝔪]

/- English proof (translation)
The claim follows from `asIdeal_dvd_finprod_iff (finite_support_conductorExponentAt hH χ hχ) v`.
-/
theorem dvd_conductor_iff (hH : NoSmallSubgroups H) (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H)
    (hχ : Continuous χ) (v : HeightOneSpectrum (𝓞 K)) :
    v.asIdeal ∣ conductor χ ↔ 1 ≤ conductorExponentAt χ v :=
  asIdeal_dvd_finprod_iff (finite_support_conductorExponentAt hH χ hχ) v

/- English proof (translation)
Rewrite using `[dvd_conductor_iff hH χ hχ, ← conductorExponentAt_eq_zero_iff hH χ hχ, Nat.one_le_iff_ne_zero, not_not]`.
-/
theorem not_dvd_conductor_iff (hH : NoSmallSubgroups H) (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H)
    (hχ : Continuous χ) (v : HeightOneSpectrum (𝓞 K)) :
    ¬ v.asIdeal ∣ conductor χ ↔
      (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤
        (χ.comp (finiteUnitsSingle v)).ker := by
  rw [dvd_conductor_iff hH χ hχ, ← conductorExponentAt_eq_zero_iff hH χ hχ,
    Nat.one_le_iff_ne_zero, not_not]

def ofFinite : (FiniteAdeleRing (𝓞 K) K)ˣ →* IdeleGroup K :=
  (ContinuousMulEquiv.symm (prodEquiv K)).toMulEquiv.toMonoidHom.comp (MonoidHom.inr _ _)

/- English proof (translation)
Establish `: Continuous fun x : (FiniteAdeleRing (𝓞 K) K)ˣ ↦ ContinuousMulEquiv.symm (prodEquiv K) ((1 : (InfiniteAdeleRing K)ˣ), x)` using `(ContinuousMulEquiv.symm (prodEquiv K)).continuous.comp (continuous_const.prodMk continuous_id)`. Conclude with `this`. Use the proof step `@[simp]`.
-/
theorem continuous_ofFinite : Continuous (ofFinite (K := K)) := by
  have : Continuous fun x : (FiniteAdeleRing (𝓞 K) K)ˣ ↦
      ContinuousMulEquiv.symm (prodEquiv K) ((1 : (InfiniteAdeleRing K)ˣ), x) :=
    (ContinuousMulEquiv.symm (prodEquiv K)).continuous.comp (continuous_const.prodMk continuous_id)
  exact this

@[simp]
/- English proof (translation)
Express the relevant statement in the definitionally equal form `((prodEquiv K) ((ContinuousMulEquiv.symm (prodEquiv K)) (1, x))).2 = x`. Rewrite using `[ContinuousMulEquiv.apply_symm_apply]`. Use the proof step `@[simp]`.
-/
theorem toFinite_ofFinite (x : (FiniteAdeleRing (𝓞 K) K)ˣ) : toFinite K (ofFinite x) = x := by
  change ((prodEquiv K) ((ContinuousMulEquiv.symm (prodEquiv K)) (1, x))).2 = x
  rw [ContinuousMulEquiv.apply_symm_apply]

@[simp]
/- English proof (translation)
Express the relevant statement in the definitionally equal form `((prodEquiv K) ((ContinuousMulEquiv.symm (prodEquiv K)) (1, x))).1 = 1`. Rewrite using `[ContinuousMulEquiv.apply_symm_apply]`.
-/
theorem toInfinite_ofFinite (x : (FiniteAdeleRing (𝓞 K) K)ˣ) : toInfinite K (ofFinite x) = 1 := by
  change ((prodEquiv K) ((ContinuousMulEquiv.symm (prodEquiv K)) (1, x))).1 = 1
  rw [ContinuousMulEquiv.apply_symm_apply]

/- English proof (translation)
Rewrite using `[mem_standardOpenSubgroup, mem_finiteLevel]`. Use `forall_congr' fun v ↦ ?_` and prove the remaining obligations. Rewrite using `[Pi.zero_apply, unitsLevel_zero, Submonoid.mem_units_iff]`. Both sides reduce to the same expression.
-/
theorem mem_standardOpenSubgroup_iff_toFinite_mem (x : IdeleGroup K) :
    x ∈ standardOpenSubgroup K ↔ toFinite K x ∈ finiteLevel 0 := by
  rw [mem_standardOpenSubgroup, mem_finiteLevel]
  refine forall_congr' fun v ↦ ?_
  rw [Pi.zero_apply, unitsLevel_zero, Submonoid.mem_units_iff]
  rfl

/- English proof (translation)
Rewrite using `[Subgroup.map_le_iff_le_comap, MonoidHom.comap_ker]`. Conclude with `idealLevel_le_ker_iff hH _ (hχ.comp continuous_ofFinite) h𝔪`.
-/
theorem map_idealLevel_le_ker_iff (hH : NoSmallSubgroups H) (χ : IdeleGroup K →* H)
    (hχ : Continuous χ) {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) :
    (idealLevel 𝔪).map ofFinite ≤ χ.ker ↔ conductor (χ.comp ofFinite) ∣ 𝔪 := by
  rw [Subgroup.map_le_iff_le_comap, MonoidHom.comap_ker]
  exact idealLevel_le_ker_iff hH _ (hχ.comp continuous_ofFinite) h𝔪

end IdeleGroup

end

end GroundTheory.Global
