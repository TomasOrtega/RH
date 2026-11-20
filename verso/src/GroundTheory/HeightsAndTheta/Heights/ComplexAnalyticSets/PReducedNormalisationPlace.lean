import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StReducedNormalisationPlace
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PMinimalPrimePlace
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets MinimalPrimePlace

noncomputable section

namespace ReducedNormalisationPlace

variable {A B : Type*} [CommRing A] [CommRing B]

/- English proof (translation)
Rewrite using `[IsLocalization.map_mk', IsFractionRing.mk'_eq_zero_iff_eq_zero, RingHom.mem_ker]`.
-/
theorem fracMap_mk'_eq_zero_iff [IsDomain B] (π : A →+* B) (hker : RingHom.ker π ∈ minimalPrimes A) (a : A)
    (u : nonZeroDivisors A) :
    fracMap π hker (IsLocalization.mk' (FractionRing A) a u) = 0 ↔ a ∈ RingHom.ker π := by
  rw [IsLocalization.map_mk', IsFractionRing.mk'_eq_zero_iff_eq_zero, RingHom.mem_ker]

/- English proof (translation)
Take `⟨⟨a, u⟩, rfl⟩` from `IsLocalization.mk'_surjective (nonZeroDivisors A) z`. Rewrite using `[fracMap_mk'_eq_zero_iff, fracMap_mk'_eq_zero_iff, h]`.
-/
theorem fracMap_eq_zero_iff {C : Type*} [CommRing C] [IsDomain B] [IsDomain C] (π : A →+* B) (π' : A →+* C)
    (hker : RingHom.ker π ∈ minimalPrimes A) (hker' : RingHom.ker π' ∈ minimalPrimes A)
    (h : RingHom.ker π = RingHom.ker π') (z : FractionRing A) :
    fracMap π hker z = 0 ↔ fracMap π' hker' z = 0 := by
  obtain ⟨⟨a, u⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors A) z
  rw [fracMap_mk'_eq_zero_iff, fracMap_mk'_eq_zero_iff, h]

/- English proof (translation)
Take `⟨⟨a, u⟩, rfl⟩` from `IsLocalization.mk'_surjective (nonZeroDivisors A) z`. Use `show IsLocalization.mk' (FractionRing A) a u = 0`. Rewrite using `[eq_zero_of_forall_mem_minimalPrimes fun p hp ↦ h p hp a u rfl, IsLocalization.mk'_zero]`.
-/
theorem eq_zero_of_forall_num_mem [IsReduced A] (z : FractionRing A)
    (h : ∀ p ∈ minimalPrimes A, ∀ (a : A) (u : nonZeroDivisors A),
      z = IsLocalization.mk' (FractionRing A) a u → a ∈ p) : z = 0 := by
  obtain ⟨⟨a, u⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors A) z
  show IsLocalization.mk' (FractionRing A) a u = 0
  rw [eq_zero_of_forall_mem_minimalPrimes fun p hp ↦ h p hp a u rfl, IsLocalization.mk'_zero]

/- English proof (translation)
Use `hp.1.1` as an intermediate fact. Establish `hk : RingHom.ker (Ideal.Quotient.mk p) ∈ minimalPrimes A` using `by rwa [Ideal.mk_ker]`. Take `⟨e, he1, hek, -⟩` from `exists_fracMap_unit (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective hk`. Establish `he : IsIntegral A e`. Simplify using `using isIntegral_mul_of_fracMap _ Ideal.Quotient.mk_surjective hk (x := 1) he1 hek (by rw [map_one]; exact isIntegral_one)`.

Use `⟨⟨e, he⟩, fun B _ _ π _ hker ↦ ⟨?_, fun z hz ↦ hek z ?_⟩⟩` and prove the remaining obligations. Establish `hπ : RingHom.ker π ∈ minimalPrimes A` using `by rw [hker]; exact hp`. Rewrite using `[← sub_eq_zero, ← map_one (fracMap π hπ), ← map_sub, fracMap_eq_zero_iff π (Ideal.Quotient.mk p) hπ hk (by rw [hker, Ideal.mk_ker]), map_sub, he1, map_one, sub_self]`. Establish `hπ : RingHom.ker π ∈ minimalPrimes A` using `by rw [hker]; exact hp`. Conclude with `(fracMap_eq_zero_iff π (Ideal.Quotient.mk p) hπ hk (by rw [hker, Ideal.mk_ker]) z).1 hz`.
-/
theorem exists_idempotent [IsNoetherianRing A] [IsReduced A] (p : Ideal A) (hp : p ∈ minimalPrimes A) :
    ∃ e : integralClosure A (FractionRing A), ∀ (B : Type) [CommRing B] [IsDomain B] (π : A →+* B),
      Function.Surjective π → ∀ hker : RingHom.ker π = p,
        fracMap π (by rw [hker]; exact hp) e = 1 ∧
          ∀ z, fracMap π (by rw [hker]; exact hp) z = 0 → (e : FractionRing A) * z = 0 := by
  have := hp.1.1
  have hk : RingHom.ker (Ideal.Quotient.mk p) ∈ minimalPrimes A := by rwa [Ideal.mk_ker]
  obtain ⟨e, he1, hek, -⟩ := exists_fracMap_unit (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective hk
  have he : IsIntegral A e := by
    simpa using isIntegral_mul_of_fracMap _ Ideal.Quotient.mk_surjective hk (x := 1) he1 hek
      (by rw [map_one]; exact isIntegral_one)
  refine ⟨⟨e, he⟩, fun B _ _ π _ hker ↦ ⟨?_, fun z hz ↦ hek z ?_⟩⟩
  · have hπ : RingHom.ker π ∈ minimalPrimes A := by rw [hker]; exact hp
    rw [← sub_eq_zero, ← map_one (fracMap π hπ), ← map_sub,
      fracMap_eq_zero_iff π (Ideal.Quotient.mk p) hπ hk (by rw [hker, Ideal.mk_ker]), map_sub, he1, map_one,
      sub_self]
  · have hπ : RingHom.ker π ∈ minimalPrimes A := by rw [hker]; exact hp
    exact (fracMap_eq_zero_iff π (Ideal.Quotient.mk p) hπ hk (by rw [hker, Ideal.mk_ker]) z).1 hz

end ReducedNormalisationPlace

open ReducedNormalisationPlace in

/- English proof (translation)
Introduce `R _ _ _ P`. Establish `hfin` using `minimalPrimes.finite_of_isNoetherianRing R`. Use `P.isMaximal.isPrime` as an intermediate fact. Use `choose! e he using fun p (hp : p ∈ minimalPrimes R) ↦ exists_idempotent p hp`. Establish `hprodK : ∏ p ∈ hfin.toFinset, (1 - (e p : FractionRing R)) = 0`.

Use `eq_zero_of_forall_num_mem _ fun p hp a u hz ↦ ?_` and prove the remaining obligations. Use `hp.1.1` as an intermediate fact. Establish `hk : RingHom.ker (Ideal.Quotient.mk p) ∈ minimalPrimes R` using `by rwa [Ideal.mk_ker]`. Establish `h0 : fracMap (Ideal.Quotient.mk p) hk (∏ q ∈ hfin.toFinset, (1 - (e q : FractionRing R))) = 0`. Rewrite using `[map_prod]`.

Use `Finset.prod_eq_zero (hfin.mem_toFinset.2 hp) ?_` and prove the remaining obligations. Rewrite using `[map_sub, map_one, (he p hp (R ⧸ p) (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective Ideal.mk_ker).1, sub_self]`. Rewrite `h0` using `[hz, fracMap_mk'_eq_zero_iff, Ideal.mk_ker]`. Conclude with `h0`. Establish `hprod : ∏ p ∈ hfin.toFinset, (1 - e p) = 0` using `Subtype.ext (by push_cast; exact hprodK)`.

Take `⟨p, hpT, hp1⟩` from `(Ideal.IsPrime.prod_mem_iff (p := P.asIdeal)).1 (by rw [hprod]; exact P.asIdeal.zero_mem)`. Establish `hpmin : p ∈ minimalPrimes R` using `hfin.mem_toFinset.1 hpT`. Establish `hepP : e p ∉ P.asIdeal` using `fun h ↦ P.isMaximal.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using P.asIdeal.add_mem h hp1))`. Use `⟨p, hpmin, fun S _ φ hφ hkerφ ↦ ?_⟩` and prove the remaining obligations. Establish `hpr : (RingHom.ker φ).IsPrime` using `hkerφ ▸ hpmin.1.1`.

Establish `: IsDomain S` using `MulEquiv.isDomain (R ⧸ RingHom.ker φ) (RingHom.quotientKerEquivOfSurjective hφ).symm.toMulEquiv`. Establish `hker : RingHom.ker φ ∈ minimalPrimes R` using `by rw [hkerφ]; exact hpmin`. Take `⟨he1, hek⟩` from `he p hpmin S φ hφ hkerφ`. Take `⟨_, -, -, hsurj⟩` from `exists_fracMap_unit φ hφ hker`. Establish `hN : Function.Surjective (normMap φ hker)`.

Introduce `y`. Take `⟨x, hx⟩` from `hsurj y`. Establish `hint : IsIntegral R ((e p : FractionRing R) * x)` using `isIntegral_mul_of_fracMap φ hφ hker he1 hek (by rw [hx]; exact y.2)`. Use `⟨⟨_, hint⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Use `show fracMap φ hker ((e p : FractionRing R) * x) = y`.

Rewrite using `[map_mul, he1, one_mul, hx]`. Establish `hε1 : normMap φ hker (e p) = 1` using `Subtype.ext he1`. Establish `hε : ∀ z, normMap φ hker z = 0 → e p * z = 0` using `fun z hz ↦ Subtype.ext (hek z (congrArg Subtype.val hz))`. Establish `hkerP : RingHom.ker (normMap φ hker) ≤ P.asIdeal` using `fun z hz ↦ (P.isMaximal.isPrime.mem_or_mem (by rw [hε z hz]; exact P.asIdeal.zero_mem)).resolve_left hepP`. Establish `hcm : (P.asIdeal.map (normMap φ hker)).comap (normMap φ hker) = P.asIdeal`.

Rewrite using `[Ideal.comap_map_of_surjective _ hN, ← RingHom.ker_eq_comap_bot, sup_eq_left.2 hkerP]`. Establish `hmax : (P.asIdeal.map (normMap φ hker)).IsMaximal` using `(Ideal.map_eq_top_or_isMaximal_of_surjective _ hN P.isMaximal).resolve_left fun h ↦ P.isMaximal.ne_top (by rw [← hcm, h, Ideal.comap_top])`. Take `⟨E, hE⟩` from `exists_localization_ringEquiv (normMap φ hker) hN (e p) hε1 hε (P.asIdeal.map (normMap φ hker))`. Use `⟨⟨_, hmax⟩, fun x ↦ ?_⟩` and prove the remaining obligations. Establish `key : ∀ (Q : Ideal (integralClosure R (FractionRing R))) [Q.IsPrime], Q = P.asIdeal → ∀ E' : Localization.AtPrime Q ≃+* Localization.AtPrime (P.asIdeal.map (normMap φ hker)), (∀ r, E' (algebraMap _ _ r) = algebraMap _ _ (normMap φ hker r)) → Ring.ord (Localization.AtPrime P.asIde …`.

Introduce and unpack `Q _ rfl E' hE'`. Rewrite using `[← ord_ringEquiv (R := Localization.AtPrime P.asIdeal) (S := Localization.AtPrime (P.asIdeal.map (normMap φ hker))) E', hE', normMap_algebraMap]`. Conclude with `key _ hcm E hE`.
-/
theorem ReducedNormalisationPlace.proof : ReducedNormalisationPlace.Statement := by
  intro R _ _ _ P
  have hfin := minimalPrimes.finite_of_isNoetherianRing R
  have := P.isMaximal.isPrime
  choose! e he using fun p (hp : p ∈ minimalPrimes R) ↦ exists_idempotent p hp
  have hprodK : ∏ p ∈ hfin.toFinset, (1 - (e p : FractionRing R)) = 0 := by
    refine eq_zero_of_forall_num_mem _ fun p hp a u hz ↦ ?_
    have := hp.1.1
    have hk : RingHom.ker (Ideal.Quotient.mk p) ∈ minimalPrimes R := by rwa [Ideal.mk_ker]
    have h0 : fracMap (Ideal.Quotient.mk p) hk (∏ q ∈ hfin.toFinset, (1 - (e q : FractionRing R))) = 0 := by
      rw [map_prod]
      refine Finset.prod_eq_zero (hfin.mem_toFinset.2 hp) ?_
      rw [map_sub, map_one,
        (he p hp (R ⧸ p) (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective Ideal.mk_ker).1, sub_self]
    rw [hz, fracMap_mk'_eq_zero_iff, Ideal.mk_ker] at h0
    exact h0
  have hprod : ∏ p ∈ hfin.toFinset, (1 - e p) = 0 := Subtype.ext (by push_cast; exact hprodK)
  obtain ⟨p, hpT, hp1⟩ := (Ideal.IsPrime.prod_mem_iff (p := P.asIdeal)).1
    (by rw [hprod]; exact P.asIdeal.zero_mem)
  have hpmin : p ∈ minimalPrimes R := hfin.mem_toFinset.1 hpT
  have hepP : e p ∉ P.asIdeal := fun h ↦
    P.isMaximal.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using P.asIdeal.add_mem h hp1))
  refine ⟨p, hpmin, fun S _ φ hφ hkerφ ↦ ?_⟩
  have hpr : (RingHom.ker φ).IsPrime := hkerφ ▸ hpmin.1.1
  have : IsDomain S :=
    MulEquiv.isDomain (R ⧸ RingHom.ker φ) (RingHom.quotientKerEquivOfSurjective hφ).symm.toMulEquiv
  have hker : RingHom.ker φ ∈ minimalPrimes R := by rw [hkerφ]; exact hpmin
  obtain ⟨he1, hek⟩ := he p hpmin S φ hφ hkerφ
  obtain ⟨_, -, -, hsurj⟩ := exists_fracMap_unit φ hφ hker
  have hN : Function.Surjective (normMap φ hker) := by
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    have hint : IsIntegral R ((e p : FractionRing R) * x) :=
      isIntegral_mul_of_fracMap φ hφ hker he1 hek (by rw [hx]; exact y.2)
    refine ⟨⟨_, hint⟩, Subtype.ext ?_⟩
    show fracMap φ hker ((e p : FractionRing R) * x) = y
    rw [map_mul, he1, one_mul, hx]
  have hε1 : normMap φ hker (e p) = 1 := Subtype.ext he1
  have hε : ∀ z, normMap φ hker z = 0 → e p * z = 0 := fun z hz ↦
    Subtype.ext (hek z (congrArg Subtype.val hz))
  have hkerP : RingHom.ker (normMap φ hker) ≤ P.asIdeal := fun z hz ↦
    (P.isMaximal.isPrime.mem_or_mem (by rw [hε z hz]; exact P.asIdeal.zero_mem)).resolve_left hepP
  have hcm : (P.asIdeal.map (normMap φ hker)).comap (normMap φ hker) = P.asIdeal := by
    rw [Ideal.comap_map_of_surjective _ hN, ← RingHom.ker_eq_comap_bot, sup_eq_left.2 hkerP]
  have hmax : (P.asIdeal.map (normMap φ hker)).IsMaximal :=
    (Ideal.map_eq_top_or_isMaximal_of_surjective _ hN P.isMaximal).resolve_left fun h ↦
      P.isMaximal.ne_top (by rw [← hcm, h, Ideal.comap_top])
  obtain ⟨E, hE⟩ := exists_localization_ringEquiv (normMap φ hker) hN (e p) hε1 hε
    (P.asIdeal.map (normMap φ hker))
  refine ⟨⟨_, hmax⟩, fun x ↦ ?_⟩
  have key : ∀ (Q : Ideal (integralClosure R (FractionRing R))) [Q.IsPrime], Q = P.asIdeal →
      ∀ E' : Localization.AtPrime Q ≃+* Localization.AtPrime (P.asIdeal.map (normMap φ hker)),
        (∀ r, E' (algebraMap _ _ r) = algebraMap _ _ (normMap φ hker r)) →
        Ring.ord (Localization.AtPrime P.asIdeal)
            (algebraMap _ (Localization.AtPrime P.asIdeal) (algebraMap R (integralClosure R (FractionRing R)) x)) =
          Ring.ord (Localization.AtPrime (P.asIdeal.map (normMap φ hker)))
            (algebraMap _ (Localization.AtPrime (P.asIdeal.map (normMap φ hker)))
              (algebraMap S (integralClosure S (FractionRing S)) (φ x))) := by
    rintro Q _ rfl E' hE'
    rw [← ord_ringEquiv (R := Localization.AtPrime P.asIdeal)
      (S := Localization.AtPrime (P.asIdeal.map (normMap φ hker))) E', hE', normMap_algebraMap]
  exact key _ hcm E hE

end

end GroundTheory.Heights₂.Heights
