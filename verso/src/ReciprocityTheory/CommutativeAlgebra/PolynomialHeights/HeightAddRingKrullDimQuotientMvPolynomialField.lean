import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.PolyCM
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Integral

namespace ReciprocityTheory.CA

universe u

/- English proof (translation)
Use `⟨inferInstance, 0, by simp [ringKrullDim_eq_zero_of_field], [], rfl, by simp, RingTheory.Sequence.IsRegular.nil K K⟩` and prove the remaining obligations.
-/
theorem isCM_field (K : Type*) [Field K] : IsCM K := by
  refine ⟨inferInstance, 0, by simp [ringKrullDim_eq_zero_of_field], [], rfl, by simp,
    RingTheory.Sequence.IsRegular.nil K K⟩

/- English proof (translation)
Establish `h1` using `(Ideal.eq_bot_or_top (𝔐.comap MvPolynomial.C)).resolve_right (inferInstance : (𝔐.comap (MvPolynomial.C : K →+* MvPolynomial (Fin N) K)).IsPrime).ne_top`. Establish `h2` using `(Ideal.eq_bot_or_top (IsLocalRing.maximalIdeal K)).resolve_right (IsLocalRing.maximalIdeal.isMaximal K).ne_top`. Rewrite using `[h1, h2]`.
-/
theorem comap_C_eq_maximalIdeal_field (K : Type*) [Field K] (N : ℕ)
    (𝔐 : Ideal (MvPolynomial (Fin N) K)) [𝔐.IsMaximal] :
    𝔐.comap MvPolynomial.C = IsLocalRing.maximalIdeal K := by
  have h1 := (Ideal.eq_bot_or_top (𝔐.comap MvPolynomial.C)).resolve_right
    (inferInstance : (𝔐.comap (MvPolynomial.C : K →+* MvPolynomial (Fin N) K)).IsPrime).ne_top
  have h2 := (Ideal.eq_bot_or_top (IsLocalRing.maximalIdeal K)).resolve_right
    (IsLocalRing.maximalIdeal.isMaximal K).ne_top
  rw [h1, h2]

/- English proof (translation)
Take `⟨hcm, hh⟩` from `isCM_localization_mvPolynomial (isCM_field K) N 𝔐 (comap_C_eq_maximalIdeal_field K N 𝔐)`. Use `⟨hcm, ?_⟩` and prove the remaining obligations. Rewrite `hh` using `[ringKrullDim_eq_zero_of_field K, zero_add]`. Conclude with `hh` after adjusting the coercions.
-/
theorem height_maximal_mvPolynomial_field (K : Type*) [Field K] (N : ℕ)
    (𝔐 : Ideal (MvPolynomial (Fin N) K)) [𝔐.IsMaximal] :
    IsCM (Localization.AtPrime 𝔐) ∧ 𝔐.height = N := by
  obtain ⟨hcm, hh⟩ := isCM_localization_mvPolynomial (isCM_field K) N 𝔐
    (comap_C_eq_maximalIdeal_field K N 𝔐)
  refine ⟨hcm, ?_⟩
  rw [ringKrullDim_eq_zero_of_field K, zero_add] at hh
  exact_mod_cast hh

/- English proof (translation)
Take `⟨hcm, hh⟩` from `height_maximal_mvPolynomial_field K N 𝔐`. Rewrite using `[← hh]`. Conclude with `(height_eq_add_of_isCM_localization 𝔐 𝔔 hcm hle).symm`.
-/
theorem height_add_height_map_eq_mvPolynomial_field (K : Type*) [Field K] (N : ℕ)
    (𝔔 𝔐 : Ideal (MvPolynomial (Fin N) K)) [𝔔.IsPrime] [𝔐.IsMaximal] (hle : 𝔔 ≤ 𝔐) :
    𝔔.height + (𝔐.map (Ideal.Quotient.mk 𝔔)).height = N := by
  obtain ⟨hcm, hh⟩ := height_maximal_mvPolynomial_field K N 𝔐
  rw [← hh]
  exact (height_eq_add_of_isCM_localization 𝔐 𝔔 hcm hle).symm

/- English proof (translation)
Use `haveI : (𝔪.comap (Ideal.Quotient.mk 𝔔)).IsMaximal := Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective`. Establish `hle : 𝔔 ≤ 𝔪.comap (Ideal.Quotient.mk 𝔔)` using `fun x hx => Ideal.mem_comap.2 (by rw [Ideal.Quotient.eq_zero_iff_mem.2 hx]; exact 𝔪.zero_mem)`. Establish `h` using `height_add_height_map_eq_mvPolynomial_field K N 𝔔 (𝔪.comap (Ideal.Quotient.mk 𝔔)) hle`. Rewrite `h` using `[Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]`. Then use the resulting hypothesis.
-/
theorem height_add_height_maximal_quotient_field (K : Type*) [Field K] (N : ℕ)
    (𝔔 : Ideal (MvPolynomial (Fin N) K)) [𝔔.IsPrime]
    (𝔪 : Ideal (MvPolynomial (Fin N) K ⧸ 𝔔)) [h𝔪 : 𝔪.IsMaximal] :
    𝔔.height + 𝔪.height = N := by
  haveI : (𝔪.comap (Ideal.Quotient.mk 𝔔)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  have hle : 𝔔 ≤ 𝔪.comap (Ideal.Quotient.mk 𝔔) := fun x hx =>
    Ideal.mem_comap.2 (by rw [Ideal.Quotient.eq_zero_iff_mem.2 hx]; exact 𝔪.zero_mem)
  have h := height_add_height_map_eq_mvPolynomial_field K N 𝔔 (𝔪.comap (Ideal.Quotient.mk 𝔔)) hle
  rwa [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at h

/- English proof (translation)
Take `⟨𝔪0, h𝔪0⟩` from `Ideal.exists_maximal (MvPolynomial (Fin N) K ⧸ 𝔔)`. Establish `cancel : ∀ a b : ℕ∞, 𝔔.height + a = N → 𝔔.height + b = N → a = b`. Introduce `a b ha hb`. Establish `hq : 𝔔.height ≠ ⊤` using `fun h => by rw [h, top_add] at ha; exact ENat.top_ne_coe N ha`. Establish `ha' : a ≠ ⊤` using `fun h => by rw [h, add_top] at ha; exact ENat.top_ne_coe N ha`.

Establish `hb' : b ≠ ⊤` using `fun h => by rw [h, add_top] at hb; exact ENat.top_ne_coe N hb`. Take `⟨q, hq0⟩` from `ENat.ne_top_iff_exists.1 hq`. Take `⟨a0, ha0⟩` from `ENat.ne_top_iff_exists.1 ha'`. Take `⟨b0, hb0⟩` from `ENat.ne_top_iff_exists.1 hb'`. Rewrite `ha` using `[← hq0, ← ha0]`.

Rewrite `hb` using `[← hq0, ← hb0]`. Rewrite using `[← ha0, ← hb0]`. Establish `e1 : q + a0 = N` using `by exact_mod_cast ha`. Establish `e2 : q + b0 = N` using `by exact_mod_cast hb`. Use `congr 1`.

Use linear arithmetic over natural numbers and integers. Establish `hall : ∀ 𝔪 : Ideal (MvPolynomial (Fin N) K ⧸ 𝔔), 𝔪.IsMaximal → 𝔪.height = 𝔪0.height`. Introduce `𝔪 h𝔪`. Conclude with `cancel _ _ (height_add_height_maximal_quotient_field K N 𝔔 𝔪) (height_add_height_maximal_quotient_field K N 𝔔 𝔪0)`. Establish `hsup : (⨆ I : Ideal (MvPolynomial (Fin N) K ⧸ 𝔔), ⨆ (_ : I.IsMaximal), I.height) = 𝔪0.height` using `le_antisymm (iSup₂_le fun I hI => (hall I hI).le) (le_iSup₂_of_le 𝔪0 h𝔪0 le_rfl)`.

Rewrite using `[← Ideal.sup_isMaximal_height_eq_ringKrullDim, hsup]`. Establish `e` using `height_add_height_maximal_quotient_field K N 𝔔 𝔪0`. Conclude with `e` after adjusting the coercions.
-/
theorem height_add_ringKrullDim_quotient_mvPolynomial_field (K : Type*) [Field K] (N : ℕ)
    (𝔔 : Ideal (MvPolynomial (Fin N) K)) [𝔔.IsPrime] :
    (𝔔.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial (Fin N) K ⧸ 𝔔) = N := by
  obtain ⟨𝔪0, h𝔪0⟩ := Ideal.exists_maximal (MvPolynomial (Fin N) K ⧸ 𝔔)
  have cancel : ∀ a b : ℕ∞, 𝔔.height + a = N → 𝔔.height + b = N → a = b := by
      intro a b ha hb
      have hq : 𝔔.height ≠ ⊤ := fun h => by rw [h, top_add] at ha; exact ENat.top_ne_coe N ha
      have ha' : a ≠ ⊤ := fun h => by rw [h, add_top] at ha; exact ENat.top_ne_coe N ha
      have hb' : b ≠ ⊤ := fun h => by rw [h, add_top] at hb; exact ENat.top_ne_coe N hb
      obtain ⟨q, hq0⟩ := ENat.ne_top_iff_exists.1 hq
      obtain ⟨a0, ha0⟩ := ENat.ne_top_iff_exists.1 ha'
      obtain ⟨b0, hb0⟩ := ENat.ne_top_iff_exists.1 hb'
      rw [← hq0, ← ha0] at ha
      rw [← hq0, ← hb0] at hb
      rw [← ha0, ← hb0]
      have e1 : q + a0 = N := by exact_mod_cast ha
      have e2 : q + b0 = N := by exact_mod_cast hb
      congr 1
      omega
  have hall : ∀ 𝔪 : Ideal (MvPolynomial (Fin N) K ⧸ 𝔔), 𝔪.IsMaximal → 𝔪.height = 𝔪0.height := by
    intro 𝔪 h𝔪
    exact cancel _ _ (height_add_height_maximal_quotient_field K N 𝔔 𝔪)
      (height_add_height_maximal_quotient_field K N 𝔔 𝔪0)
  have hsup : (⨆ I : Ideal (MvPolynomial (Fin N) K ⧸ 𝔔), ⨆ (_ : I.IsMaximal), I.height) = 𝔪0.height :=
    le_antisymm (iSup₂_le fun I hI => (hall I hI).le) (le_iSup₂_of_le 𝔪0 h𝔪0 le_rfl)
  rw [← Ideal.sup_isMaximal_height_eq_ringKrullDim, hsup]
  have e := height_add_height_maximal_quotient_field K N 𝔔 𝔪0
  exact_mod_cast e

/- English proof (translation)
Take `⟨s, g, hinj, hfin⟩` from `exists_finite_inj_algHom_of_fg K A`. Use `letI : Algebra (MvPolynomial (Fin s) K) A := g.toRingHom.toAlgebra`. Use `haveI : Module.Finite (MvPolynomial (Fin s) K) A := hfin`. Use `haveI : IsScalarTower K (MvPolynomial (Fin s) K) A := IsScalarTower.of_algebraMap_eq (fun x => (g.commutes x).symm)`. Establish `hinj' : Function.Injective (algebraMap (MvPolynomial (Fin s) K) A)` using `hinj`.

Use `haveI : FaithfulSMul (MvPolynomial (Fin s) K) A := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj'`. Use `haveI : FaithfulSMul K (MvPolynomial (Fin s) K) := (faithfulSMul_iff_algebraMap_injective _ _).2 (MvPolynomial.C_injective _ _)`. Use `⟨s, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[ringKrullDim_eq_of_isIntegral_of_injective hinj']`. Establish `h6` using `height_add_ringKrullDim_quotient_mvPolynomial_field K s (⊥ : Ideal (MvPolynomial (Fin s) K))`.

Rewrite `h6` using `[Ideal.height_bot, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _)]`. Simplify using `using h6`. Establish `h` using `trdeg_add_eq K (MvPolynomial (Fin s) K) (A := A)`. Rewrite `h` using `[trdeg_eq_zero (R := MvPolynomial (Fin s) K) (A := A), add_zero, MvPolynomial.trdeg_of_isDomain]`. Rewrite using `[← h]`.

Simplify using the standard rewrite rules.
-/
theorem exists_dim_trdeg_field {K A : Type u} [Field K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] :
    ∃ s : ℕ, ringKrullDim A = s ∧ Algebra.trdeg K A = s := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg K A
  letI : Algebra (MvPolynomial (Fin s) K) A := g.toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin s) K) A := hfin
  haveI : IsScalarTower K (MvPolynomial (Fin s) K) A :=
    IsScalarTower.of_algebraMap_eq (fun x => (g.commutes x).symm)
  have hinj' : Function.Injective (algebraMap (MvPolynomial (Fin s) K) A) := hinj
  haveI : FaithfulSMul (MvPolynomial (Fin s) K) A := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj'
  haveI : FaithfulSMul K (MvPolynomial (Fin s) K) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (MvPolynomial.C_injective _ _)
  refine ⟨s, ?_, ?_⟩
  · rw [ringKrullDim_eq_of_isIntegral_of_injective hinj']
    have h6 := height_add_ringKrullDim_quotient_mvPolynomial_field K s (⊥ : Ideal (MvPolynomial (Fin s) K))
    rw [Ideal.height_bot, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _)] at h6
    simpa using h6
  · have h := trdeg_add_eq K (MvPolynomial (Fin s) K) (A := A)
    rw [trdeg_eq_zero (R := MvPolynomial (Fin s) K) (A := A), add_zero, MvPolynomial.trdeg_of_isDomain] at h
    rw [← h]
    simp

/- English proof (translation)
Take `⟨s, h1, h2⟩` from `exists_dim_trdeg_field (K := K) (A := A)`. Rewrite `h` using `[h2]`. Establish `hs : s = n` using `by exact_mod_cast h`. Rewrite using `[h1, hs]`.
-/
theorem ringKrullDim_eq_of_trdeg_eq_field {K A : Type u} [Field K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] (n : ℕ) (h : Algebra.trdeg K A = n) :
    ringKrullDim A = n := by
  obtain ⟨s, h1, h2⟩ := exists_dim_trdeg_field (K := K) (A := A)
  rw [h2] at h
  have hs : s = n := by exact_mod_cast h
  rw [h1, hs]

/- English proof (translation)
Take `⟨N, f, hf⟩` from `Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance : Algebra.FiniteType K A)`. Set `e : (MvPolynomial (Fin N) K ⧸ RingHom.ker f.toRingHom) ≃+* A` to `RingHom.quotientKerEquivOfSurjective (f := f.toRingHom) hf`. Use `haveI : (RingHom.ker f.toRingHom).IsPrime := RingHom.ker_isPrime _`. Use `haveI : (𝔪.comap e).IsMaximal := Ideal.comap_isMaximal_of_surjective _ e.surjective`. Establish `h5` using `height_add_height_maximal_quotient_field K N (RingHom.ker f.toRingHom) (𝔪.comap e)`.

Rewrite `h5` using `[RingEquiv.height_comap]`. Establish `h6` using `height_add_ringKrullDim_quotient_mvPolynomial_field K N (RingHom.ker f.toRingHom)`. Rewrite `h6` using `[ringKrullDim_eq_of_ringEquiv e, ringKrullDim_eq_of_trdeg_eq_field n h]`. Establish `h6' : (RingHom.ker f.toRingHom).height + n = N` using `by exact_mod_cast h6`. Establish `cancel : ∀ a b : ℕ∞, (RingHom.ker f.toRingHom).height + a = N → (RingHom.ker f.toRingHom).height + b = N → a = b`.

Introduce `a b ha hb`. Establish `hq : (RingHom.ker f.toRingHom).height ≠ ⊤` using `fun h => by rw [h, top_add] at ha; exact ENat.top_ne_coe N ha`. Establish `ha' : a ≠ ⊤` using `fun h => by rw [h, add_top] at ha; exact ENat.top_ne_coe N ha`. Establish `hb' : b ≠ ⊤` using `fun h => by rw [h, add_top] at hb; exact ENat.top_ne_coe N hb`. Take `⟨q, hq0⟩` from `ENat.ne_top_iff_exists.1 hq`.

Take `⟨a0, ha0⟩` from `ENat.ne_top_iff_exists.1 ha'`. Take `⟨b0, hb0⟩` from `ENat.ne_top_iff_exists.1 hb'`. Rewrite `ha` using `[← hq0, ← ha0]`. Rewrite `hb` using `[← hq0, ← hb0]`. Rewrite using `[← ha0, ← hb0]`.

Establish `e1 : q + a0 = N` using `by exact_mod_cast ha`. Establish `e2 : q + b0 = N` using `by exact_mod_cast hb`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Conclude with `cancel _ _ h5 h6'`.
-/
theorem height_eq_of_isMaximal_of_trdeg_eq_field {K A : Type u} [Field K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] (n : ℕ) (h : Algebra.trdeg K A = n) (𝔪 : Ideal A)
    [𝔪.IsMaximal] : 𝔪.height = n := by
  obtain ⟨N, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance : Algebra.FiniteType K A)
  let e : (MvPolynomial (Fin N) K ⧸ RingHom.ker f.toRingHom) ≃+* A :=
    RingHom.quotientKerEquivOfSurjective (f := f.toRingHom) hf
  haveI : (RingHom.ker f.toRingHom).IsPrime := RingHom.ker_isPrime _
  haveI : (𝔪.comap e).IsMaximal := Ideal.comap_isMaximal_of_surjective _ e.surjective
  have h5 := height_add_height_maximal_quotient_field K N (RingHom.ker f.toRingHom) (𝔪.comap e)
  rw [RingEquiv.height_comap] at h5
  have h6 := height_add_ringKrullDim_quotient_mvPolynomial_field K N (RingHom.ker f.toRingHom)
  rw [ringKrullDim_eq_of_ringEquiv e, ringKrullDim_eq_of_trdeg_eq_field n h] at h6
  have h6' : (RingHom.ker f.toRingHom).height + n = N := by exact_mod_cast h6
  have cancel : ∀ a b : ℕ∞, (RingHom.ker f.toRingHom).height + a = N → (RingHom.ker f.toRingHom).height + b = N → a = b := by
      intro a b ha hb
      have hq : (RingHom.ker f.toRingHom).height ≠ ⊤ := fun h => by rw [h, top_add] at ha; exact ENat.top_ne_coe N ha
      have ha' : a ≠ ⊤ := fun h => by rw [h, add_top] at ha; exact ENat.top_ne_coe N ha
      have hb' : b ≠ ⊤ := fun h => by rw [h, add_top] at hb; exact ENat.top_ne_coe N hb
      obtain ⟨q, hq0⟩ := ENat.ne_top_iff_exists.1 hq
      obtain ⟨a0, ha0⟩ := ENat.ne_top_iff_exists.1 ha'
      obtain ⟨b0, hb0⟩ := ENat.ne_top_iff_exists.1 hb'
      rw [← hq0, ← ha0] at ha
      rw [← hq0, ← hb0] at hb
      rw [← ha0, ← hb0]
      have e1 : q + a0 = N := by exact_mod_cast ha
      have e2 : q + b0 = N := by exact_mod_cast hb
      congr 1
      omega
  exact cancel _ _ h5 h6'

end ReciprocityTheory.CA
