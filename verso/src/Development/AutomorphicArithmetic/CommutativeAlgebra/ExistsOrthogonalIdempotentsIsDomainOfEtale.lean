import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgClosedFractionRingOfMonicPolynomialsHaveRoo
noncomputable section

open TensorProduct Polynomial

/- English proof (translation)
Rewrite using `[isIntegrallyClosed_iff (FractionRing T)]`. Introduce `x hx`. Take `⟨p, hp, hpx⟩` from `hx`. Proceed by induction on `h : p.natDegree using Nat.strong_induction_on generalizing p with`. Consider the case `_ d ih`.

Break down `Nat.eq_zero_or_pos d with h0 | hpos` into its components or cases. Substitute `h0` using the available equality. Establish `h1 : p = 1` using `hp.natDegree_eq_zero.1 h`. Simplify using `[h1] at hpx`. Take `⟨a, ha⟩` from `hT p hp (h ▸ hpos)`.

Take `⟨q, hq⟩` from `dvd_iff_isRoot.2 ha`. Establish `hqm : q.Monic` using `(monic_X_sub_C a).of_mul_monic_left (hq ▸ hp)`. Establish `hdeg : p.natDegree = 1 + q.natDegree`. Rewrite using `[hq, (monic_X_sub_C a).natDegree_mul hqm, natDegree_X_sub_C]`. Rewrite `hpx` using `[hq, eval₂_mul]`.

Break down `mul_eq_zero.1 hpx with h1 | h1` into its components or cases. Use `⟨a, ?_⟩` and prove the remaining obligations. Simplify using `only [eval₂_sub, eval₂_X, eval₂_C] at h1`. Conclude with `(sub_eq_zero.1 h1).symm`. Conclude with `ih q.natDegree (by omega) q hqm h1 rfl`.
-/
private theorem isIntegrallyClosed_of_AIC (T : Type) [CommRing T] [IsDomain T]
    (hT : GlobalTheory.EtC.AIC T) : IsIntegrallyClosed T := by
  rw [isIntegrallyClosed_iff (FractionRing T)]
  intro x hx
  obtain ⟨p, hp, hpx⟩ := hx
  induction h : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ d ih =>
    rcases Nat.eq_zero_or_pos d with h0 | hpos
    · subst h0
      have h1 : p = 1 := hp.natDegree_eq_zero.1 h
      simp [h1] at hpx
    · obtain ⟨a, ha⟩ := hT p hp (h ▸ hpos)
      obtain ⟨q, hq⟩ := dvd_iff_isRoot.2 ha
      have hqm : q.Monic := (monic_X_sub_C a).of_mul_monic_left (hq ▸ hp)
      have hdeg : p.natDegree = 1 + q.natDegree := by
        rw [hq, (monic_X_sub_C a).natDegree_mul hqm, natDegree_X_sub_C]
      rw [hq, eval₂_mul] at hpx
      rcases mul_eq_zero.1 hpx with h1 | h1
      · refine ⟨a, ?_⟩
        simp only [eval₂_sub, eval₂_X, eval₂_C] at h1
        exact (sub_eq_zero.1 h1).symm
      · exact ih q.natDegree (by omega) q hqm h1 rfl

/- English proof (translation)
Establish `hint : IsIntegral C z`. Use `⟨X ^ 2 - X, monic_X_pow_sub (n := 2) (lt_of_le_of_lt degree_X_le (by norm_num)), ?_⟩` and prove the remaining obligations. Simplify using `[eval₂_sub, pow_two, hz]`. Take `⟨t, ht⟩` from `(TensorProduct.toIntegralClosure_bijective_of_smooth (R := T) (S := C) (B := FractionRing T)).2 ⟨z, hint⟩`. Establish `ht' : Algebra.TensorProduct.map (AlgHom.id C C) (integralClosure T (FractionRing T)).val t = z` using `congrArg Subtype.val ht`.

Rewrite using `[← ht']`. Use `clear ht ht'`. Proceed by induction on `t with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x y hx hy`.

Take `⟨a, ha⟩` from `hx`. Take `⟨b, hb⟩` from `hy`. Conclude with `⟨a + b, by rw [map_add, map_add, ha, hb]⟩`. Consider the case `tmul x y`. Take `⟨r, hr⟩` from `IsIntegrallyClosed.algebraMap_eq_of_integral (R := T) y.2`.

Use `⟨r • x, ?_⟩` and prove the remaining obligations. Simplify using `only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.coe_val, ← hr, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]`. Rewrite using `[Algebra.algebraMap_eq_smul_one, smul_tmul]`.
-/
private theorem exists_of_idem (T C : Type) [CommRing T] [IsDomain T] [IsIntegrallyClosed T]
    [CommRing C] [Algebra T C] [Algebra.Etale T C] (z : C ⊗[T] FractionRing T) (hz : z * z = z) :
    ∃ s : C, algebraMap C (C ⊗[T] FractionRing T) s = z := by
  have hint : IsIntegral C z := by
    refine ⟨X ^ 2 - X, monic_X_pow_sub (n := 2) (lt_of_le_of_lt degree_X_le (by norm_num)), ?_⟩
    simp [eval₂_sub, pow_two, hz]
  obtain ⟨t, ht⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth (R := T) (S := C)
    (B := FractionRing T)).2 ⟨z, hint⟩
  have ht' : Algebra.TensorProduct.map (AlgHom.id C C)
      (integralClosure T (FractionRing T)).val t = z := congrArg Subtype.val ht
  rw [← ht']
  clear ht ht'
  induction t with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩
  | tmul x y =>
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (R := T) y.2
    refine ⟨r • x, ?_⟩
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.coe_val, ← hr,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [Algebra.algebraMap_eq_smul_one, smul_tmul]

/- English proof (translation)
Set `G : C →+* (Fin n → FractionRing T)` to `g.toRingHom.comp (algebraMap C (C ⊗[T] FractionRing T))`. Establish `hι : Function.Injective (algebraMap C (C ⊗[T] FractionRing T))` using `Algebra.TensorProduct.includeLeft_injective (S := T) (IsFractionRing.injective T (FractionRing T))`. Establish `hG : Function.Injective G` using `g.injective.comp hι`. Establish `hex : ∀ j : Fin n, ∃ s : C, G s = Pi.single j 1`. Introduce `j`.

Take `⟨s, hs⟩` from `exists_of_idem T C (g.symm (Pi.single j 1)) (by`. Apply `g.injective` to reduce the goal to its premises. Rewrite using `[map_mul, g.apply_symm_apply, ← Pi.single_mul, one_mul])`. Conclude with `⟨s, by simp [G, hs]⟩`. Use `choose c hc using hex`.

Establish `hcoi : CompleteOrthogonalIdempotents c`. Use `⟨⟨fun i => hG ?_, fun i j hij => hG ?_⟩, hG ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hc, ← Pi.single_mul, one_mul]`. Rewrite using `[map_mul, hc, hc, map_zero]`. Use extensionality with `k`.

Distinguish the cases in `h : k = i`. Substitute `h` using the available equality. Simplify using `[Pi.single_eq_of_ne hij]`. Simplify using `[Pi.single_eq_of_ne h]`. Rewrite using `[map_sum, map_one]`.

Simplify using `only [hc]`. Conclude with `Finset.univ_sum_single 1`. Use `⟨c, hcoi, fun j => ?_⟩` and prove the remaining obligations. Establish `hidem : IsIdempotentElem (c j)` using `hcoi.idem j`. Set `φ : C →+* FractionRing T` to `(Pi.evalRingHom _ j).comp G`.

Establish `hφ : φ (c j) = 1` using `by simp [φ, hc]`. Establish `hu : IsUnit (φ (c j))` using `by rw [hφ]; exact isUnit_one`. Set `ψ : Localization.Away (c j) →+* FractionRing T` to `IsLocalization.Away.lift (c j) hu`. Establish `hψ : ∀ x, ψ (algebraMap C _ x) = φ x` using `fun x => IsLocalization.Away.lift_eq (c j) hu x`. Establish `hsurj : Function.Surjective (algebraMap C (Localization.Away (c j)))` using `IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem (c j) hidem`.

Establish `hone : algebraMap C (Localization.Away (c j)) (c j) = 1` using `(IsIdempotentElem.iff_eq_one_of_isUnit (IsLocalization.Away.algebraMap_isUnit (c j))).1 (hidem.map _)`. Establish `hinj : Function.Injective ψ`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Take `⟨x, rfl⟩` from `hsurj a`.

Rewrite `ha` using `[hψ]`. Establish `hx : x * c j = 0`. Apply `hG` to reduce the goal to its premises. Rewrite using `[map_mul, hc, map_zero]`. Use extensionality with `k`.

Distinguish the cases in `h : k = j`. Substitute `h` using the available equality. Simplify `ha` using `[φ]`. Simplify using `[Pi.single_eq_of_ne h]`. Use `congrArg (algebraMap C (Localization.Away (c j))) hx` as an intermediate fact.

Rewrite `this` using `[map_mul, hone, mul_one, map_zero]`. Then use the resulting hypothesis. Conclude with `hinj.isDomain ψ`.
-/
private theorem core (T C : Type) [CommRing T] [IsDomain T] [IsIntegrallyClosed T]
    [CommRing C] [Algebra T C] [Algebra.Etale T C] {n : ℕ}
    (g : C ⊗[T] FractionRing T ≃+* (Fin n → FractionRing T)) :
    ∃ (e : Fin n → C), CompleteOrthogonalIdempotents e ∧
      ∀ j, IsDomain (Localization.Away (e j)) := by
  classical
  let G : C →+* (Fin n → FractionRing T) :=
    g.toRingHom.comp (algebraMap C (C ⊗[T] FractionRing T))
  have hι : Function.Injective (algebraMap C (C ⊗[T] FractionRing T)) :=
    Algebra.TensorProduct.includeLeft_injective (S := T)
      (IsFractionRing.injective T (FractionRing T))
  have hG : Function.Injective G := g.injective.comp hι
  have hex : ∀ j : Fin n, ∃ s : C, G s = Pi.single j 1 := by
    intro j
    obtain ⟨s, hs⟩ := exists_of_idem T C (g.symm (Pi.single j 1)) (by
      apply g.injective
      rw [map_mul, g.apply_symm_apply, ← Pi.single_mul, one_mul])
    exact ⟨s, by simp [G, hs]⟩
  choose c hc using hex
  have hcoi : CompleteOrthogonalIdempotents c := by
    refine ⟨⟨fun i => hG ?_, fun i j hij => hG ?_⟩, hG ?_⟩
    · rw [map_mul, hc, ← Pi.single_mul, one_mul]
    · rw [map_mul, hc, hc, map_zero]
      ext k
      by_cases h : k = i
      · subst h; simp [Pi.single_eq_of_ne hij]
      · simp [Pi.single_eq_of_ne h]
    · rw [map_sum, map_one]
      simp only [hc]
      exact Finset.univ_sum_single 1
  refine ⟨c, hcoi, fun j => ?_⟩
  have hidem : IsIdempotentElem (c j) := hcoi.idem j
  let φ : C →+* FractionRing T := (Pi.evalRingHom _ j).comp G
  have hφ : φ (c j) = 1 := by simp [φ, hc]
  have hu : IsUnit (φ (c j)) := by rw [hφ]; exact isUnit_one
  let ψ : Localization.Away (c j) →+* FractionRing T := IsLocalization.Away.lift (c j) hu
  have hψ : ∀ x, ψ (algebraMap C _ x) = φ x := fun x => IsLocalization.Away.lift_eq (c j) hu x
  have hsurj : Function.Surjective (algebraMap C (Localization.Away (c j))) :=
    IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem (c j) hidem
  have hone : algebraMap C (Localization.Away (c j)) (c j) = 1 :=
    (IsIdempotentElem.iff_eq_one_of_isUnit (IsLocalization.Away.algebraMap_isUnit (c j))).1
      (hidem.map _)
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨x, rfl⟩ := hsurj a
    rw [hψ] at ha
    have hx : x * c j = 0 := by
      apply hG
      rw [map_mul, hc, map_zero]
      ext k
      by_cases h : k = j
      · subst h
        simpa [φ] using ha
      · simp [Pi.single_eq_of_ne h]
    have := congrArg (algebraMap C (Localization.Away (c j))) hx
    rwa [map_mul, hone, mul_one, map_zero] at this
  exact hinj.isDomain ψ

/- English proof (translation)
Introduce `T C _ _ _ _ _ hT`. Use `haveI := GlobalTheory.isAlgClosed_fractionRing_of_AIC T hT`. Use `haveI := isIntegrallyClosed_of_AIC T hT`. Set `e0` to `Algebra.FormallyEtale.equivPiOfIsSepClosed (FractionRing T) (FractionRing T ⊗[T] C)`. Use `haveI := Algebra.FormallyUnramified.finite_of_free (FractionRing T) (FractionRing T ⊗[T] C)`.

Use `haveI : IsArtinianRing (FractionRing T ⊗[T] C) := isArtinian_of_tower (FractionRing T) inferInstance`. Take `⟨n, ⟨eq⟩⟩` from `Finite.exists_equiv_fin (PrimeSpectrum (FractionRing T ⊗[T] C))`. Set `g : C ⊗[T] FractionRing T ≃+* (Fin n → FractionRing T)` to `((Algebra.TensorProduct.comm T C (FractionRing T)).toRingEquiv.trans e0.toRingEquiv).trans (RingEquiv.piCongrLeft (fun _ : Fin n => FractionRing T) eq)`. Take `⟨e, h1, h2⟩` from `core T C g`. Conclude with `⟨n, e, h1, h2⟩`.
-/
theorem UpperTheory.exists_orthogonalIdempotents_isDomain_of_etale :
    ∀ (T C : Type) [CommRing T] [IsDomain T] [CommRing C] [Algebra T C] [Algebra.Etale T C], GlobalTheory.EtC.AIC T →
      ∃ (n : ℕ) (e : Fin n → C), CompleteOrthogonalIdempotents e ∧ ∀ j, IsDomain (Localization.Away (e j)) := by
  intro T C _ _ _ _ _ hT
  haveI := GlobalTheory.isAlgClosed_fractionRing_of_AIC T hT
  haveI := isIntegrallyClosed_of_AIC T hT
  let e0 := Algebra.FormallyEtale.equivPiOfIsSepClosed (FractionRing T) (FractionRing T ⊗[T] C)
  haveI := Algebra.FormallyUnramified.finite_of_free (FractionRing T) (FractionRing T ⊗[T] C)
  haveI : IsArtinianRing (FractionRing T ⊗[T] C) := isArtinian_of_tower (FractionRing T) inferInstance
  obtain ⟨n, ⟨eq⟩⟩ := Finite.exists_equiv_fin (PrimeSpectrum (FractionRing T ⊗[T] C))
  let g : C ⊗[T] FractionRing T ≃+* (Fin n → FractionRing T) :=
    ((Algebra.TensorProduct.comm T C (FractionRing T)).toRingEquiv.trans e0.toRingEquiv).trans
      (RingEquiv.piCongrLeft (fun _ : Fin n => FractionRing T) eq)
  obtain ⟨e, h1, h2⟩ := core T C g
  exact ⟨n, e, h1, h2⟩

end
