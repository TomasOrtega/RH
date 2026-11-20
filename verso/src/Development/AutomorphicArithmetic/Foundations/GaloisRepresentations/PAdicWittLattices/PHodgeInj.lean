import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPullbackFromSpecAppPreimage
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
open Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR KaehlerDifferential
universe u v

set_option autoImplicit false

/- English proof (translation)
Establish `h : IsUnit (n : k)` using `isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hn)`. Simplify using `using h.map (algebraMap k A)`.
-/
private theorem natCast_isUnit (k : Type) [Field k] [CharZero k] {A : Type} [CommRing A] [Algebra k A]
    {n : ℕ} (hn : n ≠ 0) : IsUnit (n : A) := by
  have h : IsUnit (n : k) := isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hn)
  simpa using h.map (algebraMap k A)

/- English proof (translation)
Assume the negation of the conclusion as `hnot`. Take `⟨M, hM, hmem⟩` from `exists_max_ideal_of_mem_nonunits hnot`. Take `⟨Q, hQ⟩` from `onto ⟨M, hM.isPrime⟩`. Establish `hcomap : Q.asIdeal.comap (algebraMap A A') = M` using `congrArg PrimeSpectrum.asIdeal hQ`. Set `Am` to `Localization.AtPrime M`.

Set `L` to `LocalizedModule M.primeCompl A'`. Establish `base` using `IsLocalizedModule.isBaseChange M.primeCompl Am (LocalizedModule.mkLinearMap M.primeCompl A')`. Use `haveI : Module.Free Am L := Module.free_of_flat_of_isLocalRing`. Use `haveI : Nontrivial L := by`. Use `⟨⟨LocalizedModule.mkLinearMap M.primeCompl _ 1, 0, fun h ↦ ?_⟩⟩` and prove the remaining obligations.

Take `⟨t, ht⟩` from `(IsLocalizedModule.eq_zero_iff M.primeCompl (LocalizedModule.mkLinearMap M.primeCompl A')).1 h`. Establish `ht0 : algebraMap A A' t = 0`. Rewrite using `[Algebra.algebraMap_eq_smul_one]`. Conclude with `ht`. Establish `hin : (t : A) ∈ Q.asIdeal.comap (algebraMap A A')`.

Rewrite using `[Ideal.mem_comap, ht0]`. Conclude with `Q.asIdeal.zero_mem`. Conclude with `t.2 (hcomap.le hin)`. Establish `hrank : algebraMap A Am (algTrace A A' 1) = (Module.finrank Am L : Am)`. Rewrite using `[algTrace_apply, ← projTrace_of_isBaseChange base (LinearMap.mul _ _ 1) LinearMap.id (fun x ↦ by simp), projTrace_eq_trace, LinearMap.trace_id]`.

Establish `hne : Module.finrank Am L ≠ 0` using `fun h ↦ not_subsingleton L ((Module.finrank_eq_zero_iff_of_free Am L).1 h)`. Establish `hunit : IsUnit (algebraMap A Am (algTrace A A' 1))`. Rewrite using `[hrank, ← map_natCast (algebraMap A Am)]`. Conclude with `(natCast_isUnit k hne).map _`. Conclude with `(IsLocalization.AtPrime.isUnit_to_map_iff Am M _).1 hunit hmem`.
-/
private theorem unit_of_trace_one (k : Type) [Field k] [CharZero k] {A A' : Type} [CommRing A]
    [CommRing A'] [Algebra k A] [Algebra A A'] [Module.Finite A A'] [Module.Projective A A']
    (onto : Function.Surjective (PrimeSpectrum.comap (algebraMap A A'))) :
    IsUnit (algTrace A A' 1) := by
  by_contra hnot
  obtain ⟨M, hM, hmem⟩ := exists_max_ideal_of_mem_nonunits hnot
  obtain ⟨Q, hQ⟩ := onto ⟨M, hM.isPrime⟩
  have hcomap : Q.asIdeal.comap (algebraMap A A') = M := congrArg PrimeSpectrum.asIdeal hQ
  let Am := Localization.AtPrime M
  let L := LocalizedModule M.primeCompl A'
  have base := IsLocalizedModule.isBaseChange M.primeCompl Am
    (LocalizedModule.mkLinearMap M.primeCompl A')
  haveI : Module.Free Am L := Module.free_of_flat_of_isLocalRing
  haveI : Nontrivial L := by
    refine ⟨⟨LocalizedModule.mkLinearMap M.primeCompl _ 1, 0, fun h ↦ ?_⟩⟩
    obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff M.primeCompl
      (LocalizedModule.mkLinearMap M.primeCompl A')).1 h
    have ht0 : algebraMap A A' t = 0 := by
      rw [Algebra.algebraMap_eq_smul_one]; exact ht
    have hin : (t : A) ∈ Q.asIdeal.comap (algebraMap A A') := by
      rw [Ideal.mem_comap, ht0]; exact Q.asIdeal.zero_mem
    exact t.2 (hcomap.le hin)
  have hrank : algebraMap A Am (algTrace A A' 1) = (Module.finrank Am L : Am) := by
    rw [algTrace_apply, ← projTrace_of_isBaseChange base (LinearMap.mul _ _ 1) LinearMap.id
      (fun x ↦ by simp), projTrace_eq_trace, LinearMap.trace_id]
  have hne : Module.finrank Am L ≠ 0 := fun h ↦
    not_subsingleton L ((Module.finrank_eq_zero_iff_of_free Am L).1 h)
  have hunit : IsUnit (algebraMap A Am (algTrace A A' 1)) := by
    rw [hrank, ← map_natCast (algebraMap A Am)]
    exact (natCast_isUnit k hne).map _
  exact (IsLocalization.AtPrime.isUnit_to_map_iff Am M _).1 hunit hmem

section
variable {k : Type} [Field k] [CharZero k] {X X' : Scheme.{0}} {s : X ⟶ Sp k} {s' : X' ⟶ Sp k}
  {f : X' ⟶ X} [IsFinite f] [Etale f]

/- English proof (translation)
Use `letI := secAlg s s' f U`. Use `haveI := sec_finite (s := s) (s' := s') (f := f) hU`. Use `haveI := sec_etale (s := s) (s' := s') (f := f) hU`. Use `haveI := projective_of_etale (Sec s U) (Sec s' (f ⁻¹ᵁ U))`. Establish `hsq : Surjective (Spec.map (f.app U))` using `MorphismProperty.of_isPullback (P := @Surjective) (isPullback_fromSpec_app_preimage f hU (hU.preimage f)) inferInstance`.

Conclude with `unit_of_trace_one k (A := Sec s U) (A' := Sec s' (f ⁻¹ᵁ U)) hsq.surj`.
-/
private theorem unit_secTrace [Surjective f] {U : X.Opens} (hU : IsAffineOpen U) :
    IsUnit (secTrace (f := f) s s' hU 1) := by
  letI := secAlg s s' f U
  haveI := sec_finite (s := s) (s' := s') (f := f) hU
  haveI := sec_etale (s := s) (s' := s') (f := f) hU
  haveI := projective_of_etale (Sec s U) (Sec s' (f ⁻¹ᵁ U))
  have hsq : Surjective (Spec.map (f.app U)) :=
    MorphismProperty.of_isPullback (P := @Surjective)
      (isPullback_fromSpec_app_preimage f hU (hU.preimage f)) inferInstance
  exact unit_of_trace_one k (A := Sec s U) (A' := Sec s' (f ⁻¹ᵁ U)) hsq.surj

omit [CharZero k] in
/- English proof (translation)
Take `⟨x, rfl⟩` from `toOm_surjective (s := s) (j := j) hU w`. Rewrite using `[Scheme.Modules.Hom.comp_app]`. Express the relevant statement in the definitionally equal form `(omegaTrace hf j).app U ((omegaPull hf j).val.app (op U) ((toOmega s j).app (op U) x)) = _`. Rewrite using `[omegaPull_toOmega hf j U x, ← one_smul (Sec s' (f ⁻¹ᵁ U)) (formPull hf U j x)]`. Use `erw [omegaTrace_toOm_smul_formPull hf j hU]`.

Conclude with `(toOm s j U).map_smul _ x`.
-/
private theorem pull_trace_app (hf : f ≫ s = s') (j : ℕ) {U : X.Opens} (hU : IsAffineOpen U)
    (w : Γ(Omega s j, U)) :
    (omegaPull hf j ≫ omegaTrace hf j).app U w = secTrace (f := f) s s' hU 1 • w := by
  obtain ⟨x, rfl⟩ := toOm_surjective (s := s) (j := j) hU w
  rw [Scheme.Modules.Hom.comp_app]
  change (omegaTrace hf j).app U ((omegaPull hf j).val.app (op U) ((toOmega s j).app (op U) x)) = _
  rw [omegaPull_toOmega hf j U x, ← one_smul (Sec s' (f ⁻¹ᵁ U)) (formPull hf U j x)]
  erw [omegaTrace_toOm_smul_formPull hf j hU]
  exact (toOm s j U).map_smul _ x

/- English proof (translation)
Set `t : ∀ U : X.affineOpens, (Sec s U.1)ˣ` to `fun U ↦ (unit_secTrace (s := s) (s' := s') (f := f) U.2).unit`. Establish `ht : ∀ U : X.affineOpens, (t U : Sec s U.1) = secTrace (f` using `f) s s' U.2 1 := fun _ ↦ rfl`. Establish `hinv : ∀ (U V : X.affineOpens) (h : V.1 ≤ U.1), Sec.res s h ((t U)⁻¹ : (Sec s U.1)ˣ) = ((t V)⁻¹ : (Sec s V.1)ˣ)` using `fun U V h ↦ by`. Establish `e : Sec.res s h (t U) = t V`. Rewrite using `[ht, ht, secTrace_res U.2 V.2 h, map_one]`.

Use `Units.eq_inv_of_mul_eq_one_right ?_` and prove the remaining obligations. Rewrite using `[← e, ← map_mul, Units.inv_mul, map_one]`. Set `mulInv : ∀ U : X.affineOpens, Γ(Omega s j, U.1) →ₗ[Γ(X, U.1)] Γ(Omega s j, U.1)` to `fun U ↦ LinearMap.lsmul Γ(X, U.1) Γ(Omega s j, U.1) (show Sec s U.1 from ((t U)⁻¹ : (Sec s U.1)ˣ))`. Establish `hmul : ∀ (U : X.affineOpens) (w : Γ(Omega s j, U.1)), mulInv U w = (((t U)⁻¹ : (Sec s U.1)ˣ) : Sec s U.1) • w` using `fun _ _ ↦ rfl`. Establish `hres : ∀ (U V : X.Opens) (h : V ≤ U) (g : Sec s U) (n : Γ(Omega s j, U)), (Omega s j).presheaf.map (homOfLE h).op (g • n) = Sec.res s h g • (Omega s j).presheaf.map (homOfLE h).op n` using `fun _ _ _ _ _ ↦ Scheme.Modules.map_smul _ _ _ _`.

Use `⟨homOfAffine mulInv fun U V h w ↦ by rw [hmul, hmul, hres, hinv], hom_ext_affine fun U hU w ↦ ?_⟩` and prove the remaining obligations. Use `(homOfAffine_app mulInv _ ⟨U, hU⟩ ((omegaPull hf j ≫ omegaTrace hf j).app U w)).trans ?_` and prove the remaining obligations. Rewrite using `[hmul, pull_trace_app hf j hU, ← ht ⟨U, hU⟩, smul_smul, Units.inv_mul, one_smul]`. Both sides reduce to the same expression.
-/
private theorem pull_trace_leftInv [Surjective f] (hf : f ≫ s = s') (j : ℕ) :
    ∃ ψ : Omega s j ⟶ Omega s j, (omegaPull hf j ≫ omegaTrace hf j) ≫ ψ = 𝟙 _ := by
  let t : ∀ U : X.affineOpens, (Sec s U.1)ˣ := fun U ↦
    (unit_secTrace (s := s) (s' := s') (f := f) U.2).unit
  have ht : ∀ U : X.affineOpens, (t U : Sec s U.1) = secTrace (f := f) s s' U.2 1 := fun _ ↦ rfl
  have hinv : ∀ (U V : X.affineOpens) (h : V.1 ≤ U.1),
      Sec.res s h ((t U)⁻¹ : (Sec s U.1)ˣ) = ((t V)⁻¹ : (Sec s V.1)ˣ) := fun U V h ↦ by
    have e : Sec.res s h (t U) = t V := by
      rw [ht, ht, secTrace_res U.2 V.2 h, map_one]
    refine Units.eq_inv_of_mul_eq_one_right ?_
    rw [← e, ← map_mul, Units.inv_mul, map_one]
  let mulInv : ∀ U : X.affineOpens, Γ(Omega s j, U.1) →ₗ[Γ(X, U.1)] Γ(Omega s j, U.1) := fun U ↦
    LinearMap.lsmul Γ(X, U.1) Γ(Omega s j, U.1) (show Sec s U.1 from ((t U)⁻¹ : (Sec s U.1)ˣ))
  have hmul : ∀ (U : X.affineOpens) (w : Γ(Omega s j, U.1)),
      mulInv U w = (((t U)⁻¹ : (Sec s U.1)ˣ) : Sec s U.1) • w := fun _ _ ↦ rfl
  have hres : ∀ (U V : X.Opens) (h : V ≤ U) (g : Sec s U) (n : Γ(Omega s j, U)),
      (Omega s j).presheaf.map (homOfLE h).op (g • n) =
        Sec.res s h g • (Omega s j).presheaf.map (homOfLE h).op n :=
    fun _ _ _ _ _ ↦ Scheme.Modules.map_smul _ _ _ _
  refine ⟨homOfAffine mulInv fun U V h w ↦ by rw [hmul, hmul, hres, hinv],
    hom_ext_affine fun U hU w ↦ ?_⟩
  refine (homOfAffine_app mulInv _ ⟨U, hU⟩ ((omegaPull hf j ≫ omegaTrace hf j).app U w)).trans ?_
  rw [hmul, pull_trace_app hf j hU, ← ht ⟨U, hU⟩, smul_smul, Units.inv_mul, one_smul]
  rfl
end

/- English proof (translation)
Introduce `k _ _ a b Z W p r c _ _ _ hc x y hxy`. Use `letI := algΓ p`. Take `⟨ψ, hψ⟩` from `pull_trace_leftInv hc a`. Establish `back : ∀ z : hodgeH p a b, cohOn.map k ψ ⊤ b (hodgeTrace hc a b (hodgePull hc a b z)) = z` using `fun z ↦ by`. Use `(congrArg (cohOn.map k ψ ⊤ b) (hodgeTrace_hodgePull hc a b z)).trans ?_` and prove the remaining obligations.

Use `(cohOn.map_map k _ ψ z).trans ?_` and prove the remaining obligations. Rewrite using `[hψ]`. Conclude with `LinearMap.congr_fun (cohOn.map_id k _ ⊤ b) z`. Rewrite using `[← back x, ← back y, hxy]`.
-/
theorem UpperTheory.Gal.G3.pHodgeInj :
    HodgeInj := by
  intro k _ _ a b Z W p r c _ _ _ hc x y hxy
  letI := algΓ p
  obtain ⟨ψ, hψ⟩ := pull_trace_leftInv hc a
  have back : ∀ z : hodgeH p a b,
      cohOn.map k ψ ⊤ b (hodgeTrace hc a b (hodgePull hc a b z)) = z := fun z ↦ by
    refine (congrArg (cohOn.map k ψ ⊤ b) (hodgeTrace_hodgePull hc a b z)).trans ?_
    refine (cohOn.map_map k _ ψ z).trans ?_
    rw [hψ]
    exact LinearMap.congr_fun (cohOn.map_id k _ ⊤ b) z
  rw [← back x, ← back y, hxy]
