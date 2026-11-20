import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsSectionOrder
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

noncomputable section

namespace LengthFiniteAlgebra

variable {O B : Type} [CommRing O] [IsLocalRing O] [CommRing B] [Algebra O B]

/- English proof (translation)
The claim follows from `IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P)`.
-/
theorem comap_eq_maximalIdeal [Module.Finite O B] (P : Ideal B) [P.IsMaximal] :
    P.comap (algebraMap O B) = maximalIdeal O :=
  IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P)

/- English proof (translation)
Establish `hfin` using `Algebra.QuasiFinite.finite_primesOver (R := O) (S := B) (maximalIdeal O)`. Use `hfin.to_subtype` as an intermediate fact. Use `Finite.of_injective (β := (maximalIdeal O).primesOver B) (fun P => ⟨P.asIdeal, P.isMaximal.isPrime, ⟨(comap_eq_maximalIdeal P.asIdeal).symm⟩⟩) ?_` and prove the remaining obligations. Introduce `P Q h`. Conclude with `MaximalSpectrum.ext (congrArg Subtype.val h)`.
-/
theorem finite_maximalSpectrum [Module.Finite O B] : Finite (MaximalSpectrum B) := by
  have hfin := Algebra.QuasiFinite.finite_primesOver (R := O) (S := B) (maximalIdeal O)
  have := hfin.to_subtype
  refine Finite.of_injective (β := (maximalIdeal O).primesOver B)
    (fun P => ⟨P.asIdeal, P.isMaximal.isPrime, ⟨(comap_eq_maximalIdeal P.asIdeal).symm⟩⟩) ?_
  intro P Q h
  exact MaximalSpectrum.ext (congrArg Subtype.val h)

/- English proof (translation)
Use `finite_maximalSpectrum (O := O) (B := B)` as an intermediate fact. Set `` to `Fintype.ofFinite (MaximalSpectrum B)`. Rewrite using `[finsum_eq_sum_of_fintype, ← Module.length_pi_of_fintype]`. Set `φ : B →ₗ[O] (∀ P : MaximalSpectrum B, Localization.AtPrime P.asIdeal)` to `LinearMap.pi fun P => (IsScalarTower.toAlgHom O B (Localization.AtPrime P.asIdeal)).toLinearMap`. Establish `hφ : Function.Injective φ`.

Introduce `x y h`. Apply `MaximalSpectrum.toPiLocalization_injective B` to reduce the goal to its premises. Use function extensionality and compare the values at `P`. Conclude with `congrFun h P`. Distinguish the cases in `h : Module.length O B = ⊤`.

Rewrite using `[h]`. Conclude with `(top_le_iff.mp (h ▸ Module.length_le_of_injective φ hφ)).symm`. Establish `hfl : IsFiniteLength O B` using `Module.length_ne_top_iff.mp h`. Rewrite `hfl` using `[isFiniteLength_iff_isNoetherian_isArtinian]`. Establish `: IsArtinianRing B` using `isArtinian_of_tower O hfl.2`.

Establish `hsurj : Function.Surjective φ`. Introduce `z`. Take `⟨x, hx⟩` from `PrimeSpectrum.maximalSpectrumToPiLocalization_surjective_of_discreteTopology B z`. Conclude with `⟨x, hx⟩`. Conclude with `(LinearEquiv.ofBijective φ ⟨hφ, hsurj⟩).length_eq`.
-/
theorem length_eq_finsum_localization [IsNoetherianRing O] [Module.Finite O B] :
    Module.length O B =
      ∑ᶠ P : MaximalSpectrum B, Module.length O (Localization.AtPrime P.asIdeal) := by
  have := finite_maximalSpectrum (O := O) (B := B)
  let := Fintype.ofFinite (MaximalSpectrum B)
  rw [finsum_eq_sum_of_fintype, ← Module.length_pi_of_fintype]
  let φ : B →ₗ[O] (∀ P : MaximalSpectrum B, Localization.AtPrime P.asIdeal) :=
    LinearMap.pi fun P => (IsScalarTower.toAlgHom O B (Localization.AtPrime P.asIdeal)).toLinearMap
  have hφ : Function.Injective φ := by
    intro x y h
    apply MaximalSpectrum.toPiLocalization_injective B
    funext P
    exact congrFun h P
  by_cases h : Module.length O B = ⊤
  · rw [h]
    exact (top_le_iff.mp (h ▸ Module.length_le_of_injective φ hφ)).symm
  · have hfl : IsFiniteLength O B := Module.length_ne_top_iff.mp h
    rw [isFiniteLength_iff_isNoetherian_isArtinian] at hfl
    have : IsArtinianRing B := isArtinian_of_tower O hfl.2
    have hsurj : Function.Surjective φ := by
      intro z
      obtain ⟨x, hx⟩ := PrimeSpectrum.maximalSpectrumToPiLocalization_surjective_of_discreteTopology B z
      exact ⟨x, hx⟩
    exact (LinearEquiv.ofBijective φ ⟨hφ, hsurj⟩).length_eq

/- English proof (translation)
Use `⟨fun a ha => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hna`. Establish `h1 : a ∈ P.comap (algebraMap O B)`. Rewrite using `[comap_eq_maximalIdeal P]`. Conclude with `hna`.

Establish `h2 : algebraMap B (Localization.AtPrime P) (algebraMap O B a) ∈ maximalIdeal (Localization.AtPrime P)` using `(IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P _).mpr h1`. Rewrite `h2` using `[← IsScalarTower.algebraMap_apply]`. Conclude with `h2 ha`.
-/
theorem isLocalHom_localization [Module.Finite O B] (P : Ideal B) [P.IsMaximal] :
    IsLocalHom (algebraMap O (Localization.AtPrime P)) := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have h1 : a ∈ P.comap (algebraMap O B) := by
    rw [comap_eq_maximalIdeal P]; exact hna
  have h2 : algebraMap B (Localization.AtPrime P) (algebraMap O B a) ∈
      maximalIdeal (Localization.AtPrime P) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P _).mpr h1
  rw [← IsScalarTower.algebraMap_apply] at h2
  exact h2 ha

omit [IsLocalRing O] in

/- English proof (translation)
Set `e : (B ⧸ P) ≃+* ResidueField (Localization.AtPrime P)` to `IsLocalization.AtPrime.equivQuotMaximalIdeal P (Localization.AtPrime P)`. Set `e' : (B ⧸ P) ≃ₐ[B] ResidueField (Localization.AtPrime P)` to `AlgEquiv.ofRingEquiv (f := e) fun x => rfl`. Conclude with `(e'.toLinearEquiv.restrictScalars O).length_eq.symm`.
-/
theorem length_residueField (P : Ideal B) [P.IsMaximal] :
    Module.length O (ResidueField (Localization.AtPrime P)) = Module.length O (B ⧸ P) := by
  let e : (B ⧸ P) ≃+* ResidueField (Localization.AtPrime P) :=
    IsLocalization.AtPrime.equivQuotMaximalIdeal P (Localization.AtPrime P)
  let e' : (B ⧸ P) ≃ₐ[B] ResidueField (Localization.AtPrime P) :=
    AlgEquiv.ofRingEquiv (f := e) fun x => rfl
  exact (e'.toLinearEquiv.restrictScalars O).length_eq.symm

/- English proof (translation)
Use `isLocalHom_localization (O := O) P` as an intermediate fact. Establish `h1` using `IsLocalRing.length_restrictScalars O (Localization.AtPrime P) (Localization.AtPrime P ⧸ Ideal.span {algebraMap B (Localization.AtPrime P) θ})`. Establish `h2` using `IsLocalRing.length_restrictScalars O (Localization.AtPrime P) (ResidueField (Localization.AtPrime P))`. Establish `h3 : Module.length (Localization.AtPrime P) (ResidueField (Localization.AtPrime P)) = 1`. Rewrite using `[Module.length_eq_of_surjective (S := Localization.AtPrime P) (R := ResidueField (Localization.AtPrime P)) residue_surjective]`.

Conclude with `Module.length_eq_one _ _`. Rewrite `h2` using `[length_residueField, h3, one_mul]`. Rewrite using `[h2, h1]`. Both sides reduce to the same expression.
-/
theorem ord_mul_length [Module.Finite O B] (P : Ideal B) [P.IsMaximal] (θ : B) :
    Ring.ord (Localization.AtPrime P) (algebraMap B _ θ) * Module.length O (B ⧸ P) =
      Module.length O (Localization.AtPrime P ⧸
        Ideal.span {algebraMap B (Localization.AtPrime P) θ}) := by
  have := isLocalHom_localization (O := O) P
  have h1 := IsLocalRing.length_restrictScalars O (Localization.AtPrime P)
    (Localization.AtPrime P ⧸ Ideal.span {algebraMap B (Localization.AtPrime P) θ})
  have h2 := IsLocalRing.length_restrictScalars O (Localization.AtPrime P)
    (ResidueField (Localization.AtPrime P))
  have h3 : Module.length (Localization.AtPrime P) (ResidueField (Localization.AtPrime P)) = 1 := by
    rw [Module.length_eq_of_surjective (S := Localization.AtPrime P)
      (R := ResidueField (Localization.AtPrime P)) residue_surjective]
    exact Module.length_eq_one _ _
  rw [length_residueField, h3, one_mul] at h2
  rw [h2, h1]
  rfl

omit [IsLocalRing O] in

/- English proof (translation)
Establish `hsub : Algebra.algebraMapSubmonoid (B ⧸ I) (Q.comap (Ideal.Quotient.mk I)).primeCompl = Q.primeCompl`. Use extensionality with `y`. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, hxy⟩`.

Rewrite using `[← hxy]`. Conclude with `hx`. Introduce `hy`. Conclude with `⟨y, hy, rfl⟩`. Establish `: IsLocalization Q.primeCompl (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)) ⧸ I.map (algebraMap B (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)))))`.

Rewrite using `[← hsub]`. Use `infer_instance`. Set `e` to `IsLocalization.algEquiv Q.primeCompl (Localization.AtPrime Q) (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)) ⧸ I.map (algebraMap B (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)))))`. Establish `: IsScalarTower O (B ⧸ I) (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)) ⧸ I.map (algebraMap B (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)))))` using `IsScalarTower.of_algebraMap_eq fun c => by`. Rewrite using `[IsScalarTower.algebraMap_apply O B (B ⧸ I), IsScalarTower.algebraMap_apply O (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I))), IsScalarTower.algebraMap_apply O B (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)))]`.

Both sides reduce to the same expression. Conclude with `(e.toLinearEquiv.restrictScalars O).length_eq`.
-/
theorem length_localization_quotient (I : Ideal B) (Q : Ideal (B ⧸ I)) [Q.IsMaximal] :
    Module.length O (Localization.AtPrime Q) =
      Module.length O (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)) ⧸
        I.map (algebraMap B (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I))))) := by
  have hsub : Algebra.algebraMapSubmonoid (B ⧸ I) (Q.comap (Ideal.Quotient.mk I)).primeCompl =
      Q.primeCompl := by
    ext y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    constructor
    · rintro ⟨x, hx, hxy⟩
      rw [← hxy]
      exact hx
    · intro hy
      exact ⟨y, hy, rfl⟩
  have : IsLocalization Q.primeCompl
      (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)) ⧸
        I.map (algebraMap B (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I))))) := by
    rw [← hsub]; infer_instance
  let e := IsLocalization.algEquiv Q.primeCompl (Localization.AtPrime Q)
    (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)) ⧸
        I.map (algebraMap B (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)))))
  have : IsScalarTower O (B ⧸ I)
      (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)) ⧸
        I.map (algebraMap B (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I))))) :=
    IsScalarTower.of_algebraMap_eq fun c => by
      rw [IsScalarTower.algebraMap_apply O B (B ⧸ I),
        IsScalarTower.algebraMap_apply O (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I))),
        IsScalarTower.algebraMap_apply O B (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)))]
      rfl
  exact (e.toLinearEquiv.restrictScalars O).length_eq

/- English proof (translation)
Use `finite_maximalSpectrum (O := O) (B := B)` as an intermediate fact. Establish `: Module.Finite O (B ⧸ Ideal.span {θ})` using `Module.Finite.of_surjective (Ideal.Quotient.mkₐ O _).toLinearMap Ideal.Quotient.mk_surjective`. Use `finite_maximalSpectrum (O := O) (B := B ⧸ Ideal.span {θ})` as an intermediate fact. Set `` to `Fintype.ofFinite (MaximalSpectrum B)`. Set `` to `Fintype.ofFinite (MaximalSpectrum (B ⧸ Ideal.span {θ}))`.

Rewrite using `[finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]`. Set `ι : MaximalSpectrum (B ⧸ Ideal.span {θ}) → MaximalSpectrum B` to `fun Q => ⟨Q.asIdeal.comap (Ideal.Quotient.mk _), by`. Use `Q.isMaximal` as an intermediate fact. Conclude with `Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective⟩`. Use `Fintype.sum_of_injective ι ?_ _ _ ?_ ?_` and prove the remaining obligations.

Introduce `Q₁ Q₂ h`. Conclude with `MaximalSpectrum.ext (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective (congrArg MaximalSpectrum.asIdeal h))`. Introduce `P hP`. Establish `hθ : θ ∉ P.asIdeal`. Introduce `hθ`.

Apply `hP` to reduce the goal to its premises. Establish `hle : Ideal.span {θ} ≤ P.asIdeal` using `(Ideal.span_singleton_le_iff_mem _).mpr hθ`. Use `P.isMaximal` as an intermediate fact. Establish `hmax` using `Ideal.IsMaximal.map_of_surjective_of_ker_le (m := P.asIdeal) (f := Ideal.Quotient.mk (Ideal.span {θ})) Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])`. Conclude with `⟨⟨_, hmax⟩, MaximalSpectrum.ext (Ideal.comap_map_mk hle)⟩`.

Establish `hu : IsUnit (algebraMap B (Localization.AtPrime P.asIdeal) θ)` using `IsLocalization.map_units (Localization.AtPrime P.asIdeal) (⟨θ, hθ⟩ : P.asIdeal.primeCompl)`. Rewrite using `[Ideal.span_singleton_eq_top.mpr hu]`. Conclude with `Module.length_eq_zero`. Introduce `Q`. Use `Q.isMaximal` as an intermediate fact.

Rewrite using `[length_localization_quotient (Ideal.span {θ}) Q.asIdeal, Ideal.map_span, Set.image_singleton]`.
-/
theorem finsum_reindex [Module.Finite O B] (θ : B) :
    ∑ᶠ Q : MaximalSpectrum (B ⧸ Ideal.span {θ}), Module.length O (Localization.AtPrime Q.asIdeal) =
      ∑ᶠ P : MaximalSpectrum B, Module.length O (Localization.AtPrime P.asIdeal ⧸
        Ideal.span {algebraMap B (Localization.AtPrime P.asIdeal) θ}) := by
  have := finite_maximalSpectrum (O := O) (B := B)
  have : Module.Finite O (B ⧸ Ideal.span {θ}) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ O _).toLinearMap Ideal.Quotient.mk_surjective
  have := finite_maximalSpectrum (O := O) (B := B ⧸ Ideal.span {θ})
  let := Fintype.ofFinite (MaximalSpectrum B)
  let := Fintype.ofFinite (MaximalSpectrum (B ⧸ Ideal.span {θ}))
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  let ι : MaximalSpectrum (B ⧸ Ideal.span {θ}) → MaximalSpectrum B := fun Q =>
    ⟨Q.asIdeal.comap (Ideal.Quotient.mk _), by
      have := Q.isMaximal; exact Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective⟩
  refine Fintype.sum_of_injective ι ?_ _ _ ?_ ?_
  · intro Q₁ Q₂ h
    exact MaximalSpectrum.ext (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
      (congrArg MaximalSpectrum.asIdeal h))
  · intro P hP
    have hθ : θ ∉ P.asIdeal := by
      intro hθ
      apply hP
      have hle : Ideal.span {θ} ≤ P.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr hθ
      have := P.isMaximal
      have hmax := Ideal.IsMaximal.map_of_surjective_of_ker_le (m := P.asIdeal)
        (f := Ideal.Quotient.mk (Ideal.span {θ})) Ideal.Quotient.mk_surjective
        (by rwa [Ideal.mk_ker])
      exact ⟨⟨_, hmax⟩, MaximalSpectrum.ext (Ideal.comap_map_mk hle)⟩
    have hu : IsUnit (algebraMap B (Localization.AtPrime P.asIdeal) θ) :=
      IsLocalization.map_units (Localization.AtPrime P.asIdeal) (⟨θ, hθ⟩ : P.asIdeal.primeCompl)
    rw [Ideal.span_singleton_eq_top.mpr hu]
    exact Module.length_eq_zero
  · intro Q
    have := Q.isMaximal
    rw [length_localization_quotient (Ideal.span {θ}) Q.asIdeal, Ideal.map_span, Set.image_singleton]

end LengthFiniteAlgebra

open LengthFiniteAlgebra in

/- English proof (translation)
Introduce `O B _ _ _ _ _ _ θ`. Establish `hr : LinearMap.range (LinearMap.mulLeft O θ) = (Ideal.span {θ}).restrictScalars O`. Use extensionality with `x`. Simplify using `[Ideal.mem_span_singleton', mul_comm]`. Establish `: Module.Finite O (B ⧸ Ideal.span {θ})` using `Module.Finite.of_surjective (Ideal.Quotient.mkₐ O _).toLinearMap Ideal.Quotient.mk_surjective`.

Rewrite using `[(Submodule.quotEquivOfEq _ _ hr ≪≫ₗ Submodule.Quotient.restrictScalarsEquiv O (Ideal.span {θ})).length_eq, length_eq_finsum_localization, finsum_reindex]`. Use `congr 1`. Use function extensionality and compare the values at `P`. Conclude with `(ord_mul_length P.asIdeal θ).symm`.
-/
theorem LengthFiniteAlgebra.proof : LengthFiniteAlgebra.Statement := by
  intro O B _ _ _ _ _ _ θ
  have hr : LinearMap.range (LinearMap.mulLeft O θ) = (Ideal.span {θ}).restrictScalars O := by
    ext x
    simp [Ideal.mem_span_singleton', mul_comm]
  have : Module.Finite O (B ⧸ Ideal.span {θ}) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ O _).toLinearMap Ideal.Quotient.mk_surjective
  rw [(Submodule.quotEquivOfEq _ _ hr ≪≫ₗ
      Submodule.Quotient.restrictScalarsEquiv O (Ideal.span {θ})).length_eq,
    length_eq_finsum_localization, finsum_reindex]
  congr 1
  funext P
  exact (ord_mul_length P.asIdeal θ).symm

end

end GroundTheory.Heights₂.Heights
