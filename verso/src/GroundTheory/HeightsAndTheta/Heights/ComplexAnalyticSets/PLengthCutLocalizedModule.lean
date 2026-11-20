import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLengthCutLocalizedModule
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLengthCutGlobal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLengthLocalizedLocalized
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u v

open IsLocalRing

/- English proof (translation)
Introduce `B _ _ P _ y Q₀ _ M _ _ _ hnil hy hQ htf`. Establish `hPQ : P ≤ Q₀` using `hQ ▸ le_sup_left`. Establish `hdisj : Disjoint (Q₀.primeCompl : Set B) P` using `Set.disjoint_left.mpr fun _ hx hxP => hx (hPQ hxP)`. Establish `hP' : (P.map (algebraMap B (Localization.AtPrime Q₀))).IsPrime` using `LengthLocalizedLocalized.map_isPrime B P Q₀ hPQ`. Establish `: IsNoetherianRing (Localization.AtPrime Q₀)` using `IsLocalization.isNoetherianRing Q₀.primeCompl _ inferInstance`.

Establish `hunder : (P.map (algebraMap B (Localization.AtPrime Q₀))).comap (algebraMap B (Localization.AtPrime Q₀)) = P` using `IsLocalization.under_map_of_isPrime_disjoint Q₀.primeCompl _ ‹P.IsPrime› hdisj`. Establish `hy' : algebraMap B (Localization.AtPrime Q₀) y ∉ P.map (algebraMap B (Localization.AtPrime Q₀))`. Introduce `h`. Apply `hy` to reduce the goal to its premises. Rewrite using `[← hunder]`.

Conclude with `h`. Establish `hsup : P.map (algebraMap B (Localization.AtPrime Q₀)) ⊔ Ideal.span {algebraMap B (Localization.AtPrime Q₀) y} = maximalIdeal (Localization.AtPrime Q₀)`. Establish `hmap : Ideal.map (algebraMap B (Localization.AtPrime Q₀)) Q₀ = Ideal.map (algebraMap B (Localization.AtPrime Q₀)) (P ⊔ Ideal.span {y})` using `congrArg _ hQ`. Rewrite using `[← Localization.AtPrime.map_eq_maximalIdeal, hmap, Ideal.map_sup, Ideal.map_span, Set.image_singleton]`. Establish `hmax : (P.map (algebraMap B (Localization.AtPrime Q₀)) ⊔ Ideal.span {algebraMap B (Localization.AtPrime Q₀) y}).IsMaximal`.

Rewrite using `[hsup]`. Conclude with `maximalIdeal.isMaximal _`. Establish `hnil' : IsNilpotent (P.map (algebraMap B (Localization.AtPrime Q₀)))`. Take `⟨n, hn⟩` from `hnil`. Use `⟨n, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Ideal.map_pow, hn]`. Simplify using the standard rewrite rules. Establish `hpir : IsPrincipalIdealRing (Localization.AtPrime Q₀ ⧸ P.map (algebraMap B (Localization.AtPrime Q₀)))` using `by set I := P.map (algebraMap B (Localization.AtPrime Q₀)) with hI`. Establish `: IsLocalRing (Localization.AtPrime Q₀ ⧸ I)` using `IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective`. Establish `hm : maximalIdeal (Localization.AtPrime Q₀ ⧸ I) = Ideal.span {Ideal.Quotient.mk I (algebraMap B (Localization.AtPrime Q₀) y)}`.

Establish `hc : (maximalIdeal (Localization.AtPrime Q₀ ⧸ I)).comap (Ideal.Quotient.mk I) = maximalIdeal (Localization.AtPrime Q₀)` using `eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)`. Rewrite using `[← Ideal.map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective (maximalIdeal _), hc, ← hsup, Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_span, Set.image_singleton]`. Establish `hprin : (maximalIdeal (Localization.AtPrime Q₀ ⧸ I)).IsPrincipal` using `⟨⟨_, hm⟩⟩`. Conclude with `((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (Localization.AtPrime Q₀ ⧸ I)).out 0 4).mpr hprin`. Establish `htf' : ∀ s ∉ P.map (algebraMap B (Localization.AtPrime Q₀)), ∀ m : LocalizedModule Q₀.primeCompl M, s • m = 0 → m = 0`.

Introduce `s hs m hsm`. Proceed by induction on `s using Localization.induction_on with`. Consider the case `H x`. Take `⟨a, t⟩` from `x`. Simplify using `only at hs hsm`.

Establish `ha : a ∉ P`. Introduce `ha`. Apply `hs` to reduce the goal to its premises. Rewrite using `[Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)`.

Proceed by induction on `m using LocalizedModule.induction_on with`. Consider the case `h m u`. Rewrite `hsm` using `[LocalizedModule.mk_smul_mk, ← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq]`. Take `⟨v, hv⟩` from `hsm`. Simplify using `only [smul_zero, one_smul, Submonoid.smul_def, smul_smul] at hv`.

Establish `hva : (v : B) * a ∉ P` using `fun h => (‹P.IsPrime›.mem_or_mem h).elim (fun h1 => v.2 (hPQ h1)) ha`. Rewrite using `[htf _ hva m hv, LocalizedModule.zero_mk]`. Establish `hloc : (Ideal.span {y} • ⊤ : Submodule B M).localized' (Localization.AtPrime Q₀) Q₀.primeCompl (LocalizedModule.mkLinearMap Q₀.primeCompl M) = (Ideal.span {algebraMap B (Localization.AtPrime Q₀) y} • ⊤ : Submodule (Localization.AtPrime Q₀) (LocalizedModule Q₀.primeCompl M))`. Rewrite using `[Submodule.localized'_smul, Submodule.localized'_top, Ideal.localized'_eq_map, Ideal.map_span, Set.image_singleton]`. Set `e` to `(IsLocalizedModule.linearEquiv Q₀.primeCompl ((Ideal.span {y} • ⊤ : Submodule B M).toLocalizedQuotient' (Localization.AtPrime Q₀) Q₀.primeCompl (LocalizedModule.mkLinearMap Q₀.primeCompl M)) (LocalizedModule.mkLinearMap Q₀.primeCompl (M ⧸ (Ideal.span {y} • ⊤ : Submodule B M)))).e …`.

Rewrite using `[← e.length_eq, (Submodule.quotEquivOfEq _ _ hloc).length_eq, hG (Localization.AtPrime Q₀) (P.map (algebraMap B (Localization.AtPrime Q₀))) (algebraMap B (Localization.AtPrime Q₀) y) (LocalizedModule Q₀.primeCompl M) hnil' hpir hy' hmax htf', hL B P Q₀ M hPQ]`.
-/
theorem LengthCutLocalizedModule.proof (hG : LengthCutGlobal.Statement.{u, max u v})
    (hL : LengthLocalizedLocalized.Statement.{u, v}) : LengthCutLocalizedModule.Statement.{u, v} := by
  intro B _ _ P _ y Q₀ _ M _ _ _ hnil hy hQ htf
  have hPQ : P ≤ Q₀ := hQ ▸ le_sup_left
  have hdisj : Disjoint (Q₀.primeCompl : Set B) P := Set.disjoint_left.mpr fun _ hx hxP => hx (hPQ hxP)
  have hP' : (P.map (algebraMap B (Localization.AtPrime Q₀))).IsPrime :=
    LengthLocalizedLocalized.map_isPrime B P Q₀ hPQ
  have : IsNoetherianRing (Localization.AtPrime Q₀) :=
    IsLocalization.isNoetherianRing Q₀.primeCompl _ inferInstance
  have hunder : (P.map (algebraMap B (Localization.AtPrime Q₀))).comap (algebraMap B (Localization.AtPrime Q₀)) =
      P := IsLocalization.under_map_of_isPrime_disjoint Q₀.primeCompl _ ‹P.IsPrime› hdisj

  have hy' : algebraMap B (Localization.AtPrime Q₀) y ∉ P.map (algebraMap B (Localization.AtPrime Q₀)) := by
    intro h
    apply hy
    rw [← hunder]
    exact h

  have hsup : P.map (algebraMap B (Localization.AtPrime Q₀)) ⊔
      Ideal.span {algebraMap B (Localization.AtPrime Q₀) y} = maximalIdeal (Localization.AtPrime Q₀) := by
    have hmap : Ideal.map (algebraMap B (Localization.AtPrime Q₀)) Q₀ =
        Ideal.map (algebraMap B (Localization.AtPrime Q₀)) (P ⊔ Ideal.span {y}) := congrArg _ hQ
    rw [← Localization.AtPrime.map_eq_maximalIdeal, hmap, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  have hmax : (P.map (algebraMap B (Localization.AtPrime Q₀)) ⊔
      Ideal.span {algebraMap B (Localization.AtPrime Q₀) y}).IsMaximal := by
    rw [hsup]
    exact maximalIdeal.isMaximal _

  have hnil' : IsNilpotent (P.map (algebraMap B (Localization.AtPrime Q₀))) := by
    obtain ⟨n, hn⟩ := hnil
    refine ⟨n, ?_⟩
    rw [← Ideal.map_pow, hn]
    simp

  have hpir : IsPrincipalIdealRing
      (Localization.AtPrime Q₀ ⧸ P.map (algebraMap B (Localization.AtPrime Q₀))) := by
    set I := P.map (algebraMap B (Localization.AtPrime Q₀)) with hI
    have : IsLocalRing (Localization.AtPrime Q₀ ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    have hm : maximalIdeal (Localization.AtPrime Q₀ ⧸ I) =
        Ideal.span {Ideal.Quotient.mk I (algebraMap B (Localization.AtPrime Q₀) y)} := by
      have hc : (maximalIdeal (Localization.AtPrime Q₀ ⧸ I)).comap (Ideal.Quotient.mk I) =
          maximalIdeal (Localization.AtPrime Q₀) :=
        eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
      rw [← Ideal.map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective (maximalIdeal _), hc, ← hsup,
        Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_span, Set.image_singleton]
    have hprin : (maximalIdeal (Localization.AtPrime Q₀ ⧸ I)).IsPrincipal := ⟨⟨_, hm⟩⟩
    exact ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (Localization.AtPrime Q₀ ⧸ I)).out 0 4).mpr hprin

  have htf' : ∀ s ∉ P.map (algebraMap B (Localization.AtPrime Q₀)), ∀ m : LocalizedModule Q₀.primeCompl M,
      s • m = 0 → m = 0 := by
    intro s hs m hsm
    induction s using Localization.induction_on with
    | H x =>
    obtain ⟨a, t⟩ := x
    dsimp only at hs hsm
    have ha : a ∉ P := by
      intro ha
      apply hs
      rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)
    induction m using LocalizedModule.induction_on with
    | h m u =>
      rw [LocalizedModule.mk_smul_mk, ← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at hsm
      obtain ⟨v, hv⟩ := hsm
      simp only [smul_zero, one_smul, Submonoid.smul_def, smul_smul] at hv
      have hva : (v : B) * a ∉ P := fun h =>
        (‹P.IsPrime›.mem_or_mem h).elim (fun h1 => v.2 (hPQ h1)) ha
      rw [htf _ hva m hv, LocalizedModule.zero_mk]

  have hloc : (Ideal.span {y} • ⊤ : Submodule B M).localized' (Localization.AtPrime Q₀) Q₀.primeCompl
      (LocalizedModule.mkLinearMap Q₀.primeCompl M) =
      (Ideal.span {algebraMap B (Localization.AtPrime Q₀) y} • ⊤ :
        Submodule (Localization.AtPrime Q₀) (LocalizedModule Q₀.primeCompl M)) := by
    rw [Submodule.localized'_smul, Submodule.localized'_top, Ideal.localized'_eq_map, Ideal.map_span,
      Set.image_singleton]
  let e := (IsLocalizedModule.linearEquiv Q₀.primeCompl
    ((Ideal.span {y} • ⊤ : Submodule B M).toLocalizedQuotient' (Localization.AtPrime Q₀) Q₀.primeCompl
      (LocalizedModule.mkLinearMap Q₀.primeCompl M))
    (LocalizedModule.mkLinearMap Q₀.primeCompl (M ⧸ (Ideal.span {y} • ⊤ : Submodule B M)))).extendScalarsOfIsLocalization
      Q₀.primeCompl (Localization.AtPrime Q₀)
  rw [← e.length_eq, (Submodule.quotEquivOfEq _ _ hloc).length_eq,
    hG (Localization.AtPrime Q₀) (P.map (algebraMap B (Localization.AtPrime Q₀)))
      (algebraMap B (Localization.AtPrime Q₀) y) (LocalizedModule Q₀.primeCompl M) hnil' hpir hy' hmax htf',
    hL B P Q₀ M hPQ]

end GroundTheory.Heights₂.Heights
