import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightMaximalLePrimeAddDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedComplementDimBound
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.DedekindDimFormula
open ReciprocityTheory.CA

/- English proof (translation)
Establish `hi` using `MvPolynomial.quotient_mk_comp_C_isIntegral_of_isJacobsonRing 𝔑`. Use `letI := Ideal.Quotient.field 𝔑`. Use `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ hi (⊥ : Ideal (MvPolynomial (Fin N) o ⧸ 𝔑))` as an intermediate fact. Rewrite `this` using `[← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]`. Then use the resulting hypothesis.
-/
theorem isMaximal_comap_C {o : Type} [CommRing o] [IsJacobsonRing o] (N : ℕ)
    (𝔑 : Ideal (MvPolynomial (Fin N) o)) [𝔑.IsMaximal] :
    (𝔑.comap (MvPolynomial.C : o →+* MvPolynomial (Fin N) o)).IsMaximal := by
  have hi := MvPolynomial.quotient_mk_comp_C_isIntegral_of_isJacobsonRing 𝔑
  letI := Ideal.Quotient.field 𝔑
  have := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ hi
    (⊥ : Ideal (MvPolynomial (Fin N) o ⧸ 𝔑))
  rwa [← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at this

/- English proof (translation)
Distinguish the cases in `hf : IsField o`. Use `⟨0, fun p _ => ?_⟩` and prove the remaining obligations. Use `letI := hf.toField`. Establish `hp : p = ⊥` using `(Ideal.eq_bot_or_top p).resolve_right (Ideal.IsMaximal.ne_top inferInstance)`. Establish `hd : ringKrullDim (Localization.AtPrime p) = 0`.

Rewrite using `[IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p), hp, Ideal.height_bot]`. Both sides reduce to the same expression. Use `⟨⟨inferInstance, 0, by rw [hd]; rfl, ?_⟩, hd⟩` and prove the remaining obligations. Use `⟨[], rfl, by simp, ?_⟩` and prove the remaining obligations. Rewrite using `[IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal (by simp)]`.

Conclude with `RingTheory.Sequence.IsWeaklyRegular.nil _ _`. Use `⟨1, fun p _ => ?_⟩` and prove the remaining obligations. Establish `hp : p ≠ ⊥`. Introduce `h`. Conclude with `hf (Ring.isField_iff_maximal_bot.mpr (h ▸ inferInstance))`.

Use `haveI : IsDiscreteValuationRing (Localization.AtPrime p) := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain o hp _`. Establish `hd` using `IsDiscreteValuationRing.ringKrullDim_eq_one (Localization.AtPrime p)`. Use `⟨⟨inferInstance, 1, by rw [hd]; rfl, ?_⟩, by rw [hd]; rfl⟩` and prove the remaining obligations. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime p)`. Establish `hm : ϖ ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p)` using `hϖ.not_isUnit`.

Use `⟨[ϖ], rfl, by simpa using hm, ?_⟩` and prove the remaining obligations. Rewrite using `[IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal (by simpa using hm), RingTheory.Sequence.isWeaklyRegular_singleton_iff]`. Conclude with `IsSMulRegular.of_ne_zero hϖ.ne_zero`.
-/
theorem isCM_localization (o : Type) [CommRing o] [IsDomain o] [IsDedekindDomain o] :
    ∃ δ : ℕ, ∀ (p : Ideal o) [p.IsMaximal],
      IsCM (Localization.AtPrime p) ∧ ringKrullDim (Localization.AtPrime p) = δ := by
  by_cases hf : IsField o
  · refine ⟨0, fun p _ => ?_⟩
    letI := hf.toField
    have hp : p = ⊥ := (Ideal.eq_bot_or_top p).resolve_right (Ideal.IsMaximal.ne_top inferInstance)
    have hd : ringKrullDim (Localization.AtPrime p) = 0 := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p), hp,
        Ideal.height_bot]
      rfl
    refine ⟨⟨inferInstance, 0, by rw [hd]; rfl, ?_⟩, hd⟩
    refine ⟨[], rfl, by simp, ?_⟩
    rw [IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal (by simp)]
    exact RingTheory.Sequence.IsWeaklyRegular.nil _ _
  · refine ⟨1, fun p _ => ?_⟩
    have hp : p ≠ ⊥ := by
      intro h
      exact hf (Ring.isField_iff_maximal_bot.mpr (h ▸ inferInstance))
    haveI : IsDiscreteValuationRing (Localization.AtPrime p) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain o hp _
    have hd := IsDiscreteValuationRing.ringKrullDim_eq_one (Localization.AtPrime p)
    refine ⟨⟨inferInstance, 1, by rw [hd]; rfl, ?_⟩, by rw [hd]; rfl⟩
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime p)
    have hm : ϖ ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p) := hϖ.not_isUnit
    refine ⟨[ϖ], rfl, by simpa using hm, ?_⟩
    rw [IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal (by simpa using hm),
      RingTheory.Sequence.isWeaklyRegular_singleton_iff]
    exact IsSMulRegular.of_ne_zero hϖ.ne_zero

/- English proof (translation)
Use `letI : Algebra (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)) := MvPolynomial.algebraMvPolynomial`. Set `W : Submonoid (MvPolynomial (Fin N) o)` to `p.primeCompl.map (MvPolynomial.C (σ := Fin N))`. Use `haveI hL : IsLocalization W (MvPolynomial (Fin N) (Localization.AtPrime p)) := MvPolynomial.isLocalization p.primeCompl (Localization.AtPrime p)`. Establish `hdisj : Disjoint (W : Set (MvPolynomial (Fin N) o)) (𝔑 : Set _)`. Rewrite using `[Set.disjoint_left]`.

Introduce and unpack `x ⟨m, hm, rfl⟩ hx`. Conclude with `hm (hc ▸ (show m ∈ 𝔑.comap MvPolynomial.C from hx))`. Set `𝔑'` to `𝔑.map (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)))`. Use `haveI hP : 𝔑'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint W _ 𝔑 inferInstance hdisj`. Establish `hcm : 𝔑'.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p))) = 𝔑` using `IsLocalization.under_map_of_isPrime_disjoint W _ inferInstance hdisj`.

Use `haveI hM : 𝔑'.IsMaximal := by`. Use `⟨⟨hP.ne_top, fun J hJ => ?_⟩⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hJt`. Establish `h1 : 𝔑 ≤ J.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)))` using `hcm ▸ Ideal.comap_mono hJ.le`. Establish `h2 : J.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p))) ≠ ⊤`.

Introduce `h`. Apply `hJt` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one]`. Establish `: (1 : MvPolynomial (Fin N) o) ∈ J.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)))` using `h ▸ Submodule.mem_top`. Simplify using `using this`.

Establish `h3` using `(‹𝔑.IsMaximal›.eq_of_le h2 h1)`. Establish `h4 : J = 𝔑'`. Establish `h5` using `IsLocalization.map_comap W (MvPolynomial (Fin N) (Localization.AtPrime p)) J`. Express the relevant statement in the definitionally equal form `Ideal.map _ (J.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)))) = J at h5`. Rewrite `h5` using `[← h3]`.

Conclude with `h5.symm`. Conclude with `hJ.ne' h4`. Use `⟨𝔑', hM, ?_, ?_, IsLocalization.height_map_of_disjoint W 𝔑 hdisj⟩` and prove the remaining obligations. Use `haveI : (𝔑'.comap (MvPolynomial.C : Localization.AtPrime p →+* _)).IsPrime := Ideal.comap_isPrime _ _`. Use `le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) ?_` and prove the remaining obligations.

Rewrite using `[← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]`. Introduce `x hx`. Rewrite using `[Ideal.mem_comap, Ideal.mem_comap]`. Establish `e : (MvPolynomial.C (algebraMap o (Localization.AtPrime p) x) : MvPolynomial (Fin N) (Localization.AtPrime p)) = algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)) (MvPolynomial.C x)`. Rewrite using `[MvPolynomial.algebraMap_def, MvPolynomial.map_C]`.

Rewrite using `[e]`. Conclude with `Ideal.mem_map_of_mem _ (by rw [← hc] at hx; exact hx)`. Use `haveI h0 : IsLocalization.AtPrime (Localization.AtPrime 𝔑') (𝔑'.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)))) := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization W _ 𝔑' haveI : IsLocalization 𝔑.primeCompl (Localiza …`. Establish `hsub : (𝔑'.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)))).primeCompl = 𝔑.primeCompl` using `Submonoid.ext fun x => by simp only [Ideal.mem_primeCompl_iff, hcm]`. Establish `h0' : IsLocalization (𝔑'.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)))).primeCompl (Localization.AtPrime 𝔑')` using `h0`.

Rewrite `h0'` using `[hsub]`. Conclude with `h0'`. Conclude with `⟨(IsLocalization.algEquiv 𝔑.primeCompl (Localization.AtPrime 𝔑') (Localization.AtPrime 𝔑)).toRingEquiv⟩`.
-/
theorem exists_maximal_mvPolynomial_localization' {o : Type} [CommRing o] (N : ℕ) (p : Ideal o) [p.IsMaximal] (𝔑 : Ideal (MvPolynomial (Fin N) o)) [𝔑.IsMaximal]
    (hc : 𝔑.comap (MvPolynomial.C : o →+* MvPolynomial (Fin N) o) = p) :
    ∃ (𝔑' : Ideal (MvPolynomial (Fin N) (Localization.AtPrime p))) (_ : 𝔑'.IsMaximal),
      𝔑'.comap (MvPolynomial.C : Localization.AtPrime p →+* _) =
        IsLocalRing.maximalIdeal (Localization.AtPrime p) ∧
      Nonempty (Localization.AtPrime 𝔑' ≃+* Localization.AtPrime 𝔑) ∧ 𝔑'.height = 𝔑.height := by
  classical
  letI : Algebra (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)) :=
    MvPolynomial.algebraMvPolynomial
  let W : Submonoid (MvPolynomial (Fin N) o) := p.primeCompl.map (MvPolynomial.C (σ := Fin N))
  haveI hL : IsLocalization W (MvPolynomial (Fin N) (Localization.AtPrime p)) :=
    MvPolynomial.isLocalization p.primeCompl (Localization.AtPrime p)
  have hdisj : Disjoint (W : Set (MvPolynomial (Fin N) o)) (𝔑 : Set _) := by
    rw [Set.disjoint_left]
    rintro x ⟨m, hm, rfl⟩ hx
    exact hm (hc ▸ (show m ∈ 𝔑.comap MvPolynomial.C from hx))
  let 𝔑' := 𝔑.map (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)))
  haveI hP : 𝔑'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint W _ 𝔑 inferInstance hdisj
  have hcm : 𝔑'.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p))) = 𝔑 :=
    IsLocalization.under_map_of_isPrime_disjoint W _ inferInstance hdisj
  haveI hM : 𝔑'.IsMaximal := by
    refine ⟨⟨hP.ne_top, fun J hJ => ?_⟩⟩
    by_contra hJt
    have h1 : 𝔑 ≤ J.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p))) :=
      hcm ▸ Ideal.comap_mono hJ.le
    have h2 : J.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p))) ≠ ⊤ := by
      intro h
      apply hJt
      rw [Ideal.eq_top_iff_one]
      have : (1 : MvPolynomial (Fin N) o) ∈ J.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p))) := h ▸ Submodule.mem_top
      simpa using this
    have h3 := (‹𝔑.IsMaximal›.eq_of_le h2 h1)
    have h4 : J = 𝔑' := by
      have h5 := IsLocalization.map_comap W (MvPolynomial (Fin N) (Localization.AtPrime p)) J
      change Ideal.map _ (J.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)))) = J at h5
      rw [← h3] at h5
      exact h5.symm
    exact hJ.ne' h4
  refine ⟨𝔑', hM, ?_, ?_, IsLocalization.height_map_of_disjoint W 𝔑 hdisj⟩
  · haveI : (𝔑'.comap (MvPolynomial.C : Localization.AtPrime p →+* _)).IsPrime := Ideal.comap_isPrime _ _
    refine le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) ?_
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_comap]
    have e : (MvPolynomial.C (algebraMap o (Localization.AtPrime p) x) : MvPolynomial (Fin N) (Localization.AtPrime p)) =
        algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)) (MvPolynomial.C x) := by
      rw [MvPolynomial.algebraMap_def, MvPolynomial.map_C]
    rw [e]
    exact Ideal.mem_map_of_mem _ (by rw [← hc] at hx; exact hx)
  · haveI h0 : IsLocalization.AtPrime (Localization.AtPrime 𝔑')
        (𝔑'.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)))) :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization W _ 𝔑'
    haveI : IsLocalization 𝔑.primeCompl (Localization.AtPrime 𝔑') := by
      have hsub : (𝔑'.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)))).primeCompl = 𝔑.primeCompl :=
        Submonoid.ext fun x => by simp only [Ideal.mem_primeCompl_iff, hcm]
      have h0' : IsLocalization (𝔑'.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)))).primeCompl (Localization.AtPrime 𝔑') := h0
      rw [hsub] at h0'
      exact h0'
    exact ⟨(IsLocalization.algEquiv 𝔑.primeCompl (Localization.AtPrime 𝔑') (Localization.AtPrime 𝔑)).toRingEquiv⟩

/- English proof (translation)
Introduce `o _ _ _ _ N`. Take `⟨δ, hδ⟩` from `isCM_localization o`. Use `⟨δ + N, fun 𝔑 _ => ?_⟩` and prove the remaining obligations. Use `haveI := isMaximal_comap_C N 𝔑`. Take `⟨hCM, hdim⟩` from `hδ (𝔑.comap (MvPolynomial.C : o →+* MvPolynomial (Fin N) o))`.

Take `⟨𝔑', h𝔑', hc, ⟨e⟩, hh⟩` from `exists_maximal_mvPolynomial_localization' N _ 𝔑 rfl`. Establish `h` using `isCM_localization_mvPolynomial hCM N 𝔑' hc`. Use `⟨h.1.of_ringEquiv e, ?_⟩` and prove the remaining obligations. Establish `h2` using `h.2`. Rewrite `h2` using `[hdim, hh]`.

Establish `h3 : ((𝔑.height : ℕ∞) : WithBot ℕ∞) = (((δ + N : ℕ) : ℕ∞) : WithBot ℕ∞)`. Rewrite using `[h2]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Conclude with `WithBot.coe_injective h3`.
-/
theorem polyEquidim : ∀ (o : Type) [CommRing o] [IsDomain o] [IsDedekindDomain o] [IsJacobsonRing o] (N : ℕ),
    ∃ d : ℕ, ∀ (𝔑 : Ideal (MvPolynomial (Fin N) o)) [𝔑.IsMaximal],
      IsCM (Localization.AtPrime 𝔑) ∧ 𝔑.height = (d : ℕ∞) := by
  intro o _ _ _ _ N
  obtain ⟨δ, hδ⟩ := isCM_localization o
  refine ⟨δ + N, fun 𝔑 _ => ?_⟩
  haveI := isMaximal_comap_C N 𝔑
  obtain ⟨hCM, hdim⟩ := hδ (𝔑.comap (MvPolynomial.C : o →+* MvPolynomial (Fin N) o))
  obtain ⟨𝔑', h𝔑', hc, ⟨e⟩, hh⟩ := exists_maximal_mvPolynomial_localization' N _ 𝔑 rfl
  have h := isCM_localization_mvPolynomial hCM N 𝔑' hc
  refine ⟨h.1.of_ringEquiv e, ?_⟩
  have h2 := h.2
  rw [hdim, hh] at h2
  have h3 : ((𝔑.height : ℕ∞) : WithBot ℕ∞) = (((δ + N : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    rw [h2]; push_cast; ring
  exact WithBot.coe_injective h3

end GlobalTheory.DedekindDimFormula

namespace GlobalTheory.DedekindDimFormula

/- English proof (translation)
Take `⟨N, f, hf⟩` from `Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType o A›`. Take `⟨d, hd⟩` from `polyEquidim o N`. Use `set Q := RingHom.ker (f : MvPolynomial (Fin N) o →+* A) with hQdef`. Use `haveI : Q.IsPrime := RingHom.ker_isPrime _`. Set `e : (MvPolynomial (Fin N) o ⧸ Q) ≃+* A` to `RingHom.quotientKerEquivOfSurjective (f := (f : MvPolynomial (Fin N) o →+* A)) hf`.

Take `⟨M₀, hM₀⟩` from `Ideal.exists_maximal (MvPolynomial (Fin N) o ⧸ Q)`. Use `haveI : (M₀.comap (Ideal.Quotient.mk Q)).IsMaximal := Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective`. Establish `hQle : Q.height ≤ d`. Rewrite using `[← (hd (M₀.comap (Ideal.Quotient.mk Q))).2]`. Conclude with `Ideal.height_mono fun x hx => by`.

Simplify using `[Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx, M₀.zero_mem]`. Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k : ℕ, Q.height = k := by`. Establish `: Q.height ≠ ⊤` using `ne_top_of_le_ne_top (ENat.coe_ne_top d) hQle`. Conclude with `⟨Q.height.toNat, (ENat.coe_toNat this).symm⟩`. Establish `hkd : k ≤ d` using `by rw [hk] at hQle; exact_mod_cast hQle`.

Use `⟨d - k, fun M _ => ?_, fun P M _ _ => ?_⟩` and prove the remaining obligations. Use `haveI : (M.comap e).IsMaximal := Ideal.comap_isMaximal_of_surjective _ e.surjective haveI : ((M.comap e).comap (Ideal.Quotient.mk Q)).IsMaximal := Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective`. Take `⟨hCM, hh⟩` from `hd ((M.comap e).comap (Ideal.Quotient.mk Q))`. Establish `e1` using `GlobalTheory.FinTypeIntCatenary.height_comap_mk Q (M.comap e) hCM`. Rewrite `e1` using `[hh, hk, RingEquiv.height_comap]`.

Establish `: ((d - k : ℕ) : ℕ∞) + k = M.height + k`. Rewrite using `[← Nat.cast_add, Nat.sub_add_cancel hkd, e1, add_comm]`. Conclude with `(WithTop.add_right_cancel (ENat.coe_ne_top k) this).symm`. Use `haveI : (P.comap e).IsPrime := Ideal.comap_isPrime _ _ haveI : (M.comap e).IsMaximal := Ideal.comap_isMaximal_of_surjective _ e.surjective`. Establish `h` using `GlobalTheory.FinTypeIntCatenary.height_le_of_equidim d (fun 𝔑 _ => hd 𝔑) Q (P.comap e) (M.comap e)`.

Rewrite `h` using `[RingEquiv.height_comap, RingEquiv.height_comap]`. Establish `hdim : ringKrullDim ((MvPolynomial (Fin N) o ⧸ Q) ⧸ P.comap e) = ringKrullDim (A ⧸ P)` using `ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ e (Ideal.map_comap_of_surjective _ e.surjective P).symm)`. Rewrite `h` using `[hdim]`. Then use the resulting hypothesis.
-/
theorem affine_heights (o A : Type) [CommRing o] [IsDomain o] [IsDedekindDomain o] [IsJacobsonRing o]
    [CommRing A] [IsDomain A] [Algebra o A] [Algebra.FiniteType o A] :
    ∃ h : ℕ, (∀ (M : Ideal A) [M.IsMaximal], M.height = (h : ℕ∞)) ∧
      ∀ (P M : Ideal A) [P.IsPrime] [M.IsMaximal],
        (M.height : WithBot ℕ∞) ≤ (P.height : WithBot ℕ∞) + ringKrullDim (A ⧸ P) := by
  obtain ⟨N, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType o A›
  obtain ⟨d, hd⟩ := polyEquidim o N
  set Q := RingHom.ker (f : MvPolynomial (Fin N) o →+* A) with hQdef
  haveI : Q.IsPrime := RingHom.ker_isPrime _
  let e : (MvPolynomial (Fin N) o ⧸ Q) ≃+* A :=
    RingHom.quotientKerEquivOfSurjective (f := (f : MvPolynomial (Fin N) o →+* A)) hf
  obtain ⟨M₀, hM₀⟩ := Ideal.exists_maximal (MvPolynomial (Fin N) o ⧸ Q)
  haveI : (M₀.comap (Ideal.Quotient.mk Q)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  have hQle : Q.height ≤ d := by
    rw [← (hd (M₀.comap (Ideal.Quotient.mk Q))).2]
    exact Ideal.height_mono fun x hx => by
      simp [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx, M₀.zero_mem]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Q.height = k := by
    have : Q.height ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top d) hQle
    exact ⟨Q.height.toNat, (ENat.coe_toNat this).symm⟩
  have hkd : k ≤ d := by rw [hk] at hQle; exact_mod_cast hQle
  refine ⟨d - k, fun M _ => ?_, fun P M _ _ => ?_⟩
  · haveI : (M.comap e).IsMaximal := Ideal.comap_isMaximal_of_surjective _ e.surjective
    haveI : ((M.comap e).comap (Ideal.Quotient.mk Q)).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    obtain ⟨hCM, hh⟩ := hd ((M.comap e).comap (Ideal.Quotient.mk Q))
    have e1 := GlobalTheory.FinTypeIntCatenary.height_comap_mk Q (M.comap e) hCM
    rw [hh, hk, RingEquiv.height_comap] at e1
    have : ((d - k : ℕ) : ℕ∞) + k = M.height + k := by
      rw [← Nat.cast_add, Nat.sub_add_cancel hkd, e1, add_comm]
    exact (WithTop.add_right_cancel (ENat.coe_ne_top k) this).symm
  · haveI : (P.comap e).IsPrime := Ideal.comap_isPrime _ _
    haveI : (M.comap e).IsMaximal := Ideal.comap_isMaximal_of_surjective _ e.surjective
    have h := GlobalTheory.FinTypeIntCatenary.height_le_of_equidim d (fun 𝔑 _ => hd 𝔑) Q (P.comap e) (M.comap e)
    rw [RingEquiv.height_comap, RingEquiv.height_comap] at h
    have hdim : ringKrullDim ((MvPolynomial (Fin N) o ⧸ Q) ⧸ P.comap e) = ringKrullDim (A ⧸ P) :=
      ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ e
        (Ideal.map_comap_of_surjective _ e.surjective P).symm)
    rwa [hdim] at h

end GlobalTheory.DedekindDimFormula

namespace GlobalTheory.DedekindDimFormula

end GlobalTheory.DedekindDimFormula
