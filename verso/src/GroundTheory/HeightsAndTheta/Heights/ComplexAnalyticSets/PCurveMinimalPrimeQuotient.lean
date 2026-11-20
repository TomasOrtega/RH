import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveMinimalPrimeQuotient
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

/- English proof (translation)
Introduce `n I q p hp`. Establish `hpP : p.IsPrime` using `hp.1.1`. Set `ext : Ideal (MvPolynomial (Fin n) ℂ) → Ideal (Localization.AtPrime (RingHom.ker (eval q)))` to `fun K ↦ K.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))`. Set `mk` to `Ideal.Quotient.mk (ext I)`. Establish `hmk : Function.Surjective mk` using `Ideal.Quotient.mk_surjective`.

Establish `hcomp : algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) = mk.comp (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))` using `rfl`. Set `P : Ideal (Localization.AtPrime (RingHom.ker (eval q)))` to `p.comap mk`. Establish `hPP : P.IsPrime` using `Ideal.comap_isPrime mk p`. Establish `hIP : ext I ≤ P` using `fun x hx ↦ by`. Express the relevant statement in the definitionally equal form `mk x ∈ p`.

Rewrite using `[Ideal.Quotient.eq_zero_iff_mem.2 hx]`. Conclude with `p.zero_mem`. Establish `hpmap : P.map mk = p` using `Ideal.map_comap_of_surjective mk hmk p`. Set `J : Ideal (MvPolynomial (Fin n) ℂ)` to `P.comap (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))`. Establish `hJP : J.IsPrime` using `Ideal.comap_isPrime _ P`.

Establish `hJmem : ∀ f, f ∈ J ↔ algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f ∈ p` using `fun f ↦ by`. Rewrite using `[hcomp]`. Both sides reduce to the same expression. Establish `hextJ : ext J = P` using `IsLocalization.map_under (RingHom.ker (eval q)).primeCompl _ P`. Establish `hIJ : I ≤ J` using `fun f hf ↦ hIP (Ideal.mem_map_of_mem _ hf)`.

Establish `hJm : J ≤ RingHom.ker (eval q)`. Introduce `f hf`. Assume the negation of the conclusion as `h`. Conclude with `hpP.ne_top (Ideal.eq_top_of_isUnit_mem _ ((hJmem f).1 hf) (isUnit_algebraMap_curveLocalRing I q f fun h' ↦ h (RingHom.mem_ker.2 h')))`. Establish `hJmin : J ∈ I.minimalPrimes`.

Use `⟨⟨hJP, hIJ⟩, fun J' hJ' hJ'J ↦ ?_⟩` and prove the remaining obligations. Take `⟨hJ'P, hIJ'⟩` from `hJ'`. Establish `hdisj : Disjoint ((RingHom.ker (eval q)).primeCompl : Set (MvPolynomial (Fin n) ℂ)) J'` using `Set.disjoint_left.2 fun x hx hx' ↦ hx (hJm (hJ'J hx'))`. Establish `hP'P : (ext J').IsPrime` using `IsLocalization.isPrime_of_isPrime_disjoint (RingHom.ker (eval q)).primeCompl _ J' hJ'P hdisj`. Establish `hIP' : ext I ≤ ext J'` using `Ideal.map_mono hIJ'`.

Establish `hker : RingHom.ker mk ≤ ext J'`. Rewrite using `[Ideal.mk_ker]`. Conclude with `hIP'`. Establish `hp'P : ((ext J').map mk).IsPrime` using `Ideal.map_isPrime_of_surjective hmk hker`. Establish `hp'le : (ext J').map mk ≤ p`.

Rewrite using `[← hpmap, ← hextJ]`. Conclude with `Ideal.map_mono (Ideal.map_mono hJ'J)`. Establish `hpp' : p ≤ (ext J').map mk` using `hp.2 ⟨hp'P, bot_le⟩ hp'le`. Introduce `f hf`. Establish `h1 : mk (algebraMap _ (Localization.AtPrime (RingHom.ker (eval q))) f) ∈ (ext J').map mk` using `hpp' ((hJmem f).1 hf)`.

Rewrite `h1` using `[← Ideal.mem_comap, Ideal.comap_map_of_surjective mk hmk, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.2 hIP']`. Establish `h2` using `(IsLocalization.under_map_of_isPrime_disjoint (RingHom.ker (eval q)).primeCompl (Localization.AtPrime (RingHom.ker (eval q))) hJ'P hdisj)`. Rewrite using `[← h2]`. Conclude with `h1`. Establish `hle : ext I ≤ ext J` using `Ideal.map_mono hIJ`.

Use `⟨J, hJmin, hJm, (Ideal.Quotient.factor hle : curveLocalRing I q →+* curveLocalRing J q), Ideal.Quotient.factor_surjective hle, ?_, fun f ↦ Ideal.Quotient.factor_mk hle _⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `RingHom.ker (Ideal.Quotient.factor hle) = p`. Rewrite using `[Ideal.Quotient.factor_ker, hextJ]`. Conclude with `hpmap`.
-/
theorem CurveMinimalPrimeQuotient.proof : CurveMinimalPrimeQuotient.Statement := by
  intro n I q p hp
  have hpP : p.IsPrime := hp.1.1

  let ext : Ideal (MvPolynomial (Fin n) ℂ) → Ideal (Localization.AtPrime (RingHom.ker (eval q))) :=
    fun K ↦ K.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))
  let mk := Ideal.Quotient.mk (ext I)
  have hmk : Function.Surjective mk := Ideal.Quotient.mk_surjective
  have hcomp : algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) =
      mk.comp (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))) := rfl

  let P : Ideal (Localization.AtPrime (RingHom.ker (eval q))) := p.comap mk
  have hPP : P.IsPrime := Ideal.comap_isPrime mk p
  have hIP : ext I ≤ P := fun x hx ↦ by
    change mk x ∈ p
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hx]
    exact p.zero_mem
  have hpmap : P.map mk = p := Ideal.map_comap_of_surjective mk hmk p
  let J : Ideal (MvPolynomial (Fin n) ℂ) :=
    P.comap (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))
  have hJP : J.IsPrime := Ideal.comap_isPrime _ P
  have hJmem : ∀ f, f ∈ J ↔ algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f ∈ p := fun f ↦ by
    rw [hcomp]; rfl
  have hextJ : ext J = P := IsLocalization.map_under (RingHom.ker (eval q)).primeCompl _ P
  have hIJ : I ≤ J := fun f hf ↦ hIP (Ideal.mem_map_of_mem _ hf)
  have hJm : J ≤ RingHom.ker (eval q) := by
    intro f hf
    by_contra h
    exact hpP.ne_top (Ideal.eq_top_of_isUnit_mem _ ((hJmem f).1 hf)
      (isUnit_algebraMap_curveLocalRing I q f fun h' ↦ h (RingHom.mem_ker.2 h')))

  have hJmin : J ∈ I.minimalPrimes := by
    refine ⟨⟨hJP, hIJ⟩, fun J' hJ' hJ'J ↦ ?_⟩
    obtain ⟨hJ'P, hIJ'⟩ := hJ'
    have hdisj : Disjoint ((RingHom.ker (eval q)).primeCompl : Set (MvPolynomial (Fin n) ℂ)) J' :=
      Set.disjoint_left.2 fun x hx hx' ↦ hx (hJm (hJ'J hx'))
    have hP'P : (ext J').IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint (RingHom.ker (eval q)).primeCompl _ J' hJ'P hdisj
    have hIP' : ext I ≤ ext J' := Ideal.map_mono hIJ'
    have hker : RingHom.ker mk ≤ ext J' := by
      rw [Ideal.mk_ker]; exact hIP'
    have hp'P : ((ext J').map mk).IsPrime := Ideal.map_isPrime_of_surjective hmk hker
    have hp'le : (ext J').map mk ≤ p := by
      rw [← hpmap, ← hextJ]
      exact Ideal.map_mono (Ideal.map_mono hJ'J)
    have hpp' : p ≤ (ext J').map mk := hp.2 ⟨hp'P, bot_le⟩ hp'le
    intro f hf
    have h1 : mk (algebraMap _ (Localization.AtPrime (RingHom.ker (eval q))) f) ∈ (ext J').map mk :=
      hpp' ((hJmem f).1 hf)
    rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective mk hmk, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      sup_eq_left.2 hIP'] at h1
    have h2 := (IsLocalization.under_map_of_isPrime_disjoint (RingHom.ker (eval q)).primeCompl
      (Localization.AtPrime (RingHom.ker (eval q))) hJ'P hdisj)
    rw [← h2]
    exact h1

  have hle : ext I ≤ ext J := Ideal.map_mono hIJ
  refine ⟨J, hJmin, hJm, (Ideal.Quotient.factor hle : curveLocalRing I q →+* curveLocalRing J q),
    Ideal.Quotient.factor_surjective hle, ?_, fun f ↦ Ideal.Quotient.factor_mk hle _⟩
  change RingHom.ker (Ideal.Quotient.factor hle) = p
  rw [Ideal.Quotient.factor_ker, hextJ]
  exact hpmap

end GroundTheory.Heights₂.Heights
