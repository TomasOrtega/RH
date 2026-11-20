import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersUnramifiedOffLevelPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderEqOrSmulUnderEq
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SecondStepGluing
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GoodPrimes

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Use `((Formalism.DivisionValues.conjPl P).isMaximal.eq_of_le P'.isPrime.ne_top ?_).symm` and prove the remaining obligations. Use `Ideal.map_le_iff_le_comap.2 fun c hc => ?_` and prove the remaining obligations.

Take `⟨c', h1, h2⟩` from `h c hc`. Establish `: Formalism.DivisionValues.cO _ c = c'` using `RingOfIntegers.ext h2.symm`. Use `show Formalism.DivisionValues.cO _ c ∈ P'.asIdeal`. Rewrite using `[this]` and apply the resulting hypothesis. Introduce and unpack `rfl`.

Conclude with `fun c hc => ⟨Formalism.DivisionValues.cO _ c, Ideal.mem_map_of_mem _ hc, rfl⟩`.
-/
theorem isConjPl_iff {D : D7} {P P' : Pl D.host.E} : Formalism.IndefR.Lev.IsConjPl P P' ↔ P' = Formalism.DivisionValues.conjPl P := by
  constructor
  · intro h
    apply HeightOneSpectrum.ext
    refine ((Formalism.DivisionValues.conjPl P).isMaximal.eq_of_le P'.isPrime.ne_top ?_).symm
    refine Ideal.map_le_iff_le_comap.2 fun c hc => ?_
    obtain ⟨c', h1, h2⟩ := h c hc
    have : Formalism.DivisionValues.cO _ c = c' := RingOfIntegers.ext h2.symm
    show Formalism.DivisionValues.cO _ c ∈ P'.asIdeal
    rwa [this]
  · rintro rfl
    exact fun c hc => ⟨Formalism.DivisionValues.cO _ c, Ideal.mem_map_of_mem _ hc, rfl⟩

/- English proof (translation)
Establish `hsub : (Q.asIdeal : Set (𝓞 D.host.E)) ⊆ P.asIdeal ∪ (Formalism.DivisionValues.conjPl P).asIdeal`. Introduce `x hx`. Establish `hfix : star ((x : D.host.E) * star (x : D.host.E)) = (x : D.host.E) * star (x : D.host.E)`. Rewrite using `[star_mul', star_star, mul_comm]`. Take `⟨y, hy⟩` from `(D.sp.cm.fixed ((x : D.host.E) * star (x : D.host.E))).1 hfix`.

Establish `hint : IsIntegral ℤ y`. Rewrite using `[← isIntegral_algebraMap_iff (algebraMap D.host.F D.host.E).injective]`. Establish `e : algebraMap D.host.F D.host.E y = ((x * Formalism.DivisionValues.cO _ x : 𝓞 D.host.E) : D.host.E)` using `hy`. Rewrite using `[e]`. Conclude with `(x * Formalism.DivisionValues.cO _ x).isIntegral_coe`.

Establish `hn : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ⟨y, hint⟩ = x * Formalism.DivisionValues.cO _ x` using `RingOfIntegers.ext hy`. Establish `h1 : (⟨y, hint⟩ : 𝓞 D.host.F) ∈ (Q.under (𝓞 D.host.F)).asIdeal` using `by show algebraMap _ (𝓞 D.host.E) _ ∈ Q.asIdeal`. Rewrite using `[hn]`. Conclude with `Ideal.mul_mem_right _ _ hx`. Rewrite `h1` using `[h]`.

Establish `h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ⟨y, hint⟩ ∈ P.asIdeal` using `h1`. Rewrite `h2` using `[hn]`. Use `(P.isPrime.mem_or_mem h2).imp id fun h3 => ?_` and prove the remaining obligations. Establish `h4 : Formalism.DivisionValues.cO _ (Formalism.DivisionValues.cO _ x) ∈ (Formalism.DivisionValues.conjPl P).asIdeal` using `Ideal.mem_map_of_mem _ h3`. Establish `e : Formalism.DivisionValues.cO _ (Formalism.DivisionValues.cO _ x) = x` using `RingOfIntegers.ext (star_star (x : D.host.E))`.

Rewrite `h4` using `[e]`. Conclude with `h4`. Conclude with `(Ideal.subset_union.1 hsub).imp (fun h => HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h)) (fun h => HeightOneSpectrum.ext (Q.isMaximal.eq_of_le (Formalism.DivisionValues.conjPl P).isPrime.ne_top h))`.
-/
theorem eq_or_conj_of_under_eq {D : D7} {P Q : Pl D.host.E} (h : Q.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)) :
    Q = P ∨ Q = Formalism.DivisionValues.conjPl P := by
  have hsub : (Q.asIdeal : Set (𝓞 D.host.E)) ⊆ P.asIdeal ∪ (Formalism.DivisionValues.conjPl P).asIdeal := by
    intro x hx
    have hfix : star ((x : D.host.E) * star (x : D.host.E)) = (x : D.host.E) * star (x : D.host.E) := by
      rw [star_mul', star_star, mul_comm]
    obtain ⟨y, hy⟩ := (D.sp.cm.fixed ((x : D.host.E) * star (x : D.host.E))).1 hfix
    have hint : IsIntegral ℤ y := by
      rw [← isIntegral_algebraMap_iff (algebraMap D.host.F D.host.E).injective]
      have e : algebraMap D.host.F D.host.E y = ((x * Formalism.DivisionValues.cO _ x : 𝓞 D.host.E) : D.host.E) := hy
      rw [e]
      exact (x * Formalism.DivisionValues.cO _ x).isIntegral_coe
    have hn : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ⟨y, hint⟩ = x * Formalism.DivisionValues.cO _ x := RingOfIntegers.ext hy
    have h1 : (⟨y, hint⟩ : 𝓞 D.host.F) ∈ (Q.under (𝓞 D.host.F)).asIdeal := by
      show algebraMap _ (𝓞 D.host.E) _ ∈ Q.asIdeal
      rw [hn]
      exact Ideal.mul_mem_right _ _ hx
    rw [h] at h1
    have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ⟨y, hint⟩ ∈ P.asIdeal := h1
    rw [hn] at h2
    refine (P.isPrime.mem_or_mem h2).imp id fun h3 => ?_
    have h4 : Formalism.DivisionValues.cO _ (Formalism.DivisionValues.cO _ x) ∈ (Formalism.DivisionValues.conjPl P).asIdeal := Ideal.mem_map_of_mem _ h3
    have e : Formalism.DivisionValues.cO _ (Formalism.DivisionValues.cO _ x) = x := RingOfIntegers.ext (star_star (x : D.host.E))
    rw [e] at h4
    exact h4
  exact (Ideal.subset_union.1 hsub).imp
    (fun h => HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h))
    (fun h => HeightOneSpectrum.ext (Q.isMaximal.eq_of_le (Formalism.DivisionValues.conjPl P).isPrime.ne_top h))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h hP`. Take `⟨x, hx, hy⟩` from `h _ hP`. Conclude with `hy (algebraMap _ _ x) rfl hx`. Introduce `h v hv`.

Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Apply `h` to reduce the goal to its premises. Establish `: v = P.under (𝓞 D.host.F)`. Use `HeightOneSpectrum.ext (v.isMaximal.eq_of_le (P.under (𝓞 D.host.F)).isPrime.ne_top fun x hx => ?_)` and prove the remaining obligations.

Take `⟨y, h1, h2⟩` from `hc x hx`. Establish `e : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x = y` using `RingOfIntegers.ext h1.symm`. Use `show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ P.asIdeal`. Rewrite using `[e]` and apply the resulting hypothesis. Rewrite using `[← this]` and apply the resulting hypothesis.
-/
theorem offS_iff {D : D7} (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (P : Pl D.host.E) :
    OffS D S P ↔ P.under (𝓞 D.host.F) ∉ S := by
  constructor
  · intro h hP
    obtain ⟨x, hx, hy⟩ := h _ hP
    exact hy (algebraMap _ _ x) rfl hx
  · intro h v hv
    by_contra hc
    push Not at hc
    apply h
    have : v = P.under (𝓞 D.host.F) := by
      refine HeightOneSpectrum.ext (v.isMaximal.eq_of_le (P.under (𝓞 D.host.F)).isPrime.ne_top fun x hx => ?_)
      obtain ⟨y, h1, h2⟩ := hc x hx
      have e : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x = y := RingOfIntegers.ext h1.symm
      show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ P.asIdeal
      rwa [e]
    rwa [← this]

/- English proof (translation)
Introduce `D G _ _ Pl0 T A Ks _ _ _ R F hL`. Establish `hQ : R.Q A.μ0 = ∅`. Use `Finset.eq_empty_of_forall_notMem fun PP h => ?_` and prove the remaining obligations. Use `(hL.Q_ram A.μ0 PP).2 (Or.inl h) ?_` and prove the remaining obligations. Rewrite using `[hL.xi_base]`.

Conclude with `fun x _ => rfl`. Establish `hcc` using `fun w : Pl D.host.E => Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl w`. Use `⟨hQ, fun t P hP => ⟨fun hg => ?_, fun PP h => ?_, fun PP h => ?_⟩, fun SF hSF P => ?_, fun hF t P hP => ?_⟩` and prove the remaining obligations. Establish `hk : ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal`. Rewrite `hg` using `[Nat.cast_mul]`.

Break down `P.isPrime.mem_or_mem hg with h | h` into its components or cases. Use `exacts [⟨0, h⟩, ⟨1, h⟩]`. Take `⟨k, hk⟩` from `hk`. Break down `GlobalTheory.ConjOverQuad.div_or_conj_div D R.C.P k P hk with h | ⟨w', h, hw⟩` into its components or cases. Conclude with `(hP P (Or.inl ((hL.Pg P).2 ⟨k, h⟩))).1 rfl`.

Use `(hP w' (Or.inl ((hL.Pg w').2 ⟨k, h⟩))).2 (isConjPl_iff.2 ?_)` and prove the remaining obligations. Rewrite `hw` using `[Formalism.DivisionValues.GluingInclusion.conjIdeal_eq]`. Rewrite using `[HeightOneSpectrum.ext hw, hcc]`. Take `⟨h1, h2⟩` from `hP PP h`. Rewrite `h2`, the goal using `[isConjPl_iff]`.

Use `⟨fun e => h2 (by rw [e, hcc]), fun e => h1 ?_⟩` and prove the remaining obligations. Rewrite using `[← hcc PP, ← e, hcc]`. Rewrite `h` using `[hQ]`. Conclude with `hP PP (Or.inl (h.resolve_right (Finset.notMem_empty _)))`. Rewrite using `[offS_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce `h PP hPP`. Rewrite `hPP` using `[hQ]`. Establish `hPP'` using `hPP.resolve_right (Finset.notMem_empty _)`. Establish `key : PP.under (𝓞 D.host.F) ≠ P.under (𝓞 D.host.F)` using `fun e => h ((hSF _).2 ⟨PP, hPP', by rw [← e]; rfl⟩)`.

Conclude with `⟨fun e => key (by rw [e]), fun e => key (GlobalTheory.LevelPlaces.under_eq_of_isConjPl e)⟩`. Introduce `h hm`. Take `⟨PP, hPP, e⟩` from `(hSF _).1 hm`. Take `⟨h1, h2⟩` from `h PP (Or.inl hPP)`. Establish `e' : P.under (𝓞 D.host.F) = PP.under (𝓞 D.host.F)` using `HeightOneSpectrum.ext e.symm`.

Break down `eq_or_conj_of_under_eq e' with h3 | h3` into its components or cases. Conclude with `h1 h3.symm`. Conclude with `h2 (isConjPl_iff.2 h3)`. Take `⟨gramR, c0R, c0L, hT⟩` from `hF.tie`. Take `⟨h1, h2, h3⟩` from `(hT.ok t P).1 hP`.

Rewrite `h1`, `h3` using `[Formalism.DivisionValues.GluingInclusion.conjIdeal_eq]`. Use `⟨fun PP h => ?_, fun e => h1 (by rw [e]), ?_⟩` and prove the remaining obligations. Establish `hm : PP ∈ (R.Sb : Set (Pl D.host.E)) ∪ (R.Q t : Set (Pl D.host.E))` using `h.imp (fun h => hF.Sb h) id`. Use `⟨fun e => h2 (e ▸ hm), fun hc => h3 PP hm ?_⟩` and prove the remaining obligations. Rewrite using `[isConjPl_iff.1 hc, hcc]`.

Rewrite using `[hT.q P, Ideal.absNorm_apply, Submodule.cardQuot_apply]`.
-/
theorem good_primes : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.Q A.μ0 = ∅ ∧ (∀ t P, Good R t P → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ Good R t (Formalism.DivisionValues.conjPl P) ∧ Good R A.μ0 P) ∧ (∀ SF, IsSF R SF → ∀ P, OffS D SF P ↔ Good R A.μ0 P) ∧ (R.IsFam → ∀ t, ∀ P ∈ A.ok t, Good R t (R.pl P) ∧ Formalism.DivisionValues.conjPl (R.pl P) ≠ R.pl P ∧ A.q P = Ideal.absNorm (R.pl P).asIdeal) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL
  have hQ : R.Q A.μ0 = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun PP h => ?_
    refine (hL.Q_ram A.μ0 PP).2 (Or.inl h) ?_
    rw [hL.xi_base]
    exact fun x _ => rfl
  have hcc := fun w : Pl D.host.E => Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl w
  refine ⟨hQ, fun t P hP => ⟨fun hg => ?_, fun PP h => ?_, fun PP h => ?_⟩, fun SF hSF P => ?_, fun hF t P hP => ?_⟩
  · have hk : ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
      rw [Nat.cast_mul] at hg
      rcases P.isPrime.mem_or_mem hg with h | h
      exacts [⟨0, h⟩, ⟨1, h⟩]
    obtain ⟨k, hk⟩ := hk
    rcases GlobalTheory.ConjOverQuad.div_or_conj_div D R.C.P k P hk with h | ⟨w', h, hw⟩
    · exact (hP P (Or.inl ((hL.Pg P).2 ⟨k, h⟩))).1 rfl
    · refine (hP w' (Or.inl ((hL.Pg w').2 ⟨k, h⟩))).2 (isConjPl_iff.2 ?_)
      rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq] at hw
      rw [HeightOneSpectrum.ext hw, hcc]
  · obtain ⟨h1, h2⟩ := hP PP h
    rw [isConjPl_iff] at h2 ⊢
    refine ⟨fun e => h2 (by rw [e, hcc]), fun e => h1 ?_⟩
    rw [← hcc PP, ← e, hcc]
  · rw [hQ] at h
    exact hP PP (Or.inl (h.resolve_right (Finset.notMem_empty _)))
  · rw [offS_iff]
    constructor
    · intro h PP hPP
      rw [hQ] at hPP
      have hPP' := hPP.resolve_right (Finset.notMem_empty _)
      have key : PP.under (𝓞 D.host.F) ≠ P.under (𝓞 D.host.F) := fun e =>
        h ((hSF _).2 ⟨PP, hPP', by rw [← e]; rfl⟩)
      exact ⟨fun e => key (by rw [e]), fun e => key (GlobalTheory.LevelPlaces.under_eq_of_isConjPl e)⟩
    · intro h hm
      obtain ⟨PP, hPP, e⟩ := (hSF _).1 hm
      obtain ⟨h1, h2⟩ := h PP (Or.inl hPP)
      have e' : P.under (𝓞 D.host.F) = PP.under (𝓞 D.host.F) := HeightOneSpectrum.ext e.symm
      rcases eq_or_conj_of_under_eq e' with h3 | h3
      · exact h1 h3.symm
      · exact h2 (isConjPl_iff.2 h3)
  · obtain ⟨gramR, c0R, c0L, hT⟩ := hF.tie
    obtain ⟨h1, h2, h3⟩ := (hT.ok t P).1 hP
    rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq] at h1 h3
    refine ⟨fun PP h => ?_, fun e => h1 (by rw [e]), ?_⟩
    · have hm : PP ∈ (R.Sb : Set (Pl D.host.E)) ∪ (R.Q t : Set (Pl D.host.E)) :=
        h.imp (fun h => hF.Sb h) id
      refine ⟨fun e => h2 (e ▸ hm), fun hc => h3 PP hm ?_⟩
      rw [isConjPl_iff.1 hc, hcc]
    · rw [hT.q P, Ideal.absNorm_apply, Submodule.cardQuot_apply]

end GlobalTheory.GoodPrimes
