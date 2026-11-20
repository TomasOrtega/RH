import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IteratedLiftChains

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Links
open GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains GlobalTheory.PRep GlobalTheory.LFun
open Formalism.UG (IsCommensurated Hecke)
open Formalism.MainNotions.SchurIrreducible (IsSplit)

namespace GlobalTheory.SplitPlace

/- English proof (translation)
Use `haveI hfin : Module.Finite (𝓞 F) (𝓞 E) := by first`. Consider the case `infer_instance`. Consider the case `exact Module.Finite.of_restrictScalars_finite ℤ (𝓞 F) (𝓞 E)`. Use `haveI hint : Algebra.IsIntegral (𝓞 F) (𝓞 E) := by first`. Consider the case `infer_instance`.

Consider the case `exact Algebra.IsIntegral.of_finite (𝓞 F) (𝓞 E)`. Establish `hdeg : Module.finrank (𝓞 F) (𝓞 E) = 2`. Rewrite using `[← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E]`. Conclude with `h2`. Establish `hsum` using `Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 E)`.

Rewrite `hsum` using `[hdeg]`. Establish `hover : ∀ Q : Ideal (𝓞 E), Q.LiesOver v.asIdeal → (p : 𝓞 E) ∈ Q`. Introduce `Q hQo`. Establish `hmem : (p : 𝓞 F) ∈ Q.under (𝓞 F)`. Rewrite using `[← hQo.over]`.

Conclude with `hv`. Establish `hmem' : algebraMap (𝓞 F) (𝓞 E) (p : 𝓞 F) ∈ Q` using `hmem`. Simplify using `using hmem'`. Establish `hf : ∀ q : v.asIdeal.primesOver (𝓞 E), q.1.inertiaDeg (𝓞 F) = 1`. Introduce and unpack `⟨Q, hQp, hQo⟩`.

Use `haveI := hQp`. Use `haveI := hQo`. Establish `hQ0 : Q ≠ ⊥` using `Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q`. Establish `hN : Ideal.absNorm Q = p` using `(h ⟨Q, hQp, hQ0⟩ (hover Q hQo)).1`. Establish `key : Ideal.absNorm v.asIdeal ^ Q.inertiaDeg (𝓞 F) = p`.

Rewrite using `[Ideal.absNorm_pow_inertiaDeg v.asIdeal Q]`. Conclude with `hN`. Conclude with `Nat.Prime.eq_one_of_pow (by rw [key]; exact hp)`. Establish `he : ∀ q : v.asIdeal.primesOver (𝓞 E), q.1.ramificationIdx (𝓞 F) = 1`. Introduce and unpack `⟨Q, hQp, hQo⟩`.

Use `haveI := hQp`. Use `haveI := hQo`. Establish `hQ0 : Q ≠ ⊥` using `Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q`. Establish `hsq : (p : 𝓞 E) ∉ Q ^ 2` using `(h ⟨Q, hQp, hQ0⟩ (hover Q hQo)).2`. Establish `hle : Q.ramificationIdx (𝓞 F) ≤ 1`.

Rewrite using `[← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal Q v.ne_bot]`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `hmap : v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) ≤ Q ^ 2` using `Ideal.le_pow_of_le_ramificationIdx' hlt`. Apply `hsq` to reduce the goal to its premises.

Establish `hin` using `hmap (Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) hv)`. Simplify using `using hin`. Establish `hpos : 0 < Q.ramificationIdx (𝓞 F)` using `Ideal.ramificationIdx_pos Q (𝓞 F)`. Use `show Q.ramificationIdx (𝓞 F) = 1`. Use linear arithmetic over natural numbers and integers.

Assume the negation of the conclusion as `hns`. Take `⟨Q0, hQ0p, hQ0o⟩ : ∃ Q0 : Ideal (𝓞 E), Q0.IsPrime ∧ Q0.LiesOver v.asIdeal` from `by first`. Consider the case `obtain ⟨Q0, hQ0m, hQ0o⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal`. Conclude with `⟨Q0, hQ0m.isPrime, hQ0o⟩`. Consider the case `obtain ⟨Q0, hQ0⟩ := Set.nonempty_of_ncard_ne_zero (IsDedekindDomain.primesOver_ncard_ne_zero v.asIdeal (𝓞 E))`.

Conclude with `⟨Q0, hQ0.1, hQ0.2⟩`. Set `q0 : v.asIdeal.primesOver (𝓞 E)` to `⟨Q0, hQ0p, hQ0o⟩`. Establish `honly : ∀ q : v.asIdeal.primesOver (𝓞 E), q = q0`. Introduce and unpack `⟨Q, hQp, hQo⟩`. Assume the negation of the conclusion as `hne`.

Apply `hns` to reduce the goal to its premises. Use `haveI := hQo`. Use `haveI := hQ0o`. Use `⟨⟨Q, hQp, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, ⟨Q0, hQ0p, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q0⟩, ?_, hQo.over.symm, hQ0o.over.symm⟩` and prove the remaining obligations. Introduce `hPQ`.

Conclude with `hne (Subtype.ext (congrArg HeightOneSpectrum.asIdeal hPQ))`. Rewrite `hsum` using `[Finset.sum_eq_single q0 (fun b _ hb => absurd (honly b) hb) (fun h0 => absurd (Finset.mem_univ q0) h0), he q0, hf q0]`. Use linear arithmetic over natural numbers and integers.
-/
theorem isSplit_of_norm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) {p : ℕ} (hp : p.Prime)
    (h : ∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal →
      Ideal.absNorm w.asIdeal = p ∧ (p : 𝓞 E) ∉ w.asIdeal ^ 2)
    (v : HeightOneSpectrum (𝓞 F)) (hv : (p : 𝓞 F) ∈ v.asIdeal) : IsSplit (E := E) v := by
  classical
  haveI hfin : Module.Finite (𝓞 F) (𝓞 E) := by
    first
    | infer_instance
    | exact Module.Finite.of_restrictScalars_finite ℤ (𝓞 F) (𝓞 E)
  haveI hint : Algebra.IsIntegral (𝓞 F) (𝓞 E) := by
    first
    | infer_instance
    | exact Algebra.IsIntegral.of_finite (𝓞 F) (𝓞 E)

  have hdeg : Module.finrank (𝓞 F) (𝓞 E) = 2 := by
    rw [← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E]
    exact h2

  have hsum := Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 E)
  rw [hdeg] at hsum

  have hover : ∀ Q : Ideal (𝓞 E), Q.LiesOver v.asIdeal → (p : 𝓞 E) ∈ Q := by
    intro Q hQo
    have hmem : (p : 𝓞 F) ∈ Q.under (𝓞 F) := by
      rw [← hQo.over]
      exact hv
    have hmem' : algebraMap (𝓞 F) (𝓞 E) (p : 𝓞 F) ∈ Q := hmem
    simpa using hmem'

  have hf : ∀ q : v.asIdeal.primesOver (𝓞 E), q.1.inertiaDeg (𝓞 F) = 1 := by
    rintro ⟨Q, hQp, hQo⟩
    haveI := hQp
    haveI := hQo
    have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
    have hN : Ideal.absNorm Q = p := (h ⟨Q, hQp, hQ0⟩ (hover Q hQo)).1
    have key : Ideal.absNorm v.asIdeal ^ Q.inertiaDeg (𝓞 F) = p := by
      rw [Ideal.absNorm_pow_inertiaDeg v.asIdeal Q]
      exact hN
    exact Nat.Prime.eq_one_of_pow (by rw [key]; exact hp)

  have he : ∀ q : v.asIdeal.primesOver (𝓞 E), q.1.ramificationIdx (𝓞 F) = 1 := by
    rintro ⟨Q, hQp, hQo⟩
    haveI := hQp
    haveI := hQo
    have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
    have hsq : (p : 𝓞 E) ∉ Q ^ 2 := (h ⟨Q, hQp, hQ0⟩ (hover Q hQo)).2
    have hle : Q.ramificationIdx (𝓞 F) ≤ 1 := by
      rw [← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal Q v.ne_bot]
      by_contra hlt
      push_neg at hlt
      have hmap : v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) ≤ Q ^ 2 :=
        Ideal.le_pow_of_le_ramificationIdx' hlt
      apply hsq
      have hin := hmap (Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) hv)
      simpa using hin
    have hpos : 0 < Q.ramificationIdx (𝓞 F) := Ideal.ramificationIdx_pos Q (𝓞 F)
    show Q.ramificationIdx (𝓞 F) = 1
    omega

  by_contra hns
  obtain ⟨Q0, hQ0p, hQ0o⟩ : ∃ Q0 : Ideal (𝓞 E), Q0.IsPrime ∧ Q0.LiesOver v.asIdeal := by
    first
    | obtain ⟨Q0, hQ0m, hQ0o⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
      exact ⟨Q0, hQ0m.isPrime, hQ0o⟩
    | obtain ⟨Q0, hQ0⟩ := Set.nonempty_of_ncard_ne_zero
        (IsDedekindDomain.primesOver_ncard_ne_zero v.asIdeal (𝓞 E))
      exact ⟨Q0, hQ0.1, hQ0.2⟩
  let q0 : v.asIdeal.primesOver (𝓞 E) := ⟨Q0, hQ0p, hQ0o⟩
  have honly : ∀ q : v.asIdeal.primesOver (𝓞 E), q = q0 := by
    rintro ⟨Q, hQp, hQo⟩
    by_contra hne
    apply hns
    haveI := hQo
    haveI := hQ0o
    refine ⟨⟨Q, hQp, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩,
      ⟨Q0, hQ0p, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q0⟩, ?_, hQo.over.symm, hQ0o.over.symm⟩
    intro hPQ
    exact hne (Subtype.ext (congrArg HeightOneSpectrum.asIdeal hPQ))
  rw [Finset.sum_eq_single q0 (fun b _ hb => absurd (honly b) hb)
    (fun h0 => absurd (Finset.mem_univ q0) h0), he q0, hf q0] at hsum
  omega

/- English proof (translation)
Introduce `D p hp v hv`. Establish `h2 : Module.finrank D.host.F D.host.E = 2` using `by first`. Consider the case `haveI : IsCMField D.host.E := Formalism.HC.HostAx.isCMField_hostE D.host.toHostAx`. Conclude with `IsQuadraticExtension.finrank_eq_two _ _`. Consider the case `have hE := Formalism.HC.HostAx.finrank_cmField D.host.toHostAx`.

Establish `hF` using `Formalism.HC.HostAx.finrank_hostF D.host.toHostAx`. Establish `hm` using `Module.finrank_mul_finrank ℚ D.host.F D.host.E`. Establish `hpos : 0 < Module.finrank ℚ D.host.F` using `Module.finrank_pos`. Rewrite `hm` using `[hE, hF]`. Rewrite `hpos` using `[hF]`.

Conclude with `Nat.eq_of_mul_eq_mul_left hpos (by linarith)`. Conclude with `isSplit_of_norm h2 hp.1 hp.2 v hv`.
-/
theorem isSplit_of_splitsCompletely : ∀ (D : D7) (p : ℕ), SplitsCompletely D p → ∀ v : HeightOneSpectrum (𝓞 D.host.F), (p : 𝓞 D.host.F) ∈ v.asIdeal → IsSplit (E := D.host.E) v := by
  intro D p hp v hv
  have h2 : Module.finrank D.host.F D.host.E = 2 := by
    first
    | haveI : IsCMField D.host.E := Formalism.HC.HostAx.isCMField_hostE D.host.toHostAx
      exact IsQuadraticExtension.finrank_eq_two _ _
    | have hE := Formalism.HC.HostAx.finrank_cmField D.host.toHostAx
      have hF := Formalism.HC.HostAx.finrank_hostF D.host.toHostAx
      have hm := Module.finrank_mul_finrank ℚ D.host.F D.host.E
      have hpos : 0 < Module.finrank ℚ D.host.F := Module.finrank_pos
      rw [hE, hF] at hm
      rw [hF] at hpos
      exact Nat.eq_of_mul_eq_mul_left hpos (by linarith)
  exact isSplit_of_norm h2 hp.1 hp.2 v hv

end GlobalTheory.SplitPlace
