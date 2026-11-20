import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StaircaseIdealConjugateInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMulInvIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option synthInstance.maxHeartbeats 160000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.StairUnit

/- English proof (translation)
Establish `h : ∀ v' : GlobalTheory.FinPl.Pl D, ∃ x : 𝓞 D.host.F, x ∉ v.asIdeal ∧ (v' ∈ P.S0 → x ∈ v'.asIdeal)`. Introduce `v'`. Distinguish the cases in `h' : v' ∈ P.S0`. Establish `hn : ¬ v'.asIdeal ≤ v.asIdeal` using `fun hle => hv (HeightOneSpectrum.ext (v'.isMaximal.eq_of_le v.isPrime.ne_top hle) ▸ h')`. Take `⟨x, hx, hx'⟩` from `Set.not_subset.1 hn`.

Conclude with `⟨x, hx', fun _ => hx⟩`. Conclude with `⟨1, (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top, fun h => absurd h h'⟩`. Use `choose x hx hx' using h`. Use `⟨∏ v' ∈ P.S0, x v' ^ P.depth sc v', fun hu => ?_, ?_⟩` and prove the remaining obligations. Use `haveI := v.isPrime`.

Take `⟨v', -, h'⟩` from `Ideal.IsPrime.prod_mem_iff.1 hu`. Conclude with `hx v' (v.isPrime.mem_of_pow_mem _ h')`. Rewrite using `[map_prod]`. Use `Ideal.prod_mem_prod fun v' h' => ?_` and prove the remaining obligations. Rewrite using `[map_pow]`.

Use `Ideal.pow_mem_pow ?_ _` and prove the remaining obligations. Establish `h1 : x v' ∈ ((P.w v').under (𝓞 D.host.F)).asIdeal` using `by rw [P.under_w h']; exact hx' v' h'`. Conclude with `h1`.
-/
theorem exists_mem_modul_notMem {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) (v : GlobalTheory.FinPl.Pl D)
    (hv : v ∉ P.S0) : ∃ u : 𝓞 D.host.F, u ∉ v.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) u ∈ P.modul sc := by
  have h : ∀ v' : GlobalTheory.FinPl.Pl D, ∃ x : 𝓞 D.host.F, x ∉ v.asIdeal ∧ (v' ∈ P.S0 → x ∈ v'.asIdeal) := by
    intro v'
    by_cases h' : v' ∈ P.S0
    · have hn : ¬ v'.asIdeal ≤ v.asIdeal := fun hle =>
        hv (HeightOneSpectrum.ext (v'.isMaximal.eq_of_le v.isPrime.ne_top hle) ▸ h')
      obtain ⟨x, hx, hx'⟩ := Set.not_subset.1 hn
      exact ⟨x, hx', fun _ => hx⟩
    · exact ⟨1, (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top, fun h => absurd h h'⟩
  choose x hx hx' using h
  refine ⟨∏ v' ∈ P.S0, x v' ^ P.depth sc v', fun hu => ?_, ?_⟩
  · haveI := v.isPrime
    obtain ⟨v', -, h'⟩ := Ideal.IsPrime.prod_mem_iff.1 hu
    exact hx v' (v.isPrime.mem_of_pow_mem _ h')
  · rw [map_prod]
    refine Ideal.prod_mem_prod fun v' h' => ?_
    rw [map_pow]
    refine Ideal.pow_mem_pow ?_ _
    have h1 : x v' ∈ ((P.w v').under (𝓞 D.host.F)).asIdeal := by rw [P.under_w h']; exact hx' v' h'
    exact h1

/- English proof (translation)
Use `FractionalIdeal.mul_induction_on ht (fun x hx c hc => ?_) fun x y => Submodule.add_mem _` and prove the remaining obligations. Use `FractionalIdeal.mul_induction_on (C := fun x => x * c ∈ Submodule.span (𝓞 E) {t : E | ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, t = star (a * b) * c}) hx (fun a ha b hb => ?_) fun x y hx hy => ?_` and prove the remaining obligations. Conclude with `Submodule.subset_span ⟨_, hA a ha, _, hB b hb, c, hc, by rw [star_mul', star_star, star_star]⟩`. Rewrite using `[add_mul]`. Conclude with `Submodule.add_mem _ hx hy`.
-/
theorem mem_span_of_mem_mul {E : Type} [Field E] [NumberField E] [StarRing E] {A B A' B' C : FractionalIdeal (𝓞 E)⁰ E}
    (hA : ∀ x ∈ A', star x ∈ A) (hB : ∀ x ∈ B', star x ∈ B) {t : E} (ht : t ∈ A' * B' * C) :
    t ∈ Submodule.span (𝓞 E) {t : E | ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, t = star (a * b) * c} := by
  refine FractionalIdeal.mul_induction_on ht (fun x hx c hc => ?_) fun x y => Submodule.add_mem _
  refine FractionalIdeal.mul_induction_on (C := fun x => x * c ∈ Submodule.span (𝓞 E)
    {t : E | ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, t = star (a * b) * c}) hx (fun a ha b hb => ?_) fun x y hx hy => ?_
  · exact Submodule.subset_span ⟨_, hA a ha, _, hB b hb, c, hc, by rw [star_mul', star_star, star_star]⟩
  · rw [add_mul]; exact Submodule.add_mem _ hx hy

/- English proof (translation)
Introduce `D T L sc G ρ p q hpq v hv`. Take `⟨u, hu, hum⟩` from `exists_mem_modul_notMem G.pl sc v hv`. Use `⟨u, hu, ?_⟩` and prove the remaining obligations. Establish `hs : ∀ x : D.host.E, star x = D.host.conj x` using `bridge_star_holds D.R D.host`. Take `⟨hAA, hAAc⟩` from `(GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1`.

Take `⟨hA, hconj⟩` from `(GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 T L G.pl sc`. Establish `hne : ∀ {I J : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E}, I ≠ 0 → (∀ x, x ∈ J ↔ star x ∈ I) → J ≠ 0`. Introduce `I J hI hJ h0`. Apply `hI` to reduce the goal to its premises. Rewrite `h0`, the goal using `[FractionalIdeal.eq_zero_iff]`.

Introduce `y hy`. Establish `h2` using `h0 _ ((hJ (star y)).2 (by rwa [star_star]))`. Rewrite `h2` using `[star_eq_zero]`. Then use the resulting hypothesis. Establish `hAb` using `hne hA hconj`. Establish `hAAb` using `hne hAA hAAc`.

Establish `hB : ∀ x ∈ (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) q.rev)⁻¹, star x ∈ stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) q`. Introduce `x hx`. Establish `h1` using `(GlobalTheory.ChiGrid.stairId_ne_zero_and_mem_rev_iff D _ _ hA hconj _ q.rev).2 (star x)`. Rewrite `h1` using `[Fin.rev_rev, star_star]`. Conclude with `h1.2 hx`.

Establish `key : D.host.AAbar * (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) q.rev)⁻¹ * stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) p = ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)`. Establish `hq` using `q.2`. Establish `e1 : 2 * ρ + 1 - 1 - q.rev.1 = q.1 + 1` using `by rw [Fin.val_rev]; omega`. Establish `e2 : q.rev.1 + 1 = p.1` using `by rw [Fin.val_rev]; omega`. Establish `e3 : 2 * ρ + 2 - 1 - p.1 = q.1 + 1` using `by omega`.

Establish `e4 : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) = D.host.AAbar * (G.pl.stAbar sc)⁻¹`. Rewrite using `[Places.stAbar, mul_inv, inv_inv, mul_inv_cancel_left₀ hAAb]`. Unfold `stairId`. Rewrite using `[e1, e2, e3, e4, pow_succ (G.pl.stAbar sc) p.1]`. Establish `h1 : G.pl.stA sc ^ (q.1 + 1) ≠ 0` using `pow_ne_zero _ hA`.

Establish `h2 : G.pl.stAbar sc ^ p.1 ≠ 0` using `pow_ne_zero _ hAb`. Clear the denominators using the available nonvanishing facts. Establish `hmem : ((u : D.host.F) : D.host.E) ∈ ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)` using `(FractionalIdeal.mem_coeIdeal _).2 ⟨_, hum, rfl⟩`. Rewrite `hmem` using `[← key]`. Establish `h` using `mem_span_of_mem_mul (fun x hx => (hAAc x).1 hx) hB hmem`.

Simplify using `only [hs] at h`. Conclude with `h`.
-/
theorem exists_unit_mem_span : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (ρ : ℕ) (p : Fin (2 * ρ + 2 - 1)) (q : Fin (2 * ρ + 1 - 1)), p.1 + q.1 = 2 * ρ → ∀ v : GlobalTheory.FinPl.Pl D, v ∉ G.pl.S0 → ∃ u : 𝓞 D.host.F, u ∉ v.asIdeal ∧ ((u : D.host.F) : D.host.E) ∈ Submodule.span (𝓞 D.host.E) {t : D.host.E | ∃ a ∈ D.host.AA, ∃ c' ∈ stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) q, ∃ c ∈ stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) p, t = D.host.conj (a * c') * c} := by
  intro D T L sc G ρ p q hpq v hv
  obtain ⟨u, hu, hum⟩ := exists_mem_modul_notMem G.pl sc v hv
  refine ⟨u, hu, ?_⟩
  have hs : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  obtain ⟨hAA, hAAc⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1
  obtain ⟨hA, hconj⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 T L G.pl sc
  have hne : ∀ {I J : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E}, I ≠ 0 → (∀ x, x ∈ J ↔ star x ∈ I) → J ≠ 0 := by
    intro I J hI hJ h0
    apply hI
    rw [FractionalIdeal.eq_zero_iff] at h0 ⊢
    intro y hy
    have h2 := h0 _ ((hJ (star y)).2 (by rwa [star_star]))
    rwa [star_eq_zero] at h2
  have hAb := hne hA hconj
  have hAAb := hne hAA hAAc
  have hB : ∀ x ∈ (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) q.rev)⁻¹,
      star x ∈ stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) q := by
    intro x hx
    have h1 := (GlobalTheory.ChiGrid.stairId_ne_zero_and_mem_rev_iff D _ _ hA hconj _ q.rev).2 (star x)
    rw [Fin.rev_rev, star_star] at h1
    exact h1.2 hx
  have key : D.host.AAbar * (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) q.rev)⁻¹ *
      stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) p =
      ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
    have hq := q.2
    have e1 : 2 * ρ + 1 - 1 - q.rev.1 = q.1 + 1 := by rw [Fin.val_rev]; omega
    have e2 : q.rev.1 + 1 = p.1 := by rw [Fin.val_rev]; omega
    have e3 : 2 * ρ + 2 - 1 - p.1 = q.1 + 1 := by omega
    have e4 : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) =
        D.host.AAbar * (G.pl.stAbar sc)⁻¹ := by
      rw [Places.stAbar, mul_inv, inv_inv, mul_inv_cancel_left₀ hAAb]
    unfold stairId
    rw [e1, e2, e3, e4, pow_succ (G.pl.stAbar sc) p.1]
    have h1 : G.pl.stA sc ^ (q.1 + 1) ≠ 0 := pow_ne_zero _ hA
    have h2 : G.pl.stAbar sc ^ p.1 ≠ 0 := pow_ne_zero _ hAb
    field_simp
  have hmem : ((u : D.host.F) : D.host.E) ∈
      ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :=
    (FractionalIdeal.mem_coeIdeal _).2 ⟨_, hum, rfl⟩
  rw [← key] at hmem
  have h := mem_span_of_mem_mul (fun x hx => (hAAc x).1 hx) hB hmem
  simp only [hs] at h
  exact h

end GlobalTheory.StairUnit
