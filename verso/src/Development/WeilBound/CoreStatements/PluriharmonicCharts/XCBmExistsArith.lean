import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BirationalOfTranscendenceDegreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FunctionFieldRatioGenerators
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerFinrankFractionFieldStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.MetricStatements.ExistsFlagModelBaseMetric
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.RootOnFund
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
import Development.AutomorphicSpectrum.Proofs.MetricProofs.OmHeightslockG
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

namespace PositivityTheory.Xgp.c_bm_exists_arith

open KaehlerDifferential

open Algebra in
/- English proof (translation)
Establish `: Algebra.IsAlgebraic ℤ ℚ` using `IsLocalization.isAlgebraic _ (nonZeroDivisors ℤ)`. Establish `: FaithfulSMul ℤ ℚ` using `(faithfulSMul_iff_algebraMap_injective ℤ ℚ).mpr Int.cast_injective`. Establish `: FaithfulSMul ℚ L` using `(faithfulSMul_iff_algebraMap_injective ℚ L).mpr (algebraMap ℚ L).injective`. Rewrite using `[← trdeg_add_eq ℤ ℚ (A := L), trdeg_eq_zero, zero_add]`.
-/
theorem trdeg_int_eq_rat (L : Type) [Field L] [Algebra ℚ L] : Algebra.trdeg ℤ L = Algebra.trdeg ℚ L := by
  have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic _ (nonZeroDivisors ℤ)
  have : FaithfulSMul ℤ ℚ := (faithfulSMul_iff_algebraMap_injective ℤ ℚ).mpr Int.cast_injective
  have : FaithfulSMul ℚ L := (faithfulSMul_iff_algebraMap_injective ℚ L).mpr (algebraMap ℚ L).injective
  rw [← trdeg_add_eq ℤ ℚ (A := L), trdeg_eq_zero, zero_add]

end PositivityTheory.Xgp.c_bm_exists_arith

/- English proof (translation)
Introduce `X Ω _ _ ξ K _ J _ x n bd hn T hs`. Take `⟨c, hc⟩` from `T.cover ⟨genPt ξ, specializes_rfl⟩`. Establish `hc0 : ∀ k, x ⟨k, c k⟩ ≠ 0` using `fun k => Finset.prod_ne_zero_iff.1 hc.1 k (Finset.mem_univ k)`. Take `⟨m, f, a, hf, ha, hsum, hmain⟩` from `hs c hc0`. Choose the witnesses or unpack the hypotheses as in `⟨l, hl⟩ : ∃ l, f l ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Simplify using `[h] at hsum`. Use `set R : Set Ω := Set.range fun p : Σ k, J k => x p / x ⟨p.1, c p.1⟩ with hR`. Use `set S : Subalgebra ℚ Ω := Algebra.adjoin ℚ (insert (f l)⁻¹ R) with hS`.

Take `⟨hsm, z, n', -, hli, hspan, -⟩` from `hmain l hl S rfl`. Establish `hRS : R ⊆ S` using `fun r hr => Algebra.subset_adjoin (Set.mem_insert_of_mem _ hr)`. Establish `hmono : Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, x ⟨k, j k⟩) / ∏ k, x ⟨k, c k⟩) ≤ S.restrictScalars ℤ`. Use `Algebra.adjoin_le ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩`.

Use `show (∏ k, x ⟨k, j k⟩) / ∏ k, x ⟨k, c k⟩ ∈ S`. Rewrite using `[← Finset.prod_div_distrib]`. Conclude with `Subalgebra.prod_mem _ fun k _ => hRS ⟨⟨k, j k⟩, rfl⟩`. Establish `hfr : IsFractionRing S Ω`. Use `IsFractionRing.of_field S Ω fun a => ?_` and prove the remaining obligations.

Take `⟨g, hg, h, hh, -, e⟩` from `GlobalTheory.CompanionTheory.Ar.FlagBun.FracChart.exists_eq_div_adjoin X Ω ξ _ _ c T hc.1 a`. Conclude with `⟨⟨g, hmono hg⟩, ⟨h, hmono hh⟩, e⟩`. Establish `hfin : Module.finrank Ω (KaehlerDifferential ℚ Ω) = n` using `GlobalTheory.CompanionTheory.Ggeo.finrank_kaehler_fractionRing_eq_of_basis ℚ S ℚ Ω n z hli hspan`. Establish `hK : Nonempty K`. Assume the negation of the conclusion as `hK`.

Rewrite `hK` using `[not_nonempty_iff]`. Establish `hall : ∀ a : Ω, a ∈ Set.range (algebraMap ℚ Ω)`. Introduce `a`. Take `⟨g, hg, h, hh, -, e⟩` from `GlobalTheory.CompanionTheory.Ar.FlagBun.FracChart.exists_eq_div_adjoin X Ω ξ _ _ c T hc.1 a`. Establish `h1 : (Set.range fun j : (k : K) → J k => (∏ k, x ⟨k, j k⟩) / ∏ k, x ⟨k, c k⟩) ⊆ {1}`.

Introduce and unpack `_ ⟨j, rfl⟩`. Simplify using the standard rewrite rules. Establish `hbot : ∀ b ∈ Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, x ⟨k, j k⟩) / ∏ k, x ⟨k, c k⟩), ∃ q : ℤ, b = q`. Introduce `b hb`. Use `Algebra.adjoin_mono h1 hb` as an intermediate fact.

Rewrite `this` using `[Algebra.adjoin_singleton_one, Algebra.mem_bot]`. Take `⟨q, rfl⟩` from `this`. Conclude with `⟨q, by simp⟩`. Take `⟨q1, rfl⟩` from `hbot g hg`. Take `⟨q2, rfl⟩` from `hbot h hh`.

Conclude with `⟨(q1 : ℚ) / q2, by rw [e]; simp⟩`. Establish `hsub : Subsingleton (KaehlerDifferential ℚ Ω)`. Establish `htop` using `KaehlerDifferential.span_range_derivation ℚ Ω`. Use `subsingleton_of_forall_eq 0 fun w => ?_` and prove the remaining obligations. Establish `hw : w ∈ (⊤ : Submodule Ω (KaehlerDifferential ℚ Ω))` using `trivial`.

Rewrite `hw` using `[← htop]`. Establish `hle : Submodule.span Ω (Set.range (KaehlerDifferential.D ℚ Ω)) ≤ ⊥`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨b, rfl⟩`. Take `⟨q, rfl⟩` from `hall b`.

Conclude with `(KaehlerDifferential.D ℚ Ω).map_algebraMap q`. Simplify using `using hle hw`. Use `Module.finrank_zero_of_subsingleton (R := Ω) (M := KaehlerDifferential ℚ Ω)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `: Algebra.EssFiniteType S Ω` using `.of_isLocalization Ω (nonZeroDivisors S)`.

Establish `: Algebra.EssFiniteType ℚ Ω` using `.comp ℚ S Ω`. Establish `hfd : Module.Finite Ω (KaehlerDifferential ℚ Ω)` using `Module.finite_of_finrank_pos (by omega)`. Establish `htr : Algebra.trdeg ℚ Ω = n`. Rewrite using `[← GlobalTheory.rank_kaehler_eq_trdeg, ← Module.finrank_eq_rank, hfin]`. Establish `htr' : Algebra.trdeg ℤ Ω = n` using `(PositivityTheory.Xgp.c_bm_exists_arith.trdeg_int_eq_rat Ω).trans htr`.

Conclude with `(GlobalTheory.T.birational_of_transcendence_degree X Ω ξ K J x n T htr').2`.
-/
theorem PositivityTheory.Xgp.t_c_bm_exists_arith : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (x : (Σ k, J k) → Ω) (n : ℕ) (bd : Ideal (MRing J)), 1 ≤ n → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, x ⟨k, c' k⟩) → Cmp.IsSncModel x n bd → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal x) (n + 1) := by
  intro X Ω _ _ ξ K _ J _ x n bd hn T hs
  classical

  obtain ⟨c, hc⟩ := T.cover ⟨genPt ξ, specializes_rfl⟩
  have hc0 : ∀ k, x ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc.1 k (Finset.mem_univ k)
  obtain ⟨m, f, a, hf, ha, hsum, hmain⟩ := hs c hc0
  obtain ⟨l, hl⟩ : ∃ l, f l ≠ 0 := by
    by_contra h
    push_neg at h
    simp [h] at hsum
  set R : Set Ω := Set.range fun p : Σ k, J k => x p / x ⟨p.1, c p.1⟩ with hR
  set S : Subalgebra ℚ Ω := Algebra.adjoin ℚ (insert (f l)⁻¹ R) with hS
  obtain ⟨hsm, z, n', -, hli, hspan, -⟩ := hmain l hl S rfl

  have hRS : R ⊆ S := fun r hr => Algebra.subset_adjoin (Set.mem_insert_of_mem _ hr)
  have hmono : Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k =>
      (∏ k, x ⟨k, j k⟩) / ∏ k, x ⟨k, c k⟩) ≤ S.restrictScalars ℤ := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨j, rfl⟩
    show (∏ k, x ⟨k, j k⟩) / ∏ k, x ⟨k, c k⟩ ∈ S
    rw [← Finset.prod_div_distrib]
    exact Subalgebra.prod_mem _ fun k _ => hRS ⟨⟨k, j k⟩, rfl⟩
  have hfr : IsFractionRing S Ω := by
    refine IsFractionRing.of_field S Ω fun a => ?_
    obtain ⟨g, hg, h, hh, -, e⟩ := GlobalTheory.CompanionTheory.Ar.FlagBun.FracChart.exists_eq_div_adjoin X Ω ξ _ _ c T hc.1 a
    exact ⟨⟨g, hmono hg⟩, ⟨h, hmono hh⟩, e⟩
  have hfin : Module.finrank Ω (KaehlerDifferential ℚ Ω) = n :=
    GlobalTheory.CompanionTheory.Ggeo.finrank_kaehler_fractionRing_eq_of_basis ℚ S ℚ Ω n z hli hspan

  have hK : Nonempty K := by
    by_contra hK
    rw [not_nonempty_iff] at hK
    have hall : ∀ a : Ω, a ∈ Set.range (algebraMap ℚ Ω) := by
      intro a
      obtain ⟨g, hg, h, hh, -, e⟩ := GlobalTheory.CompanionTheory.Ar.FlagBun.FracChart.exists_eq_div_adjoin X Ω ξ _ _ c T hc.1 a
      have h1 : (Set.range fun j : (k : K) → J k => (∏ k, x ⟨k, j k⟩) / ∏ k, x ⟨k, c k⟩) ⊆ {1} := by
        rintro _ ⟨j, rfl⟩
        simp
      have hbot : ∀ b ∈ Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k =>
          (∏ k, x ⟨k, j k⟩) / ∏ k, x ⟨k, c k⟩), ∃ q : ℤ, b = q := by
        intro b hb
        have := Algebra.adjoin_mono h1 hb
        rw [Algebra.adjoin_singleton_one, Algebra.mem_bot] at this
        obtain ⟨q, rfl⟩ := this
        exact ⟨q, by simp⟩
      obtain ⟨q1, rfl⟩ := hbot g hg
      obtain ⟨q2, rfl⟩ := hbot h hh
      exact ⟨(q1 : ℚ) / q2, by rw [e]; simp⟩
    have hsub : Subsingleton (KaehlerDifferential ℚ Ω) := by
      have htop := KaehlerDifferential.span_range_derivation ℚ Ω
      refine subsingleton_of_forall_eq 0 fun w => ?_
      have hw : w ∈ (⊤ : Submodule Ω (KaehlerDifferential ℚ Ω)) := trivial
      rw [← htop] at hw
      have hle : Submodule.span Ω (Set.range (KaehlerDifferential.D ℚ Ω)) ≤ ⊥ := by
        rw [Submodule.span_le]
        rintro _ ⟨b, rfl⟩
        obtain ⟨q, rfl⟩ := hall b
        exact (KaehlerDifferential.D ℚ Ω).map_algebraMap q
      simpa using hle hw
    have := Module.finrank_zero_of_subsingleton (R := Ω) (M := KaehlerDifferential ℚ Ω)
    omega

  have : Algebra.EssFiniteType S Ω := .of_isLocalization Ω (nonZeroDivisors S)
  have : Algebra.EssFiniteType ℚ Ω := .comp ℚ S Ω
  have hfd : Module.Finite Ω (KaehlerDifferential ℚ Ω) := Module.finite_of_finrank_pos (by omega)
  have htr : Algebra.trdeg ℚ Ω = n := by
    rw [← GlobalTheory.rank_kaehler_eq_trdeg, ← Module.finrank_eq_rank, hfin]
  have htr' : Algebra.trdeg ℤ Ω = n := (PositivityTheory.Xgp.c_bm_exists_arith.trdeg_int_eq_rat Ω).trans htr
  exact (GlobalTheory.T.birational_of_transcendence_degree X Ω ξ K J x n T htr').2
