import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFrameVec
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.FlagTri

/- English proof (translation)
Introduce `Ω _ L _ _ r b b₀ Tm hb hflag hT`. Establish `hspan : Submodule.span Ω (Set.range b₀) = Submodule.span Ω (Set.range b)`. Establish `h` using `hflag r`. Unfold `flagStep at h`. Establish `e1 : b₀ '' {k : Fin r | (k : ℕ) < r} = Set.range b₀`.

Rewrite using `[← Set.image_univ]`. Use `congr 1`. Use extensionality with `k`. Simplify using `[k.isLt]`. Establish `e2 : b '' {k : Fin r | (k : ℕ) < r} = Set.range b`.

Rewrite using `[← Set.image_univ]`. Use `congr 1`. Use extensionality with `k`. Simplify using `[k.isLt]`. Rewrite `h` using `[e1, e2]`.

Conclude with `h.symm`. Establish `hb₀ : LinearIndependent Ω b₀`. Rewrite using `[linearIndependent_iff_card_eq_finrank_span]`. Use `show Fintype.card (Fin r) = Module.finrank Ω (Submodule.span Ω (Set.range b₀))`. Rewrite using `[hspan, finrank_span_eq_card hb]`.

Use `⟨hb₀, fun i j hij => ?_⟩` and prove the remaining obligations. Establish `hmem : b i ∈ Submodule.span Ω (b₀ '' {k : Fin r | (k : ℕ) < (i : ℕ) + 1})`. Establish `h` using `hflag ((i : ℕ) + 1)`. Unfold `flagStep at h`. Rewrite using `[← h]`.

Conclude with `Submodule.subset_span ⟨i, by simp, rfl⟩`. Take `⟨c, hc, hcb⟩` from `(Finsupp.mem_span_image_iff_linearCombination Ω).mp hmem`. Establish `hsum : ∑ k, (c k - Tm i k) • b₀ k = 0`. Simplify using `only [sub_smul, Finset.sum_sub_distrib]`. Rewrite using `[← hT i, ← hcb, Finsupp.linearCombination_apply, Finsupp.sum_fintype]`.

Simplify using the standard rewrite rules. Introduce `k`. Simplify using the standard rewrite rules. Establish `h0 : c j - Tm i j = 0` using `(Fintype.linearIndependent_iff.mp hb₀) (fun k => c k - Tm i k) hsum j`. Establish `hcj : c j = 0`.

Assume the negation of the conclusion as `hne`. Establish `hsupp` using `(Finsupp.mem_supported Ω c).mp hc`. Establish `hj : j ∈ ({k : Fin r | (k : ℕ) < (i : ℕ) + 1} : Set (Fin r))` using `hsupp (Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr hne))`. Establish `hj' : (j : ℕ) < (i : ℕ) + 1` using `hj`. Establish `hij' : (i : ℕ) < (j : ℕ)` using `hij`.

Use linear arithmetic over natural numbers and integers. Rewrite `h0` using `[hcj, zero_sub, neg_eq_zero]`. Conclude with `h0`.
-/
theorem independent_and_triangular : ∀ (Ω : Type) [Field Ω] (L : Type) [AddCommGroup L] [Module Ω L] (r : ℕ) (b b₀ : Fin r → L) (Tm : Matrix (Fin r) (Fin r) Ω), LinearIndependent Ω b → (∀ i : ℕ, flagStep Ω b i = flagStep Ω b₀ i) → (∀ i, b i = ∑ j, Tm i j • b₀ j) → LinearIndependent Ω b₀ ∧ ∀ i j, i < j → Tm i j = 0 := by
  intro Ω _ L _ _ r b b₀ Tm hb hflag hT
  have hspan : Submodule.span Ω (Set.range b₀) = Submodule.span Ω (Set.range b) := by
    have h := hflag r
    unfold flagStep at h
    have e1 : b₀ '' {k : Fin r | (k : ℕ) < r} = Set.range b₀ := by
      rw [← Set.image_univ]
      congr 1
      ext k
      simp [k.isLt]
    have e2 : b '' {k : Fin r | (k : ℕ) < r} = Set.range b := by
      rw [← Set.image_univ]
      congr 1
      ext k
      simp [k.isLt]
    rw [e1, e2] at h
    exact h.symm
  have hb₀ : LinearIndependent Ω b₀ := by
    rw [linearIndependent_iff_card_eq_finrank_span]
    show Fintype.card (Fin r) = Module.finrank Ω (Submodule.span Ω (Set.range b₀))
    rw [hspan, finrank_span_eq_card hb]
  refine ⟨hb₀, fun i j hij => ?_⟩
  have hmem : b i ∈ Submodule.span Ω (b₀ '' {k : Fin r | (k : ℕ) < (i : ℕ) + 1}) := by
    have h := hflag ((i : ℕ) + 1)
    unfold flagStep at h
    rw [← h]
    exact Submodule.subset_span ⟨i, by simp, rfl⟩
  obtain ⟨c, hc, hcb⟩ := (Finsupp.mem_span_image_iff_linearCombination Ω).mp hmem
  have hsum : ∑ k, (c k - Tm i k) • b₀ k = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [← hT i, ← hcb, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    · simp
    · intro k
      simp
  have h0 : c j - Tm i j = 0 := (Fintype.linearIndependent_iff.mp hb₀) (fun k => c k - Tm i k) hsum j
  have hcj : c j = 0 := by
    by_contra hne
    have hsupp := (Finsupp.mem_supported Ω c).mp hc
    have hj : j ∈ ({k : Fin r | (k : ℕ) < (i : ℕ) + 1} : Set (Fin r)) :=
      hsupp (Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr hne))
    have hj' : (j : ℕ) < (i : ℕ) + 1 := hj
    have hij' : (i : ℕ) < (j : ℕ) := hij
    omega
  rw [hcj, zero_sub, neg_eq_zero] at h0
  exact h0

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.FlagTri
