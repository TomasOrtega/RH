import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsLatticeFamily
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import Development.WeilBound.CoreStatements.HodgeTatePoints.HcptgenRing

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.ChartNoethFrac

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing div_mem_chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

/- English proof (translation)
Establish `hfg : (chartRing O y c).FG` using `⟨(Set.finite_range _).toFinset, by rw [Set.Finite.coe_toFinset]; rfl⟩`. Establish `: Algebra.FiniteType O (chartRing O y c)` using `(Subalgebra.fg_iff_finiteType _).1 hfg`. Conclude with `Algebra.FiniteType.isNoetherianRing O _`.
-/
theorem isNoetherianRing_chartRing {O Ω σ : Type} [CommRing O] [IsNoetherianRing O] [Field Ω] [Algebra O Ω]
    [Finite σ] (y : σ → Ω) (c : σ) : IsNoetherianRing (chartRing O y c) := by
  have hfg : (chartRing O y c).FG := ⟨(Set.finite_range _).toFinset, by rw [Set.Finite.coe_toFinset]; rfl⟩
  have : Algebra.FiniteType O (chartRing O y c) := (Subalgebra.fg_iff_finiteType _).1 hfg
  exact Algebra.FiniteType.isNoetherianRing O _

variable {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type}

/- English proof (translation)
Establish `hr : ∀ (k : K) (i : ι k), x ⟨k, i⟩ / x ⟨k, c k⟩ ∈ chartRing O (mseg x) c` using `fun k i => by`. Rewrite using `[PositivityTheory.HtPt.Hcptgen.ratio_eq x c hc k i]`. Conclude with `div_mem_chartRing _ _ _`. Use `(Subfield.closure_le).2 ?_` and prove the remaining obligations. Introduce and unpack `_ (⟨r, rfl⟩ | ⟨⟨k, i, j⟩, rfl⟩)`.

Conclude with `Subfield.subset_closure ((chartRing O (mseg x) c).algebraMap_mem r)`. Establish `hk : x ⟨k, c k⟩ ≠ 0` using `Finset.prod_ne_zero_iff.1 hc k (Finset.mem_univ k)`. Establish `e : x ⟨k, i⟩ / x ⟨k, j⟩ = (x ⟨k, i⟩ / x ⟨k, c k⟩) / (x ⟨k, j⟩ / x ⟨k, c k⟩)` using `(div_div_div_cancel_right₀ hk _ _).symm`. Use `show x ⟨k, i⟩ / x ⟨k, j⟩ ∈ Subfield.closure (chartRing O (mseg x) c : Set Ω)`. Rewrite using `[e]`.

Conclude with `div_mem (Subfield.subset_closure (hr k i)) (Subfield.subset_closure (hr k j))`.
-/
theorem fnField_le_closure [DecidableEq K] [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (c : ∀ k, ι k)
    (hc : mseg x c ≠ 0) :
    fnField O x ≤ Subfield.closure (chartRing O (mseg x) c : Set Ω) := by
  have hr : ∀ (k : K) (i : ι k), x ⟨k, i⟩ / x ⟨k, c k⟩ ∈ chartRing O (mseg x) c := fun k i => by
    rw [PositivityTheory.HtPt.Hcptgen.ratio_eq x c hc k i]
    exact div_mem_chartRing _ _ _
  refine (Subfield.closure_le).2 ?_
  rintro _ (⟨r, rfl⟩ | ⟨⟨k, i, j⟩, rfl⟩)
  · exact Subfield.subset_closure ((chartRing O (mseg x) c).algebraMap_mem r)
  · have hk : x ⟨k, c k⟩ ≠ 0 := Finset.prod_ne_zero_iff.1 hc k (Finset.mem_univ k)
    have e : x ⟨k, i⟩ / x ⟨k, j⟩ = (x ⟨k, i⟩ / x ⟨k, c k⟩) / (x ⟨k, j⟩ / x ⟨k, c k⟩) :=
      (div_div_div_cancel_right₀ hk _ _).symm
    show x ⟨k, i⟩ / x ⟨k, j⟩ ∈ Subfield.closure (chartRing O (mseg x) c : Set Ω)
    rw [e]
    exact div_mem (Subfield.subset_closure (hr k i)) (Subfield.subset_closure (hr k j))

/- English proof (translation)
Use `IsFractionRing.of_field A Ω fun z => ?_` and prove the remaining obligations. Establish `hz : z ∈ Subfield.closure (A : Set Ω)` using `h ▸ Subfield.mem_top z`. Take `⟨a, ha, b, hb, rfl⟩` from `Subfield.mem_closure_iff.1 hz`. Establish `hs : Subring.closure (A : Set Ω) = A.toSubring`. Use `Subring.closure_eq A.toSubring` as an intermediate fact.

Simplify using `using this`. Rewrite `ha`, `hb` using `[hs]`. Conclude with `⟨⟨a, ha⟩, ⟨b, hb⟩, rfl⟩`.
-/
theorem isFractionRing_of_closure_eq_top (A : Subalgebra O Ω)
    (h : Subfield.closure (A : Set Ω) = ⊤) : IsFractionRing A Ω := by
  refine IsFractionRing.of_field A Ω fun z => ?_
  have hz : z ∈ Subfield.closure (A : Set Ω) := h ▸ Subfield.mem_top z
  obtain ⟨a, ha, b, hb, rfl⟩ := Subfield.mem_closure_iff.1 hz
  have hs : Subring.closure (A : Set Ω) = A.toSubring := by
    have := Subring.closure_eq A.toSubring
    simpa using this
  rw [hs] at ha hb
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl⟩

variable {K' : Type} [Fintype K'] {ι' : K' → Type}

/- English proof (translation)
Unfold `mseg`. Rewrite using `[Fintype.prod_sum_type]`. Both sides reduce to the same expression.
-/
theorem mseg_joinCoord [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    mseg (joinCoord x z) s = mseg x (restrictChart s) * mseg z (fun k => s (.inr k)) := by
  unfold mseg
  rw [Fintype.prod_sum_type]
  rfl

def comb (t : ∀ k, ι k) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) : ∀ k : K ⊕ K', Sum.elim ι ι' k
  | .inl k => t k
  | .inr k => s (.inr k)

omit [Fintype K] [Fintype K'] in

/- English proof (translation)
Use `Subfield.closure_mono (Set.union_subset_union_right _ ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨k, i, j⟩, rfl⟩`. Conclude with `⟨⟨.inl k, i, j⟩, rfl⟩`.
-/
theorem fnField_le_join (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) :
    fnField O x ≤ fnField O (joinCoord x z) := by
  refine Subfield.closure_mono (Set.union_subset_union_right _ ?_)
  rintro _ ⟨⟨k, i, j⟩, rfl⟩
  exact ⟨⟨.inl k, i, j⟩, rfl⟩

/- English proof (translation)
Establish `hw : mseg z (fun k => s (.inr k)) ≠ 0`. Rewrite `hs` using `[mseg_joinCoord]`. Conclude with `right_ne_zero_of_mul hs`. Use `Algebra.adjoin_le ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨t, rfl⟩`.

Establish `h : mseg x t / mseg x (restrictChart s) = mseg (joinCoord x z) (comb t s) / mseg (joinCoord x z) s`. Rewrite using `[mseg_joinCoord x z (comb t s), mseg_joinCoord x z s]`. Conclude with `(mul_div_mul_right _ _ hw).symm`. Use `show mseg x t / mseg x (restrictChart s) ∈ chartRing O (mseg (joinCoord x z)) s`. Rewrite using `[h]`.

Conclude with `div_mem_chartRing _ _ _`.
-/
theorem chartRing_le_join [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) (hs : mseg (joinCoord x z) s ≠ 0) :
    chartRing O (mseg x) (restrictChart s) ≤ chartRing O (mseg (joinCoord x z)) s := by
  have hw : mseg z (fun k => s (.inr k)) ≠ 0 := by
    rw [mseg_joinCoord] at hs
    exact right_ne_zero_of_mul hs
  refine Algebra.adjoin_le ?_
  rintro _ ⟨t, rfl⟩
  have h : mseg x t / mseg x (restrictChart s) =
      mseg (joinCoord x z) (comb t s) / mseg (joinCoord x z) s := by
    rw [mseg_joinCoord x z (comb t s), mseg_joinCoord x z s]
    exact (mul_div_mul_right _ _ hw).symm
  show mseg x t / mseg x (restrictChart s) ∈ chartRing O (mseg (joinCoord x z)) s
  rw [h]
  exact div_mem_chartRing _ _ _

/- English proof (translation)
Introduce `O _ _ _ Ω _ _ K _ _ ι _ x`. Use `⟨fun c => isNoetherianRing_chartRing _ c, fun htop c hc => ?_, fun K' _ _ ι' _ z => ⟨fun htop => top_le_iff.1 (htop ▸ fnField_le_join x z), fun c hc => ⟨?_, chartRing_le_join x z c hc⟩⟩⟩` and prove the remaining obligations. Conclude with `isFractionRing_of_closure_eq_top _ (top_le_iff.1 (htop ▸ fnField_le_closure x c hc))`. Rewrite `hc` using `[mseg_joinCoord]`. Conclude with `left_ne_zero_of_mul hc`.
-/
theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω), (∀ c, IsNoetherianRing (chartRing O (mseg x) c)) ∧ (fnField O x = ⊤ → ∀ c, mseg x c ≠ 0 → IsFractionRing (chartRing O (mseg x) c) Ω) ∧ ∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω), (fnField O x = ⊤ → fnField O (joinCoord x z) = ⊤) ∧ ∀ c, mseg (joinCoord x z) c ≠ 0 → mseg x (restrictChart c) ≠ 0 ∧ (chartRing O (mseg x) (restrictChart c)) ≤ (chartRing O (mseg (joinCoord x z)) c) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x
  refine ⟨fun c => isNoetherianRing_chartRing _ c, fun htop c hc => ?_, fun K' _ _ ι' _ z =>
    ⟨fun htop => top_le_iff.1 (htop ▸ fnField_le_join x z), fun c hc => ⟨?_, chartRing_le_join x z c hc⟩⟩⟩
  · exact isFractionRing_of_closure_eq_top _ (top_le_iff.1 (htop ▸ fnField_le_closure x c hc))
  · rw [mseg_joinCoord] at hc
    exact left_ne_zero_of_mul hc

end GlobalTheory.CompanionTheory.Ar.Num.ChartNoethFrac
