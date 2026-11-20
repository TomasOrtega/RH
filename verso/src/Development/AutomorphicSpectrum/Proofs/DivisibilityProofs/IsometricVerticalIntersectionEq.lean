import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Cartier
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LogIntegralCongrSmulStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FiniteVerticalRecursionStatement
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num.Link

/- English proof (translation)
Distinguish the cases in `hc : W.IsPrime ∧ P ≤ W ∧ IsRelevant W`. Take `⟨u, v, hu, hv, huv⟩` from `h W hc.1 hc.2.1 hc.2.2 (hW hc.1)`. Conclude with `divCycle_eq_of_mul_sub_mem hu hv huv`. Establish `h0 : ∀ s : MRing ι ℤ, divCycle P s W = 0` using `fun s => by`. Assume the negation of the conclusion as `hne`.

Conclude with `hc (le_and_isRelevant_of_divCycle_ne_zero hne)`. Rewrite using `[h0, h0]`.
-/
theorem divCycle_eq_off {K : Type} {ι : K → Type} {P : Ideal (MRing ι ℤ)} {f g : MRing ι ℤ} {S : Finset Nat.Primes}
    (h : ∀ W : Ideal (MvPolynomial (Σ k, ι k) ℤ), W.IsPrime → P ≤ W → IsRelevant W →
      (∀ p ∈ S, (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∉ W) →
      ∃ u v : MvPolynomial (Σ k, ι k) ℤ, u ∉ W ∧ v ∉ W ∧ u * f - v * g ∈ P)
    {W : Ideal (MRing ι ℤ)}
    (hW : W.IsPrime → ∀ p ∈ S, (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∉ W) :
    divCycle P f W = divCycle P g W := by
  by_cases hc : W.IsPrime ∧ P ≤ W ∧ IsRelevant W
  · obtain ⟨u, v, hu, hv, huv⟩ := h W hc.1 hc.2.1 hc.2.2 (hW hc.1)
    exact divCycle_eq_of_mul_sub_mem hu hv huv
  · have h0 : ∀ s : MRing ι ℤ, divCycle P s W = 0 := fun s => by
      by_contra hne
      exact hc (le_and_isRelevant_of_divCycle_ne_zero hne)
    rw [h0, h0]

/- English proof (translation)
Introduce `hq`. Establish `hcop : IsCoprime ((p : ℕ) : ℤ) ((q : ℕ) : ℤ)`. Rewrite using `[Nat.isCoprime_iff_coprime]`. Conclude with `(Nat.coprime_primes p.2 q.2).2 fun h => hpq (Subtype.ext h)`. Take `⟨a, b, hab⟩` from `hcop`.

Apply `hW.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one]`. Establish `e : (1 : MvPolynomial (Σ k, ι k) ℤ) = C a * C ((p : ℕ) : ℤ) + C b * C ((q : ℕ) : ℤ)`. Rewrite using `[← C_mul, ← C_mul, ← C_add, hab, C_1]`. Rewrite using `[e]`.

Conclude with `W.add_mem (W.mul_mem_left _ hp) (W.mul_mem_left _ hq)`.
-/
theorem not_mem_of_mem {K : Type} {ι : K → Type} {W : Ideal (MRing ι ℤ)} (hW : W.IsPrime) {p q : Nat.Primes}
    (hpq : p ≠ q) (hp : (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∈ W) :
    (C ((q : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∉ W := by
  intro hq
  have hcop : IsCoprime ((p : ℕ) : ℤ) ((q : ℕ) : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact (Nat.coprime_primes p.2 q.2).2 fun h => hpq (Subtype.ext h)
  obtain ⟨a, b, hab⟩ := hcop
  apply hW.ne_top
  rw [Ideal.eq_top_iff_one]
  have e : (1 : MvPolynomial (Σ k, ι k) ℤ) =
      C a * C ((p : ℕ) : ℤ) + C b * C ((q : ℕ) : ℤ) := by
    rw [← C_mul, ← C_mul, ← C_add, hab, C_1]
  rw [e]
  exact W.add_mem (W.mul_mem_left _ hp) (W.mul_mem_left _ hq)

/- English proof (translation)
Introduce `hp`. Establish `h1 : ((p : ℕ) : ℤ) ∈ W.comap (C : ℤ →+* MvPolynomial (Σ k, ι k) ℤ)` using `hp`. Rewrite `h1` using `[show W.comap (C : ℤ →+* MvPolynomial (Σ k, ι k) ℤ) = ⊥ from hW, Ideal.mem_bot]`. Conclude with `p.2.ne_zero (by exact_mod_cast h1)`.
-/
theorem not_mem_of_horizontal {K : Type} {ι : K → Type} {W : Ideal (MRing ι ℤ)} (hW : IsHorizontal W)
    (p : Nat.Primes) : (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∉ W := by
  intro hp
  have h1 : ((p : ℕ) : ℤ) ∈ W.comap (C : ℤ →+* MvPolynomial (Σ k, ι k) ℤ) := hp
  rw [show W.comap (C : ℤ →+* MvPolynomial (Σ k, ι k) ℤ) = ⊥ from hW, Ideal.mem_bot] at h1
  exact p.2.ne_zero (by exact_mod_cast h1)

/- English proof (translation)
Introduce `K _ _ ι _ P D hP I hI S T hT A A' hA hA' hiso L hL`. Take `⟨⟨bf, bg, hf, hg, hdeg⟩, hfP, hgP, hunit⟩` from `hT ()`. Take `⟨hAa, hA'a, hnorm⟩` from `hiso ()`. Set `B : HermLine ι` to `(ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric bf).tensor A.inv`. Establish `hB : IsSmoothHerm B` using `ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor (ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_sqMetric bf) (ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_inv hA)`.

Establish `hAB : IsSmoothHerm (A.tensor B)` using `ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor hA hB`. Establish `hAB' : IsSmoothHerm (A'.tensor B)` using `ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor hA' hB`. Establish `dF : ∀ k, (A.tensor B).a k = bf k` using `fun k => by`. Simplify using `[B, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.inv, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric]`. Establish `dG : ∀ k, (A'.tensor B).a k = bg k` using `fun k => by`.

Establish `h1` using `congrFun hdeg k`. Establish `h2` using `congrFun hAa k`. Establish `h3` using `congrFun hA'a k`. Simplify using `only [Pi.sub_apply] at h1`. Simplify using `only [B, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.inv, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric, Pi.add_apply, Pi.neg_apply]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `e1` using `hI.2.1 P D L A B hP hL hA hB`. Establish `e2` using `hI.2.1 P D L A' B hP hL hA' hB`. Establish `r1` using `hI.2.2 P D L (A.tensor B) (T.f ()) bf hP hL hAB dF ((GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_iff _ _).1 hf) hfP`. Establish `r2` using `hI.2.2 P D L (A'.tensor B) (T.g ()) bg hP hL hAB' dG ((GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_iff _ _).1 hg) hgP`.

Take `⟨fin1, s1⟩` from `GlobalTheory.T.finite_vertical_recursion K ι P D hP I bf (T.f ()) hf hfP L (A.tensor B)`. Take `⟨fin2, s2⟩` from `GlobalTheory.T.finite_vertical_recursion K ι P D hP I bg (T.g ()) hg hgP L (A'.tensor B)`. Establish `hor : (∑ᶠ W, (divCycle P (T.f ()) W : ℝ) * Set.indicator {W | IsHorizontal W} (fun W => I W D L) W) = ∑ᶠ W, (divCycle P (T.g ()) W : ℝ) * Set.indicator {W | IsHorizontal W} (fun W => I W D L) W`. Use `finsum_congr fun W => ?_` and prove the remaining obligations. Distinguish the cases in `hW : IsHorizontal W`.

Rewrite using `[divCycle_eq_off hunit (fun _ p _ => not_mem_of_horizontal hW p)]`. Establish `: W ∉ {W | IsHorizontal W}` using `hW`. Simplify using `[Set.indicator_of_notMem this]`. Establish `ar : arInt P (T.f ()) (A.tensor B) L = arInt P (T.g ()) (A'.tensor B) L`. Use `(GlobalTheory.T.log_integral_congr_smul K ι P D _).1 _ _ fun z hz => ?_` and prove the remaining obligations.

Establish `h1` using `hnorm z hz`. Establish `pA` using `A.pos z hz.1`. Establish `pA'` using `A'.pos z hz.1`. Establish `pB` using `B.pos z hz.1`. Simplify using `only [ReciprocityTheory.ChartRestriction.G.Geo.logNorm, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor]`.

Use `congr 1`. Rewrite using `[div_eq_div_iff (by positivity) (by positivity)]`. Take the linear combination `(B.h z) * h1`. Establish `hv : ∀ p : Nat.Primes, p ∉ S → vertAt p P (T.f ()) (List.ofFn fun j => (L j).a) = vertAt p P (T.g ()) (List.ofFn fun j => (L j).a)`. Introduce `p hp`.

Unfold `vertAt cycEval`. Use `finsum_congr fun W => ?_` and prove the remaining obligations. Distinguish the cases in `hpW : (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∈ W`. Rewrite using `[divCycle_eq_off hunit (fun hWp q hq => not_mem_of_mem hWp (fun h : p = q => hp (by rw [h]; exact hq)) hpW)]`. Simplify using `only [if_neg hpW, mul_zero]`.

Establish `vert : (∑ᶠ p : Nat.Primes, Real.log (p : ℕ) * (vertAt p P (T.f ()) (List.ofFn fun j => (L j).a) : ℝ)) - (∑ᶠ p : Nat.Primes, Real.log (p : ℕ) * (vertAt p P (T.g ()) (List.ofFn fun j => (L j).a) : ℝ)) = ∑ p ∈ S, Real.log (p : ℕ) * ((vertAt p P (T.f ()) (List.ofFn fun j => (L j).a) …`. Establish `hF : (Function.support fun p : Nat.Primes => Real.log (p : ℕ) * (vertAt p P (T.f ()) (List.ofFn fun j => (L j).a) : ℝ)).Finite` using `fin1.subset fun p hp h0 => hp (by simp [h0])`. Establish `hG : (Function.support fun p : Nat.Primes => Real.log (p : ℕ) * (vertAt p P (T.g ()) (List.ofFn fun j => (L j).a) : ℝ)).Finite` using `fin2.subset fun p hp h0 => hp (by simp [h0])`. Rewrite using `[← finsum_sub_distrib hF hG, finsum_eq_sum_of_support_subset (s := S) _ fun p hp => ?_]`. Conclude with `Finset.sum_congr rfl fun p _ => by ring`.

Assume the negation of the conclusion as `hpS`. Conclude with `hp (by simp [hv p (by simpa using hpS)])`. Establish `e3 : I P (D + 1) (Fin.snoc L A) - I P (D + 1) (Fin.snoc L A') = I P (D + 1) (Fin.snoc L (A.tensor B)) - I P (D + 1) (Fin.snoc L (A'.tensor B))`. Rewrite using `[e1, e2]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e3, r1, r2, s1, s2, hor, ar, ← vert]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem change_line : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ (I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I → ∀ (S : Finset Nat.Primes) (T : LocPair ι ℤ Unit), T.IsVertOff P S → ∀ A A' : HermLine ι, IsSmoothHerm A → IsSmoothHerm A' → T.IsIsometric P (fun _ => A) (fun _ => A') → ∀ L : Fin D → HermLine ι, (∀ j, IsSmoothHerm (L j)) → I P (D + 1) (Fin.snoc L A) - I P (D + 1) (Fin.snoc L A') = ∑ p ∈ S, Real.log (p : ℕ) * ((vertAt p P (T.f ()) (List.ofFn fun j => (L j).a) : ℝ) - (vertAt p P (T.g ()) (List.ofFn fun j => (L j).a) : ℝ)) := by
  intro K _ _ ι _ P D hP I hI S T hT A A' hA hA' hiso L hL
  obtain ⟨⟨bf, bg, hf, hg, hdeg⟩, hfP, hgP, hunit⟩ := hT ()
  obtain ⟨hAa, hA'a, hnorm⟩ := hiso ()
  let B : HermLine ι := (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric bf).tensor A.inv
  have hB : IsSmoothHerm B := ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor
    (ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_sqMetric bf) (ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_inv hA)
  have hAB : IsSmoothHerm (A.tensor B) := ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor hA hB
  have hAB' : IsSmoothHerm (A'.tensor B) := ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor hA' hB
  have dF : ∀ k, (A.tensor B).a k = bf k := fun k => by
    simp [B, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.inv,
      ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric]
  have dG : ∀ k, (A'.tensor B).a k = bg k := fun k => by
    have h1 := congrFun hdeg k
    have h2 := congrFun hAa k
    have h3 := congrFun hA'a k
    simp only [Pi.sub_apply] at h1
    simp only [B, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.inv,
      ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric, Pi.add_apply, Pi.neg_apply]
    linarith
  have e1 := hI.2.1 P D L A B hP hL hA hB
  have e2 := hI.2.1 P D L A' B hP hL hA' hB
  have r1 := hI.2.2 P D L (A.tensor B) (T.f ()) bf hP hL hAB dF
    ((GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_iff _ _).1 hf) hfP
  have r2 := hI.2.2 P D L (A'.tensor B) (T.g ()) bg hP hL hAB' dG
    ((GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_iff _ _).1 hg) hgP
  obtain ⟨fin1, s1⟩ := GlobalTheory.T.finite_vertical_recursion K ι P D hP I bf (T.f ()) hf hfP L (A.tensor B)
  obtain ⟨fin2, s2⟩ := GlobalTheory.T.finite_vertical_recursion K ι P D hP I bg (T.g ()) hg hgP L (A'.tensor B)
  have hor : (∑ᶠ W, (divCycle P (T.f ()) W : ℝ) * Set.indicator {W | IsHorizontal W} (fun W => I W D L) W) =
      ∑ᶠ W, (divCycle P (T.g ()) W : ℝ) * Set.indicator {W | IsHorizontal W} (fun W => I W D L) W := by
    refine finsum_congr fun W => ?_
    by_cases hW : IsHorizontal W
    · rw [divCycle_eq_off hunit (fun _ p _ => not_mem_of_horizontal hW p)]
    · have : W ∉ {W | IsHorizontal W} := hW
      simp [Set.indicator_of_notMem this]
  have ar : arInt P (T.f ()) (A.tensor B) L = arInt P (T.g ()) (A'.tensor B) L := by
    refine (GlobalTheory.T.log_integral_congr_smul K ι P D _).1 _ _ fun z hz => ?_
    have h1 := hnorm z hz
    have pA := A.pos z hz.1
    have pA' := A'.pos z hz.1
    have pB := B.pos z hz.1
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.logNorm, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor]
    congr 1
    rw [div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (B.h z) * h1
  have hv : ∀ p : Nat.Primes, p ∉ S → vertAt p P (T.f ()) (List.ofFn fun j => (L j).a) =
      vertAt p P (T.g ()) (List.ofFn fun j => (L j).a) := by
    intro p hp
    unfold vertAt cycEval
    refine finsum_congr fun W => ?_
    by_cases hpW : (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∈ W
    · rw [divCycle_eq_off hunit (fun hWp q hq => not_mem_of_mem hWp
        (fun h : p = q => hp (by rw [h]; exact hq)) hpW)]
    · simp only [if_neg hpW, mul_zero]
  have vert : (∑ᶠ p : Nat.Primes, Real.log (p : ℕ) * (vertAt p P (T.f ()) (List.ofFn fun j => (L j).a) : ℝ)) -
      (∑ᶠ p : Nat.Primes, Real.log (p : ℕ) * (vertAt p P (T.g ()) (List.ofFn fun j => (L j).a) : ℝ)) =
      ∑ p ∈ S, Real.log (p : ℕ) * ((vertAt p P (T.f ()) (List.ofFn fun j => (L j).a) : ℝ) -
        (vertAt p P (T.g ()) (List.ofFn fun j => (L j).a) : ℝ)) := by
    have hF : (Function.support fun p : Nat.Primes =>
        Real.log (p : ℕ) * (vertAt p P (T.f ()) (List.ofFn fun j => (L j).a) : ℝ)).Finite :=
      fin1.subset fun p hp h0 => hp (by simp [h0])
    have hG : (Function.support fun p : Nat.Primes =>
        Real.log (p : ℕ) * (vertAt p P (T.g ()) (List.ofFn fun j => (L j).a) : ℝ)).Finite :=
      fin2.subset fun p hp h0 => hp (by simp [h0])
    rw [← finsum_sub_distrib hF hG,
      finsum_eq_sum_of_support_subset (s := S) _ fun p hp => ?_]
    · exact Finset.sum_congr rfl fun p _ => by ring
    · by_contra hpS
      exact hp (by simp [hv p (by simpa using hpS)])
  have e3 : I P (D + 1) (Fin.snoc L A) - I P (D + 1) (Fin.snoc L A') =
      I P (D + 1) (Fin.snoc L (A.tensor B)) - I P (D + 1) (Fin.snoc L (A'.tensor B)) := by
    rw [e1, e2]; ring
  rw [e3, r1, r2, s1, s2, hor, ar, ← vert]
  ring

end GlobalTheory.CompanionTheory.Ar.Num.Link
