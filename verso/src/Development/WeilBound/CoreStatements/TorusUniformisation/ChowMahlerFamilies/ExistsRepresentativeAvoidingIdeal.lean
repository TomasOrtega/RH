import Mathlib
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.RepresentativeAvoidance

section General

variable {σ M R : Type*} [CommRing R] [AddCommGroup M] (w : σ → M)

/- English proof (translation)
Proceed by induction. Treat this case separately. Establish an intermediate fact. Establish an intermediate fact. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Treat this case separately.
-/
theorem comp_mul (u f : MvPolynomial σ R) (d n : M) (hf : IsWeightedHomogeneous w f d) :
    weightedHomogeneousComponent w (n + d) (u * f) = weightedHomogeneousComponent w n u * f := by
  classical
  induction u using MvPolynomial.induction_on' with
  | monomial s a =>
    have h1 : IsWeightedHomogeneous w (monomial s a : MvPolynomial σ R) (Finsupp.weight w s) :=
      isWeightedHomogeneous_monomial w s a rfl
    have h2 := h1.mul hf
    by_cases hn : n = Finsupp.weight w s
    · subst hn
      rw [h1.weightedHomogeneousComponent_same, h2.weightedHomogeneousComponent_same]
    · rw [h1.weightedHomogeneousComponent_ne n hn,
        h2.weightedHomogeneousComponent_ne (n + d) (fun h => hn (add_right_cancel h)), zero_mul]
  | add p q hp hq => rw [add_mul, map_add, map_add, hp, hq, add_mul]

/- English proof (translation)
Establish an intermediate fact. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Treat this case separately. Simplify using the standard rewrite rules.

Treat this case separately. Rewrite the conclusion using the stated equalities. Treat this case separately. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

A detailed English derivation is pending.
-/
theorem comp_mem_span (S : Set (MvPolynomial σ R))
    (hS : ∀ f ∈ S, ∃ d, IsWeightedHomogeneous w f d) (x : MvPolynomial σ R)
    (hx : x ∈ Ideal.span S) (n : M) : weightedHomogeneousComponent w n x ∈ Ideal.span S := by
  have key : ∀ r n, weightedHomogeneousComponent w n (r * x) ∈ Ideal.span S := by
    induction hx using Submodule.span_induction with
    | mem x h =>
      intro r n
      obtain ⟨d, hd⟩ := hS x h
      have := comp_mul w r x d (n - d) hd
      rw [sub_add_cancel] at this
      rw [this]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span h)
    | zero => intro r n; simp
    | add x y _ _ hx hy => intro r n; rw [mul_add, map_add]; exact add_mem (hx r n) (hy r n)
    | smul a x _ hx => intro r n; rw [smul_eq_mul, ← mul_assoc]; exact hx _ n
  simpa using key 1 n

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_comp_notMem (W : Ideal (MvPolynomial σ R)) (u : MvPolynomial σ R) (hu : u ∉ W) :
    ∃ n, weightedHomogeneousComponent w n u ∉ W := by
  by_contra h
  push Not at h
  apply hu
  rw [← sum_weightedHomogeneousComponent (w := w) u,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp u)]
  exact W.sum_mem fun n _ => h n

end General

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

def wt (ι : K → Type) : (Σ k, ι k) → (K → ℤ) := fun p => Pi.single p.1 1

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem weight_wt (m : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (wt ι) m k = ((∑ i, m ⟨k, i⟩ : ℕ) : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma,
    Finset.sum_eq_single k]
  · simp [wt]
  · intro j _ hj
    simp [wt, Pi.single_eq_of_ne hj.symm]
  · simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.
-/
theorem wh_of_mh {f : MRing ι} {d : K → ℕ} (h : IsMultiHomog f d) :
    IsWeightedHomogeneous (wt ι) f (fun k => (d k : ℤ)) := by
  intro m hm
  funext k
  rw [weight_wt, h m (mem_support_iff.mpr hm) k]

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem mh_of_wh {f : MRing ι} {d : K → ℤ} (h : IsWeightedHomogeneous (wt ι) f d) (h0 : f ≠ 0) :
    ∃ e : K → ℕ, IsMultiHomog f e ∧ ∀ k, (e k : ℤ) = d k := by
  obtain ⟨m0, hm0⟩ := exists_coeff_ne_zero h0
  refine ⟨fun k => ∑ i, m0 ⟨k, i⟩, fun m hm k => ?_, fun k => ?_⟩
  · have h1 := congrFun ((h (mem_support_iff.mp hm)).trans (h hm0).symm) k
    rw [weight_wt, weight_wt] at h1
    exact_mod_cast h1
  · rw [← weight_wt, h hm0]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem exists_mono (W : Ideal (MRing ι)) (hW : W.IsPrime) (hr : IsRelevant W) (e : K → ℕ) :
    ∃ m : MRing ι, m ∉ W ∧ IsWeightedHomogeneous (wt ι) m (fun k => (e k : ℤ)) := by
  choose c hc using hr
  refine ⟨∏ k, X ⟨k, c k⟩ ^ e k, fun h => ?_, ?_⟩
  · obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hc k (hW.mem_of_pow_mem _ hk)
  · have := IsWeightedHomogeneous.prod (w := wt ι) Finset.univ
      (fun k => (X ⟨k, c k⟩ : MRing ι) ^ e k) (fun k => e k • wt ι ⟨k, c k⟩)
      (fun k _ => (isWeightedHomogeneous_X ℤ (wt ι) _).pow _)
    convert this using 1
    funext k
    simp [wt, Finset.sum_apply, Pi.single_apply]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws.

Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Consider separately whether the proposition holds or fails. Supply the required witnesses or components. Consider separately whether the proposition holds or fails. Supply the required witnesses or components. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion. Expand and normalize the polynomial expressions, which then agree.

A detailed English derivation is pending.
-/
theorem exists_pair (P W : Ideal (MRing ι)) (f g : MRing ι) (df dg : K → ℕ)
    (hP : IsMultiProjPrime P) (hW : IsMultiProjPrime W) (hPW : P ≤ W) (hf : IsMultiHomog f df)
    (hg : IsMultiHomog g dg) (hu : IsUnitSec P f g) :
    ∃ (U V : MRing ι) (c : K → ℤ), IsWeightedHomogeneous (wt ι) U c ∧
      IsWeightedHomogeneous (wt ι) V (c + ((fun k => (df k : ℤ)) - fun k => (dg k : ℤ))) ∧
      U ∉ W ∧ V ∉ W ∧ U * f - V * g ∈ P := by
  obtain ⟨u, v, hu, hv, huv⟩ := hu W hW.1 hPW hW.2.2
  set δ : K → ℤ := (fun k => (df k : ℤ)) - fun k => (dg k : ℤ) with hδ
  have hpair : ∀ a : K → ℤ, weightedHomogeneousComponent (wt ι) a u * f -
      weightedHomogeneousComponent (wt ι) (a + δ) v * g ∈ P := by
    intro a
    obtain ⟨S, hS, rfl⟩ := hP.2.1
    have := comp_mem_span (wt ι) S (fun x hx => (hS x hx).elim fun d hd => ⟨_, wh_of_mh hd⟩) _ huv
      (a + fun k => (df k : ℤ))
    rw [map_sub, comp_mul _ u f _ a (wh_of_mh hf)] at this
    rw [← comp_mul _ v g _ (a + δ) (wh_of_mh hg)]
    convert this using 4
    rw [hδ]; abel
  have hA : ∀ a, IsWeightedHomogeneous (wt ι) (weightedHomogeneousComponent (wt ι) a u) a :=
    fun a => weightedHomogeneousComponent_isWeightedHomogeneous a u
  have hB : ∀ a, IsWeightedHomogeneous (wt ι) (weightedHomogeneousComponent (wt ι) a v) a :=
    fun a => weightedHomogeneousComponent_isWeightedHomogeneous a v
  obtain ⟨a, ha⟩ := exists_comp_notMem (wt ι) W u hu
  obtain ⟨b, hb⟩ := exists_comp_notMem (wt ι) W v hv
  obtain ⟨a', rfl⟩ : ∃ a', b = a' + δ := ⟨b - δ, by abel⟩
  by_cases h1 : weightedHomogeneousComponent (wt ι) (a + δ) v ∈ W
  swap
  · exact ⟨_, _, a, hA a, hB _, ha, h1, hpair a⟩
  by_cases h2 : weightedHomogeneousComponent (wt ι) a' u ∈ W
  swap
  · exact ⟨_, _, a', hA a', hB _, h2, hb, hpair a'⟩
  obtain ⟨m, hm, hmd⟩ := exists_mono W hW.1 hW.2.2 (fun k => (a' k - a k).toNat)
  obtain ⟨m', hm', hmd'⟩ := exists_mono W hW.1 hW.2.2 (fun k => (a k - a' k).toNat)
  have he : (fun k => (((a k - a' k).toNat : ℕ) : ℤ)) + a' =
      (fun k => (((a' k - a k).toNat : ℕ) : ℤ)) + a := by
    funext k
    simp only [Pi.add_apply]
    omega
  refine ⟨m * weightedHomogeneousComponent (wt ι) a u + m' * weightedHomogeneousComponent (wt ι) a' u,
    m * weightedHomogeneousComponent (wt ι) (a + δ) v +
      m' * weightedHomogeneousComponent (wt ι) (a' + δ) v,
    (fun k => (((a' k - a k).toNat : ℕ) : ℤ)) + a, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hmd.mul (hA a)).add (he ▸ hmd'.mul (hA a'))
  · refine IsWeightedHomogeneous.add ?_ ?_
    · rw [add_assoc]; exact hmd.mul (hB _)
    · rw [← he, add_assoc]; exact hmd'.mul (hB _)
  · intro h
    rw [W.add_mem_iff_left (W.mul_mem_left _ h2)] at h
    exact (hW.1.mem_or_mem h).elim hm ha
  · intro h
    rw [W.add_mem_iff_right (W.mul_mem_left _ h1)] at h
    exact (hW.1.mem_or_mem h).elim hm' hb
  · convert add_mem (P.mul_mem_left m (hpair a)) (P.mul_mem_left m' (hpair a')) using 1
    ring

end PositivityTheory.Xgn.RepresentativeAvoidance

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Apply an available result and prove the equalities needed to match it to the conclusion. Expand and normalize the polynomial expressions, which then agree. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Apply an available result and prove the equalities needed to match it to the conclusion. Expand and normalize the polynomial expressions, which then agree.
-/
theorem PositivityTheory.Xgn.exists_representative_avoiding_ideal : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι)) (f g : MRing ι) (df dg : K → ℕ), IsMultiProjPrime P → IsMultiProjPrime W → P ≤ W → IsMultiHomog f df → IsMultiHomog g dg → g ∉ P → IsUnitSec P f g → ∃ (f' g' : MRing ι) (df' dg' : K → ℕ), IsMultiHomog f' df' ∧ IsMultiHomog g' dg' ∧ (∀ k, (df' k : ℤ) - dg' k = (df k : ℤ) - dg k) ∧ f' ∉ W ∧ g' ∉ W ∧ f' * g - g' * f ∈ P ∧ IsUnitSec P f' g' := by
  intro K _ ι _ P W f g df dg hP hW hPW hf hg hgP hu
  classical
  obtain ⟨U, V, c, hU, hV, hUW, hVW, hUV⟩ :=
    PositivityTheory.Xgn.RepresentativeAvoidance.exists_pair P W f g df dg hP hW hPW hf hg hu
  obtain ⟨eU, heU, hcU⟩ := PositivityTheory.Xgn.RepresentativeAvoidance.mh_of_wh hU
    (fun h => hUW (h ▸ W.zero_mem))
  obtain ⟨eV, heV, hcV⟩ := PositivityTheory.Xgn.RepresentativeAvoidance.mh_of_wh hV
    (fun h => hVW (h ▸ W.zero_mem))
  refine ⟨V, U, eV, eU, heV, heU, fun k => ?_, hVW, hUW, ?_, fun W' hW' hPW' hr => ?_⟩
  · rw [hcU, hcV]; simp
  · convert neg_mem hUV using 1
    ring
  · obtain ⟨u, v, hu', hv', huv⟩ := hu W' hW' hPW' hr
    refine ⟨u, v, hu', hv', (hP.1.mem_or_mem (x := g) ?_).resolve_left hgP⟩
    convert sub_mem (P.mul_mem_left U huv) (P.mul_mem_left u hUV) using 1
    ring
