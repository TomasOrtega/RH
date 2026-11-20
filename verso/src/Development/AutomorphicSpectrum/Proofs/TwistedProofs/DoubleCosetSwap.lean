import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

noncomputable section

open Formalism.UG GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertZeta

variable {G : Type} [Group G] {K : Subgroup G}

def cosetsIn (hK : IsCommensurated K) (g : G) : Finset (G ⧸ K) :=
  (P.finite_cosets_in_doset hK g).toFinset

/- English proof (translation)
Rewrite using `[cosetsIn, Set.Finite.mem_toFinset, DoubleCoset.mem_doubleCoset]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, b, h⟩`. Conclude with `⟨a, a.2, b, b.2, h⟩`. Introduce and unpack `⟨a, ha, b, hb, h⟩`.

Conclude with `⟨⟨a, ha⟩, ⟨b, hb⟩, h⟩`.
-/
theorem mem_cosetsIn {hK : IsCommensurated K} {g : G} {x : G ⧸ K} :
    x ∈ cosetsIn hK g ↔ x.out ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G) := by
  rw [cosetsIn, Set.Finite.mem_toFinset, DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨a, b, h⟩
    exact ⟨a, a.2, b, b.2, h⟩
  · rintro ⟨a, ha, b, hb, h⟩
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, h⟩

/- English proof (translation)
Unfold `hAct`. Rewrite using `[finsum_eq_sum_of_support_subset (s := cosetsIn hK g)]`. Use `Finset.sum_congr rfl fun x hx => ?_` and prove the remaining obligations. Establish `hm : x.out ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G)` using `mem_cosetsIn.mp hx`. Simplify using `[dosetInd, Set.indicator_apply, hm]`.

Introduce `x hx`. Rewrite `hx` using `[Function.mem_support]`. Rewrite using `[Finset.mem_coe, mem_cosetsIn]`. Assume the negation of the conclusion as `hm`. Apply `hx` to reduce the goal to its premises.

Simplify using `[dosetInd, Set.indicator_apply, hm]`.
-/
theorem hAct_dosetInd (hK : IsCommensurated K) (g : G) (f : G → ℂ) :
    hAct K (dosetInd ℂ K g) f 1 = ∑ x ∈ cosetsIn hK g, f x.out := by
  unfold hAct
  rw [finsum_eq_sum_of_support_subset (s := cosetsIn hK g)]
  · refine Finset.sum_congr rfl fun x hx => ?_
    have hm : x.out ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G) := mem_cosetsIn.mp hx
    simp [dosetInd, Set.indicator_apply, hm]
  · intro x hx
    rw [Function.mem_support] at hx
    rw [Finset.mem_coe, mem_cosetsIn]
    by_contra hm
    apply hx
    simp [dosetInd, Set.indicator_apply, hm]

/- English proof (translation)
Take `⟨a, ha, b, hb, h⟩` from `DoubleCoset.mem_doubleCoset.mp (mem_cosetsIn.mp hx)`. Rewrite using `[h]`. Conclude with `hf ⟨a, ha⟩ ⟨b, hb⟩ g`.
-/
theorem eq_of_mem_cosetsIn {hK : IsCommensurated K} {f : G → ℂ} (hf : IsBiInv K f) {g : G} {x : G ⧸ K}
    (hx : x ∈ cosetsIn hK g) : f x.out = f g := by
  obtain ⟨a, ha, b, hb, h⟩ := DoubleCoset.mem_doubleCoset.mp (mem_cosetsIn.mp hx)
  rw [h]
  exact hf ⟨a, ha⟩ ⟨b, hb⟩ g

def dosetOf (x : G ⧸ K) : Set G := DoubleCoset.doubleCoset x.out (K : Set G) (K : Set G)

/- English proof (translation)
Rewrite using `[mem_cosetsIn]`. Unfold `dosetOf`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[← h]`.

Conclude with `DoubleCoset.mem_doubleCoset_self K K y.out`. Introduce `h`. Conclude with `DoubleCoset.doubleCoset_eq_of_mem h`.
-/
theorem dosetOf_eq_iff {hK : IsCommensurated K} {x y : G ⧸ K} : dosetOf y = dosetOf x ↔ y ∈ cosetsIn hK x.out := by
  rw [mem_cosetsIn]
  unfold dosetOf
  constructor
  · intro h
    rw [← h]
    exact DoubleCoset.mem_doubleCoset_self K K y.out
  · intro h
    exact DoubleCoset.doubleCoset_eq_of_mem h

/- English proof (translation)
Rewrite using `[← Finset.tsum_subtype (cosetsIn hK x.out) h]`. Conclude with `(Equiv.subtypeEquivRight (fun y => (dosetOf_eq_iff (hK := hK) (x := x) (y := y)))).tsum_eq (fun c => h c.1)`.
-/
theorem tsum_fiber {M : Type} [AddCommMonoid M] [TopologicalSpace M] (hK : IsCommensurated K) (x : G ⧸ K)
    (h : G ⧸ K → M) : ∑' c : {y : G ⧸ K // dosetOf y = dosetOf x}, h c = ∑ y ∈ cosetsIn hK x.out, h y := by
  rw [← Finset.tsum_subtype (cosetsIn hK x.out) h]
  exact (Equiv.subtypeEquivRight
    (fun y => (dosetOf_eq_iff (hK := hK) (x := x) (y := y)))).tsum_eq (fun c => h c.1)

/- English proof (translation)
Distinguish the cases in `hne : ∃ y : G ⧸ K, dosetOf y = q`. Take `⟨x, rfl⟩` from `hne`. Conclude with `Finite.of_equiv _ (Equiv.subtypeEquivRight (fun y => (dosetOf_eq_iff (hK := hK) (x := x) (y := y)))).symm`. Use `haveI : IsEmpty {y : G ⧸ K // dosetOf y = q} := ⟨fun c => hne ⟨c.1, c.2⟩⟩ infer_instance`.
-/
theorem finite_fiber (hK : IsCommensurated K) (q : Set G) : Finite {y : G ⧸ K // dosetOf y = q} := by
  by_cases hne : ∃ y : G ⧸ K, dosetOf y = q
  · obtain ⟨x, rfl⟩ := hne
    exact Finite.of_equiv _ (Equiv.subtypeEquivRight
      (fun y => (dosetOf_eq_iff (hK := hK) (x := x) (y := y)))).symm
  · haveI : IsEmpty {y : G ⧸ K // dosetOf y = q} := ⟨fun c => hne ⟨c.1, c.2⟩⟩
    infer_instance

/- English proof (translation)
Distinguish the cases in `hne : ∃ y : G ⧸ K, dosetOf y = q`. Take `⟨x, rfl⟩` from `hne`. Establish `t1 : (∑' c : {y : G ⧸ K // dosetOf y = dosetOf x}, F c.1.out * φ c.1.out) = ∑ y ∈ cosetsIn hK x.out, F y.out * φ y.out` using `tsum_fiber hK x (fun y => F y.out * φ y.out)`. Establish `t2 : (∑' c : {y : G ⧸ K // dosetOf y = dosetOf x}, F c.1.out * w c.1.out) = ∑ y ∈ cosetsIn hK x.out, F y.out * w y.out` using `tsum_fiber hK x (fun y => F y.out * w y.out)`. Establish `t3 : (∑' c : {y : G ⧸ K // dosetOf y = dosetOf x}, ‖F c.1.out * w c.1.out‖) = ∑ y ∈ cosetsIn hK x.out, ‖F y.out * w y.out‖` using `tsum_fiber hK x (fun y => ‖F y.out * w y.out‖)`.

Establish `t4 : (∑' c : {y : G ⧸ K // dosetOf y = dosetOf x}, ‖F c.1.out * φ c.1.out‖) = ∑ y ∈ cosetsIn hK x.out, ‖F y.out * φ y.out‖` using `tsum_fiber hK x (fun y => ‖F y.out * φ y.out‖)`. Rewrite using `[t1, t2, t3, t4]`. Establish `hF' : ∀ y ∈ cosetsIn hK x.out, F y.out = F x.out` using `fun y hy => eq_of_mem_cosetsIn hF hy`. Establish `hW' : ∀ y ∈ cosetsIn hK x.out, w y.out = w x.out` using `fun y hy => eq_of_mem_cosetsIn hw hy`. Establish `hsum : ∑ y ∈ cosetsIn hK x.out, φ y.out = ∑ y ∈ cosetsIn hK x.out, w y.out`.

Rewrite using `[← hAct_dosetInd hK, ← hAct_dosetInd hK, h]`. Establish `e1 : ∑ y ∈ cosetsIn hK x.out, F y.out * φ y.out = F x.out * ∑ y ∈ cosetsIn hK x.out, φ y.out`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun y hy => by rw [hF' y hy]`. Establish `e2 : ∑ y ∈ cosetsIn hK x.out, F y.out * w y.out = F x.out * ∑ y ∈ cosetsIn hK x.out, w y.out`.

Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun y hy => by rw [hF' y hy]`. Establish `e4 : ∑ y ∈ cosetsIn hK x.out, F y.out * w y.out = ∑ y ∈ cosetsIn hK x.out, F y.out * φ y.out`. Rewrite using `[e1, e2, hsum]`. Establish `hc : ∀ y ∈ cosetsIn hK x.out, F y.out * w y.out = F x.out * w x.out` using `fun y hy => by`.

Rewrite using `[hF' y hy, hW' y hy]`. Establish `e3 : ∑ y ∈ cosetsIn hK x.out, ‖F y.out * w y.out‖ = ‖∑ y ∈ cosetsIn hK x.out, F y.out * w y.out‖`. Rewrite using `[Finset.sum_congr rfl hc, Finset.sum_congr rfl (fun y hy => congrArg (‖·‖) (hc y hy))]`. Simplify using `only [Finset.sum_const, nsmul_eq_mul, norm_mul, Complex.norm_natCast]`. Use `⟨e4.symm, ?_⟩` and prove the remaining obligations.

Rewrite using `[e3, e4]`. Conclude with `norm_sum_le _ _`. Use `haveI : IsEmpty {y : G ⧸ K // dosetOf y = q} := ⟨fun c => hne ⟨c.1, c.2⟩⟩`. Simplify using `only [tsum_empty, le_refl, and_self]`.
-/
theorem fiber_compare (hK : IsCommensurated K) {F w φ : G → ℂ} (hF : IsBiInv K F) (hw : IsBiInv K w)
    (h : ∀ g, hAct K (dosetInd ℂ K g) w 1 = hAct K (dosetInd ℂ K g) φ 1) (q : Set G) :
    ∑' c : {y : G ⧸ K // dosetOf y = q}, F c.1.out * φ c.1.out = ∑' c : {y : G ⧸ K // dosetOf y = q}, F c.1.out * w c.1.out ∧
    ∑' c : {y : G ⧸ K // dosetOf y = q}, ‖F c.1.out * w c.1.out‖ ≤
      ∑' c : {y : G ⧸ K // dosetOf y = q}, ‖F c.1.out * φ c.1.out‖ := by
  by_cases hne : ∃ y : G ⧸ K, dosetOf y = q
  · obtain ⟨x, rfl⟩ := hne
    have t1 : (∑' c : {y : G ⧸ K // dosetOf y = dosetOf x}, F c.1.out * φ c.1.out) =
        ∑ y ∈ cosetsIn hK x.out, F y.out * φ y.out := tsum_fiber hK x (fun y => F y.out * φ y.out)
    have t2 : (∑' c : {y : G ⧸ K // dosetOf y = dosetOf x}, F c.1.out * w c.1.out) =
        ∑ y ∈ cosetsIn hK x.out, F y.out * w y.out := tsum_fiber hK x (fun y => F y.out * w y.out)
    have t3 : (∑' c : {y : G ⧸ K // dosetOf y = dosetOf x}, ‖F c.1.out * w c.1.out‖) =
        ∑ y ∈ cosetsIn hK x.out, ‖F y.out * w y.out‖ := tsum_fiber hK x (fun y => ‖F y.out * w y.out‖)
    have t4 : (∑' c : {y : G ⧸ K // dosetOf y = dosetOf x}, ‖F c.1.out * φ c.1.out‖) =
        ∑ y ∈ cosetsIn hK x.out, ‖F y.out * φ y.out‖ := tsum_fiber hK x (fun y => ‖F y.out * φ y.out‖)
    rw [t1, t2, t3, t4]
    have hF' : ∀ y ∈ cosetsIn hK x.out, F y.out = F x.out := fun y hy => eq_of_mem_cosetsIn hF hy
    have hW' : ∀ y ∈ cosetsIn hK x.out, w y.out = w x.out := fun y hy => eq_of_mem_cosetsIn hw hy
    have hsum : ∑ y ∈ cosetsIn hK x.out, φ y.out = ∑ y ∈ cosetsIn hK x.out, w y.out := by
      rw [← hAct_dosetInd hK, ← hAct_dosetInd hK, h]
    have e1 : ∑ y ∈ cosetsIn hK x.out, F y.out * φ y.out = F x.out * ∑ y ∈ cosetsIn hK x.out, φ y.out := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y hy => by rw [hF' y hy]
    have e2 : ∑ y ∈ cosetsIn hK x.out, F y.out * w y.out = F x.out * ∑ y ∈ cosetsIn hK x.out, w y.out := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y hy => by rw [hF' y hy]
    have e4 : ∑ y ∈ cosetsIn hK x.out, F y.out * w y.out = ∑ y ∈ cosetsIn hK x.out, F y.out * φ y.out := by
      rw [e1, e2, hsum]
    have hc : ∀ y ∈ cosetsIn hK x.out, F y.out * w y.out = F x.out * w x.out := fun y hy => by
      rw [hF' y hy, hW' y hy]
    have e3 : ∑ y ∈ cosetsIn hK x.out, ‖F y.out * w y.out‖ = ‖∑ y ∈ cosetsIn hK x.out, F y.out * w y.out‖ := by
      rw [Finset.sum_congr rfl hc, Finset.sum_congr rfl (fun y hy => congrArg (‖·‖) (hc y hy))]
      simp only [Finset.sum_const, nsmul_eq_mul, norm_mul, Complex.norm_natCast]
    refine ⟨e4.symm, ?_⟩
    rw [e3, e4]
    exact norm_sum_le _ _
  · haveI : IsEmpty {y : G ⧸ K // dosetOf y = q} := ⟨fun c => hne ⟨c.1, c.2⟩⟩
    simp only [tsum_empty, le_refl, and_self]

/- English proof (translation)
Introduce `G _ K hK F w φ Z hF hw h ha`. Set `e : (Σ q : Set G, {y : G ⧸ K // dosetOf y = q}) ≃ G ⧸ K` to `Equiv.sigmaFiberEquiv dosetOf`. Establish `haN : Summable fun x : G ⧸ K => ‖F x.out * φ x.out‖` using `summable_norm_iff.mpr ha.summable`. Establish `haN' : Summable fun p => ‖F (e p).out * φ (e p).out‖` using `(e.summable_iff (f := fun x : G ⧸ K => ‖F x.out * φ x.out‖)).mpr haN`. Establish `hbN' : Summable fun p => ‖F (e p).out * w (e p).out‖`.

Rewrite using `[summable_sigma_of_nonneg (fun p => norm_nonneg _)]`. Use `⟨fun q => ?_, ?_⟩` and prove the remaining obligations. Use `haveI := finite_fiber hK q`. Conclude with `Summable.of_finite`. Establish `hA` using `((summable_sigma_of_nonneg (fun p => norm_nonneg _)).mp haN').2`.

Use `Summable.of_nonneg_of_le (fun q => tsum_nonneg fun _ => norm_nonneg _) (fun q => ?_) hA` and prove the remaining obligations. Conclude with `(fiber_compare hK hF hw h q).2`. Establish `hbN : Summable fun x : G ⧸ K => ‖F x.out * w x.out‖` using `(e.summable_iff (f := fun x : G ⧸ K => ‖F x.out * w x.out‖)).mp hbN'`. Establish `hbS : Summable fun x : G ⧸ K => F x.out * w x.out` using `hbN.of_norm`. Establish `hbS' : Summable fun p => F (e p).out * w (e p).out` using `(e.summable_iff (f := fun x : G ⧸ K => F x.out * w x.out)).mpr hbS`.

Establish `haS' : Summable fun p => F (e p).out * φ (e p).out` using `(e.summable_iff (f := fun x : G ⧸ K => F x.out * φ x.out)).mpr ha.summable`. Establish `key : ∑' x : G ⧸ K, F x.out * w x.out = ∑' x : G ⧸ K, F x.out * φ x.out`. Combine the equalities or inequalities in the displayed calculation. Establish `hb` using `hbS.hasSum`. Rewrite `hb` using `[key, ha.tsum_eq]`. Then use the resulting hypothesis.
-/
theorem dosetSwap : DosetSwap := by
  intro G _ K hK F w φ Z hF hw h ha
  let e : (Σ q : Set G, {y : G ⧸ K // dosetOf y = q}) ≃ G ⧸ K := Equiv.sigmaFiberEquiv dosetOf
  have haN : Summable fun x : G ⧸ K => ‖F x.out * φ x.out‖ := summable_norm_iff.mpr ha.summable
  have haN' : Summable fun p => ‖F (e p).out * φ (e p).out‖ :=
    (e.summable_iff (f := fun x : G ⧸ K => ‖F x.out * φ x.out‖)).mpr haN
  have hbN' : Summable fun p => ‖F (e p).out * w (e p).out‖ := by
    rw [summable_sigma_of_nonneg (fun p => norm_nonneg _)]
    refine ⟨fun q => ?_, ?_⟩
    · haveI := finite_fiber hK q
      exact Summable.of_finite
    · have hA := ((summable_sigma_of_nonneg (fun p => norm_nonneg _)).mp haN').2
      refine Summable.of_nonneg_of_le (fun q => tsum_nonneg fun _ => norm_nonneg _) (fun q => ?_) hA
      exact (fiber_compare hK hF hw h q).2
  have hbN : Summable fun x : G ⧸ K => ‖F x.out * w x.out‖ :=
    (e.summable_iff (f := fun x : G ⧸ K => ‖F x.out * w x.out‖)).mp hbN'
  have hbS : Summable fun x : G ⧸ K => F x.out * w x.out := hbN.of_norm
  have hbS' : Summable fun p => F (e p).out * w (e p).out :=
    (e.summable_iff (f := fun x : G ⧸ K => F x.out * w x.out)).mpr hbS
  have haS' : Summable fun p => F (e p).out * φ (e p).out :=
    (e.summable_iff (f := fun x : G ⧸ K => F x.out * φ x.out)).mpr ha.summable
  have key : ∑' x : G ⧸ K, F x.out * w x.out = ∑' x : G ⧸ K, F x.out * φ x.out := by
    calc ∑' x : G ⧸ K, F x.out * w x.out = ∑' p, F (e p).out * w (e p).out :=
          (e.tsum_eq (fun x => F x.out * w x.out)).symm
      _ = ∑' q, ∑' c : {y : G ⧸ K // dosetOf y = q}, F c.1.out * w c.1.out := hbS'.tsum_sigma
      _ = ∑' q, ∑' c : {y : G ⧸ K // dosetOf y = q}, F c.1.out * φ c.1.out :=
          tsum_congr fun q => ((fiber_compare hK hF hw h q).1).symm
      _ = ∑' p, F (e p).out * φ (e p).out := haS'.tsum_sigma.symm
      _ = ∑' x : G ⧸ K, F x.out * φ x.out := e.tsum_eq (fun x => F x.out * φ x.out)
  have hb := hbS.hasSum
  rwa [key, ha.tsum_eq] at hb

end GlobalTheory.CompanionTheory.InertZeta
