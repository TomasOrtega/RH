import Mathlib
import GroundTheory.PAdicHodge.KerFontaineThetaCompFrobeniusEquivSymmPow
set_option maxSynthPendingDepth 1

noncomputable section

open WittVector Filter Topology

namespace GroundTheory.PAdicHodge

section Coordinates

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R]

/- English proof (translation)
Establish `key : ∀ a b : WittVector p R, (∀ i < n, a.coeff i - b.coeff i ∈ J) ↔ WittVector.truncate n (WittVector.map (Ideal.Quotient.mk J) a) = WittVector.truncate n (WittVector.map (Ideal.Quotient.mk J) b)`. Introduce `a b`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `TruncatedWittVector.ext fun i => ?_` and prove the remaining obligations.

Rewrite using `[coeff_truncate, coeff_truncate, map_coeff, map_coeff, Ideal.Quotient.eq]`. Conclude with `h i i.2`. Introduce `h i hi`. Use `congrArg (TruncatedWittVector.coeff ⟨i, hi⟩) h` as an intermediate fact. Simplify using `only [coeff_truncate, map_coeff] at this`.

Conclude with `Ideal.Quotient.eq.1 this`. Establish `h2` using `key (x - y) 0`. Simplify using `only [zero_coeff, sub_zero, map_sub, map_zero, sub_eq_zero] at h2`. Rewrite using `[key]`. Conclude with `h2.symm`.
-/
theorem WittVector.forall_lt_sub_coeff_mem_iff (J : Ideal R) (n : ℕ) (x y : WittVector p R) :
    (∀ i < n, x.coeff i - y.coeff i ∈ J) ↔ ∀ i < n, (x - y).coeff i ∈ J := by
  have key : ∀ a b : WittVector p R, (∀ i < n, a.coeff i - b.coeff i ∈ J) ↔
      WittVector.truncate n (WittVector.map (Ideal.Quotient.mk J) a) =
        WittVector.truncate n (WittVector.map (Ideal.Quotient.mk J) b) := by
    intro a b
    constructor
    · intro h
      refine TruncatedWittVector.ext fun i => ?_
      rw [coeff_truncate, coeff_truncate, map_coeff, map_coeff, Ideal.Quotient.eq]
      exact h i i.2
    · intro h i hi
      have := congrArg (TruncatedWittVector.coeff ⟨i, hi⟩) h
      simp only [coeff_truncate, map_coeff] at this
      exact Ideal.Quotient.eq.1 this
  have h2 := key (x - y) 0
  simp only [zero_coeff, sub_zero, map_sub, map_zero, sub_eq_zero] at h2
  rw [key]
  exact h2.symm

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h i`. Conclude with `(WittVector.forall_lt_sub_coeff_mem_iff J (i + 1) x y).1 (fun j _ => h j) i i.lt_succ_self`. Introduce `h i`. Conclude with `(WittVector.forall_lt_sub_coeff_mem_iff J (i + 1) x y).2 (fun j _ => h j) i i.lt_succ_self`.
-/
theorem WittVector.forall_sub_coeff_mem_iff (J : Ideal R) (x y : WittVector p R) :
    (∀ i, x.coeff i - y.coeff i ∈ J) ↔ ∀ i, (x - y).coeff i ∈ J := by
  constructor
  · intro h i
    exact (WittVector.forall_lt_sub_coeff_mem_iff J (i + 1) x y).1 (fun j _ => h j) i i.lt_succ_self
  · intro h i
    exact (WittVector.forall_lt_sub_coeff_mem_iff J (i + 1) x y).2 (fun j _ => h j) i i.lt_succ_self

variable [CharP R p]

/- English proof (translation)
Take `⟨c, hc⟩` from `(WittVector.mem_span_teichmuller_iff b y).1 hy i`. Rewrite using `[hc]`. Conclude with `J.mul_mem_right c (J.pow_mem_of_mem hb _ (pow_pos hp.out.pos i))`.
-/
theorem WittVector.coeff_mem_of_mem_span_teichmuller {b : R} {J : Ideal R} (hb : b ∈ J)
    {y : WittVector p R} (hy : y ∈ Ideal.span {teichmuller p b}) (i : ℕ) : y.coeff i ∈ J := by
  obtain ⟨c, hc⟩ := (WittVector.mem_span_teichmuller_iff b y).1 hy i
  rw [hc]
  exact J.mul_mem_right c (J.pow_mem_of_mem hb _ (pow_pos hp.out.pos i))

end Coordinates

/- English proof (translation)
Rewrite using `[le_iff_nhds]`. Introduce `x`. Rewrite using `[(J.hasBasis_nhds_adic x).ge_iff]`. Introduce `n _`. Conclude with `(I.hasBasis_nhds_adic x).mem_iff.2 ⟨n, trivial, Set.image_mono (Ideal.pow_right_mono h n)⟩`.
-/
theorem Ideal.adicTopology_mono {A : Type*} [CommRing A] {I J : Ideal A} (h : I ≤ J) :
    I.adicTopology ≤ J.adicTopology := by
  rw [le_iff_nhds]
  intro x
  rw [(J.hasBasis_nhds_adic x).ge_iff]
  intro n _
  exact (I.hasBasis_nhds_adic x).mem_iff.2 ⟨n, trivial, Set.image_mono (Ideal.pow_right_mono h n)⟩

namespace AInf

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]

local notation "𝒪♭" => PreTilt (normInteger K) p

variable (K p) in

@[instance_reducible]
def pAdicTopology : TopologicalSpace (AInf K p) :=
  (Ideal.span {(p : AInf K p)}).adicTopology

@[instance_reducible]
def teichmullerAdicTopology (ϖ : 𝒪♭) : TopologicalSpace (AInf K p) :=
  (Ideal.span {teichmuller p ϖ}).adicTopology

variable (K p) in

@[instance_reducible]
def weakTopology : TopologicalSpace (AInf K p) :=
  TopologicalSpace.induced (fun x : AInf K p => x.coeff) inferInstance

/- English proof (translation)
Rewrite using `[Ideal.mem_span_singleton, preTilt_dvd_iff_norm_le, norm_pow]`.
-/
theorem mem_span_pow_iff_norm_le (ϖ x : 𝒪♭) (k : ℕ) :
    x ∈ Ideal.span {ϖ ^ k} ↔ ‖x‖ ≤ ‖ϖ‖ ^ k := by
  rw [Ideal.mem_span_singleton, preTilt_dvd_iff_norm_le, norm_pow]

/- English proof (translation)
Repeatedly rewrite using `[← mem_span_pow_iff_norm_le]`. Conclude with `WittVector.forall_lt_sub_coeff_mem_iff _ n x y`.
-/
theorem norm_coeff_sub_le_iff (ϖ : 𝒪♭) (k n : ℕ) (x y : AInf K p) :
    (∀ i < n, ‖x.coeff i - y.coeff i‖ ≤ ‖ϖ‖ ^ k) ↔ ∀ i < n, ‖(x - y).coeff i‖ ≤ ‖ϖ‖ ^ k := by
  simp_rw [← mem_span_pow_iff_norm_le]
  exact WittVector.forall_lt_sub_coeff_mem_iff _ n x y

/- English proof (translation)
Repeatedly rewrite using `[← mem_span_pow_iff_norm_le]`. Conclude with `WittVector.forall_sub_coeff_mem_iff _ x y`.
-/
theorem norm_coeff_sub_le_iff' (ϖ : 𝒪♭) (k : ℕ) (x y : AInf K p) :
    (∀ i, ‖x.coeff i - y.coeff i‖ ≤ ‖ϖ‖ ^ k) ↔ ∀ i, ‖(x - y).coeff i‖ ≤ ‖ϖ‖ ^ k := by
  simp_rw [← mem_span_pow_iff_norm_le]
  exact WittVector.forall_sub_coeff_mem_iff _ x y

/- English proof (translation)
Rewrite using `[WittVector.mem_span_teichmuller_pow_iff]`. Repeatedly rewrite using `[preTilt_dvd_iff_norm_le, norm_pow]`.
-/
theorem mem_span_teichmuller_pow_iff_norm_le (ϖ : 𝒪♭) (n : ℕ) (d : AInf K p) :
    d ∈ Ideal.span {teichmuller p ϖ} ^ n ↔ ∀ i, ‖d.coeff i‖ ≤ ‖ϖ‖ ^ (n * p ^ i) := by
  rw [WittVector.mem_span_teichmuller_pow_iff]
  simp_rw [preTilt_dvd_iff_norm_le, norm_pow]

/- English proof (translation)
Break down `n with _ | n` into its components or cases. Simplify using the standard rewrite rules. Use `set c : ℕ → 𝒪♭ := fun i => ((_root_.frobeniusEquiv 𝒪♭ p).symm ^ i) (d.coeff i) with hc`. Establish `hexp` using `WittVector.dvd_sub_sum_teichmullerSeries (p := p) c n`. Rewrite `hexp` using `[hc, WittVector.teichmullerSeries_coeff_eq, ← hc]`.

Take `⟨z, hz⟩` from `hexp`. Establish `hd : d = ∑ i ∈ Finset.Iic n, teichmuller p (c i) * (p : AInf K p) ^ i + (p : AInf K p) ^ (n + 1) * z`. Rewrite using `[← hz]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hd]`.

Establish `hpJ : (p : AInf K p) ∈ Ideal.span {(p : AInf K p), teichmuller p ϖ}` using `Ideal.subset_span (by simp)`. Establish `hϖJ : teichmuller p ϖ ∈ Ideal.span {(p : AInf K p), teichmuller p ϖ}` using `Ideal.subset_span (by simp)`. Use `add_mem (Ideal.sum_mem _ fun i hi => ?_) (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hpJ _))` and prove the remaining obligations. Establish `hin : i < n + 1` using `Nat.lt_succ_of_le (Finset.mem_Iic.1 hi)`. Establish `hci : ϖ ^ (n + 1) ∣ c i`.

Rewrite using `[preTilt_dvd_iff_norm_le, norm_pow]`. Establish `h1 : ‖c i‖ ^ p ^ i = ‖d.coeff i‖`. Rewrite using `[← norm_pow, hc, frobeniusEquiv_symm_pow_apply_pow]`. Establish `h2 : ‖ϖ‖ ^ ((n + 1) * p ^ (n + 1)) ≤ (‖ϖ‖ ^ (n + 1)) ^ p ^ i`. Rewrite using `[← pow_mul]`.

Conclude with `pow_le_pow_of_le_one (norm_nonneg _) (preTilt_norm_le_one ϖ) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hp.out.pos hin.le))`. Conclude with `(pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (pow_ne_zero _ hp.out.ne_zero)).1 (h1 ▸ (h i hin).trans h2)`. Take `⟨e, he⟩` from `hci`. Rewrite using `[he, map_mul, map_pow]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hϖJ _))`.
-/
theorem mem_span_pow_of_norm_coeff_le (ϖ : 𝒪♭) (n : ℕ) (d : AInf K p)
    (h : ∀ i < n, ‖d.coeff i‖ ≤ ‖ϖ‖ ^ (n * p ^ n)) :
    d ∈ Ideal.span {(p : AInf K p), teichmuller p ϖ} ^ n := by
  rcases n with _ | n
  · simp
  set c : ℕ → 𝒪♭ := fun i => ((_root_.frobeniusEquiv 𝒪♭ p).symm ^ i) (d.coeff i) with hc
  have hexp := WittVector.dvd_sub_sum_teichmullerSeries (p := p) c n
  rw [hc, WittVector.teichmullerSeries_coeff_eq, ← hc] at hexp
  obtain ⟨z, hz⟩ := hexp
  have hd : d = ∑ i ∈ Finset.Iic n, teichmuller p (c i) * (p : AInf K p) ^ i +
      (p : AInf K p) ^ (n + 1) * z := by
    rw [← hz]; ring
  rw [hd]
  have hpJ : (p : AInf K p) ∈ Ideal.span {(p : AInf K p), teichmuller p ϖ} :=
    Ideal.subset_span (by simp)
  have hϖJ : teichmuller p ϖ ∈ Ideal.span {(p : AInf K p), teichmuller p ϖ} :=
    Ideal.subset_span (by simp)
  refine add_mem (Ideal.sum_mem _ fun i hi => ?_) (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hpJ _))
  have hin : i < n + 1 := Nat.lt_succ_of_le (Finset.mem_Iic.1 hi)
  have hci : ϖ ^ (n + 1) ∣ c i := by
    rw [preTilt_dvd_iff_norm_le, norm_pow]
    have h1 : ‖c i‖ ^ p ^ i = ‖d.coeff i‖ := by
      rw [← norm_pow, hc, frobeniusEquiv_symm_pow_apply_pow]
    have h2 : ‖ϖ‖ ^ ((n + 1) * p ^ (n + 1)) ≤ (‖ϖ‖ ^ (n + 1)) ^ p ^ i := by
      rw [← pow_mul]
      exact pow_le_pow_of_le_one (norm_nonneg _) (preTilt_norm_le_one ϖ)
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hp.out.pos hin.le))
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity)
      (pow_ne_zero _ hp.out.ne_zero)).1 (h1 ▸ (h i hin).trans h2)
  obtain ⟨e, he⟩ := hci
  rw [he, map_mul, map_pow]
  exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hϖJ _))

/- English proof (translation)
Rewrite `hd` using `[Ideal.span_insert]`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 (Ideal.sup_pow_add_le_pow_sup_pow hd)`. Rewrite `ha` using `[Ideal.span_singleton_pow, mem_span_p_pow_iff_le_coeff_eq_zero]`. Rewrite `hb` using `[WittVector.span_teichmuller_pow]`. Establish `hb'` using `WittVector.coeff_mem_of_mem_span_teichmuller (Ideal.mem_span_singleton_self (ϖ ^ N)) hb`.

Establish `hab` using `(WittVector.forall_lt_sub_coeff_mem_iff (Ideal.span {ϖ ^ N}) N (a + b) b).2 (fun i hi => by rw [add_sub_cancel_right, ha i hi]; exact Ideal.zero_mem _)`. Introduce `i hi`. Rewrite using `[← mem_span_pow_iff_norm_le]`. Use `add_mem (hab i hi) (hb' i)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis.
-/
theorem norm_coeff_le_of_mem_span_pow (ϖ : 𝒪♭) (N : ℕ) (d : AInf K p)
    (hd : d ∈ Ideal.span {(p : AInf K p), teichmuller p ϖ} ^ (N + N)) :
    ∀ i < N, ‖d.coeff i‖ ≤ ‖ϖ‖ ^ N := by
  rw [Ideal.span_insert] at hd
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (Ideal.sup_pow_add_le_pow_sup_pow hd)
  rw [Ideal.span_singleton_pow, mem_span_p_pow_iff_le_coeff_eq_zero] at ha
  rw [WittVector.span_teichmuller_pow] at hb
  have hb' := WittVector.coeff_mem_of_mem_span_teichmuller
    (Ideal.mem_span_singleton_self (ϖ ^ N)) hb
  have hab := (WittVector.forall_lt_sub_coeff_mem_iff (Ideal.span {ϖ ^ N}) N (a + b) b).2
    (fun i hi => by rw [add_sub_cancel_right, ha i hi]; exact Ideal.zero_mem _)
  intro i hi
  rw [← mem_span_pow_iff_norm_le]
  have := add_mem (hab i hi) (hb' i)
  rwa [sub_add_cancel] at this

/- English proof (translation)
The claim follows from `(norm_coeff_sub_le_iff ϖ N N x y).2 (norm_coeff_le_of_mem_span_pow ϖ N _ hd)`.
-/
theorem norm_coeff_sub_le_of_mem_span_pow (ϖ : 𝒪♭) (N : ℕ) (x y : AInf K p)
    (hd : x - y ∈ Ideal.span {(p : AInf K p), teichmuller p ϖ} ^ (N + N)) :
    ∀ i < N, ‖x.coeff i - y.coeff i‖ ≤ ‖ϖ‖ ^ N :=
  (norm_coeff_sub_le_iff ϖ N N x y).2 (norm_coeff_le_of_mem_span_pow ϖ N _ hd)

/- English proof (translation)
Set `` to `weakTopology K p`. Conclude with `(continuous_apply i).comp continuous_induced_dom`.
-/
theorem continuous_coeff (i : ℕ) :
    @Continuous (AInf K p) 𝒪♭ (weakTopology K p) _ fun y => y.coeff i := by
  let := weakTopology K p
  exact (continuous_apply i).comp continuous_induced_dom

/- English proof (translation)
Use `set J := Ideal.span {(p : AInf K p), teichmuller p ϖ}`. Establish `hr : 0 < ‖ϖ‖` using `norm_pos_iff.2 hϖ0`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[le_iff_nhds]`. Introduce `x`.

Rewrite using `[(J.hasBasis_nhds_adic x).ge_iff]`. Introduce `n _`. Set `` to `weakTopology K p`. Use `set N := n * p ^ n`. Establish `hnN : n ≤ N` using `Nat.le_mul_of_pos_right n (pow_pos hp.out.pos n)`.

Establish `hmem : {y : AInf K p | ∀ i ∈ Finset.range N, ‖y.coeff i - x.coeff i‖ ≤ ‖ϖ‖ ^ N} ∈ @nhds _ (weakTopology K p) x`. Establish `: {y : AInf K p | ∀ i ∈ Finset.range N, ‖y.coeff i - x.coeff i‖ ≤ ‖ϖ‖ ^ N} = ⋂ i ∈ Finset.range N, {y : AInf K p | ‖y.coeff i - x.coeff i‖ ≤ ‖ϖ‖ ^ N}`. Use extensionality with `y`. Simplify using the standard rewrite rules. Rewrite using `[this, @Filter.biInter_finset_mem]`.

Introduce `i _`. Establish `hb : Metric.closedBall (x.coeff i) (‖ϖ‖ ^ N) ∈ 𝓝 (x.coeff i)` using `Metric.closedBall_mem_nhds _ (pow_pos hr N)`. Use `(continuous_coeff (K := K) (p := p) i).continuousAt (x := x) |>.preimage_mem_nhds hb` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `y`.

Simplify using `[Metric.mem_closedBall, dist_eq_norm]`. Use `Filter.mem_of_superset hmem fun y hy => ⟨y - x, ?_, by simp⟩` and prove the remaining obligations. Apply `mem_span_pow_of_norm_coeff_le ϖ n` to reduce the goal to its premises. Introduce `i hi`. Conclude with `(norm_coeff_sub_le_iff ϖ N N y x).1 (fun j hj => hy j (Finset.mem_range.2 hj)) i (hi.trans_le hnN)`.

Rewrite using `[le_iff_nhds]`. Introduce `x s hs`. Rewrite using `[(J.hasBasis_nhds_adic x).mem_iff]`. Rewrite `hs` using `[weakTopology, nhds_induced, Filter.mem_comap]`. Take `⟨t, ht, hts⟩` from `hs`.

Rewrite `ht` using `[nhds_pi, Filter.mem_pi']`. Take `⟨I, u, hu, hIu⟩` from `ht`. Establish `hk : ∀ i, ∃ k : ℕ, ∀ z, ‖z - x.coeff i‖ ≤ ‖ϖ‖ ^ k → z ∈ u i`. Introduce `i`. Take `⟨ε, hε, hεu⟩` from `Metric.mem_nhds_iff.1 (hu i)`.

Take `⟨k, hk⟩` from `exists_pow_lt_of_lt_one hε hϖ1`. Conclude with `⟨k, fun z hz => hεu (by rw [Metric.mem_ball, dist_eq_norm]; exact hz.trans_lt hk)⟩`. Use `choose k hk using hk`. Use `set N := max (I.sup id + 1) (I.sup k)`. Use `⟨N + N, trivial, ?_⟩` and prove the remaining obligations.

Introduce and unpack `_ ⟨d, hd, rfl⟩`. Apply `hts` to reduce the goal to its premises. Apply `hIu` to reduce the goal to its premises. Introduce `i hi`. Establish `hiN : i < N` using `lt_of_lt_of_le (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)) (le_max_left _ _)`.

Establish `hkN : k i ≤ N` using `(Finset.le_sup (f := k) hi).trans (le_max_right _ _)`. Apply `hk i` to reduce the goal to its premises. Establish `h1` using `norm_coeff_sub_le_of_mem_span_pow ϖ N (x + d) x (by rwa [add_sub_cancel_left]) i hiN`. Conclude with `h1.trans (pow_le_pow_of_le_one (norm_nonneg _) (preTilt_norm_le_one _) hkN)`.
-/
theorem weakTopology_eq_adicTopology (ϖ : 𝒪♭) (hϖ0 : ϖ ≠ 0) (hϖ1 : ‖ϖ‖ < 1) :
    weakTopology K p = (Ideal.span {(p : AInf K p), teichmuller p ϖ}).adicTopology := by
  set J := Ideal.span {(p : AInf K p), teichmuller p ϖ}
  have hr : 0 < ‖ϖ‖ := norm_pos_iff.2 hϖ0
  apply le_antisymm
  · rw [le_iff_nhds]
    intro x
    rw [(J.hasBasis_nhds_adic x).ge_iff]
    intro n _
    let := weakTopology K p
    set N := n * p ^ n
    have hnN : n ≤ N := Nat.le_mul_of_pos_right n (pow_pos hp.out.pos n)
    have hmem : {y : AInf K p | ∀ i ∈ Finset.range N, ‖y.coeff i - x.coeff i‖ ≤ ‖ϖ‖ ^ N} ∈
        @nhds _ (weakTopology K p) x := by
      have : {y : AInf K p | ∀ i ∈ Finset.range N, ‖y.coeff i - x.coeff i‖ ≤ ‖ϖ‖ ^ N} =
          ⋂ i ∈ Finset.range N, {y : AInf K p | ‖y.coeff i - x.coeff i‖ ≤ ‖ϖ‖ ^ N} := by
        ext y; simp
      rw [this, @Filter.biInter_finset_mem]
      intro i _
      have hb : Metric.closedBall (x.coeff i) (‖ϖ‖ ^ N) ∈ 𝓝 (x.coeff i) :=
        Metric.closedBall_mem_nhds _ (pow_pos hr N)
      have := (continuous_coeff (K := K) (p := p) i).continuousAt (x := x) |>.preimage_mem_nhds hb
      convert this using 1
      ext y
      simp [Metric.mem_closedBall, dist_eq_norm]
    refine Filter.mem_of_superset hmem fun y hy => ⟨y - x, ?_, by simp⟩
    apply mem_span_pow_of_norm_coeff_le ϖ n
    intro i hi
    exact (norm_coeff_sub_le_iff ϖ N N y x).1 (fun j hj => hy j (Finset.mem_range.2 hj)) i
      (hi.trans_le hnN)
  · rw [le_iff_nhds]
    intro x s hs
    rw [(J.hasBasis_nhds_adic x).mem_iff]
    rw [weakTopology, nhds_induced, Filter.mem_comap] at hs
    obtain ⟨t, ht, hts⟩ := hs
    rw [nhds_pi, Filter.mem_pi'] at ht
    obtain ⟨I, u, hu, hIu⟩ := ht
    have hk : ∀ i, ∃ k : ℕ, ∀ z, ‖z - x.coeff i‖ ≤ ‖ϖ‖ ^ k → z ∈ u i := by
      intro i
      obtain ⟨ε, hε, hεu⟩ := Metric.mem_nhds_iff.1 (hu i)
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε hϖ1
      exact ⟨k, fun z hz => hεu (by rw [Metric.mem_ball, dist_eq_norm]; exact hz.trans_lt hk)⟩
    choose k hk using hk
    set N := max (I.sup id + 1) (I.sup k)
    refine ⟨N + N, trivial, ?_⟩
    rintro _ ⟨d, hd, rfl⟩
    apply hts
    apply hIu
    intro i hi
    have hiN : i < N := lt_of_lt_of_le (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
      (le_max_left _ _)
    have hkN : k i ≤ N := (Finset.le_sup (f := k) hi).trans (le_max_right _ _)
    apply hk i
    have h1 := norm_coeff_sub_le_of_mem_span_pow ϖ N (x + d) x (by rwa [add_sub_cancel_left]) i hiN
    exact h1.trans (pow_le_pow_of_le_one (norm_nonneg _) (preTilt_norm_le_one _) hkN)

/- English proof (translation)
Rewrite using `[← weakTopology_eq_adicTopology ϖ hϖ0 hϖ1, ← weakTopology_eq_adicTopology ϖ' hϖ0' hϖ1']`.
-/
theorem adicTopology_eq (ϖ ϖ' : 𝒪♭) (hϖ0 : ϖ ≠ 0) (hϖ1 : ‖ϖ‖ < 1) (hϖ0' : ϖ' ≠ 0)
    (hϖ1' : ‖ϖ'‖ < 1) :
    (Ideal.span {(p : AInf K p), teichmuller p ϖ}).adicTopology =
      (Ideal.span {(p : AInf K p), teichmuller p ϖ'}).adicTopology := by
  rw [← weakTopology_eq_adicTopology ϖ hϖ0 hϖ1, ← weakTopology_eq_adicTopology ϖ' hϖ0' hϖ1']

/- English proof (translation)
Rewrite using `[WittVector.span_teichmuller_pow, WittVector.span_teichmuller_pow, Ideal.span_singleton_le_span_singleton]`. Use `map_dvd (teichmuller p) ?_` and prove the remaining obligations. Rewrite using `[preTilt_dvd_iff_norm_le, norm_pow, norm_pow]`. Conclude with `h`.
-/
theorem span_teichmuller_pow_le {ϖ ϖ' : 𝒪♭} {m n : ℕ} (h : ‖ϖ‖ ^ m ≤ ‖ϖ'‖ ^ n) :
    Ideal.span {teichmuller p ϖ} ^ m ≤ Ideal.span {(teichmuller p ϖ' : AInf K p)} ^ n := by
  rw [WittVector.span_teichmuller_pow, WittVector.span_teichmuller_pow,
    Ideal.span_singleton_le_span_singleton]
  refine map_dvd (teichmuller p) ?_
  rw [preTilt_dvd_iff_norm_le, norm_pow, norm_pow]
  exact h

/- English proof (translation)
Rewrite using `[teichmullerAdicTopology, teichmullerAdicTopology, le_iff_nhds]`. Introduce `x`. Rewrite using `[((Ideal.span {teichmuller p ϖ'}).hasBasis_nhds_adic x).ge_iff]`. Introduce `n _`. Take `⟨m, hm⟩` from `exists_pow_lt_of_lt_one (pow_pos (norm_pos_iff.2 hϖ0') n) hϖ1`.

Conclude with `((Ideal.span {teichmuller p ϖ}).hasBasis_nhds_adic x).mem_iff.2 ⟨m, trivial, Set.image_mono (span_teichmuller_pow_le hm.le)⟩`.
-/
theorem teichmullerAdicTopology_le (ϖ ϖ' : 𝒪♭) (hϖ1 : ‖ϖ‖ < 1) (hϖ0' : ϖ' ≠ 0) :
    teichmullerAdicTopology (K := K) ϖ ≤ teichmullerAdicTopology ϖ' := by
  rw [teichmullerAdicTopology, teichmullerAdicTopology, le_iff_nhds]
  intro x
  rw [((Ideal.span {teichmuller p ϖ'}).hasBasis_nhds_adic x).ge_iff]
  intro n _
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (pow_pos (norm_pos_iff.2 hϖ0') n) hϖ1
  exact ((Ideal.span {teichmuller p ϖ}).hasBasis_nhds_adic x).mem_iff.2
    ⟨m, trivial, Set.image_mono (span_teichmuller_pow_le hm.le)⟩

/- English proof (translation)
The claim follows from `le_antisymm (teichmullerAdicTopology_le ϖ ϖ' hϖ1 hϖ0') (teichmullerAdicTopology_le ϖ' ϖ hϖ1' hϖ0)`.
-/
theorem teichmullerAdicTopology_eq (ϖ ϖ' : 𝒪♭) (hϖ0 : ϖ ≠ 0) (hϖ1 : ‖ϖ‖ < 1) (hϖ0' : ϖ' ≠ 0)
    (hϖ1' : ‖ϖ'‖ < 1) :
    teichmullerAdicTopology (K := K) ϖ = teichmullerAdicTopology ϖ' :=
  le_antisymm (teichmullerAdicTopology_le ϖ ϖ' hϖ1 hϖ0') (teichmullerAdicTopology_le ϖ' ϖ hϖ1' hϖ0)

/- English proof (translation)
Rewrite using `[weakTopology_eq_adicTopology ϖ hϖ0 hϖ1, pAdicTopology]`. Conclude with `Ideal.adicTopology_mono (Ideal.span_mono (by simp))`.
-/
theorem pAdicTopology_le_weakTopology (ϖ : 𝒪♭) (hϖ0 : ϖ ≠ 0) (hϖ1 : ‖ϖ‖ < 1) :
    pAdicTopology K p ≤ weakTopology K p := by
  rw [weakTopology_eq_adicTopology ϖ hϖ0 hϖ1, pAdicTopology]
  exact Ideal.adicTopology_mono (Ideal.span_mono (by simp))

/- English proof (translation)
Rewrite using `[weakTopology_eq_adicTopology ϖ hϖ0 hϖ1, teichmullerAdicTopology]`. Conclude with `Ideal.adicTopology_mono (Ideal.span_mono (by simp))`.
-/
theorem teichmullerAdicTopology_le_weakTopology (ϖ : 𝒪♭) (hϖ0 : ϖ ≠ 0) (hϖ1 : ‖ϖ‖ < 1) :
    teichmullerAdicTopology ϖ ≤ weakTopology K p := by
  rw [weakTopology_eq_adicTopology ϖ hϖ0 hϖ1, teichmullerAdicTopology]
  exact Ideal.adicTopology_mono (Ideal.span_mono (by simp))

/- English proof (translation)
Rewrite using `[weakTopology_eq_adicTopology ϖ hϖ0 hϖ1]`. Conclude with `(Ideal.span {(p : AInf K p), teichmuller p ϖ}).ringFilterBasis.isTopologicalRing`.
-/
theorem isTopologicalRing_weakTopology (ϖ : 𝒪♭) (hϖ0 : ϖ ≠ 0) (hϖ1 : ‖ϖ‖ < 1) :
    @IsTopologicalRing (AInf K p) (weakTopology K p) _ := by
  rw [weakTopology_eq_adicTopology ϖ hϖ0 hϖ1]
  exact (Ideal.span {(p : AInf K p), teichmuller p ϖ}).ringFilterBasis.isTopologicalRing

omit hp [IsPerfectoidField K p] in

/- English proof (translation)
Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]`.
-/
theorem smodEq_pow_iff {A : Type*} [CommRing A] (I : Ideal A) (n : ℕ) (x y : A) :
    x ≡ y [SMOD (I ^ n • ⊤ : Submodule A A)] ↔ x - y ∈ I ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

/- English proof (translation)
The claim follows from `inferInstance`.
-/
theorem isAdicComplete_p : IsAdicComplete (Ideal.span {(p : AInf K p)}) (AInf K p) :=
  inferInstance

/- English proof (translation)
Use `set J := Ideal.span {(p : AInf K p), teichmuller p ϖ}`. Establish `hr : 0 < ‖ϖ‖` using `norm_pos_iff.2 hϖ0`. Establish `ht` using `tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hϖ1`. Use `{ haus' := fun x hx => ?_, prec' := fun f hf => ?_ }` and prove the remaining obligations. Use extensionality with `i`.

Rewrite using `[zero_coeff, ← norm_le_zero_iff]`. Use `ge_of_tendsto ht (eventually_atTop.2 ⟨i + 1, fun N hN => ?_⟩)` and prove the remaining obligations. Use `(smodEq_pow_iff J (N + N) x 0).1 (hx (N + N))` as an intermediate fact. Rewrite `this` using `[sub_zero]`. Conclude with `norm_coeff_le_of_mem_span_pow ϖ N x this i hN`.

Establish `hf' : ∀ m n, m ≤ n → f m - f n ∈ J ^ m` using `fun m n h => (smodEq_pow_iff J m _ _).1 (hf h)`. Establish `hcauchy : ∀ i, CauchySeq fun m => (f m).coeff i`. Introduce `i`. Rewrite using `[Metric.cauchySeq_iff']`. Introduce `ε hε`.

Take `⟨M, hM⟩` from `exists_pow_lt_of_lt_one hε hϖ1`. Use `⟨(M + i + 1) + (M + i + 1), fun m hm => ?_⟩` and prove the remaining obligations. Establish `h1` using `norm_coeff_sub_le_of_mem_span_pow ϖ (M + i + 1) _ _ (hf' _ m hm) i (by omega)`. Rewrite using `[dist_eq_norm, norm_sub_rev]`. Conclude with `h1.trans_lt ((pow_le_pow_of_le_one (norm_nonneg _) hϖ1.le (by omega)).trans_lt hM)`.

Use `choose c hc using fun i => cauchySeq_tendsto_of_complete (hcauchy i)`. Use `⟨WittVector.mk p c, fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[smodEq_pow_iff]`. Use `set N := n * p ^ n`. Establish `hev : ∀ᶠ m in atTop, ∀ i ∈ Finset.range N, ‖(f m).coeff i - c i‖ ≤ ‖ϖ‖ ^ N`.

Rewrite using `[Filter.eventually_all_finset]`. Introduce `i _`. Use `filter_upwards [(hc i).eventually (Metric.closedBall_mem_nhds (c i) (pow_pos hr N))] with m hm`. Rewrite `hm` using `[dist_eq_norm]`. Then use the resulting hypothesis. Take `⟨m, hm, hmn⟩` from `(hev.and (eventually_ge_atTop n)).exists`.

Establish `h2 : f m - WittVector.mk p c ∈ J ^ n`. Apply `mem_span_pow_of_norm_coeff_le ϖ n` to reduce the goal to its premises. Introduce `i hi`. Use `(norm_coeff_sub_le_iff ϖ N N (f m) (WittVector.mk p c)).1 (fun j hj => ?_) i (hi.trans_le (Nat.le_mul_of_pos_right n (pow_pos hp.out.pos n)))` and prove the remaining obligations. Rewrite using `[coeff_mk]`.

Conclude with `hm j (Finset.mem_range.2 hj)`. Use `add_mem (hf' n m hmn) h2` as an intermediate fact. Rewrite `this` using `[sub_add_sub_cancel]`. Then use the resulting hypothesis.
-/
theorem isAdicComplete_weak (ϖ : 𝒪♭) (hϖ0 : ϖ ≠ 0) (hϖ1 : ‖ϖ‖ < 1) :
    IsAdicComplete (Ideal.span {(p : AInf K p), teichmuller p ϖ}) (AInf K p) := by
  set J := Ideal.span {(p : AInf K p), teichmuller p ϖ}
  have hr : 0 < ‖ϖ‖ := norm_pos_iff.2 hϖ0
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hϖ1
  refine { haus' := fun x hx => ?_, prec' := fun f hf => ?_ }
  · ext i
    rw [zero_coeff, ← norm_le_zero_iff]
    refine ge_of_tendsto ht (eventually_atTop.2 ⟨i + 1, fun N hN => ?_⟩)
    have := (smodEq_pow_iff J (N + N) x 0).1 (hx (N + N))
    rw [sub_zero] at this
    exact norm_coeff_le_of_mem_span_pow ϖ N x this i hN
  · have hf' : ∀ m n, m ≤ n → f m - f n ∈ J ^ m := fun m n h => (smodEq_pow_iff J m _ _).1 (hf h)
    have hcauchy : ∀ i, CauchySeq fun m => (f m).coeff i := by
      intro i
      rw [Metric.cauchySeq_iff']
      intro ε hε
      obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hε hϖ1
      refine ⟨(M + i + 1) + (M + i + 1), fun m hm => ?_⟩
      have h1 := norm_coeff_sub_le_of_mem_span_pow ϖ (M + i + 1) _ _ (hf' _ m hm) i (by omega)
      rw [dist_eq_norm, norm_sub_rev]
      exact h1.trans_lt ((pow_le_pow_of_le_one (norm_nonneg _) hϖ1.le (by omega)).trans_lt hM)
    choose c hc using fun i => cauchySeq_tendsto_of_complete (hcauchy i)
    refine ⟨WittVector.mk p c, fun n => ?_⟩
    rw [smodEq_pow_iff]
    set N := n * p ^ n
    have hev : ∀ᶠ m in atTop, ∀ i ∈ Finset.range N, ‖(f m).coeff i - c i‖ ≤ ‖ϖ‖ ^ N := by
      rw [Filter.eventually_all_finset]
      intro i _
      filter_upwards [(hc i).eventually (Metric.closedBall_mem_nhds (c i) (pow_pos hr N))] with m hm
      rwa [dist_eq_norm] at hm
    obtain ⟨m, hm, hmn⟩ := (hev.and (eventually_ge_atTop n)).exists
    have h2 : f m - WittVector.mk p c ∈ J ^ n := by
      apply mem_span_pow_of_norm_coeff_le ϖ n
      intro i hi
      refine (norm_coeff_sub_le_iff ϖ N N (f m) (WittVector.mk p c)).1 (fun j hj => ?_) i
        (hi.trans_le (Nat.le_mul_of_pos_right n (pow_pos hp.out.pos n)))
      rw [coeff_mk]
      exact hm j (Finset.mem_range.2 hj)
    have := add_mem (hf' n m hmn) h2
    rwa [sub_add_sub_cancel] at this

/- English proof (translation)
Use `set I := Ideal.span {(teichmuller p ϖ : AInf K p)}`. Establish `hr : 0 < ‖ϖ‖` using `norm_pos_iff.2 hϖ0`. Establish `ht` using `tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hϖ1`. Establish `hle : ∀ (n : ℕ) (d : AInf K p), d ∈ I ^ n → ∀ i, ‖d.coeff i‖ ≤ ‖ϖ‖ ^ n`. Introduce `n d hd i`.

Use `((mem_span_teichmuller_pow_iff_norm_le ϖ n d).1 hd i).trans ?_` and prove the remaining obligations. Conclude with `pow_le_pow_of_le_one (norm_nonneg _) hϖ1.le (Nat.le_mul_of_pos_right n (pow_pos hp.out.pos i))`. Use `{ haus' := fun x hx => ?_, prec' := fun f hf => ?_ }` and prove the remaining obligations. Use extensionality with `i`. Rewrite using `[zero_coeff, ← norm_le_zero_iff]`.

Use `ge_of_tendsto ht (Eventually.of_forall fun n => ?_)` and prove the remaining obligations. Use `(smodEq_pow_iff I n x 0).1 (hx n)` as an intermediate fact. Rewrite `this` using `[sub_zero]`. Conclude with `hle n x this i`. Establish `hf' : ∀ m n, m ≤ n → ∀ i, ‖(f m).coeff i - (f n).coeff i‖ ≤ ‖ϖ‖ ^ m` using `fun m n h => (norm_coeff_sub_le_iff' ϖ m _ _).2 (hle m _ ((smodEq_pow_iff I m _ _).1 (hf h)))`.

Establish `hcauchy : ∀ i, CauchySeq fun m => (f m).coeff i`. Introduce `i`. Rewrite using `[Metric.cauchySeq_iff']`. Introduce `ε hε`. Take `⟨M, hM⟩` from `exists_pow_lt_of_lt_one hε hϖ1`.

Use `⟨M, fun m hm => ?_⟩` and prove the remaining obligations. Rewrite using `[dist_eq_norm, norm_sub_rev]`. Conclude with `(hf' M m hm i).trans_lt hM`. Use `choose c hc using fun i => cauchySeq_tendsto_of_complete (hcauchy i)`. Establish `hlim : ∀ m i, ‖(f m).coeff i - c i‖ ≤ ‖ϖ‖ ^ m`.

Introduce `m i`. Conclude with `le_of_tendsto (((hc i).const_sub ((f m).coeff i)).norm) (eventually_atTop.2 ⟨m, fun n hn => hf' m n hn i⟩)`. Use `⟨WittVector.mk p c, fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[smodEq_pow_iff, mem_span_teichmuller_pow_iff_norm_le]`. Introduce `i`.

Use `set M := n * p ^ i`. Establish `hnM : n ≤ M` using `Nat.le_mul_of_pos_right n (pow_pos hp.out.pos i)`. Establish `hd : ‖(f n - f M).coeff i‖ ≤ ‖ϖ‖ ^ M` using `(mem_span_teichmuller_pow_iff_norm_le ϖ n _).1 ((smodEq_pow_iff I n _ _).1 (hf hnM)) i`. Establish `he : ∀ j, ‖(f M - WittVector.mk p c).coeff j‖ ≤ ‖ϖ‖ ^ M` using `(norm_coeff_sub_le_iff' ϖ M _ _).1 fun j => by rw [coeff_mk]; exact hlim M j`. Establish `hde` using `(norm_coeff_sub_le_iff' ϖ M ((f n - f M) + (f M - WittVector.mk p c)) (f n - f M)).2 (fun j => by rw [add_sub_cancel_left]; exact he j) i`.

Rewrite `hde` using `[sub_add_sub_cancel]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[sub_add_cancel]`. Use `_ ≤ max ‖(f n - WittVector.mk p c).coeff i - (f n - f M).coeff i‖ ‖(f n - f M).coeff i‖ := IsUltrametricDist.norm_add_le_max _ _`. Use `_ ≤ ‖ϖ‖ ^ M := max_le hde hd`.
-/
theorem isAdicComplete_teichmuller (ϖ : 𝒪♭) (hϖ0 : ϖ ≠ 0) (hϖ1 : ‖ϖ‖ < 1) :
    IsAdicComplete (Ideal.span {(teichmuller p ϖ : AInf K p)}) (AInf K p) := by
  set I := Ideal.span {(teichmuller p ϖ : AInf K p)}
  have hr : 0 < ‖ϖ‖ := norm_pos_iff.2 hϖ0
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hϖ1
  have hle : ∀ (n : ℕ) (d : AInf K p), d ∈ I ^ n → ∀ i, ‖d.coeff i‖ ≤ ‖ϖ‖ ^ n := by
    intro n d hd i
    refine ((mem_span_teichmuller_pow_iff_norm_le ϖ n d).1 hd i).trans ?_
    exact pow_le_pow_of_le_one (norm_nonneg _) hϖ1.le
      (Nat.le_mul_of_pos_right n (pow_pos hp.out.pos i))
  refine { haus' := fun x hx => ?_, prec' := fun f hf => ?_ }
  · ext i
    rw [zero_coeff, ← norm_le_zero_iff]
    refine ge_of_tendsto ht (Eventually.of_forall fun n => ?_)
    have := (smodEq_pow_iff I n x 0).1 (hx n)
    rw [sub_zero] at this
    exact hle n x this i
  · have hf' : ∀ m n, m ≤ n → ∀ i, ‖(f m).coeff i - (f n).coeff i‖ ≤ ‖ϖ‖ ^ m :=
      fun m n h => (norm_coeff_sub_le_iff' ϖ m _ _).2 (hle m _ ((smodEq_pow_iff I m _ _).1 (hf h)))
    have hcauchy : ∀ i, CauchySeq fun m => (f m).coeff i := by
      intro i
      rw [Metric.cauchySeq_iff']
      intro ε hε
      obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hε hϖ1
      refine ⟨M, fun m hm => ?_⟩
      rw [dist_eq_norm, norm_sub_rev]
      exact (hf' M m hm i).trans_lt hM
    choose c hc using fun i => cauchySeq_tendsto_of_complete (hcauchy i)
    have hlim : ∀ m i, ‖(f m).coeff i - c i‖ ≤ ‖ϖ‖ ^ m := by
      intro m i
      exact le_of_tendsto (((hc i).const_sub ((f m).coeff i)).norm)
        (eventually_atTop.2 ⟨m, fun n hn => hf' m n hn i⟩)
    refine ⟨WittVector.mk p c, fun n => ?_⟩
    rw [smodEq_pow_iff, mem_span_teichmuller_pow_iff_norm_le]
    intro i
    set M := n * p ^ i
    have hnM : n ≤ M := Nat.le_mul_of_pos_right n (pow_pos hp.out.pos i)
    have hd : ‖(f n - f M).coeff i‖ ≤ ‖ϖ‖ ^ M :=
      (mem_span_teichmuller_pow_iff_norm_le ϖ n _).1
        ((smodEq_pow_iff I n _ _).1 (hf hnM)) i
    have he : ∀ j, ‖(f M - WittVector.mk p c).coeff j‖ ≤ ‖ϖ‖ ^ M :=
      (norm_coeff_sub_le_iff' ϖ M _ _).1 fun j => by rw [coeff_mk]; exact hlim M j
    have hde := (norm_coeff_sub_le_iff' ϖ M ((f n - f M) + (f M - WittVector.mk p c))
      (f n - f M)).2 (fun j => by rw [add_sub_cancel_left]; exact he j) i
    rw [sub_add_sub_cancel] at hde
    calc ‖(f n - WittVector.mk p c).coeff i‖
        = ‖((f n - WittVector.mk p c).coeff i - (f n - f M).coeff i) + (f n - f M).coeff i‖ := by
          rw [sub_add_cancel]
      _ ≤ max ‖(f n - WittVector.mk p c).coeff i - (f n - f M).coeff i‖ ‖(f n - f M).coeff i‖ :=
          IsUltrametricDist.norm_add_le_max _ _
      _ ≤ ‖ϖ‖ ^ M := max_le hde hd

/- English proof (translation)
Set `` to `pAdicTopology K p`. Use `set I := Ideal.span {(p : AInf K p)}`. Express the relevant statement in the definitionally equal form `Tendsto _ atTop _`. Rewrite using `[(I.hasBasis_nhds_adic _).tendsto_right_iff]`. Introduce `n _`.

Break down `n with _ | n` into its components or cases. Conclude with `Eventually.of_forall fun s => ⟨(∑ i ∈ s, teichmuller p (a i) * (p : AInf K p) ^ i) - WittVector.teichmullerSeries a, by simp, by simp⟩`. Use `filter_upwards [eventually_ge_atTop (Finset.Iic n)] with s hs`. Use `⟨(∑ i ∈ s, teichmuller p (a i) * (p : AInf K p) ^ i) - WittVector.teichmullerSeries a, ?_, by simp⟩` and prove the remaining obligations. Establish `h1 : WittVector.teichmullerSeries a - ∑ i ∈ Finset.Iic n, teichmuller p (a i) * (p : AInf K p) ^ i ∈ I ^ (n + 1)`.

Rewrite using `[Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Conclude with `WittVector.dvd_sub_sum_teichmullerSeries a n`. Establish `h2 : ∑ i ∈ s \ Finset.Iic n, teichmuller p (a i) * (p : AInf K p) ^ i ∈ I ^ (n + 1)`. Use `Ideal.sum_mem _ fun i hi => ?_` and prove the remaining obligations. Establish `hi' : n + 1 ≤ i`.

Use `(Finset.mem_sdiff.1 hi).2` as an intermediate fact. Rewrite `this` using `[Finset.mem_Iic, not_le]`. Conclude with `this`. Rewrite using `[Ideal.span_singleton_pow]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton.2 (pow_dvd_pow _ hi'))`.

Rewrite using `[SetLike.mem_coe, ← Finset.sum_sdiff hs]`. Establish `e : ∑ i ∈ s \ Finset.Iic n, teichmuller p (a i) * (p : AInf K p) ^ i + ∑ i ∈ Finset.Iic n, teichmuller p (a i) * (p : AInf K p) ^ i - WittVector.teichmullerSeries a = ∑ i ∈ s \ Finset.Iic n, teichmuller p (a i) * (p : AInf K p) ^ i - (WittVector.teichmullerSeries a - ∑ i ∈ Finset …` using `by ring`. Rewrite using `[e]`. Conclude with `sub_mem h2 h1`.
-/
theorem hasSum_teichmullerSeries (a : ℕ → 𝒪♭) :
    @HasSum (AInf K p) ℕ _ (pAdicTopology K p) (fun n => teichmuller p (a n) * (p : AInf K p) ^ n)
      (WittVector.teichmullerSeries a) (SummationFilter.unconditional ℕ) := by
  let := pAdicTopology K p
  set I := Ideal.span {(p : AInf K p)}
  change Tendsto _ atTop _
  rw [(I.hasBasis_nhds_adic _).tendsto_right_iff]
  intro n _
  rcases n with _ | n
  · exact Eventually.of_forall fun s =>
      ⟨(∑ i ∈ s, teichmuller p (a i) * (p : AInf K p) ^ i) - WittVector.teichmullerSeries a,
        by simp, by simp⟩
  filter_upwards [eventually_ge_atTop (Finset.Iic n)] with s hs
  refine ⟨(∑ i ∈ s, teichmuller p (a i) * (p : AInf K p) ^ i) - WittVector.teichmullerSeries a,
    ?_, by simp⟩
  have h1 : WittVector.teichmullerSeries a -
      ∑ i ∈ Finset.Iic n, teichmuller p (a i) * (p : AInf K p) ^ i ∈ I ^ (n + 1) := by
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact WittVector.dvd_sub_sum_teichmullerSeries a n
  have h2 : ∑ i ∈ s \ Finset.Iic n, teichmuller p (a i) * (p : AInf K p) ^ i ∈
      I ^ (n + 1) := by
    refine Ideal.sum_mem _ fun i hi => ?_
    have hi' : n + 1 ≤ i := by
      have := (Finset.mem_sdiff.1 hi).2
      rw [Finset.mem_Iic, not_le] at this
      exact this
    rw [Ideal.span_singleton_pow]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton.2 (pow_dvd_pow _ hi'))
  rw [SetLike.mem_coe, ← Finset.sum_sdiff hs]
  have e : ∑ i ∈ s \ Finset.Iic n, teichmuller p (a i) * (p : AInf K p) ^ i +
      ∑ i ∈ Finset.Iic n, teichmuller p (a i) * (p : AInf K p) ^ i -
        WittVector.teichmullerSeries a =
      ∑ i ∈ s \ Finset.Iic n, teichmuller p (a i) * (p : AInf K p) ^ i -
        (WittVector.teichmullerSeries a -
          ∑ i ∈ Finset.Iic n, teichmuller p (a i) * (p : AInf K p) ^ i) := by ring
  rw [e]
  exact sub_mem h2 h1

/- English proof (translation)
Use `hasSum_teichmullerSeries (K := K) (fun n => ((_root_.frobeniusEquiv 𝒪♭ p).symm ^ n) (x.coeff n))` as an intermediate fact. Rewrite `this` using `[WittVector.teichmullerSeries_coeff_eq]`. Then use the resulting hypothesis.
-/
theorem hasSum_teichmuller_coeff (x : AInf K p) :
    @HasSum (AInf K p) ℕ _ (pAdicTopology K p)
      (fun n => teichmuller p (((_root_.frobeniusEquiv 𝒪♭ p).symm ^ n) (x.coeff n)) *
        (p : AInf K p) ^ n) x (SummationFilter.unconditional ℕ) := by
  have := hasSum_teichmullerSeries (K := K)
    (fun n => ((_root_.frobeniusEquiv 𝒪♭ p).symm ^ n) (x.coeff n))
  rwa [WittVector.teichmullerSeries_coeff_eq] at this

omit hp [IsPerfectoidField K p] in

/- English proof (translation)
Use `(@continuous_iff_continuousAt A B I.adicTopology J.adicTopology f).2 fun x => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Tendsto f (@nhds A I.adicTopology x) (@nhds B J.adicTopology (f x))`. Rewrite using `[(I.hasBasis_nhds_adic x).tendsto_iff (J.hasBasis_nhds_adic (f x))]`. Introduce `n _`. Use `⟨n, trivial, ?_⟩` and prove the remaining obligations.

Introduce and unpack `_ ⟨d, hd, rfl⟩`. Use `⟨f d, ?_, (map_add f x d).symm⟩` and prove the remaining obligations. Establish `: f d ∈ (I.map f) ^ n`. Rewrite using `[← Ideal.map_pow]`. Conclude with `Ideal.mem_map_of_mem f hd`.

Conclude with `Ideal.pow_right_mono h n this`.
-/
theorem _root_.Ideal.continuous_of_map_le {A B F : Type*} [CommRing A] [CommRing B] [FunLike F A B]
    [RingHomClass F A B] (f : F) {I : Ideal A} {J : Ideal B} (h : I.map f ≤ J) :
    @Continuous A B I.adicTopology J.adicTopology f := by
  refine (@continuous_iff_continuousAt A B I.adicTopology J.adicTopology f).2 fun x => ?_
  change Tendsto f (@nhds A I.adicTopology x) (@nhds B J.adicTopology (f x))
  rw [(I.hasBasis_nhds_adic x).tendsto_iff (J.hasBasis_nhds_adic (f x))]
  intro n _
  refine ⟨n, trivial, ?_⟩
  rintro _ ⟨d, hd, rfl⟩
  refine ⟨f d, ?_, (map_add f x d).symm⟩
  have : f d ∈ (I.map f) ^ n := by
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem f hd
  exact Ideal.pow_right_mono h n this

local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)

/- English proof (translation)
Rewrite using `[Ideal.map_span, Set.image_singleton, map_natCast]`.
-/
theorem map_frobeniusEquiv_span_p :
    Ideal.map (φ) (Ideal.span {(p : AInf K p)}) = Ideal.span {(p : AInf K p)} := by
  rw [Ideal.map_span, Set.image_singleton, map_natCast]

/- English proof (translation)
Rewrite using `[Ideal.map_span, Set.image_singleton, map_natCast]`.
-/
theorem map_frobeniusEquiv_symm_span_p :
    Ideal.map (φ).symm (Ideal.span {(p : AInf K p)}) = Ideal.span {(p : AInf K p)} := by
  rw [Ideal.map_span, Set.image_singleton, map_natCast]

/- English proof (translation)
Rewrite using `[Ideal.map_span, Set.image_singleton, WittVector.frobeniusEquiv_teichmuller]`.
-/
theorem map_frobeniusEquiv_span_teichmuller (ϖ : 𝒪♭) :
    Ideal.map (φ) (Ideal.span {(teichmuller p ϖ : AInf K p)}) =
      Ideal.span {(teichmuller p (ϖ ^ p) : AInf K p)} := by
  rw [Ideal.map_span, Set.image_singleton, WittVector.frobeniusEquiv_teichmuller]

/- English proof (translation)
Rewrite using `[Ideal.map_span, Set.image_singleton, ← WittVector.frobeniusEquiv_teichmuller, RingEquiv.symm_apply_apply]`.
-/
theorem map_frobeniusEquiv_symm_span_teichmuller_pow (ϖ : 𝒪♭) :
    Ideal.map (φ).symm (Ideal.span {(teichmuller p (ϖ ^ p) : AInf K p)}) =
      Ideal.span {(teichmuller p ϖ : AInf K p)} := by
  rw [Ideal.map_span, Set.image_singleton, ← WittVector.frobeniusEquiv_teichmuller,
    RingEquiv.symm_apply_apply]

/- English proof (translation)
Rewrite using `[Ideal.map_span, Set.image_pair, map_natCast, WittVector.frobeniusEquiv_teichmuller]`.
-/
theorem map_frobeniusEquiv_span_p_teichmuller (ϖ : 𝒪♭) :
    Ideal.map (φ) (Ideal.span {(p : AInf K p), teichmuller p ϖ}) =
      Ideal.span {(p : AInf K p), teichmuller p (ϖ ^ p)} := by
  rw [Ideal.map_span, Set.image_pair, map_natCast, WittVector.frobeniusEquiv_teichmuller]

/- English proof (translation)
Rewrite using `[Ideal.map_span, Set.image_pair, map_natCast, ← WittVector.frobeniusEquiv_teichmuller, RingEquiv.symm_apply_apply]`.
-/
theorem map_frobeniusEquiv_symm_span_p_teichmuller_pow (ϖ : 𝒪♭) :
    Ideal.map (φ).symm (Ideal.span {(p : AInf K p), teichmuller p (ϖ ^ p)}) =
      Ideal.span {(p : AInf K p), teichmuller p ϖ} := by
  rw [Ideal.map_span, Set.image_pair, map_natCast, ← WittVector.frobeniusEquiv_teichmuller,
    RingEquiv.symm_apply_apply]

/- English proof (translation)
The claim follows from `Ideal.continuous_of_map_le (φ) map_frobeniusEquiv_span_p.le`.
-/
theorem continuous_frobeniusEquiv_pAdic :
    @Continuous (AInf K p) (AInf K p) (pAdicTopology K p) (pAdicTopology K p) (φ) :=
  Ideal.continuous_of_map_le (φ) map_frobeniusEquiv_span_p.le

/- English proof (translation)
The claim follows from `Ideal.continuous_of_map_le (φ).symm map_frobeniusEquiv_symm_span_p.le`.
-/
theorem continuous_frobeniusEquiv_symm_pAdic :
    @Continuous (AInf K p) (AInf K p) (pAdicTopology K p) (pAdicTopology K p) (φ).symm :=
  Ideal.continuous_of_map_le (φ).symm map_frobeniusEquiv_symm_span_p.le

/- English proof (translation)
Rewrite using `[← norm_pos_iff, norm_pow]`. Conclude with `pow_pos (norm_pos_iff.2 hϖ0) p`.
-/
theorem pow_ne_zero_of_norm (ϖ : 𝒪♭) (hϖ0 : ϖ ≠ 0) : ϖ ^ p ≠ 0 := by
  rw [← norm_pos_iff, norm_pow]
  exact pow_pos (norm_pos_iff.2 hϖ0) p

/- English proof (translation)
Rewrite using `[norm_pow]`. Conclude with `pow_lt_one₀ (norm_nonneg _) hϖ1 hp.out.ne_zero`.
-/
theorem norm_pow_p_lt_one (ϖ : 𝒪♭) (hϖ1 : ‖ϖ‖ < 1) : ‖ϖ ^ p‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) hϖ1 hp.out.ne_zero

/- English proof (translation)
Use `Ideal.continuous_of_map_le (φ) ?_` and prove the remaining obligations. Rewrite using `[map_frobeniusEquiv_span_teichmuller, Ideal.span_singleton_le_span_singleton]`. Conclude with `map_dvd (teichmuller p) (dvd_pow_self ϖ hp.out.ne_zero)`.
-/
theorem continuous_frobeniusEquiv_teichmullerAdic (ϖ : 𝒪♭) :
    @Continuous (AInf K p) (AInf K p) (teichmullerAdicTopology ϖ) (teichmullerAdicTopology ϖ) (φ) := by
  refine Ideal.continuous_of_map_le (φ) ?_
  rw [map_frobeniusEquiv_span_teichmuller, Ideal.span_singleton_le_span_singleton]
  exact map_dvd (teichmuller p) (dvd_pow_self ϖ hp.out.ne_zero)

/- English proof (translation)
Establish `h` using `Ideal.continuous_of_map_le (φ).symm (map_frobeniusEquiv_symm_span_teichmuller_pow ϖ).le`. Rewrite `h` using `[← teichmullerAdicTopology, ← teichmullerAdicTopology, teichmullerAdicTopology_eq (ϖ ^ p) ϖ (pow_ne_zero_of_norm ϖ hϖ0) (norm_pow_p_lt_one ϖ hϖ1) hϖ0 hϖ1]`. Then use the resulting hypothesis.
-/
theorem continuous_frobeniusEquiv_symm_teichmullerAdic (ϖ : 𝒪♭) (hϖ0 : ϖ ≠ 0) (hϖ1 : ‖ϖ‖ < 1) :
    @Continuous (AInf K p) (AInf K p) (teichmullerAdicTopology ϖ) (teichmullerAdicTopology ϖ)
      (φ).symm := by
  have h := Ideal.continuous_of_map_le (φ).symm (map_frobeniusEquiv_symm_span_teichmuller_pow ϖ).le
  rwa [← teichmullerAdicTopology, ← teichmullerAdicTopology,
    teichmullerAdicTopology_eq (ϖ ^ p) ϖ (pow_ne_zero_of_norm ϖ hϖ0) (norm_pow_p_lt_one ϖ hϖ1)
      hϖ0 hϖ1] at h

/- English proof (translation)
Establish `h` using `Ideal.continuous_of_map_le (φ) (map_frobeniusEquiv_span_p_teichmuller ϖ).le`. Rewrite `h` using `[← weakTopology_eq_adicTopology ϖ hϖ0 hϖ1, ← weakTopology_eq_adicTopology (ϖ ^ p) (pow_ne_zero_of_norm ϖ hϖ0) (norm_pow_p_lt_one ϖ hϖ1)]`. Then use the resulting hypothesis.
-/
theorem continuous_frobeniusEquiv_weak (ϖ : 𝒪♭) (hϖ0 : ϖ ≠ 0) (hϖ1 : ‖ϖ‖ < 1) :
    @Continuous (AInf K p) (AInf K p) (weakTopology K p) (weakTopology K p) (φ) := by
  have h := Ideal.continuous_of_map_le (φ) (map_frobeniusEquiv_span_p_teichmuller ϖ).le
  rwa [← weakTopology_eq_adicTopology ϖ hϖ0 hϖ1,
    ← weakTopology_eq_adicTopology (ϖ ^ p) (pow_ne_zero_of_norm ϖ hϖ0)
      (norm_pow_p_lt_one ϖ hϖ1)] at h

/- English proof (translation)
Establish `h` using `Ideal.continuous_of_map_le (φ).symm (map_frobeniusEquiv_symm_span_p_teichmuller_pow ϖ).le`. Rewrite `h` using `[← weakTopology_eq_adicTopology ϖ hϖ0 hϖ1, ← weakTopology_eq_adicTopology (ϖ ^ p) (pow_ne_zero_of_norm ϖ hϖ0) (norm_pow_p_lt_one ϖ hϖ1)]`. Then use the resulting hypothesis.
-/
theorem continuous_frobeniusEquiv_symm_weak (ϖ : 𝒪♭) (hϖ0 : ϖ ≠ 0) (hϖ1 : ‖ϖ‖ < 1) :
    @Continuous (AInf K p) (AInf K p) (weakTopology K p) (weakTopology K p) (φ).symm := by
  have h := Ideal.continuous_of_map_le (φ).symm
    (map_frobeniusEquiv_symm_span_p_teichmuller_pow ϖ).le
  rwa [← weakTopology_eq_adicTopology ϖ hϖ0 hϖ1,
    ← weakTopology_eq_adicTopology (ϖ ^ p) (pow_ne_zero_of_norm ϖ hϖ0)
      (norm_pow_p_lt_one ϖ hϖ1)] at h

end AInf

end GroundTheory.PAdicHodge
