import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace Domination

section Charts

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N N' : ℕ}
  {x : Fin (N + 1) → Ω} {x' : Fin (N' + 1) → Ω}

/- English proof (translation)
Take `⟨j, hj⟩` from `J.2.1`. Rewrite using `[twistMod_eq_span 0 J hj, zpow_zero, Submodule.mem_span_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`. Rewrite using `[chartRing_smul_def, mul_one]`.

Conclude with `a.2`. Introduce `hz`. Conclude with `⟨⟨z, hz⟩, by rw [chartRing_smul_def, mul_one]⟩`.
-/
theorem mem_twistMod_zero_iff {R : Type*} [CommRing R] [Algebra R Ω] {y : Fin (N' + 1) → Ω}
    (J : Chart y) (z : Ω) : z ∈ twistMod R y 0 J ↔ z ∈ chartRing R y J := by
  obtain ⟨j, hj⟩ := J.2.1
  rw [twistMod_eq_span 0 J hj, zpow_zero, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    rw [chartRing_smul_def, mul_one]
    exact a.2
  · intro hz
    exact ⟨⟨z, hz⟩, by rw [chartRing_smul_def, mul_one]⟩

abbrev pullPow (x : Fin (N + 1) → Ω) (x' : Fin (N' + 1) → Ω) (n : ℕ) (J : Chart x') :
    Submodule (chartRing S x' J) Ω :=
  ((pullSys (S := S) x x').pow n).sub J

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pullPow_succ (n : ℕ) (J : Chart x') :
    pullPow (S := S) x x' (n + 1) J = Submodule.span _ {z | ∃ q ∈ (pullSys (S := S) x x').sub J,
      ∃ y ∈ pullPow (S := S) x x' n J, z = q • y} := rfl

/- English proof (translation)
The claim follows from `mem_twistMod_zero_iff J z`.
-/
theorem mem_pullPow_zero_iff (J : Chart x') (z : Ω) :
    z ∈ pullPow (S := S) x x' 0 J ↔ z ∈ chartRing S x' J :=
  mem_twistMod_zero_iff J z

/- English proof (translation)
Rewrite using `[pullPow_succ]`. Conclude with `Submodule.subset_span ⟨x l, Submodule.subset_span ⟨l, rfl⟩, 1, (mem_pullPow_zero_iff J 1).mpr (one_mem _), by rw [smul_eq_mul, mul_one]⟩`.
-/
theorem coord_mem_pullPow_one (J : Chart x') (l : Fin (N + 1)) : x l ∈ pullPow (S := S) x x' 1 J := by
  rw [pullPow_succ]
  exact Submodule.subset_span ⟨x l, Submodule.subset_span ⟨l, rfl⟩, 1,
    (mem_pullPow_zero_iff J 1).mpr (one_mem _), by rw [smul_eq_mul, mul_one]⟩

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `y hy`. Establish `hy'` using `(mem_pullPow_zero_iff J y).mp hy`.

Establish `h : z * y = (⟨y, hy'⟩ : chartRing S x' J) • z`. Rewrite using `[chartRing_smul_def, mul_comm]`. Rewrite using `[h]`. Conclude with `Submodule.smul_mem _ _ hz`. Consider the case `succ m ih`.

Introduce `y hy`. Rewrite `hy` using `[pullPow_succ]`. Rewrite using `[← Nat.add_assoc, pullPow_succ]`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem w hw`.

Take `⟨q, hq, y', hy', rfl⟩` from `hw`. Use `Submodule.subset_span ⟨q, hq, z * y', ih hy', ?_⟩` and prove the remaining obligations. Simplify using `only [smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `zero => rw [mul_zero]`.

Conclude with `Submodule.zero_mem _`. Consider the case `add a b _ _ ha hb => rw [mul_add]`. Conclude with `Submodule.add_mem _ ha hb`. Consider the case `smul c a _ ha`. Establish `h : z * (c • a) = c • (z * a)` using `by simp only [chartRing_smul_def]; ring`.

Rewrite using `[h]`. Conclude with `Submodule.smul_mem _ _ ha`.
-/
theorem mul_mem_pullPow (J : Chart x') {n : ℕ} {z : Ω} (hz : z ∈ pullPow (S := S) x x' n J) :
    ∀ (m : ℕ) {y : Ω}, y ∈ pullPow (S := S) x x' m J → z * y ∈ pullPow (S := S) x x' (n + m) J := by
  intro m
  induction m with
  | zero =>
    intro y hy
    have hy' := (mem_pullPow_zero_iff J y).mp hy
    have h : z * y = (⟨y, hy'⟩ : chartRing S x' J) • z := by
      rw [chartRing_smul_def, mul_comm]
    rw [h]
    exact Submodule.smul_mem _ _ hz
  | succ m ih =>
    intro y hy
    rw [pullPow_succ] at hy
    rw [← Nat.add_assoc, pullPow_succ]
    induction hy using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨q, hq, y', hy', rfl⟩ := hw
      refine Submodule.subset_span ⟨q, hq, z * y', ih hy', ?_⟩
      simp only [smul_eq_mul]
      ring
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [mul_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha =>
      have h : z * (c • a) = c • (z * a) := by simp only [chartRing_smul_def]; ring
      rw [h]
      exact Submodule.smul_mem _ _ ha

/- English proof (translation)
The claim follows from `| 0 => by rw [pow_zero]; exact (mem_pullPow_zero_iff J 1).mpr (one_mem _) | n + 1 => by rw [pow_succ] exact mul_mem_pullPow J (pow_mem_pullPow J l n) 1 (coord_mem_pullPow_one J l)`.
-/
theorem pow_mem_pullPow (J : Chart x') (l : Fin (N + 1)) :
    ∀ n : ℕ, x l ^ n ∈ pullPow (S := S) x x' n J
  | 0 => by rw [pow_zero]; exact (mem_pullPow_zero_iff J 1).mpr (one_mem _)
  | n + 1 => by
    rw [pow_succ]
    exact mul_mem_pullPow J (pow_mem_pullPow J l n) 1 (coord_mem_pullPow_one J l)

/- English proof (translation)
Simplify using `only [ampleChart, one_mul, Set.mem_ofPred_eq]`.
-/
theorem mem_ampleChart_iff (J : Chart x') (l : Fin (N + 1)) (a : Ω) :
    a ∈ ampleChart (pullSys (S := S) x x') 1 (x l) J ↔ ∃ n : ℕ, a * x l ^ n ∈ pullPow (S := S) x x' n J := by
  simp only [ampleChart, one_mul, Set.mem_ofPred_eq]

def ampleSub (J : Chart x') (l : Fin (N + 1)) : Subalgebra S Ω where
  carrier := ampleChart (pullSys (S := S) x x') 1 (x l) J
  mul_mem' := by
    intro a b ha hb
    rw [mem_ampleChart_iff] at ha hb ⊢
    obtain ⟨n, hn⟩ := ha
    obtain ⟨m, hm⟩ := hb
    refine ⟨n + m, ?_⟩
    have h := mul_mem_pullPow J hn m hm
    rw [show a * x l ^ n * (b * x l ^ m) = a * b * x l ^ (n + m) by ring] at h
    exact h
  add_mem' := by
    intro a b ha hb
    rw [mem_ampleChart_iff] at ha hb ⊢
    obtain ⟨n, hn⟩ := ha
    obtain ⟨m, hm⟩ := hb
    refine ⟨n + m, ?_⟩
    have h1 := mul_mem_pullPow J hn m (pow_mem_pullPow J l m)
    have h2 := mul_mem_pullPow J hm n (pow_mem_pullPow J l n)
    rw [Nat.add_comm m n] at h2
    have h := Submodule.add_mem _ h1 h2
    rw [show a * x l ^ n * x l ^ m + b * x l ^ m * x l ^ n = (a + b) * x l ^ (n + m) by ring] at h
    exact h
  algebraMap_mem' s := by
    show _ ∈ ampleChart _ _ _ _
    rw [mem_ampleChart_iff]
    refine ⟨0, ?_⟩
    rw [pow_zero, mul_one, mem_pullPow_zero_iff]
    exact Subalgebra.algebraMap_mem _ s

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `a ha`. Conclude with `mem_ampleBase_of_mem_chartRing hi ha`. Rewrite using `[ampleBase, Algebra.adjoin_le_iff]`. Introduce and unpack `_ ⟨l, rfl⟩`.

Conclude with `(ratio (S := S) hi l).2`.
-/
theorem chartRing_eq_ampleBase {i : Fin (N + 1)} (hi : x i ≠ 0) :
    chartRing S x (singleChart hi) = ampleBase (S := S) x i := by
  apply le_antisymm
  · intro a ha
    exact mem_ampleBase_of_mem_chartRing hi ha
  · rw [ampleBase, Algebra.adjoin_le_iff]
    rintro _ ⟨l, rfl⟩
    exact (ratio (S := S) hi l).2

/- English proof (translation)
Establish `hfg : (chartRing S x (singleChart hi)).FG`. Rewrite using `[chartRing_eq_ampleBase hi, ampleBase]`. Use `⟨Finset.univ.image fun l => x l / x i, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.coe_image, Finset.coe_univ, Set.image_univ]`. Establish `: Algebra.FiniteType S (chartRing S x (singleChart hi))` using `⟨(Subalgebra.fg_top _).mpr hfg⟩`.

Conclude with `Algebra.FiniteType.isNoetherianRing S _`.
-/
theorem isNoetherianRing_chartRing [IsNoetherianRing S] {i : Fin (N + 1)} (hi : x i ≠ 0) :
    IsNoetherianRing (chartRing S x (singleChart hi)) := by
  classical
  have hfg : (chartRing S x (singleChart hi)).FG := by
    rw [chartRing_eq_ampleBase hi, ampleBase]
    refine ⟨Finset.univ.image fun l => x l / x i, ?_⟩
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have : Algebra.FiniteType S (chartRing S x (singleChart hi)) := ⟨(Subalgebra.fg_top _).mpr hfg⟩
  exact Algebra.FiniteType.isNoetherianRing S _

variable {i : Fin (N + 1)} (hi : x i ≠ 0) {j : Fin (N' + 1)} (hj : x' j ≠ 0)

/- English proof (translation)
Establish `h` using `mem_ampleBase_of_mem_chartRing (S := S) hj hz`. Rewrite `h` using `[ampleBase]`. Use `clear hz`. Proceed by induction on `h using Algebra.adjoin_induction with`. Consider the case `mem z hz`.

Take `⟨k, rfl⟩` from `hz`. Conclude with `(ratio (S := chartRing S x (singleChart hi)) hj k).2`. Consider the case `algebraMap s`. Conclude with `Subalgebra.algebraMap_mem _ (algebraMap S (chartRing S x (singleChart hi)) s)`. Consider the case `add a b _ _ ha hb => exact add_mem ha hb`.

Consider the case `mul a b _ _ ha hb => exact mul_mem ha hb`.
-/
theorem mem_chartRing_base_of_mem (z : Ω) (hz : z ∈ chartRing S x' (singleChart hj)) :
    z ∈ chartRing (chartRing S x (singleChart hi)) x' (singleChart hj) := by
  have h := mem_ampleBase_of_mem_chartRing (S := S) hj hz
  rw [ampleBase] at h
  clear hz
  induction h using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨k, rfl⟩ := hz
    exact (ratio (S := chartRing S x (singleChart hi)) hj k).2
  | algebraMap s =>
    exact Subalgebra.algebraMap_mem _ (algebraMap S (chartRing S x (singleChart hi)) s)
  | add a b _ _ ha hb => exact add_mem ha hb
  | mul a b _ _ ha hb => exact mul_mem ha hb

/- English proof (translation)
The claim follows from `Subalgebra.algebraMap_mem _ (⟨z, hz⟩ : chartRing S x (singleChart hi))`.
-/
theorem mem_chartRing_base_of_base (z : Ω) (hz : z ∈ chartRing S x (singleChart hi)) :
    z ∈ chartRing (chartRing S x (singleChart hi)) x' (singleChart hj) :=
  Subalgebra.algebraMap_mem _ (⟨z, hz⟩ : chartRing S x (singleChart hi))

/- English proof (translation)
The claim follows from `| 0, y, hy => by rw [pow_zero, div_one] exact mem_chartRing_base_of_mem hi hj y ((mem_pullPow_zero_iff _ y).mp hy) | n + 1, y, hy => by rw [pullPow_succ] at hy induction hy using Submodule.span_induction with | mem w hw => obtain ⟨q, hq, y', hy', rfl⟩ := hw change q ∈ Submodule.s …`.
-/
theorem div_mem_of_mem_pullPow : ∀ (n : ℕ) {y : Ω}, y ∈ pullPow (S := S) x x' n (singleChart hj) →
    y / x i ^ n ∈ chartRing (chartRing S x (singleChart hi)) x' (singleChart hj)
  | 0, y, hy => by
    rw [pow_zero, div_one]
    exact mem_chartRing_base_of_mem hi hj y ((mem_pullPow_zero_iff _ y).mp hy)
  | n + 1, y, hy => by
    rw [pullPow_succ] at hy
    induction hy using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨q, hq, y', hy', rfl⟩ := hw
      change q ∈ Submodule.span _ (Set.range x) at hq
      have hq' : q / x i ∈ chartRing (chartRing S x (singleChart hi)) x' (singleChart hj) := by
        induction hq using Submodule.span_induction with
        | mem q hq =>
          obtain ⟨l, rfl⟩ := hq
          exact mem_chartRing_base_of_base hi hj _ (ratio (S := S) hi l).2
        | zero => rw [zero_div]; exact zero_mem _
        | add a b _ _ ha hb => rw [add_div]; exact add_mem ha hb
        | smul c a _ ha =>
          rw [chartRing_smul_def, mul_div_assoc]
          exact mul_mem (mem_chartRing_base_of_mem hi hj _ c.2) ha
      have h := mul_mem hq' (div_mem_of_mem_pullPow n hy')
      rw [smul_eq_mul, pow_succ]
      rwa [div_mul_div_comm, mul_comm (x i) (x i ^ n)] at h
    | zero => rw [zero_div]; exact zero_mem _
    | add a b _ _ ha hb => rw [add_div]; exact add_mem ha hb
    | smul c a _ ha =>
      rw [chartRing_smul_def, mul_div_assoc]
      exact mul_mem (mem_chartRing_base_of_mem hi hj _ c.2) ha

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `ha`. Rewrite `ha` using `[mem_ampleChart_iff]`. Take `⟨n, hn⟩` from `ha`. Establish `h` using `div_mem_of_mem_pullPow hi hj n hn`.

Rewrite `h` using `[mul_div_assoc, div_self (pow_ne_zero n hi), mul_one]`. Then use the resulting hypothesis. Introduce `ha`. Establish `hA : chartRing S x (singleChart hi) ≤ ampleSub (S` using `S) (x := x) (singleChart hj) i := by`. Rewrite using `[chartRing_eq_ampleBase hi, ampleBase, Algebra.adjoin_le_iff]`. Introduce and unpack `_ ⟨l, rfl⟩`.

Use `show _ ∈ ampleChart _ _ _ _`. Rewrite using `[mem_ampleChart_iff]`. Use `⟨1, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_one, div_mul_cancel₀ _ hi]`. Conclude with `coord_mem_pullPow_one _ l`.

Establish `h` using `mem_ampleBase_of_mem_chartRing (S := chartRing S x (singleChart hi)) hj ha`. Rewrite `h` using `[ampleBase]`. Use `clear ha`. Proceed by induction on `h using Algebra.adjoin_induction with`. Consider the case `mem z hz`.

Take `⟨k, rfl⟩` from `hz`. Rewrite using `[mem_ampleChart_iff]`. Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_zero, mul_one, mem_pullPow_zero_iff]`. Conclude with `(ratio (S := S) hj k).2`.

Consider the case `algebraMap a0 => exact hA a0.2`. Consider the case `add a b _ _ ha hb => exact (ampleSub (S := S) (x := x) (singleChart hj) i).add_mem ha hb`. Consider the case `mul a b _ _ ha hb => exact (ampleSub (S := S) (x := x) (singleChart hj) i).mul_mem ha hb`.
-/
theorem mem_ampleChart_single_iff (a : Ω) :
    a ∈ ampleChart (pullSys (S := S) x x') 1 (x i) (singleChart hj) ↔
      a ∈ chartRing (chartRing S x (singleChart hi)) x' (singleChart hj) := by
  constructor
  · intro ha
    rw [mem_ampleChart_iff] at ha
    obtain ⟨n, hn⟩ := ha
    have h := div_mem_of_mem_pullPow hi hj n hn
    rwa [mul_div_assoc, div_self (pow_ne_zero n hi), mul_one] at h
  · intro ha
    have hA : chartRing S x (singleChart hi) ≤ ampleSub (S := S) (x := x) (singleChart hj) i := by
      rw [chartRing_eq_ampleBase hi, ampleBase, Algebra.adjoin_le_iff]
      rintro _ ⟨l, rfl⟩
      show _ ∈ ampleChart _ _ _ _
      rw [mem_ampleChart_iff]
      refine ⟨1, ?_⟩
      rw [pow_one, div_mul_cancel₀ _ hi]
      exact coord_mem_pullPow_one _ l
    have h := mem_ampleBase_of_mem_chartRing (S := chartRing S x (singleChart hi)) hj ha
    rw [ampleBase] at h
    clear ha
    induction h using Algebra.adjoin_induction with
    | mem z hz =>
      obtain ⟨k, rfl⟩ := hz
      rw [mem_ampleChart_iff]
      refine ⟨0, ?_⟩
      rw [pow_zero, mul_one, mem_pullPow_zero_iff]
      exact (ratio (S := S) hj k).2
    | algebraMap a0 => exact hA a0.2
    | add a b _ _ ha hb => exact (ampleSub (S := S) (x := x) (singleChart hj) i).add_mem ha hb
    | mul a b _ _ ha hb => exact (ampleSub (S := S) (x := x) (singleChart hj) i).mul_mem ha hb

/- English proof (translation)
Rewrite using `[domRing, ampleRing, Set.mem_iInter]`. Prove the components needed by the constructor for the conclusion. Introduce `hb J`. Take `⟨j, hjJ⟩` from `J.2.1`. Establish `hj : x' j ≠ 0` using `(mem_support x').mp (J.2.2 hjJ)`.

Establish `h1` using `(mem_ampleChart_single_iff hi hj b).mp (hb (singleChart hj))`. Conclude with `chartRing_mono (Finset.singleton_subset_iff.mpr hjJ) h1`. Introduce `hb J`. Take `⟨j, hjJ⟩` from `J.2.1`. Establish `hj : x' j ≠ 0` using `(mem_support x').mp (J.2.2 hjJ)`.

Establish `h1` using `(mem_ampleChart_single_iff hi hj b).mpr (hb (singleChart hj))`. Rewrite `h1`, the goal using `[mem_ampleChart_iff]`. Take `⟨n, hn⟩` from `h1`. Conclude with `⟨n, ((pullSys (S := S) x x').pow n).mono _ _ (Finset.singleton_subset_iff.mpr hjJ) _ hn⟩`.
-/
theorem mem_domRing_iff (b : Ω) : b ∈ domRing S x x' i ↔
    ∀ J : Chart x', b ∈ chartRing (chartRing S x (singleChart hi)) x' J := by
  rw [domRing, ampleRing, Set.mem_iInter]
  constructor
  · intro hb J
    obtain ⟨j, hjJ⟩ := J.2.1
    have hj : x' j ≠ 0 := (mem_support x').mp (J.2.2 hjJ)
    have h1 := (mem_ampleChart_single_iff hi hj b).mp (hb (singleChart hj))
    exact chartRing_mono (Finset.singleton_subset_iff.mpr hjJ) h1
  · intro hb J
    obtain ⟨j, hjJ⟩ := J.2.1
    have hj : x' j ≠ 0 := (mem_support x').mp (J.2.2 hjJ)
    have h1 := (mem_ampleChart_single_iff hi hj b).mpr (hb (singleChart hj))
    rw [mem_ampleChart_iff] at h1 ⊢
    obtain ⟨n, hn⟩ := h1
    exact ⟨n, ((pullSys (S := S) x x').pow n).mono _ _ (Finset.singleton_subset_iff.mpr hjJ) _ hn⟩

omit [Algebra S Ω] in

/- English proof (translation)
Simplify using `only [SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem]`. Conclude with `forall_congr' fun J => mem_twistMod_zero_iff J z`.
-/
theorem mem_secs_twistBundle_zero_iff {R : Type*} [CommRing R] [Algebra R Ω] (z : Ω) :
    z ∈ (twistBundle R x' 0).secs ↔ ∀ J : Chart x', z ∈ chartRing R x' J := by
  simp only [SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem]
  exact forall_congr' fun J => mem_twistMod_zero_iff J z

variable (x') in

def domSub : Subalgebra (chartRing S x (singleChart hi)) Ω :=
  ⨅ J : Chart x', chartRing (chartRing S x (singleChart hi)) x' J

/- English proof (translation)
Rewrite using `[domSub, Algebra.mem_iInf, mem_domRing_iff hi]`.
-/
theorem mem_domSub_iff (b : Ω) : b ∈ domSub (S := S) x' hi ↔ b ∈ domRing S x x' i := by
  rw [domSub, Algebra.mem_iInf, mem_domRing_iff hi]

/- English proof (translation)
Use `isNoetherianRing_chartRing (S := S) hi` as an intermediate fact. Establish `h` using `(hF (chartRing S x (singleChart hi)) Ω N' x' (twistBundle _ x' 0) hx').1`. Rewrite `h` using `[Module.Finite.iff_fg]`. Establish `heq : Subalgebra.toSubmodule (domSub (S` using `S) x' hi) = (twistBundle _ x' 0).secs := by`. Use extensionality with `z`.

Rewrite using `[Subalgebra.mem_toSubmodule, mem_secs_twistBundle_zero_iff, domSub, Algebra.mem_iInf]`. Rewrite using `[heq]`. Conclude with `h`.
-/
theorem fg_domSub [IsNoetherianRing S] (hF : FiniteSections.Statement.{w, w}) (hx' : x' ≠ 0) :
    (Subalgebra.toSubmodule (domSub (S := S) x' hi)).FG := by
  have := isNoetherianRing_chartRing (S := S) hi
  have h := (hF (chartRing S x (singleChart hi)) Ω N' x' (twistBundle _ x' 0) hx').1
  rw [Module.Finite.iff_fg] at h
  have heq : Subalgebra.toSubmodule (domSub (S := S) x' hi) = (twistBundle _ x' 0).secs := by
    ext z
    rw [Subalgebra.mem_toSubmodule, mem_secs_twistBundle_zero_iff, domSub, Algebra.mem_iInf]
  rw [heq]
  exact h

end Charts

section Clauses

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N N' : ℕ}
  {x : Fin (N + 1) → Ω} {x' : Fin (N' + 1) → Ω}

/- English proof (translation)
Take `⟨t, ht⟩` from `hB`. Establish `h' : ∀ g : t, ∃ d ∈ P, d * (g : Ω) ∈ A` using `fun g => h g (by rw [← ht]; exact Submodule.subset_span (Finset.mem_coe.mpr g.2))`. Use `choose d hdP hdA using h'`. Use `⟨∏ g, d g, Finset.prod_induction _ (· ∈ P) (fun a b ha hb => hPmul a ha b hb) hP1 fun g _ => hdP g, ?_⟩` and prove the remaining obligations. Introduce `b hb`.

Rewrite `hb` using `[← ht]`. Proceed by induction on `hb using Submodule.span_induction with`. Consider the case `mem g hg`. Establish `hg' : g ∈ t` using `Finset.mem_coe.mp hg`. Rewrite using `[← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ ⟨g, hg'⟩), show ∀ p q r : Ω, p * q * r = q * (p * r) from fun p q r => by ring]`.

Conclude with `A.mul_mem (Finset.prod_induction _ (· ∈ A) (fun a b ha hb => A.mul_mem ha hb) A.one_mem fun g' _ => hPA _ (hdP g')) (hdA ⟨g, hg'⟩)`. Consider the case `zero => rw [mul_zero]`. Conclude with `A.zero_mem`. Consider the case `add a b _ _ ha hb => rw [mul_add]`. Conclude with `A.add_mem ha hb`.

Consider the case `smul c a _ ha`. Express the relevant statement in the definitionally equal form `(∏ g, d g) * ((c : Ω) * a) ∈ A`. Rewrite using `[mul_left_comm]`. Conclude with `A.mul_mem c.2 ha`.
-/
theorem exists_clear {A : Subalgebra S Ω} {B : Submodule A Ω} (hB : B.FG) (P : Set Ω) (hP1 : (1 : Ω) ∈ P)
    (hPmul : ∀ a ∈ P, ∀ b ∈ P, a * b ∈ P) (hPA : ∀ a ∈ P, a ∈ A)
    (h : ∀ g ∈ B, ∃ d ∈ P, d * g ∈ A) : ∃ d ∈ P, ∀ b ∈ B, d * b ∈ A := by
  classical
  obtain ⟨t, ht⟩ := hB
  have h' : ∀ g : t, ∃ d ∈ P, d * (g : Ω) ∈ A := fun g =>
    h g (by rw [← ht]; exact Submodule.subset_span (Finset.mem_coe.mpr g.2))
  choose d hdP hdA using h'
  refine ⟨∏ g, d g, Finset.prod_induction _ (· ∈ P) (fun a b ha hb => hPmul a ha b hb) hP1
    fun g _ => hdP g, ?_⟩
  intro b hb
  rw [← ht] at hb
  induction hb using Submodule.span_induction with
  | mem g hg =>
    have hg' : g ∈ t := Finset.mem_coe.mp hg
    rw [← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ ⟨g, hg'⟩),
      show ∀ p q r : Ω, p * q * r = q * (p * r) from fun p q r => by ring]
    exact A.mul_mem (Finset.prod_induction _ (· ∈ A) (fun a b ha hb => A.mul_mem ha hb) A.one_mem
      fun g' _ => hPA _ (hdP g')) (hdA ⟨g, hg'⟩)
  | zero => rw [mul_zero]; exact A.zero_mem
  | add a b _ _ ha hb => rw [mul_add]; exact A.add_mem ha hb
  | smul c a _ ha =>
    change (∏ g, d g) * ((c : Ω) * a) ∈ A
    rw [mul_left_comm]
    exact A.mul_mem c.2 ha

/- English proof (translation)
Introduce `z hz`. Simplify using `only [pullSecs, Submodule.mem_iInf] at hz`. Simplify using `only [SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem]`. Introduce `I`. Take `⟨i, hiI⟩` from `I.2.1`.

Establish `hi : x i ≠ 0` using `(mem_support x).mp (I.2.2 hiI)`. Use `L'.mono (singleChart hi) I (Finset.singleton_subset_iff.mpr hiI) _ ?_` and prove the remaining obligations. Establish `hz'` using `hz i hi`. Use `clear hz`. Proceed by induction on `hz' using Submodule.span_induction with`.

Consider the case `mem w hw`. Take `⟨b, hb, l, hl, rfl⟩` from `hw`. Conclude with `h i hi b hb l hl`. Consider the case `zero => rw [mul_zero]`. Conclude with `zero_mem _`.

Consider the case `add a b _ _ ha hb => rw [mul_add]`. Conclude with `add_mem ha hb`. Consider the case `smul s a _ ha`. Rewrite using `[mul_smul_comm]`. Conclude with `Submodule.smul_of_tower_mem _ s ha`.
-/
theorem mul_mem_secs_of_pullSecs {L L' : SubSystem S x Ω} {κ : Ω}
    (h : ∀ (i : Fin (N + 1)) (hi : x i ≠ 0), ∀ b ∈ domRing S x x' i, ∀ l ∈ L.sub (singleChart hi),
      κ * (b * l) ∈ L'.sub (singleChart hi)) :
    ∀ z ∈ pullSecs x' L, κ * z ∈ L'.secs := by
  intro z hz
  simp only [pullSecs, Submodule.mem_iInf] at hz
  simp only [SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem]
  intro I
  obtain ⟨i, hiI⟩ := I.2.1
  have hi : x i ≠ 0 := (mem_support x).mp (I.2.2 hiI)
  refine L'.mono (singleChart hi) I (Finset.singleton_subset_iff.mpr hiI) _ ?_
  have hz' := hz i hi
  clear hz
  induction hz' using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨b, hb, l, hl, rfl⟩ := hw
    exact h i hi b hb l hl
  | zero => rw [mul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
  | smul s a _ ha =>
    rw [mul_smul_comm]
    exact Submodule.smul_of_tower_mem _ s ha

omit [Algebra S Ω] in

/- English proof (translation)
Take `⟨I, -⟩` from `h 0`. Take `⟨j, hj⟩` from `I.2.1`. Introduce `hy`. Conclude with `(mem_support y).mp (I.2.2 hj) (by rw [hy]; rfl)`.
-/
theorem ne_zero_of_isBirationalPt [Algebra S Ω] {y : Fin (N' + 1) → Ω} (h : IsBirationalPt S y) :
    y ≠ 0 := by
  obtain ⟨I, -⟩ := h 0
  obtain ⟨j, hj⟩ := I.2.1
  intro hy
  exact (mem_support y).mp (I.2.2 hj) (by rw [hy]; rfl)

/- English proof (translation)
Take `⟨I, a, b, ⟨f, s, e, hs, hf, hse, rfl⟩, ⟨f', s', e', hs', hf', hse', rfl⟩, hb0, hgb⟩` from `hbir g`. Establish `hs0` using `eval_ne_zero_of_mem_monos I hs`. Establish `hs0'` using `eval_ne_zero_of_mem_monos I hs'`. Establish `hf'0 : aeval x f' ≠ 0`. Introduce `h`.

Apply `hb0` to reduce the goal to its premises. Rewrite using `[h, zero_div]`. Establish `key : aeval x s * aeval x f' * g = aeval x f * aeval x s'`. Combine the equalities or inequalities in the displayed calculation. Clear the denominators using the available nonvanishing facts.

Use `_ = aeval x s * aeval x s' * (aeval x f / aeval x s) := by rw [hgb]`. Use `_ = aeval x f * aeval x s' := by`. Clear the denominators using the available nonvanishing facts. Use `⟨aeval x (s * f') / x i ^ (e + e'), ⟨s * f', e + e', hse.mul hf', by rw [map_mul]; exact mul_ne_zero hs0 hf'0, rfl⟩, ?_⟩` and prove the remaining obligations. Use `⟨f * s', X i ^ (e + e'), e + e', pow_mem (X_mem_monos (Finset.mem_singleton_self i)) _, hf.mul hse', isHomogeneous_X_pow i _, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_pow, aeval_X, map_mul, map_mul, div_mul_eq_mul_div, key]`.
-/
theorem birational_clear (hbir : IsBirationalPt S x) {i : Fin (N + 1)} (hi : x i ≠ 0) (g : Ω) :
    ∃ d ∈ {y | ∃ (f : Poly S N) (e : ℕ), f.IsHomogeneous e ∧ aeval x f ≠ 0 ∧ aeval x f / x i ^ e = y},
      d * g ∈ chartRing S x (singleChart hi) := by
  obtain ⟨I, a, b, ⟨f, s, e, hs, hf, hse, rfl⟩, ⟨f', s', e', hs', hf', hse', rfl⟩, hb0, hgb⟩ := hbir g
  have hs0 := eval_ne_zero_of_mem_monos I hs
  have hs0' := eval_ne_zero_of_mem_monos I hs'
  have hf'0 : aeval x f' ≠ 0 := by
    intro h
    apply hb0
    rw [h, zero_div]
  have key : aeval x s * aeval x f' * g = aeval x f * aeval x s' := by
    calc aeval x s * aeval x f' * g
        = aeval x s * aeval x s' * (g * (aeval x f' / aeval x s')) := by
          field_simp
      _ = aeval x s * aeval x s' * (aeval x f / aeval x s) := by rw [hgb]
      _ = aeval x f * aeval x s' := by
          field_simp
  refine ⟨aeval x (s * f') / x i ^ (e + e'),
    ⟨s * f', e + e', hse.mul hf', by rw [map_mul]; exact mul_ne_zero hs0 hf'0, rfl⟩, ?_⟩
  refine ⟨f * s', X i ^ (e + e'), e + e', pow_mem (X_mem_monos (Finset.mem_singleton_self i)) _,
    hf.mul hse', isHomogeneous_X_pow i _, ?_⟩
  rw [map_pow, aeval_X, map_mul, map_mul, div_mul_eq_mul_div, key]

end Clauses

/- English proof (translation)
Introduce `S _ _ _ Ω _ _ N N' x x' hx' _ hcl`. Establish `key : ∀ (i : Fin (N + 1)) (hi : x i ≠ 0), ∃ m : S, algebraMap S Ω m ≠ 0 ∧ ∀ b ∈ domRing S x x' i, algebraMap S Ω m * b ∈ chartRing S x (singleChart hi)`. Introduce `i hi`. Take `⟨d, ⟨m, hm0, rfl⟩, hd⟩` from `exists_clear (A := chartRing S x (singleChart hi)) (fg_domSub hi hF hx') {y | ∃ s : S, algebraMap S Ω s ≠ 0 ∧ algebraMap S Ω s = y} ⟨1, by simp, by simp⟩ (by`. Introduce and unpack `_ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩`.

Conclude with `⟨a * b, by rw [map_mul]; exact mul_ne_zero ha hb, map_mul _ _ _⟩)`. Use the proof step `(by`. Introduce and unpack `_ ⟨a, -, rfl⟩`. Conclude with `Subalgebra.algebraMap_mem _ a)`. Use the proof step `(fun g hg => by`.

Take `⟨s, hs0, hs⟩` from `hcl i hi g ((mem_domSub_iff hi g).mp hg)`. Conclude with `⟨_, ⟨s, hs0, rfl⟩, hs⟩)`. Conclude with `⟨m, hm0, fun b hb => hd b ((mem_domSub_iff hi b).mpr hb)⟩`. Use `choose m hm0 hm using key`. Establish `hM : ∀ (i : Fin (N + 1)) (hi : x i ≠ 0), ∀ b ∈ domRing S x x' i, algebraMap S Ω (∏ j : {i // x i ≠ 0}, m j.1 j.2) * b ∈ chartRing S x (singleChart hi)`.

Introduce `i hi b hb`. Rewrite using `[← Finset.mul_prod_erase Finset.univ (fun j : {i // x i ≠ 0} => m j.1 j.2) (Finset.mem_univ ⟨i, hi⟩), map_mul, mul_comm (algebraMap S Ω _) (algebraMap S Ω _), mul_assoc]`. Conclude with `Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (hm i hi b hb)`. Use `⟨∏ j : {i // x i ≠ 0}, m j.1 j.2, ?_, hM, fun L n z hz => ?_⟩` and prove the remaining obligations. Rewrite using `[map_prod]`.

Conclude with `Finset.prod_ne_zero_iff.mpr fun j _ => hm0 j.1 j.2`. Use `mul_mem_secs_of_pullSecs (fun i hi b hb l hl => ?_) z hz` and prove the remaining obligations. Rewrite using `[← mul_assoc]`. Conclude with `Submodule.smul_mem _ (⟨_, hM i hi b hb⟩ : chartRing S x (singleChart hi)) hl`.
-/
theorem Generic.proof (hF : FiniteSections.Statement.{w, w}) : Generic.Statement.{u, w} := by
  intro S _ _ _ Ω _ _ N N' x x' hx' _ hcl
  classical
  have key : ∀ (i : Fin (N + 1)) (hi : x i ≠ 0), ∃ m : S, algebraMap S Ω m ≠ 0 ∧
      ∀ b ∈ domRing S x x' i, algebraMap S Ω m * b ∈ chartRing S x (singleChart hi) := by
    intro i hi
    obtain ⟨d, ⟨m, hm0, rfl⟩, hd⟩ := exists_clear (A := chartRing S x (singleChart hi))
      (fg_domSub hi hF hx') {y | ∃ s : S, algebraMap S Ω s ≠ 0 ∧ algebraMap S Ω s = y}
      ⟨1, by simp, by simp⟩
      (by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        exact ⟨a * b, by rw [map_mul]; exact mul_ne_zero ha hb, map_mul _ _ _⟩)
      (by
        rintro _ ⟨a, -, rfl⟩
        exact Subalgebra.algebraMap_mem _ a)
      (fun g hg => by
        obtain ⟨s, hs0, hs⟩ := hcl i hi g ((mem_domSub_iff hi g).mp hg)
        exact ⟨_, ⟨s, hs0, rfl⟩, hs⟩)
    exact ⟨m, hm0, fun b hb => hd b ((mem_domSub_iff hi b).mpr hb)⟩
  choose m hm0 hm using key
  have hM : ∀ (i : Fin (N + 1)) (hi : x i ≠ 0), ∀ b ∈ domRing S x x' i,
      algebraMap S Ω (∏ j : {i // x i ≠ 0}, m j.1 j.2) * b ∈ chartRing S x (singleChart hi) := by
    intro i hi b hb
    rw [← Finset.mul_prod_erase Finset.univ (fun j : {i // x i ≠ 0} => m j.1 j.2)
      (Finset.mem_univ ⟨i, hi⟩), map_mul, mul_comm (algebraMap S Ω _) (algebraMap S Ω _), mul_assoc]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (hm i hi b hb)
  refine ⟨∏ j : {i // x i ≠ 0}, m j.1 j.2, ?_, hM, fun L n z hz => ?_⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => hm0 j.1 j.2
  · refine mul_mem_secs_of_pullSecs (fun i hi b hb l hl => ?_) z hz
    rw [← mul_assoc]
    exact Submodule.smul_mem _ (⟨_, hM i hi b hb⟩ : chartRing S x (singleChart hi)) hl

/- English proof (translation)
Introduce `S _ _ Ω _ _ N N' x x' _ _ hbir' hnorm`. Establish `hx' : x' ≠ 0` using `ne_zero_of_isBirationalPt hbir'`. Establish `key : ∀ (i : Fin (N + 1)) (hi : x i ≠ 0), domRing S x x' i = (chartRing S x (singleChart hi) : Set Ω)`. Introduce `i hi`. Use extensionality with `b`.

Prove the components needed by the constructor for the conclusion. Introduce `hb`. Conclude with `hnorm i hi b (IsIntegral.of_mem_of_fg _ (fg_domSub hi hF hx') b ((mem_domSub_iff hi b).mpr hb))`. Introduce `hb`. Conclude with `(mem_domRing_iff hi b).mpr fun J => Subalgebra.algebraMap_mem _ (⟨b, hb⟩ : chartRing S x (singleChart hi))`.

Use `⟨key, fun L n => ?_⟩` and prove the remaining obligations. Introduce `z hz`. Establish `h` using `mul_mem_secs_of_pullSecs (κ := 1) (L := L.pow n) (L' := L.pow n) (fun i hi b hb l hl => by`. Rewrite using `[one_mul]`. Establish `hb' : b ∈ chartRing S x (singleChart hi)`.

Rewrite `hb` using `[key i hi]`. Conclude with `hb`. Conclude with `Submodule.smul_mem _ (⟨b, hb'⟩ : chartRing S x (singleChart hi)) hl) z hz`. Rewrite `h` using `[one_mul]`. Then use the resulting hypothesis.
-/
theorem Normal.proof (hF : FiniteSections.Statement.{w, w}) : Normal.Statement.{u, w} := by
  intro S _ _ Ω _ _ N N' x x' _ _ hbir' hnorm
  have hx' : x' ≠ 0 := ne_zero_of_isBirationalPt hbir'
  have key : ∀ (i : Fin (N + 1)) (hi : x i ≠ 0),
      domRing S x x' i = (chartRing S x (singleChart hi) : Set Ω) := by
    intro i hi
    ext b
    constructor
    · intro hb
      exact hnorm i hi b (IsIntegral.of_mem_of_fg _ (fg_domSub hi hF hx') b
        ((mem_domSub_iff hi b).mpr hb))
    · intro hb
      exact (mem_domRing_iff hi b).mpr fun J =>
        Subalgebra.algebraMap_mem _ (⟨b, hb⟩ : chartRing S x (singleChart hi))
  refine ⟨key, fun L n => ?_⟩
  intro z hz
  have h := mul_mem_secs_of_pullSecs (κ := 1) (L := L.pow n) (L' := L.pow n)
    (fun i hi b hb l hl => by
      rw [one_mul]
      have hb' : b ∈ chartRing S x (singleChart hi) := by
        rw [key i hi] at hb
        exact hb
      exact Submodule.smul_mem _ (⟨b, hb'⟩ : chartRing S x (singleChart hi)) hl) z hz
  rwa [one_mul] at h

/- English proof (translation)
Introduce `S _ _ Ω _ _ N N' x x' _ hbir hbir'`. Establish `hx' : x' ≠ 0` using `ne_zero_of_isBirationalPt hbir'`. Establish `key : ∀ (i : Fin (N + 1)) (hi : x i ≠ 0), ∃ (f : Poly S N) (e : ℕ), f.IsHomogeneous e ∧ aeval x f ≠ 0 ∧ ∀ b ∈ domRing S x x' i, aeval x f / x i ^ e * b ∈ chartRing S x (singleChart hi)`. Introduce `i hi`. Take `⟨d, ⟨f, e, hf, hf0, rfl⟩, hd⟩` from `exists_clear (A := chartRing S x (singleChart hi)) (fg_domSub hi hF hx') {y | ∃ (f : Poly S N) (e : ℕ), f.IsHomogeneous e ∧ aeval x f ≠ 0 ∧ aeval x f / x i ^ e = y} ⟨1, 0, isHomogeneous_one _ _, by simp, by simp⟩ (by`.

Introduce and unpack `_ ⟨f, e, hf, hf0, rfl⟩ _ ⟨f', e', hf', hf0', rfl⟩`. Use `⟨f * f', e + e', hf.mul hf', by rw [map_mul]; exact mul_ne_zero hf0 hf0', ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, pow_add, div_mul_div_comm])`. Use the proof step `(by`. Introduce and unpack `_ ⟨f, e, hf, -, rfl⟩`.

Conclude with `⟨f, X i ^ e, e, pow_mem (X_mem_monos (Finset.mem_singleton_self i)) e, hf, isHomogeneous_X_pow i e, by rw [map_pow, aeval_X]⟩)`. Use the proof step `(fun g _ => birational_clear hbir hi g)`. Conclude with `⟨f, e, hf, hf0, fun b hb => hd b ((mem_domSub_iff hi b).mpr hb)⟩`. Use `choose f e hf hf0 hfb using key`. Establish `hG : (∏ j : {i // x i ≠ 0}, f j.1 j.2).IsHomogeneous (∑ j : {i // x i ≠ 0}, e j.1 j.2)` using `IsHomogeneous.prod _ _ _ fun j _ => hf j.1 j.2`.

Establish `hsplit : ∀ (i : Fin (N + 1)) (hi : x i ≠ 0), ∃ w ∈ chartRing S x (singleChart hi), aeval x (∏ j : {i // x i ≠ 0}, f j.1 j.2) / x i ^ (∑ j : {i // x i ≠ 0}, e j.1 j.2) = aeval x (f i hi) / x i ^ e i hi * w`. Introduce `i hi`. Establish `hmem` using `Finset.mem_univ (⟨i, hi⟩ : {i // x i ≠ 0})`. Use `⟨aeval x (∏ j ∈ Finset.univ.erase (⟨i, hi⟩ : {i // x i ≠ 0}), f j.1 j.2) / x i ^ (∑ j ∈ Finset.univ.erase (⟨i, hi⟩ : {i // x i ≠ 0}), e j.1 j.2), ⟨_, X i ^ _, _, pow_mem (X_mem_monos (Finset.mem_singleton_self i)) _, IsHomogeneous.prod _ _ _ fun (j : {i // x i ≠ 0}) _ => hf j.1 j …` and prove the remaining obligations. Rewrite using `[← Finset.mul_prod_erase _ (fun j : {i // x i ≠ 0} => f j.1 j.2) hmem, ← Finset.add_sum_erase _ (fun j : {i // x i ≠ 0} => e j.1 j.2) hmem, map_mul, pow_add, div_mul_div_comm]`.

Use `⟨∑ j : {i // x i ≠ 0}, e j.1 j.2, aeval x (∏ j : {i // x i ≠ 0}, f j.1 j.2), ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem]`. Introduce `I`. Conclude with `Submodule.subset_span ⟨_, 1, 0, _, one_mem _, hG, isHomogeneous_one _ _, by simp, by rw [map_one, div_one]⟩`. Rewrite using `[map_prod]`.

Conclude with `Finset.prod_ne_zero_iff.mpr fun j _ => hf0 j.1 j.2`. Introduce `L n z hz`. Use `mul_mem_secs_of_pullSecs (fun i hi b hb l hl => ?_) z hz` and prove the remaining obligations. Use `Submodule.subset_span ⟨_ * b, ?_, l, hl, by rw [smul_eq_mul, mul_assoc]⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ ∈ twistMod S x _ (singleChart hi)`.

Rewrite using `[twistMod_eq_span _ (singleChart hi) (Finset.mem_singleton_self i), Submodule.mem_span_singleton]`. Take `⟨w, hw, hw'⟩` from `hsplit i hi`. Establish `hmem : aeval x (∏ j : {i // x i ≠ 0}, f j.1 j.2) / x i ^ (∑ j : {i // x i ≠ 0}, e j.1 j.2) * b ∈ chartRing S x (singleChart hi)`. Rewrite using `[hw', show ∀ p q r : Ω, p * q * r = q * (p * r) from fun p q r => by ring]`. Conclude with `mul_mem hw (hfb i hi b hb)`.

Use `⟨⟨_, hmem⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[chartRing_smul_def, zpow_natCast]`. Clear the denominators using the available nonvanishing facts.
-/
theorem Conductor.proof (hF : FiniteSections.Statement.{w, w}) : Conductor.Statement.{u, w} := by
  intro S _ _ Ω _ _ N N' x x' _ hbir hbir'
  classical
  have hx' : x' ≠ 0 := ne_zero_of_isBirationalPt hbir'
  have key : ∀ (i : Fin (N + 1)) (hi : x i ≠ 0), ∃ (f : Poly S N) (e : ℕ), f.IsHomogeneous e ∧
      aeval x f ≠ 0 ∧ ∀ b ∈ domRing S x x' i, aeval x f / x i ^ e * b ∈ chartRing S x (singleChart hi) := by
    intro i hi
    obtain ⟨d, ⟨f, e, hf, hf0, rfl⟩, hd⟩ := exists_clear (A := chartRing S x (singleChart hi))
      (fg_domSub hi hF hx')
      {y | ∃ (f : Poly S N) (e : ℕ), f.IsHomogeneous e ∧ aeval x f ≠ 0 ∧ aeval x f / x i ^ e = y}
      ⟨1, 0, isHomogeneous_one _ _, by simp, by simp⟩
      (by
        rintro _ ⟨f, e, hf, hf0, rfl⟩ _ ⟨f', e', hf', hf0', rfl⟩
        refine ⟨f * f', e + e', hf.mul hf', by rw [map_mul]; exact mul_ne_zero hf0 hf0', ?_⟩
        rw [map_mul, pow_add, div_mul_div_comm])
      (by
        rintro _ ⟨f, e, hf, -, rfl⟩
        exact ⟨f, X i ^ e, e, pow_mem (X_mem_monos (Finset.mem_singleton_self i)) e, hf,
          isHomogeneous_X_pow i e, by rw [map_pow, aeval_X]⟩)
      (fun g _ => birational_clear hbir hi g)
    exact ⟨f, e, hf, hf0, fun b hb => hd b ((mem_domSub_iff hi b).mpr hb)⟩
  choose f e hf hf0 hfb using key
  have hG : (∏ j : {i // x i ≠ 0}, f j.1 j.2).IsHomogeneous (∑ j : {i // x i ≠ 0}, e j.1 j.2) :=
    IsHomogeneous.prod _ _ _ fun j _ => hf j.1 j.2
  have hsplit : ∀ (i : Fin (N + 1)) (hi : x i ≠ 0), ∃ w ∈ chartRing S x (singleChart hi),
      aeval x (∏ j : {i // x i ≠ 0}, f j.1 j.2) / x i ^ (∑ j : {i // x i ≠ 0}, e j.1 j.2) =
        aeval x (f i hi) / x i ^ e i hi * w := by
    intro i hi
    have hmem := Finset.mem_univ (⟨i, hi⟩ : {i // x i ≠ 0})
    refine ⟨aeval x (∏ j ∈ Finset.univ.erase (⟨i, hi⟩ : {i // x i ≠ 0}), f j.1 j.2) /
      x i ^ (∑ j ∈ Finset.univ.erase (⟨i, hi⟩ : {i // x i ≠ 0}), e j.1 j.2),
      ⟨_, X i ^ _, _, pow_mem (X_mem_monos (Finset.mem_singleton_self i)) _,
        IsHomogeneous.prod _ _ _ fun (j : {i // x i ≠ 0}) _ => hf j.1 j.2, isHomogeneous_X_pow i _,
        by rw [map_pow, aeval_X]⟩, ?_⟩
    rw [← Finset.mul_prod_erase _ (fun j : {i // x i ≠ 0} => f j.1 j.2) hmem,
      ← Finset.add_sum_erase _ (fun j : {i // x i ≠ 0} => e j.1 j.2) hmem, map_mul, pow_add,
      div_mul_div_comm]
  refine ⟨∑ j : {i // x i ≠ 0}, e j.1 j.2, aeval x (∏ j : {i // x i ≠ 0}, f j.1 j.2), ?_, ?_, ?_⟩
  · simp only [SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem]
    intro I
    exact Submodule.subset_span ⟨_, 1, 0, _, one_mem _, hG, isHomogeneous_one _ _, by simp,
      by rw [map_one, div_one]⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => hf0 j.1 j.2
  · intro L n z hz
    refine mul_mem_secs_of_pullSecs (fun i hi b hb l hl => ?_) z hz
    refine Submodule.subset_span ⟨_ * b, ?_, l, hl, by rw [smul_eq_mul, mul_assoc]⟩
    change _ ∈ twistMod S x _ (singleChart hi)
    rw [twistMod_eq_span _ (singleChart hi) (Finset.mem_singleton_self i), Submodule.mem_span_singleton]
    obtain ⟨w, hw, hw'⟩ := hsplit i hi
    have hmem : aeval x (∏ j : {i // x i ≠ 0}, f j.1 j.2) / x i ^ (∑ j : {i // x i ≠ 0}, e j.1 j.2) * b ∈
        chartRing S x (singleChart hi) := by
      rw [hw', show ∀ p q r : Ω, p * q * r = q * (p * r) from fun p q r => by ring]
      exact mul_mem hw (hfb i hi b hb)
    refine ⟨⟨_, hmem⟩, ?_⟩
    rw [chartRing_smul_def, zpow_natCast]
    field_simp

/- English proof (translation)
Assemble the required witnesses or components as `⟨Generic.proof hF, Normal.proof hF, Conductor.proof hF⟩`.
-/
theorem proof (hF : FiniteSections.Statement.{w, w}) : Domination.Statement.{u, w} :=
  ⟨Generic.proof hF, Normal.proof hF, Conductor.proof hF⟩

end Domination

end

end GroundTheory.Heights₂.Heights.Kleiman
