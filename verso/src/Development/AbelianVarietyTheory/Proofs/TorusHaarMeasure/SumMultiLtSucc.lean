import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.PointwiseNormConstantSection

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.JetsPure

open Filter Asymptotics

open MeasureTheory Topology Filter Asymptotics in
open scoped ContDiff ENNReal Matrix in
/- English proof (translation)
Establish `h1 : ∀ q, σ q =O[𝓝 0] fun z : _root_.ReciprocityTheory.L2DbarEstimates.V n => ‖z‖`. Introduce `q`. Establish `h` using `(hσ q).hasFDerivAt.isBigO_sub.norm_right`. Simplify `h` using `only [h0 q, sub_zero]`. Establish `h2 : (fun z => ∏ q, σ q z ^ α q) =O[𝓝 0] fun z : _root_.ReciprocityTheory.L2DbarEstimates.V n => ∏ q, ‖z‖ ^ α q` using `IsBigO.finsetProd fun q _ => (h1 q).pow (α q)`.

Simplify `h2` using `only [Finset.prod_pow_eq_pow_sum]`.
-/
theorem _root_.GlobalTheory.JetsPure.monomial_isBigO {n D : ℕ} (σ : Fin D → _root_.ReciprocityTheory.L2DbarEstimates.V n → ℂ)
    (hσ : ∀ k, DifferentiableAt ℂ (σ k) 0) (h0 : ∀ k, σ k 0 = 0) (α : Fin D → ℕ) :
    (fun z => ∏ q, σ q z ^ α q) =O[𝓝 0] fun z => ‖z‖ ^ (∑ q, α q) := by
  have h1 : ∀ q, σ q =O[𝓝 0] fun z : _root_.ReciprocityTheory.L2DbarEstimates.V n => ‖z‖ := by
    intro q
    have h := (hσ q).hasFDerivAt.isBigO_sub.norm_right
    simpa only [h0 q, sub_zero] using h
  have h2 : (fun z => ∏ q, σ q z ^ α q) =O[𝓝 0] fun z : _root_.ReciprocityTheory.L2DbarEstimates.V n => ∏ q, ‖z‖ ^ α q :=
    IsBigO.finsetProd fun q _ => (h1 q).pow (α q)
  simpa only [Finset.prod_pow_eq_pow_sum] using h2

open MeasureTheory Topology Filter Asymptotics in
open scoped ContDiff ENNReal Matrix in

/- English proof (translation)
Introduce `J I _ D T a haT n e f w0 s t hdiff hnz hsurj`. Proceed by induction on `a with`. Consider the case `zero`. Use `⟨0, fun p => ?_⟩` and prove the remaining obligations. Establish `hf : ContinuousAt (f p) 0` using `(hdiff p).self_of_nhds.1.continuousAt`.

Simplify using `using hf.tendsto.isBigO_one ℝ`. Consider the case `succ a ih`. Take `⟨cc, hcc⟩` from `ih (by omega)`. Establish `haT' : a ≤ T` using `by omega`. Establish `hw0c : ∀ p, ContinuousAt (w0 p) 0` using `fun p => (hdiff p).self_of_nhds.2.1.continuousAt`.

Establish `hev : ∀ p, ∀ᶠ z in 𝓝 (0 : _root_.ReciprocityTheory.L2DbarEstimates.V (n p)), (DifferentiableAt ℂ (f p) z ∧ DifferentiableAt ℂ (w0 p) z ∧ (∀ k, DifferentiableAt ℂ (s p k) z) ∧ ∀ k, DifferentiableAt ℂ (t p k) z) ∧ w0 p z ≠ 0` using `fun p => (hdiff p).and ((hw0c p).eventually_ne (hnz p).1)`. Establish `htaylor : ∀ p, ∃ b : (Fin (n p) → ℕ) → ℂ, (fun z => (f p z - ∑ α ∈ _root_.ReciprocityTheory.ChartRestriction.G.AR.multiLt D a, ∑ k, cc α k * (∏ q, s p q z ^ α q) * w0 p z ^ (T - ∑ q, α q) * t p k z) - ∑ β ∈ Finset.Nat.antidiagonalTuple (n p) a, b β * ∏ k, (s p (e p k) z / w0 p z) …`. Introduce `p`. Take `⟨U, hU, hUo, h0U⟩` from `eventually_nhds_iff.mp (hev p)`. Establish `hζ : DifferentiableOn ℂ (fun z => (WithLp.toLp 2 fun k => s p (e p k) z / w0 p z : _root_.ReciprocityTheory.L2DbarEstimates.V (n p))) U`.

Introduce `z hz`. Apply `DifferentiableAt.differentiableWithinAt` to reduce the goal to its premises. Apply `differentiableAt_euclidean.mpr` to reduce the goal to its premises. Introduce `k`. Take `⟨⟨-, hw, hs, -⟩, hw0⟩` from `hU z hz`.

Establish `hsk` using `hs (e p k)`. Use `fun_prop (disch := assumption)`. Establish `hg : DifferentiableOn ℂ (fun z => f p z - ∑ α ∈ _root_.ReciprocityTheory.ChartRestriction.G.AR.multiLt D a, ∑ k, cc α k * (∏ q, s p q z ^ α q) * w0 p z ^ (T - ∑ q, α q) * t p k z) U`. Introduce `z hz`. Apply `DifferentiableAt.differentiableWithinAt` to reduce the goal to its premises.

Take `⟨⟨hf, hw, hs, ht⟩, -⟩` from `hU z hz`. Use `fun_prop`. Take `⟨b, hb⟩` from `_root_.ReciprocityTheory.ChartRestriction.G.AR.taylor_expansion_local_coordinates (a := a) _ (fun z => (WithLp.toLp 2 fun k => s p (e p k) z / w0 p z : _root_.ReciprocityTheory.L2DbarEstimates.V (n p))) U 0 hUo h0U hg hζ (by simp [(hnz p).2.1]; rfl) (hnz p).2.2 (by simpa only [su …`. Conclude with `⟨b, by simpa only [WithLp.ofLp_toLp, sub_zero] using hb⟩`. Use `choose b hb using htaylor`.

Use `choose u hu using fun α : Fin D → ℕ => hsurj fun p => b p (α ∘ e p) / w0 p 0 ^ T`. Use `⟨fun α => if ∑ q, α q < a then cc α else u α, fun p => ?_⟩` and prove the remaining obligations. Establish `hsplit : _root_.ReciprocityTheory.ChartRestriction.G.AR.multiLt D (a + 1) = _root_.ReciprocityTheory.ChartRestriction.G.AR.multiLt D a ∪ Finset.Nat.antidiagonalTuple D a`. Use extensionality with `α`. Simplify using `only [Finset.mem_union, _root_.ReciprocityTheory.ChartRestriction.G.AR.mem_multiIndicesBelow_iff, Finset.Nat.mem_antidiagonalTuple]`.

Use linear arithmetic over natural numbers and integers. Establish `hdisj : Disjoint (_root_.ReciprocityTheory.ChartRestriction.G.AR.multiLt D a) (Finset.Nat.antidiagonalTuple D a)`. Rewrite using `[Finset.disjoint_left]`. Introduce `α h1 h2`. Rewrite `h1` using `[_root_.ReciprocityTheory.ChartRestriction.G.AR.mem_multiIndicesBelow_iff]`.

Rewrite `h2` using `[Finset.Nat.mem_antidiagonalTuple]`. Use linear arithmetic over natural numbers and integers. Establish `hreidx : ∀ z, ∑ β ∈ Finset.Nat.antidiagonalTuple (n p) a, b p β * ∏ k, (s p (e p k) z / w0 p z) ^ β k = ∑ α ∈ Finset.Nat.antidiagonalTuple D a, b p (α ∘ e p) * ∏ q, (s p q z / w0 p z) ^ α q`. Introduce `z`. Use `symm`.

Use `Finset.sum_nbij' (fun α => α ∘ e p) (fun β => β ∘ (e p).symm) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `α hα`. Simplify using `only [Finset.mem_coe, Finset.Nat.mem_antidiagonalTuple] at hα ⊢`. Rewrite using `[← hα]`. Conclude with `Equiv.sum_comp (e p) α`.

Introduce `β hβ`. Simplify using `only [Finset.mem_coe, Finset.Nat.mem_antidiagonalTuple] at hβ ⊢`. Rewrite using `[← hβ]`. Conclude with `Equiv.sum_comp (e p).symm β`. Introduce `α _`.

Use extensionality with `q`. Simplify using the standard rewrite rules. Introduce `β _`. Use extensionality with `k`. Simplify using the standard rewrite rules.

Introduce `α _`. Simplify using `only [Function.comp_apply]`. Rewrite using `[Equiv.prod_comp (e p) (fun q => (s p q z / w0 p z) ^ α q)]`. Establish `hsum_split : ∀ z, ∑ α ∈ _root_.ReciprocityTheory.ChartRestriction.G.AR.multiLt D (a + 1), ∑ k, (if ∑ q, α q < a then cc α else u α) k * (∏ q, s p q z ^ α q) * w0 p z ^ (T - ∑ q, α q) * t p k z = ∑ α ∈ _root_.ReciprocityTheory.ChartRestriction.G.AR.multiLt D a, ∑ k, cc α k * (∏ q, …`. Introduce `z`.

Rewrite using `[hsplit, Finset.sum_union hdisj]`. Use `congr 1`. Use `Finset.sum_congr rfl fun α hα => ?_` and prove the remaining obligations. Rewrite using `[if_pos (_root_.ReciprocityTheory.ChartRestriction.G.AR.mem_multiIndicesBelow_iff.mp hα)]`. Use `Finset.sum_congr rfl fun α hα => ?_` and prove the remaining obligations.

Rewrite using `[if_neg (by rw [Finset.Nat.mem_antidiagonalTuple.mp hα]; exact lt_irrefl a)]`. Establish `hR : ∀ α ∈ Finset.Nat.antidiagonalTuple D a, (fun z => ∑ k, u α k * (∏ q, s p q z ^ α q) * w0 p z ^ (T - ∑ q, α q) * t p k z - b p (α ∘ e p) * ∏ q, (s p q z / w0 p z) ^ α q) =O[𝓝 0] fun z => ‖z‖ ^ (a + 1)`. Introduce `α hα`. Establish `hsum : ∑ q, α q = a` using `Finset.Nat.mem_antidiagonalTuple.mp hα`. Take `⟨-, hw, hs, ht⟩` from `(hdiff p).self_of_nhds`.

Establish `hH0 : ∑ k, u α k * (w0 p 0 ^ T * t p k 0) = b p (α ∘ e p)`. Establish `hw : w0 p 0 ^ T ≠ 0` using `pow_ne_zero _ (hnz p).1`. Establish `h : ∑ k, u α k * (w0 p 0 ^ T * t p k 0) = w0 p 0 ^ T * ∑ k, u α k * t p k 0`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => by ring`.

Rewrite using `[h, hu α p]`. Clear the denominators using the available nonvanishing facts. Establish `hHd : DifferentiableAt ℂ (fun z => ∑ k, u α k * (w0 p z ^ T * t p k z)) 0` using `by fun_prop`. Establish `hHO : (fun z => ∑ k, u α k * (w0 p z ^ T * t p k z) - ∑ k, u α k * (w0 p 0 ^ T * t p k 0)) =O[𝓝 0] fun z : _root_.ReciprocityTheory.L2DbarEstimates.V (n p) => ‖z‖`. Simplify `hHd.hasFDerivAt.isBigO_sub.norm_right` using `only [sub_zero]`.

Establish `hmono` using `_root_.GlobalTheory.JetsPure.monomial_isBigO (fun q z => s p q z / w0 p z) (fun q => by`. Establish `hsq` using `hs q`. Establish `hw00` using `(hnz p).1`. Use `fun_prop (disch := assumption)) (fun q => by simp [(hnz p).2.1]) α`. Rewrite `hmono` using `[hsum]`.

Use `(hmono.mul hHO).congr' ?_ (Eventually.of_forall fun z => by ring)` and prove the remaining obligations. Use `filter_upwards [(hw0c p).eventually_ne (hnz p).1] with z hz`. Rewrite using `[hH0]`. Establish `hP : ∏ q, s p q z ^ α q = (∏ q, (s p q z / w0 p z) ^ α q) * w0 p z ^ a`. Rewrite using `[← hsum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hz)]`. Establish `hW : w0 p z ^ a * w0 p z ^ (T - a) = w0 p z ^ T`. Rewrite using `[← pow_add, Nat.add_sub_cancel' haT']`. Rewrite using `[hsum, hP, mul_sub, Finset.mul_sum, ← hW]`.

Use `congr 1`. Conclude with `Finset.sum_congr rfl fun k _ => by ring`. Expand and normalize the polynomial expressions, which then agree. Use `((hb p).sub (IsBigO.sum hR)).congr' (Eventually.of_forall fun z => ?_) (Eventually.of_forall fun z => rfl)` and prove the remaining obligations. Use `clear hdiff hnz hsurj ih hcc hev hsplit hdisj hR hw0c hb hu`.

Use `beta_reduce`. Rewrite using `[hsum_split z, hreidx z, Finset.sum_apply, Finset.sum_sub_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem _root_.GlobalTheory.JetsPure.main : ∀ (J I : Type) [Fintype I] (D T a : ℕ),
    a ≤ T + 1 → ∀ (n : J → ℕ) (e : ∀ p, Fin (n p) ≃ Fin D)
    (f w0 : ∀ p, _root_.ReciprocityTheory.L2DbarEstimates.V (n p) → ℂ) (s : ∀ p, Fin D → _root_.ReciprocityTheory.L2DbarEstimates.V (n p) → ℂ)
    (t : ∀ p, I → _root_.ReciprocityTheory.L2DbarEstimates.V (n p) → ℂ),
    (∀ p, ∀ᶠ z in 𝓝 (0 : _root_.ReciprocityTheory.L2DbarEstimates.V (n p)), DifferentiableAt ℂ (f p) z ∧
      DifferentiableAt ℂ (w0 p) z ∧
      (∀ k, DifferentiableAt ℂ (s p k) z) ∧ ∀ k, DifferentiableAt ℂ (t p k) z) →
    (∀ p, w0 p 0 ≠ 0 ∧ (∀ k, s p k 0 = 0) ∧
      (fderiv ℂ (fun z => (WithLp.toLp 2 fun k => s p (e p k) z / w0 p z : _root_.ReciprocityTheory.L2DbarEstimates.V (n p))) 0).det
        ≠ 0) →
    (∀ v : J → ℂ, ∃ u : I → ℂ, ∀ p, ∑ k, u k * t p k 0 = v p) →
    ∃ cc : (Fin D → ℕ) → I → ℂ, ∀ p, (fun z => f p z - ∑ α ∈ _root_.ReciprocityTheory.ChartRestriction.G.AR.multiLt D a, ∑ k,
      cc α k * (∏ q, s p q z ^ α q) * w0 p z ^ (T - ∑ q, α q) * t p k z) =O[𝓝 0]
        fun z => ‖z‖ ^ a := by
  intro J I _ D T a haT n e f w0 s t hdiff hnz hsurj
  induction a with
  | zero =>
    refine ⟨0, fun p => ?_⟩
    have hf : ContinuousAt (f p) 0 := (hdiff p).self_of_nhds.1.continuousAt
    simpa using hf.tendsto.isBigO_one ℝ
  | succ a ih =>
    obtain ⟨cc, hcc⟩ := ih (by omega)
    have haT' : a ≤ T := by omega
    have hw0c : ∀ p, ContinuousAt (w0 p) 0 := fun p =>
      (hdiff p).self_of_nhds.2.1.continuousAt
    have hev : ∀ p, ∀ᶠ z in 𝓝 (0 : _root_.ReciprocityTheory.L2DbarEstimates.V (n p)), (DifferentiableAt ℂ (f p) z ∧
        DifferentiableAt ℂ (w0 p) z ∧ (∀ k, DifferentiableAt ℂ (s p k) z) ∧
        ∀ k, DifferentiableAt ℂ (t p k) z) ∧ w0 p z ≠ 0 :=
      fun p => (hdiff p).and ((hw0c p).eventually_ne (hnz p).1)
    have htaylor : ∀ p, ∃ b : (Fin (n p) → ℕ) → ℂ, (fun z => (f p z - ∑ α ∈ _root_.ReciprocityTheory.ChartRestriction.G.AR.multiLt D a, ∑ k,
        cc α k * (∏ q, s p q z ^ α q) * w0 p z ^ (T - ∑ q, α q) * t p k z) -
        ∑ β ∈ Finset.Nat.antidiagonalTuple (n p) a, b β * ∏ k, (s p (e p k) z / w0 p z) ^ β k)
          =O[𝓝 0] fun z => ‖z‖ ^ (a + 1) := by
      intro p
      obtain ⟨U, hU, hUo, h0U⟩ := eventually_nhds_iff.mp (hev p)
      have hζ : DifferentiableOn ℂ
          (fun z => (WithLp.toLp 2 fun k => s p (e p k) z / w0 p z : _root_.ReciprocityTheory.L2DbarEstimates.V (n p))) U := by
        intro z hz
        apply DifferentiableAt.differentiableWithinAt
        apply differentiableAt_euclidean.mpr
        intro k
        obtain ⟨⟨-, hw, hs, -⟩, hw0⟩ := hU z hz
        have hsk := hs (e p k)
        fun_prop (disch := assumption)
      have hg : DifferentiableOn ℂ (fun z => f p z - ∑ α ∈ _root_.ReciprocityTheory.ChartRestriction.G.AR.multiLt D a, ∑ k,
          cc α k * (∏ q, s p q z ^ α q) * w0 p z ^ (T - ∑ q, α q) * t p k z) U := by
        intro z hz
        apply DifferentiableAt.differentiableWithinAt
        obtain ⟨⟨hf, hw, hs, ht⟩, -⟩ := hU z hz
        fun_prop
      obtain ⟨b, hb⟩ := _root_.ReciprocityTheory.ChartRestriction.G.AR.taylor_expansion_local_coordinates (a := a) _
        (fun z => (WithLp.toLp 2 fun k => s p (e p k) z / w0 p z : _root_.ReciprocityTheory.L2DbarEstimates.V (n p))) U 0 hUo h0U
        hg hζ (by simp [(hnz p).2.1]; rfl) (hnz p).2.2 (by simpa only [sub_zero] using hcc p)
      exact ⟨b, by simpa only [WithLp.ofLp_toLp, sub_zero] using hb⟩
    choose b hb using htaylor
    choose u hu using fun α : Fin D → ℕ => hsurj fun p => b p (α ∘ e p) / w0 p 0 ^ T
    refine ⟨fun α => if ∑ q, α q < a then cc α else u α, fun p => ?_⟩
    have hsplit : _root_.ReciprocityTheory.ChartRestriction.G.AR.multiLt D (a + 1) = _root_.ReciprocityTheory.ChartRestriction.G.AR.multiLt D a ∪ Finset.Nat.antidiagonalTuple D a := by
      ext α
      simp only [Finset.mem_union, _root_.ReciprocityTheory.ChartRestriction.G.AR.mem_multiIndicesBelow_iff, Finset.Nat.mem_antidiagonalTuple]
      omega
    have hdisj : Disjoint (_root_.ReciprocityTheory.ChartRestriction.G.AR.multiLt D a) (Finset.Nat.antidiagonalTuple D a) := by
      rw [Finset.disjoint_left]
      intro α h1 h2
      rw [_root_.ReciprocityTheory.ChartRestriction.G.AR.mem_multiIndicesBelow_iff] at h1
      rw [Finset.Nat.mem_antidiagonalTuple] at h2
      omega
    have hreidx : ∀ z, ∑ β ∈ Finset.Nat.antidiagonalTuple (n p) a,
        b p β * ∏ k, (s p (e p k) z / w0 p z) ^ β k =
        ∑ α ∈ Finset.Nat.antidiagonalTuple D a, b p (α ∘ e p) * ∏ q, (s p q z / w0 p z) ^ α q := by
      intro z
      symm
      refine Finset.sum_nbij' (fun α => α ∘ e p) (fun β => β ∘ (e p).symm) ?_ ?_ ?_ ?_ ?_
      · intro α hα
        simp only [Finset.mem_coe, Finset.Nat.mem_antidiagonalTuple] at hα ⊢
        rw [← hα]
        exact Equiv.sum_comp (e p) α
      · intro β hβ
        simp only [Finset.mem_coe, Finset.Nat.mem_antidiagonalTuple] at hβ ⊢
        rw [← hβ]
        exact Equiv.sum_comp (e p).symm β
      · intro α _
        ext q
        simp
      · intro β _
        ext k
        simp
      · intro α _
        simp only [Function.comp_apply]
        rw [Equiv.prod_comp (e p) (fun q => (s p q z / w0 p z) ^ α q)]
    have hsum_split : ∀ z, ∑ α ∈ _root_.ReciprocityTheory.ChartRestriction.G.AR.multiLt D (a + 1), ∑ k,
        (if ∑ q, α q < a then cc α else u α) k * (∏ q, s p q z ^ α q) *
          w0 p z ^ (T - ∑ q, α q) * t p k z =
        ∑ α ∈ _root_.ReciprocityTheory.ChartRestriction.G.AR.multiLt D a, ∑ k,
          cc α k * (∏ q, s p q z ^ α q) * w0 p z ^ (T - ∑ q, α q) * t p k z +
        ∑ α ∈ Finset.Nat.antidiagonalTuple D a, ∑ k,
          u α k * (∏ q, s p q z ^ α q) * w0 p z ^ (T - ∑ q, α q) * t p k z := by
      intro z
      rw [hsplit, Finset.sum_union hdisj]
      congr 1
      · refine Finset.sum_congr rfl fun α hα => ?_
        rw [if_pos (_root_.ReciprocityTheory.ChartRestriction.G.AR.mem_multiIndicesBelow_iff.mp hα)]
      · refine Finset.sum_congr rfl fun α hα => ?_
        rw [if_neg (by rw [Finset.Nat.mem_antidiagonalTuple.mp hα]; exact lt_irrefl a)]
    have hR : ∀ α ∈ Finset.Nat.antidiagonalTuple D a, (fun z => ∑ k, u α k *
        (∏ q, s p q z ^ α q) * w0 p z ^ (T - ∑ q, α q) * t p k z -
        b p (α ∘ e p) * ∏ q, (s p q z / w0 p z) ^ α q) =O[𝓝 0] fun z => ‖z‖ ^ (a + 1) := by
      intro α hα
      have hsum : ∑ q, α q = a := Finset.Nat.mem_antidiagonalTuple.mp hα
      obtain ⟨-, hw, hs, ht⟩ := (hdiff p).self_of_nhds
      have hH0 : ∑ k, u α k * (w0 p 0 ^ T * t p k 0) = b p (α ∘ e p) := by
        have hw : w0 p 0 ^ T ≠ 0 := pow_ne_zero _ (hnz p).1
        have h : ∑ k, u α k * (w0 p 0 ^ T * t p k 0) = w0 p 0 ^ T * ∑ k, u α k * t p k 0 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
        rw [h, hu α p]
        field_simp
      have hHd : DifferentiableAt ℂ (fun z => ∑ k, u α k * (w0 p z ^ T * t p k z)) 0 := by
        fun_prop
      have hHO : (fun z => ∑ k, u α k * (w0 p z ^ T * t p k z) -
          ∑ k, u α k * (w0 p 0 ^ T * t p k 0)) =O[𝓝 0] fun z : _root_.ReciprocityTheory.L2DbarEstimates.V (n p) => ‖z‖ := by
        simpa only [sub_zero] using hHd.hasFDerivAt.isBigO_sub.norm_right
      have hmono := _root_.GlobalTheory.JetsPure.monomial_isBigO (fun q z => s p q z / w0 p z)
        (fun q => by
          have hsq := hs q
          have hw00 := (hnz p).1
          fun_prop (disch := assumption)) (fun q => by simp [(hnz p).2.1]) α
      rw [hsum] at hmono
      refine (hmono.mul hHO).congr' ?_ (Eventually.of_forall fun z => by ring)
      filter_upwards [(hw0c p).eventually_ne (hnz p).1] with z hz
      rw [hH0]
      have hP : ∏ q, s p q z ^ α q = (∏ q, (s p q z / w0 p z) ^ α q) * w0 p z ^ a := by
        rw [← hsum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun q _ => ?_
        rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hz)]
      have hW : w0 p z ^ a * w0 p z ^ (T - a) = w0 p z ^ T := by
        rw [← pow_add, Nat.add_sub_cancel' haT']
      rw [hsum, hP, mul_sub, Finset.mul_sum, ← hW]
      congr 1
      · exact Finset.sum_congr rfl fun k _ => by ring
      · ring
    refine ((hb p).sub (IsBigO.sum hR)).congr' (Eventually.of_forall fun z => ?_)
      (Eventually.of_forall fun z => rfl)
    clear hdiff hnz hsurj ih hcc hev hsplit hdisj hR hw0c hb hu
    beta_reduce
    rw [hsum_split z, hreidx z, Finset.sum_apply, Finset.sum_sub_distrib]
    ring

end GlobalTheory.JetsPure
