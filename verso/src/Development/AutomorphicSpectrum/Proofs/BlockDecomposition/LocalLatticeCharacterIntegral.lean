import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EMatMulNegCol
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FibreMassEq
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.Imports
open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.AvgFree.Cov

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.P6.r08a.GlobalTheory.CompanionTheory.AvgFree.Cov.exists_sep H T`.
-/
theorem exists_sep {K : Type} [AddCommGroup K] (H : AddSubgroup K) (T : Finset K) :
    ∃ Rep : Finset K, Rep ⊆ T ∧ (∀ x ∈ T, ∃ r ∈ Rep, x - r ∈ H) ∧
      ∀ r ∈ Rep, ∀ r' ∈ Rep, r - r' ∈ H → r = r' :=
  _root_.UpperTheory.Reformulated.B.P6.r08a.GlobalTheory.CompanionTheory.AvgFree.Cov.exists_sep H T

/- English proof (translation)
Set `H : AddSubgroup K` to `O.toAddSubgroup.map (AddMonoidHom.mulLeft (s : K))`. Establish `hHmem : ∀ x, x ∈ H ↔ ∃ o ∈ O, x = s * o`. Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨o, ho, rfl⟩`.

Conclude with `⟨o, ho, rfl⟩`. Introduce and unpack `⟨o, ho, rfl⟩`. Conclude with `⟨o, ho, rfl⟩`. Establish `hHset : (H : Set K) = (fun x => (s : K) * x) '' (O : Set K)`. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Take `⟨o, ho, rfl⟩` from `(hHmem x).1 hx`. Conclude with `⟨o, ho, rfl⟩`. Introduce and unpack `⟨o, ho, rfl⟩`.

Conclude with `(hHmem _).2 ⟨o, ho, rfl⟩`. Establish `hHpre : (H : Set K) = (fun x => ((s⁻¹ : Kˣ) : K) * x) ⁻¹' (O : Set K)`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Take `⟨o, ho, rfl⟩` from `(hHmem x).1 hx`. Use `show ((s⁻¹ : Kˣ) : K) * (s * o) ∈ O`. Rewrite using `[Units.inv_mul_cancel_left]` and apply the resulting hypothesis. Introduce `hx`. Use `(hHmem x).2 ⟨_, hx, ?_⟩` and prove the remaining obligations.

Rewrite using `[Units.mul_inv_cancel_left]`. Establish `hHo : IsOpen (H : Set K)`. Rewrite using `[hHpre]`. Conclude with `hOo.preimage (continuous_const.mul continuous_id)`. Establish `hHO : ∀ x ∈ H, x ∈ O`.

Introduce `x hx`. Take `⟨o, ho, rfl⟩` from `(hHmem x).1 hx`. Conclude with `O.mul_mem hs ho`. Set `U : K → Set K` to `fun x => (fun y => y - x) ⁻¹' (H : Set K)`. Establish `hUo : ∀ x, IsOpen (U x)` using `fun x => hHo.preimage (continuous_id.sub continuous_const)`.

Establish `hUx : ∀ x, x ∈ U x` using `fun x => by show x - x ∈ H`. Simplify using the standard rewrite rules. Take `⟨T, hTO, hcov⟩` from `hOc.elim_nhds_subcover U fun x _ => (hUo x).mem_nhds (hUx x)`. Take `⟨Rep, hRT, hR2, hR3⟩` from `exists_sep H T`. Establish `hRO : ∀ r ∈ Rep, r ∈ O` using `fun r hr => hTO r (hRT hr)`.

Establish `hOpos : μ (O : Set K) ≠ 0` using `hOo.measure_ne_zero μ ⟨1, O.one_mem⟩`. Establish `hOtop : μ (O : Set K) ≠ ⊤` using `hOc.measure_lt_top.ne`. Establish `hHμ : μ (H : Set K) = c * μ (O : Set K)` using `by rw [hHset, hμ]`. Establish `hHpos : μ (H : Set K) ≠ 0` using `hHo.measure_ne_zero μ ⟨0, H.zero_mem⟩`. Establish `hc0 : c ≠ 0`.

Introduce and unpack `rfl`. Apply `hHpos` to reduce the goal to its premises. Rewrite using `[hHμ]`. Simplify using the standard rewrite rules. Establish `hUμ : ∀ x, μ (U x) = μ (H : Set K)` using `fun x => by`.

Establish `: U x = (fun y => -x + y) ⁻¹' (H : Set K)`. Use extensionality with `y`. Use `show y - x ∈ H ↔ -x + y ∈ H`. Rewrite using `[sub_eq_neg_add]`. Rewrite using `[this]`.

Conclude with `measure_preimage_add μ _ _`. Establish `hdisj : (Rep : Set K).PairwiseDisjoint U`. Introduce `r hr r' hr' hne`. Use `Set.disjoint_left.2 fun y hy hy' => hne (hR3 r hr r' hr' ?_)` and prove the remaining obligations. Use `H.sub_mem hy' hy` as an intermediate fact.

Establish `e : (y - r') - (y - r) = r - r'` using `by abel`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Establish `hsub : (⋃ r ∈ Rep, U r) ⊆ (O : Set K)`. Introduce `y hy`. Take `⟨r, hr, hy⟩` from `Set.mem_iUnion₂.1 hy`.

Establish `h1` using `hHO _ hy`. Establish `e : y = (y - r) + r` using `by abel`. Rewrite using `[e]`. Conclude with `O.add_mem h1 (hRO r hr)`. Establish `hsum : (Rep.card : ℝ≥0∞) * (c * μ (O : Set K)) ≤ μ (O : Set K)`.

Establish `h1` using `measure_mono (μ := μ) hsub`. Rewrite `h1` using `[measure_biUnion_finset hdisj fun r _ => (hUo r).measurableSet]`. Simplify `h1` using `[hUμ, hHμ]`. Establish `hcard : (Rep.card : ℝ≥0) * c ≤ 1`. Establish `h2 : (Rep.card : ℝ≥0∞) * c * μ (O : Set K) ≤ 1 * μ (O : Set K)`.

Rewrite using `[mul_assoc, one_mul]`. Conclude with `hsum`. Establish `h3` using `(ENNReal.mul_le_mul_iff_left hOpos hOtop).1 h2`. Conclude with `h3` after adjusting the coercions. Use `⟨Rep, (NNReal.le_inv_iff_mul_le hc0).2 hcard, hRO, ?_⟩` and prove the remaining obligations.

Introduce `a ha`. Take `⟨x, hxT, hax⟩` from `Set.mem_iUnion₂.1 (hcov ha)`. Take `⟨r, hr, hxr⟩` from `hR2 x hxT`. Use `⟨r, hr, ?_⟩` and prove the remaining obligations. Establish `h1 : a - r ∈ H`.

Use `H.add_mem hax hxr` as an intermediate fact. Establish `e : (a - x) + (x - r) = a - r` using `by abel`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Conclude with `(hHmem _).1 h1`.
-/
theorem exists_reps {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [MeasurableSpace K]
    [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure] (O : Subring K) (hOc : IsCompact (O : Set K))
    (hOo : IsOpen (O : Set K)) (s : Kˣ) (hs : (s : K) ∈ O) (c : ℝ≥0)
    (hμ : ∀ Y : Set K, μ ((fun x => (s : K) * x) '' Y) = c * μ Y) :
    ∃ Rep : Finset K, (Rep.card : ℝ≥0) ≤ c⁻¹ ∧ (∀ r ∈ Rep, r ∈ O) ∧
      ∀ a ∈ O, ∃ r ∈ Rep, ∃ o ∈ O, a - r = s * o := by
  classical
  let H : AddSubgroup K := O.toAddSubgroup.map (AddMonoidHom.mulLeft (s : K))
  have hHmem : ∀ x, x ∈ H ↔ ∃ o ∈ O, x = s * o := by
    intro x
    constructor
    · rintro ⟨o, ho, rfl⟩
      exact ⟨o, ho, rfl⟩
    · rintro ⟨o, ho, rfl⟩
      exact ⟨o, ho, rfl⟩
  have hHset : (H : Set K) = (fun x => (s : K) * x) '' (O : Set K) := by
    ext x
    constructor
    · intro hx
      obtain ⟨o, ho, rfl⟩ := (hHmem x).1 hx
      exact ⟨o, ho, rfl⟩
    · rintro ⟨o, ho, rfl⟩
      exact (hHmem _).2 ⟨o, ho, rfl⟩
  have hHpre : (H : Set K) = (fun x => ((s⁻¹ : Kˣ) : K) * x) ⁻¹' (O : Set K) := by
    ext x
    constructor
    · intro hx
      obtain ⟨o, ho, rfl⟩ := (hHmem x).1 hx
      show ((s⁻¹ : Kˣ) : K) * (s * o) ∈ O
      rwa [Units.inv_mul_cancel_left]
    · intro hx
      refine (hHmem x).2 ⟨_, hx, ?_⟩
      rw [Units.mul_inv_cancel_left]
  have hHo : IsOpen (H : Set K) := by
    rw [hHpre]
    exact hOo.preimage (continuous_const.mul continuous_id)
  have hHO : ∀ x ∈ H, x ∈ O := by
    intro x hx
    obtain ⟨o, ho, rfl⟩ := (hHmem x).1 hx
    exact O.mul_mem hs ho

  let U : K → Set K := fun x => (fun y => y - x) ⁻¹' (H : Set K)
  have hUo : ∀ x, IsOpen (U x) := fun x => hHo.preimage (continuous_id.sub continuous_const)
  have hUx : ∀ x, x ∈ U x := fun x => by
    show x - x ∈ H
    simp
  obtain ⟨T, hTO, hcov⟩ := hOc.elim_nhds_subcover U fun x _ => (hUo x).mem_nhds (hUx x)
  obtain ⟨Rep, hRT, hR2, hR3⟩ := exists_sep H T
  have hRO : ∀ r ∈ Rep, r ∈ O := fun r hr => hTO r (hRT hr)
  have hOpos : μ (O : Set K) ≠ 0 := hOo.measure_ne_zero μ ⟨1, O.one_mem⟩
  have hOtop : μ (O : Set K) ≠ ⊤ := hOc.measure_lt_top.ne
  have hHμ : μ (H : Set K) = c * μ (O : Set K) := by rw [hHset, hμ]
  have hHpos : μ (H : Set K) ≠ 0 := hHo.measure_ne_zero μ ⟨0, H.zero_mem⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hHpos
    rw [hHμ]
    simp
  have hUμ : ∀ x, μ (U x) = μ (H : Set K) := fun x => by
    have : U x = (fun y => -x + y) ⁻¹' (H : Set K) := by
      ext y
      show y - x ∈ H ↔ -x + y ∈ H
      rw [sub_eq_neg_add]
    rw [this]
    exact measure_preimage_add μ _ _
  have hdisj : (Rep : Set K).PairwiseDisjoint U := by
    intro r hr r' hr' hne
    refine Set.disjoint_left.2 fun y hy hy' => hne (hR3 r hr r' hr' ?_)
    have := H.sub_mem hy' hy
    have e : (y - r') - (y - r) = r - r' := by abel
    rwa [e] at this
  have hsub : (⋃ r ∈ Rep, U r) ⊆ (O : Set K) := by
    intro y hy
    obtain ⟨r, hr, hy⟩ := Set.mem_iUnion₂.1 hy
    have h1 := hHO _ hy
    have e : y = (y - r) + r := by abel
    rw [e]
    exact O.add_mem h1 (hRO r hr)
  have hsum : (Rep.card : ℝ≥0∞) * (c * μ (O : Set K)) ≤ μ (O : Set K) := by
    have h1 := measure_mono (μ := μ) hsub
    rw [measure_biUnion_finset hdisj fun r _ => (hUo r).measurableSet] at h1
    simpa [hUμ, hHμ] using h1
  have hcard : (Rep.card : ℝ≥0) * c ≤ 1 := by
    have h2 : (Rep.card : ℝ≥0∞) * c * μ (O : Set K) ≤ 1 * μ (O : Set K) := by
      rw [mul_assoc, one_mul]
      exact hsum
    have h3 := (ENNReal.mul_le_mul_iff_left hOpos hOtop).1 h2
    exact_mod_cast h3
  refine ⟨Rep, (NNReal.le_inv_iff_mul_le hc0).2 hcard, hRO, ?_⟩
  intro a ha
  obtain ⟨x, hxT, hax⟩ := Set.mem_iUnion₂.1 (hcov ha)
  obtain ⟨r, hr, hxr⟩ := hR2 x hxT
  refine ⟨r, hr, ?_⟩
  have h1 : a - r ∈ H := by
    have := H.add_mem hax hxr
    have e : (a - x) + (x - r) = a - r := by abel
    rwa [e] at this
  exact (hHmem _).1 h1

/- English proof (translation)
Set `T : AddSubgroup K` to `L.toAddSubgroup.map (AddMonoidHom.mulLeft s)`. Establish `hT : ∀ x, x ∈ T ↔ x ∈ (fun x => s * x) '' (L : Set K)`. Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`.

Conclude with `⟨y, hy, rfl⟩`. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `⟨y, hy, rfl⟩`. Rewrite `h0`, the goal using `[← hT]`. Establish `e : ∑ i, X i k * a i = ∑ i, X i k * a0 i + ∑ i, X i k * (a i - a0 i)`.

Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Rewrite using `[e]`. Use `T.add_mem h0 (T.sum_mem fun i _ => ?_)` and prove the remaining obligations. Distinguish the cases in `hi : i = l`.

Substitute `hi` using the available equality. Rewrite using `[hl, sub_self, mul_zero]`. Conclude with `T.zero_mem`. Take `⟨o, ho, hoe⟩` from `h i hi`. Rewrite using `[hT, hoe]`.

Use `⟨(⟨o, ho⟩ : O) • X i k, L.smul_mem _ (hX i k), ?_⟩` and prove the remaining obligations. Use `show s * (o * X i k) = X i k * (s * o)`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_near {K : Type} [CommRing K] (O : Subring K) (L : Submodule O K) (s : K) {n M : ℕ}
    (X : Fin n → Fin M → K) (hX : ∀ i k, X i k ∈ L) (l : Fin n) (a a0 : Fin n → K) (hl : a l = a0 l)
    (h : ∀ i, i ≠ l → ∃ o ∈ O, a i - a0 i = s * o) (k : Fin M)
    (h0 : ∑ i, X i k * a0 i ∈ (fun x => s * x) '' (L : Set K)) :
    ∑ i, X i k * a i ∈ (fun x => s * x) '' (L : Set K) := by
  let T : AddSubgroup K := L.toAddSubgroup.map (AddMonoidHom.mulLeft s)
  have hT : ∀ x, x ∈ T ↔ x ∈ (fun x => s * x) '' (L : Set K) := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
  rw [← hT] at h0 ⊢
  have e : ∑ i, X i k * a i = ∑ i, X i k * a0 i + ∑ i, X i k * (a i - a0 i) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  refine T.add_mem h0 (T.sum_mem fun i _ => ?_)
  by_cases hi : i = l
  · subst hi
    rw [hl, sub_self, mul_zero]
    exact T.zero_mem
  · obtain ⟨o, ho, hoe⟩ := h i hi
    rw [hT, hoe]
    refine ⟨(⟨o, ho⟩ : O) • X i k, L.smul_mem _ (hX i k), ?_⟩
    show s * (o * X i k) = X i k * (s * o)
    ring

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

/- English proof (translation)
Introduce `c k`. Use `show ∑ e, X e k * (eMat R l a * dMat R l ((s⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E)) e c ∈ L`. Simplify using `only [dMat, Matrix.mul_diagonal]`. Distinguish the cases in `hc : c = l`. Substitute `hc` using the available equality.

Take `⟨y, hy, hye⟩` from `h k`. Establish `: ∑ e, X e k * (eMat R c a e c * Function.update (1 : Fin n → R ⊗[F] E) c ((s⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E) c) = y`. Simplify using `only [eMat, Matrix.updateCol_self, Function.update_self]`. Establish `e1 : ∑ e, X e k * (a e * ((s⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E)) = ((s⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E) * ∑ e, X e k * a e`. Rewrite using `[Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun e _ => by ring`. Rewrite using `[e1, ← hye]`. Conclude with `Units.inv_mul_cancel_left s y`. Rewrite using `[this]`. Conclude with `hy`.

Establish `: ∑ e, X e k * (eMat R l a e c * Function.update (1 : Fin n → R ⊗[F] E) l ((s⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E) c) = X c k`. Simplify using `only [eMat, Matrix.updateCol_ne hc, Function.update_of_ne hc, Pi.one_apply, mul_one, Matrix.one_apply]`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `hX c k`.
-/
theorem rmul_mem_tupIn {n M : ℕ} (L : Set (R ⊗[F] E)) (s : (R ⊗[F] E)ˣ) (l : Fin n) (a : Fin n → R ⊗[F] E)
    (X : Fin n → Fin M → R ⊗[F] E) (hX : X ∈ tupIn R L)
    (h : ∀ k, ∑ i, X i k * a i ∈ (fun x => (s : R ⊗[F] E) * x) '' L) :
    GlobalTheory.CompanionTheory.SW.rmul R X (eMat R l a * dMat R l ((s⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E)) ∈ tupIn R L := by
  classical
  intro c k
  show ∑ e, X e k * (eMat R l a * dMat R l ((s⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E)) e c ∈ L
  simp only [dMat, Matrix.mul_diagonal]
  by_cases hc : c = l
  · subst hc
    obtain ⟨y, hy, hye⟩ := h k
    have : ∑ e, X e k * (eMat R c a e c * Function.update (1 : Fin n → R ⊗[F] E) c ((s⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E) c) = y := by
      simp only [eMat, Matrix.updateCol_self, Function.update_self]
      have e1 : ∑ e, X e k * (a e * ((s⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E)) =
          ((s⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E) * ∑ e, X e k * a e := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun e _ => by ring
      rw [e1, ← hye]
      exact Units.inv_mul_cancel_left s y
    rw [this]
    exact hy
  · have : ∑ e, X e k * (eMat R l a e c * Function.update (1 : Fin n → R ⊗[F] E) l ((s⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E) c) = X c k := by
      simp only [eMat, Matrix.updateCol_ne hc, Function.update_of_ne hc, Pi.one_apply, mul_one,
        Matrix.one_apply]
      simp
    rw [this]
    exact hX c k

end GlobalTheory.CompanionTheory.AvgFree.Cov

open GlobalTheory.CompanionTheory.AvgFree.Cov in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ d b v lv hlv O S hOrd L _ _ n M _ p hp θ hθ j`. Take `⟨r1, r2, r3, r4, -⟩` from `GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v`. Use `haveI := r1`. Use `haveI := r2`. Use `haveI := r3`.

Use `haveI := r4`. Use `haveI : BorelSpace (Fv F v) := ⟨rfl⟩`. Take `⟨a1, a2, a3, a4, -, -, -, a8, -, -⟩` from `GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)`. Use `haveI := a1`. Use `haveI := a2`.

Use `haveI := a3`. Use `haveI := a4`. Use `haveI := hlv.1`. Take `⟨hK, -, -⟩` from `GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Fv F v) d b lv hlv.1`. Use `haveI := hK`.

Take `⟨hOc, hOo, -, hS, -⟩` from `hOrd`. Establish `htO : (p.1 : Fv F v ⊗[F] E) ∈ O` using `(hS p hp).1`. Establish `hpow : ∀ (i : ℕ) (Y : Set (Fv F v ⊗[F] E)), GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv ((fun x => ((p.1 ^ i : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) * x) '' Y) = ((θ ^ i : ℝ≥0) : ℝ≥0∞) * GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv Y`. Introduce `i`. Proceed by induction on `i with`.

Consider the case `zero => intro Y`. Simplify using the standard rewrite rules. Consider the case `succ i ih`. Introduce `Y`. Establish `e : (fun x => ((p.1 ^ (i + 1) : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) * x) '' Y = (fun x => (p.1 : Fv F v ⊗[F] E) * x) '' ((fun x => ((p.1 ^ i : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) * x) '' Y)`.

Rewrite using `[Set.image_image]`. Use `Set.image_congr fun x _ => ?_` and prove the remaining obligations. Rewrite using `[pow_succ', Units.val_mul, mul_assoc]`. Rewrite using `[e, hθ, ih, pow_succ', ENNReal.coe_mul, mul_assoc]`. Establish `hsO : ((p.1 ^ j : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ O`.

Rewrite using `[Units.val_pow_eq_pow_val]`. Conclude with `O.pow_mem htO j`. Take `⟨Rep, hcard, hRO, hRep⟩` from `exists_reps (GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv) O hOc hOo (p.1 ^ j) hsO (θ ^ j) (hpow j)`. Set `G : Finset (Fin n × (Fin n → (Fv F v ⊗[F] E)))` to `((Finset.univ : Finset (Fin n)) ×ˢ Fintype.piFinset (fun _ : Fin n => Rep)).image fun q => (q.1, Function.update q.2 q.1 1)`. Use `⟨G, ?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `h1 : G.card ≤ n * Rep.card ^ n`. Use `Finset.card_image_le.trans ?_` and prove the remaining obligations. Simplify using `[Finset.card_product, Fintype.card_piFinset_const]`. Establish `h2 : (G.card : ℝ≥0) ≤ n * (Rep.card : ℝ≥0) ^ n` using `by exact_mod_cast h1`. Use `h2.trans ?_` and prove the remaining obligations.

Rewrite using `[pow_mul, inv_pow]`. Use `gcongr`. Introduce `q hq`. Take `⟨⟨l, r⟩, hm, rfl⟩` from `Finset.mem_image.1 hq`. Establish `hr` using `Fintype.mem_piFinset.1 (Finset.mem_product.1 hm).2`.

Use `⟨fun i => ?_, by simp⟩` and prove the remaining obligations. Distinguish the cases in `hi : i = l`. Substitute `hi` using the available equality. Simplify using `using O.one_mem`. Simplify `hRO _ (hr i)` using `[Function.update_of_ne hi]`.

Introduce and unpack `X ⟨hX, l, a0, ha0, hl0, hk⟩ choose r hrRep o ho hoe using fun i => hRep (a0 i) (ha0 i)`. Use `⟨(l, Function.update r l 1), ?_, ?_⟩` and prove the remaining obligations. Use `Finset.mem_image.2 ⟨(l, r), Finset.mem_product.2 ⟨Finset.mem_univ _, ?_⟩, rfl⟩` and prove the remaining obligations. Conclude with `Fintype.mem_piFinset.2 hrRep`. Use `rmul_mem_tupIn (Fv F v) (L : Set (Fv F v ⊗[F] E)) (p.1 ^ j) l _ X hX fun k => ?_` and prove the remaining obligations.

Use `sum_near O L _ X hX l _ a0 (by simp [hl0]) (fun i hi => ?_) k ?_` and prove the remaining obligations. Use `⟨- o i, O.neg_mem (ho i), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Function.update r l 1 i - a0 i = _`. Rewrite using `[Function.update_of_ne hi, mul_neg, ← hoe i]`. Normalize the expressions using the abelian group laws.

Rewrite using `[Units.val_pow_eq_pow_val]`. Conclude with `hk k`.
-/
theorem GlobalTheory.CompanionTheory.AvgFree.nearNF_cover : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ (O : Subring (Fv F v ⊗[F] E)) (S : Finset ((Fv F v ⊗[F] E)ˣ × (Fv F v ⊗[F] E))), IsOrdData (Fv F v) σ b lv O S → ∀ L : Submodule O (Fv F v ⊗[F] E), IsCompact (L : Set (Fv F v ⊗[F] E)) → IsOpen (L : Set (Fv F v ⊗[F] E)) → ∀ (n M : ℕ), 0 < n → ∀ p ∈ S, ∀ θ : ℝ≥0, (∀ Y : Set (Fv F v ⊗[F] E), (GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv) ((fun x => (p.1 : (Fv F v ⊗[F] E)) * x) '' Y) = θ * (GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv) Y) → ∀ j : ℕ, ∃ G : Finset (Fin n × (Fin n → (Fv F v ⊗[F] E))), ((G.card : ℝ≥0) ≤ n * (θ⁻¹) ^ (j * n)) ∧ (∀ q ∈ G, (∀ i, q.2 i ∈ O) ∧ q.2 q.1 = 1) ∧ ∀ X ∈ nearNF (M := M) (n := n) (Fv F v) (O : Set (Fv F v ⊗[F] E)) (L : Set (Fv F v ⊗[F] E)) (p.1 : (Fv F v ⊗[F] E)) j, ∃ q ∈ G, GlobalTheory.CompanionTheory.SW.rmul (Fv F v) X (eMat (Fv F v) q.1 q.2 * dMat (Fv F v) q.1 ((p.1 ^ j)⁻¹ : (Fv F v ⊗[F] E)ˣ)) ∈ tupIn (Fv F v) (L : Set (Fv F v ⊗[F] E)) := by
  intro F E _ _ _ _ _ σ hσ d b v lv hlv O S hOrd L _ _ n M _ p hp θ hθ j
  classical
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨a1, a2, a3, a4, -, -, -, a8, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  haveI := hlv.1
  obtain ⟨hK, -, -⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Fv F v) d b lv hlv.1
  haveI := hK
  obtain ⟨hOc, hOo, -, hS, -⟩ := hOrd
  have htO : (p.1 : Fv F v ⊗[F] E) ∈ O := (hS p hp).1
  have hpow : ∀ (i : ℕ) (Y : Set (Fv F v ⊗[F] E)),
      GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv ((fun x => ((p.1 ^ i : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) * x) '' Y) =
        ((θ ^ i : ℝ≥0) : ℝ≥0∞) * GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv Y := by
    intro i
    induction i with
    | zero => intro Y; simp
    | succ i ih =>
      intro Y
      have e : (fun x => ((p.1 ^ (i + 1) : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) * x) '' Y =
          (fun x => (p.1 : Fv F v ⊗[F] E) * x) ''
            ((fun x => ((p.1 ^ i : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) * x) '' Y) := by
        rw [Set.image_image]
        refine Set.image_congr fun x _ => ?_
        rw [pow_succ', Units.val_mul, mul_assoc]
      rw [e, hθ, ih, pow_succ', ENNReal.coe_mul, mul_assoc]
  have hsO : ((p.1 ^ j : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ O := by
    rw [Units.val_pow_eq_pow_val]
    exact O.pow_mem htO j
  obtain ⟨Rep, hcard, hRO, hRep⟩ := exists_reps (GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv) O hOc hOo (p.1 ^ j) hsO
    (θ ^ j) (hpow j)
  let G : Finset (Fin n × (Fin n → (Fv F v ⊗[F] E))) :=
    ((Finset.univ : Finset (Fin n)) ×ˢ Fintype.piFinset (fun _ : Fin n => Rep)).image
      fun q => (q.1, Function.update q.2 q.1 1)
  refine ⟨G, ?_, ?_, ?_⟩
  · have h1 : G.card ≤ n * Rep.card ^ n := by
      refine Finset.card_image_le.trans ?_
      simp [Finset.card_product, Fintype.card_piFinset_const]
    have h2 : (G.card : ℝ≥0) ≤ n * (Rep.card : ℝ≥0) ^ n := by exact_mod_cast h1
    refine h2.trans ?_
    rw [pow_mul, inv_pow]
    gcongr
  · intro q hq
    obtain ⟨⟨l, r⟩, hm, rfl⟩ := Finset.mem_image.1 hq
    have hr := Fintype.mem_piFinset.1 (Finset.mem_product.1 hm).2
    refine ⟨fun i => ?_, by simp⟩
    by_cases hi : i = l
    · subst hi
      simpa using O.one_mem
    · simpa [Function.update_of_ne hi] using hRO _ (hr i)
  · rintro X ⟨hX, l, a0, ha0, hl0, hk⟩
    choose r hrRep o ho hoe using fun i => hRep (a0 i) (ha0 i)
    refine ⟨(l, Function.update r l 1), ?_, ?_⟩
    · refine Finset.mem_image.2 ⟨(l, r), Finset.mem_product.2 ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      exact Fintype.mem_piFinset.2 hrRep
    · refine rmul_mem_tupIn (Fv F v) (L : Set (Fv F v ⊗[F] E)) (p.1 ^ j) l _ X hX fun k => ?_
      refine sum_near O L _ X hX l _ a0 (by simp [hl0]) (fun i hi => ?_) k ?_
      · refine ⟨- o i, O.neg_mem (ho i), ?_⟩
        change Function.update r l 1 i - a0 i = _
        rw [Function.update_of_ne hi, mul_neg, ← hoe i]
        abel
      · rw [Units.val_pow_eq_pow_val]
        exact hk k
