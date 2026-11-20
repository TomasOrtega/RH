import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.FormalDegreeBessel.FinalG

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.RankOneEmbeddings.Wb

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ}

abbrev mid (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := r ≤ i.val ∧ i.val ≤ r + k

/- English proof (translation)
Establish `hj' : ¬ (r ≤ j.val ∧ j.val ≤ r + k)` using `hj`. Simplify using `only [embWb]`. Rewrite using `[dif_neg (fun h => hj' h.2)]`. Distinguish the cases in `hqj : q = j`. Substitute `hqj` using the available equality.

Rewrite using `[if_pos ⟨rfl, hj'⟩, if_pos rfl]`. Rewrite using `[if_neg (fun h => hqj h.1), if_neg hqj]`.
-/
lemma emb_out_col (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (q j : Fin (2 * r + k + 1)) (hj : ¬ mid k r j) :
    embWb k r μ q j = if q = j then 1 else 0 := by
  have hj' : ¬ (r ≤ j.val ∧ j.val ≤ r + k) := hj
  simp only [embWb]
  rw [dif_neg (fun h => hj' h.2)]
  by_cases hqj : q = j
  · subst hqj
    rw [if_pos ⟨rfl, hj'⟩, if_pos rfl]
  · rw [if_neg (fun h => hqj h.1), if_neg hqj]

/- English proof (translation)
Establish `hq' : ¬ (r ≤ q.val ∧ q.val ≤ r + k)` using `hq`. Simplify using `only [embWb]`. Rewrite using `[dif_neg (fun h => hq' h.1)]`. Distinguish the cases in `hqj : q = j`. Substitute `hqj` using the available equality.

Rewrite using `[if_pos ⟨rfl, hq'⟩, if_pos rfl]`. Rewrite using `[if_neg (fun h => hqj h.1), if_neg hqj]`.
-/
lemma emb_out_row (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (q j : Fin (2 * r + k + 1)) (hq : ¬ mid k r q) :
    embWb k r μ q j = if q = j then 1 else 0 := by
  have hq' : ¬ (r ≤ q.val ∧ q.val ≤ r + k) := hq
  simp only [embWb]
  rw [dif_neg (fun h => hq' h.1)]
  by_cases hqj : q = j
  · subst hqj
    rw [if_pos ⟨rfl, hq'⟩, if_pos rfl]
  · rw [if_neg (fun h => hqj h.1), if_neg hqj]

/- English proof (translation)
Simplify using `only [embWb]`. Rewrite using `[dif_pos ⟨hq, hj⟩]`.
-/
lemma emb_mid (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (q j : Fin (2 * r + k + 1)) (hq : mid k r q) (hj : mid k r j) :
    embWb k r μ q j = μ ⟨q.val - r, by have := hq; omega⟩ ⟨j.val - r, by have := hj; omega⟩ := by
  simp only [embWb]
  rw [dif_pos ⟨hq, hj⟩]

/- English proof (translation)
Use `l.isLt` as an intermediate fact. Use `show r ≤ r + l.val ∧ r + l.val ≤ r + k`. Use linear arithmetic over natural numbers and integers.
-/
lemma wI_mid (l : Fin (k + 1)) : mid k r (wI k r l) := by
  have := l.isLt
  show r ≤ r + l.val ∧ r + l.val ≤ r + k
  omega

/- English proof (translation)
The claim follows from `Fin.ext (by simp [wI])`.
-/
private lemma fin_wI_sub_eq_self (q : Fin (k + 1)) (h : (wI k r q).val - r < k + 1) :
    (⟨(wI k r q).val - r, h⟩ : Fin (k + 1)) = q :=
  Fin.ext (by simp [wI])

/- English proof (translation)
Rewrite using `[emb_mid (r := r) μ _ _ (wI_mid i) (wI_mid j)]`. Simplify using `only [fin_wI_sub_eq_self]`.
-/
lemma emb_wI (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i j : Fin (k + 1)) :
    embWb k r μ (wI k r i) (wI k r j) = μ i j := by
  rw [emb_mid (r := r) μ _ _ (wI_mid i) (wI_mid j)]
  simp only [fin_wI_sub_eq_self]

/- English proof (translation)
Establish `hinj : Function.Injective (wI k r)` using `fun a b h => by`. Simplify `h` using `[wI, Fin.ext_iff]`. Combine the equalities or inequalities in the displayed calculation. Use `(Finset.sum_subset (Finset.subset_univ _) ?_).symm` and prove the remaining obligations. Introduce `p _ hp`.

Apply `hf` to reduce the goal to its premises. Introduce `hm`. Apply `hp` to reduce the goal to its premises. Rewrite using `[Finset.mem_map]`. Use `⟨⟨p.val - r, by have := hm.2; omega⟩, Finset.mem_univ _, ?_⟩` and prove the remaining obligations.

Apply `Fin.ext` to reduce the goal to its premises. Use `hm.1` as an intermediate fact. Use `show r + (p.val - r) = p.val`. Use linear arithmetic over natural numbers and integers. Use `_ = ∑ q : Fin (k + 1), f (wI k r q) := Finset.sum_map _ _ _`.
-/
private lemma sum_eq_sum_wI_of_eq_zero_off_mid (f : Fin (2 * r + k + 1) → ℂ) (hf : ∀ p, ¬ mid k r p → f p = 0) :
    ∑ p, f p = ∑ q : Fin (k + 1), f (wI k r q) := by
  have hinj : Function.Injective (wI k r) := fun a b h => by
    simpa [wI, Fin.ext_iff] using h
  calc ∑ p, f p = ∑ p ∈ Finset.univ.map ⟨wI k r, hinj⟩, f p := by
        refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
        intro p _ hp
        apply hf
        intro hm
        apply hp
        rw [Finset.mem_map]
        refine ⟨⟨p.val - r, by have := hm.2; omega⟩, Finset.mem_univ _, ?_⟩
        apply Fin.ext
        have := hm.1
        show r + (p.val - r) = p.val
        omega
    _ = ∑ q : Fin (k + 1), f (wI k r q) := Finset.sum_map _ _ _

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply]`. Distinguish the cases in `hi : mid k r i`. Distinguish the cases in `hj : mid k r j`. Rewrite using `[emb_mid _ _ _ hi hj, Matrix.mul_apply, sum_eq_sum_wI_of_eq_zero_off_mid]`.

Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[emb_mid _ _ _ hi (wI_mid q), emb_mid _ _ _ (wI_mid q) hj]`. Simplify using `only [fin_wI_sub_eq_self]`. Introduce `p hp`. Rewrite using `[emb_out_col a i p hp, if_neg (fun (h : i = p) => hp (h ▸ hi)), zero_mul]`.

Simplify using `[emb_out_col b _ _ hj]`. Rewrite using `[emb_out_col _ _ _ hj, emb_out_col _ _ _ hj]`. Simplify using `[emb_out_row a _ _ hi]`. Rewrite using `[emb_out_row _ _ _ hi, emb_out_row _ _ _ hi]`.
-/
lemma emb_mul (a b : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    embWb k r (a * b) = embWb k r a * embWb k r b := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : mid k r i
  · by_cases hj : mid k r j
    · rw [emb_mid _ _ _ hi hj, Matrix.mul_apply, sum_eq_sum_wI_of_eq_zero_off_mid]
      · refine Finset.sum_congr rfl fun q _ => ?_
        rw [emb_mid _ _ _ hi (wI_mid q), emb_mid _ _ _ (wI_mid q) hj]
        simp only [fin_wI_sub_eq_self]
      · intro p hp
        rw [emb_out_col a i p hp, if_neg (fun (h : i = p) => hp (h ▸ hi)), zero_mul]
    · simp [emb_out_col b _ _ hj]
      rw [emb_out_col _ _ _ hj, emb_out_col _ _ _ hj]
  · simp [emb_out_row a _ _ hi]
    rw [emb_out_row _ _ _ hi, emb_out_row _ _ _ hi]

/- English proof (translation)
Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Simplify using `only [embWb]`. Use `split_ifs`. Apply the tactic sequence `all_goals first`. Consider the case `exact continuous_const`.

Consider the case `exact (continuous_apply _).comp (continuous_apply _)`. Consider the case `fun_prop`.
-/
lemma emb_cont : Continuous (fun μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ => (embWb k r μ : Mt k r)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [embWb]
  split_ifs
  all_goals first
    | exact continuous_const
    | exact (continuous_apply _).comp (continuous_apply _)
    | fun_prop

def sg (k : ℕ) : Fin (k + 1) → Bool := fun j => decide (j ≠ Fin.last k)

/- English proof (translation)
Unfold `Jm Hb sg`. Use `congr 1`. Use function extensionality and compare the values at `j`. Apply the tactic sequence `by_cases h : j = Fin.last k <;> simp [h]`.
-/
lemma Jm_sg : Jm (sg k) = Hb k := by
  unfold Jm Hb sg
  congr 1
  funext j
  by_cases h : j = Fin.last k <;> simp [h]

/- English proof (translation)
Establish `hc : ∀ v : Fin (2 * r + k + 1) → ℂ, Continuous fun g : Mat k r => g *ᵥ v` using `fun v => by first`. Consider the case `fun_prop`. Consider the case `exact continuous_id.matrix_mulVec continuous_const`. Unfold `UWb GV UH`. Rewrite using `[Set.setOf_and]`.

Use `IsClosed.inter ?_ ?_` and prove the remaining obligations. Simplify using `only [Set.setOf_mem_eq]`. Use `isClosed_eq ?_ continuous_const` and prove the remaining obligations. Use `first`. Consider the case `fun_prop`.

Consider the case `exact (continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id`. Rewrite using `[Set.setOf_forall]`. Use `isClosed_iInter fun a => ?_` and prove the remaining obligations. Rewrite using `[Set.setOf_and]`. Conclude with `(isClosed_eq (hc _) continuous_const).inter (isClosed_eq (hc _) continuous_const)`.
-/
lemma uwb_closed : IsClosed (UWb k r) := by
  have hc : ∀ v : Fin (2 * r + k + 1) → ℂ, Continuous fun g : Mat k r => g *ᵥ v := fun v => by
    first
      | fun_prop
      | exact continuous_id.matrix_mulVec continuous_const
  unfold UWb GV UH
  rw [Set.setOf_and]
  refine IsClosed.inter ?_ ?_
  · simp only [Set.setOf_mem_eq]
    refine isClosed_eq ?_ continuous_const
    first
      | fun_prop
      | exact (continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id
  · rw [Set.setOf_forall]
    refine isClosed_iInter fun a => ?_
    rw [Set.setOf_and]
    exact (isClosed_eq (hc _) continuous_const).inter (isClosed_eq (hc _) continuous_const)

def Φ (k r : ℕ) (g : UJ (sg k)) : Mt k r :=
  embWb k r ((g : (Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)ˣ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)

/- English proof (translation)
Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Simplify using `only [lmulM, Matrix.mul_apply, Matrix.of_apply]`. Use `fun_prop`.
-/
lemma lmulM_cont (a : Mat k r) : Continuous (lmulM a : Mt k r → Mt k r) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [lmulM, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

/- English proof (translation)
Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Simplify using `only [rmulF, Matrix.mul_apply, Matrix.of_apply]`. Use `fun_prop`.
-/
lemma rmulF_cont {n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) : Continuous (rmulF a) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [rmulF, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

end Formalism.FourierDecayAlt.P.RankOneEmbeddings.Wb

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.RankOneEmbeddings.Wb

/- English proof (translation)
Introduce `hEmb hUni hBall hFacts k r`. Establish `hΦc : Continuous (Φ k r)` using `emb_cont.comp (hEmb (k + 1) (sg k)).1.continuous`. Establish `hΦ : Measurable (Φ k r)` using `hΦc.measurable`. Establish `hU : UWb k r = embWb k r '' {μ | μᴴ * Hb k * μ = Hb k}` using `(hFacts k r).1`. Establish `hmem : ∀ g : UJ (sg k), (Φ k r g : Mat k r) ∈ UWb k r`.

Introduce `g`. Rewrite using `[hU]`. Use `⟨_, ?_, rfl⟩` and prove the remaining obligations. Establish `: inUJ (sg k) ((g : (Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)ˣ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)` using `g.2`. Unfold `inUJ at this`.

Rewrite `this` using `[Jm_sg]`. Conclude with `this`. Establish `hlift : ∀ a ∈ UWb k r, ∃ g₀ : UJ (sg k), a = embWb k r ((g₀ : (Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)ˣ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)`. Introduce `a ha`. Rewrite `ha` using `[hU]`.

Take `⟨α, hα, rfl⟩` from `ha`. Establish `h1 : α ∈ {g | inUJ (sg k) g}` using `by show αᴴ * Jm (sg k) * α = Jm (sg k)`. Rewrite using `[Jm_sg]`. Conclude with `hα`. Rewrite `h1` using `[← (hEmb (k + 1) (sg k)).2]`.

Take `⟨g₀, hg₀⟩` from `h1`. Conclude with `⟨g₀, by rw [← hg₀]⟩`. Use `⟨(muG (sg k)).map (Φ k r), ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Measure.map_apply hΦ (show IsOpen ((UWb k r)ᶜ : Set (Mt k r)) from uwb_closed.isOpen_compl).measurableSet]`. Establish `: Φ k r ⁻¹' ((UWb k r)ᶜ : Set (Mt k r)) = ∅`.

Use extensionality with `g`. Simplify using `only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]`. Conclude with `fun h => h (hmem g)`. Rewrite using `[this, measure_empty]`. Introduce `a ha`.

Take `⟨g₀, hg₀⟩` from `hlift a ha`. Rewrite using `[Measure.map_map (lmulM_cont _).measurable hΦ]`. Establish `: (lmulM a ∘ Φ k r) = Φ k r ∘ (fun x => g₀ * x)`. Use function extensionality and compare the values at `x`. Rewrite using `[hg₀]`.

Conclude with `(emb_mul _ _).symm`. Rewrite using `[this, ← Measure.map_map hΦ (continuous_const_mul g₀).measurable, map_mul_left_eq_self]`. Introduce `a ha`. Take `⟨g₀, hg₀⟩` from `hlift a ha`. Rewrite using `[Measure.map_map (rmulF_cont _).measurable hΦ]`.

Establish `: (rmulF a ∘ Φ k r) = Φ k r ∘ (fun x => x * g₀)`. Use function extensionality and compare the values at `x`. Rewrite using `[hg₀]`. Conclude with `(emb_mul _ _).symm`. Rewrite using `[this, ← Measure.map_map hΦ (continuous_mul_const g₀).measurable, hUni (k + 1) (sg k) g₀]`.

Introduce `K hK`. Rewrite using `[Measure.map_apply hΦ hK.isClosed.measurableSet]`. Establish `hφ : Continuous (fun x : Mt k r => ∑ i : Fin (k + 1), ∑ j : Fin (k + 1), ‖x (wI k r i) (wI k r j)‖ ^ 2)`. Use `continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_` and prove the remaining obligations. Conclude with `((continuous_apply_apply (wI k r i) (wI k r j)).norm).pow 2`.

Take `⟨R, hR⟩` from `hK.bddAbove_image hφ.continuousOn`. Use `lt_of_le_of_lt (measure_mono ?_) (hBall (k + 1) (sg k) R)` and prove the remaining obligations. Introduce `g hg`. Establish `h1` using `hR ⟨_, hg, rfl⟩`. Use `show hsG g ≤ R`.

Unfold `hsG hs`. Use `le_of_eq_of_le ?_ h1` and prove the remaining obligations. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `show _ = ‖embWb k r _ (wI k r i) (wI k r j)‖ ^ 2`. Rewrite using `[emb_wI]`.

Introduce `h0`. Rewrite `h0` using `[Measure.map_eq_zero_iff hΦ.aemeasurable]`. Use `isOpen_univ.measure_ne_zero (muG (sg k)) Set.univ_nonempty` as an intermediate fact. Rewrite `this` using `[h0]`. Conclude with `this rfl`.
-/
theorem weyl_measure_from_diagonal : Formalism.FourierDecayAlt.B2.WbFromDiag := by
  intro hEmb hUni hBall hFacts k r
  have hΦc : Continuous (Φ k r) := emb_cont.comp (hEmb (k + 1) (sg k)).1.continuous
  have hΦ : Measurable (Φ k r) := hΦc.measurable
  have hU : UWb k r = embWb k r '' {μ | μᴴ * Hb k * μ = Hb k} := (hFacts k r).1
  have hmem : ∀ g : UJ (sg k), (Φ k r g : Mat k r) ∈ UWb k r := by
    intro g
    rw [hU]
    refine ⟨_, ?_, rfl⟩
    have : inUJ (sg k) ((g : (Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)ˣ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) := g.2
    unfold inUJ at this
    rw [Jm_sg] at this
    exact this
  have hlift : ∀ a ∈ UWb k r, ∃ g₀ : UJ (sg k), a = embWb k r
      ((g₀ : (Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)ˣ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) := by
    intro a ha
    rw [hU] at ha
    obtain ⟨α, hα, rfl⟩ := ha
    have h1 : α ∈ {g | inUJ (sg k) g} := by
      show αᴴ * Jm (sg k) * α = Jm (sg k)
      rw [Jm_sg]; exact hα
    rw [← (hEmb (k + 1) (sg k)).2] at h1
    obtain ⟨g₀, hg₀⟩ := h1
    exact ⟨g₀, by rw [← hg₀]⟩
  refine ⟨(muG (sg k)).map (Φ k r), ?_, ?_, ?_, ?_, ?_⟩
  · rw [Measure.map_apply hΦ (show IsOpen ((UWb k r)ᶜ : Set (Mt k r)) from uwb_closed.isOpen_compl).measurableSet]
    have : Φ k r ⁻¹' ((UWb k r)ᶜ : Set (Mt k r)) = ∅ := by
      ext g
      simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
      exact fun h => h (hmem g)
    rw [this, measure_empty]
  · intro a ha
    obtain ⟨g₀, hg₀⟩ := hlift a ha
    rw [Measure.map_map (lmulM_cont _).measurable hΦ]
    have : (lmulM a ∘ Φ k r) = Φ k r ∘ (fun x => g₀ * x) := by
      funext x
      rw [hg₀]
      exact (emb_mul _ _).symm
    rw [this, ← Measure.map_map hΦ (continuous_const_mul g₀).measurable, map_mul_left_eq_self]
  · intro a ha
    obtain ⟨g₀, hg₀⟩ := hlift a ha
    rw [Measure.map_map (rmulF_cont _).measurable hΦ]
    have : (rmulF a ∘ Φ k r) = Φ k r ∘ (fun x => x * g₀) := by
      funext x
      rw [hg₀]
      exact (emb_mul _ _).symm
    rw [this, ← Measure.map_map hΦ (continuous_mul_const g₀).measurable, hUni (k + 1) (sg k) g₀]
  · intro K hK
    rw [Measure.map_apply hΦ hK.isClosed.measurableSet]
    have hφ : Continuous (fun x : Mt k r => ∑ i : Fin (k + 1), ∑ j : Fin (k + 1), ‖x (wI k r i) (wI k r j)‖ ^ 2) := by
      refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
      exact ((continuous_apply_apply (wI k r i) (wI k r j)).norm).pow 2
    obtain ⟨R, hR⟩ := hK.bddAbove_image hφ.continuousOn
    refine lt_of_le_of_lt (measure_mono ?_) (hBall (k + 1) (sg k) R)
    intro g hg
    have h1 := hR ⟨_, hg, rfl⟩
    show hsG g ≤ R
    unfold hsG hs
    refine le_of_eq_of_le ?_ h1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    show _ = ‖embWb k r _ (wI k r i) (wI k r j)‖ ^ 2
    rw [emb_wI]
  · intro h0
    rw [Measure.map_eq_zero_iff hΦ.aemeasurable] at h0
    have := isOpen_univ.measure_ne_zero (muG (sg k)) Set.univ_nonempty
    rw [h0] at this
    exact this rfl

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

/- English proof (translation)
Establish `h1 : Measurable[MeasurableSpace.comap π inferInstance] F`. Introduce `B hB`. Establish `hA : MeasurableSet (F ⁻¹' B)` using `hF hB`. Establish `hsat : π ⁻¹' (π '' (F ⁻¹' B)) = F ⁻¹' B`. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, hxy⟩ show F x ∈ B`. Rewrite using `[hfib x y hxy.symm]`. Conclude with `hy`. Introduce `hx`.

Conclude with `⟨x, hx, rfl⟩`. Rewrite `hA` using `[← hsat]`. Establish `: MeasurableSpace.CountablySeparated (Set.range π)` using `MeasurableSpace.Subtype.countablySeparated`. Establish `h2` using `(hπ.measurableSet_preimage_iff_preimage_val).mp hA`. Take `⟨B', hB', hBB⟩` from `h2`.

Use `⟨B', hB', ?_⟩` and prove the remaining obligations. Rewrite using `[← hsat]`. Use extensionality with `x`. Use `congrArg (fun S : Set (Set.range π) => (⟨π x, x, rfl⟩ : Set.range π) ∈ S) hBB` as an intermediate fact. Simplify using `using this`.

Take `⟨G, hG, hFG⟩` from `h1.exists_eq_measurable_comp`. Conclude with `⟨G, hG, fun x => congrFun hFG x⟩`.
-/
theorem factor_meas {X V : Type*} [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace V]
    [MeasurableSpace.CountablySeparated V] (π : X → V) (hπ : Measurable π) (F : X → ℝ≥0∞) (hF : Measurable F)
    (hfib : ∀ x y, π x = π y → F x = F y) : ∃ G : V → ℝ≥0∞, Measurable G ∧ ∀ x, F x = G (π x) := by
  have h1 : Measurable[MeasurableSpace.comap π inferInstance] F := by
    intro B hB
    have hA : MeasurableSet (F ⁻¹' B) := hF hB
    have hsat : π ⁻¹' (π '' (F ⁻¹' B)) = F ⁻¹' B := by
      ext x; constructor
      · rintro ⟨y, hy, hxy⟩
        show F x ∈ B
        rw [hfib x y hxy.symm]; exact hy
      · intro hx; exact ⟨x, hx, rfl⟩
    rw [← hsat] at hA
    have : MeasurableSpace.CountablySeparated (Set.range π) := MeasurableSpace.Subtype.countablySeparated
    have h2 := (hπ.measurableSet_preimage_iff_preimage_val).mp hA
    obtain ⟨B', hB', hBB⟩ := h2
    refine ⟨B', hB', ?_⟩
    rw [← hsat]
    ext x
    have := congrArg (fun S : Set (Set.range π) => (⟨π x, x, rfl⟩ : Set.range π) ∈ S) hBB
    simpa using this
  obtain ⟨G, hG, hFG⟩ := h1.exists_eq_measurable_comp
  exact ⟨G, hG, fun x => congrFun hFG x⟩

variable {k r : ℕ}

abbrev Vc (k r : ℕ) := Fin (2 * r + k + 1) → ℂ

def mvM (p : Mt k r × Vc k r) : Vc k r := (Matrix.of p.1 : Mat k r) *ᵥ p.2

/- English proof (translation)
Use `continuous_pi fun i => ?_` and prove the remaining obligations. Use `first`. Consider the case `fun_prop`. Consider the case `(simp only [mvM, Matrix.mulVec, dotProduct, Matrix.of_apply]; fun_prop)`. Consider the case `(simp only [mvM, Matrix.mulVec, Matrix.dotProduct, Matrix.of_apply]; fun_prop)`.
-/
theorem mvM_cont : Continuous (mvM (k := k) (r := r)) := by
  refine continuous_pi fun i => ?_
  first
    | fun_prop
    | (simp only [mvM, Matrix.mulVec, dotProduct, Matrix.of_apply]; fun_prop)
    | (simp only [mvM, Matrix.mulVec, Matrix.dotProduct, Matrix.of_apply]; fun_prop)

/- English proof (translation)
Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Simplify using `only [mulM, Matrix.mul_apply, Matrix.of_apply]`. Use `fun_prop`.
-/
theorem mulM_cont : Continuous (mulM (k := k) (r := r)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [mulM, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

def adjF (x : Mt k r) : Mt k r := (Matrix.of x : Mat k r).adjugate
def detF (x : Mt k r) : ℂ := (Matrix.of x : Mat k r).det

/- English proof (translation)
Use `first`. Consider the case `exact continuous_id.matrix_det`. Consider the case `(unfold detF; fun_prop)`.
-/
theorem detF_cont : Continuous (detF (k := k) (r := r)) := by
  first
    | exact continuous_id.matrix_det
    | (unfold detF; fun_prop)
/- English proof (translation)
Use `first`. Consider the case `exact continuous_id.matrix_adjugate`. Consider the case `(unfold adjF; fun_prop)`.
-/
theorem adjF_cont : Continuous (adjF (k := k) (r := r)) := by
  first
    | exact continuous_id.matrix_adjugate
    | (unfold adjF; fun_prop)

/- English proof (translation)
Use function extensionality and compare the values at `x`. Use `show ((Matrix.of x : Mat k r)⁻¹ : Mat k r) = (detF x)⁻¹ • adjF x`. Rewrite using `[Matrix.inv_def, Ring.inverse_eq_inv]`. Both sides reduce to the same expression.
-/
theorem invM_smul : (invM : Mt k r → Mt k r) = fun x => (detF x)⁻¹ • adjF x := by
  funext x
  show ((Matrix.of x : Mat k r)⁻¹ : Mat k r) = (detF x)⁻¹ • adjF x
  rw [Matrix.inv_def, Ring.inverse_eq_inv]
  rfl

/- English proof (translation)
Rewrite using `[invM_smul]`. Use `measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_` and prove the remaining obligations. Establish `h1 : Measurable fun x : Mt k r => (detF x)⁻¹` using `detF_cont.measurable.inv`. Establish `h2 : Measurable fun x : Mt k r => adjF x i j` using `((continuous_apply j).comp ((continuous_apply i).comp adjF_cont)).measurable`. Conclude with `h1.mul h2`.
-/
theorem invM_meas : Measurable (invM : Mt k r → Mt k r) := by
  rw [invM_smul]
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  have h1 : Measurable fun x : Mt k r => (detF x)⁻¹ := detF_cont.measurable.inv
  have h2 : Measurable fun x : Mt k r => adjF x i j :=
    ((continuous_apply j).comp ((continuous_apply i).comp adjF_cont)).measurable
  exact h1.mul h2

/- English proof (translation)
Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Simplify using `only [lmulM, Matrix.mul_apply, Matrix.of_apply]`. Use `fun_prop`.
-/
theorem lmulM_cont (a : Mat k r) : Continuous (lmulM a : Mt k r → Mt k r) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [lmulM, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

def embF (k r : ℕ) (μ : Fin (k + 1) → Fin (k + 1) → ℂ) : Mt k r := embWb k r (Matrix.of μ)

/- English proof (translation)
Conclude with `Formalism.FourierDecayAlt.P.RankOneEmbeddings.Wb.emb_cont`.
-/
theorem embF_cont : Continuous (embF k r) := by
  exact Formalism.FourierDecayAlt.P.RankOneEmbeddings.Wb.emb_cont

/- English proof (translation)
Use `haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩`. Use `infer_instance`.
-/
theorem haar_sigmaFinite {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) : SigmaFinite μ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
  infer_instance

/- English proof (translation)
The claim follows from `hU.measurableSet.standardBorel`.
-/
example (U : Set (Mt k r)) (hU : IsClosed U) : StandardBorelSpace U := hU.measurableSet.standardBorel

end Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1

namespace Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ}

def Om (k r : ℕ) (z z' : Vc k r) : Set ℂ := {ζ | Tz k r z * Tz k r z' < Complex.normSq ζ}

/- English proof (translation)
Conclude with `isOpen_lt continuous_const Complex.continuous_normSq`.
-/
theorem Om_open (z z' : Vc k r) : IsOpen (Om k r z z') := by
  exact isOpen_lt continuous_const Complex.continuous_normSq

open Classical in

def secF (k r : ℕ) (z z' : Vc k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (ζ : ℂ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := if ζ ∈ Om k r z z' then μsec ζ else 1

/- English proof (translation)
Unfold `secF`. Conclude with `if_pos h`.
-/
theorem secF_on {z z' : Vc k r} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} {ζ : ℂ} (h : ζ ∈ Om k r z z') :
    secF k r z z' μsec ζ = μsec ζ := by
  unfold secF
  exact if_pos h

/- English proof (translation)
Unfold `secF`. Conclude with `if_neg h`.
-/
theorem secF_off {z z' : Vc k r} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} {ζ : ℂ} (h : ζ ∉ Om k r z z') :
    secF k r z z' μsec ζ = 1 := by
  unfold secF
  exact if_neg h

/- English proof (translation)
Establish `hs` using `hsec`. Unfold `IsSection at hs ⊢`. Use `⟨fun i j => (hs.1 i j).congr fun ζ hζ => ?_, fun ζ hζ => ?_⟩` and prove the remaining obligations. Use `show secF k r z z' μsec ζ i j = μsec ζ i j`. Rewrite using `[secF_on (μsec := μsec) (show ζ ∈ Om k r z z' from hζ)]`.

Rewrite using `[secF_on (μsec := μsec) (show ζ ∈ Om k r z z' from hζ)]`. Conclude with `hs.2 ζ hζ`.
-/
theorem secF_section {z z' : Vc k r} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hsec : IsSection k r z z' μsec) : IsSection k r z z' (secF k r z z' μsec) := by
  have hs := hsec
  unfold IsSection at hs ⊢
  refine ⟨fun i j => (hs.1 i j).congr fun ζ hζ => ?_, fun ζ hζ => ?_⟩
  · show secF k r z z' μsec ζ i j = μsec ζ i j
    rw [secF_on (μsec := μsec) (show ζ ∈ Om k r z z' from hζ)]
  · rw [secF_on (μsec := μsec) (show ζ ∈ Om k r z z' from hζ)]
    exact hs.2 ζ hζ

/- English proof (translation)
Establish `hs` using `hsec`. Unfold `IsSection at hs`. Distinguish the cases in `h : ζ ∈ Om k r z z'`. Rewrite using `[secF_on h]`. Conclude with `(hs.2 ζ h).1`.

Rewrite using `[secF_off h]`. Simplify using the standard rewrite rules.
-/
theorem secF_unit {z z' : Vc k r} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hsec : IsSection k r z z' μsec) (ζ : ℂ) :
    (secF k r z z' μsec ζ)ᴴ * Hb k * secF k r z z' μsec ζ = Hb k := by
  have hs := hsec
  unfold IsSection at hs
  by_cases h : ζ ∈ Om k r z z'
  · rw [secF_on h]
    exact (hs.2 ζ h).1
  · rw [secF_off h]
    simp

def MeasSec (s : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Prop :=
  @Measurable ℂ (Fin (k + 1) → Fin (k + 1) → ℂ) _ _ s

/- English proof (translation)
Establish `hs` using `hsec`. Unfold `IsSection at hs`. Unfold `MeasSec`. Use `measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_` and prove the remaining obligations. Establish `heq : (fun ζ => secF k r z z' μsec ζ i j) = (Om k r z z').piecewise (fun ζ => μsec ζ i j) (fun _ => (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) i j)`.

Use function extensionality and compare the values at `ζ`. Unfold `secF Set.piecewise`. Apply the tactic sequence `split_ifs <;> rfl`. Rewrite using `[heq]`. Conclude with `ContinuousOn.measurable_piecewise (hs.1 i j).continuousOn continuousOn_const (Om_open z z').measurableSet`.
-/
theorem secF_meas {z z' : Vc k r} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hsec : IsSection k r z z' μsec) : MeasSec (secF k r z z' μsec) := by
  classical
  have hs := hsec
  unfold IsSection at hs
  unfold MeasSec
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  have heq : (fun ζ => secF k r z z' μsec ζ i j) =
      (Om k r z z').piecewise (fun ζ => μsec ζ i j) (fun _ => (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) i j) := by
    funext ζ
    unfold secF Set.piecewise
    split_ifs <;> rfl
  rw [heq]
  exact ContinuousOn.measurable_piecewise (hs.1 i j).continuousOn continuousOn_const (Om_open z z').measurableSet

/- English proof (translation)
Unfold `zWeight`. Conclude with `Measurable.ite (measurableSet_le measurable_const Complex.continuous_normSq.measurable) ((Complex.continuous_normSq.measurable.sub_const _).pow_const _) measurable_const`.
-/
theorem zW_meas (k : ℕ) (T T' : ℝ) : Measurable (zWeight k T T') := by
  unfold zWeight
  exact Measurable.ite (measurableSet_le measurable_const Complex.continuous_normSq.measurable)
    ((Complex.continuous_normSq.measurable.sub_const _).pow_const _) measurable_const

/- English proof (translation)
Establish `hnull : (volume : Measure ℂ) (Metric.sphere (0 : ℂ) (Real.sqrt (Tz k r z * Tz k r z'))) = 0` using `Measure.addHaar_sphere volume _ _`. Establish `hae : ∀ᵐ ζ : ℂ, ζ ∉ Metric.sphere (0 : ℂ) (Real.sqrt (Tz k r z * Tz k r z'))`. Rewrite using `[ae_iff]`. Simplify using `only [not_not, Set.setOf_mem_eq]`. Conclude with `hnull`.

Use `filter_upwards [hae] with ζ hζ`. Distinguish the cases in `h : ζ ∈ Om k r z z'`. Conclude with `Or.inl h`. Use `right`. Establish `h0 : ¬ (Tz k r z * Tz k r z' < Complex.normSq ζ)` using `h`.

Establish `h' : Complex.normSq ζ ≤ Tz k r z * Tz k r z'` using `not_lt.1 h0`. Unfold `zWeight`. Rewrite using `[if_neg]`. Introduce `hle`. Apply `hζ` to reduce the goal to its premises.

Rewrite using `[mem_sphere_zero_iff_norm, ← le_antisymm h' hle, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]`.
-/
theorem ae_Om (z z' : Vc k r) :
    ∀ᵐ ζ : ℂ, ζ ∈ Om k r z z' ∨ zWeight k (Tz k r z) (Tz k r z') ζ = 0 := by
  have hnull : (volume : Measure ℂ) (Metric.sphere (0 : ℂ) (Real.sqrt (Tz k r z * Tz k r z'))) = 0 :=
    Measure.addHaar_sphere volume _ _
  have hae : ∀ᵐ ζ : ℂ, ζ ∉ Metric.sphere (0 : ℂ) (Real.sqrt (Tz k r z * Tz k r z')) := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_mem_eq]
    exact hnull
  filter_upwards [hae] with ζ hζ
  by_cases h : ζ ∈ Om k r z z'
  · exact Or.inl h
  · right
    have h0 : ¬ (Tz k r z * Tz k r z' < Complex.normSq ζ) := h
    have h' : Complex.normSq ζ ≤ Tz k r z * Tz k r z' := not_lt.1 h0
    unfold zWeight
    rw [if_neg]
    intro hle
    apply hζ
    rw [mem_sphere_zero_iff_norm, ← le_antisymm h' hle, Complex.normSq_eq_norm_sq,
      Real.sqrt_sq (norm_nonneg _)]

abbrev wd (k r : ℕ) (z z' : Vc k r) : Measure ℂ :=
  (volume : Measure ℂ).withDensity fun ζ => ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ)

def Phi (s : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (x : ℂ × (Mt k r × Mt k r)) : Mt k r :=
  mulM (mulM (invM x.2.1, embF k r (s x.1)), x.2.2)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Phi_eq (s : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (x : ℂ × (Mt k r × Mt k r)) :
    Phi s x = (Matrix.of x.2.1 : Mat k r)⁻¹ * embWb k r (s x.1) * Matrix.of x.2.2 := rfl

/- English proof (translation)
Conclude with `embF_cont.measurable.comp hs`.
-/
theorem embS_meas {s : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hs : MeasSec s) :
    Measurable fun ζ : ℂ => embF k r (s ζ) := by
  exact embF_cont.measurable.comp hs

/- English proof (translation)
Establish `h1 : Measurable fun x : ℂ × (Mt k r × Mt k r) => invM x.2.1` using `invM_meas.comp (measurable_fst.comp measurable_snd)`. Establish `h2 : Measurable fun x : ℂ × (Mt k r × Mt k r) => embF k r (s x.1)` using `(embS_meas (r := r) hs).comp measurable_fst`. Establish `h3 : Measurable fun x : ℂ × (Mt k r × Mt k r) => x.2.2` using `measurable_snd.comp measurable_snd`. Conclude with `mulM_cont.measurable.comp ((mulM_cont.measurable.comp (h1.prodMk h2)).prodMk h3)`.
-/
theorem Phi_meas {s : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hs : MeasSec s) : Measurable (Phi (r := r) s) := by
  have h1 : Measurable fun x : ℂ × (Mt k r × Mt k r) => invM x.2.1 :=
    invM_meas.comp (measurable_fst.comp measurable_snd)
  have h2 : Measurable fun x : ℂ × (Mt k r × Mt k r) => embF k r (s x.1) :=
    (embS_meas (r := r) hs).comp measurable_fst
  have h3 : Measurable fun x : ℂ × (Mt k r × Mt k r) => x.2.2 := measurable_snd.comp measurable_snd
  exact mulM_cont.measurable.comp ((mulM_cont.measurable.comp (h1.prodMk h2)).prodMk h3)

/- English proof (translation)
Establish `hF : Measurable fun x : ℂ × (Mt k r × Mt k r) => f (Phi s x)` using `hf.comp (Phi_meas hs)`. Rewrite using `[lintegral_map hf (Phi_meas hs), lintegral_prod _ hF.aemeasurable, lintegral_withDensity_eq_lintegral_mul _ ((zW_meas k _ _).ennreal_ofReal) hF.lintegral_prod_right']`. Both sides reduce to the same expression.
-/
theorem lint_nu {s : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hs : MeasSec s) (z z' : Vc k r)
    (μW μW' : Measure (Mt k r)) [SFinite μW] [SFinite μW'] (f : Mt k r → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ m, f m ∂(((wd k r z z').prod (μW.prod μW')).map (Phi s)) =
      ∫⁻ ζ : ℂ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) *
        ∫⁻ p : Mt k r × Mt k r, f (Phi s (ζ, p)) ∂(μW.prod μW') := by
  have hF : Measurable fun x : ℂ × (Mt k r × Mt k r) => f (Phi s x) := hf.comp (Phi_meas hs)
  rw [lintegral_map hf (Phi_meas hs), lintegral_prod _ hF.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ ((zW_meas k _ _).ennreal_ofReal) hF.lintegral_prod_right']
  rfl

/- English proof (translation)
Conclude with `ae_iff.2 h.conc`.
-/
theorem ae_mem {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) :
    ∀ᵐ x : Mt k r ∂μ, (Matrix.of x : Mat k r) ∈ U := by
  exact ae_iff.2 h.conc

/- English proof (translation)
Take `⟨U, hUdef⟩ : ∃ U : Set (Mt k r), U = {m | (Matrix.of m : Mat k r) ∈ UWb k r}` from `⟨_, rfl⟩`. Establish `hUc : IsClosed U`. Rewrite using `[hUdef]`. Conclude with `(CWb k r).closed`. Use `haveI : PolishSpace U := hUc.polishSpace`.

Establish `h2 : ∀ x : Mt k r, x ∈ U → (Matrix.of x : Mat k r) ∈ UWb k r`. Rewrite using `[hUdef]`. Introduce `x hx`. Conclude with `hx`. Establish `hmem : ∀ m : U, (Matrix.of (m : Mt k r) : Mat k r) ∈ UWb k r` using `fun m => h2 m m.2`.

Establish `hπ : Measurable fun m : U => (Matrix.of (m : Mt k r) : Mat k r) *ᵥ z'` using `(mvM_cont.comp (continuous_subtype_val.prodMk continuous_const)).measurable`. Establish `hF' : Measurable fun m : U => F m` using `hF.comp measurable_subtype_coe`. Establish `hfib : ∀ x y : U, (Matrix.of (x : Mt k r) : Mat k r) *ᵥ z' = (Matrix.of (y : Mt k r) : Mat k r) *ᵥ z' → F x = F y`. Introduce and unpack `⟨a, ha0⟩ ⟨b, hb0⟩ hxy`. Establish `hW` using `CWb k r`.

Establish `hx' : (Matrix.of a : Mat k r) ∈ UWb k r` using `hmem ⟨a, ha0⟩`. Establish `hy' : (Matrix.of b : Mat k r) ∈ UWb k r` using `hmem ⟨b, hb0⟩`. Establish `hxy' : (Matrix.of a : Mat k r) *ᵥ z' = (Matrix.of b : Mat k r) *ᵥ z'` using `hxy`. Establish `ha : IsUnit (Matrix.of a : Mat k r).det` using `hW.unit _ hx'`. Establish `hg : (Matrix.of a : Mat k r)⁻¹ * Matrix.of b ∈ UWb k r` using `hW.mul_mem _ (hW.inv_mem _ hx') _ hy'`.

Establish `hgz : ((Matrix.of a : Mat k r)⁻¹ * Matrix.of b) *ᵥ z' = z'`. Rewrite using `[← Matrix.mulVec_mulVec, ← hxy', Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ ha, Matrix.one_mulVec]`. Establish `hgW : (Matrix.of a : Mat k r)⁻¹ * Matrix.of b ∈ UWset k r z'` using `⟨hg.1, hg.2, hgz⟩`. Establish `hab : (Matrix.of a : Mat k r) * ((Matrix.of a : Mat k r)⁻¹ * Matrix.of b) = Matrix.of b`. Rewrite using `[← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha, Matrix.one_mul]`.

Establish `h1` using `hinv (Matrix.of a) _ hgW`. Rewrite `h1` using `[hab]`. Conclude with `h1.symm`. Take `⟨G, hG, hFG⟩` from `factor_meas (fun m : U => (Matrix.of (m : Mt k r) : Mat k r) *ᵥ z') hπ (fun m => F m) hF' hfib`. Use `⟨G, hG, fun m hm => hFG ⟨m, ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[hUdef]`. Conclude with `hm`.
-/
theorem exists_G (CWb : ClosedWb) (z' : Vc k r) (F : Mt k r → ℝ≥0∞) (hF : Measurable F)
    (hinv : ∀ m : Mat k r, ∀ h ∈ UWset k r z', F (m * h : Mat k r) = F m) :
    ∃ G : Vc k r → ℝ≥0∞, Measurable G ∧ ∀ m ∈ UWb k r, F m = G (m *ᵥ z') := by
  obtain ⟨U, hUdef⟩ : ∃ U : Set (Mt k r), U = {m | (Matrix.of m : Mat k r) ∈ UWb k r} := ⟨_, rfl⟩
  have hUc : IsClosed U := by
    rw [hUdef]
    exact (CWb k r).closed
  haveI : PolishSpace U := hUc.polishSpace
  have h2 : ∀ x : Mt k r, x ∈ U → (Matrix.of x : Mat k r) ∈ UWb k r := by
    rw [hUdef]
    intro x hx
    exact hx
  have hmem : ∀ m : U, (Matrix.of (m : Mt k r) : Mat k r) ∈ UWb k r := fun m => h2 m m.2
  have hπ : Measurable fun m : U => (Matrix.of (m : Mt k r) : Mat k r) *ᵥ z' :=
    (mvM_cont.comp (continuous_subtype_val.prodMk continuous_const)).measurable
  have hF' : Measurable fun m : U => F m := hF.comp measurable_subtype_coe
  have hfib : ∀ x y : U, (Matrix.of (x : Mt k r) : Mat k r) *ᵥ z' = (Matrix.of (y : Mt k r) : Mat k r) *ᵥ z' →
      F x = F y := by
    rintro ⟨a, ha0⟩ ⟨b, hb0⟩ hxy
    have hW := CWb k r
    have hx' : (Matrix.of a : Mat k r) ∈ UWb k r := hmem ⟨a, ha0⟩
    have hy' : (Matrix.of b : Mat k r) ∈ UWb k r := hmem ⟨b, hb0⟩
    have hxy' : (Matrix.of a : Mat k r) *ᵥ z' = (Matrix.of b : Mat k r) *ᵥ z' := hxy
    have ha : IsUnit (Matrix.of a : Mat k r).det := hW.unit _ hx'
    have hg : (Matrix.of a : Mat k r)⁻¹ * Matrix.of b ∈ UWb k r := hW.mul_mem _ (hW.inv_mem _ hx') _ hy'
    have hgz : ((Matrix.of a : Mat k r)⁻¹ * Matrix.of b) *ᵥ z' = z' := by
      rw [← Matrix.mulVec_mulVec, ← hxy', Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ ha, Matrix.one_mulVec]
    have hgW : (Matrix.of a : Mat k r)⁻¹ * Matrix.of b ∈ UWset k r z' := ⟨hg.1, hg.2, hgz⟩
    have hab : (Matrix.of a : Mat k r) * ((Matrix.of a : Mat k r)⁻¹ * Matrix.of b) = Matrix.of b := by
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha, Matrix.one_mul]
    have h1 := hinv (Matrix.of a) _ hgW
    rw [hab] at h1
    exact h1.symm
  obtain ⟨G, hG, hFG⟩ := factor_meas (fun m : U => (Matrix.of (m : Mt k r) : Mat k r) *ᵥ z') hπ
    (fun m => F m) hF' hfib
  refine ⟨G, hG, fun m hm => hFG ⟨m, ?_⟩⟩
  rw [hUdef]
  exact hm

end Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1

namespace Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ}

abbrev nu (z z' : Vc k r) (s : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (μW μW' : Measure (Mt k r)) :
    Measure (Mt k r) := ((wd k r z z').prod (μW.prod μW')).map (Phi s)

/- English proof (translation)
Rewrite using `[(UF k r).1]`. Conclude with `⟨s ζ, hsu ζ, rfl⟩`.
-/
theorem emb_mem (UF : UWbFacts) {s : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hsu : ∀ ζ, (s ζ)ᴴ * Hb k * s ζ = Hb k) (ζ : ℂ) : embWb k r (s ζ) ∈ UWb k r := by
  rw [(UF k r).1]
  exact ⟨s ζ, hsu ζ, rfl⟩

/- English proof (translation)
Conclude with `(hf.comp mulM_cont.measurable).lintegral_prod_right'`.
-/
theorem FF_meas (μW' : Measure (Mt k r)) [SFinite μW'] (f : Mt k r → ℝ≥0∞) (hf : Measurable f) :
    Measurable fun m : Mt k r => ∫⁻ h', f (mulM (m, h')) ∂μW' := by
  exact (hf.comp mulM_cont.measurable).lintegral_prod_right'

/- English proof (translation)
Establish `hmeas : Measurable (lmulM h : Mt k r → Mt k r)` using `(lmulM_cont h).measurable`. Establish `hF : Measurable fun h' : Mt k r => f (mulM (m, h'))` using `hf.comp (mulM_cont.measurable.comp (measurable_const.prodMk measurable_id))`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use function extensionality and compare the values at `h'`.

Use `congr 1`. Conclude with `Matrix.mul_assoc m h (Matrix.of h')`. Use `_ = ∫⁻ h', f (mulM (m, h')) ∂(μW'.map (lmulM h)) := (lintegral_map hF hmeas).symm`. Use `_ = ∫⁻ h', f (mulM (m, h')) ∂μW' := by rw [hW'.left h hh]`.
-/
theorem FF_inv {z' : Vc k r} {μW' : Measure (Mt k r)} (hW' : IsHaarOn (UWset k r z') μW')
    (f : Mt k r → ℝ≥0∞) (hf : Measurable f) (m : Mat k r) (h : Mat k r) (hh : h ∈ UWset k r z') :
    ∫⁻ h', f (mulM ((m * h : Mat k r), h')) ∂μW' = ∫⁻ h', f (mulM (m, h')) ∂μW' := by
  have hmeas : Measurable (lmulM h : Mt k r → Mt k r) := (lmulM_cont h).measurable
  have hF : Measurable fun h' : Mt k r => f (mulM (m, h')) :=
    hf.comp (mulM_cont.measurable.comp (measurable_const.prodMk measurable_id))
  calc ∫⁻ h', f (mulM ((m * h : Mat k r), h')) ∂μW' = ∫⁻ h', f (mulM (m, lmulM h h')) ∂μW' := by
        congr 1
        funext h'
        congr 1
        exact Matrix.mul_assoc m h (Matrix.of h')
    _ = ∫⁻ h', f (mulM (m, h')) ∂(μW'.map (lmulM h)) := (lintegral_map hF hmeas).symm
    _ = ∫⁻ h', f (mulM (m, h')) ∂μW' := by rw [hW'.left h hh]

/- English proof (translation)
Establish `h1 : Measurable fun p : ℂ × Mt k r => embF k r (s p.1)` using `(embS_meas (r := r) hs).comp measurable_fst`. Establish `h2 : Measurable fun p : ℂ × Mt k r => mvM (embF k r (s p.1), z')` using `mvM_cont.measurable.comp (h1.prodMk measurable_const)`. Conclude with `mvM_cont.measurable.comp ((invM_meas.comp measurable_snd).prodMk h2)`.
-/
theorem measurable_inv_mulVec_embWb_of_measSec {s : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hs : MeasSec s) (z' : Vc k r) :
    Measurable fun p : ℂ × Mt k r => (Matrix.of p.2 : Mat k r)⁻¹ *ᵥ (embWb k r (s p.1) *ᵥ z') := by
  have h1 : Measurable fun p : ℂ × Mt k r => embF k r (s p.1) := (embS_meas (r := r) hs).comp measurable_fst
  have h2 : Measurable fun p : ℂ × Mt k r => mvM (embF k r (s p.1), z') :=
    mvM_cont.measurable.comp (h1.prodMk measurable_const)
  exact mvM_cont.measurable.comp ((invM_meas.comp measurable_snd).prodMk h2)

/- English proof (translation)
Establish `hWb` using `CWb k r`. Establish `hPhi` using `Phi_meas (r := r) hs`. Establish `hL : Measurable (lmulM b : Mt k r → Mt k r)` using `(lmulM_cont b).measurable`. Establish `hψ` using `measurable_inv_mulVec_embWb_of_measSec (r := r) hs z'`. Establish `hbv : Measurable fun v : Vc k r => b *ᵥ v` using `(mvM_cont.comp (continuous_const.prodMk continuous_id)).measurable`.

Establish `hfL : Measurable fun m : Mt k r => f (lmulM b m)` using `hf.comp hL`. Establish `hGb : Measurable fun v : Vc k r => G (b *ᵥ v)` using `hG.comp hbv`. Establish `hF : Measurable fun x : ℂ × (Mt k r × Mt k r) => f (lmulM b (Phi s x))` using `hfL.comp hPhi`. Establish `hGψ : Measurable fun p : ℂ × Mt k r => G (b *ᵥ ((Matrix.of p.2 : Mat k r)⁻¹ *ᵥ (embWb k r (s p.1) *ᵥ z')))` using `hGb.comp hψ`. Unfold `nu hypMeas`.

Rewrite using `[lintegral_map hfL hPhi, lintegral_map hGb hψ, lintegral_prod _ hF.aemeasurable, lintegral_prod _ hGψ.aemeasurable]`. Use `lintegral_congr fun ζ => ?_` and prove the remaining obligations. Establish `hFζ : Measurable fun p : Mt k r × Mt k r => f (lmulM b (Phi s (ζ, p)))` using `hF.comp (measurable_const.prodMk measurable_id)`. Rewrite using `[lintegral_prod _ hFζ.aemeasurable]`. Use `lintegral_congr_ae ?_` and prove the remaining obligations.

Use `filter_upwards [ae_mem hW] with h hh`. Establish `hu : (Matrix.of h : Mat k r) ∈ UWb k r` using `(UF k r).2.1 z hh`. Establish `hm : (Matrix.of h : Mat k r)⁻¹ * embWb k r (s ζ) ∈ UWb k r` using `hWb.mul_mem _ (hWb.inv_mem _ hu) _ (emb_mem UF hsu ζ)`. Establish `hbm : b * ((Matrix.of h : Mat k r)⁻¹ * embWb k r (s ζ)) ∈ UWb k r` using `hWb.mul_mem _ hb _ hm`. Establish `e1 : ∀ h' : Mt k r, f (lmulM b (Phi s (ζ, (h, h')))) = f (mulM (b * ((Matrix.of h : Mat k r)⁻¹ * embWb k r (s ζ)), h'))` using `fun h' => by`.

Use `congr 1`. Use `show b * ((Matrix.of h : Mat k r)⁻¹ * embWb k r (s ζ) * Matrix.of h') = b * ((Matrix.of h : Mat k r)⁻¹ * embWb k r (s ζ)) * Matrix.of h'`. Simplify using `only [Matrix.mul_assoc]`. Simplify using `only [e1]`. Rewrite using `[hFG _ hbm]`.

Use `congr 1`. Simplify using `only [Matrix.mulVec_mulVec, Matrix.mul_assoc]`.
-/
theorem nu_hyp (CWb : ClosedWb) (CW : ClosedW) (UF : UWbFacts) (z z' : Vc k r)
    {s : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hs : MeasSec s) (hsu : ∀ ζ, (s ζ)ᴴ * Hb k * s ζ = Hb k)
    {μW μW' : Measure (Mt k r)} (hW : IsHaarOn (UWset k r z) μW) [SFinite μW] [SFinite μW']
    (f : Mt k r → ℝ≥0∞) (hf : Measurable f) (G : Vc k r → ℝ≥0∞) (hG : Measurable G)
    (hFG : ∀ m ∈ UWb k r, (∫⁻ h', f (mulM (m, h')) ∂μW') = G (m *ᵥ z')) (b : Mat k r) (hb : b ∈ UWb k r) :
    ∫⁻ m, f (lmulM b m) ∂(nu z z' s μW μW') = ∫⁻ v, G (b *ᵥ v) ∂(hypMeas k r z z' s μW) := by
  have hWb := CWb k r
  have hPhi := Phi_meas (r := r) hs
  have hL : Measurable (lmulM b : Mt k r → Mt k r) := (lmulM_cont b).measurable
  have hψ := measurable_inv_mulVec_embWb_of_measSec (r := r) hs z'
  have hbv : Measurable fun v : Vc k r => b *ᵥ v :=
    (mvM_cont.comp (continuous_const.prodMk continuous_id)).measurable
  have hfL : Measurable fun m : Mt k r => f (lmulM b m) := hf.comp hL
  have hGb : Measurable fun v : Vc k r => G (b *ᵥ v) := hG.comp hbv
  have hF : Measurable fun x : ℂ × (Mt k r × Mt k r) => f (lmulM b (Phi s x)) := hfL.comp hPhi
  have hGψ : Measurable fun p : ℂ × Mt k r =>
      G (b *ᵥ ((Matrix.of p.2 : Mat k r)⁻¹ *ᵥ (embWb k r (s p.1) *ᵥ z'))) := hGb.comp hψ
  unfold nu hypMeas
  rw [lintegral_map hfL hPhi, lintegral_map hGb hψ, lintegral_prod _ hF.aemeasurable,
    lintegral_prod _ hGψ.aemeasurable]
  refine lintegral_congr fun ζ => ?_
  have hFζ : Measurable fun p : Mt k r × Mt k r => f (lmulM b (Phi s (ζ, p))) :=
    hF.comp (measurable_const.prodMk measurable_id)
  rw [lintegral_prod _ hFζ.aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_mem hW] with h hh
  have hu : (Matrix.of h : Mat k r) ∈ UWb k r := (UF k r).2.1 z hh
  have hm : (Matrix.of h : Mat k r)⁻¹ * embWb k r (s ζ) ∈ UWb k r :=
    hWb.mul_mem _ (hWb.inv_mem _ hu) _ (emb_mem UF hsu ζ)
  have hbm : b * ((Matrix.of h : Mat k r)⁻¹ * embWb k r (s ζ)) ∈ UWb k r := hWb.mul_mem _ hb _ hm
  have e1 : ∀ h' : Mt k r, f (lmulM b (Phi s (ζ, (h, h')))) =
      f (mulM (b * ((Matrix.of h : Mat k r)⁻¹ * embWb k r (s ζ)), h')) := fun h' => by
    congr 1
    show b * ((Matrix.of h : Mat k r)⁻¹ * embWb k r (s ζ) * Matrix.of h') =
      b * ((Matrix.of h : Mat k r)⁻¹ * embWb k r (s ζ)) * Matrix.of h'
    simp only [Matrix.mul_assoc]
  simp only [e1]
  rw [hFG _ hbm]
  congr 1
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

/- English proof (translation)
Use `haveI := haar_sigmaFinite hW`. Use `haveI := haar_sigmaFinite hW'`. Establish `hWb` using `CWb k r`. Apply `Measure.ext_of_lintegral` to reduce the goal to its premises. Introduce `f hf`.

Establish `hL : Measurable (lmulM a : Mt k r → Mt k r)` using `(lmulM_cont a).measurable`. Rewrite using `[lintegral_map hf hL]`. Take `⟨G, hG, hFG⟩` from `exists_G CWb z' (fun m => ∫⁻ h', f (mulM (m, h')) ∂μW') (FF_meas μW' f hf) (fun m h hh => FF_inv hW' f hf m h hh)`. Establish `hFG' : ∀ m ∈ UWb k r, (∫⁻ h', f (mulM (m, h')) ∂μW') = G (m *ᵥ z')` using `hFG`. Establish `h1` using `nu_hyp CWb CW UF z z' hs hsu hW f hf G hG hFG' a ha`.

Establish `h2` using `nu_hyp CWb CW UF z z' hs hsu hW f hf G hG hFG' 1 hWb.one_mem`. Establish `hHI` using `HI k r z z' s μW hk hz hz' hT hT' hsec hW a ha`. Establish `hav : Measurable fun v : Vc k r => a *ᵥ v` using `(mvM_cont.comp (continuous_const.prodMk continuous_id)).measurable`. Rewrite using `[h1]`. Combine the equalities or inequalities in the displayed calculation.

Use `congr 1`. Use function extensionality and compare the values at `m`. Use `congr 1`. Use `show (1 : Mat k r) * Matrix.of m = m`. Conclude with `Matrix.one_mul _`.
-/
theorem nu_left (CWb : ClosedWb) (CW : ClosedW) (UF : UWbFacts) (HI : HypInv) (z z' : Vc k r)
    {s : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hs : MeasSec s) (hsu : ∀ ζ, (s ζ)ᴴ * Hb k * s ζ = Hb k)
    (hk : 1 ≤ k) (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (hsec : IsSection k r z z' s)
    {μW μW' : Measure (Mt k r)} (hW : IsHaarOn (UWset k r z) μW) (hW' : IsHaarOn (UWset k r z') μW')
    (a : Mat k r) (ha : a ∈ UWb k r) : (nu z z' s μW μW').map (lmulM a) = nu z z' s μW μW' := by
  haveI := haar_sigmaFinite hW
  haveI := haar_sigmaFinite hW'
  have hWb := CWb k r
  apply Measure.ext_of_lintegral
  intro f hf
  have hL : Measurable (lmulM a : Mt k r → Mt k r) := (lmulM_cont a).measurable
  rw [lintegral_map hf hL]
  obtain ⟨G, hG, hFG⟩ := exists_G CWb z' (fun m => ∫⁻ h', f (mulM (m, h')) ∂μW') (FF_meas μW' f hf)
    (fun m h hh => FF_inv hW' f hf m h hh)
  have hFG' : ∀ m ∈ UWb k r, (∫⁻ h', f (mulM (m, h')) ∂μW') = G (m *ᵥ z') := hFG
  have h1 := nu_hyp CWb CW UF z z' hs hsu hW f hf G hG hFG' a ha
  have h2 := nu_hyp CWb CW UF z z' hs hsu hW f hf G hG hFG' 1 hWb.one_mem
  have hHI := HI k r z z' s μW hk hz hz' hT hT' hsec hW a ha
  have hav : Measurable fun v : Vc k r => a *ᵥ v :=
    (mvM_cont.comp (continuous_const.prodMk continuous_id)).measurable
  rw [h1]
  calc ∫⁻ v, G (a *ᵥ v) ∂(hypMeas k r z z' s μW)
      = ∫⁻ v, G v ∂((hypMeas k r z z' s μW).map fun v => a *ᵥ v) := (lintegral_map hG hav).symm
    _ = ∫⁻ v, G v ∂(hypMeas k r z z' s μW) := by rw [hHI]
    _ = ∫⁻ v, G ((1 : Mat k r) *ᵥ v) ∂(hypMeas k r z z' s μW) := by simp only [Matrix.one_mulVec]
    _ = ∫⁻ m, f (lmulM 1 m) ∂(nu z z' s μW μW') := h2.symm
    _ = ∫⁻ m, f m ∂(nu z z' s μW μW') := by
      congr 1
      funext m
      congr 1
      show (1 : Mat k r) * Matrix.of m = m
      exact Matrix.one_mul _

/- English proof (translation)
Establish `hA : ∀ᵐ p ∂(μW.prod μW'), (Matrix.of p.1 : Mat k r) ∈ UWset k r z` using `Measure.quasiMeasurePreserving_fst.ae (ae_mem hW)`. Establish `hB : ∀ᵐ p ∂(μW.prod μW'), (Matrix.of p.2 : Mat k r) ∈ UWset k r z'` using `Measure.quasiMeasurePreserving_snd.ae (ae_mem hW')`. Conclude with `Measure.quasiMeasurePreserving_snd.ae (hA.and hB)`.
-/
theorem ae_both (z z' : Vc k r) {μW μW' : Measure (Mt k r)} (hW : IsHaarOn (UWset k r z) μW)
    (hW' : IsHaarOn (UWset k r z') μW') [SFinite μW] [SFinite μW'] :
    ∀ᵐ x : ℂ × (Mt k r × Mt k r) ∂((wd k r z z').prod (μW.prod μW')),
      (Matrix.of x.2.1 : Mat k r) ∈ UWset k r z ∧ (Matrix.of x.2.2 : Mat k r) ∈ UWset k r z' := by
  have hA : ∀ᵐ p ∂(μW.prod μW'), (Matrix.of p.1 : Mat k r) ∈ UWset k r z :=
    Measure.quasiMeasurePreserving_fst.ae (ae_mem hW)
  have hB : ∀ᵐ p ∂(μW.prod μW'), (Matrix.of p.2 : Mat k r) ∈ UWset k r z' :=
    Measure.quasiMeasurePreserving_snd.ae (ae_mem hW')
  exact Measure.quasiMeasurePreserving_snd.ae (hA.and hB)

/- English proof (translation)
Use `haveI := haar_sigmaFinite hW`. Use `haveI := haar_sigmaFinite hW'`. Establish `hWb` using `CWb k r`. Establish `hc' : IsClosed {m : Mt k r | (Matrix.of m : Mat k r) ∈ UWb k r}` using `hWb.closed`. Establish `hcl : MeasurableSet ({m : Mt k r | (Matrix.of m : Mat k r) ∈ UWb k r}ᶜ)` using `hc'.measurableSet.compl`.

Use `show (Measure.map (Phi s) ((wd k r z z').prod (μW.prod μW'))) ({m : Mt k r | (Matrix.of m : Mat k r) ∈ UWb k r}ᶜ) = 0`. Rewrite using `[Measure.map_apply (Phi_meas hs) hcl]`. Apply `measure_mono_null _ (ae_iff.1 (ae_both z z' hW hW'))` to reduce the goal to its premises. Introduce `x hx`. Establish `hx' : (Matrix.of (Phi s x) : Mat k r) ∉ UWb k r` using `hx`.

Use `show ¬ ((Matrix.of x.2.1 : Mat k r) ∈ UWset k r z ∧ (Matrix.of x.2.2 : Mat k r) ∈ UWset k r z')`. Introduce and unpack `⟨h1, h2⟩`. Apply `hx'` to reduce the goal to its premises. Establish `hu1 : (Matrix.of x.2.1 : Mat k r) ∈ UWb k r` using `(UF k r).2.1 z h1`. Establish `hu2 : (Matrix.of x.2.2 : Mat k r) ∈ UWb k r` using `(UF k r).2.1 z' h2`.

Conclude with `hWb.mul_mem _ (hWb.mul_mem _ (hWb.inv_mem _ hu1) _ (emb_mem UF hsu x.1)) _ hu2`.
-/
theorem nu_conc (CWb : ClosedWb) (CW : ClosedW) (UF : UWbFacts) (z z' : Vc k r)
    {s : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hs : MeasSec s) (hsu : ∀ ζ, (s ζ)ᴴ * Hb k * s ζ = Hb k)
    {μW μW' : Measure (Mt k r)} (hW : IsHaarOn (UWset k r z) μW) (hW' : IsHaarOn (UWset k r z') μW') :
    (nu z z' s μW μW') (UWb k r)ᶜ = 0 := by
  haveI := haar_sigmaFinite hW
  haveI := haar_sigmaFinite hW'
  have hWb := CWb k r
  have hc' : IsClosed {m : Mt k r | (Matrix.of m : Mat k r) ∈ UWb k r} := hWb.closed
  have hcl : MeasurableSet ({m : Mt k r | (Matrix.of m : Mat k r) ∈ UWb k r}ᶜ) := hc'.measurableSet.compl
  show (Measure.map (Phi s) ((wd k r z z').prod (μW.prod μW'))) ({m : Mt k r | (Matrix.of m : Mat k r) ∈ UWb k r}ᶜ) = 0
  rw [Measure.map_apply (Phi_meas hs) hcl]
  apply measure_mono_null _ (ae_iff.1 (ae_both z z' hW hW'))
  intro x hx
  have hx' : (Matrix.of (Phi s x) : Mat k r) ∉ UWb k r := hx
  show ¬ ((Matrix.of x.2.1 : Mat k r) ∈ UWset k r z ∧ (Matrix.of x.2.2 : Mat k r) ∈ UWset k r z')
  rintro ⟨h1, h2⟩
  apply hx'
  have hu1 : (Matrix.of x.2.1 : Mat k r) ∈ UWb k r := (UF k r).2.1 z h1
  have hu2 : (Matrix.of x.2.2 : Mat k r) ∈ UWb k r := (UF k r).2.1 z' h2
  exact hWb.mul_mem _ (hWb.mul_mem _ (hWb.inv_mem _ hu1) _ (emb_mem UF hsu x.1)) _ hu2

/- English proof (translation)
Establish `hK : IsCompact (UWset k r z)` using `KW k r z hz hT`. Prove the components needed by the constructor for the conclusion. Establish `h1` using `hW.finite_compact _ hK`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem haar_finite (KW : CompactW) {z : Vc k r} (hz : inWb k r z) (hT : 0 < Tz k r z) {μW : Measure (Mt k r)}
    (hW : IsHaarOn (UWset k r z) μW) : IsFiniteMeasure μW := by
  have hK : IsCompact (UWset k r z) := KW k r z hz hT
  constructor
  have h1 := hW.finite_compact _ hK
  calc μW Set.univ ≤ μW (UWset k r z) + μW (UWset k r z)ᶜ := measure_univ_le_add_compl _
    _ < ∞ := by rw [hW.conc, add_zero]; exact h1

/- English proof (translation)
Use `show (volume.withDensity fun ζ => ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ)) (Metric.closedBall 0 ρ) < ∞`. Rewrite using `[withDensity_apply _ measurableSet_closedBall]`. Combine the equalities or inequalities in the displayed calculation. Use `setLIntegral_mono' measurableSet_closedBall fun ζ hζ => ?_` and prove the remaining obligations. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises.

Establish `hn : ‖ζ‖ ≤ ρ` using `by simpa using hζ`. Establish `hq : Complex.normSq ζ ≤ ρ ^ 2`. Rewrite using `[Complex.normSq_eq_norm_sq]`. Use polynomial arithmetic with `[norm_nonneg ζ]`. Unfold `zWeight`.

Use `split_ifs with h`. Use `first`. Consider the case `exact pow_le_pow_left (by linarith) (by linarith) _`. Consider the case `exact pow_le_pow_left₀ (by linarith) (by linarith) _`. Check the signs of the components of the expression.

Use `_ = ENNReal.ofReal ((ρ ^ 2) ^ (k - 1)) * volume (Metric.closedBall (0:ℂ) ρ) := setLIntegral_const _ _`. Use `_ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top`.
-/
theorem wd_ball (z z' : Vc k r) (hTT : 0 ≤ Tz k r z * Tz k r z') (ρ : ℝ) :
    wd k r z z' (Metric.closedBall 0 ρ) < ∞ := by
  show (volume.withDensity fun ζ => ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ))
    (Metric.closedBall 0 ρ) < ∞
  rw [withDensity_apply _ measurableSet_closedBall]
  calc ∫⁻ ζ in Metric.closedBall (0:ℂ) ρ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ)
      ≤ ∫⁻ ζ in Metric.closedBall (0:ℂ) ρ, ENNReal.ofReal ((ρ ^ 2) ^ (k - 1)) := by
        refine setLIntegral_mono' measurableSet_closedBall fun ζ hζ => ?_
        apply ENNReal.ofReal_le_ofReal
        have hn : ‖ζ‖ ≤ ρ := by simpa using hζ
        have hq : Complex.normSq ζ ≤ ρ ^ 2 := by
          rw [Complex.normSq_eq_norm_sq]
          nlinarith [norm_nonneg ζ]
        unfold zWeight
        split_ifs with h
        · first
            | exact pow_le_pow_left (by linarith) (by linarith) _
            | exact pow_le_pow_left₀ (by linarith) (by linarith) _
        · positivity
    _ = ENNReal.ofReal ((ρ ^ 2) ^ (k - 1)) * volume (Metric.closedBall (0:ℂ) ρ) := setLIntegral_const _ _
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top

/- English proof (translation)
Use `haveI := haar_sigmaFinite hW`. Use `haveI := haar_sigmaFinite hW'`. Use `haveI := haar_finite KW hz hT hW`. Use `haveI := haar_finite KW hz' hT' hW'`. Establish `hcont : Continuous fun m : Mt k r => herm (Hpk k r) ((Matrix.of m : Mat k r) *ᵥ z') z`.

Unfold `herm`. Use `fun_prop`. Take `⟨R, hR⟩` from `(hK.image hcont).isBounded.subset_closedBall (0 : ℂ)`. Establish `hOm : MeasurableSet (Om k r z z')` using `(Om_open z z').measurableSet`. Take `⟨B, hBdef⟩ : ∃ B : Set ℂ, B = Metric.closedBall 0 R ∪ (Om k r z z')ᶜ` from `⟨_, rfl⟩`.

Establish `hnull` using `ae_iff.1 (ae_both z z' hW hW')`. Unfold `nu`. Rewrite using `[Measure.map_apply (Phi_meas hs) hK.isClosed.measurableSet]`. Establish `hsub : Phi s ⁻¹' K ⊆ (B ×ˢ Set.univ) ∪ {x : ℂ × (Mt k r × Mt k r) | ¬((Matrix.of x.2.1 : Mat k r) ∈ UWset k r z ∧ (Matrix.of x.2.2 : Mat k r) ∈ UWset k r z')}`. Introduce `x hx`.

Distinguish the cases in `hg : (Matrix.of x.2.1 : Mat k r) ∈ UWset k r z ∧ (Matrix.of x.2.2 : Mat k r) ∈ UWset k r z'`. Use `left`. Use `⟨?_, Set.mem_univ _⟩` and prove the remaining obligations. Rewrite using `[hBdef]`. Distinguish the cases in `hζ : x.1 ∈ Om k r z z'`.

Use `left`. Establish `hrm` using `(RM k r z z' s hz hz' hsec x.1 hζ _ hg.1 _ hg.2).2`. Conclude with `hR ⟨Phi s x, hx, hrm⟩`. Use `right`. Conclude with `hζ`.

Use `right`. Conclude with `hg`. Establish `h1 : wd k r z z' (Om k r z z')ᶜ = 0` using `by show (volume.withDensity fun ζ => ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ)) (Om k r z z')ᶜ = 0`. Rewrite using `[withDensity_apply _ hOm.compl]`. Establish `hae : ∀ᵐ ζ ∂(volume.restrict (Om k r z z')ᶜ), ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) = 0`.

Rewrite using `[ae_restrict_iff' hOm.compl]`. Use `filter_upwards [ae_Om (r := r) z z'] with ζ hζ hc`. Break down `hζ with hζ | hζ` into its components or cases. Conclude with `absurd hζ hc`. Rewrite using `[hζ, ENNReal.ofReal_zero]`.

Rewrite using `[lintegral_congr_ae hae, lintegral_zero]`. Establish `hwdB : wd k r z z' B < ∞`. Rewrite using `[hBdef]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h1, add_zero]`.

Conclude with `wd_ball z z' (mul_nonneg hT.le hT'.le) R`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Measure.prod_prod, hnull, add_zero]`. Conclude with `ENNReal.mul_lt_top hwdB (measure_lt_top _ _)`.
-/
theorem nu_finite (KW : CompactW) (RM : RankOneMem) (z z' : Vc k r)
    {s : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hs : MeasSec s)
    (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (hsec : IsSection k r z z' s)
    {μW μW' : Measure (Mt k r)} (hW : IsHaarOn (UWset k r z) μW) (hW' : IsHaarOn (UWset k r z') μW')
    (K : Set (Mt k r)) (hK : IsCompact K) : (nu z z' s μW μW') K < ∞ := by
  haveI := haar_sigmaFinite hW
  haveI := haar_sigmaFinite hW'
  haveI := haar_finite KW hz hT hW
  haveI := haar_finite KW hz' hT' hW'
  have hcont : Continuous fun m : Mt k r => herm (Hpk k r) ((Matrix.of m : Mat k r) *ᵥ z') z := by
    unfold herm
    fun_prop
  obtain ⟨R, hR⟩ := (hK.image hcont).isBounded.subset_closedBall (0 : ℂ)
  have hOm : MeasurableSet (Om k r z z') := (Om_open z z').measurableSet
  obtain ⟨B, hBdef⟩ : ∃ B : Set ℂ, B = Metric.closedBall 0 R ∪ (Om k r z z')ᶜ := ⟨_, rfl⟩
  have hnull := ae_iff.1 (ae_both z z' hW hW')
  unfold nu
  rw [Measure.map_apply (Phi_meas hs) hK.isClosed.measurableSet]
  have hsub : Phi s ⁻¹' K ⊆ (B ×ˢ Set.univ) ∪
      {x : ℂ × (Mt k r × Mt k r) | ¬((Matrix.of x.2.1 : Mat k r) ∈ UWset k r z ∧
        (Matrix.of x.2.2 : Mat k r) ∈ UWset k r z')} := by
    intro x hx
    by_cases hg : (Matrix.of x.2.1 : Mat k r) ∈ UWset k r z ∧ (Matrix.of x.2.2 : Mat k r) ∈ UWset k r z'
    · left
      refine ⟨?_, Set.mem_univ _⟩
      rw [hBdef]
      by_cases hζ : x.1 ∈ Om k r z z'
      · left
        have hrm := (RM k r z z' s hz hz' hsec x.1 hζ _ hg.1 _ hg.2).2
        exact hR ⟨Phi s x, hx, hrm⟩
      · right
        exact hζ
    · right
      exact hg
  have h1 : wd k r z z' (Om k r z z')ᶜ = 0 := by
    show (volume.withDensity fun ζ => ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ)) (Om k r z z')ᶜ = 0
    rw [withDensity_apply _ hOm.compl]
    have hae : ∀ᵐ ζ ∂(volume.restrict (Om k r z z')ᶜ),
        ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) = 0 := by
      rw [ae_restrict_iff' hOm.compl]
      filter_upwards [ae_Om (r := r) z z'] with ζ hζ hc
      rcases hζ with hζ | hζ
      · exact absurd hζ hc
      · rw [hζ, ENNReal.ofReal_zero]
    rw [lintegral_congr_ae hae, lintegral_zero]
  have hwdB : wd k r z z' B < ∞ := by
    rw [hBdef]
    calc wd k r z z' (Metric.closedBall 0 R ∪ (Om k r z z')ᶜ)
        ≤ wd k r z z' (Metric.closedBall 0 R) + wd k r z z' (Om k r z z')ᶜ := measure_union_le _ _
      _ < ∞ := by
        rw [h1, add_zero]
        exact wd_ball z z' (mul_nonneg hT.le hT'.le) R
  calc ((wd k r z z').prod (μW.prod μW')) (Phi s ⁻¹' K)
      ≤ ((wd k r z z').prod (μW.prod μW')) ((B ×ˢ Set.univ) ∪
        {x : ℂ × (Mt k r × Mt k r) | ¬((Matrix.of x.2.1 : Mat k r) ∈ UWset k r z ∧
          (Matrix.of x.2.2 : Mat k r) ∈ UWset k r z')}) := measure_mono hsub
    _ ≤ ((wd k r z z').prod (μW.prod μW')) (B ×ˢ Set.univ) +
        ((wd k r z z').prod (μW.prod μW')) {x : ℂ × (Mt k r × Mt k r) | ¬((Matrix.of x.2.1 : Mat k r) ∈ UWset k r z ∧
          (Matrix.of x.2.2 : Mat k r) ∈ UWset k r z')} := measure_union_le _ _
    _ < ∞ := by
      rw [Measure.prod_prod, hnull, add_zero]
      exact ENNReal.mul_lt_top hwdB (measure_lt_top _ _)

/- English proof (translation)
Introduce `h0`. Establish `hmeas : Measurable fun ζ : ℂ => ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ)` using `(zW_meas k _ _).ennreal_ofReal`. Establish `h1 : (volume : Measure ℂ).withDensity (fun ζ => ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ)) = 0` using `h0`. Rewrite `h1` using `[withDensity_eq_zero_iff hmeas.aemeasurable]`. Establish `hc0 : (0 : ℝ) ≤ |Tz k r z * Tz k r z'| + 1` using `by positivity`.

Establish `hS : IsOpen {ζ : ℂ | |Tz k r z * Tz k r z'| + 1 < Complex.normSq ζ}` using `isOpen_lt continuous_const Complex.continuous_normSq`. Establish `hne : ({ζ : ℂ | |Tz k r z * Tz k r z'| + 1 < Complex.normSq ζ}).Nonempty`. Use `⟨((|Tz k r z * Tz k r z'| + 2 : ℝ) : ℂ), ?_⟩` and prove the remaining obligations. Use `show |Tz k r z * Tz k r z'| + 1 < Complex.normSq ((|Tz k r z * Tz k r z'| + 2 : ℝ) : ℂ)`. Rewrite using `[Complex.normSq_ofReal]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hpos` using `hS.measure_pos (volume : Measure ℂ) hne`. Apply `hpos.ne'` to reduce the goal to its premises. Apply `measure_mono_null _ (ae_iff.1 h1)` to reduce the goal to its premises. Introduce `ζ hζ`.

Establish `hζ' : |Tz k r z * Tz k r z'| + 1 < Complex.normSq ζ` using `hζ`. Establish `hlt : Tz k r z * Tz k r z' < Complex.normSq ζ` using `lt_of_le_of_lt (le_trans (le_abs_self _) (by linarith)) hζ'`. Establish `hp : 0 < (Complex.normSq ζ - Tz k r z * Tz k r z') ^ (k - 1)` using `pow_pos (by linarith) _`. Use `show ¬ (ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) = 0)`. Unfold `zWeight`.

Rewrite using `[if_pos hlt.le]`. Conclude with `(ENNReal.ofReal_pos.2 hp).ne'`.
-/
theorem wd_ne_zero (z z' : Vc k r) : wd k r z z' ≠ 0 := by
  intro h0
  have hmeas : Measurable fun ζ : ℂ => ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) :=
    (zW_meas k _ _).ennreal_ofReal
  have h1 : (volume : Measure ℂ).withDensity (fun ζ => ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ)) = 0 := h0
  rw [withDensity_eq_zero_iff hmeas.aemeasurable] at h1
  have hc0 : (0 : ℝ) ≤ |Tz k r z * Tz k r z'| + 1 := by positivity
  have hS : IsOpen {ζ : ℂ | |Tz k r z * Tz k r z'| + 1 < Complex.normSq ζ} :=
    isOpen_lt continuous_const Complex.continuous_normSq
  have hne : ({ζ : ℂ | |Tz k r z * Tz k r z'| + 1 < Complex.normSq ζ}).Nonempty := by
    refine ⟨((|Tz k r z * Tz k r z'| + 2 : ℝ) : ℂ), ?_⟩
    show |Tz k r z * Tz k r z'| + 1 < Complex.normSq ((|Tz k r z * Tz k r z'| + 2 : ℝ) : ℂ)
    rw [Complex.normSq_ofReal]
    nlinarith
  have hpos := hS.measure_pos (volume : Measure ℂ) hne
  apply hpos.ne'
  apply measure_mono_null _ (ae_iff.1 h1)
  intro ζ hζ
  have hζ' : |Tz k r z * Tz k r z'| + 1 < Complex.normSq ζ := hζ
  have hlt : Tz k r z * Tz k r z' < Complex.normSq ζ :=
    lt_of_le_of_lt (le_trans (le_abs_self _) (by linarith)) hζ'
  have hp : 0 < (Complex.normSq ζ - Tz k r z * Tz k r z') ^ (k - 1) := pow_pos (by linarith) _
  show ¬ (ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) = 0)
  unfold zWeight
  rw [if_pos hlt.le]
  exact (ENNReal.ofReal_pos.2 hp).ne'

/- English proof (translation)
Use `haveI := haar_sigmaFinite hW`. Use `haveI := haar_sigmaFinite hW'`. Unfold `nu`. Introduce `h0`. Rewrite `h0` using `[Measure.map_eq_zero_iff (Phi_meas hs).aemeasurable]`.

Establish `h1 : ((wd k r z z').prod (μW.prod μW')) Set.univ = 0` using `by simp [h0]`. Rewrite `h1` using `[← Set.univ_prod_univ, Measure.prod_prod, ← Set.univ_prod_univ, Measure.prod_prod]`. Break down `mul_eq_zero.1 h1 with h | h` into its components or cases. Conclude with `wd_ne_zero z z' (Measure.measure_univ_eq_zero.1 h)`. Break down `mul_eq_zero.1 h with h | h` into its components or cases.

Conclude with `hW.ne_zero (Measure.measure_univ_eq_zero.1 h)`. Conclude with `hW'.ne_zero (Measure.measure_univ_eq_zero.1 h)`.
-/
theorem nu_ne_zero (z z' : Vc k r) {s : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hs : MeasSec s)
    {μW μW' : Measure (Mt k r)} (hW : IsHaarOn (UWset k r z) μW) (hW' : IsHaarOn (UWset k r z') μW') :
    nu z z' s μW μW' ≠ 0 := by
  haveI := haar_sigmaFinite hW
  haveI := haar_sigmaFinite hW'
  unfold nu
  intro h0
  rw [Measure.map_eq_zero_iff (Phi_meas hs).aemeasurable] at h0
  have h1 : ((wd k r z z').prod (μW.prod μW')) Set.univ = 0 := by simp [h0]
  rw [← Set.univ_prod_univ, Measure.prod_prod, ← Set.univ_prod_univ, Measure.prod_prod] at h1
  rcases mul_eq_zero.1 h1 with h | h
  · exact wd_ne_zero z z' (Measure.measure_univ_eq_zero.1 h)
  · rcases mul_eq_zero.1 h with h | h
    · exact hW.ne_zero (Measure.measure_univ_eq_zero.1 h)
    · exact hW'.ne_zero (Measure.measure_univ_eq_zero.1 h)

end Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1

/- English proof (translation)
Introduce `HU CWb CW KW UF RM RC HI k r z z' μsec μb μW μW' hk hz hz' hT hT' hsec hb hW hW'`. Use `haveI := haar_sigmaFinite hW`. Use `haveI := haar_sigmaFinite hW'`. Establish `hsm : MeasSec (secF k r z z' μsec)` using `secF_meas hsec`. Establish `hss : IsSection k r z z' (secF k r z z' μsec)` using `secF_section hsec`.

Establish `hsu : ∀ ζ, (secF k r z z' μsec ζ)ᴴ * Hb k * secF k r z z' μsec ζ = Hb k` using `secF_unit hsec`. Take `⟨c, hc⟩` from `HU k r (UWb k r) μb (nu z z' (secF k r z z' μsec) μW μW') (CWb k r) hb (nu_conc CWb CW UF z z' hsm hsu hW hW') (fun a ha => nu_left CWb CW UF HI z z' hsm hsu hk hz hz' hT hT' hss hW hW' a ha) (fun K hK => nu_finite KW RM z z' hsm hz hz' hT hT' hss hW hW' K hK)`. Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`. Conclude with `nu_ne_zero z z' hsm hW hW' (by rw [hc]; simp)`.

Use `⟨c⁻¹, inv_pos.2 (pos_iff_ne_zero.2 hc0), fun f hf => ?_⟩` and prove the remaining obligations. Establish `hint` using `lint_nu hsm z z' μW μW' f hf`. Establish `e1 : ∫⁻ m, f m ∂(nu z z' (secF k r z z' μsec) μW μW') = (c : ℝ≥0∞) * ∫⁻ m, f m ∂μb`. Rewrite using `[hc, lintegral_smul_measure]`. Use `first`.

Consider the case `rfl`. Consider the case `simp [ENNReal.smul_def]`. Consider the case `simp`. Establish `e2 : ∫⁻ ζ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) * ∫⁻ p, f (Phi (secF k r z z' μsec) (ζ, p)) ∂(μW.prod μW') = ∫⁻ ζ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) * ∫⁻ p : Mt k r × Mt k r, f ((Matrix.of p.1)⁻¹ * embWb k r (μsec ζ) * Matrix.of p.2) ∂(μW.prod μW' …`. Use `lintegral_congr_ae ?_` and prove the remaining obligations.

Use `filter_upwards [ae_Om (r := r) z z'] with ζ hζ`. Break down `hζ with hζ | hζ` into its components or cases. Use `congr 1`. Use `lintegral_congr fun p => ?_` and prove the remaining obligations. Use `show f ((Matrix.of p.1 : Mat k r)⁻¹ * embWb k r (secF k r z z' μsec ζ) * Matrix.of p.2) = _`.

Rewrite using `[secF_on hζ]`. Rewrite using `[hζ]`. Simplify using the standard rewrite rules. Establish `hcne : (c : ℝ≥0∞) ≠ 0` using `by exact_mod_cast hc0`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← mul_assoc, ENNReal.inv_mul_cancel hcne ENNReal.coe_ne_top, one_mul]`. Use `_ = (c : ℝ≥0∞)⁻¹ * ∫⁻ m, f m ∂(nu z z' (secF k r z z' μsec) μW μW') := by rw [e1]`. Use `_ = (c : ℝ≥0∞)⁻¹ * ∫⁻ ζ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) * ∫⁻ p, f (Phi (secF k r z z' μsec) (ζ, p)) ∂(μW.prod μW') := congrArg (fun t => (c : ℝ≥0∞)⁻¹ * t) hint`. Use `_ = _ := by rw [e2, ENNReal.coe_inv hc0]`.
-/
theorem rank_one_formula_of_parts : Formalism.FourierDecayAlt.B2.AssembleRankOne := by
  intro HU CWb CW KW UF RM RC HI k r z z' μsec μb μW μW' hk hz hz' hT hT' hsec hb hW hW'
  haveI := haar_sigmaFinite hW
  haveI := haar_sigmaFinite hW'
  have hsm : MeasSec (secF k r z z' μsec) := secF_meas hsec
  have hss : IsSection k r z z' (secF k r z z' μsec) := secF_section hsec
  have hsu : ∀ ζ, (secF k r z z' μsec ζ)ᴴ * Hb k * secF k r z z' μsec ζ = Hb k := secF_unit hsec
  obtain ⟨c, hc⟩ := HU k r (UWb k r) μb (nu z z' (secF k r z z' μsec) μW μW') (CWb k r) hb
    (nu_conc CWb CW UF z z' hsm hsu hW hW')
    (fun a ha => nu_left CWb CW UF HI z z' hsm hsu hk hz hz' hT hT' hss hW hW' a ha)
    (fun K hK => nu_finite KW RM z z' hsm hz hz' hT hT' hss hW hW' K hK)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact nu_ne_zero z z' hsm hW hW' (by rw [hc]; simp)
  refine ⟨c⁻¹, inv_pos.2 (pos_iff_ne_zero.2 hc0), fun f hf => ?_⟩
  have hint := lint_nu hsm z z' μW μW' f hf
  have e1 : ∫⁻ m, f m ∂(nu z z' (secF k r z z' μsec) μW μW') = (c : ℝ≥0∞) * ∫⁻ m, f m ∂μb := by
    rw [hc, lintegral_smul_measure]
    first
      | rfl
      | simp [ENNReal.smul_def]
      | simp
  have e2 : ∫⁻ ζ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) *
        ∫⁻ p, f (Phi (secF k r z z' μsec) (ζ, p)) ∂(μW.prod μW') =
      ∫⁻ ζ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) *
        ∫⁻ p : Mt k r × Mt k r, f ((Matrix.of p.1)⁻¹ * embWb k r (μsec ζ) * Matrix.of p.2) ∂(μW.prod μW') := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_Om (r := r) z z'] with ζ hζ
    rcases hζ with hζ | hζ
    · congr 1
      refine lintegral_congr fun p => ?_
      show f ((Matrix.of p.1 : Mat k r)⁻¹ * embWb k r (secF k r z z' μsec ζ) * Matrix.of p.2) = _
      rw [secF_on hζ]
    · rw [hζ]
      simp
  have hcne : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc0
  calc ∫⁻ m, f m ∂μb = (c : ℝ≥0∞)⁻¹ * ((c : ℝ≥0∞) * ∫⁻ m, f m ∂μb) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hcne ENNReal.coe_ne_top, one_mul]
    _ = (c : ℝ≥0∞)⁻¹ * ∫⁻ m, f m ∂(nu z z' (secF k r z z' μsec) μW μW') := by rw [e1]
    _ = (c : ℝ≥0∞)⁻¹ * ∫⁻ ζ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) *
        ∫⁻ p, f (Phi (secF k r z z' μsec) (ζ, p)) ∂(μW.prod μW') := congrArg (fun t => (c : ℝ≥0∞)⁻¹ * t) hint
    _ = _ := by rw [e2, ENNReal.coe_inv hc0]

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.RankOneEmbeddings.In

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1

variable {k r : ℕ}

/- English proof (translation)
Conclude with `mulM_cont.measurable`.
-/
theorem mulM_meas : Measurable (mulM (k := k) (r := r)) := by
  exact mulM_cont.measurable

attribute [local fun_prop] mulM_meas invM_meas

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply, Matrix.one_apply]`. Establish `hi` using `i.isLt`. Establish `hj` using `j.isLt`. Distinguish the cases in `hm : r ≤ i.val ∧ i.val ≤ r + k`.

Rewrite using `[Finset.sum_eq_single i]`. Apply the tactic sequence `simp only [Hpk] split_ifs <;> (first`. Consider the case `(exfalso; (try simp only [Fin.ext_iff, Fin.val_mk, ne_eq, and_true, true_and] at *); omega)`. Consider the case `(norm_num; done)`. Consider the case `rfl)`.

Introduce `l _ hl`. Establish `: Hpk k r i l = 0`. Simplify using `only [Hpk]`. Apply the tactic sequence `split_ifs <;> (first`. Consider the case `(exfalso; (try simp only [Fin.ext_iff, Fin.val_mk, ne_eq, and_true, true_and] at *); omega)`.

Consider the case `(norm_num; done)`. Consider the case `rfl)`. Rewrite using `[this, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`.

Establish `hp : 2 * r + k - i.val < 2 * r + k + 1` using `by omega`. Rewrite using `[Finset.sum_eq_single ⟨2 * r + k - i.val, hp⟩]`. Apply the tactic sequence `simp only [Hpk] split_ifs <;> (first`. Consider the case `(exfalso; (try simp only [Fin.ext_iff, Fin.val_mk, ne_eq, and_true, true_and] at *); omega)`. Consider the case `(norm_num; done)`.

Consider the case `rfl)`. Introduce `l _ hl`. Establish `: Hpk k r i l = 0`. Simplify using `only [Hpk]`. Apply the tactic sequence `split_ifs <;> (first`.

Consider the case `(exfalso; (try simp only [Fin.ext_iff, Fin.val_mk, ne_eq, and_true, true_and] at *); omega)`. Consider the case `(norm_num; done)`. Consider the case `rfl)`. Rewrite using `[this, zero_mul]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`.
-/
private lemma hpk_sq_lemma : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hi := i.isLt
  have hj := j.isLt
  by_cases hm : r ≤ i.val ∧ i.val ≤ r + k
  · rw [Finset.sum_eq_single i]
    · simp only [Hpk]
      split_ifs <;> (first
          | (exfalso; (try simp only [Fin.ext_iff, Fin.val_mk, ne_eq, and_true, true_and] at *); omega)
          | (norm_num; done)
          | rfl)
    · intro l _ hl
      have : Hpk k r i l = 0 := by
        simp only [Hpk]
        split_ifs <;> (first
          | (exfalso; (try simp only [Fin.ext_iff, Fin.val_mk, ne_eq, and_true, true_and] at *); omega)
          | (norm_num; done)
          | rfl)
      rw [this, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · have hp : 2 * r + k - i.val < 2 * r + k + 1 := by omega
    rw [Finset.sum_eq_single ⟨2 * r + k - i.val, hp⟩]
    · simp only [Hpk]
      split_ifs <;> (first
          | (exfalso; (try simp only [Fin.ext_iff, Fin.val_mk, ne_eq, and_true, true_and] at *); omega)
          | (norm_num; done)
          | rfl)
    · intro l _ hl
      have : Hpk k r i l = 0 := by
        simp only [Hpk]
        split_ifs <;> (first
          | (exfalso; (try simp only [Fin.ext_iff, Fin.val_mk, ne_eq, and_true, true_and] at *); omega)
          | (norm_num; done)
          | rfl)
      rw [this, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Establish `h1 : hᴴ * Hpk k r * h = Hpk k r` using `hh.1`. Establish `hd : (Hpk k r).det ≠ 0`. Introduce `h0`. Use `congrArg Matrix.det (hpk_sq_lemma (k := k) (r := r))` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, h0, zero_mul, Matrix.det_one]`.

Conclude with `zero_ne_one this`. Establish `h2` using `congrArg Matrix.det h1`. Rewrite `h2` using `[Matrix.det_mul, Matrix.det_mul]`. Rewrite using `[isUnit_iff_ne_zero]`. Introduce `h0`.

Rewrite `h2` using `[h0, mul_zero]`. Conclude with `hd h2.symm`.
-/
theorem uw_unit {z : Vc k r} {h : Mat k r} (hh : h ∈ UWset k r z) : IsUnit h.det := by
  have h1 : hᴴ * Hpk k r * h = Hpk k r := hh.1
  have hd : (Hpk k r).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det (hpk_sq_lemma (k := k) (r := r))
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, Matrix.det_mul] at h2
  rw [isUnit_iff_ne_zero]
  intro h0
  rw [h0, mul_zero] at h2
  exact hd h2.symm

/- English proof (translation)
Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Simplify using `only [conjM, Matrix.mul_apply, Matrix.of_apply]`. Use `fun_prop`.
-/
theorem conjM_cont (a : Mat k r) : Continuous (conjM a : Mt k r → Mt k r) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [conjM, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

def m1 (p : Mt k r × Mt k r) : Mt k r := mulM (p.2, p.1)

/- English proof (translation)
Conclude with `mulM_cont.measurable.comp (measurable_snd.prodMk measurable_fst)`.
-/
theorem first_coordinate_map_measurable : Measurable (m1 (k := k) (r := r)) := by
  exact mulM_cont.measurable.comp (measurable_snd.prodMk measurable_fst)

/- English proof (translation)
Use extensionality with `S hS`. Rewrite using `[Measure.map_apply first_coordinate_map_measurable hS, Measure.map_apply mulM_meas hS, Measure.prod_apply (first_coordinate_map_measurable hS), Measure.prod_apply (mulM_meas hS)]`. Use `lintegral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [ae_mem hW] with h hh`. Establish `hu` using `uw_unit hh`.

Establish `hT' : MeasurableSet (Prod.mk h ⁻¹' (m1 ⁻¹' S))` using `(measurable_const.prodMk measurable_id : Measurable fun n : Mt k r => (h, n)) (first_coordinate_map_measurable hS)`. Establish `hset : Prod.mk h ⁻¹' (mulM ⁻¹' S) = conjM (Matrix.of h) ⁻¹' (Prod.mk h ⁻¹' (m1 ⁻¹' S))`. Use extensionality with `n`. Simplify using `only [Set.mem_preimage, m1]`. Establish `e : mulM (conjM (Matrix.of h) n, h) = mulM (h, n)` using `by show (Matrix.of h : Mat k r) * Matrix.of n * (Matrix.of h : Mat k r)⁻¹ * Matrix.of h = (Matrix.of h : Mat k r) * Matrix.of n`.

Rewrite using `[Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]`. Rewrite using `[e]`. Rewrite using `[hset, ← Measure.map_apply (conjM_cont _).measurable hT', hc _ hh]`.
-/
theorem swap_meas {z : Vc k r} {μW μN : Measure (Mt k r)} [SFinite μW] [SFinite μN]
    (hW : IsHaarOn (UWset k r z) μW) (hc : ∀ h ∈ UWset k r z, μN.map (conjM h) = μN) :
    (μW.prod μN).map m1 = (μW.prod μN).map mulM := by
  ext S hS
  rw [Measure.map_apply first_coordinate_map_measurable hS, Measure.map_apply mulM_meas hS,
    Measure.prod_apply (first_coordinate_map_measurable hS), Measure.prod_apply (mulM_meas hS)]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_mem hW] with h hh
  have hu := uw_unit hh
  have hT' : MeasurableSet (Prod.mk h ⁻¹' (m1 ⁻¹' S)) :=
    (measurable_const.prodMk measurable_id : Measurable fun n : Mt k r => (h, n)) (first_coordinate_map_measurable hS)
  have hset : Prod.mk h ⁻¹' (mulM ⁻¹' S) = conjM (Matrix.of h) ⁻¹' (Prod.mk h ⁻¹' (m1 ⁻¹' S)) := by
    ext n
    simp only [Set.mem_preimage, m1]
    have e : mulM (conjM (Matrix.of h) n, h) = mulM (h, n) := by
      show (Matrix.of h : Mat k r) * Matrix.of n * (Matrix.of h : Mat k r)⁻¹ * Matrix.of h =
        (Matrix.of h : Mat k r) * Matrix.of n
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
    rw [e]
  rw [hset, ← Measure.map_apply (conjM_cont _).measurable hT', hc _ hh]

/- English proof (translation)
Establish `e1` using `Measure.measurePreserving_swap (μ := a.prod b) (ν := c.prod d)`. Establish `e2` using `measurePreserving_prodAssoc c d (a.prod b)`. Establish `g1` using `(measurePreserving_prodAssoc d a b).symm MeasurableEquiv.prodAssoc`. Establish `g2` using `(Measure.measurePreserving_swap (μ := d) (ν := a)).prod (MeasurePreserving.id b)`. Establish `g3` using `measurePreserving_prodAssoc a d b`.

Establish `eg` using `(MeasurePreserving.id c).prod (g3.comp (g2.comp g1))`. Establish `e4` using `(measurePreserving_prodAssoc c a (d.prod b)).symm MeasurableEquiv.prodAssoc`. Use `e4.comp (eg.comp (e2.comp e1))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `all_goals (funext x; rfl)`.
-/
theorem mp_perm {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    (a : Measure α) (b : Measure β) (c : Measure γ) (d : Measure δ) [SFinite a] [SFinite b] [SFinite c] [SFinite d] :
    MeasurePreserving (fun x : (α × β) × (γ × δ) => ((x.2.1, x.1.1), (x.2.2, x.1.2)))
      ((a.prod b).prod (c.prod d)) ((c.prod a).prod (d.prod b)) := by
  have e1 := Measure.measurePreserving_swap (μ := a.prod b) (ν := c.prod d)
  have e2 := measurePreserving_prodAssoc c d (a.prod b)
  have g1 := (measurePreserving_prodAssoc d a b).symm MeasurableEquiv.prodAssoc
  have g2 := (Measure.measurePreserving_swap (μ := d) (ν := a)).prod (MeasurePreserving.id b)
  have g3 := measurePreserving_prodAssoc a d b
  have eg := (MeasurePreserving.id c).prod (g3.comp (g2.comp g1))
  have e4 := (measurePreserving_prodAssoc c a (d.prod b)).symm MeasurableEquiv.prodAssoc
  have := e4.comp (eg.comp (e2.comp e1))
  convert this using 1
  all_goals (funext x; rfl)

def sgF (x : SS k r × Mt k r) : Mt k r :=
  mulM (mulM (mulM (mulM (invM x.1.1.1, invM x.1.1.2), x.2), x.1.2.2), x.1.2.1)

/- English proof (translation)
Unfold `sgF`. Use `fun_prop`.
-/
theorem sgF_meas : Measurable (sgF (k := k) (r := r)) := by
  unfold sgF
  fun_prop

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sgs_eq (p : SS k r) (g : Mat k r) : sgs p g = sgF (p, g) := rfl

/- English proof (translation)
Set `Γ : Mt k r × Mt k r → ℝ≥0∞` to `fun ab => f (mulM (mulM (invM ab.1, mulM (g0, E)), ab.2))`. Establish `hΓ : Measurable Γ` using `by show Measurable fun ab : Mt k r × Mt k r => f (mulM (mulM (invM ab.1, mulM (g0, E)), ab.2)) fun_prop`. Establish `r1 : ∫⁻ p : SS k r, f (sgF (p, mulM (g0, E))) ∂((μW.prod μN).prod (μW'.prod μN)) = ∫⁻ p : SS k r, Γ (Prod.map m1 m1 p) ∂((μW.prod μN).prod (μW'.prod μN))`. Use `lintegral_congr fun p => congrArg f ?_` and prove the remaining obligations. Use `show (Matrix.of p.1.1 : Mat k r)⁻¹ * (Matrix.of p.1.2 : Mat k r)⁻¹ * ((Matrix.of g0 : Mat k r) * Matrix.of E) * Matrix.of p.2.2 * Matrix.of p.2.1 = ((Matrix.of p.1.2 : Mat k r) * Matrix.of p.1.1)⁻¹ * ((Matrix.of g0 : Mat k r) * Matrix.of E) * ((Matrix.of p.2.2 : Mat k r) * Matrix …`.

Rewrite using `[Matrix.mul_inv_rev, ← Matrix.mul_assoc _ (Matrix.of p.2.2 : Mat k r)]`. Establish `r2 : ∫⁻ p : SS k r, Γ (Prod.map m1 m1 p) ∂((μW.prod μN).prod (μW'.prod μN)) = ∫⁻ p : SS k r, Γ (Prod.map mulM mulM p) ∂((μW.prod μN).prod (μW'.prod μN))`. Rewrite using `[← lintegral_map hΓ (first_coordinate_map_measurable.prodMap first_coordinate_map_measurable), ← lintegral_map hΓ (mulM_meas.prodMap mulM_meas), ← Measure.map_prod_map _ _ first_coordinate_map_measurable first_coordinate_map_measurable, ← Measure.map_prod_map _ _ mulM_meas mulM_m …`. Establish `hΓ2 : Measurable fun p : SS k r => Γ (Prod.map mulM mulM p)` using `hΓ.comp (mulM_meas.prodMap mulM_meas)`. Establish `r3 : ∫⁻ x : (Mt k r × Mt k r) × (Mt k r × Mt k r), Γ (Prod.map mulM mulM ((x.2.1, x.1.1), (x.2.2, x.1.2))) ∂((μN.prod μN).prod (μW.prod μW')) = ∫⁻ p : SS k r, Γ (Prod.map mulM mulM p) ∂((μW.prod μN).prod (μW'.prod μN))` using `(mp_perm μN μN μW μW').lintegral_comp hΓ2`.

Rewrite using `[r1, r2, ← r3, lintegral_prod (fun x : (Mt k r × Mt k r) × (Mt k r × Mt k r) => Γ (Prod.map mulM mulM ((x.2.1, x.1.1), (x.2.2, x.1.2)))) (hΓ2.comp (mp_perm μN μN μW μW').measurable).aemeasurable]`. Use `lintegral_congr fun nn => ?_` and prove the remaining obligations. Use `lintegral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μW) (ν := μW')).ae (ae_mem hW)] with hh h1`. Use `congrArg f ?_` and prove the remaining obligations.

Use `show (Matrix.of nn.1 : Mat k r)⁻¹ * (Matrix.of g0 : Mat k r) * ((Matrix.of hh.1 : Mat k r)⁻¹ * Matrix.of E * Matrix.of hh.2) * Matrix.of nn.2 = ((Matrix.of hh.1 : Mat k r) * Matrix.of nn.1)⁻¹ * ((Matrix.of g0 : Mat k r) * Matrix.of E) * ((Matrix.of hh.2 : Mat k r) * Matrix.of nn. …`. Establish `hu` using `uw_unit h1`. Establish `e1 : (Matrix.of g0 : Mat k r) * (Matrix.of hh.1 : Mat k r)⁻¹ = (Matrix.of hh.1 : Mat k r)⁻¹ * Matrix.of g0`. Establish `e0` using `hcomm _ ((UF k r).2.1 z h1)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Matrix.nonsing_inv_mul_cancel_left _ _ hu]`. Use `_ = (Matrix.of hh.1 : Mat k r)⁻¹ * Matrix.of g0 := by`. Rewrite using `[e0, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hu]`. Rewrite using `[Matrix.mul_inv_rev]`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[← Matrix.mul_assoc (Matrix.of g0 : Mat k r) (Matrix.of hh.1 : Mat k r)⁻¹, e1]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem key {z z' : Vc k r} {μW μN μW' : Measure (Mt k r)} [SFinite μW] [SFinite μN] [SFinite μW']
    (UF : UWbFacts) (hW : IsHaarOn (UWset k r z) μW) (hW' : IsHaarOn (UWset k r z') μW')
    (hc : ∀ h ∈ UWset k r z, μN.map (conjM h) = μN) (hc' : ∀ h ∈ UWset k r z', μN.map (conjM h) = μN)
    (g0 E : Mt k r) (hcomm : ∀ m ∈ UWb k r, m * (Matrix.of g0 : Mat k r) = (Matrix.of g0 : Mat k r) * m)
    (f : Mt k r → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ nn : Mt k r × Mt k r, ∫⁻ hh : Mt k r × Mt k r,
        f (mulM (mulM (mulM (invM nn.1, g0), mulM (mulM (invM hh.1, E), hh.2)), nn.2)) ∂(μW.prod μW') ∂(μN.prod μN) =
      ∫⁻ p : SS k r, f (sgF (p, mulM (g0, E))) ∂((μW.prod μN).prod (μW'.prod μN)) := by
  let Γ : Mt k r × Mt k r → ℝ≥0∞ := fun ab => f (mulM (mulM (invM ab.1, mulM (g0, E)), ab.2))
  have hΓ : Measurable Γ := by
    show Measurable fun ab : Mt k r × Mt k r => f (mulM (mulM (invM ab.1, mulM (g0, E)), ab.2))
    fun_prop
  have r1 : ∫⁻ p : SS k r, f (sgF (p, mulM (g0, E))) ∂((μW.prod μN).prod (μW'.prod μN)) =
      ∫⁻ p : SS k r, Γ (Prod.map m1 m1 p) ∂((μW.prod μN).prod (μW'.prod μN)) := by
    refine lintegral_congr fun p => congrArg f ?_
    show (Matrix.of p.1.1 : Mat k r)⁻¹ * (Matrix.of p.1.2 : Mat k r)⁻¹ * ((Matrix.of g0 : Mat k r) * Matrix.of E) *
        Matrix.of p.2.2 * Matrix.of p.2.1 =
      ((Matrix.of p.1.2 : Mat k r) * Matrix.of p.1.1)⁻¹ * ((Matrix.of g0 : Mat k r) * Matrix.of E) *
        ((Matrix.of p.2.2 : Mat k r) * Matrix.of p.2.1)
    rw [Matrix.mul_inv_rev, ← Matrix.mul_assoc _ (Matrix.of p.2.2 : Mat k r)]
  have r2 : ∫⁻ p : SS k r, Γ (Prod.map m1 m1 p) ∂((μW.prod μN).prod (μW'.prod μN)) =
      ∫⁻ p : SS k r, Γ (Prod.map mulM mulM p) ∂((μW.prod μN).prod (μW'.prod μN)) := by
    rw [← lintegral_map hΓ (first_coordinate_map_measurable.prodMap first_coordinate_map_measurable), ← lintegral_map hΓ (mulM_meas.prodMap mulM_meas),
      ← Measure.map_prod_map _ _ first_coordinate_map_measurable first_coordinate_map_measurable, ← Measure.map_prod_map _ _ mulM_meas mulM_meas,
      swap_meas hW hc, swap_meas hW' hc']
  have hΓ2 : Measurable fun p : SS k r => Γ (Prod.map mulM mulM p) := hΓ.comp (mulM_meas.prodMap mulM_meas)
  have r3 : ∫⁻ x : (Mt k r × Mt k r) × (Mt k r × Mt k r), Γ (Prod.map mulM mulM ((x.2.1, x.1.1), (x.2.2, x.1.2)))
        ∂((μN.prod μN).prod (μW.prod μW')) =
      ∫⁻ p : SS k r, Γ (Prod.map mulM mulM p) ∂((μW.prod μN).prod (μW'.prod μN)) :=
    (mp_perm μN μN μW μW').lintegral_comp hΓ2
  rw [r1, r2, ← r3, lintegral_prod
    (fun x : (Mt k r × Mt k r) × (Mt k r × Mt k r) => Γ (Prod.map mulM mulM ((x.2.1, x.1.1), (x.2.2, x.1.2))))
    (hΓ2.comp (mp_perm μN μN μW μW').measurable).aemeasurable]
  refine lintegral_congr fun nn => ?_
  refine lintegral_congr_ae ?_
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μW) (ν := μW')).ae (ae_mem hW)] with hh h1
  refine congrArg f ?_
  show (Matrix.of nn.1 : Mat k r)⁻¹ * (Matrix.of g0 : Mat k r) *
        ((Matrix.of hh.1 : Mat k r)⁻¹ * Matrix.of E * Matrix.of hh.2) * Matrix.of nn.2 =
    ((Matrix.of hh.1 : Mat k r) * Matrix.of nn.1)⁻¹ * ((Matrix.of g0 : Mat k r) * Matrix.of E) *
      ((Matrix.of hh.2 : Mat k r) * Matrix.of nn.2)
  have hu := uw_unit h1
  have e1 : (Matrix.of g0 : Mat k r) * (Matrix.of hh.1 : Mat k r)⁻¹ = (Matrix.of hh.1 : Mat k r)⁻¹ * Matrix.of g0 := by
    have e0 := hcomm _ ((UF k r).2.1 z h1)
    calc (Matrix.of g0 : Mat k r) * (Matrix.of hh.1 : Mat k r)⁻¹
        = (Matrix.of hh.1 : Mat k r)⁻¹ * ((Matrix.of hh.1 : Mat k r) * Matrix.of g0) * (Matrix.of hh.1 : Mat k r)⁻¹ := by
          rw [Matrix.nonsing_inv_mul_cancel_left _ _ hu]
      _ = (Matrix.of hh.1 : Mat k r)⁻¹ * Matrix.of g0 := by
          rw [e0, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hu]
  rw [Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Matrix.of g0 : Mat k r) (Matrix.of hh.1 : Mat k r)⁻¹, e1]
  simp only [Matrix.mul_assoc]

end Formalism.FourierDecayAlt.P.RankOneEmbeddings.In

namespace Formalism.FourierDecayAlt.P.RankOneEmbeddings.In

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1

variable {k r : ℕ}

attribute [local fun_prop] mulM_meas invM_meas sgF_meas

def bc1 (k r : ℕ) (c : Fin r → ℂ) : Mt k r := bigCell k r c 1

/- English proof (translation)
Use `measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_` and prove the remaining obligations. Simplify using `only [bc1, bigCell]`. Use `split_ifs`. Apply the tactic sequence `all_goals first`. Consider the case `exact measurable_const`.

Consider the case `exact measurable_pi_apply _`. Consider the case `exact (continuous_star.measurable.comp (measurable_pi_apply _)).inv`. Consider the case `fun_prop`.
-/
theorem big_cell_coordinate_measurable : Measurable (bc1 k r) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  simp only [bc1, bigCell]
  split_ifs
  all_goals first
    | exact measurable_const
    | exact measurable_pi_apply _
    | exact (continuous_star.measurable.comp (measurable_pi_apply _)).inv
    | fun_prop

/- English proof (translation)
Unfold `cWeight`. Use `fun_prop`.
-/
theorem cW_cont : Continuous (cWeight k r) := by
  unfold cWeight
  fun_prop

/- English proof (translation)
Unfold `cWeight`. Conclude with `Finset.prod_nonneg fun a _ => pow_nonneg (norm_nonneg _) _`.
-/
theorem cW_nonneg (c : Fin r → ℂ) : 0 ≤ cWeight k r c := by
  unfold cWeight
  exact Finset.prod_nonneg fun a _ => pow_nonneg (norm_nonneg _) _

set_option maxHeartbeats 800000 in

/- English proof (translation)
Establish `hcw : Measurable (cWeight k r)` using `cW_cont.measurable`. Establish `hzw : Measurable (zWeight k T T')` using `zW_meas k T T'`. Establish `hKm : Measurable fun q : (Fin r → ℂ) × ℂ => ∫⁻ p : SS k r, f (sgF (p, mulM (G0 q.1, ES q.2))) ∂((μW.prod μN).prod (μW'.prod μN))` using `(by fun_prop : Measurable fun x : ((Fin r → ℂ) × ℂ) × SS k r => f (sgF (x.2, mulM (G0 x.1.1, ES x.1.2)))).lintegral_prod_right'`. Establish `hA : ∀ c : Fin r → ℂ, ∫⁻ p : (Mt k r × Mt k r) × Mt k r, f (mulM (mulM (mulM (invM p.1.1, G0 c), p.2), p.1.2)) ∂((μN.prod μN).prod μb) = (C2 : ℝ≥0∞) * ∫⁻ ζ, ENNReal.ofReal (zWeight k T T' ζ) * ∫⁻ p : SS k r, f (sgF (p, mulM (G0 c, ES ζ))) ∂((μW.prod μN).prod (μW'.prod μN))`. Introduce `c`.

Establish `hIm : Measurable fun y : (Mt k r × Mt k r) × ℂ => ∫⁻ hh : Mt k r × Mt k r, f (mulM (mulM (mulM (invM y.1.1, G0 c), mulM (mulM (invM hh.1, ES y.2), hh.2)), y.1.2)) ∂(μW.prod μW')` using `(by fun_prop : Measurable fun x : ((Mt k r × Mt k r) × ℂ) × (Mt k r × Mt k r) => f (mulM (mulM (mulM (invM x.1.1.1, G0 c), mulM (mulM (invM x.2.1, ES x.1.2), x.2.2)), x.1.1.2))).lintegral_prod_right'`. Establish `hJ : Measurable fun y : (Mt k r × Mt k r) × ℂ => ENNReal.ofReal (zWeight k T T' y.2) * ∫⁻ hh : Mt k r × Mt k r, f (mulM (mulM (mulM (invM y.1.1, G0 c), mulM (mulM (invM hh.1, ES y.2), hh.2)), y.1.2)) ∂(μW.prod μW')` using `(hzw.comp measurable_snd).ennreal_ofReal.mul hIm`. Establish `hJx : Measurable fun nn : Mt k r × Mt k r => ∫⁻ ζ, ENNReal.ofReal (zWeight k T T' ζ) * ∫⁻ hh : Mt k r × Mt k r, f (mulM (mulM (mulM (invM nn.1, G0 c), mulM (mulM (invM hh.1, ES ζ), hh.2)), nn.2)) ∂(μW.prod μW')` using `hJ.lintegral_prod_right'`. Rewrite using `[lintegral_prod _ (by fun_prop : Measurable fun x : (Mt k r × Mt k r) × Mt k r => f (mulM (mulM (mulM (invM x.1.1, G0 c), x.2), x.1.2))).aemeasurable]`. Use `Eq.trans (lintegral_congr fun nn => hR (fun m => f (mulM (mulM (mulM (invM nn.1, G0 c), m), nn.2))) (by fun_prop)) ?_` and prove the remaining obligations.

Rewrite using `[lintegral_const_mul _ hJx, lintegral_lintegral_swap (f := fun (nn : Mt k r × Mt k r) (ζ : ℂ) => ENNReal.ofReal (zWeight k T T' ζ) * ∫⁻ hh : Mt k r × Mt k r, f (mulM (mulM (mulM (invM nn.1, G0 c), mulM (mulM (invM hh.1, ES ζ), hh.2)), nn.2)) ∂(μW.prod μW')) hJ.aemeasurable]`. Use `congrArg (fun t => (C2 : ℝ≥0∞) * t) ?_` and prove the remaining obligations. Use `lintegral_congr fun ζ => ?_` and prove the remaining obligations. Establish `hC : Measurable fun nn : Mt k r × Mt k r => ∫⁻ hh : Mt k r × Mt k r, f (mulM (mulM (mulM (invM nn.1, G0 c), mulM (mulM (invM hh.1, ES ζ), hh.2)), nn.2)) ∂(μW.prod μW')` using `(by fun_prop : Measurable fun x : (Mt k r × Mt k r) × (Mt k r × Mt k r) => f (mulM (mulM (mulM (invM x.1.1, G0 c), mulM (mulM (invM x.2.1, ES ζ), x.2.2)), x.1.2))).lintegral_prod_right'`. Rewrite using `[lintegral_const_mul _ hC, hkey c ζ f hf]`.

Establish `hD : ∀ c : Fin r → ℂ, Measurable fun ζ : ℂ => ENNReal.ofReal (zWeight k T T' ζ) * ∫⁻ p : SS k r, f (sgF (p, mulM (G0 c, ES ζ))) ∂((μW.prod μN).prod (μW'.prod μN))` using `fun c => by`. Establish `hK' : Measurable fun ζ : ℂ => ∫⁻ p : SS k r, f (sgF (p, mulM (G0 c, ES ζ))) ∂((μW.prod μN).prod (μW'.prod μN))` using `(by fun_prop : Measurable fun x : ℂ × SS k r => f (sgF (x.2, mulM (G0 c, ES x.1)))).lintegral_prod_right'`. Conclude with `hzw.ennreal_ofReal.mul hK'`. Establish `hB : ∀ c : Fin r → ℂ, ENNReal.ofReal (cWeight k r c) * ∫⁻ p : (Mt k r × Mt k r) × Mt k r, f (mulM (mulM (mulM (invM p.1.1, G0 c), p.2), p.1.2)) ∂((μN.prod μN).prod μb) = (C2 : ℝ≥0∞) * ∫⁻ ζ, ENNReal.ofReal (cWeight k r c * zWeight k T T' ζ) * ∫⁻ p : SS k r, f (sgF (p, mulM (G0 c, …` using `fun c => by`. Rewrite using `[hA c, ← mul_assoc, mul_comm (ENNReal.ofReal (cWeight k r c)) (C2 : ℝ≥0∞), mul_assoc, ← lintegral_const_mul _ (hD c)]`.

Use `congrArg (fun t => (C2 : ℝ≥0∞) * t) ?_` and prove the remaining obligations. Use `lintegral_congr fun ζ => ?_` and prove the remaining obligations. Rewrite using `[ENNReal.ofReal_mul (cW_nonneg c), mul_assoc]`. Establish `hQ : Measurable fun q : (Fin r → ℂ) × ℂ => ENNReal.ofReal (cWeight k r q.1 * zWeight k T T' q.2) * ∫⁻ p : SS k r, f (sgF (p, mulM (G0 q.1, ES q.2))) ∂((μW.prod μN).prod (μW'.prod μN))` using `((hcw.comp measurable_fst).mul (hzw.comp measurable_snd)).ennreal_ofReal.mul hKm`. Establish `hE : Measurable fun c : Fin r → ℂ => ∫⁻ ζ, ENNReal.ofReal (cWeight k r c * zWeight k T T' ζ) * ∫⁻ p : SS k r, f (sgF (p, mulM (G0 c, ES ζ))) ∂((μW.prod μN).prod (μW'.prod μN))` using `hQ.lintegral_prod_right'`.

Rewrite using `[hIt f hf, lintegral_congr hB, lintegral_const_mul _ hE, Measure.volume_eq_prod, lintegral_prod _ hQ.aemeasurable, ENNReal.coe_mul, mul_assoc]`.
-/
theorem engine {μG μN μb μW μW' : Measure (Mt k r)} [SFinite μN] [SFinite μb] [SFinite μW] [SFinite μW'] (T T' : ℝ)
    (G0 : (Fin r → ℂ) → Mt k r) (hG0 : Measurable G0) (ES : ℂ → Mt k r) (hES : Measurable ES) (C1 C2 : ℝ≥0)
    (hIt : ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ g, f g ∂μG = (C1 : ℝ≥0∞) * ∫⁻ c : Fin r → ℂ,
      ENNReal.ofReal (cWeight k r c) * ∫⁻ p : (Mt k r × Mt k r) × Mt k r,
        f (mulM (mulM (mulM (invM p.1.1, G0 c), p.2), p.1.2)) ∂((μN.prod μN).prod μb))
    (hR : ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ m, f m ∂μb = (C2 : ℝ≥0∞) * ∫⁻ ζ : ℂ,
      ENNReal.ofReal (zWeight k T T' ζ) * ∫⁻ p : Mt k r × Mt k r, f (mulM (mulM (invM p.1, ES ζ), p.2)) ∂(μW.prod μW'))
    (hkey : ∀ (c : Fin r → ℂ) (ζ : ℂ) (f : Mt k r → ℝ≥0∞), Measurable f →
      ∫⁻ nn : Mt k r × Mt k r, ∫⁻ hh : Mt k r × Mt k r,
        f (mulM (mulM (mulM (invM nn.1, G0 c), mulM (mulM (invM hh.1, ES ζ), hh.2)), nn.2))
          ∂(μW.prod μW') ∂(μN.prod μN) =
      ∫⁻ p : SS k r, f (sgF (p, mulM (G0 c, ES ζ))) ∂((μW.prod μN).prod (μW'.prod μN)))
    (f : Mt k r → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ g, f g ∂μG = ((C1 * C2 : ℝ≥0) : ℝ≥0∞) * ∫⁻ q : (Fin r → ℂ) × ℂ,
      ENNReal.ofReal (cWeight k r q.1 * zWeight k T T' q.2) *
        ∫⁻ p : SS k r, f (sgF (p, mulM (G0 q.1, ES q.2))) ∂((μW.prod μN).prod (μW'.prod μN)) := by
  have hcw : Measurable (cWeight k r) := cW_cont.measurable
  have hzw : Measurable (zWeight k T T') := zW_meas k T T'
  have hKm : Measurable fun q : (Fin r → ℂ) × ℂ =>
      ∫⁻ p : SS k r, f (sgF (p, mulM (G0 q.1, ES q.2))) ∂((μW.prod μN).prod (μW'.prod μN)) :=
    (by fun_prop : Measurable fun x : ((Fin r → ℂ) × ℂ) × SS k r =>
      f (sgF (x.2, mulM (G0 x.1.1, ES x.1.2)))).lintegral_prod_right'
  have hA : ∀ c : Fin r → ℂ, ∫⁻ p : (Mt k r × Mt k r) × Mt k r,
      f (mulM (mulM (mulM (invM p.1.1, G0 c), p.2), p.1.2)) ∂((μN.prod μN).prod μb) =
      (C2 : ℝ≥0∞) * ∫⁻ ζ, ENNReal.ofReal (zWeight k T T' ζ) *
        ∫⁻ p : SS k r, f (sgF (p, mulM (G0 c, ES ζ))) ∂((μW.prod μN).prod (μW'.prod μN)) := by
    intro c
    have hIm : Measurable fun y : (Mt k r × Mt k r) × ℂ => ∫⁻ hh : Mt k r × Mt k r,
        f (mulM (mulM (mulM (invM y.1.1, G0 c), mulM (mulM (invM hh.1, ES y.2), hh.2)), y.1.2)) ∂(μW.prod μW') :=
      (by fun_prop : Measurable fun x : ((Mt k r × Mt k r) × ℂ) × (Mt k r × Mt k r) =>
        f (mulM (mulM (mulM (invM x.1.1.1, G0 c), mulM (mulM (invM x.2.1, ES x.1.2), x.2.2)), x.1.1.2))).lintegral_prod_right'
    have hJ : Measurable fun y : (Mt k r × Mt k r) × ℂ => ENNReal.ofReal (zWeight k T T' y.2) *
        ∫⁻ hh : Mt k r × Mt k r, f (mulM (mulM (mulM (invM y.1.1, G0 c), mulM (mulM (invM hh.1, ES y.2), hh.2)), y.1.2)) ∂(μW.prod μW') :=
      (hzw.comp measurable_snd).ennreal_ofReal.mul hIm
    have hJx : Measurable fun nn : Mt k r × Mt k r => ∫⁻ ζ, ENNReal.ofReal (zWeight k T T' ζ) *
        ∫⁻ hh : Mt k r × Mt k r, f (mulM (mulM (mulM (invM nn.1, G0 c), mulM (mulM (invM hh.1, ES ζ), hh.2)), nn.2)) ∂(μW.prod μW') :=
      hJ.lintegral_prod_right'
    rw [lintegral_prod _ (by fun_prop : Measurable fun x : (Mt k r × Mt k r) × Mt k r =>
      f (mulM (mulM (mulM (invM x.1.1, G0 c), x.2), x.1.2))).aemeasurable]
    refine Eq.trans (lintegral_congr fun nn =>
      hR (fun m => f (mulM (mulM (mulM (invM nn.1, G0 c), m), nn.2))) (by fun_prop)) ?_
    rw [lintegral_const_mul _ hJx, lintegral_lintegral_swap (f := fun (nn : Mt k r × Mt k r) (ζ : ℂ) =>
      ENNReal.ofReal (zWeight k T T' ζ) * ∫⁻ hh : Mt k r × Mt k r,
        f (mulM (mulM (mulM (invM nn.1, G0 c), mulM (mulM (invM hh.1, ES ζ), hh.2)), nn.2)) ∂(μW.prod μW'))
      hJ.aemeasurable]
    refine congrArg (fun t => (C2 : ℝ≥0∞) * t) ?_
    refine lintegral_congr fun ζ => ?_
    have hC : Measurable fun nn : Mt k r × Mt k r => ∫⁻ hh : Mt k r × Mt k r,
        f (mulM (mulM (mulM (invM nn.1, G0 c), mulM (mulM (invM hh.1, ES ζ), hh.2)), nn.2)) ∂(μW.prod μW') :=
      (by fun_prop : Measurable fun x : (Mt k r × Mt k r) × (Mt k r × Mt k r) =>
        f (mulM (mulM (mulM (invM x.1.1, G0 c), mulM (mulM (invM x.2.1, ES ζ), x.2.2)), x.1.2))).lintegral_prod_right'
    rw [lintegral_const_mul _ hC, hkey c ζ f hf]
  have hD : ∀ c : Fin r → ℂ, Measurable fun ζ : ℂ => ENNReal.ofReal (zWeight k T T' ζ) *
      ∫⁻ p : SS k r, f (sgF (p, mulM (G0 c, ES ζ))) ∂((μW.prod μN).prod (μW'.prod μN)) := fun c => by
    have hK' : Measurable fun ζ : ℂ => ∫⁻ p : SS k r, f (sgF (p, mulM (G0 c, ES ζ))) ∂((μW.prod μN).prod (μW'.prod μN)) :=
      (by fun_prop : Measurable fun x : ℂ × SS k r => f (sgF (x.2, mulM (G0 c, ES x.1)))).lintegral_prod_right'
    exact hzw.ennreal_ofReal.mul hK'
  have hB : ∀ c : Fin r → ℂ, ENNReal.ofReal (cWeight k r c) * ∫⁻ p : (Mt k r × Mt k r) × Mt k r,
        f (mulM (mulM (mulM (invM p.1.1, G0 c), p.2), p.1.2)) ∂((μN.prod μN).prod μb) =
      (C2 : ℝ≥0∞) * ∫⁻ ζ, ENNReal.ofReal (cWeight k r c * zWeight k T T' ζ) *
        ∫⁻ p : SS k r, f (sgF (p, mulM (G0 c, ES ζ))) ∂((μW.prod μN).prod (μW'.prod μN)) := fun c => by
    rw [hA c, ← mul_assoc, mul_comm (ENNReal.ofReal (cWeight k r c)) (C2 : ℝ≥0∞), mul_assoc,
      ← lintegral_const_mul _ (hD c)]
    refine congrArg (fun t => (C2 : ℝ≥0∞) * t) ?_
    refine lintegral_congr fun ζ => ?_
    rw [ENNReal.ofReal_mul (cW_nonneg c), mul_assoc]
  have hQ : Measurable fun q : (Fin r → ℂ) × ℂ => ENNReal.ofReal (cWeight k r q.1 * zWeight k T T' q.2) *
      ∫⁻ p : SS k r, f (sgF (p, mulM (G0 q.1, ES q.2))) ∂((μW.prod μN).prod (μW'.prod μN)) :=
    ((hcw.comp measurable_fst).mul (hzw.comp measurable_snd)).ennreal_ofReal.mul hKm
  have hE : Measurable fun c : Fin r → ℂ => ∫⁻ ζ, ENNReal.ofReal (cWeight k r c * zWeight k T T' ζ) *
      ∫⁻ p : SS k r, f (sgF (p, mulM (G0 c, ES ζ))) ∂((μW.prod μN).prod (μW'.prod μN)) :=
    hQ.lintegral_prod_right'
  rw [hIt f hf, lintegral_congr hB, lintegral_const_mul _ hE, Measure.volume_eq_prod,
    lintegral_prod _ hQ.aemeasurable, ENNReal.coe_mul, mul_assoc]

end Formalism.FourierDecayAlt.P.RankOneEmbeddings.In

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1 Formalism.FourierDecayAlt.P.RankOneEmbeddings.In

/- English proof (translation)
Introduce `hIter hR1 hConj hWbE hBCF UF hWF k r z z' μsec μG μW μN μW' hD`. Take `⟨μb, hb⟩` from `hWbE k r`. Establish `hsec'` using `secF_section hD.sec`. Establish `hsm` using `secF_meas hD.sec`. Use `haar_sigmaFinite hD.haarW` as an intermediate fact.

Use `haar_sigmaFinite hD.haarW'` as an intermediate fact. Use `haar_sigmaFinite hD.haarN` as an intermediate fact. Use `haar_sigmaFinite hb` as an intermediate fact. Take `⟨C1, hC1, h1⟩` from `hIter k r μG μN μb hD.haarG hD.haarN hb`. Take `⟨C2, hC2, h2⟩` from `hR1 k r z z' (secF k r z z' μsec) μb μW μW' hD.k_pos hD.z_mem hD.z'_mem hD.T_pos hD.T'_pos hsec' hb hD.haarW hD.haarW'`.

Use `⟨C1 * C2, mul_pos hC1 hC2, fun f hf => ?_⟩` and prove the remaining obligations. Establish `h1' : ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ g, f g ∂μG = (C1 : ℝ≥0∞) * ∫⁻ c : Fin r → ℂ, ENNReal.ofReal (cWeight k r c) * ∫⁻ p : (Mt k r × Mt k r) × Mt k r, f (mulM (mulM (mulM (invM p.1.1, bc1 k r c), p.2), p.1.2)) ∂((μN.prod μN).prod μb)` using `h1`. Establish `h2' : ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ m, f m ∂μb = (C2 : ℝ≥0∞) * ∫⁻ ζ : ℂ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) * ∫⁻ p : Mt k r × Mt k r, f (mulM (mulM (invM p.1, embF k r (secF k r z z' μsec ζ)), p.2)) ∂(μW.prod μW')` using `h2`. Establish `e` using `engine (μG := μG) (μN := μN) (μb := μb) (μW := μW) (μW' := μW') (Tz k r z) (Tz k r z') (bc1 k r) big_cell_coordinate_measurable (fun ζ => embF k r (secF k r z z' μsec ζ)) (embS_meas hsm) C1 C2 h1' h2' (fun c ζ f hf => key UF hD.haarW hD.haarW' (hConj k r z μN hD.z_mem hD.T_pos hD …`. Rewrite using `[e]`.

Use `congrArg (((C1 * C2 : ℝ≥0) : ℝ≥0∞) * ·) ?_` and prove the remaining obligations. Use `lintegral_congr_ae ?_` and prove the remaining obligations. Establish `hae : ∀ᵐ q : (Fin r → ℂ) × ℂ, q.2 ∈ Om k r z z' ∨ zWeight k (Tz k r z) (Tz k r z') q.2 = 0`. Rewrite using `[Measure.volume_eq_prod]`. Conclude with `(Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Fin r → ℂ))) (ν := (volume : Measure ℂ))).ae (ae_Om z z')`.

Use `filter_upwards [hae] with q hq`. Rewrite using `[hWF k r (Tz k r z) (Tz k r z') q]`. Break down `hq with h | h` into its components or cases. Use `congrArg (ENNReal.ofReal (cWeight k r q.1 * zWeight k (Tz k r z) (Tz k r z') q.2) * ·) ?_` and prove the remaining obligations. Use `lintegral_congr fun p => congrArg f ?_` and prove the remaining obligations.

Establish `e3 : (bigCell k r q.1 (μsec q.2) : Mt k r) = mulM (bc1 k r q.1, embF k r (secF k r z z' μsec q.2))`. Rewrite using `[secF_on h]`. Conclude with `(hBCF k r q.1 (μsec q.2)).1`. Rewrite using `[sgs_eq, e3]`. Rewrite using `[h]`.

Simplify using the standard rewrite rules.
-/
theorem integration_formula_of_parts : Formalism.FourierDecayAlt.B2.AssembleInt := by
  intro hIter hR1 hConj hWbE hBCF UF hWF k r z z' μsec μG μW μN μW' hD
  obtain ⟨μb, hb⟩ := hWbE k r
  have hsec' := secF_section hD.sec
  have hsm := secF_meas hD.sec
  have := haar_sigmaFinite hD.haarW
  have := haar_sigmaFinite hD.haarW'
  have := haar_sigmaFinite hD.haarN
  have := haar_sigmaFinite hb
  obtain ⟨C1, hC1, h1⟩ := hIter k r μG μN μb hD.haarG hD.haarN hb
  obtain ⟨C2, hC2, h2⟩ := hR1 k r z z' (secF k r z z' μsec) μb μW μW' hD.k_pos hD.z_mem hD.z'_mem hD.T_pos hD.T'_pos
    hsec' hb hD.haarW hD.haarW'
  refine ⟨C1 * C2, mul_pos hC1 hC2, fun f hf => ?_⟩
  have h1' : ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ g, f g ∂μG = (C1 : ℝ≥0∞) * ∫⁻ c : Fin r → ℂ,
      ENNReal.ofReal (cWeight k r c) * ∫⁻ p : (Mt k r × Mt k r) × Mt k r,
        f (mulM (mulM (mulM (invM p.1.1, bc1 k r c), p.2), p.1.2)) ∂((μN.prod μN).prod μb) := h1
  have h2' : ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ m, f m ∂μb = (C2 : ℝ≥0∞) * ∫⁻ ζ : ℂ,
      ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) * ∫⁻ p : Mt k r × Mt k r,
        f (mulM (mulM (invM p.1, embF k r (secF k r z z' μsec ζ)), p.2)) ∂(μW.prod μW') := h2
  have e := engine (μG := μG) (μN := μN) (μb := μb) (μW := μW) (μW' := μW') (Tz k r z) (Tz k r z') (bc1 k r) big_cell_coordinate_measurable
    (fun ζ => embF k r (secF k r z z' μsec ζ)) (embS_meas hsm) C1 C2 h1' h2'
    (fun c ζ f hf => key UF hD.haarW hD.haarW' (hConj k r z μN hD.z_mem hD.T_pos hD.haarN)
      (hConj k r z' μN hD.z'_mem hD.T'_pos hD.haarN) (bc1 k r c) _ ((UF k r).2.2 c) f hf) f hf
  rw [e]
  refine congrArg (((C1 * C2 : ℝ≥0) : ℝ≥0∞) * ·) ?_
  refine lintegral_congr_ae ?_
  have hae : ∀ᵐ q : (Fin r → ℂ) × ℂ, q.2 ∈ Om k r z z' ∨ zWeight k (Tz k r z) (Tz k r z') q.2 = 0 := by
    rw [Measure.volume_eq_prod]
    exact (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Fin r → ℂ))) (ν := (volume : Measure ℂ))).ae
      (ae_Om z z')
  filter_upwards [hae] with q hq
  rw [hWF k r (Tz k r z) (Tz k r z') q]
  rcases hq with h | h
  · refine congrArg (ENNReal.ofReal (cWeight k r q.1 * zWeight k (Tz k r z) (Tz k r z') q.2) * ·) ?_
    refine lintegral_congr fun p => congrArg f ?_
    have e3 : (bigCell k r q.1 (μsec q.2) : Mt k r) = mulM (bc1 k r q.1, embF k r (secF k r z z' μsec q.2)) := by
      rw [secF_on h]; exact (hBCF k r q.1 (μsec q.2)).1
    rw [sgs_eq, e3]
  · rw [h]; simp

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.RankOneEmbeddings.Nm

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Apply `h0` to reduce the goal to its premises. Rewrite using `[← Measure.measure_univ_eq_zero, ← iUnion_compactCovering]`. Conclude with `measure_iUnion_null fun n => hcon _ (isCompact_compactCovering _ n)`.
-/
theorem exists_pos {k r : ℕ} (μ : Measure (Mt k r)) (h0 : μ ≠ 0) : ∃ K : Set (Mt k r), IsCompact K ∧ μ K ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  apply h0
  rw [← Measure.measure_univ_eq_zero, ← iUnion_compactCovering]
  exact measure_iUnion_null fun n => hcon _ (isCompact_compactCovering _ n)

end Formalism.FourierDecayAlt.P.RankOneEmbeddings.Nm

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

/- English proof (translation)
Introduce `hC k r z z' μsec μG μW μN μW' hD`. Take `⟨C, hC0, hCf⟩` from `hC k r z z' μsec μG μW μN μW' hD`. Establish `hG` using `hD.haarG`. Take `⟨K, hKc, hK0⟩` from `Formalism.FourierDecayAlt.P.RankOneEmbeddings.Nm.exists_pos μG hG.ne_zero`. Establish `hKfin : μG K < ∞` using `hG.finite_compact K hKc`.

Establish `hKm : MeasurableSet K` using `hKc.isClosed.measurableSet`. Establish `hCne : (C : ℝ≥0∞) ≠ 0` using `by exact_mod_cast hC0.ne'`. Use `⟨C⁻¹, ⟨inv_pos.2 hC0, fun f hf => ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[lintegral_smul_measure, hCf f hf] show ((C⁻¹ : ℝ≥0) : ℝ≥0∞) * _ = _`. Rewrite using `[← mul_assoc, ENNReal.coe_inv hC0.ne', ENNReal.inv_mul_cancel hCne ENNReal.coe_ne_top, one_mul]`.

Introduce and unpack `c ⟨hc0, hcF⟩`. Establish `hmeas : Measurable (K.indicator (1 : Mt k r → ℝ≥0∞))` using `measurable_one.indicator hKm`. Establish `h1` using `hcF _ hmeas`. Establish `h2` using `hCf _ hmeas`. Rewrite `h1` using `[lintegral_smul_measure, lintegral_indicator_one hKm]`.

Rewrite `h2` using `[lintegral_indicator_one hKm]`. Rewrite `h1` using `[h2]`. Establish `key : ∀ X : ℝ≥0∞, μG K = (C : ℝ≥0∞) * X → c • ((C : ℝ≥0∞) * X) = X → c = C⁻¹`. Introduce `X hX hcX`. Establish `hcX' : (c : ℝ≥0∞) * ((C : ℝ≥0∞) * X) = X` using `hcX`.

Establish `hX0 : X ≠ 0`. Introduce and unpack `rfl`. Rewrite `hX` using `[mul_zero]`. Conclude with `hK0 hX`. Establish `hXt : X ≠ ∞`.

Introduce and unpack `rfl`. Rewrite `hX` using `[ENNReal.mul_top hCne]`. Conclude with `hKfin.ne hX`. Establish `hcC : (c : ℝ≥0∞) * C = 1`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[ENNReal.mul_inv_cancel hX0 hXt, mul_one]`. Use `_ = ((c : ℝ≥0∞) * (C * X)) * X⁻¹ := by ring`. Use `_ = X * X⁻¹ := by rw [hcX']`. Use `_ = 1 := ENNReal.mul_inv_cancel hX0 hXt`. Establish `hcC' : c * C = 1` using `by exact_mod_cast hcC`.

Conclude with `eq_inv_of_mul_eq_one_left hcC'`. Conclude with `key _ h2 h1`.
-/
theorem integral_normalisation_from_constant : Formalism.FourierDecayAlt.B2.IntNormFromConst := by
  intro hC k r z z' μsec μG μW μN μW' hD
  obtain ⟨C, hC0, hCf⟩ := hC k r z z' μsec μG μW μN μW' hD
  have hG := hD.haarG
  obtain ⟨K, hKc, hK0⟩ := Formalism.FourierDecayAlt.P.RankOneEmbeddings.Nm.exists_pos μG hG.ne_zero
  have hKfin : μG K < ∞ := hG.finite_compact K hKc
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hCne : (C : ℝ≥0∞) ≠ 0 := by exact_mod_cast hC0.ne'
  refine ⟨C⁻¹, ⟨inv_pos.2 hC0, fun f hf => ?_⟩, ?_⟩
  · rw [lintegral_smul_measure, hCf f hf]
    show ((C⁻¹ : ℝ≥0) : ℝ≥0∞) * _ = _
    rw [← mul_assoc, ENNReal.coe_inv hC0.ne', ENNReal.inv_mul_cancel hCne ENNReal.coe_ne_top, one_mul]
  · rintro c ⟨hc0, hcF⟩
    have hmeas : Measurable (K.indicator (1 : Mt k r → ℝ≥0∞)) := measurable_one.indicator hKm
    have h1 := hcF _ hmeas
    have h2 := hCf _ hmeas
    rw [lintegral_smul_measure, lintegral_indicator_one hKm] at h1
    rw [lintegral_indicator_one hKm] at h2
    rw [h2] at h1
    have key : ∀ X : ℝ≥0∞, μG K = (C : ℝ≥0∞) * X → c • ((C : ℝ≥0∞) * X) = X → c = C⁻¹ := by
      intro X hX hcX
      have hcX' : (c : ℝ≥0∞) * ((C : ℝ≥0∞) * X) = X := hcX
      have hX0 : X ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hX
        exact hK0 hX
      have hXt : X ≠ ∞ := by
        rintro rfl
        rw [ENNReal.mul_top hCne] at hX
        exact hKfin.ne hX
      have hcC : (c : ℝ≥0∞) * C = 1 := by
        calc (c : ℝ≥0∞) * C = (c : ℝ≥0∞) * C * (X * X⁻¹) := by
              rw [ENNReal.mul_inv_cancel hX0 hXt, mul_one]
          _ = ((c : ℝ≥0∞) * (C * X)) * X⁻¹ := by ring
          _ = X * X⁻¹ := by rw [hcX']
          _ = 1 := ENNReal.mul_inv_cancel hX0 hXt
      have hcC' : c * C = 1 := by exact_mod_cast hcC
      exact eq_inv_of_mul_eq_one_left hcC'
    exact key _ h2 h1

end Formalism.FourierDecayAlt.P
