import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

open Matrix MeasureTheory Filter Topology in
/- English proof (translation)
Apply `hψ.1` to reduce the goal to its premises. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem addChar_dotProduct_eq_one_of_norm_le {F : Type} [NontriviallyNormedField F]
    [IsUltrametricDist F] {ψ : AddChar F ℂ} (hψ : _root_.GlobalTheory.JR.IsStdChar ψ) {r : ℕ}
    {R : ℝ} (x δ : Fin r → F) (hx : ‖x‖ ≤ R) (hδ : ‖δ‖ * R ≤ 1) : ψ (x ⬝ᵥ δ) = 1 := by
  apply hψ.1
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
  rw [norm_mul]
  calc ‖x i‖ * ‖δ i‖ ≤ R * ‖δ‖ :=
        mul_le_mul ((norm_le_pi_norm x i).trans hx) (norm_le_pi_norm δ i) (norm_nonneg _)
          ((norm_nonneg _).trans hx)
    _ = ‖δ‖ * R := mul_comm _ _
    _ ≤ 1 := hδ

open Matrix MeasureTheory Filter Topology in

/- English proof (translation)
Introduce `F E _ _ _ _ _ r M ψ hψ f hf ⟨U, hU, hUf⟩`. Use `haveI := _root_.GlobalTheory.JR.Unram.ultraF (F := F) E`. Take `⟨C, hC⟩` from `hf.2.isCompact.exists_bound_of_continuousOn (f := fun x : _root_.GlobalTheory.JR.Gl r F => (x.2.1, x.2.2.1)) (continuous_snd.fst.prodMk continuous_snd.snd.fst).continuousOn`. Use `set R : ℝ := |C| + 1 with hRdef`. Establish `hRpos : 0 < R` using `by positivity`.

Establish `hCR : C ≤ R` using `(le_abs_self C).trans (by rw [hRdef]; linarith)`. Establish `hbd : ∀ x ∈ tsupport f, ‖x.2.1‖ ≤ R ∧ ‖x.2.2.1‖ ≤ R`. Introduce `x hx`. Establish `h : ‖(x.2.1, x.2.2.1)‖ ≤ C` using `hC x hx`. Conclude with `⟨(norm_fst_le (x.2.1, x.2.2.1)).trans (h.trans hCR), (norm_snd_le (x.2.1, x.2.2.1)).trans (h.trans hCR)⟩`.

Set `P : _root_.GlobalTheory.JR.Gl r F → _root_.GlobalTheory.JR.Gl r F` to `fun u => (u.1, 0, 0, u.2.2.2)`. Establish `hP : Continuous P` using `continuous_fst.prodMk (continuous_const.prodMk (continuous_const.prodMk continuous_snd.snd.snd))`. Establish `hP0 : P 0 = 0` using `rfl`. Use `set W : Set (_root_.GlobalTheory.JR.Gl r F) := P ⁻¹' U ∩ {u | ‖u.2.1‖ < R⁻¹} ∩ {u | ‖u.2.2.1‖ < R⁻¹} with hWdef`. Establish `hW : W ∈ 𝓝 (0 : _root_.GlobalTheory.JR.Gl r F)`.

Use `inter_mem (inter_mem (hP.continuousAt.preimage_mem_nhds (by rwa [hP0])) ?_) ?_` and prove the remaining obligations. Conclude with `(isOpen_lt (continuous_norm.comp continuous_snd.fst) continuous_const).mem_nhds (by simp [hRpos])`. Conclude with `(isOpen_lt (continuous_norm.comp continuous_snd.snd.fst) continuous_const).mem_nhds (by simp [hRpos])`. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `Y`.

Establish `hnb : {Y' | Y' - Y ∈ W} ∈ 𝓝 Y` using `(continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds (by simpa using hW)`. Use `filter_upwards [hnb] with Y' hY'`. Take `⟨⟨hu1, hu2⟩, hu3⟩` from `hY'`. Take `⟨u, rfl⟩ : ∃ u, Y' = Y + u` from `⟨Y' - Y, by abel⟩`. Simplify using `only [add_sub_cancel_left] at hu1 hu2 hu3`.

Unfold `_root_.GlobalTheory.JR.fourG`. Use `congr 1`. Use function extensionality and compare the values at `b'`. Use `congr 1`. Use function extensionality and compare the values at `c'`.

Establish `hfeq : f ((Y + u).1, b', c', (Y + u).2.2.2) = f (Y.1, b', c', Y.2.2.2)`. Use `hUf (Y.1, b', c', Y.2.2.2) (P u) hu1` as an intermediate fact. Use `this using 2` and compare the differences between its conclusion and the goal. Apply the tactic sequence `ext <;> simp [P]`. Rewrite using `[hfeq]`.

Distinguish the cases in `h0 : f (Y.1, b', c', Y.2.2.2) = 0`. Simplify using `[h0]`. Establish `hmem : (Y.1, b', c', Y.2.2.2) ∈ tsupport f` using `subset_tsupport f h0`. Take `⟨hb', hc'⟩` from `hbd _ hmem`. Establish `e1 : ψ (c' ⬝ᵥ u.2.1) = 1` using `addChar_dotProduct_eq_one_of_norm_le hψ c' u.2.1 hc' (by rw [← le_div_iff₀ hRpos, one_div]; exact hu2.le)`.

Establish `e2 : ψ (u.2.2.1 ⬝ᵥ b') = 1`. Rewrite using `[dotProduct_comm]`. Conclude with `addChar_dotProduct_eq_one_of_norm_le hψ b' u.2.2.1 hb' (by rw [← le_div_iff₀ hRpos, one_div]; exact hu3.le)`. Establish `hsum : c' ⬝ᵥ (Y + u).2.1 + (Y + u).2.2.1 ⬝ᵥ b' = (c' ⬝ᵥ Y.2.1 + Y.2.2.1 ⬝ᵥ b') + c' ⬝ᵥ u.2.1 + u.2.2.1 ⬝ᵥ b'`. Simplify using `only [Prod.snd_add, Prod.fst_add, dotProduct_add, add_dotProduct]`.

Normalize the expressions using the abelian group laws. Rewrite using `[hsum, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, e1, e2, mul_one, mul_one]`.
-/
theorem _root_.GlobalTheory.JR.fourG_isLocallyConstant_of_invariant :
    ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
      [_root_.GlobalTheory.JR.Unram F E] (r : ℕ) (M : _root_.GlobalTheory.JR.Meas r F E) (ψ : AddChar F ℂ),
      _root_.GlobalTheory.JR.IsStdChar ψ → ∀ f' : _root_.GlobalTheory.JR.Gl r F → ℂ, _root_.GlobalTheory.JR.IsTest f' →
      (∃ U ∈ 𝓝 (0 : _root_.GlobalTheory.JR.Gl r F), ∀ Y : _root_.GlobalTheory.JR.Gl r F, ∀ u ∈ U, f' (Y + u) = f' Y) →
      IsLocallyConstant (_root_.GlobalTheory.JR.fourG M ψ f') := by
  intro F E _ _ _ _ _ r M ψ hψ f hf ⟨U, hU, hUf⟩
  haveI := _root_.GlobalTheory.JR.Unram.ultraF (F := F) E
  obtain ⟨C, hC⟩ := hf.2.isCompact.exists_bound_of_continuousOn
    (f := fun x : _root_.GlobalTheory.JR.Gl r F => (x.2.1, x.2.2.1))
    (continuous_snd.fst.prodMk continuous_snd.snd.fst).continuousOn
  set R : ℝ := |C| + 1 with hRdef
  have hRpos : 0 < R := by positivity
  have hCR : C ≤ R := (le_abs_self C).trans (by rw [hRdef]; linarith)
  have hbd : ∀ x ∈ tsupport f, ‖x.2.1‖ ≤ R ∧ ‖x.2.2.1‖ ≤ R := by
    intro x hx
    have h : ‖(x.2.1, x.2.2.1)‖ ≤ C := hC x hx
    exact ⟨(norm_fst_le (x.2.1, x.2.2.1)).trans (h.trans hCR),
      (norm_snd_le (x.2.1, x.2.2.1)).trans (h.trans hCR)⟩
  let P : _root_.GlobalTheory.JR.Gl r F → _root_.GlobalTheory.JR.Gl r F := fun u => (u.1, 0, 0, u.2.2.2)
  have hP : Continuous P :=
    continuous_fst.prodMk (continuous_const.prodMk (continuous_const.prodMk continuous_snd.snd.snd))
  have hP0 : P 0 = 0 := rfl
  set W : Set (_root_.GlobalTheory.JR.Gl r F) :=
    P ⁻¹' U ∩ {u | ‖u.2.1‖ < R⁻¹} ∩ {u | ‖u.2.2.1‖ < R⁻¹} with hWdef
  have hW : W ∈ 𝓝 (0 : _root_.GlobalTheory.JR.Gl r F) := by
    refine inter_mem (inter_mem (hP.continuousAt.preimage_mem_nhds (by rwa [hP0])) ?_) ?_
    · exact (isOpen_lt (continuous_norm.comp continuous_snd.fst) continuous_const).mem_nhds
        (by simp [hRpos])
    · exact (isOpen_lt (continuous_norm.comp continuous_snd.snd.fst) continuous_const).mem_nhds
        (by simp [hRpos])
  rw [IsLocallyConstant.iff_eventually_eq]
  intro Y
  have hnb : {Y' | Y' - Y ∈ W} ∈ 𝓝 Y :=
    (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds (by simpa using hW)
  filter_upwards [hnb] with Y' hY'
  obtain ⟨⟨hu1, hu2⟩, hu3⟩ := hY'
  obtain ⟨u, rfl⟩ : ∃ u, Y' = Y + u := ⟨Y' - Y, by abel⟩
  simp only [add_sub_cancel_left] at hu1 hu2 hu3
  unfold _root_.GlobalTheory.JR.fourG
  congr 1; funext b'; congr 1; funext c'
  have hfeq : f ((Y + u).1, b', c', (Y + u).2.2.2) = f (Y.1, b', c', Y.2.2.2) := by
    have := hUf (Y.1, b', c', Y.2.2.2) (P u) hu1
    convert this using 2
    ext <;> simp [P]
  rw [hfeq]
  by_cases h0 : f (Y.1, b', c', Y.2.2.2) = 0
  · simp [h0]
  have hmem : (Y.1, b', c', Y.2.2.2) ∈ tsupport f := subset_tsupport f h0
  obtain ⟨hb', hc'⟩ := hbd _ hmem
  have e1 : ψ (c' ⬝ᵥ u.2.1) = 1 := addChar_dotProduct_eq_one_of_norm_le hψ c' u.2.1 hc'
    (by rw [← le_div_iff₀ hRpos, one_div]; exact hu2.le)
  have e2 : ψ (u.2.2.1 ⬝ᵥ b') = 1 := by
    rw [dotProduct_comm]
    exact addChar_dotProduct_eq_one_of_norm_le hψ b' u.2.2.1 hb'
      (by rw [← le_div_iff₀ hRpos, one_div]; exact hu3.le)
  have hsum : c' ⬝ᵥ (Y + u).2.1 + (Y + u).2.2.1 ⬝ᵥ b' =
      (c' ⬝ᵥ Y.2.1 + Y.2.2.1 ⬝ᵥ b') + c' ⬝ᵥ u.2.1 + u.2.2.1 ⬝ᵥ b' := by
    simp only [Prod.snd_add, Prod.fst_add, dotProduct_add, add_dotProduct]
    abel
  rw [hsum, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, e1, e2, mul_one, mul_one]

end GlobalTheory.JR
