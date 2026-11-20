import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap

open Matrix MeasureTheory Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm
open scoped ContDiff InnerProductSpace ComplexConjugate

noncomputable section

namespace CompanionTheory.Bmu

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {Hm : Mat n} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mat n → (H →L[ℂ] H)} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/- English proof (translation)
Introduce `X hX t` and use `ex_mem_of_lie (h X hX) t`.
-/
theorem LieWd.lieW {W : List (Mat n)} (h : LieWd Hm W) : LieW (UH Hm) W := fun X hX t => ex_mem_of_lie (h X hX) t

/- English proof (translation)
Use `⟨fun x hx x' hx' => ?_, fun a x hx => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, hB.add _ (hx.apply hU.rep hy) _ (hx'.apply hU.rep hy)]`. Rewrite using `[map_smul, hB.smul _ _ (hx.apply hU.rep hy)]`. Take `⟨C, Ws, hWs, hb⟩` from `hB.bd`. Use `⟨C, Ws.map fun W => W.map fun X => y⁻¹ * X * y, fun W hW => ?_, fun v hv => ?_⟩` and prove the remaining obligations.

Take `⟨W', hW', rfl⟩` from `List.mem_map.1 hW`. Conclude with `(hAd n Hm H σ hU y hy W' (hWs W' hW')).1`. Use `(hb _ (hv.apply hU.rep hy)).trans_eq ?_` and prove the remaining obligations. Rewrite using `[List.map_map]`. Use `congr 2`.

Use `List.map_congr_left fun W hW => ?_` and prove the remaining obligations. Rewrite using `[(hAd n Hm H σ hU y hy W (hWs W hW)).2 v hv, hU.iso y hy]`. Both sides reduce to the same expression.
-/
theorem CWLin.comp_sigma (hAd : DsAd) (hU : URep Hm σ) {B : H → V} (hB : CWLin Hm σ B) {y : Mat n}
    (hy : y ∈ UH Hm) : CWLin Hm σ (fun v => B (σ y v)) := by
  refine ⟨fun x hx x' hx' => ?_, fun a x hx => ?_, ?_⟩
  · rw [map_add, hB.add _ (hx.apply hU.rep hy) _ (hx'.apply hU.rep hy)]
  · rw [map_smul, hB.smul _ _ (hx.apply hU.rep hy)]
  · obtain ⟨C, Ws, hWs, hb⟩ := hB.bd
    refine ⟨C, Ws.map fun W => W.map fun X => y⁻¹ * X * y, fun W hW => ?_, fun v hv => ?_⟩
    · obtain ⟨W', hW', rfl⟩ := List.mem_map.1 hW
      exact (hAd n Hm H σ hU y hy W' (hWs W' hW')).1
    · refine (hb _ (hv.apply hU.rep hy)).trans_eq ?_
      rw [List.map_map]
      congr 2
      refine List.map_congr_left fun W hW => ?_
      rw [(hAd n Hm H σ hU y hy W (hWs W hW)).2 v hv, hU.iso y hy]
      rfl

omit [CompleteSpace H] in
/- English proof (translation)
Use `⟨fun x hx x' hx' => ?_, fun c x hx => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[h₁.add _ hx _ hx', h₂.add _ hx _ hx', smul_add, smul_add]`. Normalize the expressions using the abelian group laws. Rewrite using `[h₁.smul _ _ hx, h₂.smul _ _ hx, smul_add, smul_comm a c, smul_comm b c]`. Take `⟨C₁, W₁, hW₁, hb₁⟩` from `h₁.bd`.

Take `⟨C₂, W₂, hW₂, hb₂⟩` from `h₂.bd`. Use `⟨‖a‖ * |C₁| + ‖b‖ * |C₂|, W₁ ++ W₂, fun W hW => (List.mem_append.1 hW).elim (hW₁ W) (hW₂ W), fun v hv => ?_⟩` and prove the remaining obligations. Rewrite using `[List.map_append, List.sum_append]`. Use `set s₁ := (W₁.map fun W => ‖dsW σ W v‖).sum`. Use `set s₂ := (W₂.map fun W => ‖dsW σ W v‖).sum`.

Establish `p₁ : 0 ≤ s₁` using `List.sum_nonneg fun x hx => by`. Take `⟨W, -, rfl⟩` from `List.mem_map.1 hx`. Conclude with `norm_nonneg _`. Establish `p₂ : 0 ≤ s₂` using `List.sum_nonneg fun x hx => by`. Take `⟨W, -, rfl⟩` from `List.mem_map.1 hx`.

Conclude with `norm_nonneg _`. Establish `q₁ : ‖B₁ v‖ ≤ |C₁| * s₁` using `(hb₁ v hv).trans (mul_le_mul_of_nonneg_right (le_abs_self _) p₁)`. Establish `q₂ : ‖B₂ v‖ ≤ |C₂| * s₂` using `(hb₂ v hv).trans (mul_le_mul_of_nonneg_right (le_abs_self _) p₂)`. Establish `r₁` using `mul_le_mul_of_nonneg_left q₁ (norm_nonneg a)`. Establish `r₂` using `mul_le_mul_of_nonneg_left q₂ (norm_nonneg b)`.

Establish `t₁ : 0 ≤ ‖a‖ * |C₁| * s₂` using `by positivity`. Establish `t₂ : 0 ≤ ‖b‖ * |C₂| * s₁` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← norm_smul, ← norm_smul]`. Conclude with `norm_add_le _ _`.

Use `_ ≤ _ := by nlinarith`.
-/
theorem CWLin.comb {B₁ B₂ : H → V} (h₁ : CWLin Hm σ B₁) (h₂ : CWLin Hm σ B₂) (a b : ℂ) :
    CWLin Hm σ (fun v => a • B₁ v + b • B₂ v) := by
  refine ⟨fun x hx x' hx' => ?_, fun c x hx => ?_, ?_⟩
  · rw [h₁.add _ hx _ hx', h₂.add _ hx _ hx', smul_add, smul_add]; abel
  · rw [h₁.smul _ _ hx, h₂.smul _ _ hx, smul_add, smul_comm a c, smul_comm b c]
  · obtain ⟨C₁, W₁, hW₁, hb₁⟩ := h₁.bd
    obtain ⟨C₂, W₂, hW₂, hb₂⟩ := h₂.bd
    refine ⟨‖a‖ * |C₁| + ‖b‖ * |C₂|, W₁ ++ W₂, fun W hW => (List.mem_append.1 hW).elim (hW₁ W) (hW₂ W),
      fun v hv => ?_⟩
    rw [List.map_append, List.sum_append]
    set s₁ := (W₁.map fun W => ‖dsW σ W v‖).sum
    set s₂ := (W₂.map fun W => ‖dsW σ W v‖).sum
    have p₁ : 0 ≤ s₁ := List.sum_nonneg fun x hx => by
      obtain ⟨W, -, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _
    have p₂ : 0 ≤ s₂ := List.sum_nonneg fun x hx => by
      obtain ⟨W, -, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _
    have q₁ : ‖B₁ v‖ ≤ |C₁| * s₁ := (hb₁ v hv).trans (mul_le_mul_of_nonneg_right (le_abs_self _) p₁)
    have q₂ : ‖B₂ v‖ ≤ |C₂| * s₂ := (hb₂ v hv).trans (mul_le_mul_of_nonneg_right (le_abs_self _) p₂)
    have r₁ := mul_le_mul_of_nonneg_left q₁ (norm_nonneg a)
    have r₂ := mul_le_mul_of_nonneg_left q₂ (norm_nonneg b)
    have t₁ : 0 ≤ ‖a‖ * |C₁| * s₂ := by positivity
    have t₂ : 0 ≤ ‖b‖ * |C₂| * s₁ := by positivity
    calc ‖a • B₁ v + b • B₂ v‖ ≤ ‖a‖ * ‖B₁ v‖ + ‖b‖ * ‖B₂ v‖ := by
          rw [← norm_smul, ← norm_smul]; exact norm_add_le _ _
      _ ≤ _ := by nlinarith

omit [CompleteSpace H] in
/- English proof (translation)
Simplify using `using hB.smul 0 0 IsSm.zero`.
-/
theorem CWLin.zero {B : H → V} (hB : CWLin Hm σ B) : B 0 = 0 := by
  simpa using hB.smul 0 0 IsSm.zero

omit [CompleteSpace H] in
/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using ⟨IsSm.zero, hB.zero⟩`. Consider the case `insert a s ha ih`. Establish `h1` using `hw.apply hU.rep (hg a)`. Rewrite using `[Finset.sum_insert ha]`.

Conclude with `⟨(h1.smul _).add ih.1, by rw [hB.add _ (h1.smul _) _ ih.1, hB.smul _ _ h1, h0 _ (hg a), ih.2]; simp⟩`.
-/
theorem CWLin.sum_orbit (hU : URep Hm σ) {B : H → V} (hB : CWLin Hm σ B) {w : H} (hw : IsSm (UH Hm) σ w)
    (h0 : ∀ g ∈ UH Hm, B (σ g w) = 0) {ι : Type} (s : Finset ι) (c : ι → ℂ) (g : ι → Mat n)
    (hg : ∀ i, g i ∈ UH Hm) : IsSm (UH Hm) σ (∑ i ∈ s, c i • σ (g i) w) ∧ B (∑ i ∈ s, c i • σ (g i) w) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ⟨IsSm.zero, hB.zero⟩
  | insert a s ha ih =>
    have h1 := hw.apply hU.rep (hg a)
    rw [Finset.sum_insert ha]
    exact ⟨(h1.smul _).add ih.1, by rw [hB.add _ (h1.smul _) _ ih.1, hB.smul _ _ h1, h0 _ (hg a), ih.2]; simp⟩

omit [CompleteSpace H] in

/- English proof (translation)
Take `⟨C, Ws, hWs, hb⟩` from `hB.bd`. Rewrite using `[← norm_le_zero_iff]`. Use `le_of_forall_pos_le_add fun δ hδ => ?_` and prove the remaining obligations. Establish `hC : 0 < |C| + 1` using `by positivity`. Take `⟨N, c, g, hg, hs⟩` from `happ Ws hWs (δ / (|C| + 1)) (div_pos hδ hC)`.

Take `⟨hy, hBy⟩` from `hB.sum_orbit hU hw h0 Finset.univ c g hg`. Establish `e : B x = B (x - ∑ i, c i • σ (g i) w)`. Use `hB.add _ (hx.sub hy) _ hy` as an intermediate fact. Rewrite `this` using `[sub_add_cancel, hBy, add_zero]`. Conclude with `this`.

Establish `p : 0 ≤ (Ws.map fun W => ‖dsW σ W (x - ∑ i, c i • σ (g i) w)‖).sum` using `List.sum_nonneg fun t ht => by`. Take `⟨W, -, rfl⟩` from `List.mem_map.1 ht`. Conclude with `norm_nonneg _`. Rewrite using `[e, zero_add]`. Use `(hb _ (hx.sub hy)).trans ?_` and prove the remaining obligations.

Rewrite `hs` using `[lt_div_iff₀ hC]`. Use polynomial arithmetic with `[le_abs_self C]`.
-/
theorem CWLin.eq_zero (hU : URep Hm σ) {B : H → V} (hB : CWLin Hm σ B) {w : H} (hw : IsSm (UH Hm) σ w)
    (h0 : ∀ g ∈ UH Hm, B (σ g w) = 0) {x : H} (hx : IsSm (UH Hm) σ x)
    (happ : ∀ Ws : List (List (Mat n)), (∀ W ∈ Ws, LieWd Hm W) → ∀ δ : ℝ, 0 < δ →
      ∃ (N : ℕ) (c : Fin N → ℂ) (g : Fin N → Mat n), (∀ i, g i ∈ UH Hm) ∧
        (Ws.map fun W => ‖dsW σ W (x - ∑ i, c i • σ (g i) w)‖).sum < δ) : B x = 0 := by
  obtain ⟨C, Ws, hWs, hb⟩ := hB.bd
  rw [← norm_le_zero_iff]
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hC : 0 < |C| + 1 := by positivity
  obtain ⟨N, c, g, hg, hs⟩ := happ Ws hWs (δ / (|C| + 1)) (div_pos hδ hC)
  obtain ⟨hy, hBy⟩ := hB.sum_orbit hU hw h0 Finset.univ c g hg
  have e : B x = B (x - ∑ i, c i • σ (g i) w) := by
    have := hB.add _ (hx.sub hy) _ hy
    rw [sub_add_cancel, hBy, add_zero] at this
    exact this
  have p : 0 ≤ (Ws.map fun W => ‖dsW σ W (x - ∑ i, c i • σ (g i) w)‖).sum := List.sum_nonneg fun t ht => by
    obtain ⟨W, -, rfl⟩ := List.mem_map.1 ht; exact norm_nonneg _
  rw [e, zero_add]
  refine (hb _ (hx.sub hy)).trans ?_
  rw [lt_div_iff₀ hC] at hs
  nlinarith [le_abs_self C]

/- English proof (translation)
Take `⟨N, W, β, hW, hβ⟩` from `hF n Hm H σ hU V B hB`. Use `(continuousOn_finset_sum Finset.univ fun i _ => (β i).continuous.comp_continuousOn (continuousOn_dsW_orbit hU.rep hw (hW i).lieW)).congr fun g hg => ?_` and prove the remaining obligations. Conclude with `hβ _ (hw.apply hU.rep hg)`.
-/
theorem CWLin.continuousOn_orbit [FiniteDimensional ℂ V] (hF : Factor) (hU : URep Hm σ) {B : H → V}
    (hB : CWLin Hm σ B) {w : H} (hw : IsSm (UH Hm) σ w) : ContinuousOn (fun g => B (σ g w)) (UH Hm) := by
  obtain ⟨N, W, β, hW, hβ⟩ := hF n Hm H σ hU V B hB
  refine (continuousOn_finset_sum Finset.univ fun i _ =>
    (β i).continuous.comp_continuousOn (continuousOn_dsW_orbit hU.rep hw (hW i).lieW)).congr fun g hg => ?_
  exact hβ _ (hw.apply hU.rep hg)

end CompanionTheory.Bmu
