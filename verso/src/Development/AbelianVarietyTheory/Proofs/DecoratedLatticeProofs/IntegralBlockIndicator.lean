import Mathlib
open MeasureTheory Classical

namespace GlobalTheory.BlockFubini

/- English proof (translation)
Set `σ : {i // Q i} ⊕ {i // R i} ≃ {i // P i}` to `{ toFun := Sum.elim (fun a => ⟨a.1, hQ _ a.2⟩) (fun a => ⟨a.1, ((hR _).1 a.2).1⟩) invFun := fun a => if h : Q a.1 then Sum.inl ⟨a.1, h⟩ else Sum.inr ⟨a.1, (hR _).2 ⟨a.2, h⟩⟩ left_inv := by`. Introduce and unpack `(a | a)`. Simplify using `[a.2]`. Simplify using `[((hR _).1 a.2).2]`. Use `right_inv := by`.

Introduce `a`. Apply the tactic sequence `by_cases h : Q a.1 <;> simp [h] }`. Establish `h1` using `measurePreserving_piCongrLeft (α := fun _ : {i // P i} => k) (fun _ => ν) σ`. Establish `h2` using `measurePreserving_sumPiEquivProdPi_symm (X := fun _ : {i // Q i} ⊕ {i // R i} => k) (fun _ => ν)`. Establish `h3` using `h1.comp h2`.

Rewrite using `[← h3.integral_comp ((MeasurableEquiv.measurableEmbedding _).comp (MeasurableEquiv.measurableEmbedding _))]`. Establish `key : ∀ z : ({i // Q i} → k) × ({i // R i} → k), G (fun i => if h : P i then ((MeasurableEquiv.piCongrLeft (fun _ : {i // P i} => k) σ) ∘ (MeasurableEquiv.sumPiEquivProdPi (fun _ : {i // Q i} ⊕ {i // R i} => k)).symm) z ⟨i, h⟩ else 0) = (Set.pi Set.univ (fun _ : {i // Q i} => s)) …`. Introduce `z`. Use `set E := ((MeasurableEquiv.piCongrLeft (fun _ : {i // P i} => k) σ) ∘ (MeasurableEquiv.sumPiEquivProdPi (fun _ : {i // Q i} ⊕ {i // R i} => k)).symm) z with hE`. Establish `e0 : ∀ a, E (σ a) = Sum.elim z.1 z.2 a`.

Introduce `a`. Rewrite using `[hE]`. Simplify using `only [Function.comp_apply]`. Rewrite using `[MeasurableEquiv.piCongrLeft_apply_apply]`. Apply the tactic sequence `cases a <;> rfl`.

Establish `e1 : ∀ i (h : Q i), E ⟨i, hQ i h⟩ = z.1 ⟨i, h⟩` using `fun i h => e0 (Sum.inl ⟨i, h⟩)`. Establish `e2 : ∀ i (h : R i), E ⟨i, ((hR i).1 h).1⟩ = z.2 ⟨i, h⟩` using `fun i h => e0 (Sum.inr ⟨i, h⟩)`. Rewrite using `[hG]`. Use `congr 1`. Rewrite using `[Set.indicator_apply]`.

Use `congr 1`. Apply `propext` to reduce the goal to its premises. Simplify using `only [Set.mem_pi, Set.mem_univ, forall_true_left]`. Prove the components needed by the constructor for the conclusion. Introduce `h a`.

Use `h a.1 a.2` as an intermediate fact. Rewrite `this` using `[dif_pos (hQ _ a.2), e1 _ a.2]`. Then use the resulting hypothesis. Introduce `h i hi`. Rewrite using `[dif_pos (hQ _ hi), e1 _ hi]`. Conclude with `h _`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hq : Q i`. Establish `: ¬ R i` using `fun h => ((hR i).1 h).2 hq`. Simplify using `[hq, this]`.

Distinguish the cases in `hp : P i`. Establish `: R i` using `(hR i).2 ⟨hp, hq⟩`. Simplify using `only [hq, if_false, dif_pos hp, dif_pos this]`. Conclude with `e2 i this`. Establish `: ¬ R i` using `fun h => hp ((hR i).1 h).1`.

Simplify using `[hq, hp, this]`. Repeatedly rewrite using `[key]`. Rewrite using `[integral_prod_mul (fun x => (Set.pi Set.univ (fun _ : {i // Q i} => s)).indicator (fun _ => (1:ℂ)) x) (fun y : {i // R i} → k => G (fun i => if h : R i then y ⟨i, h⟩ else 0))]`. Use `congr 1`. Rewrite using `[integral_indicator_const _ (MeasurableSet.univ_pi fun _ => hs)]`.

Simplify using `[Measure.real, Measure.pi_pi]`.
-/
theorem integral_block_indicator (k : Type) [MeasurableSpace k] [Zero k] (ν : Measure k) [SigmaFinite ν] (I : Type) [Fintype I] (P Q R : I → Prop) [DecidablePred P] [DecidablePred Q] [DecidablePred R] (hR : ∀ i, R i ↔ P i ∧ ¬ Q i) (hQ : ∀ i, Q i → P i) (s : Set k) (hs : MeasurableSet s) (_hν : ν s ≠ ⊤) (G : (I → k) → ℂ) (hG : ∀ m : I → k, G m = (if ∀ i, Q i → m i ∈ s then (1 : ℂ) else 0) * G (fun i => if Q i then 0 else m i)) : ∫ e : {i // P i} → k, G (fun i => if h : P i then e ⟨i, h⟩ else 0) ∂(Measure.pi fun _ => ν) = (((ν s).toReal ^ Fintype.card {i // Q i} : ℝ) : ℂ) * ∫ e : {i // R i} → k, G (fun i => if h : R i then e ⟨i, h⟩ else 0) ∂(Measure.pi fun _ => ν) := by
  let σ : {i // Q i} ⊕ {i // R i} ≃ {i // P i} :=
    { toFun := Sum.elim (fun a => ⟨a.1, hQ _ a.2⟩) (fun a => ⟨a.1, ((hR _).1 a.2).1⟩)
      invFun := fun a => if h : Q a.1 then Sum.inl ⟨a.1, h⟩ else Sum.inr ⟨a.1, (hR _).2 ⟨a.2, h⟩⟩
      left_inv := by
        rintro (a | a)
        · simp [a.2]
        · simp [((hR _).1 a.2).2]
      right_inv := by
        intro a
        by_cases h : Q a.1 <;> simp [h] }
  have h1 := measurePreserving_piCongrLeft (α := fun _ : {i // P i} => k) (fun _ => ν) σ
  have h2 := measurePreserving_sumPiEquivProdPi_symm (X := fun _ : {i // Q i} ⊕ {i // R i} => k) (fun _ => ν)
  have h3 := h1.comp h2
  rw [← h3.integral_comp ((MeasurableEquiv.measurableEmbedding _).comp (MeasurableEquiv.measurableEmbedding _))]
  have key : ∀ z : ({i // Q i} → k) × ({i // R i} → k),
      G (fun i => if h : P i then ((MeasurableEquiv.piCongrLeft (fun _ : {i // P i} => k) σ) ∘ (MeasurableEquiv.sumPiEquivProdPi (fun _ : {i // Q i} ⊕ {i // R i} => k)).symm) z ⟨i, h⟩ else 0)
      = (Set.pi Set.univ (fun _ : {i // Q i} => s)).indicator (fun _ => (1:ℂ)) z.1 * G (fun i => if h : R i then z.2 ⟨i, h⟩ else 0) := by
    intro z
    set E := ((MeasurableEquiv.piCongrLeft (fun _ : {i // P i} => k) σ) ∘ (MeasurableEquiv.sumPiEquivProdPi (fun _ : {i // Q i} ⊕ {i // R i} => k)).symm) z with hE
    have e0 : ∀ a, E (σ a) = Sum.elim z.1 z.2 a := by
      intro a
      rw [hE]
      simp only [Function.comp_apply]
      rw [MeasurableEquiv.piCongrLeft_apply_apply]
      cases a <;> rfl
    have e1 : ∀ i (h : Q i), E ⟨i, hQ i h⟩ = z.1 ⟨i, h⟩ := fun i h => e0 (Sum.inl ⟨i, h⟩)
    have e2 : ∀ i (h : R i), E ⟨i, ((hR i).1 h).1⟩ = z.2 ⟨i, h⟩ := fun i h => e0 (Sum.inr ⟨i, h⟩)
    rw [hG]
    congr 1
    · rw [Set.indicator_apply]
      congr 1
      apply propext
      simp only [Set.mem_pi, Set.mem_univ, forall_true_left]
      constructor
      · intro h a
        have := h a.1 a.2
        rwa [dif_pos (hQ _ a.2), e1 _ a.2] at this
      · intro h i hi
        rw [dif_pos (hQ _ hi), e1 _ hi]
        exact h _
    · congr 1
      funext i
      by_cases hq : Q i
      · have : ¬ R i := fun h => ((hR i).1 h).2 hq
        simp [hq, this]
      · by_cases hp : P i
        · have : R i := (hR i).2 ⟨hp, hq⟩
          simp only [hq, if_false, dif_pos hp, dif_pos this]
          exact e2 i this
        · have : ¬ R i := fun h => hp ((hR i).1 h).1
          simp [hq, hp, this]
  simp_rw [key]
  rw [integral_prod_mul (fun x => (Set.pi Set.univ (fun _ : {i // Q i} => s)).indicator (fun _ => (1:ℂ)) x) (fun y : {i // R i} → k => G (fun i => if h : R i then y ⟨i, h⟩ else 0))]
  congr 1
  rw [integral_indicator_const _ (MeasurableSet.univ_pi fun _ => hs)]
  simp [Measure.real, Measure.pi_pi]

end GlobalTheory.BlockFubini
