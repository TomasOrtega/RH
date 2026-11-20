import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CompactLocalSets.OverlapG

noncomputable section

open MeasureTheory

namespace PositivityTheory.KB.LocalOverlapAverage

def Yb (H : Type) : Type := H × Bool

instance (H : Type) [Group H] : MulAction H (Yb H) where
  smul h p := ((h * p.1 : H), p.2)
  one_smul p := by
    change ((1 * p.1 : H), p.2) = p
    rw [one_mul]
    rfl
  mul_smul g h p := by
    change ((g * h * p.1 : H), p.2) = ((g * (h * p.1) : H), p.2)
    rw [mul_assoc]

/- English proof (translation)
Establish `h` using `(measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => P) i).integral_comp' (fun p : X × (Fin n → X) => f p.2)`. Rewrite `h` using `[integral_fun_snd]`. Simplify using `only [probReal_univ, one_smul] at h`. Conclude with `h`.
-/
theorem marg {X : Type} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P] {n : ℕ}
    (i : Fin (n + 1)) (f : (Fin n → X) → ℝ) :
    ∫ x, f (fun j => x (i.succAbove j)) ∂(Measure.pi fun _ : Fin (n + 1) => P) =
      ∫ x, f x ∂(Measure.pi fun _ : Fin n => P) := by
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => P) i).integral_comp'
    (fun p : X × (Fin n → X) => f p.2)
  rw [integral_fun_snd] at h
  simp only [probReal_univ, one_smul] at h
  exact h

/- English proof (translation)
Establish `he` using `measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => P) i`. Establish `hφ : Measurable fun x : Fin (n + 1) → X => fun j => x (i.succAbove j)` using `measurable_pi_lambda _ fun j => measurable_pi_apply _`. Establish `hmap : Measure.map (fun x : Fin (n + 1) → X => fun j => x (i.succAbove j)) (Measure.pi fun _ : Fin (n + 1) => P) = Measure.pi fun _ : Fin n => P`. Establish `hcomp : (fun x : Fin (n + 1) → X => fun j => x (i.succAbove j)) = Prod.snd ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) i)`. Use function extensionality and compare the values at `x`.

Both sides reduce to the same expression. Rewrite using `[hcomp, ← Measure.map_map measurable_snd he.measurable, he.map_eq, Measure.map_snd_prod, measure_univ, one_smul]`. Rewrite `hf` using `[← hmap]`. Conclude with `hf.comp_measurable hφ`.
-/
theorem marg_int {X : Type} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P] {n : ℕ}
    (i : Fin (n + 1)) (f : (Fin n → X) → ℝ) (hf : Integrable f (Measure.pi fun _ : Fin n => P)) :
    Integrable (fun x => f (fun j => x (i.succAbove j))) (Measure.pi fun _ : Fin (n + 1) => P) := by
  have he := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => P) i
  have hφ : Measurable fun x : Fin (n + 1) → X => fun j => x (i.succAbove j) :=
    measurable_pi_lambda _ fun j => measurable_pi_apply _
  have hmap : Measure.map (fun x : Fin (n + 1) → X => fun j => x (i.succAbove j))
      (Measure.pi fun _ : Fin (n + 1) => P) = Measure.pi fun _ : Fin n => P := by
    have hcomp : (fun x : Fin (n + 1) → X => fun j => x (i.succAbove j))
        = Prod.snd ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) i) := by
      funext x
      rfl
    rw [hcomp, ← Measure.map_map measurable_snd he.measurable, he.map_eq, Measure.map_snd_prod,
      measure_univ, one_smul]
  rw [← hmap] at hf
  exact hf.comp_measurable hφ

/- English proof (translation)
Introduce `G H Y X _ _ _ _ ρ k F P _ e y₀ hinv hcoc hint z hz`. Set `F' : (Fin (k + 2) → Yb H) → ℝ` to `fun p => ∫ x, F (fun j => (p j).1 • (if (p j).2 = true then e (x j) else y₀)) ∂(Measure.pi fun _ => P)`. Establish `hInv' : Inv ρ F'`. Introduce `g p`. Express the relevant statement in the definitionally equal form `∫ x, F (fun j => (ρ g * (p j).1) • (if (p j).2 = true then e (x j) else y₀)) ∂(Measure.pi fun _ => P) = F' p`.

Simplify using `only [mul_smul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Conclude with `hinv g (fun j => (p j).1 • (if (p j).2 = true then e (x j) else y₀))`. Establish `hcoc' : dC F' = 0`. Use function extensionality and compare the values at `p`.

Set `Q : (Fin (k + 3) → X) → Fin (k + 3) → Y` to `fun x j => (p j).1 • (if (p j).2 = true then e (x j) else y₀)`. Establish `hint' : ∀ i : Fin (k + 3), Integrable (fun x => F (fun j => Q x (i.succAbove j))) (Measure.pi fun _ => P)`. Introduce `i`. Conclude with `marg_int P i _ (hint (fun j => (p (i.succAbove j)).1) (fun j => (p (i.succAbove j)).2))`. Establish `hterm : ∀ i : Fin (k + 3), F' (fun j => p (i.succAbove j)) = ∫ x, F (fun j => Q x (i.succAbove j)) ∂(Measure.pi fun _ => P)` using `fun i => (marg P i _).symm`.

Express the relevant statement in the definitionally equal form `∑ i : Fin (k + 3), (-1 : ℝ) ^ (i : ℕ) * F' (fun j => p (i.succAbove j)) = 0`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hterm i, integral_const_mul]`. Use `_ = ∫ x, ∑ i : Fin (k + 3), (-1 : ℝ) ^ (i : ℕ) * F (fun j => Q x (i.succAbove j)) ∂(Measure.pi fun _ => P) := (integral_finset_sum _ fun i _ => (hint' i).const_mul _).symm`.

Use `_ = ∫ x, dC F (Q x) ∂(Measure.pi fun _ => P) := rfl`. Use `_ = 0 := by simp [hcoc]`. Set `b₀ : Yb H` to `((1 : H), false)`. Set `b₁ : Yb H` to `((1 : H), true)`. Establish `key1 : ∀ q : Fin (k + 2) → H, F' (fun j => q j • b₀) = F (fun j => q j • y₀)`.

Introduce `q`. Express the relevant statement in the definitionally equal form `∫ x, F (fun j => (q j * 1) • (if false = true then e (x j) else y₀)) ∂(Measure.pi fun _ => P) = _`. Simplify using the standard rewrite rules. Establish `key2 : ∀ q : Fin (k + 2) → H, F' (fun j => q j • b₁) = ∫ x, F (fun j => q j • e (x j)) ∂(Measure.pi fun _ => P)`. Introduce `q`.

Express the relevant statement in the definitionally equal form `∫ x, F (fun j => (q j * 1) • (if true = true then e (x j) else y₀)) ∂(Measure.pi fun _ => P) = _`. Simplify using the standard rewrite rules. Establish `h` using `(hEv G H (Yb H) ρ k F' hInv' hcoc').2 b₀ b₁ z hz`. Simplify using `only [ev, key1, key2] at h`. Simplify `h` using `[ev]`.
-/
theorem avgS_of (hEv : SEv) : AvgS := by
  intro G H Y X _ _ _ _ ρ k F P _ e y₀ hinv hcoc hint z hz
  let F' : (Fin (k + 2) → Yb H) → ℝ := fun p =>
    ∫ x, F (fun j => (p j).1 • (if (p j).2 = true then e (x j) else y₀)) ∂(Measure.pi fun _ => P)
  have hInv' : Inv ρ F' := by
    intro g p
    change ∫ x, F (fun j => (ρ g * (p j).1) • (if (p j).2 = true then e (x j) else y₀))
        ∂(Measure.pi fun _ => P) = F' p
    simp only [mul_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact hinv g (fun j => (p j).1 • (if (p j).2 = true then e (x j) else y₀))
  have hcoc' : dC F' = 0 := by
    funext p
    let Q : (Fin (k + 3) → X) → Fin (k + 3) → Y := fun x j =>
      (p j).1 • (if (p j).2 = true then e (x j) else y₀)
    have hint' : ∀ i : Fin (k + 3),
        Integrable (fun x => F (fun j => Q x (i.succAbove j))) (Measure.pi fun _ => P) := by
      intro i
      exact marg_int P i _ (hint (fun j => (p (i.succAbove j)).1) (fun j => (p (i.succAbove j)).2))
    have hterm : ∀ i : Fin (k + 3), F' (fun j => p (i.succAbove j))
        = ∫ x, F (fun j => Q x (i.succAbove j)) ∂(Measure.pi fun _ => P) :=
      fun i => (marg P i _).symm
    change ∑ i : Fin (k + 3), (-1 : ℝ) ^ (i : ℕ) * F' (fun j => p (i.succAbove j)) = 0
    calc ∑ i : Fin (k + 3), (-1 : ℝ) ^ (i : ℕ) * F' (fun j => p (i.succAbove j))
        = ∑ i : Fin (k + 3), ∫ x, (-1 : ℝ) ^ (i : ℕ) * F (fun j => Q x (i.succAbove j))
            ∂(Measure.pi fun _ => P) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hterm i, integral_const_mul]
      _ = ∫ x, ∑ i : Fin (k + 3), (-1 : ℝ) ^ (i : ℕ) * F (fun j => Q x (i.succAbove j))
            ∂(Measure.pi fun _ => P) :=
          (integral_finset_sum _ fun i _ => (hint' i).const_mul _).symm
      _ = ∫ x, dC F (Q x) ∂(Measure.pi fun _ => P) := rfl
      _ = 0 := by simp [hcoc]
  let b₀ : Yb H := ((1 : H), false)
  let b₁ : Yb H := ((1 : H), true)
  have key1 : ∀ q : Fin (k + 2) → H, F' (fun j => q j • b₀) = F (fun j => q j • y₀) := by
    intro q
    change ∫ x, F (fun j => (q j * 1) • (if false = true then e (x j) else y₀))
      ∂(Measure.pi fun _ => P) = _
    simp
  have key2 : ∀ q : Fin (k + 2) → H, F' (fun j => q j • b₁)
      = ∫ x, F (fun j => q j • e (x j)) ∂(Measure.pi fun _ => P) := by
    intro q
    change ∫ x, F (fun j => (q j * 1) • (if true = true then e (x j) else y₀))
      ∂(Measure.pi fun _ => P) = _
    simp
  have h := (hEv G H (Yb H) ρ k F' hInv' hcoc').2 b₀ b₁ z hz
  simp only [ev, key1, key2] at h
  simpa [ev] using h

end PositivityTheory.KB.LocalOverlapAverage

end
