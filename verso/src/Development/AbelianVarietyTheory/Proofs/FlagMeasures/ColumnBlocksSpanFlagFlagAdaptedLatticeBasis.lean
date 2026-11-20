import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

/- English proof (translation)
Establish `hall : ∀ x : Fin m → E, (fun l => φ (x l)) ∈ W`. Introduce `x`. Establish `hx : x ∈ Submodule.span E (Λ : Set (Fin m → E))` using `by rw [hΛ]; trivial`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem t ht => exact h t ht`.

Consider the case `zero`. Establish `e1 : (fun l => φ ((0 : Fin m → E) l)) = 0`. Use function extensionality and compare the values at `l`. Simplify using the standard rewrite rules. Rewrite using `[e1]`.

Conclude with `W.zero_mem`. Consider the case `add x y _ _ hx hy`. Establish `e1 : (fun l => φ ((x + y) l)) = (fun l => φ (x l)) + (fun l => φ (y l))`. Use function extensionality and compare the values at `l`. Simplify using the standard rewrite rules.

Rewrite using `[e1]`. Conclude with `W.add_mem hx hy`. Consider the case `smul c x _ hx`. Establish `e1 : (fun l => φ ((c • x) l)) = φ c • (fun l => φ (x l))`. Use function extensionality and compare the values at `l`.

Simplify using the standard rewrite rules. Rewrite using `[e1]`. Conclude with `W.smul_mem _ hx`. Establish `key : ∀ l, (Pi.single l (1 : ℂ) : Fin m → ℂ) ∈ W`. Introduce `l`.

Use `hall (Pi.single l 1) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `l'`. Distinguish the cases in `hl : l' = l`. Substitute `hl` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[hl]`. Rewrite using `[eq_top_iff]`. Introduce `w _`. Establish `hw : w = ∑ l, w l • (Pi.single l (1 : ℂ) : Fin m → ℂ)`. Use function extensionality and compare the values at `l'`.

Simplify using `[Finset.sum_apply, Pi.single_apply]`. Rewrite using `[hw]`. Conclude with `W.sum_mem fun l _ => W.smul_mem _ (key l)`.
-/
theorem eq_top_of_map_lattice_mem {E : Type} [Field E] [NumberField E] (φ : E →+* ℂ) {m : ℕ}
    (Λ : Submodule (𝓞 E) (Fin m → E)) (hΛ : Submodule.span E (Λ : Set (Fin m → E)) = ⊤)
    (W : Submodule ℂ (Fin m → ℂ)) (h : ∀ t ∈ Λ, (fun l => φ (t l)) ∈ W) : W = ⊤ := by

  have hall : ∀ x : Fin m → E, (fun l => φ (x l)) ∈ W := by
    intro x
    have hx : x ∈ Submodule.span E (Λ : Set (Fin m → E)) := by rw [hΛ]; trivial
    induction hx using Submodule.span_induction with
    | mem t ht => exact h t ht
    | zero =>
      have e1 : (fun l => φ ((0 : Fin m → E) l)) = 0 := by
        funext l; simp
      rw [e1]; exact W.zero_mem
    | add x y _ _ hx hy =>
      have e1 : (fun l => φ ((x + y) l)) = (fun l => φ (x l)) + (fun l => φ (y l)) := by
        funext l; simp
      rw [e1]; exact W.add_mem hx hy
    | smul c x _ hx =>
      have e1 : (fun l => φ ((c • x) l)) = φ c • (fun l => φ (x l)) := by
        funext l; simp
      rw [e1]; exact W.smul_mem _ hx

  have key : ∀ l, (Pi.single l (1 : ℂ) : Fin m → ℂ) ∈ W := by
    intro l
    convert hall (Pi.single l 1) using 1
    funext l'
    by_cases hl : l' = l
    · subst hl; simp
    · simp [hl]
  rw [eq_top_iff]
  intro w _
  have hw : w = ∑ l, w l • (Pi.single l (1 : ℂ) : Fin m → ℂ) := by
    funext l'; simp [Finset.sum_apply, Pi.single_apply]
  rw [hw]
  exact W.sum_mem fun l _ => W.smul_mem _ (key l)

/- English proof (translation)
Introduce `I I₀ e xf a j S Λ x₀ T T' T₀ hA v k y`. Take `⟨-, -, hlat, -, -, -, -, hS⟩` from `hA`. Establish `himg : ∀ u : ∀ i, Fin (j i) → I.E, ((I.P v)⁻¹ *ᵥ fun l => I.φ v ((∑ i, T i *ᵥ u i) l)) = ∑ i, ((I.P v)⁻¹ * (T i).map (I.φ v)) *ᵥ (fun l => I.φ v (u i l))`. Introduce `u`. Establish `e1 : (fun l => I.φ v ((∑ i, T i *ᵥ u i) l)) = ∑ i, (T i).map (I.φ v) *ᵥ (fun l => I.φ v (u i l))`.

Use function extensionality and compare the values at `l`. Simplify using `only [Finset.sum_apply, map_sum, RingHom.map_mulVec, Function.comp_def]`. Rewrite using `[e1, Matrix.mulVec_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => Matrix.mulVec_mulVec _ _ _`. Prove the components needed by the constructor for the conclusion.

Introduce `hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨z, hz, rfl⟩` from `hx`. Take `⟨u, -, hk, rfl⟩` from `(hS k z).1 hz`.

Use `⟨fun i l => I.φ v (u i l), fun i hi => ?_, himg u⟩` and prove the remaining obligations. Use function extensionality and compare the values at `l`. Simplify using `[hk i hi]`. Consider the case `zero => exact ⟨0, fun _ _ => rfl, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨u, hu, rfl⟩` from `hx`. Take `⟨u', hu', rfl⟩` from `hy`. Use `⟨u + u', fun i hi => by simp [hu i hi, hu' i hi], ?_⟩` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => (Matrix.mulVec_add _ _ _).symm`.

Consider the case `smul c x _ hx`. Take `⟨u, hu, rfl⟩` from `hx`. Use `⟨c • u, fun i hi => by simp [hu i hi], ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => (Matrix.mulVec_smul _ _ _).symm`.

Introduce and unpack `⟨u, hu, rfl⟩`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hik : i.castSucc < k`. Establish `htop` using `eq_top_of_map_lattice_mem (I.φ v) (Λ i) (hlat i).span_eq_top ((flagAt I S v k).comap (Matrix.mulVecLin ((I.P v)⁻¹ * (T i).map (I.φ v)))) (by`. Introduce `t ht`.

Rewrite using `[Submodule.mem_comap, Matrix.mulVecLin_apply]`. Set `w : ∀ i', Fin (j i') → I.E` to `Pi.single i t`. Establish `hw1 : ∀ i', w i' ∈ Λ i'`. Introduce `i'`. Distinguish the cases in `h' : i' = i`.

Substitute `h'` using the available equality. Simplify `ht` using `[w]`. Simplify using `[w, Pi.single_eq_of_ne h']`. Establish `hw2 : ∀ i' : Fin a, ¬ i'.castSucc < k → w i' = 0`. Introduce `i' hi'`.

Establish `h' : i' ≠ i` using `by rintro rfl; exact hi' hik`. Simplify using `[w, Pi.single_eq_of_ne h']`. Establish `hz : (∑ i', T i' *ᵥ w i') ∈ S k` using `(hS k _).2 ⟨w, hw1, hw2, rfl⟩`. Establish `hmem` using `Submodule.subset_span (R := ℂ) (Set.mem_image_of_mem (fun y : Fin I.n → I.E => (I.P v)⁻¹ *ᵥ fun l => I.φ v (y l)) hz)`. Establish `hsum` using `himg w`.

Rewrite `hmem` using `[hsum, Finset.sum_eq_single i]`. Simplify using `[w] at hmem`. Conclude with `hmem`. Introduce `i' _ h'`. Simplify using `[w, Pi.single_eq_of_ne h']`.

Conclude with `Matrix.mulVec_zero _`. Use the proof step `simp)`. Establish `: u i ∈ (flagAt I S v k).comap (Matrix.mulVecLin ((I.P v)⁻¹ * (T i).map (I.φ v)))`. Rewrite using `[htop]`. Discharge the goal by the elementary cases of `trivial`.

Simplify `this` using `[Submodule.mem_comap, Matrix.mulVecLin_apply]`. Simplify using `[hu i hik]`.
-/
theorem spansFlag_flagAt : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ v, SpansFlag (fun i => (I.P v)⁻¹ * (T i).map (I.φ v)) (flagAt I S v) := by
  intro I I₀ e xf a j S Λ x₀ T T' T₀ hA v k y
  obtain ⟨-, -, hlat, -, -, -, -, hS⟩ := hA

  have himg : ∀ u : ∀ i, Fin (j i) → I.E,
      ((I.P v)⁻¹ *ᵥ fun l => I.φ v ((∑ i, T i *ᵥ u i) l)) =
        ∑ i, ((I.P v)⁻¹ * (T i).map (I.φ v)) *ᵥ (fun l => I.φ v (u i l)) := by
    intro u
    have e1 : (fun l => I.φ v ((∑ i, T i *ᵥ u i) l)) =
        ∑ i, (T i).map (I.φ v) *ᵥ (fun l => I.φ v (u i l)) := by
      funext l
      simp only [Finset.sum_apply, map_sum, RingHom.map_mulVec, Function.comp_def]
    rw [e1, Matrix.mulVec_sum]
    exact Finset.sum_congr rfl fun i _ => Matrix.mulVec_mulVec _ _ _
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      obtain ⟨u, -, hk, rfl⟩ := (hS k z).1 hz
      refine ⟨fun i l => I.φ v (u i l), fun i hi => ?_, himg u⟩
      funext l
      simp [hk i hi]
    | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨u, hu, rfl⟩ := hx
      obtain ⟨u', hu', rfl⟩ := hy
      refine ⟨u + u', fun i hi => by simp [hu i hi, hu' i hi], ?_⟩
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => (Matrix.mulVec_add _ _ _).symm
    | smul c x _ hx =>
      obtain ⟨u, hu, rfl⟩ := hx
      refine ⟨c • u, fun i hi => by simp [hu i hi], ?_⟩
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => (Matrix.mulVec_smul _ _ _).symm
  · rintro ⟨u, hu, rfl⟩
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hik : i.castSucc < k
    ·
      have htop := eq_top_of_map_lattice_mem (I.φ v) (Λ i) (hlat i).span_eq_top
        ((flagAt I S v k).comap (Matrix.mulVecLin ((I.P v)⁻¹ * (T i).map (I.φ v)))) (by
          intro t ht
          rw [Submodule.mem_comap, Matrix.mulVecLin_apply]
          let w : ∀ i', Fin (j i') → I.E := Pi.single i t
          have hw1 : ∀ i', w i' ∈ Λ i' := by
            intro i'
            by_cases h' : i' = i
            · subst h'; simpa [w] using ht
            · simp [w, Pi.single_eq_of_ne h']
          have hw2 : ∀ i' : Fin a, ¬ i'.castSucc < k → w i' = 0 := by
            intro i' hi'
            have h' : i' ≠ i := by rintro rfl; exact hi' hik
            simp [w, Pi.single_eq_of_ne h']
          have hz : (∑ i', T i' *ᵥ w i') ∈ S k := (hS k _).2 ⟨w, hw1, hw2, rfl⟩
          have hmem := Submodule.subset_span (R := ℂ) (Set.mem_image_of_mem
            (fun y : Fin I.n → I.E => (I.P v)⁻¹ *ᵥ fun l => I.φ v (y l)) hz)
          have hsum := himg w
          rw [hsum, Finset.sum_eq_single i] at hmem
          · simp [w] at hmem
            exact hmem
          · intro i' _ h'
            simp [w, Pi.single_eq_of_ne h']
            exact Matrix.mulVec_zero _
          · simp)
      have : u i ∈ (flagAt I S v k).comap (Matrix.mulVecLin ((I.P v)⁻¹ * (T i).map (I.φ v))) := by
        rw [htop]; trivial
      simpa [Submodule.mem_comap, Matrix.mulVecLin_apply] using this
    · simp [hu i hik]

end GlobalTheory.LeviIso
