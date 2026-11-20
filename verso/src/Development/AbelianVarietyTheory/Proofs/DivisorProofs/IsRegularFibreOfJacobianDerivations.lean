import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularRingTensorOfFibreLocalRingsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularLocalRingQuotientOfDetDerivationUnitStatement
open IsLocalRing TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `S T K _ _ _ _ _ _ Q hker hfrac h f g d D hD hg hf hgQ hdet`. Use `GlobalTheory.T.isRegularRing_tensor_of_regular_fibre_localizations S T K Q hker hfrac ?_` and prove the remaining obligations. Introduce `n _ hn`. Use `set F : Fin h → T := fun j => algebraMap S T (f j) with hFdef`. Establish `hFn : ∀ j, F j ∈ n`.

Introduce `j`. Establish `: f j ∈ n.comap (algebraMap S T)` using `by rw [hn]; exact hf j`. Conclude with `this`. Establish `hdetn : (Matrix.of fun i j => D i (F j)).det ∉ n`. Introduce `hmem`.

Establish `hm : (Matrix.of fun i j => D i (F j)) = (Matrix.of fun i j => d i (f j)).map (algebraMap S T)`. Use extensionality with `i j`. Simplify using `[hFdef, hD]`. Rewrite `hmem` using `[hm, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Establish `: (Matrix.of fun i j => d i (f j)).det ∈ n.comap (algebraMap S T)` using `hmem`.

Rewrite `this` using `[hn]`. Conclude with `hdet this`. Establish `hreg` using `GlobalTheory.T.isRegularLocalRing_quotient_of_det_derivation_unit T h F D n hFn hdetn`. Establish `heq : (Ideal.span (Set.range F)).map (algebraMap T (Localization.AtPrime n)) = (Q.map (algebraMap S T)).map (algebraMap T (Localization.AtPrime n))`. Establish `hspan : Ideal.span (Set.range F) = (Ideal.span (Set.range f)).map (algebraMap S T)`.

Rewrite using `[Ideal.map_span, ← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[hspan, Ideal.map_map, Ideal.map_map]`. Apply `le_antisymm` to reduce the goal to its premises. Apply `Ideal.map_mono` to reduce the goal to its premises.

Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `hf j`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `x hx`.

Rewrite using `[Ideal.mem_comap]`. Establish `hu : IsUnit ((algebraMap T (Localization.AtPrime n)).comp (algebraMap S T) g)`. Rewrite using `[RingHom.comp_apply]`. Apply `IsLocalization.map_units (M := n.primeCompl) (Localization.AtPrime n) (⟨algebraMap S T g, ?_⟩ : n.primeCompl)` to reduce the goal to its premises. Introduce `hgn`.

Establish `: g ∈ n.comap (algebraMap S T)` using `hgn`. Rewrite `this` using `[hn]`. Conclude with `hg this`. Establish `hm : (algebraMap T (Localization.AtPrime n)).comp (algebraMap S T) (g * x) ∈ (Ideal.span (Set.range f)).map ((algebraMap T (Localization.AtPrime n)).comp (algebraMap S T))` using `Ideal.mem_map_of_mem _ (hgQ x hx)`. Rewrite `hm` using `[map_mul]`.

Conclude with `(Ideal.unit_mul_mem_iff_mem _ hu).mp hm`. Rewrite using `[← heq]`. Conclude with `hreg`.
-/
theorem regular_fibre_of_jacobian : ∀ (S T K : Type) [CommRing S] [CommRing T] [Algebra S T] [IsRegularRing T] [Field K] [Algebra S K] (Q : Ideal S), RingHom.ker (algebraMap S K) = Q → (∀ y : K, ∃ a b : S, b ∉ Q ∧ y * algebraMap S K b = algebraMap S K a) → ∀ (h : ℕ) (f : Fin h → S) (g : S) (d : Fin h → Derivation ℤ S S) (D : Fin h → Derivation ℤ T T), (∀ i x, D i (algebraMap S T x) = algebraMap S T (d i x)) → g ∉ Q → (∀ j, f j ∈ Q) → (∀ x ∈ Q, g * x ∈ Ideal.span (Set.range f)) → (Matrix.of fun i j => d i (f j)).det ∉ Q → IsRegularRing (T ⊗[S] K) := by
  intro S T K _ _ _ _ _ _ Q hker hfrac h f g d D hD hg hf hgQ hdet
  refine GlobalTheory.T.isRegularRing_tensor_of_regular_fibre_localizations S T K Q hker hfrac ?_
  intro n _ hn
  set F : Fin h → T := fun j => algebraMap S T (f j) with hFdef
  have hFn : ∀ j, F j ∈ n := by
    intro j
    have : f j ∈ n.comap (algebraMap S T) := by rw [hn]; exact hf j
    exact this
  have hdetn : (Matrix.of fun i j => D i (F j)).det ∉ n := by
    intro hmem
    have hm : (Matrix.of fun i j => D i (F j)) = (Matrix.of fun i j => d i (f j)).map (algebraMap S T) := by
      ext i j; simp [hFdef, hD]
    rw [hm, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at hmem
    have : (Matrix.of fun i j => d i (f j)).det ∈ n.comap (algebraMap S T) := hmem
    rw [hn] at this
    exact hdet this
  have hreg := GlobalTheory.T.isRegularLocalRing_quotient_of_det_derivation_unit T h F D n hFn hdetn
  have heq : (Ideal.span (Set.range F)).map (algebraMap T (Localization.AtPrime n)) =
      (Q.map (algebraMap S T)).map (algebraMap T (Localization.AtPrime n)) := by
    have hspan : Ideal.span (Set.range F) = (Ideal.span (Set.range f)).map (algebraMap S T) := by
      rw [Ideal.map_span, ← Set.range_comp]; rfl
    rw [hspan, Ideal.map_map, Ideal.map_map]
    apply le_antisymm
    · apply Ideal.map_mono
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact hf j
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap]
      have hu : IsUnit ((algebraMap T (Localization.AtPrime n)).comp (algebraMap S T) g) := by
        rw [RingHom.comp_apply]
        apply IsLocalization.map_units (M := n.primeCompl) (Localization.AtPrime n) (⟨algebraMap S T g, ?_⟩ : n.primeCompl)
        intro hgn
        have : g ∈ n.comap (algebraMap S T) := hgn
        rw [hn] at this
        exact hg this
      have hm : (algebraMap T (Localization.AtPrime n)).comp (algebraMap S T) (g * x) ∈
          (Ideal.span (Set.range f)).map ((algebraMap T (Localization.AtPrime n)).comp (algebraMap S T)) :=
        Ideal.mem_map_of_mem _ (hgQ x hx)
      rw [map_mul] at hm
      exact (Ideal.unit_mul_mem_iff_mem _ hu).mp hm
  rw [← heq]
  exact hreg

end GlobalTheory
