import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntAfApproxInterUnitConj

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.RowLev

/- English proof (translation)
Unfold `extId Ideal.map`. Use `congr 1`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, e⟩`.

Conclude with `⟨a, ha, Subtype.ext e.symm⟩`. Introduce and unpack `⟨a, ha, rfl⟩`. Conclude with `⟨a, ha, rfl⟩`.
-/
theorem extId_eq_map_psi (I : AutInst) (𝔞 : Ideal (𝓞 I.E)) : extId I 𝔞 = 𝔞.map (Inhab.psi I.F I.E) := by
  unfold extId Ideal.map
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, e⟩
    exact ⟨a, ha, Subtype.ext e.symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩

/- English proof (translation)
Introduce `I`. Set `st : 𝓞 I.E →+* 𝓞 I.E` to `RingOfIntegers.mapRingHom (starRingEnd I.E)`. Establish `hst : ∀ a : 𝓞 I.E, (st a : I.E) = star (a : I.E)` using `fun a => rfl`. Establish `hst2 : ∀ a, st (st a) = a` using `fun a => RingOfIntegers.ext (by rw [hst, hst, star_star])`. Establish `hsurj : Function.Surjective st` using `fun a => ⟨st a, hst2 a⟩`.

Establish `hsig : ∀ z ∈ IntAf I.F I.E, Formalism.UG.sigR I.cm.sig (Af I.F) z ∈ IntAf I.F I.E` using `(intAf_approx_inter_unit_conj I 1 le_rfl).2.2.2`. Use `⟨fun a b => ?_, fun a b h => ?_, fun m => ?_, fun w => ?_, fun w w' h => ?_, fun w w' w'' h h' => ?_, fun w w' h z hz => ?_⟩` and prove the remaining obligations. Simplify using `only [extId_eq_map_psi, Ideal.map_mul]`. Simplify using `only [extId_eq_map_psi, ← Ideal.map_sup, h, Ideal.map_top]`. Rewrite using `[extId_eq_map_psi, Ideal.map_span, Set.image_singleton, map_natCast]`.

Use `⟨w.comap st hsurj, fun a b hab => ?_⟩` and prove the remaining obligations. Establish `: b = st a` using `RingOfIntegers.ext hab`. Substitute `this` using the available equality. Use `show _ ↔ st (st a) ∈ w.asIdeal`. Rewrite using `[hst2]`.

Introduce `a b hab`. Conclude with `(h b a (by rw [hab, star_star])).symm`. Use `HeightOneSpectrum.ext (Ideal.ext fun b => ?_)` and prove the remaining obligations. Establish `e : (b : I.E) = star (st b : I.E)` using `by rw [hst, star_star]`. Conclude with `(h (st b) b e).symm.trans (h' (st b) b e)`.

Establish `key : (⟨_, hsig z z.2⟩ : IntAf I.F I.E) ∈ extId I w'.asIdeal`. Unfold `extId at hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨a, ha, e⟩` from `hx`.

Use `Ideal.subset_span ⟨st a, (h a (st a) (hst a)).1 ha, ?_⟩` and prove the remaining obligations. Use `show Formalism.UG.sigR I.cm.sig (Af I.F) x = _`. Rewrite using `[e]`. Both sides reduce to the same expression. Consider the case `zero`.

Use `(extId I w'.asIdeal).zero_mem using 1` and compare the differences between its conclusion and the goal. Conclude with `Subtype.ext (map_zero _)`. Consider the case `add x y _ _ hx hy`. Use `add_mem hx hy using 1` and compare the differences between its conclusion and the goal. Conclude with `Subtype.ext (map_add _ _ _)`.

Consider the case `smul a x _ hx`. Use `Ideal.mul_mem_left _ ⟨_, hsig a a.2⟩ hx using 1` and compare the differences between its conclusion and the goal. Conclude with `Subtype.ext (map_mul _ _ _)`. Conclude with `⟨_, key, rfl⟩`.
-/
theorem extId_mul_sup_natCast_conj : ∀ (I : AutInst), (∀ 𝔞 𝔟 : Ideal (𝓞 I.E), extId I (𝔞 * 𝔟) = extId I 𝔞 * extId I 𝔟) ∧ (∀ 𝔞 𝔟 : Ideal (𝓞 I.E), 𝔞 ⊔ 𝔟 = ⊤ → extId I 𝔞 ⊔ extId I 𝔟 = ⊤) ∧ (∀ m : ℕ, extId I (Ideal.span {(m : 𝓞 I.E)}) = Ideal.span {(m : IntAf I.F I.E)}) ∧ (∀ w : HeightOneSpectrum (𝓞 I.E), ∃ w', IsConj I w w') ∧ (∀ w w' : HeightOneSpectrum (𝓞 I.E), IsConj I w w' → IsConj I w' w) ∧ (∀ w w' w'' : HeightOneSpectrum (𝓞 I.E), IsConj I w w' → IsConj I w w'' → w' = w'') ∧ ∀ w w' : HeightOneSpectrum (𝓞 I.E), IsConj I w w' → ∀ z ∈ extId I w.asIdeal, ∃ z' ∈ extId I w'.asIdeal, (z' : (I.E ⊗[I.F] Af I.F)) = Formalism.UG.sigR I.cm.sig (Af I.F) z := by
  intro I
  let st : 𝓞 I.E →+* 𝓞 I.E := RingOfIntegers.mapRingHom (starRingEnd I.E)
  have hst : ∀ a : 𝓞 I.E, (st a : I.E) = star (a : I.E) := fun a => rfl
  have hst2 : ∀ a, st (st a) = a := fun a => RingOfIntegers.ext (by rw [hst, hst, star_star])
  have hsurj : Function.Surjective st := fun a => ⟨st a, hst2 a⟩
  have hsig : ∀ z ∈ IntAf I.F I.E, Formalism.UG.sigR I.cm.sig (Af I.F) z ∈ IntAf I.F I.E :=
    (intAf_approx_inter_unit_conj I 1 le_rfl).2.2.2
  refine ⟨fun a b => ?_, fun a b h => ?_, fun m => ?_, fun w => ?_, fun w w' h => ?_,
    fun w w' w'' h h' => ?_, fun w w' h z hz => ?_⟩
  · simp only [extId_eq_map_psi, Ideal.map_mul]
  · simp only [extId_eq_map_psi, ← Ideal.map_sup, h, Ideal.map_top]
  · rw [extId_eq_map_psi, Ideal.map_span, Set.image_singleton, map_natCast]
  · refine ⟨w.comap st hsurj, fun a b hab => ?_⟩
    have : b = st a := RingOfIntegers.ext hab
    subst this
    show _ ↔ st (st a) ∈ w.asIdeal
    rw [hst2]
  · intro a b hab
    exact (h b a (by rw [hab, star_star])).symm
  · refine HeightOneSpectrum.ext (Ideal.ext fun b => ?_)
    have e : (b : I.E) = star (st b : I.E) := by rw [hst, star_star]
    exact (h (st b) b e).symm.trans (h' (st b) b e)
  · have key : (⟨_, hsig z z.2⟩ : IntAf I.F I.E) ∈ extId I w'.asIdeal := by
      unfold extId at hz
      induction hz using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, ha, e⟩ := hx
        refine Ideal.subset_span ⟨st a, (h a (st a) (hst a)).1 ha, ?_⟩
        show Formalism.UG.sigR I.cm.sig (Af I.F) x = _
        rw [e]
        rfl
      | zero =>
        convert (extId I w'.asIdeal).zero_mem using 1
        exact Subtype.ext (map_zero _)
      | add x y _ _ hx hy =>
        convert add_mem hx hy using 1
        exact Subtype.ext (map_add _ _ _)
      | smul a x _ hx =>
        convert Ideal.mul_mem_left _ ⟨_, hsig a a.2⟩ hx using 1
        exact Subtype.ext (map_mul _ _ _)
    exact ⟨_, key, rfl⟩

end GlobalTheory.RowLev
