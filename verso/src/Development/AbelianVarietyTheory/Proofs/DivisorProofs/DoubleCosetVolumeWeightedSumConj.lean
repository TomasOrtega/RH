import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockParOpp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocPartMul
open MeasureTheory Matrix
open scoped Classical

noncomputable section

namespace GlobalTheory.OrbDesc

variable {H : Type} [Group H]

/- English proof (translation)
Unfold `GlobalTheory.LKLoc.locPart`. Rewrite using `[Subgroup.map_inf_eq _ _ _ (MulAut.conj c).injective, Subgroup.map_map, Subgroup.map_map]`. Use `congr 2`. Use extensionality with `k`. Simplify using `only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, MulAut.conj_apply]`.

Use `group`.
-/
theorem locPart_conj (T L : Subgroup H) (c x : H) :
    GlobalTheory.LKLoc.locPart (T.map (MulAut.conj c).toMonoidHom) (L.map (MulAut.conj c).toMonoidHom)
      (MulAut.conj c x) = (GlobalTheory.LKLoc.locPart T L x).map (MulAut.conj c).toMonoidHom := by
  unfold GlobalTheory.LKLoc.locPart
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj c).injective, Subgroup.map_map, Subgroup.map_map]
  congr 2
  ext k
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, MulAut.conj_apply]
  group

/- English proof (translation)
Unfold `GlobalTheory.LKLoc.volRat`. Rewrite using `[Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj c).injective, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj c).injective]`.
-/
theorem volRat_conj (U V : Subgroup H) (c : H) :
    GlobalTheory.LKLoc.volRat (U.map (MulAut.conj c).toMonoidHom) (V.map (MulAut.conj c).toMonoidHom) =
      GlobalTheory.LKLoc.volRat U V := by
  unfold GlobalTheory.LKLoc.volRat
  rw [Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj c).injective,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj c).injective]

/- English proof (translation)
Unfold `wt`. Rewrite using `[locPart_conj, volRat_conj]`. Use `congr 2`. Simplify using `only [MulAut.conj_apply]`. Use `group`.
-/
theorem wt_conj (T L U : Subgroup H) (Ψ : H → ℂ) (c x : H) :
    wt (T.map (MulAut.conj c).toMonoidHom) (L.map (MulAut.conj c).toMonoidHom)
      (U.map (MulAut.conj c).toMonoidHom) (fun y => Ψ (c⁻¹ * y * c)) (MulAut.conj c x) = wt T L U Ψ x := by
  unfold wt
  rw [locPart_conj, volRat_conj]
  congr 2
  simp only [MulAut.conj_apply]
  group

/- English proof (translation)
Introduce `H _ T L U Ψ c hT hΨl hΨr`. Use `set φ := MulAut.conj c with hφ`. Establish `hT' : ∀ s ∈ T.map φ.toMonoidHom, ∀ t ∈ T.map φ.toMonoidHom, s * t = t * s`. Introduce and unpack `_ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩`. Simplify using `only [MulEquiv.coe_toMonoidHom, ← map_mul, hT s hs t ht]`.

Establish `hΨl' : ∀ t ∈ T.map φ.toMonoidHom, ∀ x, Ψ (c⁻¹ * (t * x) * c) = Ψ (c⁻¹ * x * c)`. Introduce and unpack `_ ⟨t, ht, rfl⟩ x`. Establish `: c⁻¹ * (φ.toMonoidHom t * x) * c = t * (c⁻¹ * x * c)`. Simplify using `only [hφ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]`. Use `group`.

Rewrite using `[this, hΨl t ht]`. Establish `hΨr' : ∀ l ∈ L.map φ.toMonoidHom, ∀ x, Ψ (c⁻¹ * (x * l) * c) = Ψ (c⁻¹ * x * c)`. Introduce and unpack `_ ⟨l, hl, rfl⟩ x`. Establish `: c⁻¹ * (x * φ.toMonoidHom l) * c = (c⁻¹ * x * c) * l`. Simplify using `only [hφ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]`.

Use `group`. Rewrite using `[this, hΨr l hl]`. Set `E : DoubleCoset.Quotient (T : Set H) (L : Set H) ≃ DoubleCoset.Quotient ((T.map φ.toMonoidHom : Subgroup H) : Set H) ((L.map φ.toMonoidHom : Subgroup H) : Set H)` to `Quotient.congr φ.toEquiv (by`. Introduce `a b`. Rewrite using `[DoubleCoset.rel_iff, DoubleCoset.rel_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, ht, l, hl, rfl⟩`. Conclude with `⟨φ t, ⟨t, ht, rfl⟩, φ l, ⟨l, hl, rfl⟩, by simp [map_mul]⟩`. Introduce and unpack `⟨_, ⟨t, ht, rfl⟩, _, ⟨l, hl, rfl⟩, h⟩`. Use `⟨t, ht, l, hl, φ.injective ?_⟩` and prove the remaining obligations.

Simplify `h)` using `[map_mul]`. Unfold `dsum`. Rewrite using `[← finsum_comp_equiv E]`. Use `congr 1`. Use extensionality with `q`.

Establish `hE : E q = DoubleCoset.mk _ _ (φ (Quotient.out q))` using `by conv_lhs => rw [← DoubleCoset.out_eq' T L q]`. Both sides reduce to the same expression. Rewrite using `[hE, wt_out _ hT' hΨl' hΨr', wt_conj]`.
-/
theorem dsum_conj : ∀ (H : Type) [Group H] (T L U : Subgroup H) (Ψ : H → ℂ) (c : H),
  (∀ s ∈ T, ∀ t ∈ T, s * t = t * s) → (∀ t ∈ T, ∀ x, Ψ (t * x) = Ψ x) → (∀ l ∈ L, ∀ x, Ψ (x * l) = Ψ x) →
  GlobalTheory.OrbDesc.dsum T L U Ψ = GlobalTheory.OrbDesc.dsum (T.map (MulAut.conj c).toMonoidHom) (L.map (MulAut.conj c).toMonoidHom)
    (U.map (MulAut.conj c).toMonoidHom) (fun x => Ψ (c⁻¹ * x * c)) := by
  intro H _ T L U Ψ c hT hΨl hΨr
  set φ := MulAut.conj c with hφ
  have hT' : ∀ s ∈ T.map φ.toMonoidHom, ∀ t ∈ T.map φ.toMonoidHom, s * t = t * s := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul, hT s hs t ht]
  have hΨl' : ∀ t ∈ T.map φ.toMonoidHom, ∀ x, Ψ (c⁻¹ * (t * x) * c) = Ψ (c⁻¹ * x * c) := by
    rintro _ ⟨t, ht, rfl⟩ x
    have : c⁻¹ * (φ.toMonoidHom t * x) * c = t * (c⁻¹ * x * c) := by
      simp only [hφ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
    rw [this, hΨl t ht]
  have hΨr' : ∀ l ∈ L.map φ.toMonoidHom, ∀ x, Ψ (c⁻¹ * (x * l) * c) = Ψ (c⁻¹ * x * c) := by
    rintro _ ⟨l, hl, rfl⟩ x
    have : c⁻¹ * (x * φ.toMonoidHom l) * c = (c⁻¹ * x * c) * l := by
      simp only [hφ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
    rw [this, hΨr l hl]
  let E : DoubleCoset.Quotient (T : Set H) (L : Set H) ≃
      DoubleCoset.Quotient ((T.map φ.toMonoidHom : Subgroup H) : Set H) ((L.map φ.toMonoidHom : Subgroup H) : Set H) :=
    Quotient.congr φ.toEquiv (by
      intro a b
      rw [DoubleCoset.rel_iff, DoubleCoset.rel_iff]
      constructor
      · rintro ⟨t, ht, l, hl, rfl⟩
        exact ⟨φ t, ⟨t, ht, rfl⟩, φ l, ⟨l, hl, rfl⟩, by simp [map_mul]⟩
      · rintro ⟨_, ⟨t, ht, rfl⟩, _, ⟨l, hl, rfl⟩, h⟩
        refine ⟨t, ht, l, hl, φ.injective ?_⟩
        simpa [map_mul] using h)
  unfold dsum
  rw [← finsum_comp_equiv E]
  congr 1
  ext q
  have hE : E q = DoubleCoset.mk _ _ (φ (Quotient.out q)) := by
    conv_lhs => rw [← DoubleCoset.out_eq' T L q]
    rfl
  rw [hE, wt_out _ hT' hΨl' hΨr', wt_conj]

end GlobalTheory.OrbDesc
