import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.TensTopRing
import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint

noncomputable section

namespace MassDataIdxK

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain Topology
open scoped Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
The claim follows from `Module.Finite.of_restrictScalars_finite ℚ F E`.
-/
theorem fdFE : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E

instance imt (v : HeightOneSpectrum (𝓞 F)) : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩

/- English proof (translation)
Use `fdFE (F := F) (E := E)` as an intermediate fact. Set `b` to `Module.finBasis (Fv F v) (Fv F v ⊗[F] E)`. Conclude with `T2Space.of_injective_continuous b.equivFun.injective (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap)`.
-/
theorem t2Space_scalarTensorExt (v : HeightOneSpectrum (𝓞 F)) : T2Space (Fv F v ⊗[F] E) := by
  have := fdFE (F := F) (E := E)
  let b := Module.finBasis (Fv F v) (Fv F v ⊗[F] E)
  exact T2Space.of_injective_continuous b.equivFun.injective
    (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap)

variable {n : ℕ} (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Use function extensionality and compare the values at `i`. Conclude with `map_zero _`.
-/
theorem ratV_zero : ratV (F := F) (Fv F v) (0 : Fin n → E) = 0 := by
  funext i; exact map_zero _

/- English proof (translation)
Use function extensionality and compare the values at `i`. Conclude with `map_add _ _ _`.
-/
theorem ratV_add (x y : Fin n → E) :
    ratV (F := F) (Fv F v) (x + y) = ratV (F := F) (Fv F v) x + ratV (F := F) (Fv F v) y := by
  funext i; exact map_add _ _ _

/- English proof (translation)
Use function extensionality and compare the values at `i`. Conclude with `map_zsmul _ _ _`.
-/
theorem ratV_zsmul (m : ℤ) (x : Fin n → E) :
    ratV (F := F) (Fv F v) (m • x) = m • ratV (F := F) (Fv F v) x := by
  funext i; exact map_zsmul _ _ _

def mulE (e : E) : (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v] (Fin n → Fv F v ⊗[F] E) :=
  LinearMap.pi fun i => (LinearMap.mulLeft (Fv F v) (inclR (F := F) (Fv F v) e)) ∘ₗ LinearMap.proj i

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mulE_apply (e : E) (w : Fin n → Fv F v ⊗[F] E) (i : Fin n) :
    mulE v e w i = inclR (F := F) (Fv F v) e * w i := rfl

/- English proof (translation)
Use `set W := Submodule.span (Fv F v) (ratV (F := F) (Fv F v) '' (L : Set (Fin n → E))) with hW`. Establish `h1 : ∀ a : 𝓞 E, ∀ w ∈ W, mulE v (algebraMap (𝓞 E) E a) w ∈ W`. Introduce `a w hw`. Establish `: W.map (mulE v (algebraMap (𝓞 E) E a)) ≤ W`. Rewrite using `[hW, Submodule.map_span, Submodule.span_le]`.

Introduce and unpack `_ ⟨_, ⟨x, hx, rfl⟩, rfl⟩`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨a • x, L.smul_mem a hx, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Use `show inclR (F := F) (Fv F v) ((a • x) i) = inclR (F := F) (Fv F v) (algebraMap (𝓞 E) E a) * inclR _ (x i)`.

Rewrite using `[Pi.smul_apply, Algebra.smul_def, map_mul]`. Conclude with `this ⟨w, hw, rfl⟩`. Establish `h2 : ∀ e : E, ∀ w ∈ W, mulE v e w ∈ W`. Introduce `e w hw`. Take `⟨y, hy0, hyi⟩` from `IsAlgebraic.exists_integral_multiple (R := ℤ) (z := e) ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic e))`.

Set `a : 𝓞 E` to `IsIntegralClosure.mk' (𝓞 E) (y • e) hyi`. Establish `ha : algebraMap (𝓞 E) E a = y • e` using `IsIntegralClosure.algebraMap_mk' _ _ _`. Establish `hyF : ((y : Fv F v)) ≠ 0`. Rewrite using `[← map_intCast (algebraMap F (Fv F v))]`. Conclude with `(map_ne_zero _).2 (Int.cast_ne_zero.2 hy0)`.

Establish `key : algebraMap (Fv F v) (Fv F v ⊗[F] E) ((y : Fv F v))⁻¹ * (y : Fv F v ⊗[F] E) = 1`. Rewrite using `[← map_intCast (algebraMap (Fv F v) (Fv F v ⊗[F] E)), ← map_mul, inv_mul_cancel₀ hyF, map_one]`. Establish `: mulE v e w = ((y : Fv F v))⁻¹ • mulE v (algebraMap (𝓞 E) E a) w`. Use function extensionality and compare the values at `i`. Rewrite using `[Pi.smul_apply, mulE_apply, mulE_apply, ha, zsmul_eq_mul, map_mul, map_intCast, Algebra.smul_def, ← mul_assoc, ← mul_assoc, key, one_mul]`.

Rewrite using `[this]`. Conclude with `W.smul_mem _ (h1 a w hw)`. Establish `h3 : ∀ x : Fin n → E, ratV (F` using `F) (Fv F v) x ∈ W := by`. Introduce `x`. Establish `hx : x ∈ Submodule.span E (L : Set (Fin n → E))` using `by rw [hL]; exact Submodule.mem_top`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩`. Consider the case `zero => rw [ratV_zero]`. Conclude with `W.zero_mem`. Consider the case `add x y _ _ hx hy => rw [ratV_add]`.

Conclude with `W.add_mem hx hy`. Consider the case `smul e x _ hx`. Establish `: ratV (F` using `F) (Fv F v) (e • x) = mulE v e (ratV (F := F) (Fv F v) x) := by`. Use function extensionality and compare the values at `i`. Conclude with `map_mul _ _ _`.

Rewrite using `[this]`. Conclude with `h2 e _ hx`. Rewrite using `[eq_top_iff]`. Introduce `w _`. Rewrite using `[← Finset.univ_sum_single w]`.

Use `W.sum_mem fun i _ => ?_` and prove the remaining obligations. Generalize the expression as in `w i = t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => rw [Pi.single_zero]`. Conclude with `W.zero_mem`.

Consider the case `tmul r e`. Establish `: (Pi.single i (r ⊗ₜ[F] e) : Fin n → Fv F v ⊗[F] E) = r • ratV (F` using `F) (Fv F v) (Pi.single i e) := by`. Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality.

Simplify using `[ratV, inclR, TensorProduct.smul_tmul']`. Simplify using `[ratV, h]`. Rewrite using `[this]`. Conclude with `W.smul_mem r (h3 _)`. Consider the case `add s t hs ht => rw [Pi.single_add]`.

Conclude with `W.add_mem hs ht`.
-/
theorem spanTop (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    Submodule.span (Fv F v) (ratV (F := F) (Fv F v) '' (L : Set (Fin n → E))) = ⊤ := by
  set W := Submodule.span (Fv F v) (ratV (F := F) (Fv F v) '' (L : Set (Fin n → E))) with hW
  have h1 : ∀ a : 𝓞 E, ∀ w ∈ W, mulE v (algebraMap (𝓞 E) E a) w ∈ W := by
    intro a w hw
    have : W.map (mulE v (algebraMap (𝓞 E) E a)) ≤ W := by
      rw [hW, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      apply Submodule.subset_span
      refine ⟨a • x, L.smul_mem a hx, ?_⟩
      funext i
      show inclR (F := F) (Fv F v) ((a • x) i) = inclR (F := F) (Fv F v) (algebraMap (𝓞 E) E a) * inclR _ (x i)
      rw [Pi.smul_apply, Algebra.smul_def, map_mul]
    exact this ⟨w, hw, rfl⟩
  have h2 : ∀ e : E, ∀ w ∈ W, mulE v e w ∈ W := by
    intro e w hw
    obtain ⟨y, hy0, hyi⟩ := IsAlgebraic.exists_integral_multiple (R := ℤ) (z := e) ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic e))
    let a : 𝓞 E := IsIntegralClosure.mk' (𝓞 E) (y • e) hyi
    have ha : algebraMap (𝓞 E) E a = y • e := IsIntegralClosure.algebraMap_mk' _ _ _
    have hyF : ((y : Fv F v)) ≠ 0 := by
      rw [← map_intCast (algebraMap F (Fv F v))]
      exact (map_ne_zero _).2 (Int.cast_ne_zero.2 hy0)
    have key : algebraMap (Fv F v) (Fv F v ⊗[F] E) ((y : Fv F v))⁻¹ * (y : Fv F v ⊗[F] E) = 1 := by
      rw [← map_intCast (algebraMap (Fv F v) (Fv F v ⊗[F] E)), ← map_mul, inv_mul_cancel₀ hyF, map_one]
    have : mulE v e w = ((y : Fv F v))⁻¹ • mulE v (algebraMap (𝓞 E) E a) w := by
      funext i
      rw [Pi.smul_apply, mulE_apply, mulE_apply, ha, zsmul_eq_mul, map_mul, map_intCast, Algebra.smul_def,
        ← mul_assoc, ← mul_assoc, key, one_mul]
    rw [this]; exact W.smul_mem _ (h1 a w hw)
  have h3 : ∀ x : Fin n → E, ratV (F := F) (Fv F v) x ∈ W := by
    intro x
    have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := by rw [hL]; exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [ratV_zero]; exact W.zero_mem
    | add x y _ _ hx hy => rw [ratV_add]; exact W.add_mem hx hy
    | smul e x _ hx =>
        have : ratV (F := F) (Fv F v) (e • x) = mulE v e (ratV (F := F) (Fv F v) x) := by
          funext i; exact map_mul _ _ _
        rw [this]; exact h2 e _ hx
  rw [eq_top_iff]
  intro w _
  rw [← Finset.univ_sum_single w]
  refine W.sum_mem fun i _ => ?_
  generalize w i = t
  induction t using TensorProduct.induction_on with
  | zero => rw [Pi.single_zero]; exact W.zero_mem
  | tmul r e =>
      have : (Pi.single i (r ⊗ₜ[F] e) : Fin n → Fv F v ⊗[F] E) =
          r • ratV (F := F) (Fv F v) (Pi.single i e) := by
        funext j
        by_cases h : j = i
        · subst h
          simp [ratV, inclR, TensorProduct.smul_tmul']
        · simp [ratV, h]
      rw [this]; exact W.smul_mem r (h3 _)
  | add s t hs ht => rw [Pi.single_add]; exact W.add_mem hs ht

end MassDataIdxK
