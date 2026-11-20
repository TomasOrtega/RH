import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentsSimpleFDRepFiniteFinsumEqOne
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.ZSumOne

open CategoryTheory

variable {G : Type} [Group G] [Fintype G]

/- English proof (translation)
Simplify using `only [zOf, MonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply, MonoidAlgebra.single_apply, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]`.
-/
theorem zOf_coeff (χ : G → ℂ) (y : G) : (zOf χ).coeff y = χ 1 / (Fintype.card G : ℂ) * χ y⁻¹ := by
  simp only [zOf, MonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply, MonoidAlgebra.single_apply,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]

/- English proof (translation)
Rewrite using `[← hV 1, FDRep.char_one]`.
-/
theorem irr_one_eq_finrank {χ : G → ℂ} {V : FDRep ℂ G} (hV : ∀ x, V.character x = χ x) :
    χ 1 = (Module.finrank ℂ V : ℂ) := by
  rw [← hV 1, FDRep.char_one]

/- English proof (translation)
Establish `h1` using `irr_one_eq_finrank hV`. Unfold `zOf Formalism.IrreducibleCountingLemmas.TYPES.zIdem`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[h1, ← hV x⁻¹]`. Both sides reduce to the same expression.
-/
theorem zOf_eq_zIdem (χ : G → ℂ) (V : FDRep ℂ G) (hV : ∀ x, V.character x = χ x) :
    zOf χ = Formalism.IrreducibleCountingLemmas.TYPES.zIdem V := by
  have h1 := irr_one_eq_finrank hV
  unfold zOf Formalism.IrreducibleCountingLemmas.TYPES.zIdem
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [h1, ← hV x⁻¹]
  rfl

/- English proof (translation)
Introduce `χ hχ χ' hχ' h`. Take `⟨V, hs, hV⟩` from `hχ`. Take `⟨V', hs', hV'⟩` from `hχ'`. Establish `hc : (Fintype.card G : ℂ) ≠ 0` using `by exact_mod_cast Fintype.card_ne_zero`. Establish `h1` using `irr_one_eq_finrank hV`.

Establish `h1'` using `irr_one_eq_finrank hV'`. Establish `e1` using `congrArg (fun a => a.coeff 1) h`. Simplify using `only [zOf_coeff, inv_one] at e1`. Rewrite `e1` using `[h1, h1']`. Establish `e2 : ((Module.finrank ℂ V * Module.finrank ℂ V : ℕ) : ℂ) = ((Module.finrank ℂ V' * Module.finrank ℂ V' : ℕ) : ℂ)`.

Use `push_cast`. Clear denominators, using `at e1` for the nonvanishing conditions. Take the linear combination `e1`. Establish `hn : Module.finrank ℂ V = Module.finrank ℂ V'` using `Nat.mul_self_inj.mp (by exact_mod_cast e2)`. Establish `h11 : χ 1 = χ' 1` using `by rw [h1, h1', hn]`.

Use `haveI := PI.GreenLabelSurjWork.nontrivial_of_simple V hs`. Establish `hpos : (Module.finrank ℂ V : ℂ) ≠ 0`. Conclude with `(Module.finrank_pos (R := ℂ) (M := V)).ne'` after adjusting the coercions. Establish `hk : χ 1 / (Fintype.card G : ℂ) ≠ 0` using `div_ne_zero (h1 ▸ hpos) hc`. Use function extensionality and compare the values at `y`.

Establish `e3` using `congrArg (fun a => a.coeff y⁻¹) h`. Simplify using `only [zOf_coeff, inv_inv] at e3`. Rewrite `e3` using `[← h11]`. Conclude with `mul_left_cancel₀ hk e3`.
-/
theorem zOf_injOn : Set.InjOn (zOf (G := G)) {χ | IsIrr χ} := by
  intro χ hχ χ' hχ' h
  obtain ⟨V, hs, hV⟩ := hχ
  obtain ⟨V', hs', hV'⟩ := hχ'
  have hc : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h1 := irr_one_eq_finrank hV
  have h1' := irr_one_eq_finrank hV'
  have e1 := congrArg (fun a => a.coeff 1) h
  simp only [zOf_coeff, inv_one] at e1
  rw [h1, h1'] at e1
  have e2 : ((Module.finrank ℂ V * Module.finrank ℂ V : ℕ) : ℂ) =
      ((Module.finrank ℂ V' * Module.finrank ℂ V' : ℕ) : ℂ) := by
    push_cast
    field_simp at e1
    linear_combination e1
  have hn : Module.finrank ℂ V = Module.finrank ℂ V' := Nat.mul_self_inj.mp (by exact_mod_cast e2)
  have h11 : χ 1 = χ' 1 := by rw [h1, h1', hn]
  haveI := PI.GreenLabelSurjWork.nontrivial_of_simple V hs
  have hpos : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := V)).ne'
  have hk : χ 1 / (Fintype.card G : ℂ) ≠ 0 := div_ne_zero (h1 ▸ hpos) hc
  funext y
  have e3 := congrArg (fun a => a.coeff y⁻¹) h
  simp only [zOf_coeff, inv_inv] at e3
  rw [← h11] at e3
  exact mul_left_cancel₀ hk e3

/- English proof (translation)
Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨χ, ⟨V, hs, hV⟩, rfl⟩`. Conclude with `⟨V, hs, (zOf_eq_zIdem χ V hV).symm⟩`. Introduce and unpack `⟨τ, hs, rfl⟩`.

Conclude with `⟨τ.character, ⟨τ, hs, fun _ => rfl⟩, zOf_eq_zIdem _ τ fun _ => rfl⟩`.
-/
theorem zOf_image :
    zOf '' {χ : G → ℂ | IsIrr χ} =
      {z : MonoidAlgebra ℂ G | ∃ τ : FDRep ℂ G, Simple τ ∧ Formalism.IrreducibleCountingLemmas.TYPES.zIdem τ = z} := by
  ext z
  constructor
  · rintro ⟨χ, ⟨V, hs, hV⟩, rfl⟩
    exact ⟨V, hs, (zOf_eq_zIdem χ V hV).symm⟩
  · rintro ⟨τ, hs, rfl⟩
    exact ⟨τ.character, ⟨τ, hs, fun _ => rfl⟩, zOf_eq_zIdem _ τ fun _ => rfl⟩

end GlobalTheory.GLq.ZSumOne

namespace GlobalTheory.GLq

/- English proof (translation)
Introduce `G _ _`. Establish `hZ` using `GlobalTheory.SerOSys.zIdem_finite_and_finsum_eq_one G`. Rewrite `hZ` using `[← ZSumOne.zOf_image]`. Use `⟨Set.Finite.of_finite_image hZ.1 ZSumOne.zOf_injOn, ?_⟩` and prove the remaining obligations. Establish `himg` using `finsum_mem_image (f := fun z : MonoidAlgebra ℂ G => z) (ZSumOne.zOf_injOn (G := G))`.

Rewrite using `[← himg]`. Conclude with `hZ.2`.
-/
theorem irr_finite_and_finsum_zOf_eq_one : ∀ (G : Type) [Group G] [Fintype G],
    {χ : G → ℂ | IsIrr χ}.Finite ∧ ∑ᶠ χ ∈ {χ : G → ℂ | IsIrr χ}, zOf χ = 1 := by
  intro G _ _
  have hZ := GlobalTheory.SerOSys.zIdem_finite_and_finsum_eq_one G
  rw [← ZSumOne.zOf_image] at hZ
  refine ⟨Set.Finite.of_finite_image hZ.1 ZSumOne.zOf_injOn, ?_⟩
  have himg := finsum_mem_image (f := fun z : MonoidAlgebra ℂ G => z) (ZSumOne.zOf_injOn (G := G))
  rw [← himg]
  exact hZ.2

end GlobalTheory.GLq
