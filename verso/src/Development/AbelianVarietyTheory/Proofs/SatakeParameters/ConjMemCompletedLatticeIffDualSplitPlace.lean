import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralTensorAdelesEqAdelicCompletionOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitDualLat

variable {D : D7}

/- English proof (translation)
The claim follows from `map_sum f g _`.
-/
theorem ringHom_sum {A B ι : Type} [Semiring A] [Semiring B] [Fintype ι] (f : A →+* B) (g : ι → A) :
    f (∑ i, g i) = ∑ i, f (g i) := map_sum f g _

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => rw [RingHom.map_zero, RingHom.map_zero]`. Consider the case `add x y hx hy => rw [RingHom.map_add, RingHom.map_add, hx, hy]`. Consider the case `tmul a x`. Express the relevant statement in the definitionally equal form `a ⊗ₜ[D.host.F] star (star x) = _`.

Rewrite using `[star_star]`.
-/
theorem cA_cA (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, hx, hy]
  | tmul a x =>
    change a ⊗ₜ[D.host.F] star (star x) = _
    rw [star_star]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cA_incA (x : D.host.E) : cA D (incA D x) = incA D (star x) := rfl

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp only [RingHom.map_zero]`. Consider the case `add x y hx hy => simp only [RingHom.map_add, hx, hy]`. Consider the case `tmul a x => rfl`.
-/
theorem finPart_cA (x : AE D) : finPart D (cA D x) = sigR (Af D.host.F) D.sp.cm.sig (finPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add x y hx hy => simp only [RingHom.map_add, hx, hy]
  | tmul a x => rfl

/- English proof (translation)
Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, RingHom.map_zero _⟩`. Consider the case `add x y hx hy`. Take `⟨a, rfl⟩` from `hx`.

Take `⟨b, rfl⟩` from `hy`. Conclude with `⟨a + b, RingHom.map_add _ _ _⟩`. Consider the case `tmul a x => exact ⟨pairA D.host.F 0 a ⊗ₜ[D.host.F] x, rfl⟩`.
-/
theorem finPart_surjective : Function.Surjective (finPart D) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, RingHom.map_add _ _ _⟩
  | tmul a x => exact ⟨pairA D.host.F 0 a ⊗ₜ[D.host.F] x, rfl⟩

/- English proof (translation)
Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem w hw`. Take `⟨a, ha, o, rfl⟩` from `hw`. Conclude with `AddSubgroup.subset_closure ⟨a, ha, ⟨D.sp.cm.sig (o : D.host.E), (show IsIntegral ℤ (o : D.host.E) from o.2).map (D.sp.cm.sig : D.host.E →+* D.host.E).toIntAlgHom⟩, rfl⟩`. Consider the case `zero => rw [RingHom.map_zero]`.

Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [RingHom.map_add]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [RingHom.map_neg]`. Conclude with `neg_mem hx`.
-/
theorem sigR_mem_intAE {z : Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D) :
    sigR (Af D.host.F) D.sp.cm.sig z ∈ intAE D := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, o, rfl⟩ := hw
    exact AddSubgroup.subset_closure ⟨a, ha, ⟨D.sp.cm.sig (o : D.host.E),
      (show IsIntegral ℤ (o : D.host.E) from o.2).map (D.sp.cm.sig : D.host.E →+* D.host.E).toIntAlgHom⟩, rfl⟩
  | zero => rw [RingHom.map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [RingHom.map_add]; exact add_mem hx hy
  | neg x _ hx => rw [RingHom.map_neg]; exact neg_mem hx

def form (V : HSp D) (x z : Fin V.rank → AE D) : AE D := ∑ i, ∑ j, cA D (x i) * incA D (V.gram i j) * z j

/- English proof (translation)
Simplify using `only [form, ringHom_sum, RingHom.map_mul, finPart_cA]`. Both sides reduce to the same expression.
-/
theorem finPart_form (V : HSp D) (x z : Fin V.rank → AE D) :
    finPart D (form V x z) =
      hR (Af D.host.F) D.sp.cm.sig V.gram (fun i => finPart D (x i)) fun i => finPart D (z i) := by
  simp only [form, ringHom_sum, RingHom.map_mul, finPart_cA]
  rfl

/- English proof (translation)
Simplify using `only [form, map_sum, RingHom.map_mul, cA_cA, cA_incA, GlobalTheory.LatVac.gram_star]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem cA_form (V : HSp D) (x z : Fin V.rank → AE D) : cA D (form V x z) = form V z x := by
  simp only [form, map_sum, RingHom.map_mul, cA_cA, cA_incA, GlobalTheory.LatVac.gram_star]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Simplify using `only [form, RingHom.map_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem form_mul (V : HSp D) (a b : AE D) (x z : Fin V.rank → AE D) :
    form V (fun i => a * x i) (fun i => b * z i) = cA D a * b * form V x z := by
  simp only [form, RingHom.map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Rewrite using `[(GlobalTheory.LatDual.lamHat_selfDual_and_module V).1]`. Prove the components needed by the constructor for the conclusion. Introduce `h z hz`. Rewrite using `[← cA_form, finPart_cA, finPart_form]`. Conclude with `sigR_mem_intAE (h _ hz)`.

Introduce `h z hz`. Take `⟨w, rfl⟩ : ∃ w : Fin V.rank → AE D, (fun i => finPart D (w i)) = z` from `by choose s hs using finPart_surjective (D := D)`. Conclude with `⟨fun i => s (z i), funext fun i => hs _⟩`. Rewrite using `[← finPart_form, ← cA_form, finPart_cA]`. Conclude with `sigR_mem_intAE (h _ hz)`.
-/
theorem mem_iff (V : HSp D) (x : Fin V.rank → AE D) :
    (fun i => finPart D (x i)) ∈ LamHat V ↔
      ∀ z : Fin V.rank → AE D, (fun i => finPart D (z i)) ∈ LamHat V → finPart D (form V x z) ∈ intAE D := by
  rw [(GlobalTheory.LatDual.lamHat_selfDual_and_module V).1]
  constructor
  · intro h z hz
    rw [← cA_form, finPart_cA, finPart_form]
    exact sigR_mem_intAE (h _ hz)
  · intro h z hz
    obtain ⟨w, rfl⟩ : ∃ w : Fin V.rank → AE D, (fun i => finPart D (w i)) = z := by
      choose s hs using finPart_surjective (D := D)
      exact ⟨fun i => s (z i), funext fun i => hs _⟩
    rw [← finPart_form, ← cA_form, finPart_cA]
    exact sigR_mem_intAE (h _ hz)

/- English proof (translation)
Simplify using `only [form, map_sum, RingHom.map_mul, dotProduct, vecMul, Finset.sum_mul, Matrix.map_apply]`. Conclude with `Finset.sum_comm`.
-/
theorem map_form (V : HSp D) {K : Type} [CommRing K] (π : AE D →+* K) (x z : Fin V.rank → AE D) :
    π (form V x z) =
      ((fun i => π (cA D (x i))) ᵥ* (V.gram.map fun a => π (incA D a))) ⬝ᵥ fun k => π (z k) := by
  simp only [form, map_sum, RingHom.map_mul, dotProduct, vecMul, Finset.sum_mul, Matrix.map_apply]
  exact Finset.sum_comm

/- English proof (translation)
Introduce `D e v π he hπ V β hβ y`. Rewrite using `[mem_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h j choose s hs using hπ.1`. Establish `h1 : (fun k => π (s (β.1 k j))) = β.1 *ᵥ Pi.single j 1`.

Use function extensionality and compare the values at `k`. Rewrite using `[hs, Matrix.mulVec_single_one]`. Both sides reduce to the same expression. Establish `h2` using `h _ ((hβ fun k => s (β.1 k j)).2 fun i => by`. Rewrite using `[h1, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]`.

Distinguish the cases in `hi : i = j`. Substitute `hi` using the available equality. Rewrite using `[Pi.single_eq_same]`. Conclude with `⟨1, map_one _⟩`. Rewrite using `[Pi.single_eq_of_ne hi]`.

Conclude with `⟨0, map_zero _⟩)`. Rewrite `h2` using `[form_mul, cA_cA, he.1, hπ.2.2.2, map_form, h1, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, dotProduct_single, mul_one]`. Conclude with `h2`. Introduce `h z hz`. Establish `h1` using `(GlobalTheory.LatDual.lamHat_selfDual_and_module V).2 _ (GlobalTheory.AdIdem.idempotent_mem_intAE D (finPart D e) (by rw [← RingHom.map_mul, he.1])) _ hz`.

Simplify using `only [← RingHom.map_mul] at h1`. Establish `h2` using `(hβ z).1 h1`. Establish `h3` using `form_mul V (cA D e) 1 y z`. Simplify using `only [one_mul, mul_one, cA_cA] at h3`. Establish `h4 : (fun k => π (z k)) = β.1 *ᵥ ((β⁻¹).1 *ᵥ fun k => π (z k))`.

Rewrite using `[Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`. Rewrite using `[h3, hπ.2.2.2, map_form, h4, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, isInt_iff]`. Conclude with `sum_mem fun i _ => mul_mem (isInt_iff.1 (h i)) (isInt_iff.1 (h2 i))`.
-/
theorem conj_mem_lamHat_iff : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ (V : HSp D) (β : GL (Fin V.rank) (Fv D.host.F v)), Frame V e π β → ∀ y : Fin V.rank → AE D, (fun i => finPart D (cA D e * y i)) ∈ LamHat V ↔ ∀ j, IsInt (Ov D v) (((fun i => π (cA D (y i))) ᵥ* ((V.gram.map fun a => π (incA D a)) * β.1)) j) := by
  intro D e v π he hπ V β hβ y
  rw [mem_iff]
  constructor
  · intro h j
    choose s hs using hπ.1
    have h1 : (fun k => π (s (β.1 k j))) = β.1 *ᵥ Pi.single j 1 := by
      funext k
      rw [hs, Matrix.mulVec_single_one]
      rfl
    have h2 := h _ ((hβ fun k => s (β.1 k j)).2 fun i => by
      rw [h1, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      by_cases hi : i = j
      · subst hi; rw [Pi.single_eq_same]; exact ⟨1, map_one _⟩
      · rw [Pi.single_eq_of_ne hi]; exact ⟨0, map_zero _⟩)
    rw [form_mul, cA_cA, he.1, hπ.2.2.2, map_form, h1, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      dotProduct_single, mul_one] at h2
    exact h2
  · intro h z hz
    have h1 := (GlobalTheory.LatDual.lamHat_selfDual_and_module V).2 _
      (GlobalTheory.AdIdem.idempotent_mem_intAE D (finPart D e) (by rw [← RingHom.map_mul, he.1])) _ hz
    simp only [← RingHom.map_mul] at h1
    have h2 := (hβ z).1 h1
    have h3 := form_mul V (cA D e) 1 y z
    simp only [one_mul, mul_one, cA_cA] at h3
    have h4 : (fun k => π (z k)) = β.1 *ᵥ ((β⁻¹).1 *ᵥ fun k => π (z k)) := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    rw [h3, hπ.2.2.2, map_form, h4, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, isInt_iff]
    exact sum_mem fun i _ => mul_mem (isInt_iff.1 (h i)) (isInt_iff.1 (h2 i))

end GlobalTheory.SplitDualLat

end
