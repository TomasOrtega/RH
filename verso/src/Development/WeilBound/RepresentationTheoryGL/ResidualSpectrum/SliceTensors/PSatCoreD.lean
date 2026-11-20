import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSatCoreB
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDiscreteUOfIsDiscrete

noncomputable section

open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.SmGL GlobalTheory.CuspRep
open scoped TensorProduct

namespace PositivityTheory.Rg.Rs.SatakeVectors.Core

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

/- English proof (translation)
Establish `hK` using `Final.GLintComm E w N`. Rewrite using `[heckeVec, heckeVec]`. Establish `e1` using `((LinearMap.proj (R := ℂ) (φ := fun _ : GA E N => ℂ) y).comp (Sm E N).subtype).toAddMonoidHom.map_finsum (finite_heckeVec hK hf ((finRep E N).comp (locGL E N w)) F)`. Establish `e2` using `(LinearMap.proj (R := ℂ) (φ := fun _ : GL (Fin N) (w.adicCompletion E) => ℂ) (1 : GL (Fin N) (w.adicCompletion E))).toAddMonoidHom.map_finsum (finite_heckeVec hK hf (rightReg ℂ _ ℂ) (fun g => F.1 (y * finGL E N (locGL E N w g))))`. Use `e1.trans (Eq.trans (finsum_congr fun c => ?_) e2.symm)` and prove the remaining obligations.

Use `show f c.out • F.1 (y * finGL E N (locGL E N w c.out)) = f c.out • F.1 (y * finGL E N (locGL E N w (1 * c.out)))`. Rewrite using `[one_mul]`.
-/
theorem heckeVec_apply {N : ℕ} (w : HeightOneSpectrum (𝓞 E)) {F : Sm E N}
    {f : GL (Fin N) (w.adicCompletion E) → ℂ} (hf : f ∈ Hecke ℂ (KGL w N)) (y : GA E N) :
    (heckeVec ((finRep E N).comp (locGL E N w)) (KGL w N) f F).1 y =
      heckeVec (rightReg ℂ _ ℂ) (KGL w N) f (fun g => F.1 (y * finGL E N (locGL E N w g))) 1 := by
  have hK := Final.GLintComm E w N
  rw [heckeVec, heckeVec]
  have e1 := ((LinearMap.proj (R := ℂ) (φ := fun _ : GA E N => ℂ) y).comp (Sm E N).subtype).toAddMonoidHom.map_finsum
    (finite_heckeVec hK hf ((finRep E N).comp (locGL E N w)) F)
  have e2 := (LinearMap.proj (R := ℂ) (φ := fun _ : GL (Fin N) (w.adicCompletion E) => ℂ)
    (1 : GL (Fin N) (w.adicCompletion E))).toAddMonoidHom.map_finsum
    (finite_heckeVec hK hf (rightReg ℂ _ ℂ) (fun g => F.1 (y * finGL E N (locGL E N w g))))
  refine e1.trans (Eq.trans (finsum_congr fun c => ?_) e2.symm)
  show f c.out • F.1 (y * finGL E N (locGL E N w c.out)) = f c.out • F.1 (y * finGL E N (locGL E N w (1 * c.out)))
  rw [one_mul]

def evAt {m : ℕ} (U : Submodule ℂ (Sm E m)) (x : GA E m) : U →ₗ[ℂ] ℂ :=
  LinearMap.proj x ∘ₗ (Sm E m).subtype ∘ₗ U.subtype

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem evAt_apply {m : ℕ} (U : Submodule ℂ (Sm E m)) (x : GA E m) (ψ : U) : evAt U x ψ = ψ.1.1 x := rfl

/- English proof (translation)
Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨φ, rfl⟩` from `hx`. Conclude with `⟨PiTensorProduct.tprod ℂ φ, fun m => by rw [evT_tprod]; rfl⟩`. Consider the case `zero => exact ⟨0, fun m => by simp⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨v, hv⟩` from `hx`. Take `⟨v', hv'⟩` from `hy`. Conclude with `⟨v + v', fun m => by rw [Pi.add_apply, hv, hv', map_add]⟩`. Consider the case `smul a x _ hx`.

Take `⟨v, hv⟩` from `hx`. Conclude with `⟨a • v, fun m => by rw [Pi.smul_apply, hv, map_smul, smul_eq_mul]⟩`.
-/
theorem exists_tensor {c : ℕ} {n : Fin c → ℕ} (U : ∀ i, Submodule ℂ (Sm E (n i)))
    {Φ : (∀ i, GA E (n i)) → ℂ} (hΦ : Φ ∈ GlobalTheory.BCWords.tensorSp U) :
    ∃ v : ⨂[ℂ] i, U i, ∀ m, Φ m = evT (fun i => evAt (U i) (m i)) v := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, rfl⟩ := hx
    exact ⟨PiTensorProduct.tprod ℂ φ, fun m => by rw [evT_tprod]; rfl⟩
  | zero => exact ⟨0, fun m => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨v, hv⟩ := hx
    obtain ⟨v', hv'⟩ := hy
    exact ⟨v + v', fun m => by rw [Pi.add_apply, hv, hv', map_add]⟩
  | smul a x _ hx =>
    obtain ⟨v, hv⟩ := hx
    exact ⟨a • v, fun m => by rw [Pi.smul_apply, hv, map_smul, smul_eq_mul]⟩

end PositivityTheory.Rg.Rs.SatakeVectors.Core

end
