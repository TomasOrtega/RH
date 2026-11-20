import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ExistsLieCompl

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal Formalism.MainNotions.S
open scoped TensorProduct Matrix

def wV {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (v : NumberField.InfinitePlace X.B.I.F)
    (b : Fin (D.R.rS + 1 + D.R.rS)) : Fin X.B.I.n → ℂ :=
  (X.B.I.P v)⁻¹ *ᵥ fun i => X.B.I.φ v (tupH (frameOf X u') b i)

def StabInfV : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
    (x : X.B.I.Ginf), X.toInf hb x ∈ MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u') ↔
      ∀ v b, uMat (x v) *ᵥ wV X u' v b = wV X u' v b

def WittBlock : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf → ∀ v : NumberField.InfinitePlace X.B.I.F,
    ∃ (S : Finset (Fin X.B.I.n)) (c : Formalism.REAL.UJ (X.B.I.ε v)),
      (S.card = D.R.k ∧ ∀ i ∈ S, X.B.I.ε v i = true) ∧
      Submodule.span ℂ (Set.range fun b => uMat c⁻¹ *ᵥ wV X u' v b) =
        Submodule.span ℂ ((fun i => (Pi.single i 1 : Fin X.B.I.n → ℂ)) '' (↑S)ᶜ)

/- English proof (translation)
Establish `hker : ∀ x, A *ᵥ x = x ↔ x ∈ LinearMap.ker (Matrix.toLin' (A - 1))`. Introduce `x`. Rewrite using `[LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]`. Establish `e1 : (∀ b, A *ᵥ u b = u b) ↔ Submodule.span ℂ (Set.range u) ≤ LinearMap.ker (Matrix.toLin' (A - 1))`. Rewrite using `[Submodule.span_le]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `h _ ⟨b, rfl⟩`. Conclude with `(hker _).1 (h b)`. Introduce `h b`. Conclude with `(hker _).2 (h ⟨b, rfl⟩)`.

Rewrite using `[e1, hspan, Submodule.span_le]`. Prove the components needed by the constructor for the conclusion. Introduce `h i hi j`. Establish `h1` using `(hker _).2 (h ⟨i, hi, rfl⟩)`. Rewrite `h1` using `[Matrix.mulVec_single_one]`.

Use `congrFun h1 j` as an intermediate fact. Simplify using `only [Matrix.col_apply, Pi.single_apply] at this`. Conclude with `this`. Introduce and unpack `h _ ⟨i, hi, rfl⟩`. Use `(hker _).1 ?_` and prove the remaining obligations.

Rewrite using `[Matrix.mulVec_single_one]`. Use function extensionality and compare the values at `j`. Simplify using `only [Matrix.col_apply, Pi.single_apply]`. Conclude with `h i hi j`.
-/
theorem fix_iff_span {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) {ι : Type} (u : ι → Fin n → ℂ) (S : Finset (Fin n))
    (hspan : Submodule.span ℂ (Set.range u) =
      Submodule.span ℂ ((fun i => (Pi.single i 1 : Fin n → ℂ)) '' (↑S)ᶜ)) :
    (∀ b, A *ᵥ u b = u b) ↔ ∀ i ∉ S, ∀ j, A j i = if j = i then 1 else 0 := by
  classical
  have hker : ∀ x, A *ᵥ x = x ↔ x ∈ LinearMap.ker (Matrix.toLin' (A - 1)) := by
    intro x
    rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
  have e1 : (∀ b, A *ᵥ u b = u b) ↔ Submodule.span ℂ (Set.range u) ≤ LinearMap.ker (Matrix.toLin' (A - 1)) := by
    rw [Submodule.span_le]
    constructor
    · rintro h _ ⟨b, rfl⟩; exact (hker _).1 (h b)
    · intro h b; exact (hker _).2 (h ⟨b, rfl⟩)
  rw [e1, hspan, Submodule.span_le]
  constructor
  · intro h i hi j
    have h1 := (hker _).2 (h ⟨i, hi, rfl⟩)
    rw [Matrix.mulVec_single_one] at h1
    have := congrFun h1 j
    simp only [Matrix.col_apply, Pi.single_apply] at this
    exact this
  · rintro h _ ⟨i, hi, rfl⟩
    refine (hker _).1 ?_
    rw [Matrix.mulVec_single_one]
    funext j
    simp only [Matrix.col_apply, Pi.single_apply]
    exact h i hi j

/- English proof (translation)
Introduce `D X u' ψ hT μinf νinf fibInf hP hb`. Establish `h2'` using `h2 X u' ψ hT μinf νinf fibInf hP`. Use `choose S c hS hspan using h2'`. Use `⟨c, S, fun v => hS v, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[h1 X u' hb (c * g * c⁻¹)]`.

Use `forall_congr' fun v => ?_` and prove the remaining obligations. Use `Iff.trans ?_ (fix_iff_span (uMat (g v)) (fun b => uMat (c v)⁻¹ *ᵥ wV X u' v b) (S v) (hspan v))` and prove the remaining obligations. Use `forall_congr' fun b => ?_` and prove the remaining obligations. Establish `hm : uMat ((c * g * c⁻¹) v) = uMat (c v) * uMat (g v) * uMat (c v)⁻¹`. Simplify using `[uMat]`.

Establish `hci : uMat (c v)⁻¹ * uMat (c v) = 1` using `by simp [uMat]`. Establish `hci' : uMat (c v) * uMat (c v)⁻¹ = 1` using `by simp [uMat]`. Rewrite using `[hm]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Establish `h'` using `congrArg (fun y => uMat (c v)⁻¹ *ᵥ y) h`. Simplify using `only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hci, Matrix.one_mul] at h'`. Rewrite using `[Matrix.mulVec_mulVec]`. Conclude with `h'`. Introduce `h`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mulVec_mulVec, Matrix.mul_assoc]`. Use `_ = uMat (c v) *ᵥ (uMat (c v)⁻¹ *ᵥ wV X u' v b) := by rw [h]`. Use `_ = wV X u' v b := by rw [Matrix.mulVec_mulVec, hci', Matrix.one_mulVec]`.
-/
theorem stdConjEx_of (h1 : StabInfV) (h2 : WittBlock) : StdConjEx := by
  intro D X u' ψ hT μinf νinf fibInf hP hb
  have h2' := h2 X u' ψ hT μinf νinf fibInf hP
  choose S c hS hspan using h2'
  refine ⟨c, S, fun v => hS v, fun g => ?_⟩
  rw [h1 X u' hb (c * g * c⁻¹)]
  refine forall_congr' fun v => ?_
  refine Iff.trans ?_ (fix_iff_span (uMat (g v)) (fun b => uMat (c v)⁻¹ *ᵥ wV X u' v b) (S v) (hspan v))
  refine forall_congr' fun b => ?_
  have hm : uMat ((c * g * c⁻¹) v) = uMat (c v) * uMat (g v) * uMat (c v)⁻¹ := by
    simp [uMat]
  have hci : uMat (c v)⁻¹ * uMat (c v) = 1 := by simp [uMat]
  have hci' : uMat (c v) * uMat (c v)⁻¹ = 1 := by simp [uMat]
  rw [hm]
  constructor
  · intro h
    have h' := congrArg (fun y => uMat (c v)⁻¹ *ᵥ y) h
    simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hci, Matrix.one_mul] at h'
    rw [Matrix.mulVec_mulVec]
    exact h'
  · intro h
    calc (uMat (c v) * uMat (g v) * uMat (c v)⁻¹) *ᵥ wV X u' v b
        = uMat (c v) *ᵥ (uMat (g v) *ᵥ (uMat (c v)⁻¹ *ᵥ wV X u' v b)) := by
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = uMat (c v) *ᵥ (uMat (c v)⁻¹ *ᵥ wV X u' v b) := by rw [h]
      _ = wV X u' v b := by rw [Matrix.mulVec_mulVec, hci', Matrix.one_mulVec]

end PI.AprimeInfW
