import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.RadEmb

/- English proof (translation)
Simplify using `[Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]`.
-/
theorem hform_eq_dot {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    Formalism.UG.hform (starRingEnd ℂ) A x y = star x ⬝ᵥ (A *ᵥ y) := by
  simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Establish `e : star x ⬝ᵥ (Jm ε *ᵥ y) = star (Formalism.QuantumDeterminants.herm (Jm ε) x y)`. Simplify using `only [Formalism.QuantumDeterminants.herm, Jm, dotProduct, Matrix.mulVec_diagonal, star_sum, Pi.star_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp [mul_comm]`. Rewrite using `[← e, ← h, hform_eq_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]`.
-/
theorem hform_frame {n : ℕ} {ε : Fin n → Bool} {A P : Matrix (Fin n) (Fin n) ℂ} (h : Pᴴ * A * P = Jm ε)
    (x y : Fin n → ℂ) :
    Formalism.UG.hform (starRingEnd ℂ) A (P *ᵥ x) (P *ᵥ y) = star (Formalism.QuantumDeterminants.herm (Jm ε) x y) := by
  have e : star x ⬝ᵥ (Jm ε *ᵥ y) = star (Formalism.QuantumDeterminants.herm (Jm ε) x y) := by
    simp only [Formalism.QuantumDeterminants.herm, Jm, dotProduct, Matrix.mulVec_diagonal, star_sum, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp [mul_comm]
  rw [← e, ← h, hform_eq_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec]

/- English proof (translation)
Use `⟨fun x _ => by simp, fun y _ => by simp, fun y x _ => by simp [Formalism.UG.hform]⟩` and prove the remaining obligations.
-/
theorem inUnipRad_one (I : AutInst) {A : Type} [CommRing A] (s : A →+* A) (JA : Matrix (Fin I.n) (Fin I.n) A)
    (WA : Submodule A (Fin I.n → A)) : I.InUnipRad s JA WA 1 := by
  refine ⟨fun x _ => by simp, fun y _ => by simp, fun y x _ => by simp [Formalism.UG.hform]⟩

/- English proof (translation)
Establish `hφ : ∀ a, I.φ v (starRingEnd I.E a) = starRingEnd ℂ (I.φ v a)` using `fun a => I.cm.cmUnram.2.1 _ a`. Introduce `x hx y hy`. Rewrite using `[hform_eq_dot]`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨a, ha, rfl⟩` from `hx`. Take `⟨b, hb, rfl⟩` from `hy`. Use `congrArg (I.φ v) (hW.2 a ha b hb)` as an intermediate fact.

Rewrite using `[← hform_eq_dot]`. Simplify `this` using `only [Formalism.UG.hform, map_sum, map_mul, hφ, map_zero, Matrix.map_apply]`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [Matrix.mulVec_add, dotProduct_add, ha, hb, add_zero]`. Consider the case `smul c a _ ha => rw [Matrix.mulVec_smul, dotProduct_smul, ha, smul_zero]`.

Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [star_add, add_dotProduct, ha, hb, add_zero]`. Consider the case `smul c a _ ha => rw [star_smul, smul_dotProduct, ha, smul_zero]`.
-/
theorem span_isot (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) (v : InfinitePlace I.F) (hW : I.IsIsot W) :
    ∀ x ∈ Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (W : Set _)),
    ∀ y ∈ Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (W : Set _)),
      Formalism.UG.hform (starRingEnd ℂ) (I.J.map (I.φ v)) x y = 0 := by
  have hφ : ∀ a, I.φ v (starRingEnd I.E a) = starRingEnd ℂ (I.φ v a) := fun a => I.cm.cmUnram.2.1 _ a
  intro x hx y hy
  rw [hform_eq_dot]
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      have := congrArg (I.φ v) (hW.2 a ha b hb)
      rw [← hform_eq_dot]
      simpa only [Formalism.UG.hform, map_sum, map_mul, hφ, map_zero, Matrix.map_apply] using this
    | zero => simp
    | add a b _ _ ha hb => rw [Matrix.mulVec_add, dotProduct_add, ha, hb, add_zero]
    | smul c a _ ha => rw [Matrix.mulVec_smul, dotProduct_smul, ha, smul_zero]
  | zero => simp
  | add a b _ _ ha hb => rw [star_add, add_dotProduct, ha, hb, add_zero]
  | smul c a _ ha => rw [star_smul, smul_dotProduct, ha, smul_zero]

/- English proof (translation)
Introduce `I W v hW`. Establish `hP : ∀ u, I.P u * (I.P u)⁻¹ = 1` using `fun u => Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit u))`. Establish `hQ : ∀ y, I.P v *ᵥ ((I.P v)⁻¹ *ᵥ y) = y` using `fun y => by`. Rewrite using `[Matrix.mulVec_mulVec, hP, Matrix.one_mulVec]`. Use `set WA := Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (W : Set _)) with hWA`.

Establish `hf` using `hform_frame (I.P_spec v)`. Use `⟨WA.comap (I.P v).mulVecLin, ⟨?_, fun x hx y hy => ?_⟩, fun m hm => ⟨fun u => ?_, ?_⟩⟩` and prove the remaining obligations. Introduce `h`. Apply `hW.1` to reduce the goal to its premises. Rewrite using `[eq_bot_iff]`.

Introduce `w hw`. Establish `h1 : (I.P v)⁻¹ *ᵥ (fun i => I.φ v (w i)) ∈ WA.comap (I.P v).mulVecLin`. Rewrite using `[Submodule.mem_comap, Matrix.mulVecLin_apply, hQ]`. Conclude with `Submodule.subset_span ⟨w, hw, rfl⟩`. Rewrite `h1` using `[h, Submodule.mem_bot]`.

Establish `h2` using `hQ (fun i => I.φ v (w i))`. Rewrite `h2` using `[h1, Matrix.mulVec_zero]`. Rewrite using `[Submodule.mem_bot]`. Use function extensionality and compare the values at `i`. Conclude with `(map_eq_zero (I.φ v)).1 (congrFun h2 i).symm`.

Use `span_isot I W v hW _ hx _ hy` as an intermediate fact. Simplify using `only [Matrix.mulVecLin_apply] at this`. Rewrite `this` using `[hf]`. Conclude with `star_eq_zero.1 this`. Distinguish the cases in `hu : u = v`.

Substitute `hu` using the available equality. Simplify using `only [Pi.mulSingle_eq_same]`. Establish `e : ∀ y, (I.P u * uMat m * (I.P u)⁻¹ - 1) *ᵥ y = I.P u *ᵥ ((umat m - 1) *ᵥ ((I.P u)⁻¹ *ᵥ y))`. Introduce `y`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hP]`.

Establish `mem : ∀ x ∈ WA, (I.P u)⁻¹ *ᵥ x ∈ WA.comap (I.P u).mulVecLin` using `fun x hx => by`. Rewrite using `[Submodule.mem_comap, Matrix.mulVecLin_apply, hQ]`. Conclude with `hx`. Use `⟨fun x hx => ?_, fun y hy => ?_, fun y x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[e, hm.1 _ (mem x hx), Matrix.mulVec_zero]`.

Rewrite using `[e]`. Use `hm.2.1 _ fun x hx => ?_` and prove the remaining obligations. Use `hy _ hx` as an intermediate fact. Rewrite `this` using `[← hQ y, Matrix.mulVecLin_apply, hf]`. Conclude with `star_eq_zero.1 this`.

Rewrite using `[e, ← hQ x, hf, hm.2.2 _ _ (mem x hx), star_zero]`. Establish `e : uMat ((Pi.mulSingle v m : I.Ginf) u) = 1`. Rewrite using `[Pi.mulSingle_eq_of_ne hu]`. Both sides reduce to the same expression. Simplify using `only [e, Matrix.mul_one, hP]`.

Conclude with `inUnipRad_one I _ _ _`. Conclude with `inUnipRad_one I _ _ _`.
-/
theorem radical_embeds : ∀ (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) (v : InfinitePlace I.F), I.IsIsot W →
    ∃ Wv : Submodule ℂ (Fin I.n → ℂ), IsIsoC (I.ε v) Wv ∧
      ∀ m ∈ NW (I.ε v) Wv, (open Classical in ((Pi.mulSingle v m, 1) : I.GA)) ∈ I.NA W := by
  classical
  intro I W v hW
  have hP : ∀ u, I.P u * (I.P u)⁻¹ = 1 := fun u =>
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit u))
  have hQ : ∀ y, I.P v *ᵥ ((I.P v)⁻¹ *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, hP, Matrix.one_mulVec]
  set WA := Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (W : Set _)) with hWA
  have hf := hform_frame (I.P_spec v)
  refine ⟨WA.comap (I.P v).mulVecLin, ⟨?_, fun x hx y hy => ?_⟩, fun m hm => ⟨fun u => ?_, ?_⟩⟩
  · intro h
    apply hW.1
    rw [eq_bot_iff]
    intro w hw
    have h1 : (I.P v)⁻¹ *ᵥ (fun i => I.φ v (w i)) ∈ WA.comap (I.P v).mulVecLin := by
      rw [Submodule.mem_comap, Matrix.mulVecLin_apply, hQ]
      exact Submodule.subset_span ⟨w, hw, rfl⟩
    rw [h, Submodule.mem_bot] at h1
    have h2 := hQ (fun i => I.φ v (w i))
    rw [h1, Matrix.mulVec_zero] at h2
    rw [Submodule.mem_bot]
    funext i
    exact (map_eq_zero (I.φ v)).1 (congrFun h2 i).symm
  · have := span_isot I W v hW _ hx _ hy
    simp only [Matrix.mulVecLin_apply] at this
    rw [hf] at this
    exact star_eq_zero.1 this
  · by_cases hu : u = v
    · subst hu
      simp only [Pi.mulSingle_eq_same]
      have e : ∀ y, (I.P u * uMat m * (I.P u)⁻¹ - 1) *ᵥ y = I.P u *ᵥ ((umat m - 1) *ᵥ ((I.P u)⁻¹ *ᵥ y)) := by
        intro y
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hP]
      have mem : ∀ x ∈ WA, (I.P u)⁻¹ *ᵥ x ∈ WA.comap (I.P u).mulVecLin := fun x hx => by
        rw [Submodule.mem_comap, Matrix.mulVecLin_apply, hQ]; exact hx
      refine ⟨fun x hx => ?_, fun y hy => ?_, fun y x hx => ?_⟩
      · rw [e, hm.1 _ (mem x hx), Matrix.mulVec_zero]
      · rw [e]
        refine hm.2.1 _ fun x hx => ?_
        have := hy _ hx
        rw [← hQ y, Matrix.mulVecLin_apply, hf] at this
        exact star_eq_zero.1 this
      · rw [e, ← hQ x, hf, hm.2.2 _ _ (mem x hx), star_zero]
    · have e : uMat ((Pi.mulSingle v m : I.Ginf) u) = 1 := by
        rw [Pi.mulSingle_eq_of_ne hu]; rfl
      simp only [e, Matrix.mul_one, hP]
      exact inUnipRad_one I _ _ _
  · exact inUnipRad_one I _ _ _

end GlobalTheory.RadEmb
