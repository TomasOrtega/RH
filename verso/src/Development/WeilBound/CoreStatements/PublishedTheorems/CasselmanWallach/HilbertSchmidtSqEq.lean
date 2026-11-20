import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open ReciprocityTheory.ChartRestriction.DS (actM casimirK)

namespace PositivityTheory.CW.MatrixActionLinear

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

/- English proof (translation)
Unfold `actM`. Simplify using `only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]`.
-/
theorem actM_add (A : Fin n → Fin n → Module.End ℂ M) (X Y : Mx n) : actM A (X + Y) = actM A X + actM A Y := by
  unfold actM
  simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]

/- English proof (translation)
Unfold `actM`. Simplify using `only [Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]`.
-/
theorem actM_smul (A : Fin n → Fin n → Module.End ℂ M) (c : ℂ) (X : Mx n) : actM A (c • X) = c • actM A X := by
  unfold actM
  simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

/- English proof (translation)
Unfold `actM`. Rewrite using `[Finset.sum_eq_single a]`. Rewrite using `[Finset.sum_eq_single b]`. Simplify using the standard rewrite rules. Introduce `d _ hd`.

Simplify using `[Ne.symm hd]`. Simplify using the standard rewrite rules. Introduce `c _ hc`. Use `Finset.sum_eq_zero fun d _ => ?_` and prove the remaining obligations. Simplify using `[Ne.symm hc]`.

Simplify using the standard rewrite rules.
-/
theorem actM_single (A : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) : actM A (Matrix.single a b 1) = A a b := by
  classical
  unfold actM
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro d _ hd
      simp [Ne.symm hd]
    · simp
  · intro c _ hc
    refine Finset.sum_eq_zero fun d _ => ?_
    simp [Ne.symm hc]
  · simp

end PositivityTheory.CW.MatrixActionLinear

namespace PositivityTheory.CW

open MatrixActionLinear in
/- English proof (translation)
Introduce `n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ A hA T hT m`. Use `haveI : IsTopologicalAddGroup E := hπ.withSeminorms.topologicalAddGroup`. Use `haveI : ContinuousSMul ℂ E := hπ.withSeminorms.continuousSMul`. Set `P : Module.End ℂ (kfin ε σ) → Prop` to `fun u => ∃ D : E →L[ℂ] E, ∀ v : kfin ε σ, T ((u v : kfin ε σ) : H) = D (T v)`. Establish `hone : P 1` using `⟨1, fun v => rfl⟩`.

Establish `hadd : ∀ u₁ u₂, P u₁ → P u₂ → P (u₁ + u₂)`. Introduce and unpack `u₁ u₂ ⟨D₁, h₁⟩ ⟨D₂, h₂⟩`. Use `⟨D₁ + D₂, fun v => ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.add_apply, Submodule.coe_add, map_add, h₁, h₂, _root_.add_apply]`. Establish `hmul : ∀ u₁ u₂, P u₁ → P u₂ → P (u₁ * u₂)`.

Introduce and unpack `u₁ u₂ ⟨D₁, h₁⟩ ⟨D₂, h₂⟩`. Use `⟨D₁.comp D₂, fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[Module.End.mul_apply, h₁, h₂]`. Both sides reduce to the same expression. Establish `hzero : P 0` using `⟨0, fun v => by simp⟩`.

Establish `hsum : ∀ (s : Finset (Fin n)) (f : Fin n → Module.End ℂ (kfin ε σ)), (∀ i ∈ s, P (f i)) → P (∑ i ∈ s, f i)`. Introduce `s f hf`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using hzero`. Consider the case `insert a s ha ih`.

Rewrite using `[Finset.sum_insert ha]`. Conclude with `hadd _ _ (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))`. Establish `hgen : ∀ a b, P (A a b)`. Introduce `a b`. Take `⟨h1, h2, h3, -⟩` from `complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)`.

Use `set X₁ := cpart1 ε (Matrix.single a b 1)`. Use `set X₂ := cpart2 ε (Matrix.single a b 1)`. Establish `hX₁ : X₁ ∈ lieSet ε` using `h1`. Establish `hX₂ : X₂ ∈ lieSet ε` using `h2`. Establish `eA : A a b = actM A X₁ + Complex.I • actM A X₂`.

Rewrite using `[← actM_single A a b, h3, actM_add, actM_smul]`. Use `⟨dπ X₁ + Complex.I • dπ X₂, fun v => ?_⟩` and prove the remaining obligations. Establish `hv : IsKFin ε σ (v : H)` using `v.2`. Rewrite using `[eA, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul, hA X₁ hX₁ v, hA X₂ hX₂ v, map_add, map_smul, hT X₁ hX₁ v hv, hT X₂ hX₂ v hv]`. Both sides reduce to the same expression.

Establish `hcas : P (casimirK ε A)`. Unfold `casimirK`. Conclude with `hsum _ _ fun a _ => hsum _ _ fun b _ => hmul _ _ (hgen a b) (hgen b a)`. Establish `hpow : ∀ k : ℕ, P ((1 + casimirK ε A) ^ k)`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => simpa using hone`. Consider the case `succ k ih => rw [pow_succ]`. Conclude with `hmul _ _ ih (hadd _ _ hone hcas)`. Conclude with `hpow m`.
-/
theorem e3b : faceMap_castSucc_comp_eq_succ := by
  classical
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ A hA T hT m
  haveI : IsTopologicalAddGroup E := hπ.withSeminorms.topologicalAddGroup
  haveI : ContinuousSMul ℂ E := hπ.withSeminorms.continuousSMul

  let P : Module.End ℂ (kfin ε σ) → Prop := fun u => ∃ D : E →L[ℂ] E, ∀ v : kfin ε σ, T ((u v : kfin ε σ) : H) = D (T v)
  have hone : P 1 := ⟨1, fun v => rfl⟩
  have hadd : ∀ u₁ u₂, P u₁ → P u₂ → P (u₁ + u₂) := by
    rintro u₁ u₂ ⟨D₁, h₁⟩ ⟨D₂, h₂⟩
    refine ⟨D₁ + D₂, fun v => ?_⟩
    simp only [LinearMap.add_apply, Submodule.coe_add, map_add, h₁, h₂, _root_.add_apply]
  have hmul : ∀ u₁ u₂, P u₁ → P u₂ → P (u₁ * u₂) := by
    rintro u₁ u₂ ⟨D₁, h₁⟩ ⟨D₂, h₂⟩
    refine ⟨D₁.comp D₂, fun v => ?_⟩
    rw [Module.End.mul_apply, h₁, h₂]
    rfl
  have hzero : P 0 := ⟨0, fun v => by simp⟩
  have hsum : ∀ (s : Finset (Fin n)) (f : Fin n → Module.End ℂ (kfin ε σ)), (∀ i ∈ s, P (f i)) → P (∑ i ∈ s, f i) := by
    intro s f hf
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact hadd _ _ (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
  have hgen : ∀ a b, P (A a b) := by
    intro a b
    obtain ⟨h1, h2, h3, -⟩ := complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
    set X₁ := cpart1 ε (Matrix.single a b 1)
    set X₂ := cpart2 ε (Matrix.single a b 1)
    have hX₁ : X₁ ∈ lieSet ε := h1
    have hX₂ : X₂ ∈ lieSet ε := h2
    have eA : A a b = actM A X₁ + Complex.I • actM A X₂ := by
      rw [← actM_single A a b, h3, actM_add, actM_smul]
    refine ⟨dπ X₁ + Complex.I • dπ X₂, fun v => ?_⟩
    have hv : IsKFin ε σ (v : H) := v.2
    rw [eA, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul, hA X₁ hX₁ v,
      hA X₂ hX₂ v, map_add, map_smul, hT X₁ hX₁ v hv, hT X₂ hX₂ v hv]
    rfl
  have hcas : P (casimirK ε A) := by
    unfold casimirK
    exact hsum _ _ fun a _ => hsum _ _ fun b _ => hmul _ _ (hgen a b) (hgen b a)
  have hpow : ∀ k : ℕ, P ((1 + casimirK ε A) ^ k) := by
    intro k
    induction k with
    | zero => simpa using hone
    | succ k ih => rw [pow_succ]; exact hmul _ _ ih (hadd _ _ hone hcas)
  exact hpow m

end PositivityTheory.CW

end
