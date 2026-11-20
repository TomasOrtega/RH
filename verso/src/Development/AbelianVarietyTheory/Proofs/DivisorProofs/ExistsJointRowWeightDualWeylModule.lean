import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDualWeylWeightProjectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDualWeylWeightProjector
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

set_option autoImplicit false

noncomputable section

open MvPolynomial Formalism.GradedWeylDivisibility

namespace GlobalTheory.HighWt

/- English proof (translation)
Simplify using `only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[Finset.sum_comm]`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[← Finset.mul_sum]`.

Simplify using `only [rowW, colW, Finset.sum_pi_single', Finset.mem_univ, if_true]`. Apply `Nat.mul_le_mul_left` to reduce the goal to its premises. Rewrite using `[Pi.single_apply]`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem rowWeight_le_colSum (N : ℕ) (d : Fin N × Fin N →₀ ℕ) (a : Fin N) :
    (Finsupp.weight (rowW N N) d) a ≤ ∑ s, (Finsupp.weight (colW N N) d) s := by
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  rw [← Finset.mul_sum]
  simp only [rowW, colW, Finset.sum_pi_single', Finset.mem_univ, if_true]
  apply Nat.mul_le_mul_left
  rw [Pi.single_apply]
  split_ifs <;> omega

variable (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam : ι → ℕ → ℕ)

def wtBox (τ : ι) : Finset (Fin N → ℕ) :=
  Fintype.piFinset fun _ => Finset.range (∑ s : Fin N, res N (lam τ) s + 1)

/- English proof (translation)
Establish `hc : IsWeightedHomogeneous (colW N N) f (res N (lam τ))`. Use `(Submodule.mem_inf.mp hf).1` as an intermediate fact. Simplify `this` using `[mem_weightedHomogeneousSubmodule]`. Use extensionality with `d`. Rewrite using `[coeff_sum]`.

Simplify using `only [coeff_weightedHomogeneousComponent]`. Rewrite using `[Finset.sum_ite_eq]`. Use `split_ifs with h`. Both sides reduce to the same expression. Assume the negation of the conclusion as `hne`.

Apply `h` to reduce the goal to its premises. Establish `hd` using `hc (Ne.symm hne)`. Simplify using `only [wtBox, Fintype.mem_piFinset, Finset.mem_range]`. Introduce `a`. Use `rowWeight_le_colSum N d a` as an intermediate fact.

Rewrite `this` using `[hd]`. Use linear arithmetic over natural numbers and integers.
-/
theorem sum_box (τ : ι) (f : MvPolynomial (Fin N × Fin N) O) (hf : f ∈ dualWeyl O N N (res N (lam τ))) :
    ∑ w ∈ wtBox N lam τ, weightedHomogeneousComponent (rowW N N) w f = f := by
  classical
  have hc : IsWeightedHomogeneous (colW N N) f (res N (lam τ)) := by
    have := (Submodule.mem_inf.mp hf).1
    simpa [mem_weightedHomogeneousSubmodule] using this
  ext d
  rw [coeff_sum]
  simp only [coeff_weightedHomogeneousComponent]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · by_contra hne
    apply h
    have hd := hc (Ne.symm hne)
    simp only [wtBox, Fintype.mem_piFinset, Finset.mem_range]
    intro a
    have := rowWeight_le_colSum N d a
    rw [hd] at this
    omega

section Ops

variable {O N lam}

/- English proof (translation)
Apply `PiTensorProduct.ext` to reduce the goal to its premises. Apply `MultilinearMap.ext` to reduce the goal to its premises. Introduce `x`. Simplify using `only [LinearMap.compMultilinearMap_apply, Module.End.mul_apply]`. Set `y : dualWeyl O N N (res N (lam τ))` to `rowProj O N (res N (lam τ)) w (x τ)`.

Establish `hy : (y : MvPolynomial (Fin N × Fin N) O) = weightedHomogeneousComponent (rowW N N) w (x τ : MvPolynomial _ O)` using `rfl`. Rewrite using `[h x y hy]`. Establish `hy' : (y : MvPolynomial (Fin N × Fin N) O) = weightedHomogeneousComponent (rowW N N) w ((Function.update x τ y) τ : MvPolynomial _ O)`. Rewrite using `[Function.update_self, hy, weightedHomogeneousComponent_eq_self (weightedHomogeneousComponent_isWeightedHomogeneous _ _)]`. Rewrite using `[h _ y hy', Function.update_idem]`.
-/
theorem isProj_idem {τ : ι} {w : Fin N → ℕ} {a : Module.End O (NablaT O N lam)} (h : IsProj O N lam τ w a) :
    a * a = a := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [LinearMap.compMultilinearMap_apply, Module.End.mul_apply]
  let y : dualWeyl O N N (res N (lam τ)) := rowProj O N (res N (lam τ)) w (x τ)
  have hy : (y : MvPolynomial (Fin N × Fin N) O) = weightedHomogeneousComponent (rowW N N) w (x τ : MvPolynomial _ O) := rfl
  rw [h x y hy]
  have hy' : (y : MvPolynomial (Fin N × Fin N) O) =
      weightedHomogeneousComponent (rowW N N) w ((Function.update x τ y) τ : MvPolynomial _ O) := by
    rw [Function.update_self, hy, weightedHomogeneousComponent_eq_self
      (weightedHomogeneousComponent_isWeightedHomogeneous _ _)]
  rw [h _ y hy', Function.update_idem]

/- English proof (translation)
Apply `PiTensorProduct.ext` to reduce the goal to its premises. Apply `MultilinearMap.ext` to reduce the goal to its premises. Introduce `x`. Simplify using `only [LinearMap.compMultilinearMap_apply, Module.End.mul_apply]`. Set `y : dualWeyl O N N (res N (lam τ))` to `rowProj O N (res N (lam τ)) w (x τ)`.

Set `y' : dualWeyl O N N (res N (lam τ'))` to `rowProj O N (res N (lam τ')) w' (x τ')`. Establish `hy : (y : MvPolynomial (Fin N × Fin N) O) = weightedHomogeneousComponent (rowW N N) w (x τ : MvPolynomial _ O)` using `rfl`. Establish `hy' : (y' : MvPolynomial (Fin N × Fin N) O) = weightedHomogeneousComponent (rowW N N) w' (x τ' : MvPolynomial _ O)` using `rfl`. Rewrite using `[hb x y' hy', ha x y hy]`. Establish `h1 : (y : MvPolynomial (Fin N × Fin N) O) = weightedHomogeneousComponent (rowW N N) w ((Function.update x τ' y') τ : MvPolynomial _ O)`.

Rewrite using `[Function.update_of_ne hne]`. Conclude with `hy`. Establish `h2 : (y' : MvPolynomial (Fin N × Fin N) O) = weightedHomogeneousComponent (rowW N N) w' ((Function.update x τ y) τ' : MvPolynomial _ O)`. Rewrite using `[Function.update_of_ne hne.symm]`. Conclude with `hy'`.

Rewrite using `[ha _ y h1, hb _ y' h2, Function.update_comm hne]`.
-/
theorem isProj_comm {τ τ' : ι} (hne : τ ≠ τ') {w w' : Fin N → ℕ} {a b : Module.End O (NablaT O N lam)}
    (ha : IsProj O N lam τ w a) (hb : IsProj O N lam τ' w' b) : a * b = b * a := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [LinearMap.compMultilinearMap_apply, Module.End.mul_apply]
  let y : dualWeyl O N N (res N (lam τ)) := rowProj O N (res N (lam τ)) w (x τ)
  let y' : dualWeyl O N N (res N (lam τ')) := rowProj O N (res N (lam τ')) w' (x τ')
  have hy : (y : MvPolynomial (Fin N × Fin N) O) = weightedHomogeneousComponent (rowW N N) w (x τ : MvPolynomial _ O) := rfl
  have hy' : (y' : MvPolynomial (Fin N × Fin N) O) = weightedHomogeneousComponent (rowW N N) w' (x τ' : MvPolynomial _ O) := rfl
  rw [hb x y' hy', ha x y hy]
  have h1 : (y : MvPolynomial (Fin N × Fin N) O) =
      weightedHomogeneousComponent (rowW N N) w ((Function.update x τ' y') τ : MvPolynomial _ O) := by
    rw [Function.update_of_ne hne]; exact hy
  have h2 : (y' : MvPolynomial (Fin N × Fin N) O) =
      weightedHomogeneousComponent (rowW N N) w' ((Function.update x τ y) τ' : MvPolynomial _ O) := by
    rw [Function.update_of_ne hne.symm]; exact hy'
  rw [ha _ y h1, hb _ y' h2, Function.update_comm hne]

/- English proof (translation)
Apply `PiTensorProduct.ext` to reduce the goal to its premises. Apply `MultilinearMap.ext` to reduce the goal to its premises. Introduce `x`. Rewrite using `[LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply, LinearMap.sum_apply, Module.End.one_apply]`. Establish `key : ∀ w, e w (PiTensorProduct.tprod O x) = (PiTensorProduct.tprod O).toLinearMap x τ (rowProj O N (res N (lam τ)) w (x τ))`.

Introduce `w`. Rewrite using `[MultilinearMap.toLinearMap_apply]`. Conclude with `he w x _ rfl`. Rewrite using `[Finset.sum_congr rfl (fun w _ => key w)]`. Rewrite using `[← map_sum, MultilinearMap.toLinearMap_apply]`.

Establish `: ∑ w ∈ wtBox N lam τ, rowProj O N (res N (lam τ)) w (x τ) = x τ`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Submodule.coe_sum]`. Conclude with `sum_box O N lam τ _ (x τ).2`. Rewrite using `[this, Function.update_eq_self]`.
-/
theorem isProj_sum (τ : ι) (e : (Fin N → ℕ) → Module.End O (NablaT O N lam)) (he : ∀ w, IsProj O N lam τ w (e w)) :
    ∑ w ∈ wtBox N lam τ, e w = 1 := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply, LinearMap.sum_apply, Module.End.one_apply]
  have key : ∀ w, e w (PiTensorProduct.tprod O x) =
      (PiTensorProduct.tprod O).toLinearMap x τ (rowProj O N (res N (lam τ)) w (x τ)) := by
    intro w
    rw [MultilinearMap.toLinearMap_apply]
    exact he w x _ rfl
  rw [Finset.sum_congr rfl (fun w _ => key w)]
  rw [← map_sum, MultilinearMap.toLinearMap_apply]
  have : ∑ w ∈ wtBox N lam τ, rowProj O N (res N (lam τ)) w (x τ) = x τ := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact sum_box O N lam τ _ (x τ).2
  rw [this, Function.update_eq_self]

end Ops

section Main

variable {O N lam}

def projA [Fintype ι] (τ : ι) (w : Fin N → ℕ) : alg O N lam :=
  ⟨(exists_unique_isProj O N ι lam τ w).choose,
    Algebra.subset_adjoin (Or.inr ⟨τ, w, (exists_unique_isProj O N ι lam τ w).choose_spec.1⟩)⟩

variable [Fintype ι]

/- English proof (translation)
The claim follows from `(exists_unique_isProj O N ι lam τ w).choose_spec.1`.
-/
theorem projA_isProj (τ : ι) (w : Fin N → ℕ) : IsProj O N lam τ w (projA (O := O) (lam := lam) τ w : Module.End O (NablaT O N lam)) :=
  (exists_unique_isProj O N ι lam τ w).choose_spec.1

/- English proof (translation)
The claim follows from `Subtype.ext ((exists_unique_isProj O N ι lam τ w).choose_spec.2 _ h)`.
-/
theorem projA_eq {τ : ι} {w : Fin N → ℕ} {a : alg O N lam} (h : IsProj O N lam τ w a) : a = projA τ w :=
  Subtype.ext ((exists_unique_isProj O N ι lam τ w).choose_spec.2 _ h)

/- English proof (translation)
The claim follows from `Subtype.ext (isProj_idem (projA_isProj τ w))`.
-/
theorem projA_idem (τ : ι) (w : Fin N → ℕ) : projA (O := O) (lam := lam) τ w * projA τ w = projA τ w :=
  Subtype.ext (isProj_idem (projA_isProj τ w))

/- English proof (translation)
The claim follows from `Subtype.ext (isProj_comm hne (projA_isProj τ w) (projA_isProj τ' w'))`.
-/
theorem projA_comm {τ τ' : ι} (hne : τ ≠ τ') (w w' : Fin N → ℕ) :
    projA (O := O) (lam := lam) τ w * projA τ' w' = projA τ' w' * projA τ w :=
  Subtype.ext (isProj_comm hne (projA_isProj τ w) (projA_isProj τ' w'))

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[AddSubmonoidClass.coe_finset_sum, OneMemClass.coe_one]`. Conclude with `isProj_sum τ _ (projA_isProj τ)`.
-/
theorem projA_sum (τ : ι) : ∑ w ∈ wtBox N lam τ, projA (O := O) (lam := lam) τ w = 1 := by
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finset_sum, OneMemClass.coe_one]
  exact isProj_sum τ _ (projA_isProj τ)

end Main

/- English proof (translation)
Introduce `O _ _ _ _ N ι _ _ lam Gm _ _ _`. Establish `step : ∀ s : Finset ι, ∃ z : Gm, z ≠ 0 ∧ ∃ w : ι → Fin N → ℕ, ∀ τ ∈ s, projA (O` using `O) (lam := lam) τ (w τ) • z = z := by`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`.

Take `⟨z, hz⟩` from `exists_ne (0 : Gm)`. Conclude with `⟨z, hz, 0, by simp⟩`. Consider the case `insert τ s hτ ih`. Take `⟨z, hz, w, hw⟩` from `ih`. Establish `hsum : ∑ v ∈ wtBox N lam τ, projA (O` using `O) (lam := lam) τ v • z = z := by`.

Rewrite using `[← Finset.sum_smul, projA_sum, one_smul]`. Take `⟨v, -, hv⟩` from `Finset.exists_ne_zero_of_sum_ne_zero (hsum.symm ▸ hz)`. Use `⟨projA τ v • z, hv, Function.update w τ v, ?_⟩` and prove the remaining obligations. Introduce `σ hσ`. Break down `Finset.mem_insert.mp hσ with rfl | hσ` into its components or cases.

Rewrite using `[Function.update_self, smul_smul, projA_idem]`. Establish `hne : σ ≠ τ` using `fun h => hτ (h ▸ hσ)`. Rewrite using `[Function.update_of_ne hne, smul_smul, projA_comm hne, mul_smul, hw σ hσ]`. Take `⟨z, hz, w, hw⟩` from `step Finset.univ`. Conclude with `⟨w, z, hz, fun τ a ha => by rw [projA_eq ha]; exact hw τ (Finset.mem_univ _)⟩`.
-/
theorem exists_jointWt : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι]
    [DecidableEq ι] (lam : ι → ℕ → ℕ) (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], Nontrivial Gm →
    ∃ w : ι → Fin N → ℕ, GlobalTheory.HighWt.JointWt O N lam Gm w := by
  intro O _ _ _ _ N ι _ _ lam Gm _ _ _
  have step : ∀ s : Finset ι, ∃ z : Gm, z ≠ 0 ∧ ∃ w : ι → Fin N → ℕ,
      ∀ τ ∈ s, projA (O := O) (lam := lam) τ (w τ) • z = z := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨z, hz⟩ := exists_ne (0 : Gm)
      exact ⟨z, hz, 0, by simp⟩
    | insert τ s hτ ih =>
      obtain ⟨z, hz, w, hw⟩ := ih
      have hsum : ∑ v ∈ wtBox N lam τ, projA (O := O) (lam := lam) τ v • z = z := by
        rw [← Finset.sum_smul, projA_sum, one_smul]
      obtain ⟨v, -, hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hsum.symm ▸ hz)
      refine ⟨projA τ v • z, hv, Function.update w τ v, ?_⟩
      intro σ hσ
      rcases Finset.mem_insert.mp hσ with rfl | hσ
      · rw [Function.update_self, smul_smul, projA_idem]
      · have hne : σ ≠ τ := fun h => hτ (h ▸ hσ)
        rw [Function.update_of_ne hne, smul_smul, projA_comm hne, mul_smul, hw σ hσ]
  obtain ⟨z, hz, w, hw⟩ := step Finset.univ
  exact ⟨w, z, hz, fun τ a ha => by rw [projA_eq ha]; exact hw τ (Finset.mem_univ _)⟩

end GlobalTheory.HighWt
