import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

open scoped TensorProduct
open MvPolynomial

noncomputable section

namespace GlobalTheory.CompanionTheory.DSCover

open Formalism.REAL (GlRel)
open CompanionTheory.D.DSIC

/- English proof (translation)
Introduce `a b c d`. Establish `h1` using `hE a b c d`. Establish `h2` using `hF a b c d`. Establish `h3` using `h a b c d`. Establish `h4` using `h c d a b`.

Establish `e : (E a b + F a b) * (E c d + F c d) - (E c d + F c d) * (E a b + F a b) = (E a b * E c d - E c d * E a b) + (F a b * F c d - F c d * F a b)`. Simplify using `only [add_mul, mul_add, h3, h4]`. Normalize the expressions using the abelian group laws. Use `beta_reduce`. Rewrite using `[e, h1, h2]`.

Apply the tactic sequence `split_ifs <;> abel`.
-/
theorem glRel_add {A : Type} [Ring A] {n : ℕ} {E F : Fin n → Fin n → A} (hE : GlRel E) (hF : GlRel F)
    (h : ∀ a b c d, E a b * F c d = F c d * E a b) : GlRel fun a b => E a b + F a b := by
  intro a b c d
  have h1 := hE a b c d
  have h2 := hF a b c d
  have h3 := h a b c d
  have h4 := h c d a b
  have e : (E a b + F a b) * (E c d + F c d) - (E c d + F c d) * (E a b + F a b) =
      (E a b * E c d - E c d * E a b) + (F a b * F c d - F c d * F a b) := by
    simp only [add_mul, mul_add, h3, h4]
    abel
  beta_reduce
  rw [e, h1, h2]
  split_ifs <;> abel

/- English proof (translation)
Introduce `a b c d`. Establish `h` using `congrArg φ (hE a b c d)`. Simplify using `only [map_sub, map_mul] at h`. Rewrite using `[h]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem glRel_map {A B : Type} [Ring A] [Ring B] (φ : A →+* B) {n : ℕ} {E : Fin n → Fin n → A} (hE : GlRel E) :
    GlRel fun a b => φ (E a b) := by
  intro a b c d
  have h := congrArg φ (hE a b c d)
  simp only [map_sub, map_mul] at h
  rw [h]
  split_ifs <;> simp

section Pol

variable {σ : Type}

def pd (i : σ) : Module.End ℂ (MvPolynomial σ ℂ) := (pderiv i : Derivation ℂ (MvPolynomial σ ℂ) _).toLinearMap

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pd_apply (i : σ) (f : MvPolynomial σ ℂ) : pd i f = pderiv i f := rfl

/- English proof (translation)
Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `f`. Simplify using `only [Module.End.mul_apply, pd_apply]`. Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp`.

Consider the case `add p q hp hq => simp [hp, hq]`. Consider the case `mul_X p k hp`. Simplify using `only [Derivation.leibniz, map_add, smul_eq_mul, pderiv_X, hp]`. Apply the tactic sequence `by_cases h1 : i = k <;> by_cases h2 : j = k <;> simp [h1, h2, add_comm]`.
-/
theorem pd_comm (i j : σ) : pd i * pd j = pd j * pd i := by
  classical
  apply LinearMap.ext
  intro f
  simp only [Module.End.mul_apply, pd_apply]
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p k hp =>
    simp only [Derivation.leibniz, map_add, smul_eq_mul, pderiv_X, hp]
    by_cases h1 : i = k <;> by_cases h2 : j = k <;> simp [h1, h2, add_comm]

/- English proof (translation)
Proceed by induction on `l using List.reverseRecOn with`. Consider the case `nil => intro s c h`. Simplify using `at h`. Consider the case `append_singleton l i ih`. Introduce `s c h`.

Rewrite using `[List.map_append, List.prod_append]`. Simplify using `only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, Module.End.mul_apply, pd_apply, pderiv_monomial]`. Distinguish the cases in `hs : s i = 0`. Simplify using `[hs]`. Apply `ih` to reduce the goal to its premises.

Establish `e : s = (s - Finsupp.single i 1) + Finsupp.single i 1`. Rewrite using `[tsub_add_cancel_of_le]`. Rewrite using `[Finsupp.single_le_iff]`. Use linear arithmetic over natural numbers and integers. Establish `e2` using `congrArg Finsupp.degree e`.

Rewrite `e2` using `[map_add, Finsupp.degree_single]`. Simplify using `only [List.length_append, List.length_singleton] at h`. Use linear arithmetic over natural numbers and integers.
-/
theorem word_monomial (l : List σ) : ∀ (s : σ →₀ ℕ) (c : ℂ), s.degree < l.length →
    (l.map pd).prod (monomial s c) = 0 := by
  induction l using List.reverseRecOn with
  | nil => intro s c h; simp at h
  | append_singleton l i ih =>
    intro s c h
    rw [List.map_append, List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, Module.End.mul_apply, pd_apply,
      pderiv_monomial]
    by_cases hs : s i = 0
    · simp [hs]
    · apply ih
      have e : s = (s - Finsupp.single i 1) + Finsupp.single i 1 := by
        rw [tsub_add_cancel_of_le]
        rw [Finsupp.single_le_iff]
        omega
      have e2 := congrArg Finsupp.degree e
      rw [map_add, Finsupp.degree_single] at e2
      simp only [List.length_append, List.length_singleton] at h
      omega

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on' with`. Consider the case `monomial s c => exact ⟨s.degree + 1, fun l hl => word_monomial l s c (by omega)⟩`. Consider the case `add p q hp hq`. Take `⟨m, hm⟩` from `hp`. Take `⟨k, hk⟩` from `hq`.

Conclude with `⟨max m k, fun l hl => by`. Rewrite using `[map_add, hm l (le_trans (le_max_left _ _) hl), hk l (le_trans (le_max_right _ _) hl), add_zero]⟩`.
-/
theorem word_pol (f : MvPolynomial σ ℂ) : ∃ m : ℕ, ∀ l : List σ, m ≤ l.length → (l.map pd).prod f = 0 := by
  induction f using MvPolynomial.induction_on' with
  | monomial s c => exact ⟨s.degree + 1, fun l hl => word_monomial l s c (by omega)⟩
  | add p q hp hq =>
    obtain ⟨m, hm⟩ := hp
    obtain ⟨k, hk⟩ := hq
    exact ⟨max m k, fun l hl => by
      rw [map_add, hm l (le_trans (le_max_left _ _) hl), hk l (le_trans (le_max_right _ _) hl), add_zero]⟩

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons i l ih => simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ih, LinearMap.lTensor_tmul]`.
-/
theorem word_tmul (l : List σ) (v : V) (f : MvPolynomial σ ℂ) :
    (l.map fun i => ((pd i).lTensor V : Module.End ℂ (V ⊗[ℂ] MvPolynomial σ ℂ))).prod (v ⊗ₜ f) =
      v ⊗ₜ (l.map pd).prod f := by
  induction l with
  | nil => simp
  | cons i l ih => simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ih, LinearMap.lTensor_tmul]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, fun l _ => map_zero _⟩`. Consider the case `tmul v f`. Take `⟨m, hm⟩` from `word_pol f`. Conclude with `⟨m, fun l hl => by rw [word_tmul, hm l hl, TensorProduct.tmul_zero]⟩`.

Consider the case `add p q hp hq`. Take `⟨m, hm⟩` from `hp`. Take `⟨k, hk⟩` from `hq`. Conclude with `⟨max m k, fun l hl => by`. Rewrite using `[map_add, hm l (le_trans (le_max_left _ _) hl), hk l (le_trans (le_max_right _ _) hl), add_zero]⟩`.
-/
theorem word_tens (z : V ⊗[ℂ] MvPolynomial σ ℂ) : ∃ m : ℕ, ∀ l : List σ, m ≤ l.length →
    (l.map fun i => ((pd i).lTensor V : Module.End ℂ (V ⊗[ℂ] MvPolynomial σ ℂ))).prod z = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, fun l _ => map_zero _⟩
  | tmul v f =>
    obtain ⟨m, hm⟩ := word_pol f
    exact ⟨m, fun l hl => by rw [word_tmul, hm l hl, TensorProduct.tmul_zero]⟩
  | add p q hp hq =>
    obtain ⟨m, hm⟩ := hp
    obtain ⟨k, hk⟩ := hq
    exact ⟨max m k, fun l hl => by
      rw [map_add, hm l (le_trans (le_max_left _ _) hl), hk l (le_trans (le_max_right _ _) hl), add_zero]⟩

end Pol

/- English proof (translation)
Introduce `hK hV n ε V _ _ E hE`. Take `⟨M, hM, hX, h0⟩` from `hV n ε`. Set `P` to `MvPolynomial (NC ε) ℂ`. Set `EY : Fin n → Fin n → Module.End ℂ (V ⊗[ℂ] P)` to `fun a b => (E a b).rTensor P + (M a b).lTensor V`. Establish `hEY : GlRel EY`.

Use `glRel_add (E := fun a b => ((E a b).rTensor P : Module.End ℂ (V ⊗[ℂ] P))) (F := fun a b => ((M a b).lTensor V : Module.End ℂ (V ⊗[ℂ] P))) ?_ ?_ ?_` and prove the remaining obligations. Conclude with `glRel_map (Module.End.rTensorAlgHom ℂ V P).toRingHom hE`. Conclude with `glRel_map (Module.End.lTensorAlgHom ℂ P V).toRingHom hM`. Introduce `a b c d`. Apply `TensorProduct.ext'` to reduce the goal to its premises.

Introduce `v f`. Simplify using `[Module.End.mul_apply]`. Set `cc : P →ₗ[ℂ] ℂ` to `(MvPolynomial.lcoeff ℂ (0 : NC ε →₀ ℕ))`. Establish `hcc : ∀ f : P, cc f = constantCoeff f` using `fun f => rfl`. Use `⟨V ⊗[ℂ] P, inferInstance, inferInstance, EY, (TensorProduct.rid ℂ V).toLinearMap ∘ₗ cc.lTensor V, hEY, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `v`. Conclude with `⟨v ⊗ₜ 1, by simp [hcc]⟩`. Introduce `a b y`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul v f => simp [EY, hcc, h0]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Use `hK n ε (V ⊗[ℂ] P) (fun i => EY i.1.1 i.1.2) (fun i => (pd i).lTensor V) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `i j`. Establish `h` using `hEY i.1.1 i.1.2 j.1.1 j.1.2`.

Establish `h1 : i.1.2 ≠ j.1.1` using `fun e => by`. Use `i.2.2` as an intermediate fact. Rewrite `this` using `[e, j.2.1]`. Conclude with `Bool.noConfusion this`. Establish `h2 : j.1.2 ≠ i.1.1` using `fun e => by`.

Use `j.2.2` as an intermediate fact. Rewrite `this` using `[e, i.2.1]`. Conclude with `Bool.noConfusion this`. Rewrite `h` using `[if_neg h1, if_neg h2, sub_zero, sub_eq_zero]`. Conclude with `h`.

Introduce `i j`. Apply `TensorProduct.ext'` to reduce the goal to its premises. Introduce `v f`. Use `congrArg (fun T : Module.End ℂ P => T f) (pd_comm i j)` as an intermediate fact. Simplify using `only [Module.End.mul_apply] at this`.

Simplify using `only [Module.End.mul_apply, LinearMap.lTensor_tmul, this]`. Introduce `i j`. Apply `TensorProduct.ext'` to reduce the goal to its premises. Introduce `v f`. Simplify using `only [EY, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply, LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, map_add, hX, pd_apply, Derivation.leibniz, pderiv_X, smul_eq_mul, TensorProduct.tmul_add]`.

Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h, Ne.symm h]`. Introduce `z`.

Take `⟨m, hm⟩` from `word_tens z`. Conclude with `⟨m, fun l hl => hm l hl.ge⟩`.
-/
theorem cover : Koszul → Verma → Cover := by
  intro hK hV n ε V _ _ E hE
  classical
  obtain ⟨M, hM, hX, h0⟩ := hV n ε
  let P := MvPolynomial (NC ε) ℂ
  let EY : Fin n → Fin n → Module.End ℂ (V ⊗[ℂ] P) := fun a b => (E a b).rTensor P + (M a b).lTensor V
  have hEY : GlRel EY := by
    refine glRel_add (E := fun a b => ((E a b).rTensor P : Module.End ℂ (V ⊗[ℂ] P)))
      (F := fun a b => ((M a b).lTensor V : Module.End ℂ (V ⊗[ℂ] P))) ?_ ?_ ?_
    · exact glRel_map (Module.End.rTensorAlgHom ℂ V P).toRingHom hE
    · exact glRel_map (Module.End.lTensorAlgHom ℂ P V).toRingHom hM
    · intro a b c d
      apply TensorProduct.ext'
      intro v f
      simp [Module.End.mul_apply]
  let cc : P →ₗ[ℂ] ℂ := (MvPolynomial.lcoeff ℂ (0 : NC ε →₀ ℕ))
  have hcc : ∀ f : P, cc f = constantCoeff f := fun f => rfl
  refine ⟨V ⊗[ℂ] P, inferInstance, inferInstance, EY, (TensorProduct.rid ℂ V).toLinearMap ∘ₗ cc.lTensor V,
    hEY, ?_, ?_, ?_⟩
  · intro v
    exact ⟨v ⊗ₜ 1, by simp [hcc]⟩
  · intro a b y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v f => simp [EY, hcc, h0]
    | add p q hp hq => simp only [map_add, hp, hq]
  · refine hK n ε (V ⊗[ℂ] P) (fun i => EY i.1.1 i.1.2) (fun i => (pd i).lTensor V) ?_ ?_ ?_ ?_
    · intro i j
      have h := hEY i.1.1 i.1.2 j.1.1 j.1.2
      have h1 : i.1.2 ≠ j.1.1 := fun e => by
        have := i.2.2; rw [e, j.2.1] at this; exact Bool.noConfusion this
      have h2 : j.1.2 ≠ i.1.1 := fun e => by
        have := j.2.2; rw [e, i.2.1] at this; exact Bool.noConfusion this
      rw [if_neg h1, if_neg h2, sub_zero, sub_eq_zero] at h
      exact h
    · intro i j
      apply TensorProduct.ext'
      intro v f
      have := congrArg (fun T : Module.End ℂ P => T f) (pd_comm i j)
      simp only [Module.End.mul_apply] at this
      simp only [Module.End.mul_apply, LinearMap.lTensor_tmul, this]
    · intro i j
      apply TensorProduct.ext'
      intro v f
      simp only [EY, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply, LinearMap.lTensor_tmul,
        LinearMap.rTensor_tmul, map_add, hX, pd_apply, Derivation.leibniz, pderiv_X, smul_eq_mul,
        TensorProduct.tmul_add]
      by_cases h : i = j
      · subst h; simp
      · simp [h, Ne.symm h]
    · intro z
      obtain ⟨m, hm⟩ := word_tens z
      exact ⟨m, fun l hl => hm l hl.ge⟩

end GlobalTheory.CompanionTheory.DSCover
