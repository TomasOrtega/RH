import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Definitions.Jets.Imports
import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AdjointMemCapSpSubA
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WignerStepRaisingUnitaryComplementStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WigMapComp
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WigMapZeroOfContraction
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WigSh

/- English proof (translation)
Introduce `V _ _ _ n r z π u β L B l n₀ hz hT hπ hL hu hB`. Proceed by induction on `n₀ with`. Consider the case `zero`. Introduce `_`. Use `⟨V, inferInstance, inferInstance, inferInstance, π, fun _ => ContinuousLinearMap.id ℂ V, ?_, ?_, ?_⟩` and prove the remaining obligations.

Simplify using `using hπ`. Conclude with `wigMap_zero_of_contraction V V (n + 1) r z π π _ (fun v => le_rfl) (fun h _ v => rfl)`. Introduce `M v _`. Simplify using `[ContinuousLinearMap.adjoint_id]`. Consider the case `succ m ih`.

Introduce `hreg`. Take `⟨V₂, i1, i2, i3, π₂, A, hπ₂, hA, hAA⟩` from `ih (fun j hj => by`. Use `hreg j hj` as an intermediate fact. Move the coercions through the operations in `at this`. Use the proof step `omega)`.

Establish `hm0 : (0 : ℤ) ≤ (m : ℤ)` using `Int.natCast_nonneg m`. Establish `hL' : StrictAnti (Function.update L l (L l + (m : ℤ)))`. Introduce `a b hab`. Establish `h1` using `hL hab`. Distinguish the cases in `ha : a = l`.

Establish `hb : b ≠ l` using `fun hb => hab.ne (ha.trans hb.symm)`. Substitute `ha` using the available equality. Rewrite using `[Function.update_self, Function.update_of_ne hb]`. Use linear arithmetic over natural numbers and integers. Distinguish the cases in `hb : b = l`.

Substitute `hb` using the available equality. Rewrite using `[Function.update_self, Function.update_of_ne ha]`. Use `hreg a hab` as an intermediate fact. Move the coercions through the operations in `at this`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[Function.update_of_ne ha, Function.update_of_ne hb]`. Conclude with `h1`. Establish `hu' : ∀ j : Fin (n + 1), ((Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) + (m : ℝ)) ((j : ℕ) + 1) : ℝ) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + ((Function.update L l (L l + (m : ℤ)) j : ℤ) : ℂ)`. Introduce `j`. Distinguish the cases in `hj : j = l`.

Substitute `hj` using the available equality. Rewrite using `[Function.update_self, Function.update_self]`. Use `hu j` as an intermediate fact. Move the coercions through the operations in `at this ⊢`. Take the linear combination `this`.

Establish `hj' : (j : ℕ) + 1 ≠ (l : ℕ) + 1` using `fun h => hj (Fin.ext (by omega))`. Rewrite using `[Function.update_of_ne hj, Function.update_of_ne hj']`. Conclude with `hu j`. Establish `hreg' : ∀ j, Function.update L l (L l + (m : ℤ)) j ≠ Function.update L l (L l + (m : ℤ)) l + 1`. Introduce `j`.

Rewrite using `[Function.update_self]`. Break down `lt_trichotomy j l with hj | hj | hj` into its components or cases. Rewrite using `[Function.update_of_ne hj.ne]`. Use `hreg j hj` as an intermediate fact. Move the coercions through the operations in `at this`.

Use linear arithmetic over natural numbers and integers. Substitute `hj` using the available equality. Rewrite using `[Function.update_self]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Function.update_of_ne hj.ne']`.

Use `hL hj` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `⟨V₃, j1, j2, j3, π₃, a, hπ₃, ha, haa⟩` from `GlobalTheory.T.wigner_step_raising_unitary_complement V₂ n r z π₂ _ β _ B l hz hT hπ₂ hL' hu' hB hreg'`. Use `⟨V₃, j1, j2, j3, π₃, fun ω => (A ω).comp (a ω), ?_, wigMap_comp V V₂ V₃ (n + 1) r z π π₂ π₃ m 1 A a hA ha, ?_⟩` and prove the remaining obligations. Rewrite `hπ₃` using `[Function.update_self, Function.update_idem]`.

Establish `e : u ((l : ℕ) + 1) + ((m + 1 : ℕ) : ℝ) = u ((l : ℕ) + 1) + (m : ℝ) + 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `hπ₃`.

Introduce `M v hv`. Establish `hc` using `GlobalTheory.adjoint_mem_CapSp_subA V V₂ n r z π π₂ B (A (B (Fin.last n))) (shf β M) ⟨hπ.2.1, hπ.2.2.1⟩ ⟨hπ₂.2.1, hπ₂.2.2.1⟩ hπ.2.2.2.1 hπ₂.2.2.2.1 hB (fun h hh he => by`. Use `hA.2.1 h hh (B (Fin.last n))` as an intermediate fact. Rewrite using `[he] at this) v hv` and apply the resulting hypothesis. Establish `h2` using `haa M _ hc`.

Use `show A (B (Fin.last n)) (a (B (Fin.last n)) (ContinuousLinearMap.adjoint ((A (B (Fin.last n))).comp (a (B (Fin.last n)))) v)) = _`. Rewrite using `[ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply, h2, map_smul, hAA M v hv, smul_smul, Finset.prod_range_succ]`. Use `push_cast`. Rewrite using `[mul_comm]`.
-/
theorem chain_raise : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n r : ℕ) (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π : Mx (n + 1) r → (V →L[ℂ] V)) (u : ℕ → ℝ) (β : ℂ) (L : Fin (n + 1) → ℤ) (B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ)) (l : Fin (n + 1)) (n₀ : ℕ), inWb (n + 1) r z → 0 < Tz (n + 1) r z → IsType (n + 1) r z π u → StrictAnti L → (∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ)) → IsFrameOf (n + 1) r [z] B → (∀ j, j < l → L l + (n₀ : ℤ) < L j) → ∃ (V₂ : Type) (_ : NormedAddCommGroup V₂) (_ : InnerProductSpace ℂ V₂) (_ : FiniteDimensional ℂ V₂) (π₂ : Mx (n + 1) r → (V₂ →L[ℂ] V₂)) (A : (Fin (2 * r + (n + 1) + 1) → ℂ) → (V₂ →L[ℂ] V)), IsType (n + 1) r z π₂ (Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) + (n₀ : ℝ))) ∧ GlobalTheory.WigSh.WigMap (n + 1) r z π₂ π n₀ A ∧ ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA (EB π B)) (shf β M) → A (B (Fin.last n)) (ContinuousLinearMap.adjoint (A (B (Fin.last n))) v) = ((∏ j ∈ Finset.range n₀, GlobalTheory.WigSh.wP (Function.update L l (L l + (j : ℤ))) M l : ℝ) : ℂ) • v := by
  intro V _ _ _ n r z π u β L B l n₀ hz hT hπ hL hu hB
  induction n₀ with
  | zero =>
    intro _
    refine ⟨V, inferInstance, inferInstance, inferInstance, π, fun _ => ContinuousLinearMap.id ℂ V, ?_, ?_, ?_⟩
    · simpa using hπ
    · exact wigMap_zero_of_contraction V V (n + 1) r z π π _ (fun v => le_rfl) (fun h _ v => rfl)
    · intro M v _
      simp [ContinuousLinearMap.adjoint_id]
  | succ m ih =>
    intro hreg
    obtain ⟨V₂, i1, i2, i3, π₂, A, hπ₂, hA, hAA⟩ := ih (fun j hj => by
      have := hreg j hj
      push_cast at this
      omega)
    have hm0 : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg m
    have hL' : StrictAnti (Function.update L l (L l + (m : ℤ))) := by
      intro a b hab
      have h1 := hL hab
      by_cases ha : a = l
      · have hb : b ≠ l := fun hb => hab.ne (ha.trans hb.symm)
        subst ha
        rw [Function.update_self, Function.update_of_ne hb]
        omega
      · by_cases hb : b = l
        · subst hb
          rw [Function.update_self, Function.update_of_ne ha]
          have := hreg a hab
          push_cast at this
          omega
        · rw [Function.update_of_ne ha, Function.update_of_ne hb]
          exact h1
    have hu' : ∀ j : Fin (n + 1),
        ((Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) + (m : ℝ)) ((j : ℕ) + 1) : ℝ) : ℂ) -
          ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + ((Function.update L l (L l + (m : ℤ)) j : ℤ) : ℂ) := by
      intro j
      by_cases hj : j = l
      · subst hj
        rw [Function.update_self, Function.update_self]
        have := hu j
        push_cast at this ⊢
        linear_combination this
      · have hj' : (j : ℕ) + 1 ≠ (l : ℕ) + 1 := fun h => hj (Fin.ext (by omega))
        rw [Function.update_of_ne hj, Function.update_of_ne hj']
        exact hu j
    have hreg' : ∀ j, Function.update L l (L l + (m : ℤ)) j ≠ Function.update L l (L l + (m : ℤ)) l + 1 := by
      intro j
      rw [Function.update_self]
      rcases lt_trichotomy j l with hj | hj | hj
      · rw [Function.update_of_ne hj.ne]
        have := hreg j hj
        push_cast at this
        omega
      · subst hj
        rw [Function.update_self]
        omega
      · rw [Function.update_of_ne hj.ne']
        have := hL hj
        omega
    obtain ⟨V₃, j1, j2, j3, π₃, a, hπ₃, ha, haa⟩ :=
      GlobalTheory.T.wigner_step_raising_unitary_complement V₂ n r z π₂ _ β _ B l hz hT hπ₂ hL' hu' hB hreg'
    refine ⟨V₃, j1, j2, j3, π₃, fun ω => (A ω).comp (a ω), ?_,
      wigMap_comp V V₂ V₃ (n + 1) r z π π₂ π₃ m 1 A a hA ha, ?_⟩
    · rw [Function.update_self, Function.update_idem] at hπ₃
      have e : u ((l : ℕ) + 1) + ((m + 1 : ℕ) : ℝ) = u ((l : ℕ) + 1) + (m : ℝ) + 1 := by
        push_cast
        ring
      rw [e]
      exact hπ₃
    · intro M v hv
      have hc := GlobalTheory.adjoint_mem_CapSp_subA V V₂ n r z π π₂ B (A (B (Fin.last n))) (shf β M)
        ⟨hπ.2.1, hπ.2.2.1⟩ ⟨hπ₂.2.1, hπ₂.2.2.1⟩ hπ.2.2.2.1 hπ₂.2.2.2.1 hB
        (fun h hh he => by
          have := hA.2.1 h hh (B (Fin.last n))
          rwa [he] at this) v hv
      have h2 := haa M _ hc
      show A (B (Fin.last n)) (a (B (Fin.last n))
        (ContinuousLinearMap.adjoint ((A (B (Fin.last n))).comp (a (B (Fin.last n)))) v)) = _
      rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply, h2, map_smul, hAA M v hv,
        smul_smul, Finset.prod_range_succ]
      push_cast
      rw [mul_comm]

end GlobalTheory.WigSh
