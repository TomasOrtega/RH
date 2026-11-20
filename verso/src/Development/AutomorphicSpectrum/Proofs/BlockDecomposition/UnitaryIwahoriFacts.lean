import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmFieldStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.UnitaryWitt

section Generic

variable {L : Type} [Field L] {n : ℕ}

/- English proof (translation)
Establish `hbi : b.val * (b⁻¹ : GL (Fin n) L).val = 1` using `by rw [← Units.val_mul]; simp`. Establish `hib : (b⁻¹ : GL (Fin n) L).val * b.val = 1` using `by rw [← Units.val_mul]; simp`. Express the relevant statement in the definitionally equal form `cT σ (b * g * b⁻¹).val * 1 * (b * g * b⁻¹).val = 1 ↔ cT σ g.val * J * g.val = J`. Simplify using `only [Units.val_mul, Matrix.mul_one]`. Establish `hc : cT σ (b⁻¹ : GL (Fin n) L).val * cT σ b.val = 1`.

Rewrite using `[← cT_mul, hbi, cT_one]`. Establish `key : cT σ (b.val * g.val * (b⁻¹ : GL (Fin n) L).val) * (b.val * g.val * (b⁻¹ : GL (Fin n) L).val) = cT σ (b⁻¹ : GL (Fin n) L).val * (cT σ g.val * J * g.val) * (b⁻¹ : GL (Fin n) L).val`. Rewrite using `[← hb]`. Simplify using `only [cT_mul, Matrix.mul_assoc]`. Rewrite using `[key]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h2 : cT σ b.val * (cT σ (b⁻¹ : GL (Fin n) L).val * (cT σ g.val * J * g.val) * (b⁻¹ : GL (Fin n) L).val) * b.val = cT σ b.val * 1 * b.val` using `by rw [h]`. Establish `hc' : cT σ b.val * cT σ (b⁻¹ : GL (Fin n) L).val = 1`. Rewrite using `[← cT_mul, hib, cT_one]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hc', hib, Matrix.one_mul, Matrix.mul_one]`. Use `_ = cT σ b.val * (cT σ (b⁻¹ : GL (Fin n) L).val * (cT σ g.val * J * g.val) * (b⁻¹ : GL (Fin n) L).val) * b.val := by`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = J := by rw [h2, Matrix.mul_one, hb]`.

Introduce `h`. Rewrite using `[h, ← hb]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [hc, hbi, Matrix.one_mul]`.
-/
theorem conj_mem_UJ_one_iff (σ : L →+* L) {J : Matrix (Fin n) (Fin n) L} (b g : GL (Fin n) L)
    (hb : cT σ b.val * b.val = J) : b * g * b⁻¹ ∈ UJ σ 1 ↔ g ∈ UJ σ J := by
  have hbi : b.val * (b⁻¹ : GL (Fin n) L).val = 1 := by rw [← Units.val_mul]; simp
  have hib : (b⁻¹ : GL (Fin n) L).val * b.val = 1 := by rw [← Units.val_mul]; simp
  change cT σ (b * g * b⁻¹).val * 1 * (b * g * b⁻¹).val = 1 ↔ cT σ g.val * J * g.val = J
  simp only [Units.val_mul, Matrix.mul_one]
  have hc : cT σ (b⁻¹ : GL (Fin n) L).val * cT σ b.val = 1 := by
    rw [← cT_mul, hbi, cT_one]
  have key : cT σ (b.val * g.val * (b⁻¹ : GL (Fin n) L).val) * (b.val * g.val * (b⁻¹ : GL (Fin n) L).val)
      = cT σ (b⁻¹ : GL (Fin n) L).val * (cT σ g.val * J * g.val) * (b⁻¹ : GL (Fin n) L).val := by
    rw [← hb]
    simp only [cT_mul, Matrix.mul_assoc]
  rw [key]
  constructor
  · intro h
    have h2 : cT σ b.val * (cT σ (b⁻¹ : GL (Fin n) L).val * (cT σ g.val * J * g.val) * (b⁻¹ : GL (Fin n) L).val) * b.val
        = cT σ b.val * 1 * b.val := by rw [h]
    have hc' : cT σ b.val * cT σ (b⁻¹ : GL (Fin n) L).val = 1 := by
      rw [← cT_mul, hib, cT_one]
    calc cT σ g.val * J * g.val
        = (cT σ b.val * cT σ (b⁻¹ : GL (Fin n) L).val) * (cT σ g.val * J * g.val) * ((b⁻¹ : GL (Fin n) L).val * b.val) := by
          rw [hc', hib, Matrix.one_mul, Matrix.mul_one]
      _ = cT σ b.val * (cT σ (b⁻¹ : GL (Fin n) L).val * (cT σ g.val * J * g.val) * (b⁻¹ : GL (Fin n) L).val) * b.val := by
          simp only [Matrix.mul_assoc]
      _ = J := by rw [h2, Matrix.mul_one, hb]
  · intro h
    rw [h, ← hb]
    calc cT σ (b⁻¹ : GL (Fin n) L).val * (cT σ b.val * b.val) * (b⁻¹ : GL (Fin n) L).val
        = (cT σ (b⁻¹ : GL (Fin n) L).val * cT σ b.val) * (b.val * (b⁻¹ : GL (Fin n) L).val) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hc, hbi, Matrix.one_mul]

/- English proof (translation)
Establish `hent : ∀ i j, (cT σ (GlobalTheory.SmGL.diagT L (Fin n) u).val * antiJ L n * (GlobalTheory.SmGL.diagT L (Fin n) u).val) i j = σ (u i) * antiJ L n i j * u j`. Introduce `i j`. Establish `hd : cT σ (GlobalTheory.SmGL.diagT L (Fin n) u).val = Matrix.diagonal fun i => σ (u i)`. Rewrite using `[GlobalTheory.SmGL.val_diagT]`. Use extensionality with `a c`.

Distinguish the cases in `h : a = c`. Substitute `h` using the available equality. Simplify using `[cT]`. Simplify using `[cT, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]`. Rewrite using `[hd, GlobalTheory.SmGL.val_diagT, Matrix.mul_diagonal, Matrix.diagonal_mul]`.

Establish `hrev : ∀ i : Fin n, antiJ L n i (Fin.rev i) = 1`. Introduce `i`. Establish `: i.val + (Fin.rev i).val + 1 = n`. Rewrite using `[Fin.val_rev]`. Use linear arithmetic over natural numbers and integers.

Conclude with `if_pos this`. Express the relevant statement in the definitionally equal form `cT σ (GlobalTheory.SmGL.diagT L (Fin n) u).val * antiJ L n * (GlobalTheory.SmGL.diagT L (Fin n) u).val = antiJ L n ↔ _`. Prove the components needed by the constructor for the conclusion. Introduce `h i`. Use `congrFun (congrFun h i) (Fin.rev i)` as an intermediate fact.

Rewrite `this` using `[hent, hrev, mul_one]`. Conclude with `this`. Introduce `h`. Use extensionality with `i j`. Rewrite using `[hent]`.

Distinguish the cases in `hij : i.val + j.val + 1 = n`. Establish `hj : j = Fin.rev i`. Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[Fin.val_rev]`. Use linear arithmetic over natural numbers and integers.

Substitute `hj` using the available equality. Rewrite using `[hrev, mul_one, h i]`. Establish `: antiJ L n i j = 0` using `by simp [antiJ, hij]`. Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
theorem diagT_mem_UJ_antiJ_iff (σ : L →+* L) (u : Fin n → Lˣ) :
    GlobalTheory.SmGL.diagT L (Fin n) u ∈ UJ σ (antiJ L n) ↔ ∀ i, σ (u i) * u (Fin.rev i) = 1 := by
  have hent : ∀ i j, (cT σ (GlobalTheory.SmGL.diagT L (Fin n) u).val * antiJ L n * (GlobalTheory.SmGL.diagT L (Fin n) u).val) i j
      = σ (u i) * antiJ L n i j * u j := by
    intro i j
    have hd : cT σ (GlobalTheory.SmGL.diagT L (Fin n) u).val = Matrix.diagonal fun i => σ (u i) := by
      rw [GlobalTheory.SmGL.val_diagT]
      ext a c
      by_cases h : a = c
      · subst h; simp [cT]
      · simp [cT, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]
    rw [hd, GlobalTheory.SmGL.val_diagT, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hrev : ∀ i : Fin n, antiJ L n i (Fin.rev i) = 1 := by
    intro i
    have : i.val + (Fin.rev i).val + 1 = n := by
      rw [Fin.val_rev]; omega
    exact if_pos this
  change cT σ (GlobalTheory.SmGL.diagT L (Fin n) u).val * antiJ L n * (GlobalTheory.SmGL.diagT L (Fin n) u).val = antiJ L n ↔ _
  constructor
  · intro h i
    have := congrFun (congrFun h i) (Fin.rev i)
    rw [hent, hrev, mul_one] at this
    exact this
  · intro h
    ext i j
    rw [hent]
    by_cases hij : i.val + j.val + 1 = n
    · have hj : j = Fin.rev i := by
        apply Fin.ext; rw [Fin.val_rev]; omega
      subst hj
      rw [hrev, mul_one, h i]
    · have : antiJ L n i j = 0 := by simp [antiJ, hij]
      rw [this]; simp

end Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
The claim follows from `if_neg hw`.
-/
theorem UL_eq_of_not_split {w : Pl E} (hw : ¬ IsSplitAt w) (n : ℕ) : UL n w = UJ (cj w) 1 := if_neg hw

/- English proof (translation)
Rewrite using `[iwU, Subgroup.mem_subgroupOf, Subgroup.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, e⟩`. Establish `e' : b * x * b⁻¹ = γ.1` using `e`. Rewrite using `[← e']`.

Simplify `hx` using `[mul_assoc]`. Introduce `h`. Use `⟨_, h, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `b * (b⁻¹ * γ.1 * b) * b⁻¹ = γ.1`. Use `group`.
-/
theorem mem_iwU_iff (n : ℕ) (w : Pl E) (b : GLw n w) (γ : UL n w) :
    γ ∈ iwU n w b ↔ b⁻¹ * γ.1 * b ∈ iwGL n w := by
  rw [iwU, Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, e⟩
    have e' : b * x * b⁻¹ = γ.1 := e
    rw [← e']
    simpa [mul_assoc] using hx
  · intro h
    refine ⟨_, h, ?_⟩
    change b * (b⁻¹ * γ.1 * b) * b⁻¹ = γ.1
    group

/- English proof (translation)
Establish `hv : Continuous fun g : GLw n w => (g.val : Matrix (Fin n) (Fin n) (w.adicCompletion E))` using `Units.continuous_val`. Establish `hm : Continuous fun g : GLw n w => cT (cj w) g.val * 1 * g.val`. Use `Continuous.matrix_mul (Continuous.matrix_mul ?_ continuous_const) hv` and prove the remaining obligations. Conclude with `(hv.matrix_map hc).matrix_transpose`. Conclude with `isClosed_eq hm continuous_const`.
-/
theorem isClosed_UJ_one {w : Pl E} (n : ℕ) (hc : Continuous (cj w)) :
    IsClosed (UJ (cj w) (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) : Set (GLw n w)) := by
  have hv : Continuous fun g : GLw n w => (g.val : Matrix (Fin n) (Fin n) (w.adicCompletion E)) :=
    Units.continuous_val
  have hm : Continuous fun g : GLw n w => cT (cj w) g.val * 1 * g.val := by
    refine Continuous.matrix_mul (Continuous.matrix_mul ?_ continuous_const) hv
    exact (hv.matrix_map hc).matrix_transpose
  exact isClosed_eq hm continuous_const

/- English proof (translation)
Establish `hcl : IsClosed (UL n w : Set (GLw n w))`. Rewrite using `[UL_eq_of_not_split hw]`. Conclude with `isClosed_UJ_one n hc`. Establish `hK : IsCompact ((fun g : GLw n w => b * g * b⁻¹) '' (iwGL n w : Set (GLw n w)))` using `(GlobalTheory.SmGL.IwahoriOnto.isCompact_iwahori (w.adicCompletion E) (Fin n)).image (by fun_prop)`. Establish `hP` using `hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK`.

Establish `e : (iwU n w b : Set (UL n w)) = Subtype.val ⁻¹' ((fun g : GLw n w => b * g * b⁻¹) '' (iwGL n w : Set (GLw n w)))`. Use extensionality with `γ`. Simplify using `only [SetLike.mem_coe, mem_iwU_iff, Set.mem_preimage, Set.mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Conclude with `⟨_, h, by group⟩`. Introduce and unpack `⟨x, hx, e⟩`. Rewrite using `[← e]`. Simplify `hx` using `[mul_assoc]`. Rewrite using `[e]`.

Conclude with `hP`.
-/
theorem isCompact_iwU {w : Pl E} (hw : ¬ IsSplitAt w) (n : ℕ) (b : GLw n w) (hc : Continuous (cj w)) :
    IsCompact (iwU n w b : Set (UL n w)) := by
  have hcl : IsClosed (UL n w : Set (GLw n w)) := by
    rw [UL_eq_of_not_split hw]; exact isClosed_UJ_one n hc
  have hK : IsCompact ((fun g : GLw n w => b * g * b⁻¹) '' (iwGL n w : Set (GLw n w))) :=
    (GlobalTheory.SmGL.IwahoriOnto.isCompact_iwahori (w.adicCompletion E) (Fin n)).image (by fun_prop)
  have hP := hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have e : (iwU n w b : Set (UL n w)) = Subtype.val ⁻¹'
      ((fun g : GLw n w => b * g * b⁻¹) '' (iwGL n w : Set (GLw n w))) := by
    ext γ
    simp only [SetLike.mem_coe, mem_iwU_iff, Set.mem_preimage, Set.mem_image]
    constructor
    · intro h
      exact ⟨_, h, by group⟩
    · rintro ⟨x, hx, e⟩
      rw [← e]
      simpa [mul_assoc] using hx
  rw [e]
  exact hP

/- English proof (translation)
Introduce `E _ _ _ hU w hw n b hb`. Use `⟨fun g => ?_, mem_iwU_iff n w b, isCompact_iwU hw n b (GlobalTheory.T.placeConjugation_properties_cmField E hU w).1, diagT_mem_UJ_antiJ_iff (cj w)⟩` and prove the remaining obligations. Rewrite using `[UL_eq_of_not_split hw]`. Conclude with `conj_mem_UJ_one_iff (cj w) b g hb.2`.
-/
theorem unitary_hyperbolic_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (b : GLw n w), IsWitt n w b → (∀ g : GLw n w, b * g * b⁻¹ ∈ UL n w ↔ g ∈ UJ (cj w) (antiJ (w.adicCompletion E) n)) ∧ (∀ γ : UL n w, γ ∈ iwU n w b ↔ b⁻¹ * γ.1 * b ∈ iwGL n w) ∧ IsCompact (iwU n w b : Set (UL n w)) ∧ ∀ u : Fin n → (w.adicCompletion E)ˣ, GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u ∈ UJ (cj w) (antiJ (w.adicCompletion E) n) ↔ ∀ i, cj w (u i) * u (Fin.rev i) = 1 := by
  intro E _ _ _ hU w hw n b hb
  refine ⟨fun g => ?_, mem_iwU_iff n w b, isCompact_iwU hw n b (GlobalTheory.T.placeConjugation_properties_cmField E hU w).1,
    diagT_mem_UJ_antiJ_iff (cj w)⟩
  rw [UL_eq_of_not_split hw]
  exact conj_mem_UJ_one_iff (cj w) b g hb.2

end GlobalTheory.CompanionTheory.UnitaryWitt
