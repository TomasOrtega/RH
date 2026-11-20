import Mathlib
import Formalism.UnipotentAdelicQuotients.CuspEllipticValues
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.MatrixTraceIffIsCharacterOverSubfieldComplexStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsPrimitiveExtendZeroOfSumUnipotentRadicalStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.EqOfIsPrimitiveOfEqOnEllipticFiniteGLStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IrreducibleOfVirtualCharacterNormOneStatement

namespace GlobalTheory.CuspGL

/- English proof (translation)
Take `⟨⟨n, ρ, hρ⟩, hs⟩` from `h`. Establish `hx : x = 1` using `Subsingleton.elim _ _`. Substitute `hx` using the available equality. Establish `h1 : χ 1 = (n : ℂ)` using `by rw [hρ]; simp`. Rewrite `hs` using `[Fintype.sum_subsingleton _ (1 : G), Fintype.card_eq_one_iff_nonempty_unique.2 ⟨uniqueOfSubsingleton (1 : G)⟩, h1]`.

Establish `h2 : n * n = 1`. Establish `: ((n * n : ℕ) : ℂ) = ((1 : ℕ) : ℂ)` using `by simpa using hs`. Conclude with `this` after adjusting the coercions. Establish `h3 : n = 1` using `Nat.eq_one_of_mul_eq_one_right h2`. Rewrite using `[h1, h3]`.

Simplify using the standard rewrite rules.
-/
theorem irrChar_eq_one_of_subsingleton {G : Type} [Group G] [Fintype G] [Subsingleton G] (χ : G → ℂ)
    (h : CuspElliptic.IsIrrChar χ) (x : G) : χ x = 1 := by
  obtain ⟨⟨n, ρ, hρ⟩, hs⟩ := h
  have hx : x = 1 := Subsingleton.elim _ _
  subst hx
  have h1 : χ 1 = (n : ℂ) := by rw [hρ]; simp
  rw [Fintype.sum_subsingleton _ (1 : G), Fintype.card_eq_one_iff_nonempty_unique.2
    ⟨uniqueOfSubsingleton (1 : G)⟩, h1] at hs
  have h2 : n * n = 1 := by
    have : ((n * n : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by simpa using hs
    exact_mod_cast this
  have h3 : n = 1 := Nat.eq_one_of_mul_eq_one_right h2
  rw [h1, h3]; simp

/- English proof (translation)
Establish `hc : GlobalTheory.BI.IsChar ℂ ℂ χ` using `(GlobalTheory.T.matrixTrace_iff_isCharacterOverSubfield_complex G χ).1 h.1`. Establish `hv : χ ∈ GlobalTheory.BI.Virt ℂ ℂ G` using `AddSubgroup.subset_closure hc`. Establish `hs : ∑ᶠ g, χ g * star (χ g) = (Nat.card G : ℂ)`. Rewrite using `[finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]`. Conclude with `h.2`.

Conclude with `((GlobalTheory.T.irreducible_of_virtualCharacter_norm_one G χ hv hs).2 hc).1`.
-/
theorem isIrrChar_of_norm_one {G : Type} [Group G] [Fintype G] (χ : G → ℂ)
    (h : CuspElliptic.IsIrrChar χ) : GlobalTheory.BI.IsIrrChar ℂ ℂ χ := by
  have hc : GlobalTheory.BI.IsChar ℂ ℂ χ := (GlobalTheory.T.matrixTrace_iff_isCharacterOverSubfield_complex G χ).1 h.1
  have hv : χ ∈ GlobalTheory.BI.Virt ℂ ℂ G := AddSubgroup.subset_closure hc
  have hs : ∑ᶠ g, χ g * star (χ g) = (Nat.card G : ℂ) := by
    rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]; exact h.2
  exact ((GlobalTheory.T.irreducible_of_virtualCharacter_norm_one G χ hv hs).2 hc).1

/- English proof (translation)
Use `GlobalTheory.T.isPrimitive_extendZero_of_sum_unipotentRadical F d χ ((GlobalTheory.T.matrixTrace_iff_isCharacterOverSubfield_complex _ χ).1 h.1.1) fun a ha had => ?_` and prove the remaining obligations. Establish `h0` using `h.2 a ha had`. Express the relevant statement in the definitionally equal form `∑ᶠ u ∈ (CuspElliptic.unipBlock d a : Set (GL (Fin d) F)), χ u = 0`. Rewrite using `[finsum_mem_def, finsum_eq_sum_of_fintype, ← h0]`. Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hu : u ∈ (CuspElliptic.unipBlock d a : Set (GL (Fin d) F))`. Simplify using `[hu]`. Simplify using `[hu]`.
-/
theorem isPrimitive_of_isCuspChar {F : Type} [Field F] [Fintype F] [DecidableEq F] {d : ℕ}
    (χ : GL (Fin d) F → ℂ) (h : CuspElliptic.IsCuspChar χ) : IsPrimitive (extZero χ) := by
  refine GlobalTheory.T.isPrimitive_extendZero_of_sum_unipotentRadical F d χ ((GlobalTheory.T.matrixTrace_iff_isCharacterOverSubfield_complex _ χ).1 h.1.1) fun a ha had => ?_
  have h0 := h.2 a ha had
  change ∑ᶠ u ∈ (CuspElliptic.unipBlock d a : Set (GL (Fin d) F)), χ u = 0
  rw [finsum_mem_def, finsum_eq_sum_of_fintype, ← h0]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases hu : u ∈ (CuspElliptic.unipBlock d a : Set (GL (Fin d) F))
  · simp [hu]
  · simp [hu]

/- English proof (translation)
Introduce `F _ _ _ d χ χ' h h' he`. Break down `Nat.eq_zero_or_pos d with rfl | hd` into its components or cases. Establish `: Subsingleton (GL (Fin 0) F)` using `⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩`. Use function extensionality and compare the values at `x`. Rewrite using `[irrChar_eq_one_of_subsingleton χ h.1, irrChar_eq_one_of_subsingleton χ' h'.1]`.

Conclude with `GlobalTheory.T.eq_of_isPrimitive_of_eq_on_elliptic_finiteGL F d χ χ' hd (isIrrChar_of_norm_one χ h.1) (isIrrChar_of_norm_one χ' h'.1) (isPrimitive_of_isCuspChar χ h) (isPrimitive_of_isCuspChar χ' h') he`.
-/
theorem cuspElliptic_statement : CuspElliptic.Statement := by
  intro F _ _ _ d χ χ' h h' he
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have : Subsingleton (GL (Fin 0) F) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
    funext x
    rw [irrChar_eq_one_of_subsingleton χ h.1, irrChar_eq_one_of_subsingleton χ' h'.1]
  · exact GlobalTheory.T.eq_of_isPrimitive_of_eq_on_elliptic_finiteGL F d χ χ' hd (isIrrChar_of_norm_one χ h.1) (isIrrChar_of_norm_one χ' h'.1)
      (isPrimitive_of_isCuspChar χ h) (isPrimitive_of_isCuspChar χ' h') he

end GlobalTheory.CuspGL
