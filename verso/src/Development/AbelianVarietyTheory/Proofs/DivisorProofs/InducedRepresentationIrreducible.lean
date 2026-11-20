import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedScalarIrreducible

noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit

namespace GlobalTheory.KSplit

section

open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.RankFibre

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish `h1 : α * β⁻¹ * β = α` using `by ext x; simp`. Simplify using `only [parChar, h1, MonoidHom.comp_apply, MonoidHom.mul_apply, hp, deltaHalf_two, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, MonoidHom.coe_fst, MonoidHom.coe_snd, detChar_apply, Units.val_mul, val_absPow, Fintype.card_fin, apow]`. Use `show _ = (α (GeneralLinearGroup.det A) : ℂ) * β (GeneralLinearGroup.det D) * ((nabs k (GeneralLinearGroup.det A) : ℝ) : ℂ) ^ _ * ((nabs k (GeneralLinearGroup.det D) : ℝ) : ℂ) ^ _`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem parChar_div_val (a a' : ℕ) (α β : kˣ →* ℂˣ) (p : parab k (blocks a a')) (A : GL (Fin a) k) (D : GL (Fin a') k)
    (hp : leviProj k (blocks a a') p = leviTwo k (Fin a) (Fin a') (A, D)) :
    (parChar (α * β⁻¹) β a a' p : ℂ) =
      (α (gdet A) : ℂ) * β (gdet D) * apow (gdet A) ((a' : ℂ) / 2) * apow (gdet D) (-(a : ℂ) / 2) := by
  have h1 : α * β⁻¹ * β = α := by ext x; simp
  simp only [parChar, h1, MonoidHom.comp_apply, MonoidHom.mul_apply, hp, deltaHalf_two, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply, MonoidHom.coe_fst, MonoidHom.coe_snd, detChar_apply, Units.val_mul, val_absPow,
    Fintype.card_fin, apow]
  show _ = (α (GeneralLinearGroup.det A) : ℂ) * β (GeneralLinearGroup.det D) *
    ((nabs k (GeneralLinearGroup.det A) : ℝ) : ℂ) ^ _ * ((nabs k (GeneralLinearGroup.det D) : ℝ) : ℂ) ^ _
  ring

/- English proof (translation)
Use extensionality with `f`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Use `⟨mem_smoothPart_of_nhds (h2.mono fun u hu => funext hu), fun p g => ?_⟩` and prove the remaining obligations. Establish `hp : leviProj k (blocks a a') p = leviTwo k (Fin a) (Fin a') (leviProj k (blocks a a') p false, leviProj k (blocks a a') p true)` using `((leviTwo k (Fin a) (Fin a')).apply_symm_apply _).symm`.

Rewrite using `[ofChar_apply, parChar_div_val a a' α β p _ _ hp]`. Use `h1 p _ _ (fun i j => p.1.val (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j))) ?_ g` and prove the remaining obligations. Use extensionality with `(i | i) (j | j)`. Both sides reduce to the same expression. Both sides reduce to the same expression.

Conclude with `(mem_parab_two k).1 p.2 i j`. Both sides reduce to the same expression. Introduce and unpack `⟨h1, h2⟩`. Use `⟨fun b A D N hb h => ?_, ?_⟩` and prove the remaining obligations. Establish `hb' : b ∈ parab k (blocks a a')` using `(mem_parab_two k).2 fun j i => congrFun (congrFun hb (Sum.inr j)) (Sum.inl i)`.

Establish `hp : leviProj k (blocks a a') ⟨b, hb'⟩ = leviTwo k (Fin a) (Fin a') (A, D)`. Use function extensionality and compare the values at `x`. Consider the cases of `x`. Use extensionality with `i j`. Conclude with `congrFun (congrFun hb (Sum.inl i)) (Sum.inl j)`.

Use extensionality with `i j`. Conclude with `congrFun (congrFun hb (Sum.inr i)) (Sum.inr j)`. Use `h2 ⟨b, hb'⟩ h` as an intermediate fact. Rewrite `this` using `[ofChar_apply, parChar_div_val a a' α β _ _ _ hp]`. Conclude with `this`.

Establish `ho : IsOpen {g : GL (Fin (a + a')) k | rightReg ℂ (GL (Fin (a + a')) k) ℂ g f = f}` using `h1`. Conclude with `Filter.mem_of_superset (ho.mem_nhds (by simp)) fun u hu h => congrFun hu h`.
-/
theorem indSp_eq_indScal (a a' : ℕ) (α β : kˣ →* ℂˣ) : indSp a a' α β = indScal (α * β⁻¹) β a a' := by
  ext f
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨mem_smoothPart_of_nhds (h2.mono fun u hu => funext hu), fun p g => ?_⟩
    have hp : leviProj k (blocks a a') p = leviTwo k (Fin a) (Fin a')
        (leviProj k (blocks a a') p false, leviProj k (blocks a a') p true) :=
      ((leviTwo k (Fin a) (Fin a')).apply_symm_apply _).symm
    rw [ofChar_apply, parChar_div_val a a' α β p _ _ hp]
    refine h1 p _ _ (fun i j => p.1.val (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j))) ?_ g
    ext (i | i) (j | j)
    · rfl
    · rfl
    · exact (mem_parab_two k).1 p.2 i j
    · rfl
  · rintro ⟨h1, h2⟩
    refine ⟨fun b A D N hb h => ?_, ?_⟩
    · have hb' : b ∈ parab k (blocks a a') := (mem_parab_two k).2 fun j i =>
        congrFun (congrFun hb (Sum.inr j)) (Sum.inl i)
      have hp : leviProj k (blocks a a') ⟨b, hb'⟩ = leviTwo k (Fin a) (Fin a') (A, D) := by
        funext x
        cases x
        · ext i j
          exact congrFun (congrFun hb (Sum.inl i)) (Sum.inl j)
        · ext i j
          exact congrFun (congrFun hb (Sum.inr i)) (Sum.inr j)
      have := h2 ⟨b, hb'⟩ h
      rw [ofChar_apply, parChar_div_val a a' α β _ _ _ hp] at this
      exact this
    · have ho : IsOpen {g : GL (Fin (a + a')) k | rightReg ℂ (GL (Fin (a + a')) k) ℂ g f = f} := h1
      exact Filter.mem_of_superset (ho.mem_nhds (by simp)) fun u hu h => congrFun hu h

end

/- English proof (translation)
Introduce `H k _ _ _ _ a a' α β hα hβ N hN hinv`. Rewrite `hN`, the goal using `[indSp_eq_indScal]`. Establish `hs : GlobalTheory.SmGL.IsSmoothChar (α * β⁻¹)` using `GlobalTheory.SmGL.IsSmoothChar.mul hα.1 (GlobalTheory.SmGL.IsSmoothChar.inv hβ.1)`. Establish `hu : GlobalTheory.SmGL.IsUnitaryChar (α * β⁻¹)` using `fun x => by simp [hα.2 x, hβ.2 x]`. Conclude with `(GlobalTheory.RankFibre.indScal_irreducible H k a a' _ β hs hu hβ.1 hβ.2 N hN hinv).imp_right (le_antisymm hN)`.
-/
theorem indSp_irreducible : GlobalTheory.Published.BernsteinUnitaryProductIrreducible → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a a' : ℕ) (α β : kˣ →* ℂˣ), IsSmU α → IsSmU β →
    ∀ N : Submodule ℂ (GL (Fin (a + a')) k → ℂ), N ≤ indSp a a' α β → (∀ f ∈ N, ∀ x, (fun h => f (h * x)) ∈ N) →
      N = ⊥ ∨ N = indSp a a' α β := by
  intro H k _ _ _ _ a a' α β hα hβ N hN hinv
  rw [indSp_eq_indScal] at hN ⊢
  have hs : GlobalTheory.SmGL.IsSmoothChar (α * β⁻¹) :=
    GlobalTheory.SmGL.IsSmoothChar.mul hα.1 (GlobalTheory.SmGL.IsSmoothChar.inv hβ.1)
  have hu : GlobalTheory.SmGL.IsUnitaryChar (α * β⁻¹) := fun x => by simp [hα.2 x, hβ.2 x]
  exact (GlobalTheory.RankFibre.indScal_irreducible H k a a' _ β hs hu hβ.1 hβ.2 N hN hinv).imp_right (le_antisymm hN)

end GlobalTheory.KSplit

end
