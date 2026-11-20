import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinResidueLine
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAHEqOfMemRatPts
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar GlobalTheory.ResLine
open GlobalTheory.Doubling (absE)

noncomputable section

open Pointwise

namespace GlobalTheory.ResLine.HtCont

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

/- English proof (translation)
Establish `h1 : (matHom _ σ J p⁻¹).1 * (matHom _ σ J p).1 = 1`. Rewrite using `[← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]`. Establish `h2 : l.1 • ((matHom _ σ J p⁻¹).1 * adMat F x) = adMat F x`. Rewrite using `[← Matrix.mul_smul, ← hp, ← Matrix.mul_assoc, h1, Matrix.one_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem inv_eigen {x : Matrix (Fin n) (Fin 1) E} {p : GAd σ J} {l : (AF F ⊗[F] E)ˣ}
    (hp : (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x) :
    (matHom _ σ J p⁻¹).1 * adMat F x = (l⁻¹).1 • adMat F x := by
  have h1 : (matHom _ σ J p⁻¹).1 * (matHom _ σ J p).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have h2 : l.1 • ((matHom _ σ J p⁻¹).1 * adMat F x) = adMat F x := by
    rw [← Matrix.mul_smul, ← hp, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  calc _ = ((l⁻¹).1 * l.1) • ((matHom _ σ J p⁻¹).1 * adMat F x) := by rw [Units.inv_mul, one_smul]
    _ = _ := by rw [← smul_smul, h2]

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `h0 : ∀ j, X j 0 = 0` using `fun j => hc j`. Use `congrFun (congrFun hW.xy 0) 0` as an intermediate fact. Simplify using `[Matrix.mul_apply, Formalism.UG.cT, h0] at this`.
-/
theorem exists_col_ne {r : ℕ} {X Y : Matrix (Fin n) (Fin (r + 1)) E} (hW : IsWittFrame σ J X Y) :
    ∃ i, col X i 0 ≠ 0 := by
  by_contra hc
  push_neg at hc
  have h0 : ∀ j, X j 0 = 0 := fun j => hc j
  have := congrFun (congrFun hW.xy 0) 0
  simp [Matrix.mul_apply, Formalism.UG.cT, h0] at this

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J r X Y L a h hS`. Take `⟨hCM, -, -, hW, hA, hI1, hI2⟩` from `hS`. Use `haveI := hA.lat`. Use `haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)`. Use `haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F`.

Use `haveI := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := AF F)`. Establish `hK : IsCompact (levelAll σ J L a : Set (GAd σ J))` using `GlobalTheory.Doubling.isCompact_levelAll hCM J L a`. Use `⟨hK, ?_⟩` and prove the remaining obligations. Take `⟨i, hi⟩` from `exists_col_ne hW`. Use `set x := col X with hx`.

Establish `hm : Continuous fun g : GAd σ J => (matHom _ σ J g).1` using `Units.continuous_val.comp (isEmbedding_matHom _ σ J).continuous`. Set `Λ : GAd σ J → AF F ⊗[F] E` to `fun g => ((matHom _ σ J g).1 * adMat F x) i 0 * inclR (F := F) (AF F) (x i 0)⁻¹`. Establish `hΛ : Continuous Λ` using `((hm.matrix_mul continuous_const).matrix_elem i 0).mul continuous_const`. Establish `key : ∀ p (l : (AF F ⊗[F] E)ˣ), (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x → l.1 = Λ p`. Introduce `p l hl`.

Establish `e` using `congrFun (congrFun hl i) 0`. Simplify using `only [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply] at e`. Simplify using `only [Λ, e, mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, mul_one]`. Set `P : Set (GAd σ J)` to `{p | (matHom _ σ J p).1 * adMat F x = Λ p • adMat F x ∧ Λ p * Λ p⁻¹ = 1}`. Establish `memP : ∀ p, (∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x) → p ∈ P`.

Introduce and unpack `p ⟨l, hl⟩`. Establish `e1` using `key p l hl`. Establish `e2` using `key p⁻¹ l⁻¹ (inv_eigen hl)`. Conclude with `⟨by rw [← e1]; exact hl, by rw [← e1, ← e2, Units.mul_inv]⟩`. Establish `hPc : IsClosed P` using `(isClosed_eq (hm.matrix_mul continuous_const) (hΛ.smul continuous_const)).inter (isClosed_eq (hΛ.mul (hΛ.comp continuous_inv)) continuous_const)`.

Set `u : P → (AF F ⊗[F] E)ˣ` to `fun p => ⟨Λ p, Λ p.1⁻¹, p.2.2, by rw [mul_comm]; exact p.2.2⟩`. Establish `hu : Continuous u` using `Units.continuous_iff.2 ⟨hΛ.comp continuous_subtype_val, (hΛ.comp continuous_inv).comp continuous_subtype_val⟩`. Set `f : P → ℝ` to `fun p => (absE F E (u p) : ℝ)`. Establish `hf : Continuous f` using `NNReal.continuous_coe.comp (GlobalTheory.Doubling.continuous_absE.comp hu)`. Establish `hval : ∀ p : P, ∀ k ∈ levelAll σ J L a, h (p.1 * k) = f p` using `fun p k hk => hI2 p.1 (u p) p.2.1 k hk`.

Rewrite using `[continuous_iff_isClosed]`. Introduce `s hs`. Establish `hpre : h ⁻¹' s = (Subtype.val '' (f ⁻¹' s)) * (levelAll σ J L a : Set (GAd σ J))`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion.

Introduce `hg`. Take `⟨p, l, hl, k, hk, rfl⟩` from `hI1 g`. Establish `hp : p ∈ P` using `memP p ⟨l, hl⟩`. Use `⟨p, ⟨⟨p, hp⟩, ?_, rfl⟩, k, hk, rfl⟩` and prove the remaining obligations. Use `show f ⟨p, hp⟩ ∈ s`.

Rewrite using `[← hval ⟨p, hp⟩ k hk]`. Conclude with `hg`. Introduce and unpack `⟨_, ⟨p, hp, rfl⟩, k, hk, rfl⟩ show h (p.1 * k) ∈ s`. Rewrite using `[hval p k hk]`. Conclude with `hp`.

Rewrite using `[hpre]`. Conclude with `(hPc.isClosedEmbedding_subtypeVal.isClosedMap _ (hs.preimage hf)).mul_right_of_isCompact hK`.
-/
theorem isCompact_and_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), Data σ J X Y L a h →
    IsCompact (levelAll σ J L a : Set (GAd σ J)) ∧ Continuous h := by
  intro F E _ _ _ _ _ σ n J r X Y L a h hS
  obtain ⟨hCM, -, -, hW, hA, hI1, hI2⟩ := hS
  haveI := hA.lat
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := AF F)
  have hK : IsCompact (levelAll σ J L a : Set (GAd σ J)) := GlobalTheory.Doubling.isCompact_levelAll hCM J L a
  refine ⟨hK, ?_⟩
  obtain ⟨i, hi⟩ := exists_col_ne hW
  set x := col X with hx
  have hm : Continuous fun g : GAd σ J => (matHom _ σ J g).1 :=
    Units.continuous_val.comp (isEmbedding_matHom _ σ J).continuous
  let Λ : GAd σ J → AF F ⊗[F] E := fun g =>
    ((matHom _ σ J g).1 * adMat F x) i 0 * inclR (F := F) (AF F) (x i 0)⁻¹
  have hΛ : Continuous Λ := ((hm.matrix_mul continuous_const).matrix_elem i 0).mul continuous_const
  have key : ∀ p (l : (AF F ⊗[F] E)ˣ), (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x → l.1 = Λ p := by
    intro p l hl
    have e := congrFun (congrFun hl i) 0
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply] at e
    simp only [Λ, e, mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, mul_one]
  let P : Set (GAd σ J) := {p | (matHom _ σ J p).1 * adMat F x = Λ p • adMat F x ∧ Λ p * Λ p⁻¹ = 1}
  have memP : ∀ p, (∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x) → p ∈ P := by
    rintro p ⟨l, hl⟩
    have e1 := key p l hl
    have e2 := key p⁻¹ l⁻¹ (inv_eigen hl)
    exact ⟨by rw [← e1]; exact hl, by rw [← e1, ← e2, Units.mul_inv]⟩
  have hPc : IsClosed P :=
    (isClosed_eq (hm.matrix_mul continuous_const) (hΛ.smul continuous_const)).inter
      (isClosed_eq (hΛ.mul (hΛ.comp continuous_inv)) continuous_const)
  let u : P → (AF F ⊗[F] E)ˣ := fun p => ⟨Λ p, Λ p.1⁻¹, p.2.2, by rw [mul_comm]; exact p.2.2⟩
  have hu : Continuous u := Units.continuous_iff.2
    ⟨hΛ.comp continuous_subtype_val, (hΛ.comp continuous_inv).comp continuous_subtype_val⟩
  let f : P → ℝ := fun p => (absE F E (u p) : ℝ)
  have hf : Continuous f := NNReal.continuous_coe.comp (GlobalTheory.Doubling.continuous_absE.comp hu)
  have hval : ∀ p : P, ∀ k ∈ levelAll σ J L a, h (p.1 * k) = f p := fun p k hk =>
    hI2 p.1 (u p) p.2.1 k hk
  rw [continuous_iff_isClosed]
  intro s hs
  have hpre : h ⁻¹' s = (Subtype.val '' (f ⁻¹' s)) * (levelAll σ J L a : Set (GAd σ J)) := by
    ext g; constructor
    · intro hg
      obtain ⟨p, l, hl, k, hk, rfl⟩ := hI1 g
      have hp : p ∈ P := memP p ⟨l, hl⟩
      refine ⟨p, ⟨⟨p, hp⟩, ?_, rfl⟩, k, hk, rfl⟩
      show f ⟨p, hp⟩ ∈ s
      rw [← hval ⟨p, hp⟩ k hk]; exact hg
    · rintro ⟨_, ⟨p, hp, rfl⟩, k, hk, rfl⟩
      show h (p.1 * k) ∈ s
      rw [hval p k hk]; exact hp
  rw [hpre]
  exact (hPc.isClosedEmbedding_subtypeVal.isClosedMap _ (hs.preimage hf)).mul_right_of_isCompact hK

end GlobalTheory.ResLine.HtCont

end
