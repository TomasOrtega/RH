import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntersectionNumberEqGenericRankMulProjCurve
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

namespace GlobalTheory.VB

/- English proof (translation)
Proceed by induction on `a using WithBot.recBotCoe with`. Consider the case `bot => exact WithBot.bot_lt_coe _`. Consider the case `coe m`. Proceed by induction on `m using ENat.recTopCoe with`. Consider the case `top`.

It suffices to derive a contradiction. Rewrite `h` using `[← WithBot.coe_one, ← WithBot.coe_add, top_add, ← WithBot.coe_natCast, WithBot.coe_le_coe]`. Conclude with `absurd h (not_le.mpr (ENat.coe_lt_top n))`. Consider the case `coe m`. Establish `h' : ((m + 1 : ℕ) : WithBot ℕ∞) ≤ (n : WithBot ℕ∞)` using `by exact_mod_cast h`.

Establish `: m + 1 ≤ n` using `by exact_mod_cast h'`. Conclude with `(show m < n by omega)` after adjusting the coercions.
-/
theorem lt_of_add_one_le_natCast {a : WithBot ℕ∞} {n : ℕ} (h : a + 1 ≤ (n : WithBot ℕ∞)) :
    a < (n : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe m =>
    induction m using ENat.recTopCoe with
    | top =>
      exfalso
      rw [← WithBot.coe_one, ← WithBot.coe_add, top_add, ← WithBot.coe_natCast, WithBot.coe_le_coe] at h
      exact absurd h (not_le.mpr (ENat.coe_lt_top n))
    | coe m =>
      have h' : ((m + 1 : ℕ) : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) := by exact_mod_cast h
      have : m + 1 ≤ n := by exact_mod_cast h'
      exact_mod_cast (show m < n by omega)

variable {Z : Scheme.{0}} [IsIntegral Z]

/- English proof (translation)
Use `topologicalKrullDim_add_one_le (QCoh.isClosed_support F) isClosed_univ fun x _ => ⟨genericPoint Z, trivial, genRank_eq_zero_iff.1 h, genericPoint_specializes x⟩` as an intermediate fact. Establish `e : topologicalKrullDim (Set.univ : Set Z) = topologicalKrullDim Z`. Rewrite using `[← QCoh.suppDim_structureModule, QCoh.suppDim, QCoh.support_structureModule]`. Rewrite `this` using `[e]`. Conclude with `lt_of_add_one_le_natCast (this.trans hd)`.
-/
theorem suppDim_lt_of_genRank_eq_zero {n : ℕ} (hd : topologicalKrullDim Z ≤ (n : WithBot ℕ∞))
    {F : Z.Modules} [QCoh.IsFiniteQC F] (h : genRank F = 0) : QCoh.suppDim F < (n : WithBot ℕ∞) := by
  have := topologicalKrullDim_add_one_le (QCoh.isClosed_support F) isClosed_univ
    fun x _ => ⟨genericPoint Z, trivial, genRank_eq_zero_iff.1 h, genericPoint_specializes x⟩
  have e : topologicalKrullDim (Set.univ : Set Z) = topologicalKrullDim Z := by
    rw [← QCoh.suppDim_structureModule, QCoh.suppDim, QCoh.support_structureModule]
  rw [e] at this
  exact lt_of_add_one_le_natCast (this.trans hd)

variable {κ : Type} [Field κ] [Algebra κ Γ(Z, ⊤)]

/- English proof (translation)
Establish `hf` using `algebraMap_eq_strHom κ Z`. Establish `h1 : ∀ {F : Z.Modules} [QCoh.IsFiniteQC F], FiniteCohTwists κ F` using `fun {F} _ => finiteCohTwists_of_isProjOver hf F hp`. Take `⟨_, A, hA⟩` from `isProper_and_exists_isAmpleLB_of_isProjOver hp`. Proceed by induction on `r with`. Consider the case `zero`.

Introduce `G _ h`. Rewrite using `[interNum_eq_zero_of_isProjOver hf G hp (suppDim_lt_of_genRank_eq_zero hd h) hP]`. Simplify using the standard rewrite rules. Consider the case `succ r ih`. Introduce `G _ h`.

Take `⟨n, hn⟩` from `(hA.eventually_isGloballyGenerated_twist G).exists`. Establish `hM` using `isLB_lbPow hA.isLB n`. Use `Twist.isFiniteQC_twist (F := G) hM` as an intermediate fact. Establish `hr : genRank (twist G (lbPow A n)) = r + 1` using `(genRank_twist hM).trans h`. Take `⟨s, hs⟩` from `exists_germ_ne_zero hn (by omega)`.

Use `mono_sectionHom s hs` as an intermediate fact. Establish `e₁ : interNum κ (twist G (lbPow A n)) P = interNum κ G P` using `(diffVanish_chiPic_of_isProjOver (d := Fintype.card ι) hf G hp ((QCoh.suppDim_le G).trans hd)).interNum_twist le_rfl hP hM`. Establish `e₂` using `interNum_cokernel (k := κ) (QCoh.sectionHom s) hP h1 h1`. Establish `e₃` using `genRank_cokernel (QCoh.sectionHom s)`. Rewrite `e₃` using `[(isVB_structureModule Z).genRank_eq, hr]`.

Rewrite `e₂` using `[ih _ (by omega)]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem interNum_of_genRank_eq (hp : IsProjOver (strHom κ Z)) {ι : Type} [Fintype ι]
    (hd : topologicalKrullDim Z ≤ (Fintype.card ι : ℕ)) {P : ι → LB Z} (hP : ∀ i, (P i).IsLB)
    (r : ℕ) : ∀ (G : Z.Modules) [QCoh.IsFiniteQC G], genRank G = r →
      interNum κ G P = r * interNum κ (structureModule Z) P := by
  have hf := algebraMap_eq_strHom κ Z
  have h1 : ∀ {F : Z.Modules} [QCoh.IsFiniteQC F], FiniteCohTwists κ F :=
    fun {F} _ => finiteCohTwists_of_isProjOver hf F hp
  obtain ⟨_, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hp
  induction r with
  | zero =>
    intro G _ h
    rw [interNum_eq_zero_of_isProjOver hf G hp (suppDim_lt_of_genRank_eq_zero hd h) hP]
    simp
  | succ r ih =>
    intro G _ h
    obtain ⟨n, hn⟩ := (hA.eventually_isGloballyGenerated_twist G).exists
    have hM := isLB_lbPow hA.isLB n
    have := Twist.isFiniteQC_twist (F := G) hM
    have hr : genRank (twist G (lbPow A n)) = r + 1 := (genRank_twist hM).trans h
    obtain ⟨s, hs⟩ := exists_germ_ne_zero hn (by omega)
    have := mono_sectionHom s hs
    have e₁ : interNum κ (twist G (lbPow A n)) P = interNum κ G P :=
      (diffVanish_chiPic_of_isProjOver (d := Fintype.card ι) hf G hp
        ((QCoh.suppDim_le G).trans hd)).interNum_twist le_rfl hP hM
    have e₂ := interNum_cokernel (k := κ) (QCoh.sectionHom s) hP h1 h1
    have e₃ := genRank_cokernel (QCoh.sectionHom s)
    rw [(isVB_structureModule Z).genRank_eq, hr] at e₃
    rw [ih _ (by omega)] at e₂
    push_cast
    linarith

end GlobalTheory.VB

/- English proof (translation)
Introduce `_ _ _ _ _ hp _ _ hd G _ _ hP` and use `GlobalTheory.VB.interNum_of_genRank_eq hp hd hP _ G rfl`.
-/
theorem GlobalTheory.VB.interNum_eq_genRank_mul_of_isProjOver : ∀ (κ : Type) [Field κ] (Z : Scheme.{0})
    [IsIntegral Z] [Algebra κ Γ(Z, ⊤)], IsProjOver (strHom κ Z) → ∀ (ι : Type) [Fintype ι],
    topologicalKrullDim Z ≤ (Fintype.card ι : ℕ) → ∀ (G : Z.Modules) [GlobalTheory.QCoh.IsFiniteQC G]
    (P : ι → LB Z), (∀ i, (P i).IsLB) →
    interNum κ G P = (GlobalTheory.VB.genRank G : ℤ) * interNum κ (structureModule Z) P :=
  fun _ _ _ _ _ hp _ _ hd G _ _ hP => GlobalTheory.VB.interNum_of_genRank_eq hp hd hP _ G rfl
