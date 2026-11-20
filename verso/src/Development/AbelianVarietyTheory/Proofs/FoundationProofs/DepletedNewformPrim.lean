import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Chapter
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormCoeffSeqLinearStructureStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFormCoeffSeqDirichletTwistLevelMulSqStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Gamma1CharElementary
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
noncomputable section

namespace GlobalTheory.EisM

/- English proof (translation)
Introduce `k r g _ hr`. Establish `hM` using `g.pos`. Establish `hLpos : 0 < g.M * r` using `Nat.mul_pos hM (by omega)`. Establish `hdvd : g.M ∣ g.M * (g.M * r) ^ 2` using `dvd_mul_right _ _`. Establish `hLN : g.M * r ∣ g.M * (g.M * r) ^ 2` using `(dvd_pow_self _ two_ne_zero).mul_left g.M`.

Establish `hcop : ∀ n : ℕ, n.Coprime (g.M * (g.M * r) ^ 2) ↔ n.Coprime (g.M * r)`. Introduce `n`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `h.coprime_dvd_right hLN`.

Introduce `h`. Conclude with `Nat.Coprime.mul_right (h.coprime_dvd_right (dvd_mul_right _ _)) (Nat.Coprime.pow_right 2 h)`. Use `set χ : DirichletCharacter ℂ (g.M * (g.M * r) ^ 2) := DirichletCharacter.changeLevel hdvd g.χ with hχdef`. Establish `hχZ : ∀ d : ℤ, IsCoprime d ((g.M * (g.M * r) ^ 2 : ℕ) : ℤ) → ch χ d = g.χ (d : ZMod g.M)`. Introduce `d hd`.

Conclude with `DirichletCharacter.changeLevel_eq_cast_of_dvd' g.χ hdvd hd`. Establish `hχN : ∀ d : ℕ, d.Coprime (g.M * (g.M * r) ^ 2) → χ d = g.χ d`. Introduce `d hd`. Use `hχZ d (Nat.isCoprime_iff_coprime.2 hd)` as an intermediate fact. Simplify `this` using `[ch]`.

Use `⟨χ, ?_, hχN⟩` and prove the remaining obligations. Establish `hcf0` using `((gamma1_char_elementary k g.M g.χ hM).2 g.f g.char).2`. Establish `htw` using `GlobalTheory.T.isCuspFormCoeffSeq_dirichletTwist_level_mul_sq k g.M (g.M * r) g.χ (1 : DirichletCharacter ℂ (g.M * r)) (coef g.f) hLpos hcf0`. Establish `hseq : (fun n : ℕ => (1 : DirichletCharacter ℂ (g.M * r)) n * coef g.f n) = (fun n => if n.Coprime (g.M * r) then g.a n else 0)`. Use function extensionality and compare the values at `n`.

Distinguish the cases in `h : n.Coprime (g.M * r)`. Rewrite using `[if_pos h, MulChar.one_apply ((ZMod.isUnit_iff_coprime n _).2 h), one_mul]`. Both sides reduce to the same expression. Rewrite using `[if_neg h, MulChar.map_nonunit _ (fun hu => h ((ZMod.isUnit_iff_coprime n _).1 hu)), zero_mul]`. Rewrite `htw` using `[hseq]`.

Establish `hlin` using `(GlobalTheory.T.modularFormCoeffSeq_linear_structure k (g.M * (g.M * r) ^ 2) (fun d => ch g.χ d * ch (1 : DirichletCharacter ℂ (g.M * r)) d ^ 2)).2.2.2.1 (ch χ) _ ?_ htw.1`. Use `swap`. Introduce `d hd`. Establish `hdL : IsCoprime d ((g.M * r : ℕ) : ℤ)` using `hd.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.2 hLN)`. Rewrite using `[hχZ d hd]`.

Simplify using `only [ch]`. Rewrite using `[← ZMod.coe_unitOfIsCoprime d hdL, MulChar.one_apply_coe, one_pow, mul_one]`. Use `⟨⟨hlin, htw.2⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : (1 : ℕ).Coprime (g.M * r)` using `Nat.coprime_one_left _`. Simplify using `only [if_pos h1]`.

Conclude with `g.one`. Introduce `n hn`. Establish `: ¬ n.Coprime (g.M * r)` using `fun h => hn ((hcop n).2 h)`. Simplify using `only [if_neg this]`. Introduce `q hq hqN`.

Establish `hqL : q.Coprime (g.M * r)` using `(Nat.Prime.coprime_iff_not_dvd hq).2 (fun h => hqN (h.trans hLN))`. Establish `hqM : ¬ q ∣ g.M` using `fun h => hqN (h.trans hdvd)`. Establish `hchq : ch χ (q : ℤ) = g.χ (q : ZMod g.M)`. Rewrite using `[hχZ (q : ℤ) (Nat.isCoprime_iff_coprime.2 ((hcop q).2 hqL))]`. Simplify using the standard rewrite rules.

Establish `heig` using `g.eig q hq hqM`. Use function extensionality and compare the values at `n`. Simplify using `only [To, Vo, hchq, if_pos hqL]`. Distinguish the cases in `hn : n.Coprime (g.M * r)`. Establish `hn1 : 1 ≤ n`.

Break down `Nat.eq_zero_or_pos n with h0 | h0` into its components or cases. Substitute `h0` using the available equality. Rewrite `hn` using `[Nat.coprime_zero_left]`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `h0`.

Establish `hqn : (q * n).Coprime (g.M * r)` using `Nat.Coprime.mul hqL hn`. Rewrite using `[if_pos hqn, if_pos hn]`. Establish `e` using `heig n hn1`. Distinguish the cases in `hd : q ∣ n`. Establish `hnq : (n / q).Coprime (g.M * r)` using `hn.coprime_dvd_left (Nat.div_dvd_of_dvd hd)`.

Rewrite using `[if_pos hd, if_pos hnq]`. Rewrite `e` using `[if_pos hd]`. Conclude with `e`. Rewrite using `[if_neg hd]`. Rewrite `e` using `[if_neg hd]`.

Conclude with `e`. Establish `hqn : ¬ (q * n).Coprime (g.M * r)` using `fun h => hn (Nat.Coprime.coprime_mul_left h)`. Rewrite using `[if_neg hqn, if_neg hn, mul_zero]`. Distinguish the cases in `hd : q ∣ n`. Establish `hnq : ¬ (n / q).Coprime (g.M * r)`.

Introduce `h`. Apply `hn` to reduce the goal to its premises. Rewrite using `[← Nat.mul_div_cancel' hd]`. Conclude with `Nat.Coprime.mul hqL h`. Rewrite using `[if_pos hd, if_neg hnq]`.

Simplify using the standard rewrite rules. Rewrite using `[if_neg hd]`. Simplify using the standard rewrite rules.
-/
theorem depleted_newform_prim : ∀ (k r : ℕ) (g : Newform k), 1 ≤ k → 2 ≤ r → ∃ χ : DirichletCharacter ℂ (g.M * (g.M * r) ^ 2), Prim k _ χ (fun n => if n.Coprime (g.M * r) then g.a n else 0) ∧ ∀ d : ℕ, d.Coprime (g.M * (g.M * r) ^ 2) → χ d = g.χ d := by
  intro k r g _ hr
  have hM := g.pos
  have hLpos : 0 < g.M * r := Nat.mul_pos hM (by omega)
  have hdvd : g.M ∣ g.M * (g.M * r) ^ 2 := dvd_mul_right _ _
  have hLN : g.M * r ∣ g.M * (g.M * r) ^ 2 := (dvd_pow_self _ two_ne_zero).mul_left g.M
  have hcop : ∀ n : ℕ, n.Coprime (g.M * (g.M * r) ^ 2) ↔ n.Coprime (g.M * r) := by
    intro n
    constructor
    · intro h; exact h.coprime_dvd_right hLN
    · intro h
      exact Nat.Coprime.mul_right (h.coprime_dvd_right (dvd_mul_right _ _)) (Nat.Coprime.pow_right 2 h)
  set χ : DirichletCharacter ℂ (g.M * (g.M * r) ^ 2) := DirichletCharacter.changeLevel hdvd g.χ with hχdef
  have hχZ : ∀ d : ℤ, IsCoprime d ((g.M * (g.M * r) ^ 2 : ℕ) : ℤ) → ch χ d = g.χ (d : ZMod g.M) := by
    intro d hd
    exact DirichletCharacter.changeLevel_eq_cast_of_dvd' g.χ hdvd hd
  have hχN : ∀ d : ℕ, d.Coprime (g.M * (g.M * r) ^ 2) → χ d = g.χ d := by
    intro d hd
    have := hχZ d (Nat.isCoprime_iff_coprime.2 hd)
    simpa [ch] using this
  refine ⟨χ, ?_, hχN⟩

  have hcf0 := ((gamma1_char_elementary k g.M g.χ hM).2 g.f g.char).2
  have htw := GlobalTheory.T.isCuspFormCoeffSeq_dirichletTwist_level_mul_sq k g.M (g.M * r) g.χ (1 : DirichletCharacter ℂ (g.M * r)) (coef g.f) hLpos hcf0
  have hseq : (fun n : ℕ => (1 : DirichletCharacter ℂ (g.M * r)) n * coef g.f n) =
      (fun n => if n.Coprime (g.M * r) then g.a n else 0) := by
    funext n
    by_cases h : n.Coprime (g.M * r)
    · rw [if_pos h, MulChar.one_apply ((ZMod.isUnit_iff_coprime n _).2 h), one_mul]; rfl
    · rw [if_neg h, MulChar.map_nonunit _ (fun hu => h ((ZMod.isUnit_iff_coprime n _).1 hu)), zero_mul]
  rw [hseq] at htw
  have hlin := (GlobalTheory.T.modularFormCoeffSeq_linear_structure k (g.M * (g.M * r) ^ 2) (fun d => ch g.χ d * ch (1 : DirichletCharacter ℂ (g.M * r)) d ^ 2)).2.2.2.1
    (ch χ) _ ?_ htw.1
  swap
  · intro d hd
    have hdL : IsCoprime d ((g.M * r : ℕ) : ℤ) := hd.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.2 hLN)
    rw [hχZ d hd]
    simp only [ch]
    rw [← ZMod.coe_unitOfIsCoprime d hdL, MulChar.one_apply_coe, one_pow, mul_one]
  refine ⟨⟨hlin, htw.2⟩, ?_, ?_, ?_⟩
  · have h1 : (1 : ℕ).Coprime (g.M * r) := Nat.coprime_one_left _
    simp only [if_pos h1]
    exact g.one
  · intro n hn
    have : ¬ n.Coprime (g.M * r) := fun h => hn ((hcop n).2 h)
    simp only [if_neg this]
  · intro q hq hqN
    have hqL : q.Coprime (g.M * r) := (Nat.Prime.coprime_iff_not_dvd hq).2 (fun h => hqN (h.trans hLN))
    have hqM : ¬ q ∣ g.M := fun h => hqN (h.trans hdvd)
    have hchq : ch χ (q : ℤ) = g.χ (q : ZMod g.M) := by
      rw [hχZ (q : ℤ) (Nat.isCoprime_iff_coprime.2 ((hcop q).2 hqL))]; simp
    have heig := g.eig q hq hqM
    funext n
    simp only [To, Vo, hchq, if_pos hqL]
    by_cases hn : n.Coprime (g.M * r)
    · have hn1 : 1 ≤ n := by
        rcases Nat.eq_zero_or_pos n with h0 | h0
        · subst h0; rw [Nat.coprime_zero_left] at hn; nlinarith
        · exact h0
      have hqn : (q * n).Coprime (g.M * r) := Nat.Coprime.mul hqL hn
      rw [if_pos hqn, if_pos hn]
      have e := heig n hn1
      by_cases hd : q ∣ n
      · have hnq : (n / q).Coprime (g.M * r) := hn.coprime_dvd_left (Nat.div_dvd_of_dvd hd)
        rw [if_pos hd, if_pos hnq]
        rw [if_pos hd] at e
        exact e
      · rw [if_neg hd]
        rw [if_neg hd] at e
        exact e
    · have hqn : ¬ (q * n).Coprime (g.M * r) := fun h => hn (Nat.Coprime.coprime_mul_left h)
      rw [if_neg hqn, if_neg hn, mul_zero]
      by_cases hd : q ∣ n
      · have hnq : ¬ (n / q).Coprime (g.M * r) := by
          intro h
          apply hn
          rw [← Nat.mul_div_cancel' hd]
          exact Nat.Coprime.mul hqL h
        rw [if_pos hd, if_neg hnq]; simp
      · rw [if_neg hd]; simp

end GlobalTheory.EisM

end
