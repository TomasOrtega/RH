import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecomposition
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.HpgMem

/- English proof (translation)
Introduce `k _ _ _ _ i t h`. Use `set M : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k := (((h : GlobalTheory.BZMir.Mir k (i + t)) : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) with hM`. Establish `hmem : ((h : GlobalTheory.BZMir.Mir k (i + t)) : GL (Fin (i + t + 1)) k) ∈ GlobalTheory.SmGL.parab k (GlobalTheory.BZMir.Leib.ePG i t)` using `h.2`. Establish `hp` using `GlobalTheory.SmGL.mem_parab_iff.1 hmem`. Establish `hp' : ∀ (a : Fin t) (b : Fin (i + 1)), M (GlobalTheory.BZMir.Leib.ePG i t ⟨true, a⟩) (GlobalTheory.BZMir.Leib.ePG i t ⟨false, b⟩) = 0` using `fun a b => hp true false a b (by decide)`.

Establish `hzero : ∀ (r : Fin t) (c : Fin i), M (Fin.castSucc (Fin.natAdd i r)) (Fin.castSucc (Fin.castAdd t c)) = 0`. Introduce `r c`. Establish `h₁ : Fin.castSucc (Fin.natAdd i r) = GlobalTheory.BZMir.Leib.ePG i t ⟨true, r⟩` using `Fin.ext (by rw [Fin.coe_castSucc, GlobalTheory.CompanionTheory.BZPhiPG.Cells.ePG_true_val, Fin.coe_natAdd])`. Establish `h₂ : Fin.castSucc (Fin.castAdd t c) = GlobalTheory.BZMir.Leib.ePG i t ⟨false, Fin.castSucc c⟩` using `Fin.ext (by rw [Fin.coe_castSucc, GlobalTheory.CompanionTheory.BZPhiPG.Cells.ePG_false_val, Fin.coe_castAdd])`. Rewrite using `[h₁, h₂]`.

Conclude with `hp' r (Fin.castSucc c)`. Establish `hlast : ∀ r : Fin t, M (Fin.castSucc (Fin.natAdd i r)) (Fin.last (i + t)) = 0`. Introduce `r`. Establish `h₁ : Fin.castSucc (Fin.natAdd i r) = GlobalTheory.BZMir.Leib.ePG i t ⟨true, r⟩` using `Fin.ext (by rw [Fin.coe_castSucc, GlobalTheory.CompanionTheory.BZPhiPG.Cells.ePG_true_val, Fin.coe_natAdd])`. Rewrite using `[h₁, ← GlobalTheory.BZMir.Leib.ePG_false_last i t]`.

Conclude with `hp' r (Fin.last i)`. Establish `hgen : ∀ (r : Fin t) (c : Fin i) (x y : Fin (i + t)), (x : ℕ) = i + r → (y : ℕ) = c → ((GlobalTheory.BZMir.mirabolicProjection k (i + t) (h : GlobalTheory.BZMir.Mir k (i + t)) : GL (Fin (i + t)) k) : Matrix (Fin (i + t)) (Fin (i + t)) k) x y = 0`. Introduce `r c x y hx hy`. Establish `hx' : x = Fin.natAdd i r` using `Fin.ext (by rw [hx, Fin.coe_natAdd])`. Establish `hy' : y = Fin.castAdd t c` using `Fin.ext (by rw [hy, Fin.coe_castAdd])`.

Substitute `hx' hy'` using the available equality. Conclude with `hzero r c`. Establish `hq : GlobalTheory.BZMir.mirabolicProjection k (i + t) (h : GlobalTheory.BZMir.Mir k (i + t)) ∈ GlobalTheory.CompanionTheory.BZPsiPG.Qp k i t`. Unfold `GlobalTheory.CompanionTheory.BZPsiPG.Qp`. Rewrite using `[GlobalTheory.SmGL.mem_parab_iff]`.

Introduce `a b ia jb hab`. Apply the tactic sequence `cases a <;> cases b`. Conclude with `absurd hab (by decide)`. Conclude with `absurd hab (by decide)`. Use `hgen ia jb _ _ ?_ ?_` and prove the remaining obligations.

Both sides reduce to the same expression. Both sides reduce to the same expression. Conclude with `absurd hab (by decide)`. Take `⟨x, hx⟩ : ∃ x : Fin i → k, x = fun a => M (Fin.castSucc (Fin.castAdd t a)) (Fin.last (i + t))` from `⟨_, rfl⟩`. Establish `hv : (fun r : Fin (i + t) => M (Fin.castSucc r) (Fin.last (i + t))) = GlobalTheory.CompanionTheory.BZPsiPG.topV k i t x`.

Use function extensionality and compare the values at `r`. Consider the cases of `r using Fin.addCases with`. Consider the case `left a => rw [GlobalTheory.CompanionTheory.BZPsiPG.topV, Fin.append_left, hx]`. Consider the case `right b => rw [GlobalTheory.CompanionTheory.BZPsiPG.topV, Fin.append_right, Pi.zero_apply]`. Conclude with `hlast b`.

Use `⟨x, ⟨_, hq⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Use `(GlobalTheory.CompanionTheory.BZPhiPG.Cells.eq_unip_glEmb (h : GlobalTheory.BZMir.Mir k (i + t))).trans ?_` and prove the remaining obligations. Conclude with `congrArg (· * GlobalTheory.BZMir.glEmb k (i + t) (GlobalTheory.BZMir.mirabolicProjection k (i + t) (h : GlobalTheory.BZMir.Mir k (i + t)))) (congrArg (fun w => GlobalTheory.BZMir.unip k (i + t) (Multiplicative.ofAdd w)) hv)`.
-/
theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ)
    (h : HPG k i t), ∃ (x : Fin i → k) (q : Qp k i t),
      (h : Mir k (i + t)) = uM k (i + t) (topV k i t x) * levi k (i + t) (q : GL (Fin (i + t)) k) := by
  intro k _ _ _ _ i t h
  set M : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k :=
    (((h : GlobalTheory.BZMir.Mir k (i + t)) : GL (Fin (i + t + 1)) k) :
      Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) with hM
  have hmem : ((h : GlobalTheory.BZMir.Mir k (i + t)) : GL (Fin (i + t + 1)) k) ∈
      GlobalTheory.SmGL.parab k (GlobalTheory.BZMir.Leib.ePG i t) := h.2
  have hp := GlobalTheory.SmGL.mem_parab_iff.1 hmem
  have hp' : ∀ (a : Fin t) (b : Fin (i + 1)),
      M (GlobalTheory.BZMir.Leib.ePG i t ⟨true, a⟩) (GlobalTheory.BZMir.Leib.ePG i t ⟨false, b⟩) = 0 :=
    fun a b => hp true false a b (by decide)
  have hzero : ∀ (r : Fin t) (c : Fin i),
      M (Fin.castSucc (Fin.natAdd i r)) (Fin.castSucc (Fin.castAdd t c)) = 0 := by
    intro r c
    have h₁ : Fin.castSucc (Fin.natAdd i r) = GlobalTheory.BZMir.Leib.ePG i t ⟨true, r⟩ :=
      Fin.ext (by rw [Fin.coe_castSucc, GlobalTheory.CompanionTheory.BZPhiPG.Cells.ePG_true_val, Fin.coe_natAdd])
    have h₂ : Fin.castSucc (Fin.castAdd t c) =
        GlobalTheory.BZMir.Leib.ePG i t ⟨false, Fin.castSucc c⟩ :=
      Fin.ext (by rw [Fin.coe_castSucc, GlobalTheory.CompanionTheory.BZPhiPG.Cells.ePG_false_val, Fin.coe_castAdd])
    rw [h₁, h₂]
    exact hp' r (Fin.castSucc c)
  have hlast : ∀ r : Fin t, M (Fin.castSucc (Fin.natAdd i r)) (Fin.last (i + t)) = 0 := by
    intro r
    have h₁ : Fin.castSucc (Fin.natAdd i r) = GlobalTheory.BZMir.Leib.ePG i t ⟨true, r⟩ :=
      Fin.ext (by rw [Fin.coe_castSucc, GlobalTheory.CompanionTheory.BZPhiPG.Cells.ePG_true_val, Fin.coe_natAdd])
    rw [h₁, ← GlobalTheory.BZMir.Leib.ePG_false_last i t]
    exact hp' r (Fin.last i)
  have hgen : ∀ (r : Fin t) (c : Fin i) (x y : Fin (i + t)), (x : ℕ) = i + r → (y : ℕ) = c →
      ((GlobalTheory.BZMir.mirabolicProjection k (i + t) (h : GlobalTheory.BZMir.Mir k (i + t)) : GL (Fin (i + t)) k) :
        Matrix (Fin (i + t)) (Fin (i + t)) k) x y = 0 := by
    intro r c x y hx hy
    have hx' : x = Fin.natAdd i r := Fin.ext (by rw [hx, Fin.coe_natAdd])
    have hy' : y = Fin.castAdd t c := Fin.ext (by rw [hy, Fin.coe_castAdd])
    subst hx' hy'
    exact hzero r c
  have hq : GlobalTheory.BZMir.mirabolicProjection k (i + t) (h : GlobalTheory.BZMir.Mir k (i + t)) ∈
      GlobalTheory.CompanionTheory.BZPsiPG.Qp k i t := by
    unfold GlobalTheory.CompanionTheory.BZPsiPG.Qp
    rw [GlobalTheory.SmGL.mem_parab_iff]
    intro a b ia jb hab
    cases a <;> cases b
    · exact absurd hab (by decide)
    · exact absurd hab (by decide)
    · refine hgen ia jb _ _ ?_ ?_
      · rfl
      · rfl
    · exact absurd hab (by decide)
  obtain ⟨x, hx⟩ : ∃ x : Fin i → k, x = fun a => M (Fin.castSucc (Fin.castAdd t a)) (Fin.last (i + t)) :=
    ⟨_, rfl⟩
  have hv : (fun r : Fin (i + t) => M (Fin.castSucc r) (Fin.last (i + t))) = GlobalTheory.CompanionTheory.BZPsiPG.topV k i t x := by
    funext r
    cases r using Fin.addCases with
    | left a => rw [GlobalTheory.CompanionTheory.BZPsiPG.topV, Fin.append_left, hx]
    | right b => rw [GlobalTheory.CompanionTheory.BZPsiPG.topV, Fin.append_right, Pi.zero_apply]; exact hlast b
  refine ⟨x, ⟨_, hq⟩, ?_⟩
  apply Subtype.ext
  refine (GlobalTheory.CompanionTheory.BZPhiPG.Cells.eq_unip_glEmb (h : GlobalTheory.BZMir.Mir k (i + t))).trans ?_
  exact congrArg (· * GlobalTheory.BZMir.glEmb k (i + t)
      (GlobalTheory.BZMir.mirabolicProjection k (i + t) (h : GlobalTheory.BZMir.Mir k (i + t))))
    (congrArg (fun w => GlobalTheory.BZMir.unip k (i + t) (Multiplicative.ofAdd w)) hv)

end GlobalTheory.CompanionTheory.BZPsiPG.HpgMem
