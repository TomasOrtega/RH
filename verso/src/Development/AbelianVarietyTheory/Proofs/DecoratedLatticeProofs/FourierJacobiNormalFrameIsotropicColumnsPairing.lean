import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SymRead
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.JacCols

/- English proof (translation)
Introduce `D k _ _ _ _ p ρ J n _ _ c s hh F₀ F hF i`. Take `⟨hc, h0, h1, h2⟩` from `hF`. Substitute `hc` using the available equality. Establish `hpr : ∀ a, p.pr a = Witness.prH p a` using `fun _ => rfl`. Establish `hG : (J.W.gram)ᴴ = J.W.gram`.

Use extensionality with `a b`. Rewrite using `[Matrix.conjTranspose_apply]`. Conclude with `GlobalTheory.DualPairCheck.gram_star J.W b a`. Establish `L : ∀ {Z : Type} [Fintype Z] (M : Matrix (Fin J.W.rank) Z k) (z : Z), ∑ r, ∑ r', p.pr (star (J.d.e r i)) * p.pr (J.W.gram r r') * M r' z = (((J.d.eᴴ * J.W.gram).map (Witness.prH p)) * M) i z`. Introduce `Z _ M z`.

Rewrite using `[Finset.sum_comm, Matrix.mul_apply]`. Use `Finset.sum_congr rfl fun r' _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_mul, Matrix.map_apply, Matrix.mul_apply, map_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, Matrix.conjTranspose_apply, hpr, hpr]`. Establish `Ls : ∀ (M : Matrix (Fin J.W.rank) (Fin ρ) D.host.E) (j : Fin ρ) (t : k), ∑ r, ∑ r', p.pr (star (J.d.e r i)) * p.pr (J.W.gram r r') * (t * p.pr (M r' j)) = t * Witness.prH p ((J.d.eᴴ * J.W.gram * M) i j)`. Introduce `M j t`. Use `L (t • M.map (Witness.prH p)) j` as an intermediate fact. Simplify using `only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at this`.

Simplify using `only [hpr] at this ⊢`. Rewrite using `[this, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul, ← Matrix.map_mul]`. Both sides reduce to the same expression. Establish `eI : J.d.eᴴ * J.W.gram * J.d.i₀ = 0`. Use `congrArg Matrix.conjTranspose J.d.i₀e` as an intermediate fact.

Rewrite `this` using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG, Matrix.conjTranspose_zero, ← Matrix.mul_assoc]`. Then use the resulting hypothesis. Establish `eE' : J.d.eᴴ * J.W.gram * J.d.e' = 1`. Use `congrArg Matrix.conjTranspose J.d.e'e` as an intermediate fact. Rewrite `this` using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG, Matrix.conjTranspose_one, ← Matrix.mul_assoc]`. Then use the resulting hypothesis. Use `⟨Sum.inr ⟨i.val, by omega⟩, Sum.inr ⟨2 * ρ - 1 - i.val, by omega⟩, fun r => h1 i _ rfl r, fun r => h2 i _ (by simp only; omega) r, ?_⟩` and prove the remaining obligations.

Introduce `m hm`. Break down `m with a | ⟨j, hj⟩` into its components or cases. Rewrite using `[L F.β (Sum.inl a)]`. Establish `hcol : ∀ r, F.β r (Sum.inl a) = (J.d.i₀.map (Witness.prH p) * F₀.β) r a` using `fun r => h0 r a`. Rewrite using `[Matrix.mul_apply]`.

Simplify using `only [hcol]`. Rewrite using `[← Matrix.mul_apply, ← Matrix.mul_assoc, ← Matrix.map_mul, eI, Matrix.map_zero _ (map_zero _), Matrix.zero_mul, Matrix.zero_apply]`. Distinguish the cases in `hjρ : j < ρ`. Establish `hcol : ∀ r, F.β r (Sum.inr ⟨j, hj⟩) = s * p.xi ^ (ρ - j) * p.pr (J.d.e r ⟨j, hjρ⟩)` using `fun r => h1 ⟨j, hjρ⟩ _ rfl r`. Simplify using `only [hcol]`.

Rewrite using `[Ls, J.d.ee, Matrix.zero_apply, map_zero, mul_zero]`. Use `set i' : Fin ρ := ⟨2 * ρ - 1 - j, by omega⟩ with hi'`. Establish `hcol : ∀ r, F.β r (Sum.inr ⟨j, hj⟩) = s * (hh / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i'.val) * p.pr (J.d.e' r i')` using `fun r => h2 i' _ (by simp only [hi']; omega) r`. Simplify using `only [hcol]`. Establish `hne : i ≠ i'`.

Introduce `h`. Apply `hm` to reduce the goal to its premises. Rewrite using `[h]`. Simplify using `only [hi', Sum.inr.injEq, Fin.mk.injEq]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[Ls, eE', Matrix.one_apply_ne hne, map_zero, mul_zero]`.
-/
theorem cols_pair : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ρ : ℕ) (J : JacLev D ρ) (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (s hh : k) (F₀ : Frame k J.W₀.rank n) (F : Frame k J.W.rank (n ⊕ Fin c)), p.IsJacFrame J s hh F₀ F → ∀ i : Fin ρ, ∃ m₀ m₁ : n ⊕ Fin c, (∀ r, F.β r m₀ = s * p.xi ^ (ρ - i.val) * p.pr (J.d.e r i)) ∧ (∀ r, F.β r m₁ = s * (hh / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val) * p.pr (J.d.e' r i)) ∧ ∀ m, m ≠ m₁ → ∑ r, ∑ r', p.pr (star (J.d.e r i)) * p.pr (J.W.gram r r') * F.β r' m = 0 := by
  intro D k _ _ _ _ p ρ J n _ _ c s hh F₀ F hF i
  obtain ⟨hc, h0, h1, h2⟩ := hF
  subst hc
  have hpr : ∀ a, p.pr a = Witness.prH p a := fun _ => rfl

  have hG : (J.W.gram)ᴴ = J.W.gram := by
    ext a b
    rw [Matrix.conjTranspose_apply]
    exact GlobalTheory.DualPairCheck.gram_star J.W b a

  have L : ∀ {Z : Type} [Fintype Z] (M : Matrix (Fin J.W.rank) Z k) (z : Z),
      ∑ r, ∑ r', p.pr (star (J.d.e r i)) * p.pr (J.W.gram r r') * M r' z =
        (((J.d.eᴴ * J.W.gram).map (Witness.prH p)) * M) i z := by
    intro Z _ M z
    rw [Finset.sum_comm, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun r' _ => ?_
    rw [← Finset.sum_mul, Matrix.map_apply, Matrix.mul_apply, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_mul, Matrix.conjTranspose_apply, hpr, hpr]
  have Ls : ∀ (M : Matrix (Fin J.W.rank) (Fin ρ) D.host.E) (j : Fin ρ) (t : k),
      ∑ r, ∑ r', p.pr (star (J.d.e r i)) * p.pr (J.W.gram r r') * (t * p.pr (M r' j)) =
        t * Witness.prH p ((J.d.eᴴ * J.W.gram * M) i j) := by
    intro M j t
    have := L (t • M.map (Witness.prH p)) j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at this
    simp only [hpr] at this ⊢
    rw [this, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul, ← Matrix.map_mul]
    rfl

  have eI : J.d.eᴴ * J.W.gram * J.d.i₀ = 0 := by
    have := congrArg Matrix.conjTranspose J.d.i₀e
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG,
      Matrix.conjTranspose_zero, ← Matrix.mul_assoc] at this
  have eE' : J.d.eᴴ * J.W.gram * J.d.e' = 1 := by
    have := congrArg Matrix.conjTranspose J.d.e'e
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG,
      Matrix.conjTranspose_one, ← Matrix.mul_assoc] at this
  refine ⟨Sum.inr ⟨i.val, by omega⟩, Sum.inr ⟨2 * ρ - 1 - i.val, by omega⟩, fun r => h1 i _ rfl r,
    fun r => h2 i _ (by simp only; omega) r, ?_⟩
  intro m hm
  rcases m with a | ⟨j, hj⟩
  · rw [L F.β (Sum.inl a)]
    have hcol : ∀ r, F.β r (Sum.inl a) = (J.d.i₀.map (Witness.prH p) * F₀.β) r a := fun r => h0 r a
    rw [Matrix.mul_apply]
    simp only [hcol]
    rw [← Matrix.mul_apply, ← Matrix.mul_assoc, ← Matrix.map_mul, eI, Matrix.map_zero _ (map_zero _), Matrix.zero_mul,
      Matrix.zero_apply]
  · by_cases hjρ : j < ρ
    · have hcol : ∀ r, F.β r (Sum.inr ⟨j, hj⟩) = s * p.xi ^ (ρ - j) * p.pr (J.d.e r ⟨j, hjρ⟩) :=
        fun r => h1 ⟨j, hjρ⟩ _ rfl r
      simp only [hcol]
      rw [Ls, J.d.ee, Matrix.zero_apply, map_zero, mul_zero]
    · set i' : Fin ρ := ⟨2 * ρ - 1 - j, by omega⟩ with hi'
      have hcol : ∀ r, F.β r (Sum.inr ⟨j, hj⟩) = s * (hh / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i'.val) * p.pr (J.d.e' r i') :=
        fun r => h2 i' _ (by simp only [hi']; omega) r
      simp only [hcol]
      have hne : i ≠ i' := by
        intro h
        apply hm
        rw [h]
        simp only [hi', Sum.inr.injEq, Fin.mk.injEq]
        omega
      rw [Ls, eE', Matrix.one_apply_ne hne, map_zero, mul_zero]

end GlobalTheory.LocMod.JacCols
