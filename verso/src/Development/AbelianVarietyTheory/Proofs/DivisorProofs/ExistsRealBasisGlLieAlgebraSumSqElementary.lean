import Development.AbelianVarietyTheory.Definitions.Divisors.GlRes
import Development.AbelianVarietyTheory.Definitions.Divisors.IsExpLieAlgebraComplexUnits
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasKOp
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic GlobalTheory.HCAlpha
open scoped ContDiff
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ _ a`. Set `b0 : Module.Basis (Σ _ : InfinitePlace E, Fin 2) ℝ (Cinf E)` to `Pi.basis fun _ => Complex.basisOneI`. Establish `hb0 : ∀ w s, b0 ⟨w, s⟩ = Pi.single w (Complex.basisOneI s)`. Introduce `w s`. Simplify using `[b0]`.

Set `b1` to `b0.matrix (Fin a) (Fin a)`. Establish `hs : (0 : ℝ) < Real.sqrt 2` using `Real.sqrt_pos.2 two_pos`. Establish `hu : ∀ _ : Fin a × Fin a × (Σ _ : InfinitePlace E, Fin 2), IsUnit (Real.sqrt 2)` using `fun _ => IsUnit.mk0 _ hs.ne'`. Set `b2` to `(b1.isUnitSMul hu).map (Submodule.topEquiv (R := ℝ) (M := Matrix (Fin a) (Fin a) (Cinf E))).symm`. Set `e` to `Fintype.equivFin (Fin a × Fin a × (Σ _ : InfinitePlace E, Fin 2))`.

Use `⟨_, b2.reindex e, ?_⟩` and prove the remaining obligations. Introduce `A _ _ ρ`. Set `F : InfinitePlace E → Fin a → Fin a → A` to `fun w i j => ρ ⟨Matrix.single i j (Pi.single w 1), Submodule.mem_top⟩ ^ 2 + ρ ⟨Matrix.single i j (Pi.single w Complex.I), Submodule.mem_top⟩ ^ 2`. Set `G : InfinitePlace E → A` to `fun w => ∑ i, ∑ j, F w i j`. Establish `hsm : ∀ (r : ℝ) (X : Matrix (Fin a) (Fin a) (Cinf E)), ρ ⟨r • X, Submodule.mem_top⟩ = r • ρ ⟨X, Submodule.mem_top⟩`.

Introduce `r X`. Rewrite using `[← map_smul]`. Both sides reduce to the same expression. Establish `hb2 : ∀ i j w s, ρ (b2 (i, j, ⟨w, s⟩)) * ρ (b2 (i, j, ⟨w, s⟩)) = ρ ⟨Matrix.single i j (Pi.single w (Complex.basisOneI s)), Submodule.mem_top⟩ ^ 2 + ρ ⟨Matrix.single i j (Pi.single w (Complex.basisOneI s)), Submodule.mem_top⟩ ^ 2`. Introduce `i j w s`.

Establish `: b2 (i, j, ⟨w, s⟩) = ⟨Real.sqrt 2 • Matrix.single i j (Pi.single w (Complex.basisOneI s)), Submodule.mem_top⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[b2, b1, Module.Basis.isUnitSMul_apply, hb0]`. Rewrite using `[this, hsm, smul_mul_smul, Real.mul_self_sqrt (by norm_num), two_smul, sq]`. Establish `hL : ∑ k, ρ (b2.reindex e k) * ρ (b2.reindex e k) = ∑ w, (G w + G w)`.

Simplify using `only [Module.Basis.reindex_apply]`. Rewrite using `[Equiv.sum_comp e.symm (fun x => ρ (b2 x) * ρ (b2 x))]`. Simplify using `only [Fintype.sum_prod_type, Fintype.sum_sigma, Fin.sum_univ_two, hb2, Complex.coe_basisOneI, Matrix.cons_val_zero, Matrix.cons_val_one, G, F]`. Simplify using `only [← Finset.sum_add_distrib]`. Use `conv_rhs => rw [Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `conv_rhs => rw [Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Normalize the expressions using the abelian group laws. Establish `hτ : ∀ τ : E →+* ℂ, ∀ i j, ρ ⟨Matrix.single i j (atEmb τ 1), Submodule.mem_top⟩ ^ 2 + ρ ⟨Matrix.single i j (atEmb τ Complex.I), Submodule.mem_top⟩ ^ 2 = F (InfinitePlace.mk τ) i j`.

Introduce `τ i j`. Establish `hA1 : atEmb τ 1 = Pi.single (InfinitePlace.mk τ) 1`. Apply the tactic sequence `unfold atEmb; split_ifs <;> simp`. Establish `hAI : ρ ⟨Matrix.single i j (atEmb τ Complex.I), Submodule.mem_top⟩ ^ 2 = ρ ⟨Matrix.single i j (Pi.single (InfinitePlace.mk τ) Complex.I), Submodule.mem_top⟩ ^ 2`. Unfold `atEmb`.

Use `split_ifs with h`. Both sides reduce to the same expression. Establish `h1 : (⟨Matrix.single i j (Pi.single (InfinitePlace.mk τ) (starRingEnd ℂ Complex.I)), Submodule.mem_top⟩ : glL E a) = -⟨Matrix.single i j (Pi.single (InfinitePlace.mk τ) Complex.I), Submodule.mem_top⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[Pi.single_neg, Matrix.single_neg]`.

Rewrite using `[h1, map_neg, neg_sq]`. Simplify using `only [F, hAI, hA1]`. Establish `hR : ∑ τ : E →+* ℂ, ∑ i : Fin a, ∑ j : Fin a, (ρ ⟨Matrix.single i j (atEmb τ 1), Submodule.mem_top⟩ ^ 2 + ρ ⟨Matrix.single i j (atEmb τ Complex.I), Submodule.mem_top⟩ ^ 2) = ∑ w, (G w + G w)`. Simplify using `only [hτ]`. Express the relevant statement in the definitionally equal form `∑ τ : E →+* ℂ, G (InfinitePlace.mk τ) = _`.

Rewrite using `[← Finset.sum_fiberwise Finset.univ InfinitePlace.mk (fun τ => G (InfinitePlace.mk τ))]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_congr rfl (g := fun _ => G w) (fun τ hτ' => by rw [(Finset.mem_filter.1 hτ').2]), Finset.sum_const, InfinitePlace.card_filter_mk_eq]`. Establish `: w.mult = 2`. Simplify using `[InfinitePlace.mult, InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)]`.

Rewrite using `[this, two_smul]`. Rewrite using `[hL, hR]`.
-/
theorem glBasis_sum_sq : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∃ (d : ℕ) (b : Module.Basis (Fin d) ℝ (glL E a)), ∀ (A : Type) [Ring A] [Algebra ℝ A] (ρ : glL E a →ₗ[ℝ] A), ∑ k, ρ (b k) * ρ (b k) = ∑ τ : E →+* ℂ, ∑ i : Fin a, ∑ j : Fin a, (ρ ⟨Matrix.single i j (atEmb τ 1), Submodule.mem_top⟩ ^ 2 + ρ ⟨Matrix.single i j (atEmb τ Complex.I), Submodule.mem_top⟩ ^ 2) := by
  intro E _ _ _ a
  classical
  let b0 : Module.Basis (Σ _ : InfinitePlace E, Fin 2) ℝ (Cinf E) := Pi.basis fun _ => Complex.basisOneI
  have hb0 : ∀ w s, b0 ⟨w, s⟩ = Pi.single w (Complex.basisOneI s) := by
    intro w s; simp [b0]
  let b1 := b0.matrix (Fin a) (Fin a)
  have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hu : ∀ _ : Fin a × Fin a × (Σ _ : InfinitePlace E, Fin 2), IsUnit (Real.sqrt 2) :=
    fun _ => IsUnit.mk0 _ hs.ne'
  let b2 := (b1.isUnitSMul hu).map (Submodule.topEquiv (R := ℝ) (M := Matrix (Fin a) (Fin a) (Cinf E))).symm
  let e := Fintype.equivFin (Fin a × Fin a × (Σ _ : InfinitePlace E, Fin 2))
  refine ⟨_, b2.reindex e, ?_⟩
  intro A _ _ ρ
  let F : InfinitePlace E → Fin a → Fin a → A := fun w i j =>
    ρ ⟨Matrix.single i j (Pi.single w 1), Submodule.mem_top⟩ ^ 2 +
      ρ ⟨Matrix.single i j (Pi.single w Complex.I), Submodule.mem_top⟩ ^ 2
  let G : InfinitePlace E → A := fun w => ∑ i, ∑ j, F w i j
  have hsm : ∀ (r : ℝ) (X : Matrix (Fin a) (Fin a) (Cinf E)),
      ρ ⟨r • X, Submodule.mem_top⟩ = r • ρ ⟨X, Submodule.mem_top⟩ := by
    intro r X
    rw [← map_smul]; rfl
  have hb2 : ∀ i j w s, ρ (b2 (i, j, ⟨w, s⟩)) * ρ (b2 (i, j, ⟨w, s⟩)) =
      ρ ⟨Matrix.single i j (Pi.single w (Complex.basisOneI s)), Submodule.mem_top⟩ ^ 2 +
      ρ ⟨Matrix.single i j (Pi.single w (Complex.basisOneI s)), Submodule.mem_top⟩ ^ 2 := by
    intro i j w s
    have : b2 (i, j, ⟨w, s⟩) = ⟨Real.sqrt 2 • Matrix.single i j (Pi.single w (Complex.basisOneI s)), Submodule.mem_top⟩ := by
      apply Subtype.ext
      simp [b2, b1, Module.Basis.isUnitSMul_apply, hb0]
    rw [this, hsm, smul_mul_smul, Real.mul_self_sqrt (by norm_num), two_smul, sq]
  have hL : ∑ k, ρ (b2.reindex e k) * ρ (b2.reindex e k) = ∑ w, (G w + G w) := by
    simp only [Module.Basis.reindex_apply]
    rw [Equiv.sum_comp e.symm (fun x => ρ (b2 x) * ρ (b2 x))]
    simp only [Fintype.sum_prod_type, Fintype.sum_sigma, Fin.sum_univ_two, hb2, Complex.coe_basisOneI,
      Matrix.cons_val_zero, Matrix.cons_val_one, G, F]
    simp only [← Finset.sum_add_distrib]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun w _ => ?_
    abel
  have hτ : ∀ τ : E →+* ℂ, ∀ i j,
      ρ ⟨Matrix.single i j (atEmb τ 1), Submodule.mem_top⟩ ^ 2 +
        ρ ⟨Matrix.single i j (atEmb τ Complex.I), Submodule.mem_top⟩ ^ 2 = F (InfinitePlace.mk τ) i j := by
    intro τ i j
    have hA1 : atEmb τ 1 = Pi.single (InfinitePlace.mk τ) 1 := by
      unfold atEmb; split_ifs <;> simp
    have hAI : ρ ⟨Matrix.single i j (atEmb τ Complex.I), Submodule.mem_top⟩ ^ 2 =
        ρ ⟨Matrix.single i j (Pi.single (InfinitePlace.mk τ) Complex.I), Submodule.mem_top⟩ ^ 2 := by
      unfold atEmb
      split_ifs with h
      · rfl
      · have h1 : (⟨Matrix.single i j (Pi.single (InfinitePlace.mk τ) (starRingEnd ℂ Complex.I)), Submodule.mem_top⟩ : glL E a) =
            -⟨Matrix.single i j (Pi.single (InfinitePlace.mk τ) Complex.I), Submodule.mem_top⟩ := by
          apply Subtype.ext
          simp [Pi.single_neg, Matrix.single_neg]
        rw [h1, map_neg, neg_sq]
    simp only [F, hAI, hA1]
  have hR : ∑ τ : E →+* ℂ, ∑ i : Fin a, ∑ j : Fin a,
      (ρ ⟨Matrix.single i j (atEmb τ 1), Submodule.mem_top⟩ ^ 2 +
        ρ ⟨Matrix.single i j (atEmb τ Complex.I), Submodule.mem_top⟩ ^ 2) = ∑ w, (G w + G w) := by
    simp only [hτ]
    change ∑ τ : E →+* ℂ, G (InfinitePlace.mk τ) = _
    rw [← Finset.sum_fiberwise Finset.univ InfinitePlace.mk (fun τ => G (InfinitePlace.mk τ))]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => G w) (fun τ hτ' => by rw [(Finset.mem_filter.1 hτ').2]),
      Finset.sum_const, InfinitePlace.card_filter_mk_eq]
    have : w.mult = 2 := by
      simp [InfinitePlace.mult, InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)]
    rw [this, two_smul]
  rw [hL, hR]

end GlobalTheory
