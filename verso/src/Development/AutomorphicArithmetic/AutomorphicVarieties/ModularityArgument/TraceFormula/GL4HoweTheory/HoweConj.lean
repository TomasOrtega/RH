import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace

open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

private noncomputable def dg {E : Type} [Field E] (n : ℕ) (β : Eˣ) : GL (Fin n) E :=
  ⟨Matrix.diagonal fun i => ((β ^ (-((i : ℕ) : ℤ)) : Eˣ) : E), Matrix.diagonal fun i => ((β ^ ((i : ℕ) : ℤ) : Eˣ) : E),
    by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext i
      rw [← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one],
    by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext i
      rw [← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one]⟩

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(Matrix.diagonal (fun i : Fin n => ((β ^ (-((i : ℕ) : ℤ)) : Eˣ) : E)) * (x : Matrix (Fin n) (Fin n) E) * Matrix.diagonal (fun i : Fin n => ((β ^ ((i : ℕ) : ℤ) : Eˣ) : E))) i j = _`. Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul, sub_eq_add_neg, zpow_add, Units.val_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem dg_conj {E : Type} [Field E] {n : ℕ} (β : Eˣ) (x : GL (Fin n) E) (i j : Fin n) :
    ((dg n β * x * (dg n β)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j =
      ((β ^ (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) : Eˣ) : E) * (x : Matrix (Fin n) (Fin n) E) i j := by
  change (Matrix.diagonal (fun i : Fin n => ((β ^ (-((i : ℕ) : ℤ)) : Eˣ) : E)) * (x : Matrix (Fin n) (Fin n) E) *
    Matrix.diagonal (fun i : Fin n => ((β ^ ((i : ℕ) : ℤ) : Eˣ) : E))) i j = _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, sub_eq_add_neg, zpow_add, Units.val_mul]
  ring

/- English proof (translation)
Introduce `E _ _ _ _ n V _ _ π ϖ β a c t hβ ψ₀ ψ hψ h`. Take `⟨w, hw, h0⟩` from `(Submodule.ne_bot_iff _).1 h`. Use `(Submodule.ne_bot_iff _).2 ⟨π (dg n β)⁻¹ w, fun x hx => ?_, fun e => h0 ?_⟩` and prove the remaining obligations. Establish `hy : dg n β * x * (dg n β)⁻¹ ∈ howeSet n ϖ a (c - t)` using `fun i j => by`. Establish `e : ((dg n β * x * (dg n β)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j = ((β ^ (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) : Eˣ) : E) * ((x : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j)`.

Rewrite using `[dg_conj, mul_sub]`. Use `congr 1`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Matrix.one_apply_ne hij]`. Establish `e2 : valuation E ((β ^ (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) : Eˣ) : E) = valuation E ((ϖ ^ (t * (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ))) : Eˣ) : E)`. Rewrite using `[zpow_mul, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val (ϖ ^ t), map_zpow₀, map_zpow₀, hβ]`. Rewrite using `[e, map_mul, e2, show a + (c - t) * (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) = t * (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) + (a + c * (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))) by ring, zpow_add, Units.val_mul, map_mul]`. Conclude with `mul_le_mul_right (hx i j) _`.

Establish `hs : GlobalTheory.Whittaker.superDiag (dg n β * x * (dg n β)⁻¹) = β * GlobalTheory.Whittaker.superDiag x`. Simplify using `only [GlobalTheory.Whittaker.superDiag, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Rewrite using `[dg_conj, (Finset.mem_filter.1 hj).2]`. Simplify using the standard rewrite rules.

Establish `h1` using `hw _ hy`. Rewrite `h1` using `[hs, ← hψ]`. Rewrite using `[← map_smul, ← h1, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]`. Use `congr 2`. Use `group`.

Use `congrArg (π (dg n β)) e` as an intermediate fact. Rewrite `this` using `[map_zero, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.V.Z.Tf.L4.howeConj :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) E) V) (ϖ β : Eˣ) (a c t : ℤ),
      valuation E (β : E) = valuation E ((ϖ ^ t : Eˣ) : E) → ∀ ψ₀ ψ : AddChar E Circle, (∀ x, ψ x = ψ₀ (β * x)) →
      howeSpace π ψ₀ (howeSet n ϖ a (c - t)) ≠ ⊥ → howeSpace π ψ (howeSet n ϖ a c) ≠ ⊥ := by
  intro E _ _ _ _ n V _ _ π ϖ β a c t hβ ψ₀ ψ hψ h
  obtain ⟨w, hw, h0⟩ := (Submodule.ne_bot_iff _).1 h
  refine (Submodule.ne_bot_iff _).2 ⟨π (dg n β)⁻¹ w, fun x hx => ?_, fun e => h0 ?_⟩
  · have hy : dg n β * x * (dg n β)⁻¹ ∈ howeSet n ϖ a (c - t) := fun i j => by
      have e : ((dg n β * x * (dg n β)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j =
          ((β ^ (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) : Eˣ) : E) *
            ((x : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) := by
        rw [dg_conj, mul_sub]
        congr 1
        by_cases hij : i = j
        · subst hij; simp
        · simp [Matrix.one_apply_ne hij]
      have e2 : valuation E ((β ^ (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) : Eˣ) : E) =
          valuation E ((ϖ ^ (t * (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ))) : Eˣ) : E) := by
        rw [zpow_mul, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val (ϖ ^ t), map_zpow₀, map_zpow₀, hβ]
      rw [e, map_mul, e2, show a + (c - t) * (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) =
        t * (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) + (a + c * (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))) by ring, zpow_add, Units.val_mul, map_mul]
      exact mul_le_mul_right (hx i j) _
    have hs : GlobalTheory.Whittaker.superDiag (dg n β * x * (dg n β)⁻¹) = β * GlobalTheory.Whittaker.superDiag x := by
      simp only [GlobalTheory.Whittaker.superDiag, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
      rw [dg_conj, (Finset.mem_filter.1 hj).2]
      simp
    have h1 := hw _ hy
    rw [hs, ← hψ] at h1
    rw [← map_smul, ← h1, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 2
    group
  · have := congrArg (π (dg n β)) e
    rwa [map_zero, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
