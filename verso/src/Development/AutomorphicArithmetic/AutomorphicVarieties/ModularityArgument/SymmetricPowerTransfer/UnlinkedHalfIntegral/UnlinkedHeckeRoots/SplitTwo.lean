import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnitFormC
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.QuadraticCharpolyCoeffDifference

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.GalN.V

/- English proof (translation)
Establish `hAn : A ≠ 0` using `hA.ne'`. Establish `hBn : B ≠ 0` using `hB.ne'`. Apply the tactic sequence `rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> intro h <;> field_simp at h`. Apply the tactic sequence `all_goals first`. Consider the case `nlinarith`.

Consider the case `exact h3 (by nlinarith)`. Consider the case `exact h4 (by nlinarith)`.
-/
private theorem ratio_ne {A B q x y : ℝ} (hA : 0 < A) (hB : 0 < B) (hq : 1 < q) (h1 : A < q * B) (h2 : B < q * A)
    (h3 : A ^ 2 ≠ q * B ^ 2) (h4 : B ^ 2 ≠ q * A ^ 2)
    (hx : x = A / B ∨ x = 1 ∨ x = B / A) (hy : y = A / B ∨ y = 1 ∨ y = B / A) : x ≠ q * y := by
  have hAn : A ≠ 0 := hA.ne'
  have hBn : B ≠ 0 := hB.ne'
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> intro h <;> field_simp at h
  all_goals first
    | nlinarith
    | exact h3 (by nlinarith)
    | exact h4 (by nlinarith)

/- English proof (translation)
Use `set M : Matrix (Fin 2) (Fin 2) K := (g : Matrix (Fin 2) (Fin 2) K) with hM`. Establish `hmon : M.charpoly.Monic` using `Matrix.charpoly_monic M`. Establish `hsplit : M.charpoly.Splits` using `IsAlgClosed.splits _`. Establish `hprod` using `hsplit.eq_prod_roots_of_monic hmon`. Establish `hcard : M.charpoly.roots.card = 2`.

Rewrite using `[← hsplit.natDegree_eq_card_roots, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]`. Take `⟨a, b, hab⟩` from `Multiset.card_eq_two.mp hcard`. Establish `hdet : M.det ≠ 0`. Use `(Matrix.isUnit_iff_isUnit_det M).mp (Units.isUnit g)` as an intermediate fact. Conclude with `this.ne_zero`.

Establish `hnz : ∀ c ∈ M.charpoly.roots, c ≠ 0`. Introduce `c hc h0`. Rewrite `hc` using `[Polynomial.mem_roots hmon.ne_zero, Polynomial.IsRoot, Matrix.eval_charpoly, h0]`. Apply `hdet` to reduce the goal to its premises. Simplify `hc` using `[Matrix.det_neg]`.

Establish `ha : a ≠ 0` using `hnz a (by rw [hab]; simp)`. Establish `hb : b ≠ 0` using `hnz b (by rw [hab]; simp)`. Use `⟨Units.mk0 a ha, Units.mk0 b hb, ?_⟩` and prove the remaining obligations. Rewrite using `[hprod, hab]`. Simplify using the standard rewrite rules.
-/
private theorem split_two {K : Type} [Field K] [IsAlgClosed K] (g : GL (Fin 2) K) :
    ∃ a b : Kˣ, (g : Matrix (Fin 2) (Fin 2) K).charpoly = (X - C (a : K)) * (X - C (b : K)) := by
  set M : Matrix (Fin 2) (Fin 2) K := (g : Matrix (Fin 2) (Fin 2) K) with hM
  have hmon : M.charpoly.Monic := Matrix.charpoly_monic M
  have hsplit : M.charpoly.Splits := IsAlgClosed.splits _
  have hprod := hsplit.eq_prod_roots_of_monic hmon
  have hcard : M.charpoly.roots.card = 2 := by
    rw [← hsplit.natDegree_eq_card_roots, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.mp hcard
  have hdet : M.det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det M).mp (Units.isUnit g)
    exact this.ne_zero
  have hnz : ∀ c ∈ M.charpoly.roots, c ≠ 0 := by
    intro c hc h0
    rw [Polynomial.mem_roots hmon.ne_zero, Polynomial.IsRoot, Matrix.eval_charpoly, h0] at hc
    apply hdet
    simpa [Matrix.det_neg] using hc
  have ha : a ≠ 0 := hnz a (by rw [hab]; simp)
  have hb : b ≠ 0 := hnz b (by rw [hab]; simp)
  refine ⟨Units.mk0 a ha, Units.mk0 b hb, ?_⟩
  rw [hprod, hab]
  simp

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ l _ ι r hR hN w hw A hA _`. Take `⟨s, hs⟩` from `exists_isFrob hA`. Use `⟨s, 1, le_rfl, by simpa using hs, ?_⟩` and prove the remaining obligations. Introduce `α β hα hβ k hk heq`. Take `⟨a, b, hab⟩` from `split_two (r s)`.

Establish `hc` using `(ad0Facts l (G F Ω) r).2.2.2.2.1 s a b hab`. Establish `ra : (r s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.IsRoot (a : Qbar l)`. Rewrite using `[hab]`. Simplify using the standard rewrite rules. Establish `rb : (r s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.IsRoot (b : Qbar l)`.

Rewrite using `[hab]`. Simplify using the standard rewrite rules. Establish `hA0 : 0 < ‖ι (a : Qbar l)‖` using `norm_pos_iff.2 (by simp)`. Establish `hB0 : 0 < ‖ι (b : Qbar l)‖` using `norm_pos_iff.2 (by simp)`. Establish `hq : (1 : ℝ) < ((normV w : ℕ) : ℝ)`.

Use `hR w hw A hA s hs _ _ ra ra` as an intermediate fact. Assume the negation of the conclusion as `h`. Use polynomial arithmetic with `[not_lt.mp h]`. Establish `root : ∀ x : Qbar l, (ad0 r s : Matrix (Fin 3) (Fin 3) (Qbar l)).charpoly.IsRoot x → ‖ι x‖ = ‖ι (a : Qbar l)‖ / ‖ι (b : Qbar l)‖ ∨ ‖ι x‖ = 1 ∨ ‖ι x‖ = ‖ι (b : Qbar l)‖ / ‖ι (a : Qbar l)‖`. Introduce `x hx`.

Rewrite `hx` using `[hc]`. Simplify using `only [IsRoot.def, eval_mul, eval_sub, eval_X, eval_C, mul_eq_zero, sub_eq_zero] at hx`. Break down `hx with (rfl | rfl) | rfl` into its components or cases. Use `left`. Simplify using the standard rewrite rules.

Use `right`. Use `left`. Simplify using the standard rewrite rules. Use `right`. Use `right`.

Simplify using the standard rewrite rules. Establish `hn : ‖ι α‖ ^ k = (((normV w : ℕ) : ℝ) * ‖ι β‖) ^ k`. Use `congrArg (fun z => ‖ι z‖) heq` as an intermediate fact. Simplify `this` using `[map_pow, map_mul, norm_pow, norm_mul, Complex.norm_natCast]`. Establish `hn' : ‖ι α‖ = ((normV w : ℕ) : ℝ) * ‖ι β‖` using `(pow_left_inj₀ (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) (by omega)).1 hn`.

Conclude with `ratio_ne hA0 hB0 hq (hR w hw A hA s hs _ _ ra rb) (hR w hw A hA s hs _ _ rb ra) (hN w hw A hA s hs _ _ ra rb) (hN w hw A hA s hs _ _ rb ra) (root α hα) (root β hβ) hn'`.
-/
theorem UpperTheory.V.Z.Sym.Unl.adUnl :
    UpperTheory.V.Z.Sym.Unl.AdUnl := by
  intro F Ω _ _ _ _ _ l _ ι r hR hN w hw A hA _
  obtain ⟨s, hs⟩ := exists_isFrob hA
  refine ⟨s, 1, le_rfl, by simpa using hs, ?_⟩
  intro α β hα hβ k hk heq
  obtain ⟨a, b, hab⟩ := split_two (r s)
  have hc := (ad0Facts l (G F Ω) r).2.2.2.2.1 s a b hab
  have ra : (r s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.IsRoot (a : Qbar l) := by
    rw [hab]; simp
  have rb : (r s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.IsRoot (b : Qbar l) := by
    rw [hab]; simp
  have hA0 : 0 < ‖ι (a : Qbar l)‖ := norm_pos_iff.2 (by simp)
  have hB0 : 0 < ‖ι (b : Qbar l)‖ := norm_pos_iff.2 (by simp)
  have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by
    have := hR w hw A hA s hs _ _ ra ra
    by_contra h
    nlinarith [not_lt.mp h]
  have root : ∀ x : Qbar l, (ad0 r s : Matrix (Fin 3) (Fin 3) (Qbar l)).charpoly.IsRoot x →
      ‖ι x‖ = ‖ι (a : Qbar l)‖ / ‖ι (b : Qbar l)‖ ∨ ‖ι x‖ = 1 ∨ ‖ι x‖ = ‖ι (b : Qbar l)‖ / ‖ι (a : Qbar l)‖ := by
    intro x hx
    rw [hc] at hx
    simp only [IsRoot.def, eval_mul, eval_sub, eval_X, eval_C, mul_eq_zero, sub_eq_zero] at hx
    rcases hx with (rfl | rfl) | rfl
    · left; simp
    · right; left; simp
    · right; right; simp
  have hn : ‖ι α‖ ^ k = (((normV w : ℕ) : ℝ) * ‖ι β‖) ^ k := by
    have := congrArg (fun z => ‖ι z‖) heq
    simpa [map_pow, map_mul, norm_pow, norm_mul, Complex.norm_natCast] using this
  have hn' : ‖ι α‖ = ((normV w : ℕ) : ℝ) * ‖ι β‖ :=
    (pow_left_inj₀ (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) (by omega)).1 hn
  exact ratio_ne hA0 hB0 hq (hR w hw A hA s hs _ _ ra rb) (hR w hw A hA s hs _ _ rb ra)
    (hN w hw A hA s hs _ _ ra rb) (hN w hw A hA s hs _ _ rb ra) (root α hα) (root β hβ) hn'
