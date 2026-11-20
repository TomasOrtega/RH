import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

/- English proof (translation)
Take `⟨_, _, hmono, hmon, hconst, _⟩` from `h`. Establish `heq : (fun z : Circle => ((A * (tor a k z * B) : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j) = ∑ l : Fin a, fun z : Circle => (A : Matrix (Fin a) (Fin a) ℂ) i l * ((if (l:ℕ) < k then (z:ℂ) else 1) * (B : Matrix (Fin a) (Fin a) ℂ) l j)`. Use function extensionality and compare the values at `z`. Rewrite using `[Finset.sum_apply, Units.val_mul, Units.val_mul, Matrix.mul_apply]`. Use `congr 1`.

Use function extensionality and compare the values at `l`. Simplify using `only [tor, dg, Matrix.diagonal_mul]`. Use `split_ifs`. Simplify using `only [Circle.toUnits] first`. Consider the case `rfl`.

Consider the case `simp [unitSphereToUnits_apply_coe]`. Simplify using the standard rewrite rules. Rewrite using `[heq]`. Prove the components needed by the constructor for the conclusion. Use `Submodule.sum_mem _ fun l _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hl : (l:ℕ) < k`. Use `(hmon ((A : Matrix (Fin a) (Fin a) ℂ) i l * (B : Matrix (Fin a) (Fin a) ℂ) l j) 1).1 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `z`. Simplify using `only [hl, if_true, zpow_one]`. Expand and normalize the polynomial expressions, which then agree.

Use `(hmono 0 1 (by norm_num)).1 (hconst ((A : Matrix (Fin a) (Fin a) ℂ) i l * (B : Matrix (Fin a) (Fin a) ℂ) l j)).1 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `z`. Simplify using `[hl]`. Use `Submodule.sum_mem _ fun l _ => ?_` and prove the remaining obligations. Distinguish the cases in `hl : (l:ℕ) < k`.

Use `(hmono 0 1 (by norm_num)).2 (hmon ((A : Matrix (Fin a) (Fin a) ℂ) i l * (B : Matrix (Fin a) (Fin a) ℂ) l j) 1).2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `z`. Simplify using `only [hl, if_true, zpow_one]`. Expand and normalize the polynomial expressions, which then agree. Use `(hconst ((A : Matrix (Fin a) (Fin a) ℂ) i l * (B : Matrix (Fin a) (Fin a) ℂ) l j)).2 using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `z`. Simplify using `[hl]`.
-/
private theorem tor_entry_mem_expLe_one_expGe_zero (h : ExpBasic) (a k : ℕ) (A B : GL (Fin a) ℂ) (i j : Fin a) :
    (fun z : Circle => ((A * (tor a k z * B) : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j) ∈ ExpLe 1 ∧
    (fun z : Circle => ((A * (tor a k z * B) : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j) ∈ ExpGe 0 := by
  obtain ⟨_, _, hmono, hmon, hconst, _⟩ := h
  have heq : (fun z : Circle => ((A * (tor a k z * B) : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j) =
      ∑ l : Fin a, fun z : Circle => (A : Matrix (Fin a) (Fin a) ℂ) i l *
        ((if (l:ℕ) < k then (z:ℂ) else 1) * (B : Matrix (Fin a) (Fin a) ℂ) l j) := by
    funext z
    rw [Finset.sum_apply, Units.val_mul, Units.val_mul, Matrix.mul_apply]
    congr 1
    funext l
    simp only [tor, dg, Matrix.diagonal_mul]
    split_ifs
    · simp only [Circle.toUnits]
      first
        | rfl
        | simp [unitSphereToUnits_apply_coe]
    · simp
  rw [heq]
  constructor
  · refine Submodule.sum_mem _ fun l _ => ?_
    by_cases hl : (l:ℕ) < k
    · convert (hmon ((A : Matrix (Fin a) (Fin a) ℂ) i l * (B : Matrix (Fin a) (Fin a) ℂ) l j) 1).1 using 1
      funext z
      simp only [hl, if_true, zpow_one]
      ring
    · convert (hmono 0 1 (by norm_num)).1
        (hconst ((A : Matrix (Fin a) (Fin a) ℂ) i l * (B : Matrix (Fin a) (Fin a) ℂ) l j)).1 using 1
      funext z
      simp [hl]
  · refine Submodule.sum_mem _ fun l _ => ?_
    by_cases hl : (l:ℕ) < k
    · convert (hmono 0 1 (by norm_num)).2
        (hmon ((A : Matrix (Fin a) (Fin a) ℂ) i l * (B : Matrix (Fin a) (Fin a) ℂ) l j) 1).2 using 1
      funext z
      simp only [hl, if_true, zpow_one]
      ring
    · convert (hconst ((A : Matrix (Fin a) (Fin a) ℂ) i l * (B : Matrix (Fin a) (Fin a) ℂ) l j)).2 using 1
      funext z
      simp [hl]

/- English proof (translation)
Take `⟨hmulL, hmulG, _, _, hconst, _⟩` from `h`. Proceed by induction on `n with`. Consider the case `zero`. Simplify using `only [pow_zero, Nat.cast_zero]`. Conclude with `hconst 1`.

Consider the case `succ n ih`. Establish `e : (fun z => f z ^ (n + 1)) = fun z => (fun z => f z ^ n) z * f z`. Use function extensionality and compare the values at `z`. Conclude with `pow_succ _ _`. Rewrite using `[e]`.

Prove the components needed by the constructor for the conclusion. Use `hmulL _ _ _ _ ih.1 hf.1` as an intermediate fact. Use `push_cast`. Conclude with `this`. Use `hmulG _ _ _ _ ih.2 hf.2` as an intermediate fact.

Simplify using `using this`.
-/
private theorem pow_mem_expLe_expGe_of_mem (h : ExpBasic) (f : Circle → ℂ) (hf : f ∈ ExpLe 1 ∧ f ∈ ExpGe 0) (n : ℕ) :
    (fun z => f z ^ n) ∈ ExpLe (n : ℤ) ∧ (fun z => f z ^ n) ∈ ExpGe 0 := by
  obtain ⟨hmulL, hmulG, _, _, hconst, _⟩ := h
  induction n with
  | zero =>
    simp only [pow_zero, Nat.cast_zero]
    exact hconst 1
  | succ n ih =>
    have e : (fun z => f z ^ (n + 1)) = fun z => (fun z => f z ^ n) z * f z := by
      funext z
      exact pow_succ _ _
    rw [e]
    constructor
    · have := hmulL _ _ _ _ ih.1 hf.1
      push_cast
      exact this
    · have := hmulG _ _ _ _ ih.2 hf.2
      simpa using this

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty`. Simplify using `only [Finset.prod_empty, Finset.sum_empty, Nat.cast_zero]`. Conclude with `h.2.2.2.2.1 1`. Consider the case `insert x S hx ih`.

Establish `hp` using `pow_mem_expLe_expGe_of_mem h (e x) (he x) (d x)`. Establish `e1 : (fun z => ∏ i ∈ insert x S, e i z ^ d i) = fun z => (fun z => e x z ^ d x) z * (fun z => ∏ i ∈ S, e i z ^ d i) z`. Use function extensionality and compare the values at `z`. Conclude with `Finset.prod_insert hx`. Rewrite using `[e1]`.

Prove the components needed by the constructor for the conclusion. Use `h.1 _ _ _ _ hp.1 ih.1` as an intermediate fact. Rewrite using `[Finset.sum_insert hx, Nat.cast_add]`. Conclude with `this`. Use `h.2.1 _ _ _ _ hp.2 ih.2` as an intermediate fact.

Simplify using `using this`.
-/
private theorem prod_pow_mem_expLe_sum_expGe {ι : Type} [DecidableEq ι] (h : ExpBasic) (e : ι → Circle → ℂ)
    (he : ∀ i, e i ∈ ExpLe 1 ∧ e i ∈ ExpGe 0) (d : ι → ℕ) (S : Finset ι) :
    (fun z => ∏ i ∈ S, e i z ^ d i) ∈ ExpLe ((∑ i ∈ S, d i : ℕ) : ℤ) ∧
    (fun z => ∏ i ∈ S, e i z ^ d i) ∈ ExpGe 0 := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty, Nat.cast_zero]
    exact h.2.2.2.2.1 1
  | insert x S hx ih =>
    have hp := pow_mem_expLe_expGe_of_mem h (e x) (he x) (d x)
    have e1 : (fun z => ∏ i ∈ insert x S, e i z ^ d i) =
        fun z => (fun z => e x z ^ d x) z * (fun z => ∏ i ∈ S, e i z ^ d i) z := by
      funext z
      exact Finset.prod_insert hx
    rw [e1]
    constructor
    · have := h.1 _ _ _ _ hp.1 ih.1
      rw [Finset.sum_insert hx, Nat.cast_add]
      exact this
    · have := h.2.1 _ _ _ _ hp.2 ih.2
      simpa using this

/- English proof (translation)
Introduce `h a k P A B`. Set `e : Fin a × Fin a → Circle → ℂ` to `fun p z => ((A * (tor a k z * B) : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) p.1 p.2`. Establish `he : ∀ p, e p ∈ ExpLe 1 ∧ e p ∈ ExpGe 0` using `fun p => tor_entry_mem_expLe_one_expGe_zero h a k A B p.1 p.2`. Establish `hsum : (fun z => pev P (A * (tor a k z * B))) = ∑ d ∈ P.support, fun z => MvPolynomial.coeff d P * ∏ i ∈ d.support, e i z ^ d i`. Use function extensionality and compare the values at `z`.

Rewrite using `[Finset.sum_apply]`. Simplify using `only [pev]`. Rewrite using `[MvPolynomial.eval_eq]`. Rewrite using `[hsum]`. Prove the components needed by the constructor for the conclusion.

Use `Submodule.sum_mem _ fun d hd => ?_` and prove the remaining obligations. Establish `hp` using `(prod_pow_mem_expLe_sum_expGe h e he d d.support).1`. Establish `hle : ((∑ i ∈ d.support, d i : ℕ) : ℤ) ≤ (P.totalDegree : ℤ)`. Conclude with `MvPolynomial.le_totalDegree hd` after adjusting the coercions. Establish `hm` using `(h.2.2.1 _ _ hle).1 hp`.

Use `Submodule.smul_mem _ (MvPolynomial.coeff d P) hm using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `z`. Both sides reduce to the same expression. Use `Submodule.sum_mem _ fun d _ => ?_` and prove the remaining obligations. Establish `hp` using `(prod_pow_mem_expLe_sum_expGe h e he d d.support).2`.

Use `Submodule.smul_mem _ (MvPolynomial.coeff d P) hp using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `z`. Both sides reduce to the same expression.
-/
theorem UpperTheory.Gal.Wt.pevExp_of :
    UpperTheory.Gal.Wt.ExpBasic → UpperTheory.Gal.Wt.PevExp := by
  intro h a k P A B
  classical
  let e : Fin a × Fin a → Circle → ℂ := fun p z =>
    ((A * (tor a k z * B) : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) p.1 p.2
  have he : ∀ p, e p ∈ ExpLe 1 ∧ e p ∈ ExpGe 0 := fun p => tor_entry_mem_expLe_one_expGe_zero h a k A B p.1 p.2
  have hsum : (fun z => pev P (A * (tor a k z * B))) =
      ∑ d ∈ P.support, fun z => MvPolynomial.coeff d P * ∏ i ∈ d.support, e i z ^ d i := by
    funext z
    rw [Finset.sum_apply]
    simp only [pev]
    rw [MvPolynomial.eval_eq]
  rw [hsum]
  constructor
  · refine Submodule.sum_mem _ fun d hd => ?_
    have hp := (prod_pow_mem_expLe_sum_expGe h e he d d.support).1
    have hle : ((∑ i ∈ d.support, d i : ℕ) : ℤ) ≤ (P.totalDegree : ℤ) := by
      exact_mod_cast MvPolynomial.le_totalDegree hd
    have hm := (h.2.2.1 _ _ hle).1 hp
    convert Submodule.smul_mem _ (MvPolynomial.coeff d P) hm using 1
    funext z
    rfl
  · refine Submodule.sum_mem _ fun d _ => ?_
    have hp := (prod_pow_mem_expLe_sum_expGe h e he d d.support).2
    convert Submodule.smul_mem _ (MvPolynomial.coeff d P) hp using 1
    funext z
    rfl
