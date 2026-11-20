import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.AssemblyAlt
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.InvariantPolynomialEqAevalPairings

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.FFTSteps

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a => simp [sub]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p v hp`. Simplify using `only [map_mul, sub, aeval_X, eval_X]`.

Use `congr 1`. Apply the tactic sequence `rcases v with x | y <;> simp [map_sum]`.
-/
theorem stable_eval_sub {ι A B : Type} [Fintype ι] (g h : Matrix ι ι ℂ) (z : (ι × A) ⊕ (ι × B) → ℂ) (p : PV ι A B) :
    eval z (sub g h p) = eval (Sum.elim (fun x : ι × A => ∑ j, g x.1 j * z (Sum.inl (j, x.2)))
      (fun y : ι × B => ∑ j, h y.1 j * z (Sum.inr (j, y.2)))) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [sub]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, sub, aeval_X, eval_X]
    congr 1
    rcases v with x | y <;> simp [map_sum]

/- English proof (translation)
Introduce `ι A B _ _ _ _ hA hB p hp`. Use `set n := Fintype.card ι`. Set `eι : ι ≃ Fin n` to `Fintype.equivFin ι`. Set `eA : A ↪ Fin n` to `(Fintype.equivFin A).toEmbedding.trans (Fin.castLEEmb hA)`. Set `eB : B ↪ Fin n` to `(Fintype.equivFin B).toEmbedding.trans (Fin.castLEEmb hB)`.

Set `f : (ι × A) ⊕ (ι × B) → Unit × Bool × Fin n × Fin n` to `Sum.elim (fun x => ((), true, eι x.1, eA x.2)) (fun y => ((), false, eι y.1, eB y.2))`. Use `set q : MvPolynomial (Unit × Bool × Fin n × Fin n) ℂ := rename f p with hq`. Establish `hinv : ∀ u : Unit → Matrix (Fin n) (Fin n) ℂ, (∀ t, u t ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∀ z : Unit × Bool × Fin n × Fin n → ℂ, eval (fun v => ∑ l, (if v.2.1 then u v.1 v.2.2.1 l else (starRingEnd ℂ) (u v.1 v.2.2.1 l)) * z (v.1, v.2.1, l, v.2.2.2)) q = eval z q`. Introduce `u hu z`. Set `u' : Matrix ι ι ℂ` to `(u ()).submatrix eι eι`.

Establish `hu' : u' ∈ Matrix.unitaryGroup ι ℂ`. Rewrite using `[Matrix.mem_unitaryGroup_iff]`. Establish `h1` using `Matrix.mem_unitaryGroup_iff.1 (hu ())`. Simplify using `only [u', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix]`. Rewrite using `[Matrix.submatrix_mul_equiv, ← Matrix.star_eq_conjTranspose, h1, Matrix.submatrix_one_equiv]`.

Rewrite using `[hq, eval_rename, eval_rename]`. Use `congrArg (eval (z ∘ f)) (hp u' hu')` as an intermediate fact. Rewrite `this` using `[stable_eval_sub]`. Rewrite using `[← this]`. Use `congrArg (fun w => eval w p) ?_` and prove the remaining obligations.

Use function extensionality and compare the values at `v`. Break down `v with ⟨i, a⟩ | ⟨i, b⟩` into its components or cases. Simplify using `only [Function.comp, f, Sum.elim_inl, if_true, u', Matrix.submatrix_apply]`. Conclude with `(Equiv.sum_comp eι (fun l => u () (eι i) l * z ((), true, l, eA a))).symm`. Simplify using `only [Function.comp, f, Sum.elim_inr, Bool.false_eq_true, if_false, u', Matrix.submatrix_apply, Matrix.map_apply]`.

Conclude with `(Equiv.sum_comp eι (fun l => (starRingEnd ℂ) (u () (eι i) l) * z ((), false, l, eB b))).symm`. Take `⟨s, hs⟩` from `GlobalTheory.invariant_polynomial_eq_aeval_pairings Unit n n le_rfl q hinv`. Set `ψF : Unit × Bool × Fin n × Fin n → PV ι A B` to `fun v => if v.2.1 then (if h : ∃ a, eA a = v.2.2.2 then X (Sum.inl (eι.symm v.2.2.1, h.choose)) else 0) else (if h : ∃ b, eB b = v.2.2.2 then X (Sum.inr (eι.symm v.2.2.1, h.choose)) else 0)`. Establish `hψf : ∀ w, ψF (f w) = X w`. Introduce and unpack `(⟨i, a⟩ | ⟨i, b⟩)`.

Establish `h : ∃ a', eA a' = eA a` using `⟨a, rfl⟩`. Simplify using `only [f, Sum.elim_inl, ψF, if_true, dif_pos h, Equiv.symm_apply_apply]`. Rewrite using `[eA.injective h.choose_spec]`. Establish `h : ∃ b', eB b' = eB b` using `⟨b, rfl⟩`. Simplify using `only [f, Sum.elim_inr, ψF, Bool.false_eq_true, if_false, dif_pos h, Equiv.symm_apply_apply]`.

Rewrite using `[eB.injective h.choose_spec]`. Establish `hp' : p = aeval ψF q`. Rewrite using `[hq, aeval_rename]`. Establish `: (ψF ∘ f) = X` using `funext hψf`. Rewrite using `[this, aeval_X_left_apply]`.

Establish `hgen : ∀ v : Unit × Fin n × Fin n, aeval ψF (∑ k, (X (v.1, false, k, v.2.1) * X (v.1, true, k, v.2.2) : MvPolynomial (Unit × Bool × Fin n × Fin n) ℂ)) ∈ pairAlg ι A B`. Introduce and unpack `⟨t, a', b'⟩`. Simplify using `only [map_sum, map_mul, aeval_X, ψF, Bool.false_eq_true, if_false, if_true]`. Distinguish the cases in `hb : ∃ b, eB b = a'`. Distinguish the cases in `ha : ∃ a, eA a = b'`.

Simplify using `only [dif_pos hb, dif_pos ha]`. Establish `: (∑ k : Fin n, (X (Sum.inr (eι.symm k, hb.choose)) : PV ι A B) * X (Sum.inl (eι.symm k, ha.choose))) = ∑ i, (X (Sum.inl (i, ha.choose)) : PV ι A B) * X (Sum.inr (i, hb.choose))`. Rewrite using `[← Equiv.sum_comp eι]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Equiv.symm_apply_apply, mul_comm]`.

Rewrite using `[this]`. Conclude with `Algebra.subset_adjoin ⟨(ha.choose, hb.choose), rfl⟩`. Simplify using `only [dif_neg ha, mul_zero, Finset.sum_const_zero]`. Conclude with `Subalgebra.zero_mem _`. Simplify using `only [dif_neg hb, zero_mul, Finset.sum_const_zero]`.

Conclude with `Subalgebra.zero_mem _`. Rewrite using `[hp', hs, ← AlgHom.comp_apply, comp_aeval]`. Use `clear hs hp'`. Proceed by induction on `s using MvPolynomial.induction_on with`. Consider the case `C a => simp only [aeval_C]`.

Conclude with `Subalgebra.algebraMap_mem _ a`. Consider the case `add x y hx hy => rw [map_add]`. Conclude with `Subalgebra.add_mem _ hx hy`. Consider the case `mul_X x v hx => rw [map_mul, aeval_X]`. Conclude with `Subalgebra.mul_mem _ hx (hgen v)`.
-/
theorem stable : Stable := by
  intro ι A B _ _ _ _ hA hB p hp
  classical
  set n := Fintype.card ι
  let eι : ι ≃ Fin n := Fintype.equivFin ι
  let eA : A ↪ Fin n := (Fintype.equivFin A).toEmbedding.trans (Fin.castLEEmb hA)
  let eB : B ↪ Fin n := (Fintype.equivFin B).toEmbedding.trans (Fin.castLEEmb hB)
  let f : (ι × A) ⊕ (ι × B) → Unit × Bool × Fin n × Fin n :=
    Sum.elim (fun x => ((), true, eι x.1, eA x.2)) (fun y => ((), false, eι y.1, eB y.2))
  set q : MvPolynomial (Unit × Bool × Fin n × Fin n) ℂ := rename f p with hq
  have hinv : ∀ u : Unit → Matrix (Fin n) (Fin n) ℂ, (∀ t, u t ∈ Matrix.unitaryGroup (Fin n) ℂ) →
      ∀ z : Unit × Bool × Fin n × Fin n → ℂ, eval (fun v => ∑ l, (if v.2.1 then u v.1 v.2.2.1 l
        else (starRingEnd ℂ) (u v.1 v.2.2.1 l)) * z (v.1, v.2.1, l, v.2.2.2)) q = eval z q := by
    intro u hu z
    let u' : Matrix ι ι ℂ := (u ()).submatrix eι eι
    have hu' : u' ∈ Matrix.unitaryGroup ι ℂ := by
      rw [Matrix.mem_unitaryGroup_iff]
      have h1 := Matrix.mem_unitaryGroup_iff.1 (hu ())
      simp only [u', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix]
      rw [Matrix.submatrix_mul_equiv, ← Matrix.star_eq_conjTranspose, h1, Matrix.submatrix_one_equiv]
    rw [hq, eval_rename, eval_rename]
    have := congrArg (eval (z ∘ f)) (hp u' hu')
    rw [stable_eval_sub] at this
    rw [← this]
    refine congrArg (fun w => eval w p) ?_
    funext v
    rcases v with ⟨i, a⟩ | ⟨i, b⟩
    · simp only [Function.comp, f, Sum.elim_inl, if_true, u', Matrix.submatrix_apply]
      exact (Equiv.sum_comp eι (fun l => u () (eι i) l * z ((), true, l, eA a))).symm
    · simp only [Function.comp, f, Sum.elim_inr, Bool.false_eq_true, if_false, u', Matrix.submatrix_apply,
        Matrix.map_apply]
      exact (Equiv.sum_comp eι (fun l => (starRingEnd ℂ) (u () (eι i) l) * z ((), false, l, eB b))).symm
  obtain ⟨s, hs⟩ := GlobalTheory.invariant_polynomial_eq_aeval_pairings Unit n n le_rfl q hinv
  let ψF : Unit × Bool × Fin n × Fin n → PV ι A B := fun v =>
    if v.2.1 then (if h : ∃ a, eA a = v.2.2.2 then X (Sum.inl (eι.symm v.2.2.1, h.choose)) else 0)
    else (if h : ∃ b, eB b = v.2.2.2 then X (Sum.inr (eι.symm v.2.2.1, h.choose)) else 0)
  have hψf : ∀ w, ψF (f w) = X w := by
    rintro (⟨i, a⟩ | ⟨i, b⟩)
    · have h : ∃ a', eA a' = eA a := ⟨a, rfl⟩
      simp only [f, Sum.elim_inl, ψF, if_true, dif_pos h, Equiv.symm_apply_apply]
      rw [eA.injective h.choose_spec]
    · have h : ∃ b', eB b' = eB b := ⟨b, rfl⟩
      simp only [f, Sum.elim_inr, ψF, Bool.false_eq_true, if_false, dif_pos h, Equiv.symm_apply_apply]
      rw [eB.injective h.choose_spec]
  have hp' : p = aeval ψF q := by
    rw [hq, aeval_rename]
    have : (ψF ∘ f) = X := funext hψf
    rw [this, aeval_X_left_apply]
  have hgen : ∀ v : Unit × Fin n × Fin n, aeval ψF (∑ k, (X (v.1, false, k, v.2.1) * X (v.1, true, k, v.2.2) :
      MvPolynomial (Unit × Bool × Fin n × Fin n) ℂ)) ∈ pairAlg ι A B := by
    rintro ⟨t, a', b'⟩
    simp only [map_sum, map_mul, aeval_X, ψF, Bool.false_eq_true, if_false, if_true]
    by_cases hb : ∃ b, eB b = a'
    · by_cases ha : ∃ a, eA a = b'
      · simp only [dif_pos hb, dif_pos ha]
        have : (∑ k : Fin n, (X (Sum.inr (eι.symm k, hb.choose)) : PV ι A B) * X (Sum.inl (eι.symm k, ha.choose))) =
            ∑ i, (X (Sum.inl (i, ha.choose)) : PV ι A B) * X (Sum.inr (i, hb.choose)) := by
          rw [← Equiv.sum_comp eι]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Equiv.symm_apply_apply, mul_comm]
        rw [this]
        exact Algebra.subset_adjoin ⟨(ha.choose, hb.choose), rfl⟩
      · simp only [dif_neg ha, mul_zero, Finset.sum_const_zero]
        exact Subalgebra.zero_mem _
    · simp only [dif_neg hb, zero_mul, Finset.sum_const_zero]
      exact Subalgebra.zero_mem _
  rw [hp', hs, ← AlgHom.comp_apply, comp_aeval]
  clear hs hp'
  induction s using MvPolynomial.induction_on with
  | C a => simp only [aeval_C]; exact Subalgebra.algebraMap_mem _ a
  | add x y hx hy => rw [map_add]; exact Subalgebra.add_mem _ hx hy
  | mul_X x v hx => rw [map_mul, aeval_X]; exact Subalgebra.mul_mem _ hx (hgen v)

end PositivityTheory.Rg.Sw.FFTSteps
