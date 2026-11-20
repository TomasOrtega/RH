import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IsSplitFrame
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxAJacE

noncomputable section

open scoped TensorProduct
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting

namespace PI.UnitaryDimensionFormula

def FrGram : Prop := ∀ (D : D7) (X : HidaSetting D) (e : Af X.B.I.F), EgProp X.B.I.F X.B.g e →
  ∀ G : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F), (∀ l j, G l j ∈ IntAf X.B.I.F X.B.I.E) →
  (∀ l j, ZMod' X.B.I X.B.g (G l j - if l = j then epsX X e else 0)) →
  ∃ y ∈ IntAf X.B.I.F X.B.I.E, epsX X e * G.det * y = epsX X e

/- English proof (translation)
Set `G' : Matrix (Fin k) (Fin k) S` to `fun l j => ⟨G l j, hG l j⟩`. Set `ε' : S` to `⟨ε, hε⟩`. Set `g' : S` to `⟨gg, hg⟩`. Set `I : Ideal S` to `Ideal.span {g'}`. Establish `hmap : (Ideal.Quotient.mk I).mapMatrix G' = Matrix.scalar (Fin k) (Ideal.Quotient.mk I ε')`.

Use extensionality with `l j`. Take `⟨t, ht, he⟩` from `hc l j`. Establish `hsub : G' l j - (if l = j then ε' else 0) ∈ I`. Rewrite using `[Ideal.mem_span_singleton']`. Use `⟨⟨t, ht⟩, ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Apply the tactic sequence `split_ifs at he ⊢ <;> simp [G', ε', g'] <;> first | linear_combination he | linear_combination -he`. Use `Ideal.Quotient.eq.mpr hsub` as an intermediate fact. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply]`. Rewrite using `[this]`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `hdet : Ideal.Quotient.mk I G'.det = Ideal.Quotient.mk I (ε' ^ k)`. Rewrite using `[RingHom.map_det, hmap, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, map_pow]`. Take `⟨m, hm⟩` from `Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp hdet)`. Use `⟨m, m.2, ?_⟩` and prove the remaining obligations.

Establish `hG' : S.subtype.mapMatrix G' = G`. Use extensionality with `l j`. Both sides reduce to the same expression. Establish `h1 : G.det = S.subtype G'.det`. Rewrite using `[RingHom.map_det, hG']`.

Establish `h2 : G'.det = ε' ^ k + m * g'`. Rewrite using `[hm]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1, h2]`. Simplify using `[ε', g', mul_comm]`.
-/
theorem fg_det {B : Type} [CommRing B] (S : Subring B) {k : ℕ} (G : Matrix (Fin k) (Fin k) B) (ε gg : B)
    (hε : ε ∈ S) (hg : gg ∈ S) (hG : ∀ l j, G l j ∈ S)
    (hc : ∀ l j, ∃ t ∈ S, G l j - (if l = j then ε else 0) = gg * t) :
    ∃ m ∈ S, G.det = ε ^ k + gg * m := by
  classical

  let G' : Matrix (Fin k) (Fin k) S := fun l j => ⟨G l j, hG l j⟩
  let ε' : S := ⟨ε, hε⟩
  let g' : S := ⟨gg, hg⟩
  let I : Ideal S := Ideal.span {g'}
  have hmap : (Ideal.Quotient.mk I).mapMatrix G' =
      Matrix.scalar (Fin k) (Ideal.Quotient.mk I ε') := by
    ext l j
    obtain ⟨t, ht, he⟩ := hc l j
    have hsub : G' l j - (if l = j then ε' else 0) ∈ I := by
      rw [Ideal.mem_span_singleton']
      refine ⟨⟨t, ht⟩, ?_⟩
      apply Subtype.ext
      split_ifs at he ⊢ <;> simp [G', ε', g'] <;> first | linear_combination he | linear_combination -he
    have := Ideal.Quotient.eq.mpr hsub
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.scalar_apply,
      Matrix.diagonal_apply]
    rw [this]
    split_ifs <;> simp
  have hdet : Ideal.Quotient.mk I G'.det = Ideal.Quotient.mk I (ε' ^ k) := by
    rw [RingHom.map_det, hmap, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, map_pow]
  obtain ⟨m, hm⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp hdet)
  refine ⟨m, m.2, ?_⟩
  have hG' : S.subtype.mapMatrix G' = G := by
    ext l j
    rfl
  have h1 : G.det = S.subtype G'.det := by
    rw [RingHom.map_det, hG']
  have h2 : G'.det = ε' ^ k + m * g' := by
    rw [hm]; ring
  rw [h1, h2]
  simp [ε', g', mul_comm]

/- English proof (translation)
Introduce `D X e hE G hGi hGc`. Establish `h1 : X.ew * X.ew = X.ew` using `X.ew_idem`. Establish `h2 : X.ew ∈ IntAf X.B.I.F X.B.I.E` using `X.ew_int`. Establish `h3 : (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e ∈ IntAf X.B.I.F X.B.I.E`. Unfold `IntAf Formalism.UG.tensInt`.

Conclude with `Subring.subset_closure (Or.inr ⟨⟨e, hE.1⟩, rfl⟩)`. Establish `hε : epsX X e ∈ IntAf X.B.I.F X.B.I.E` using `(IntAf X.B.I.F X.B.I.E).mul_mem h3 h2`. Establish `hg : ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ∈ IntAf X.B.I.F X.B.I.E` using `natCast_mem (IntAf X.B.I.F X.B.I.E) _`. Take `⟨m, hm, hdet⟩` from `fg_det (IntAf X.B.I.F X.B.I.E) G (epsX X e) ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) hε hg hGi (fun l j => hGc l j)`. Establish `hidem : epsX X e * epsX X e = epsX X e`.

Unfold `epsX`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul, hE.2.1, h1]`. Establish `hpow : ∀ n : ℕ, epsX X e * epsX X e ^ n = epsX X e`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [pow_succ, ← mul_assoc, ih, hidem]`. Take `⟨y, hy, hyeq⟩` from `idxDJacE X.B.I.F X.B.I.E X.B.g e hE m hm`. Use `⟨y, hy, ?_⟩` and prove the remaining obligations.

Rewrite using `[hdet, mul_add, hpow]`. Establish `hfac : epsX X e + epsX X e * (((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * m) = X.ew * ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e * (1 + ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * m))`. Unfold `epsX`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hfac, mul_assoc, hyeq]`.

Unfold `epsX`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem frGram : FrGram := by
  intro D X e hE G hGi hGc
  have h1 : X.ew * X.ew = X.ew := X.ew_idem
  have h2 : X.ew ∈ IntAf X.B.I.F X.B.I.E := X.ew_int
  have h3 : (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e ∈ IntAf X.B.I.F X.B.I.E := by
    unfold IntAf Formalism.UG.tensInt
    exact Subring.subset_closure (Or.inr ⟨⟨e, hE.1⟩, rfl⟩)
  have hε : epsX X e ∈ IntAf X.B.I.F X.B.I.E := (IntAf X.B.I.F X.B.I.E).mul_mem h3 h2
  have hg : ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ∈ IntAf X.B.I.F X.B.I.E :=
    natCast_mem (IntAf X.B.I.F X.B.I.E) _
  obtain ⟨m, hm, hdet⟩ := fg_det (IntAf X.B.I.F X.B.I.E) G (epsX X e)
    ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) hε hg hGi (fun l j => hGc l j)

  have hidem : epsX X e * epsX X e = epsX X e := by
    unfold epsX
    calc (1 ⊗ₜ[X.B.I.F] e * X.ew) * (1 ⊗ₜ[X.B.I.F] e * X.ew)
        = ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e * (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) * (X.ew * X.ew) := by ring
      _ = (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e * X.ew := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hE.2.1, h1]
  have hpow : ∀ n : ℕ, epsX X e * epsX X e ^ n = epsX X e := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ← mul_assoc, ih, hidem]
  obtain ⟨y, hy, hyeq⟩ := idxDJacE X.B.I.F X.B.I.E X.B.g e hE m hm
  refine ⟨y, hy, ?_⟩
  rw [hdet, mul_add, hpow]
  have hfac : epsX X e + epsX X e * (((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * m) =
      X.ew * ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e *
        (1 + ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * m)) := by
    unfold epsX
    ring
  rw [hfac, mul_assoc, hyeq]
  unfold epsX
  ring

end PI.UnitaryDimensionFormula
