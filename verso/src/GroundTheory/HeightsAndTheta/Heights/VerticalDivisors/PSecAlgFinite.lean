import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsChowNorm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

namespace SecAlgFinite

variable {k E : Type} [Field k] [Field E] [Algebra k E] {n e : ℕ}

def lineSub (y : Par e n → E) (m : Fin n) (ij : Fin (e + 1) × Fin n) : Polynomial E :=
  Fin.cases (motive := fun _ => Polynomial E)
    (Polynomial.C (y (.inr ij.2)) * Polynomial.X - if ij.2 = m then 1 else 0)
    (fun i => Polynomial.C (y (.inl (i, ij.2)))) ij.1

def transVar (m : Fin n) (ij : Fin (e + 1) × Fin n) : MvPolynomial (Par e n) k :=
  Fin.cases (motive := fun _ => MvPolynomial (Par e n) k)
    (X (.inr ij.2) - if ij.2 = m then 1 else 0) (fun i => X (.inl (i, ij.2))) ij.1

def transVarInv (m : Fin n) : Par e n → MvPolynomial (Fin (e + 1) × Fin n) k
  | .inl ij => X (ij.1.succ, ij.2)
  | .inr j => X (0, j) + if j = m then 1 else 0

/- English proof (translation)
Establish `h : (aeval (R` using `k) (transVarInv (k := k) (e := e) m)).comp (aeval (R := k) (transVar m)) = AlgHom.id k _ := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `⟨i, j⟩`. Proceed by induction on `i using Fin.cases with`. Consider the case `zero => by_cases hj : j = m <;> simp [transVar, transVarInv, hj]`.

Consider the case `succ i => simp [transVar, transVarInv]`. Use `Function.LeftInverse.injective (g := aeval (R := k) (transVarInv m)) fun p => ?_` and prove the remaining obligations. Simplify using `using DFunLike.congr_fun h p`.
-/
theorem transVar_injective (m : Fin n) :
    Function.Injective (aeval (R := k) (transVar (k := k) (e := e) m)) := by
  have h : (aeval (R := k) (transVarInv (k := k) (e := e) m)).comp (aeval (R := k) (transVar m)) =
      AlgHom.id k _ := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    induction i using Fin.cases with
    | zero => by_cases hj : j = m <;> simp [transVar, transVarInv, hj]
    | succ i => simp [transVar, transVarInv]
  refine Function.LeftInverse.injective (g := aeval (R := k) (transVarInv m)) fun p => ?_
  simpa using DFunLike.congr_fun h p

/- English proof (translation)
Use `set Q' := Q.map (MvPolynomial.map (algebraMap k E))`. Use `set x := secCoord Q' y with hx`. Establish `hC : ∀ a : E, Ideal.Quotient.mk (secIdeal Q' y) (C a) = algebraMap E (SecAlg Q' y) a` using `fun a => rfl`. Establish `hmk : ∀ q : MvPolynomial (Fin n) k, aeval x q = Ideal.Quotient.mk (secIdeal Q' y) (MvPolynomial.map (algebraMap k E) q)`. Introduce `q`.

Proceed by induction on `q using MvPolynomial.induction_on with`. Consider the case `C a => rw [aeval_C, map_C, hC, ← IsScalarTower.algebraMap_apply]`. Consider the case `add p q hp hq => simp [hp, hq]`. Consider the case `mul_X p j hp => rw [map_mul, map_mul, map_mul, hp, aeval_X, map_X]`. Both sides reduce to the same expression.

Establish `hQ : ∀ q ∈ Q, aeval x q = 0` using `fun q hq => by`. Rewrite using `[hmk, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hq))`. Establish `ht : ∑ j, algebraMap E (SecAlg Q' y) (y (.inr j)) * x j = 1`. Establish `h : chartForm y - 1 ∈ secIdeal Q' y` using `Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)`.

Rewrite `h` using `[← Ideal.Quotient.eq]`. Simplify `h` using `[chartForm, linForm, map_sum, hC, hx, secCoord]`. Establish `hl : ∀ i, ∑ j, algebraMap E (SecAlg Q' y) (y (.inl (i, j))) * x j = 0` using `fun i => by`. Establish `h : secForm y i ∈ secIdeal Q' y` using `Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))`. Rewrite `h` using `[← Ideal.Quotient.eq_zero_iff_mem]`.

Simplify `h` using `[secForm, linForm, map_sum, hC, hx, secCoord]`. Use `set φ : MvPolynomial (Fin n ⊕ (Fin (e + 1) × Fin n)) k →ₐ[k] SecAlg Q' y := aeval (Sum.elim x fun ij => Polynomial.aeval (x m) (lineSub y m ij)) with hφ`. Establish `hker : ∀ p ∈ incIdeal Q (e + 1), φ p = 0`. Introduce `p hp`. It suffices to establish `incIdeal Q (e + 1) ≤ RingHom.ker φ.toRingHom from this hp`.

Use `sup_le ?_ ?_` and prove the remaining obligations. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `q hq`. Simplify using `only [Ideal.mem_comap, RingHom.mem_ker]`. Simplify using `[hφ, aeval_rename, hQ q hq]`.

Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Simplify using `only [SetLike.mem_coe, RingHom.mem_ker]`. Proceed by induction on `i using Fin.cases with`. Consider the case `zero`.

Establish `h0 : ∀ j, Polynomial.aeval (x m) (lineSub y m (0, j)) = algebraMap E (SecAlg Q' y) (y (.inr j)) * x m - if j = m then 1 else 0`. Introduce `j`. Apply the tactic sequence `split_ifs with hj <;> simp [lineSub, hj]`. Simplify using `only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum, map_mul, hφ, aeval_X, Sum.elim_inr, Sum.elim_inl, h0, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Rewrite using `[sub_eq_zero]`.

Use `conv_rhs => rw [← mul_one (x m), ← ht, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`. Consider the case `succ i`. Simplify `hl i` using `[hφ, lineSub]`. Take `⟨M, hM⟩` from `h1 k n (e + 1) Q g hg`.

Use `set P : Polynomial E := aeval (lineSub y m) g with hP`. Establish `hG : φ (rename Sum.inr g) = Polynomial.aeval (x m) P`. Rewrite using `[hφ, aeval_rename, Sum.elim_comp_inr, hP]`. Use `DFunLike.congr_fun (MvPolynomial.comp_aeval (R := k) (lineSub y m) ((Polynomial.aeval (x m)).restrictScalars k)) g` as an intermediate fact. Simplify using `using this.symm`.

Establish `hnil : IsNilpotent (Polynomial.aeval (x m) P)`. Rewrite using `[← hG, ← mul_one (φ _), ← ht, Finset.mul_sum]`. Use `isNilpotent_sum fun j _ => ?_` and prove the remaining obligations. Establish `hj : IsNilpotent (φ (rename Sum.inr g) * x j)`. Use `⟨M, ?_⟩` and prove the remaining obligations.

Establish `h0` using `hker _ (hM j)`. Rewrite `h0` using `[map_pow, map_mul, show φ (X (Sum.inl j)) = x j by simp [hφ]]`. Then use the resulting hypothesis. Rewrite using `[mul_left_comm]`. Conclude with `(Commute.all _ _).isNilpotent_mul_left hj`. Establish `hP0 : P ≠ 0`.

Introduce `h0`. Establish `h1' : Polynomial.aeval (1 : E) P = aeval y (aeval (transVar (k` using `k) m) g) := by`. Establish `ha` using `DFunLike.congr_fun (MvPolynomial.comp_aeval (R := k) (lineSub y m) ((Polynomial.aeval (1 : E)).restrictScalars k)) g`. Establish `hb` using `DFunLike.congr_fun (MvPolynomial.comp_aeval (R := k) (transVar (k := k) m) (aeval y)) g`. Simplify using `only [AlgHom.comp_apply, AlgHom.restrictScalars_apply] at ha hb`.

Establish `hfun : (fun ij => Polynomial.aeval (1 : E) (lineSub y m ij)) = fun ij => aeval y (transVar (k` using `k) m ij) := by`. Use function extensionality and compare the values at `⟨i, j⟩`. Proceed by induction on `i using Fin.cases with`. Consider the case `zero => by_cases hj : j = m <;> simp [lineSub, transVar, hj]`. Consider the case `succ i => simp [lineSub, transVar]`.

Rewrite using `[hP, ha, hb, hfun]`. Rewrite `h1'` using `[h0, map_zero]`. Conclude with `hg.1 (transVar_injective m ((hy.eq_zero_of_aeval_eq_zero _ h1'.symm).trans (map_zero (aeval (R := k) (transVar (k := k) (e := e) m))).symm))`. Take `⟨N, hN⟩` from `hnil`. Conclude with `isAlgebraic_iff_isIntegral.1 ⟨P ^ N, pow_ne_zero _ hP0, by rw [map_pow, hN]⟩`.
-/
theorem coord_integral (h1 : IncidenceNull.Statement) (Q : Ideal (MvPolynomial (Fin n) k))
    (g : MvPolynomial (Fin (e + 1) × Fin n) k) (y : Par e n → E) (hy : AlgebraicIndependent k y)
    (hg : IsChowForm Q (e + 1) g) (m : Fin n) :
    IsIntegral E (secCoord (Q.map (MvPolynomial.map (algebraMap k E))) y m) := by
  set Q' := Q.map (MvPolynomial.map (algebraMap k E))
  set x := secCoord Q' y with hx
  have hC : ∀ a : E, Ideal.Quotient.mk (secIdeal Q' y) (C a) = algebraMap E (SecAlg Q' y) a :=
    fun a => rfl

  have hmk : ∀ q : MvPolynomial (Fin n) k,
      aeval x q = Ideal.Quotient.mk (secIdeal Q' y) (MvPolynomial.map (algebraMap k E) q) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a => rw [aeval_C, map_C, hC, ← IsScalarTower.algebraMap_apply]
    | add p q hp hq => simp [hp, hq]
    | mul_X p j hp => rw [map_mul, map_mul, map_mul, hp, aeval_X, map_X]; rfl
  have hQ : ∀ q ∈ Q, aeval x q = 0 := fun q hq => by
    rw [hmk, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hq))
  have ht : ∑ j, algebraMap E (SecAlg Q' y) (y (.inr j)) * x j = 1 := by
    have h : chartForm y - 1 ∈ secIdeal Q' y :=
      Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    rw [← Ideal.Quotient.eq] at h
    simpa [chartForm, linForm, map_sum, hC, hx, secCoord] using h
  have hl : ∀ i, ∑ j, algebraMap E (SecAlg Q' y) (y (.inl (i, j))) * x j = 0 := fun i => by
    have h : secForm y i ∈ secIdeal Q' y :=
      Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
    rw [← Ideal.Quotient.eq_zero_iff_mem] at h
    simpa [secForm, linForm, map_sum, hC, hx, secCoord] using h

  set φ : MvPolynomial (Fin n ⊕ (Fin (e + 1) × Fin n)) k →ₐ[k] SecAlg Q' y :=
    aeval (Sum.elim x fun ij => Polynomial.aeval (x m) (lineSub y m ij)) with hφ
  have hker : ∀ p ∈ incIdeal Q (e + 1), φ p = 0 := by
    intro p hp
    suffices incIdeal Q (e + 1) ≤ RingHom.ker φ.toRingHom from this hp
    refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro q hq
      simp only [Ideal.mem_comap, RingHom.mem_ker]
      simp [hφ, aeval_rename, hQ q hq]
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp only [SetLike.mem_coe, RingHom.mem_ker]
      induction i using Fin.cases with
      | zero =>
        have h0 : ∀ j, Polynomial.aeval (x m) (lineSub y m (0, j)) =
            algebraMap E (SecAlg Q' y) (y (.inr j)) * x m - if j = m then 1 else 0 := by
          intro j
          split_ifs with hj <;> simp [lineSub, hj]
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum, map_mul, hφ, aeval_X,
          Sum.elim_inr, Sum.elim_inl, h0, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul,
          zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rw [sub_eq_zero]
        conv_rhs => rw [← mul_one (x m), ← ht, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      | succ i =>
        simpa [hφ, lineSub] using hl i
  obtain ⟨M, hM⟩ := h1 k n (e + 1) Q g hg
  set P : Polynomial E := aeval (lineSub y m) g with hP
  have hG : φ (rename Sum.inr g) = Polynomial.aeval (x m) P := by
    rw [hφ, aeval_rename, Sum.elim_comp_inr, hP]
    have := DFunLike.congr_fun
      (MvPolynomial.comp_aeval (R := k) (lineSub y m) ((Polynomial.aeval (x m)).restrictScalars k)) g
    simpa using this.symm
  have hnil : IsNilpotent (Polynomial.aeval (x m) P) := by
    rw [← hG, ← mul_one (φ _), ← ht, Finset.mul_sum]
    refine isNilpotent_sum fun j _ => ?_
    have hj : IsNilpotent (φ (rename Sum.inr g) * x j) := by
      refine ⟨M, ?_⟩
      have h0 := hker _ (hM j)
      rwa [map_pow, map_mul, show φ (X (Sum.inl j)) = x j by simp [hφ]] at h0
    rw [mul_left_comm]
    exact (Commute.all _ _).isNilpotent_mul_left hj
  have hP0 : P ≠ 0 := by
    intro h0
    have h1' : Polynomial.aeval (1 : E) P = aeval y (aeval (transVar (k := k) m) g) := by
      have ha := DFunLike.congr_fun
        (MvPolynomial.comp_aeval (R := k) (lineSub y m) ((Polynomial.aeval (1 : E)).restrictScalars k)) g
      have hb := DFunLike.congr_fun
        (MvPolynomial.comp_aeval (R := k) (transVar (k := k) m) (aeval y)) g
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply] at ha hb
      have hfun : (fun ij => Polynomial.aeval (1 : E) (lineSub y m ij)) =
          fun ij => aeval y (transVar (k := k) m ij) := by
        funext ⟨i, j⟩
        induction i using Fin.cases with
        | zero => by_cases hj : j = m <;> simp [lineSub, transVar, hj]
        | succ i => simp [lineSub, transVar]
      rw [hP, ha, hb, hfun]
    rw [h0, map_zero] at h1'
    exact hg.1 (transVar_injective m ((hy.eq_zero_of_aeval_eq_zero _ h1'.symm).trans
      (map_zero (aeval (R := k) (transVar (k := k) (e := e) m))).symm))
  obtain ⟨N, hN⟩ := hnil
  exact isAlgebraic_iff_isIntegral.1 ⟨P ^ N, pow_ne_zero _ hP0, by rw [map_pow, hN]⟩

end SecAlgFinite

/- English proof (translation)
Introduce `k E _ _ _ n e Q g y hy _ hg`. Use `set Q' := Q.map (MvPolynomial.map (algebraMap k E))`. Establish `htop : Algebra.adjoin E (Set.range (secCoord Q' y)) = ⊤`. Establish `h : Set.range (secCoord Q' y) = Ideal.Quotient.mkₐ E (secIdeal Q' y) '' Set.range X`. Rewrite using `[← Set.range_comp]`.

Both sides reduce to the same expression. Rewrite using `[h, ← AlgHom.map_adjoin, MvPolynomial.adjoin_range_X, Algebra.map_top]`. Conclude with `(AlgHom.range_eq_top _).2 (Ideal.Quotient.mkₐ_surjective E _)`. Establish `hfg` using `fg_adjoin_of_finite (Set.finite_range (secCoord Q' y)) (by rintro _ ⟨m, rfl⟩; exact SecAlgFinite.coord_integral h1 Q g y hy hg m)`. Rewrite `hfg` using `[htop, Algebra.top_toSubmodule]`.

Conclude with `⟨hfg⟩`.
-/
theorem SecAlgFinite.proof (h1 : IncidenceNull.Statement) : SecAlgFinite.Statement := by
  intro k E _ _ _ n e Q g y hy _ hg
  set Q' := Q.map (MvPolynomial.map (algebraMap k E))
  have htop : Algebra.adjoin E (Set.range (secCoord Q' y)) = ⊤ := by
    have h : Set.range (secCoord Q' y) = Ideal.Quotient.mkₐ E (secIdeal Q' y) '' Set.range X := by
      rw [← Set.range_comp]; rfl
    rw [h, ← AlgHom.map_adjoin, MvPolynomial.adjoin_range_X, Algebra.map_top]
    exact (AlgHom.range_eq_top _).2 (Ideal.Quotient.mkₐ_surjective E _)
  have hfg := fg_adjoin_of_finite (Set.finite_range (secCoord Q' y))
    (by rintro _ ⟨m, rfl⟩; exact SecAlgFinite.coord_integral h1 Q g y hy hg m)
  rw [htop, Algebra.top_toSubmodule] at hfg
  exact ⟨hfg⟩

end

end GroundTheory.Heights₂.Heights.Vertical
