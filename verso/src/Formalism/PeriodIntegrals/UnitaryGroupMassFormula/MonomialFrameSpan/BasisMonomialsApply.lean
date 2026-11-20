import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.NablaSpanC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.DetSubmatrixFun

noncomputable section

open scoped BigOperators
open Classical

namespace GenFrameSpan

open CutKW MvPolynomial

section Span

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N0 N1 l : ℕ} [Fact l.Prime]

def atMon (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (μ : XZ Lt N0 N1 →₀ ℕ) :
    MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l] :=
  monomial (Finsupp.sumFinsuppEquivProdFinsupp μ).1
    (((Finsupp.sumFinsuppEquivProdFinsupp μ).2.prod fun _ n => (n.factorial : ℂ_[l])) *
      MvPowerSeries.coeff (Finsupp.sumFinsuppEquivProdFinsupp μ).2 Th)

def Lj (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) :
    MvPolynomial (XZ Lt N0 N1) ℤ →ₗ[ℤ] MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l] :=
  (basisMonomials (XZ Lt N0 N1) ℤ).constr ℤ (atMon Th)

def Sj (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) :
    MvPolynomial (Lt × Fin N0 × Fin N1) ℤ →ₗ[ℤ] ℂ_[l] :=
  (basisMonomials (Lt × Fin N0 × Fin N1) ℤ).constr ℤ fun β =>
    (β.prod fun _ n => (n.factorial : ℂ_[l])) * MvPowerSeries.coeff β Th

/- English proof (translation)
Simplify using `[coe_basisMonomials]`.
-/
theorem basisMonomials_apply' {σ : Type} (μ : σ →₀ ℕ) :
    basisMonomials σ ℤ μ = monomial μ (1 : ℤ) := by
  simp [coe_basisMonomials]

/- English proof (translation)
Establish `h : (monomial μ c : MvPolynomial (XZ Lt N0 N1) ℤ) = c • basisMonomials (XZ Lt N0 N1) ℤ μ`. Rewrite using `[basisMonomials_apply', smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[h, map_smul, Lj, Module.Basis.constr_basis]`.
-/
theorem Lj_monomial (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (μ : XZ Lt N0 N1 →₀ ℕ)
    (c : ℤ) : Lj Th (monomial μ c) = c • atMon Th μ := by
  have h : (monomial μ c : MvPolynomial (XZ Lt N0 N1) ℤ) = c • basisMonomials (XZ Lt N0 N1) ℤ μ := by
    rw [basisMonomials_apply', smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul, Lj, Module.Basis.constr_basis]

/- English proof (translation)
Establish `h : (monomial β c : MvPolynomial (Lt × Fin N0 × Fin N1) ℤ) = c • basisMonomials (Lt × Fin N0 × Fin N1) ℤ β`. Rewrite using `[basisMonomials_apply', smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[h, map_smul, Sj, Module.Basis.constr_basis]`.
-/
theorem Sj_monomial (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (β : Lt × Fin N0 × Fin N1 →₀ ℕ) (c : ℤ) :
    Sj Th (monomial β c) = c • ((β.prod fun _ n => (n.factorial : ℂ_[l])) * MvPowerSeries.coeff β Th) := by
  have h : (monomial β c : MvPolynomial (Lt × Fin N0 × Fin N1) ℤ) =
      c • basisMonomials (Lt × Fin N0 × Fin N1) ℤ β := by
    rw [basisMonomials_apply', smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul, Sj, Module.Basis.constr_basis]

/- English proof (translation)
Use `conv_rhs => rw [P.as_sum]`. Rewrite using `[map_sum]`. Unfold `applyAt0`. Use `Finset.sum_congr rfl fun μ _ => ?_` and prove the remaining obligations. Rewrite using `[Lj_monomial, atMon, smul_monomial, zsmul_eq_mul, mul_assoc]`.
-/
theorem applyAt0_eq (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (P : MvPolynomial (XZ Lt N0 N1) ℤ) : applyAt0 N0 N1 l Th P = Lj Th P := by
  conv_rhs => rw [P.as_sum]
  rw [map_sum]
  unfold applyAt0
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Lj_monomial, atMon, smul_monomial, zsmul_eq_mul, mul_assoc]

/- English proof (translation)
Use extensionality with `x`. Apply the tactic sequence `rw [Finsupp.fst_sumFinsuppEquivProdFinsupp, Finsupp.add_apply, Finsupp.mapDomain_apply Sum.inl_injective, Finsupp.mapDomain_of_notMem_range] <;> simp`. Apply the tactic sequence `rw [Finsupp.snd_sumFinsuppEquivProdFinsupp, Finsupp.add_apply, Finsupp.mapDomain_apply Sum.inr_injective, Finsupp.mapDomain_of_notMem_range] <;> simp`.
-/
theorem sfe_inl_inr (α : Lt × ℕ × Fin N0 →₀ ℕ) (β : Lt × Fin N0 × Fin N1 →₀ ℕ) :
    Finsupp.sumFinsuppEquivProdFinsupp
      (α.mapDomain (Sum.inl : _ → XZ Lt N0 N1) + β.mapDomain Sum.inr) = (α, β) := by
  ext x
  · rw [Finsupp.fst_sumFinsuppEquivProdFinsupp, Finsupp.add_apply,
      Finsupp.mapDomain_apply Sum.inl_injective, Finsupp.mapDomain_of_notMem_range] <;> simp
  · rw [Finsupp.snd_sumFinsuppEquivProdFinsupp, Finsupp.add_apply,
      Finsupp.mapDomain_apply Sum.inr_injective, Finsupp.mapDomain_of_notMem_range] <;> simp

/- English proof (translation)
Proceed by induction on `a using MvPolynomial.induction_on' with`. Consider the case `monomial α r`. Proceed by induction on `q using MvPolynomial.induction_on' with`. Consider the case `monomial β t`. Rewrite using `[rename_monomial, rename_monomial, monomial_mul, Lj_monomial, Sj_monomial, map_monomial, atMon, sfe_inl_inr]`.

Simplify using `only [smul_monomial, zsmul_eq_mul, smul_eq_mul, eq_intCast, Int.cast_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Consider the case `add q1 q2 h1 h2 => rw [map_add, mul_add, map_add, h1, h2, map_add, add_smul]`. Consider the case `add a1 a2 h1 h2 => rw [map_add, add_mul, map_add, h1, h2, map_add, smul_add]`.
-/
theorem Lj_inl_inr (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (a : MvPolynomial (Lt × ℕ × Fin N0) ℤ) (q : MvPolynomial (Lt × Fin N0 × Fin N1) ℤ) :
    Lj Th (rename (Sum.inl : _ → XZ Lt N0 N1) a * rename (Sum.inr : _ → XZ Lt N0 N1) q) =
      Sj Th q • map (Int.castRingHom ℂ_[l]) a := by
  induction a using MvPolynomial.induction_on' with
  | monomial α r =>
    induction q using MvPolynomial.induction_on' with
    | monomial β t =>
      rw [rename_monomial, rename_monomial, monomial_mul, Lj_monomial, Sj_monomial, map_monomial,
        atMon, sfe_inl_inr]
      simp only [smul_monomial, zsmul_eq_mul, smul_eq_mul, eq_intCast, Int.cast_mul]
      congr 1
      ring
    | add q1 q2 h1 h2 => rw [map_add, mul_add, map_add, h1, h2, map_add, add_smul]
  | add a1 a2 h1 h2 => rw [map_add, add_mul, map_add, h1, h2, map_add, smul_add]

def Xm (s : Lt) (p : ℕ) : Matrix (Fin p) (Fin N0) (MvPolynomial (Lt × ℕ × Fin N0) ℤ) :=
  Matrix.of fun i a => X (s, (i : ℕ), a)

def Dm (s : Lt) (p : ℕ) (f : Fin p → Fin N0) : MvPolynomial (Lt × ℕ × Fin N0) ℤ :=
  ((Xm (N0 := N0) s p).submatrix id f).det

def Zm (s : Lt) (p : ℕ) (I : Fin p ↪o Fin N1) (f : Fin p → Fin N0) :
    MvPolynomial (Lt × Fin N0 × Fin N1) ℤ :=
  ∏ i, X (s, f i, I i)

/- English proof (translation)
Set `A : Matrix (Fin p) (Fin N0) (MvPolynomial (XZ Lt N0 N1) ℤ)` to `Matrix.of fun i a => X (Sum.inl (s, (i : ℕ), a))`. Set `B : Matrix (Fin N0) (Fin p) (MvPolynomial (XZ Lt N0 N1) ℤ)` to `Matrix.of fun a k => X (Sum.inr (s, a, I k))`. Establish `hAB : minorXZ N0 N1 s p I = (A * B).det`. Unfold `minorXZ`. Use `congr 1`.

Rewrite using `[hAB, det_mul_rect]`. Use `Finset.sum_congr rfl fun f _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`. Use `congr 1`. Rewrite using `[Dm, AlgHom.map_det]`.

Use `congr 1`. Use extensionality with `i k`. Simplify using `[A, Xm, AlgHom.mapMatrix_apply, rename_X]`. Simplify using `[Zm, B, map_prod, rename_X]`.
-/
theorem minorXZ_expand (s : Lt) (p : ℕ) (I : Fin p ↪o Fin N1) :
    minorXZ N0 N1 s p I = ∑ f : Fin p → Fin N0,
      rename (Sum.inl : _ → XZ Lt N0 N1) (Dm s p f) *
        rename (Sum.inr : _ → XZ Lt N0 N1) (Zm s p I f) := by
  let A : Matrix (Fin p) (Fin N0) (MvPolynomial (XZ Lt N0 N1) ℤ) :=
    Matrix.of fun i a => X (Sum.inl (s, (i : ℕ), a))
  let B : Matrix (Fin N0) (Fin p) (MvPolynomial (XZ Lt N0 N1) ℤ) :=
    Matrix.of fun a k => X (Sum.inr (s, a, I k))
  have hAB : minorXZ N0 N1 s p I = (A * B).det := by
    unfold minorXZ
    congr 1
  rw [hAB, det_mul_rect]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [mul_comm]
  congr 1
  · rw [Dm, AlgHom.map_det]
    congr 1
    ext i k
    simp [A, Xm, AlgHom.mapMatrix_apply, rename_X]
  · simp [Zm, B, map_prod, rename_X]

/- English proof (translation)
Unfold `Gxz`. Repeatedly rewrite using `[minorXZ_expand, Fintype.prod_sum]`. Use `Finset.sum_congr rfl fun F _ => ?_` and prove the remaining obligations. Simplify using `only [map_prod, Finset.prod_mul_distrib]`.
-/
theorem Gxz_expand (nu : Lt → YoungDiagram) (I : ColChoice N1 nu) :
    Gxz N0 N1 nu I = ∑ F : (∀ s (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) → Fin N0),
      rename (Sum.inl : _ → XZ Lt N0 N1) (∏ s, ∏ c, Dm s _ (F s c)) *
        rename (Sum.inr : _ → XZ Lt N0 N1) (∏ s, ∏ c, Zm s _ (I s c) (F s c)) := by
  unfold Gxz
  simp_rw [minorXZ_expand, Fintype.prod_sum]
  refine Finset.sum_congr rfl fun F _ => ?_
  simp only [map_prod, Finset.prod_mul_distrib]

/- English proof (translation)
Unfold `nablaX`. Use `Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_` and prove the remaining obligations. Unfold `Dm Xm`. Both sides reduce to the same expression.
-/
theorem nablaX_eq (nu : Lt → YoungDiagram) (J : ColChoice N0 nu) :
    nablaX N0 nu J = ∏ s, ∏ c, Dm s _ (J s c) := by
  unfold nablaX
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  unfold Dm Xm
  rfl

/- English proof (translation)
Distinguish the cases in `h : ∀ s (c : Fin ((nu s).rowLen 0)), ∃ (J : Fin ((nu s).colLen c) ↪o Fin N0) (e : ℤ), Dm s _ (F s c) = (e : MvPolynomial (Lt × ℕ × Fin N0) ℤ) * Dm s _ J`. Use `choose Jf ef hJ using h`. Establish `hp : ∏ s, ∏ c, Dm s _ (F s c) = ((∏ s, ∏ c, ef s c : ℤ) : MvPolynomial (Lt × ℕ × Fin N0) ℤ) * nablaX N0 nu (Jf : ColChoice N0 nu)`. Establish `hn : nablaX N0 nu Jf = ∏ s, ∏ c, Dm s _ (Jf s c)` using `nablaX_eq nu Jf`. Rewrite using `[hn]`.

Repeatedly rewrite using `[hJ, Finset.prod_mul_distrib]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[hp, map_mul, map_intCast, ← zsmul_eq_mul]`. Conclude with `zsmul_mem (Submodule.subset_span (Set.mem_range_self (f := fun J : ColChoice N0 nu => MvPolynomial.map (Int.castRingHom ℂ_[l]) (nablaX N0 nu J)) Jf)) _`.

Use `push Not at h`. Take `⟨s, c, hsc⟩` from `h`. Establish `h0 : Dm s _ (F s c) = 0`. Break down `det_submatrix_fun (Xm (N0 := N0) s _) (F s c) with h0 | ⟨J, e, he⟩` into its components or cases. Conclude with `h0`.

Conclude with `absurd he (hsc J e)`. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ s) (Finset.prod_eq_zero (Finset.mem_univ c) h0), map_zero]`. Conclude with `Submodule.zero_mem _`.
-/
theorem prodD_mem (nu : Lt → YoungDiagram)
    (F : ∀ s (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) → Fin N0) :
    map (Int.castRingHom ℂ_[l]) (∏ s, ∏ c, Dm s _ (F s c)) ∈ nablaSpanC Lt l N0 nu := by
  by_cases h : ∀ s (c : Fin ((nu s).rowLen 0)), ∃ (J : Fin ((nu s).colLen c) ↪o Fin N0) (e : ℤ),
      Dm s _ (F s c) = (e : MvPolynomial (Lt × ℕ × Fin N0) ℤ) * Dm s _ J
  · choose Jf ef hJ using h
    have hp : ∏ s, ∏ c, Dm s _ (F s c) =
        ((∏ s, ∏ c, ef s c : ℤ) : MvPolynomial (Lt × ℕ × Fin N0) ℤ) *
          nablaX N0 nu (Jf : ColChoice N0 nu) := by
      have hn : nablaX N0 nu Jf = ∏ s, ∏ c, Dm s _ (Jf s c) := nablaX_eq nu Jf
      rw [hn]
      simp_rw [hJ, Finset.prod_mul_distrib]
      push_cast
      rfl
    rw [hp, map_mul, map_intCast, ← zsmul_eq_mul]
    exact zsmul_mem (Submodule.subset_span (Set.mem_range_self (f := fun J : ColChoice N0 nu =>
      MvPolynomial.map (Int.castRingHom ℂ_[l]) (nablaX N0 nu J)) Jf)) _
  · push Not at h
    obtain ⟨s, c, hsc⟩ := h
    have h0 : Dm s _ (F s c) = 0 := by
      rcases det_submatrix_fun (Xm (N0 := N0) s _) (F s c) with h0 | ⟨J, e, he⟩
      · exact h0
      · exact absurd he (hsc J e)
    rw [Finset.prod_eq_zero (Finset.mem_univ s) (Finset.prod_eq_zero (Finset.mem_univ c) h0),
      map_zero]
    exact Submodule.zero_mem _

end Span

/- English proof (translation)
Introduce `Lt _ _ l _ N0 N1 nu Th I`. Rewrite using `[applyAt0_eq, Gxz_expand, map_sum]`. Use `Submodule.sum_mem _ fun F _ => ?_` and prove the remaining obligations. Rewrite using `[Lj_inl_inr]`. Conclude with `Submodule.smul_mem _ _ (prodD_mem nu F)`.
-/
theorem stepSpan : StepSpan := by
  intro Lt _ _ l _ N0 N1 nu Th I
  rw [applyAt0_eq, Gxz_expand, map_sum]
  refine Submodule.sum_mem _ fun F _ => ?_
  rw [Lj_inl_inr]
  exact Submodule.smul_mem _ _ (prodD_mem nu F)

end GenFrameSpan
