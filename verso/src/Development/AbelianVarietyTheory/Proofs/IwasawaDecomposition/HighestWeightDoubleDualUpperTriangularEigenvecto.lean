import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightTensorDualRepDualHighestWeightAtEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ZariskiDenseRationalPointsDefiniteUnitaryCharZerStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryRationalPointMatrixHomSurjectiveOnto

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.AlgWtF.DDHwT

section Fam

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K : Type} [Field K]

open Classical in

def fam (τ : L →+* K) (B : GL (Fin n) K) : (L →+* K) → GL (Fin n) K := fun σ =>
  if σ = τ then B else if σ = τ.comp (IsCMField.complexConj L : L →+* L) then inside₂ K n B else 1

/- English proof (translation)
Establish `hcc : ∀ σ' : L →+* K, (σ'.comp (IsCMField.complexConj L : L →+* L)).comp (IsCMField.complexConj L : L →+* L) = σ'`. Introduce `σ'`. Use extensionality with `x`. Simplify using `[IsCMField.complexConj_apply_apply]`. Establish `hinj : ∀ σ₁ σ₂ : L →+* K, σ₁.comp (IsCMField.complexConj L : L →+* L) = σ₂.comp (IsCMField.complexConj L : L →+* L) → σ₁ = σ₂`.

Introduce `σ₁ σ₂ e`. Rewrite using `[← hcc σ₁, e, hcc]`. Distinguish the cases in `h1 : σ = τ`. Substitute `h1` using the available equality. Simplify using `only [fam, h, if_false, if_true]`.

Both sides reduce to the same expression. Distinguish the cases in `h2 : σ = τ.comp (IsCMField.complexConj L : L →+* L)`. Substitute `h2` using the available equality. Simplify using `only [fam, hcc, if_true, h]`. Simplify using `[inside₂]`.

Establish `h3 : σ.comp (IsCMField.complexConj L : L →+* L) ≠ τ`. Introduce `e`. Apply `h2` to reduce the goal to its premises. Rewrite using `[← e, hcc]`. Establish `h4 : σ.comp (IsCMField.complexConj L : L →+* L) ≠ τ.comp (IsCMField.complexConj L : L →+* L)` using `fun e => h1 (hinj _ _ e)`.

Simplify using `[fam, h1, h2, h3, h4]`.
-/
theorem fam_conj (τ : L →+* K) (B : GL (Fin n) K) (h : τ.comp (IsCMField.complexConj L : L →+* L) ≠ τ)
    (σ : L →+* K) : ((fam τ B (σ.comp (IsCMField.complexConj L : L →+* L)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.transpose (((fam τ B σ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have hcc : ∀ σ' : L →+* K, (σ'.comp (IsCMField.complexConj L : L →+* L)).comp (IsCMField.complexConj L : L →+* L) = σ' := by
    intro σ'
    ext x
    simp [IsCMField.complexConj_apply_apply]
  have hinj : ∀ σ₁ σ₂ : L →+* K, σ₁.comp (IsCMField.complexConj L : L →+* L) = σ₂.comp (IsCMField.complexConj L : L →+* L) → σ₁ = σ₂ := by
    intro σ₁ σ₂ e
    rw [← hcc σ₁, e, hcc]
  by_cases h1 : σ = τ
  · subst h1
    simp only [fam, h, if_false, if_true]
    rfl
  · by_cases h2 : σ = τ.comp (IsCMField.complexConj L : L →+* L)
    · subst h2
      simp only [fam, hcc, if_true, h]
      simp [inside₂]
    · have h3 : σ.comp (IsCMField.complexConj L : L →+* L) ≠ τ := by
        intro e; apply h2; rw [← e, hcc]
      have h4 : σ.comp (IsCMField.complexConj L : L →+* L) ≠ τ.comp (IsCMField.complexConj L : L →+* L) :=
        fun e => h1 (hinj _ _ e)
      simp [fam, h1, h2, h3, h4]

/- English proof (translation)
Use function extensionality and compare the values at `p`. Simplify using `only [fam, Formalism.L2.NX.evPtF]`. Apply the tactic sequence `split_ifs <;> simp_all [inside₂, Matrix.one_apply]`.
-/
theorem fam_eval (τ : L →+* K) (B : GL (Fin n) K) :
    (fun p : (L →+* K) × Fin n × Fin n => ((fam τ B p.1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) p.2.1 p.2.2) =
      Formalism.L2.NX.evPtF (IsCMField.complexConj L : L →+* L) τ B := by
  funext p
  simp only [fam, Formalism.L2.NX.evPtF]
  split_ifs <;> simp_all [inside₂, Matrix.one_apply]

end Fam

section Eig

open Formalism.L2.DIV

variable {ι : Type} [Fintype ι] {n : ℕ} {K : Type} [Field K]

/- English proof (translation)
Rewrite using `[← (bVVfun_spec K lam).2]`. Conclude with `Submodule.subset_span ⟨j, rfl⟩`.
-/
theorem bVVfun_mem (lam : ι → DomWeight n) (j : VVIdx lam) : bVVfun K lam j ∈ VV K lam := by
  rw [← (bVVfun_spec K lam).2]
  exact Submodule.subset_span ⟨j, rfl⟩

def wOf (lam : ι → DomWeight n) (u : VVIdx lam → K) : Pol K ι n := ∑ j, u j • bVVfun K lam j

/- English proof (translation)
The claim follows from `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (bVVfun_mem lam j)`.
-/
theorem wOf_mem (lam : ι → DomWeight n) (u : VVIdx lam → K) : wOf lam u ∈ VV K lam :=
  Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (bVVfun_mem lam j)

/- English proof (translation)
Introduce `h0`. Apply `hu` to reduce the goal to its premises. Use function extensionality and compare the values at `j`. Conclude with `Fintype.linearIndependent_iff.mp (bVVfun_spec K lam).1 u h0 j`.
-/
theorem wOf_ne (lam : ι → DomWeight n) (u : VVIdx lam → K) (hu : u ≠ 0) : wOf lam u ≠ 0 := by
  intro h0
  apply hu
  funext j
  exact Fintype.linearIndependent_iff.mp (bVVfun_spec K lam).1 u h0 j

/- English proof (translation)
Use `set w := wOf lam u with hw`. Use `set F : VV K lam := ⟨_, hMV w (wOf_mem lam u)⟩ with hF`. Establish `hco : ∀ i, (bVV K lam).repr F i = c⁻¹ * χ * u i`. Introduce `i`. Establish `e1 : c * DDHw.coord lam i (Formalism.GradedWeylDivisibility.blockAct K M w) = χ * u i`.

Rewrite using `[← h i, hw, wOf, map_sum, map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, map_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : DDHw.coord lam i (Formalism.GradedWeylDivisibility.blockAct K M w) = (bVV K lam).repr F i` using `DDHw.coord_spec lam i F`.

Rewrite using `[← e2, mul_assoc, ← e1, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]`. Establish `hsum` using `congrArg Subtype.val ((bVV K lam).sum_repr F)`. Rewrite `hsum` using `[Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul, bVV_coe, hco] at hsum`. Use `show (F : Pol K ι n) = _`.

Rewrite using `[← hsum, hw, wOf, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul]`.
-/
theorem wOf_eig (lam : ι → DomWeight n) (M : ι → Matrix (Fin n) (Fin n) K)
    (hMV : ∀ F ∈ VV K lam, Formalism.GradedWeylDivisibility.blockAct K M F ∈ VV K lam) (c χ : K) (hc : c ≠ 0) (u : VVIdx lam → K)
    (h : ∀ i, ∑ j, c * DDHw.coord lam i (Formalism.GradedWeylDivisibility.blockAct K M (bVVfun K lam j)) * u j = χ * u i) :
    Formalism.GradedWeylDivisibility.blockAct K M (wOf lam u) = (c⁻¹ * χ) • wOf lam u := by
  classical
  set w := wOf lam u with hw
  set F : VV K lam := ⟨_, hMV w (wOf_mem lam u)⟩ with hF
  have hco : ∀ i, (bVV K lam).repr F i = c⁻¹ * χ * u i := by
    intro i
    have e1 : c * DDHw.coord lam i (Formalism.GradedWeylDivisibility.blockAct K M w) = χ * u i := by
      rw [← h i, hw, wOf, map_sum, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, map_smul, smul_eq_mul]
      ring
    have e2 : DDHw.coord lam i (Formalism.GradedWeylDivisibility.blockAct K M w) = (bVV K lam).repr F i := DDHw.coord_spec lam i F
    rw [← e2, mul_assoc, ← e1, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  have hsum := congrArg Subtype.val ((bVV K lam).sum_repr F)
  rw [Submodule.coe_sum] at hsum
  simp only [Submodule.coe_smul, bVV_coe, hco] at hsum
  show (F : Pol K ι n) = _
  rw [← hsum, hw, wOf, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul]

/- English proof (translation)
Use `set g : ι → GL (Fin n) K := fun τ => if τ = τ₀ then B else 1 with hg`. Establish `hgM : (fun τ => ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose) = fun τ => if τ = τ₀ then (B : Matrix (Fin n) (Fin n) K).transpose else 1`. Use function extensionality and compare the values at `τ`. Apply the tactic sequence `by_cases h : τ = τ₀ <;> simp [hg, h]`. Establish `hdet : detTwK lam g ≠ 0`.

Unfold `detTwK`. Conclude with `Finset.prod_ne_zero_iff.2 fun τ _ => Units.ne_zero _`. Establish `e : actP lam g F = detTwK lam g • Formalism.GradedWeylDivisibility.blockAct K (fun τ => if τ = τ₀ then (B : Matrix (Fin n) (Fin n) K).transpose else 1) F`. Rewrite using `[actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, trAct, hgM]`. Establish `h1` using `polyAction_mem_VV lam g hF`.

Rewrite `h1` using `[e]`. Conclude with `(Submodule.smul_mem_iff _ hdet).1 h1`.
-/
theorem blockAct_mem [DecidableEq ι] (lam : ι → DomWeight n) (τ₀ : ι) (B : GL (Fin n) K) (F : Pol K ι n)
    (hF : F ∈ VV K lam) :
    Formalism.GradedWeylDivisibility.blockAct K (fun τ => if τ = τ₀ then (B : Matrix (Fin n) (Fin n) K).transpose else 1) F ∈ VV K lam := by
  set g : ι → GL (Fin n) K := fun τ => if τ = τ₀ then B else 1 with hg
  have hgM : (fun τ => ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose) =
      fun τ => if τ = τ₀ then (B : Matrix (Fin n) (Fin n) K).transpose else 1 := by
    funext τ
    by_cases h : τ = τ₀ <;> simp [hg, h]
  have hdet : detTwK lam g ≠ 0 := by
    unfold detTwK
    exact Finset.prod_ne_zero_iff.2 fun τ _ => Units.ne_zero _
  have e : actP lam g F = detTwK lam g •
      Formalism.GradedWeylDivisibility.blockAct K (fun τ => if τ = τ₀ then (B : Matrix (Fin n) (Fin n) K).transpose else 1) F := by
    rw [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, trAct, hgM]
  have h1 := polyAction_mem_VV lam g hF
  rw [e] at h1
  exact (Submodule.smul_mem_iff _ hdet).1 h1

end Eig

section Main

open Formalism.L2.DIV
open scoped Matrix

/- English proof (translation)
Introduce `L _ _ _ n ι _ _ K _ _ emb lam hd τ₀ mu hH`. Take `⟨ι', _, _, b', P', hP', v, hv, hB⟩` from `hH`. Establish `hinj` using `hd.1`. Establish `hcm` using `hd.2`. Use `set bD := DDHw.bDD (K := K) lam with hbD`.

Use `set Q : Matrix ι' (VVIdx lam) K := b'.toMatrix bD with hQ`. Use `set Q' : Matrix (VVIdx lam) ι' K := bD.toMatrix b' with hQ'`. Establish `hQQ : Q * Q' = 1` using `Module.Basis.toMatrix_mul_toMatrix_flip _ _`. Establish `hQQ' : Q' * Q = 1` using `Module.Basis.toMatrix_mul_toMatrix_flip _ _`. Establish `hrat : ∀ a a', ∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n → MvPolynomial.eval (fun p : (L →+* K) × Fin n × Fin n => p.1 ((γ₀ : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2)) (P' a a' - ∑ i, ∑ j, MvPolynomial.C (Q a i * Q' j a') * DDHw.tenPF emb lam i j) = 0`.

Introduce `a a' γ₀ hγ`. Take `⟨γ, rfl⟩` from `ratHom_surjective L n γ₀ hγ`. Establish `hm : (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = ((ratHom γ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom`. Rewrite using `[show ratHom γ = ratFun γ from rfl, ← incGL_ratFun γ]`. Both sides reduce to the same expression.

Establish `h1` using `congrFun (congrFun (hP' γ _ hm) a) a'`. Establish `h2 : LinearMap.toMatrix b' b' ((wtRepF emb lam).dual γ) = Q * LinearMap.toMatrix bD bD ((wtRepF emb lam).dual γ) * Q'` using `(basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b' bD b' bD _).symm`. Rewrite `h2` using `[hbD, DDHw.dd_toMatrix, DDHw.tenRepF_toMatrix emb lam γ _ hm]`. Rewrite using `[map_sub, ← h1, h2, map_sum]`. Simplify using `only [map_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C, Matrix.mul_apply, Finset.sum_mul]`.

Rewrite using `[sub_eq_zero, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `erw [Matrix.mul_apply]`. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Use `set u : VVIdx lam → K := Q' *ᵥ v with hu`. Establish `hu0 : u ≠ 0`. Introduce `h0`. Apply `hv` to reduce the goal to its premises.

Establish `e : Q *ᵥ u = v` using `by rw [hu, Matrix.mulVec_mulVec, hQQ, Matrix.one_mulVec]`. Rewrite using `[← e, h0, Matrix.mulVec_zero]`. Use `⟨wOf lam u, wOf_mem lam u, wOf_ne lam u hu0, fun B hBt => ?_⟩` and prove the remaining obligations. Establish `hne : (emb τ₀).comp (IsCMField.complexConj L : L →+* L) ≠ emb τ₀` using `fun h' => hcm τ₀ τ₀ h'.symm`. Use `set T : Matrix (VVIdx lam) (VVIdx lam) K := Matrix.of fun i j => MvPolynomial.eval (NX.evPtF (IsCMField.complexConj L : L →+* L) (emb τ₀) B) (DDHw.tenPF emb lam i j) with hT`.

Establish `hev : ∀ a a', MvPolynomial.eval (NX.evPtF (IsCMField.complexConj L : L →+* L) (emb τ₀) B) (P' a a') = ∑ i, ∑ j, Q a i * Q' j a' * T i j`. Introduce `a a'`. Establish `h0` using `GlobalTheory.T.zariskiDense_rationalPoints_definiteUnitary_charZero L n K _ (hrat a a') (fam (emb τ₀) B) (fam_conj _ B hne)`. Rewrite `h0` using `[fam_eval, map_sub, sub_eq_zero]`. Rewrite using `[h0, map_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.eval_mul, MvPolynomial.eval_C, hT, Matrix.of_apply]`. Establish `hmat : (Matrix.of fun a a' => MvPolynomial.eval (NX.evPtF (IsCMField.complexConj L : L →+* L) (emb τ₀) B) (P' a a')) = Q * T * Q'`.

Use extensionality with `a a'`. Rewrite using `[Matrix.of_apply, hev, Matrix.mul_apply, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Use `set χ : K := ∏ a, (B : Matrix (Fin n) (Fin n) K) a a ^ mu a with hχ`. Establish `hTu : T *ᵥ u = χ • u`. Establish `h1` using `hB B hBt`. Rewrite `h1` using `[hmat]`.

Establish `e : Q' *ᵥ ((Q * T * Q') *ᵥ v) = T *ᵥ u`. Rewrite using `[hu, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQQ', Matrix.one_mul]`. Rewrite using `[← e, h1, Matrix.mulVec_smul]`. Use `set c : K := detPow K n B (lam τ₀).detShift with hc`. Establish `hc0 : c ≠ 0`.

Rewrite using `[hc, detPow]`. Conclude with `Units.ne_zero _`. Establish `hM : (fun τ => (Matrix.of fun a b => NX.evPtF (DDHw.cL L) (emb τ₀) B (emb τ, a, b)).transpose) = fun τ => if τ = τ₀ then (B : Matrix (Fin n) (Fin n) K).transpose else 1`. Use function extensionality and compare the values at `τ`. Use `split_ifs with hτ`.

Rewrite using `[hτ, DDHw.evPtF_self]`. Rewrite using `[DDHw.evPtF_other _ _ _ _ (fun h' => hτ (hinj h')) (hcm τ τ₀), Matrix.transpose_one]`. Establish `hTe : ∀ i j, T i j = c * DDHw.coord lam i (Formalism.GradedWeylDivisibility.blockAct K (fun τ => if τ = τ₀ then (B : Matrix (Fin n) (Fin n) K).transpose else 1) (bVVfun K lam j))`. Introduce `i j`. Rewrite using `[hT, Matrix.of_apply, DDHw.tenPF_eval]`.

Use `erw [DDHw.detTwistPolynomial_eval_embeddingPoint emb hd lam τ₀ B]`. Rewrite using `[← hM]`. Use `wOf_eig lam _ (blockAct_mem lam τ₀ B) c χ hc0 u fun i => ?_` and prove the remaining obligations. Use `congrFun hTu i` as an intermediate fact. Simplify using `only [Matrix.mulVec, dotProduct, hTe, Pi.smul_apply, smul_eq_mul] at this`.

Conclude with `this`.
-/
theorem hw_eigvec_transport : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (K : Type) [Field K] [CharZero K] (emb : ι → L →+* K) (lam : ι → DomWeight n), GlobalTheory.AlgWtF.CMDist emb →
    ∀ (τ₀ : ι) (mu : Fin n → ℤ),
      NX.HWAtF (IsCMField.complexConj L : L →+* L) (GlobalTheory.AlgWtF.wtRepF emb lam).dual (emb τ₀) mu →
      ∃ w : Formalism.L2.DIV.Pol K ι n, w ∈ Formalism.L2.DIV.VV K lam ∧ w ≠ 0 ∧
        ∀ B : GL (Fin n) K, (B : Matrix (Fin n) (Fin n) K).BlockTriangular id →
          Formalism.GradedWeylDivisibility.blockAct K (fun τ => if τ = τ₀ then (B : Matrix (Fin n) (Fin n) K).transpose else 1) w =
            ((detPow K n B (lam τ₀).detShift)⁻¹ * ∏ a, (B : Matrix (Fin n) (Fin n) K) a a ^ mu a) • w := by
  intro L _ _ _ n ι _ _ K _ _ emb lam hd τ₀ mu hH
  classical
  obtain ⟨ι', _, _, b', P', hP', v, hv, hB⟩ := hH
  have hinj := hd.1
  have hcm := hd.2
  set bD := DDHw.bDD (K := K) lam with hbD
  set Q : Matrix ι' (VVIdx lam) K := b'.toMatrix bD with hQ
  set Q' : Matrix (VVIdx lam) ι' K := bD.toMatrix b' with hQ'
  have hQQ : Q * Q' = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  have hQQ' : Q' * Q = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  have hrat : ∀ a a', ∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n →
      MvPolynomial.eval (fun p : (L →+* K) × Fin n × Fin n => p.1 ((γ₀ : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2))
        (P' a a' - ∑ i, ∑ j, MvPolynomial.C (Q a i * Q' j a') * DDHw.tenPF emb lam i j) = 0 := by
    intro a a' γ₀ hγ
    obtain ⟨γ, rfl⟩ := ratHom_surjective L n γ₀ hγ
    have hm : (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        ((ratHom γ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom := by
      rw [show ratHom γ = ratFun γ from rfl, ← incGL_ratFun γ]
      rfl
    have h1 := congrFun (congrFun (hP' γ _ hm) a) a'
    have h2 : LinearMap.toMatrix b' b' ((wtRepF emb lam).dual γ) =
        Q * LinearMap.toMatrix bD bD ((wtRepF emb lam).dual γ) * Q' :=
      (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b' bD b' bD _).symm
    rw [hbD, DDHw.dd_toMatrix, DDHw.tenRepF_toMatrix emb lam γ _ hm] at h2
    rw [map_sub, ← h1, h2, map_sum]
    simp only [map_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C, Matrix.mul_apply, Finset.sum_mul]
    rw [sub_eq_zero, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    erw [Matrix.mul_apply]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  set u : VVIdx lam → K := Q' *ᵥ v with hu
  have hu0 : u ≠ 0 := by
    intro h0
    apply hv
    have e : Q *ᵥ u = v := by rw [hu, Matrix.mulVec_mulVec, hQQ, Matrix.one_mulVec]
    rw [← e, h0, Matrix.mulVec_zero]
  refine ⟨wOf lam u, wOf_mem lam u, wOf_ne lam u hu0, fun B hBt => ?_⟩
  have hne : (emb τ₀).comp (IsCMField.complexConj L : L →+* L) ≠ emb τ₀ := fun h' => hcm τ₀ τ₀ h'.symm
  set T : Matrix (VVIdx lam) (VVIdx lam) K := Matrix.of fun i j =>
    MvPolynomial.eval (NX.evPtF (IsCMField.complexConj L : L →+* L) (emb τ₀) B) (DDHw.tenPF emb lam i j) with hT
  have hev : ∀ a a', MvPolynomial.eval (NX.evPtF (IsCMField.complexConj L : L →+* L) (emb τ₀) B) (P' a a') =
      ∑ i, ∑ j, Q a i * Q' j a' * T i j := by
    intro a a'
    have h0 := GlobalTheory.T.zariskiDense_rationalPoints_definiteUnitary_charZero L n K _ (hrat a a') (fam (emb τ₀) B) (fam_conj _ B hne)
    rw [fam_eval, map_sub, sub_eq_zero] at h0
    rw [h0, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, hT, Matrix.of_apply]
  have hmat : (Matrix.of fun a a' => MvPolynomial.eval (NX.evPtF (IsCMField.complexConj L : L →+* L) (emb τ₀) B) (P' a a')) =
      Q * T * Q' := by
    ext a a'
    rw [Matrix.of_apply, hev, Matrix.mul_apply, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  set χ : K := ∏ a, (B : Matrix (Fin n) (Fin n) K) a a ^ mu a with hχ
  have hTu : T *ᵥ u = χ • u := by
    have h1 := hB B hBt
    rw [hmat] at h1
    have e : Q' *ᵥ ((Q * T * Q') *ᵥ v) = T *ᵥ u := by
      rw [hu, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQQ', Matrix.one_mul]
    rw [← e, h1, Matrix.mulVec_smul]
  set c : K := detPow K n B (lam τ₀).detShift with hc
  have hc0 : c ≠ 0 := by
    rw [hc, detPow]
    exact Units.ne_zero _
  have hM : (fun τ => (Matrix.of fun a b => NX.evPtF (DDHw.cL L) (emb τ₀) B (emb τ, a, b)).transpose) =
      fun τ => if τ = τ₀ then (B : Matrix (Fin n) (Fin n) K).transpose else 1 := by
    funext τ
    split_ifs with hτ
    · rw [hτ, DDHw.evPtF_self]
    · rw [DDHw.evPtF_other _ _ _ _ (fun h' => hτ (hinj h')) (hcm τ τ₀), Matrix.transpose_one]
  have hTe : ∀ i j, T i j = c * DDHw.coord lam i
      (Formalism.GradedWeylDivisibility.blockAct K (fun τ => if τ = τ₀ then (B : Matrix (Fin n) (Fin n) K).transpose else 1) (bVVfun K lam j)) := by
    intro i j
    rw [hT, Matrix.of_apply, DDHw.tenPF_eval]
    erw [DDHw.detTwistPolynomial_eval_embeddingPoint emb hd lam τ₀ B]
    rw [← hM]
  refine wOf_eig lam _ (blockAct_mem lam τ₀ B) c χ hc0 u fun i => ?_
  have := congrFun hTu i
  simp only [Matrix.mulVec, dotProduct, hTe, Pi.smul_apply, smul_eq_mul] at this
  exact this

end Main

end GlobalTheory.AlgWtF.DDHwT
