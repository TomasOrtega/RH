import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
open Formalism.L2.Ker MvPolynomial

noncomputable section

namespace GlobalTheory.JetAlg

open Formalism.L2.DIV Formalism.BasicNotions

abbrev algPol (σ : Type) : Subring (MvPolynomial σ ℂ) :=
  (MvPolynomial.map (algebraMap (algebraicClosure ℚ ℂ) ℂ)).range

/- English proof (translation)
Assemble the required witnesses or components as `⟨X v, map_X _ _⟩`.
-/
theorem X_mem {σ : Type} (v : σ) : (X v : MvPolynomial σ ℂ) ∈ algPol σ := ⟨X v, map_X _ _⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨monomial u ⟨c, mem_algebraicClosure_iff.2 hc⟩, by rw [map_monomial]; rfl⟩`.
-/
theorem monomial_mem {σ : Type} (u : σ →₀ ℕ) {c : ℂ} (hc : IsAlgebraic ℚ c) :
    monomial u c ∈ algPol σ :=
  ⟨monomial u ⟨c, mem_algebraicClosure_iff.2 hc⟩, by rw [map_monomial]; rfl⟩

/- English proof (translation)
Take `⟨q, rfl⟩` from `hp`. Rewrite using `[coeff_map]`. Conclude with `mem_algebraicClosure_iff.1 (q.coeff m).2`.
-/
theorem coeff_isAlgebraic {σ : Type} {p : MvPolynomial σ ℂ} (hp : p ∈ algPol σ) (m : σ →₀ ℕ) :
    IsAlgebraic ℚ (p.coeff m) := by
  obtain ⟨q, rfl⟩ := hp
  rw [coeff_map]
  exact mem_algebraicClosure_iff.1 (q.coeff m).2

/- English proof (translation)
Use `choose N hN using h`. Use `⟨(Matrix.of N).det, ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.map_det]`. Use `congr 1`. Use extensionality with `p q`.

Simplify using `[hN]`.
-/
theorem det_mem {σ : Type} {s : ℕ} (M : Matrix (Fin s) (Fin s) (MvPolynomial σ ℂ))
    (h : ∀ p q, M p q ∈ algPol σ) : M.det ∈ algPol σ := by
  choose N hN using h
  refine ⟨(Matrix.of N).det, ?_⟩
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp [hN]

/- English proof (translation)
Take `⟨q, rfl⟩` from `hp`. Proceed by induction on `q using MvPolynomial.induction_on with`. Consider the case `C a => exact ⟨C a, by simp [algebraMap_eq]⟩`. Consider the case `add p q hp hq => rw [map_add, map_add]`. Conclude with `add_mem hp hq`.

Consider the case `mul_X p v hp => rw [map_mul, map_mul, map_X, aeval_X]`. Conclude with `mul_mem hp (hg v)`.
-/
theorem aeval_mem {σ τ : Type} {p : MvPolynomial σ ℂ} (hp : p ∈ algPol σ) (g : σ → MvPolynomial τ ℂ)
    (hg : ∀ v, g v ∈ algPol τ) : aeval g p ∈ algPol τ := by
  obtain ⟨q, rfl⟩ := hp
  induction q using MvPolynomial.induction_on with
  | C a => exact ⟨C a, by simp [algebraMap_eq]⟩
  | add p q hp hq => rw [map_add, map_add]; exact add_mem hp hq
  | mul_X p v hp => rw [map_mul, map_mul, map_X, aeval_X]; exact mul_mem hp (hg v)

/- English proof (translation)
Unfold `bVVfun ten`. Use `prod_mem fun τ _ => ?_` and prove the remaining obligations. Take `⟨-, -, K, sz, hsz, I, -, -, hb⟩` from `(Formalism.GradedWeylDivisibility.sSBasis ℂ n n (lam τ).natW).choose_spec.2 (j τ)`. Establish `hb' : ssB ℂ (lam τ).natW (j τ) = Formalism.GradedWeylDivisibility.bideterminant ℂ sz hsz I` using `hb`. Use `show Formalism.GradedWeylDivisibility.blockEmb ℂ τ (ssB ℂ (lam τ).natW (j τ)) ∈ _`.

Rewrite using `[hb']`. Establish `hB : Formalism.GradedWeylDivisibility.bideterminant ℂ sz hsz I ∈ algPol (Fin n × Fin n)`. Unfold `Formalism.GradedWeylDivisibility.bideterminant Formalism.GradedWeylDivisibility.initMinor`. Conclude with `prod_mem fun k _ => det_mem _ fun p q => X_mem _`. Take `⟨q, hq⟩` from `hB`.

Conclude with `⟨Formalism.GradedWeylDivisibility.blockEmb _ τ q, by rw [← hq]; exact map_rename _ _ _⟩`.
-/
theorem bVVfun_mem {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (j : VVIdx lam) :
    bVVfun ℂ lam j ∈ algPol (ι × Fin n × Fin n) := by
  unfold bVVfun ten
  refine prod_mem fun τ _ => ?_
  obtain ⟨-, -, K, sz, hsz, I, -, -, hb⟩ := (Formalism.GradedWeylDivisibility.sSBasis ℂ n n (lam τ).natW).choose_spec.2 (j τ)
  have hb' : ssB ℂ (lam τ).natW (j τ) = Formalism.GradedWeylDivisibility.bideterminant ℂ sz hsz I := hb
  show Formalism.GradedWeylDivisibility.blockEmb ℂ τ (ssB ℂ (lam τ).natW (j τ)) ∈ _
  rw [hb']
  have hB : Formalism.GradedWeylDivisibility.bideterminant ℂ sz hsz I ∈ algPol (Fin n × Fin n) := by
    unfold Formalism.GradedWeylDivisibility.bideterminant Formalism.GradedWeylDivisibility.initMinor
    exact prod_mem fun k _ => det_mem _ fun p q => X_mem _
  obtain ⟨q, hq⟩ := hB
  exact ⟨Formalism.GradedWeylDivisibility.blockEmb _ τ q, by rw [← hq]; exact map_rename _ _ _⟩

variable {ι : Type} [Fintype ι] {a b : ℕ}

/- English proof (translation)
The claim follows from `det_mem _ fun _ _ => X_mem _`.
-/
theorem frDet_mem (τ : ι) : frDet ℂ a τ ∈ algPol (ι × Fin a × Fin a) :=
  det_mem _ fun _ _ => X_mem _

/- English proof (translation)
Unfold `subD`. Use `aeval_mem hP _ fun v => ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `sum_mem fun β _ => mul_mem (X_mem _) (X_mem _)`. Conclude with `zero_mem _`.
-/
theorem subD_mem {P : Pol ℂ ι a} (hP : P ∈ algPol (ι × Fin a × Fin a)) :
    subD ℂ ι a b P ∈ algPol ((ι × Fin b × Fin b) ⊕ DVar ι a b) := by
  unfold subD
  refine aeval_mem hP _ fun v => ?_
  split_ifs
  · exact sum_mem fun β _ => mul_mem (X_mem _) (X_mem _)
  · exact zero_mem _

/- English proof (translation)
Establish `h1 : (monomial m c : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ) = c • basisMonomials _ ℂ m`. Rewrite using `[coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[h1, map_smul, jetLin, Module.Basis.constr_basis, smul_monomial, smul_eq_mul]`.
-/
theorem jetLin_monomial (J : (DVar ι a b →₀ ℕ) → ℂ) (m : (ι × Fin b × Fin b) ⊕ DVar ι a b →₀ ℕ) (c : ℂ) :
    jetLin J (monomial m c) =
      monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn) (c * J (m.comapDomain Sum.inr Sum.inr_injective.injOn)) := by
  have h1 : (monomial m c : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ) = c • basisMonomials _ ℂ m := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [h1, map_smul, jetLin, Module.Basis.constr_basis, smul_monomial, smul_eq_mul]

/- English proof (translation)
Rewrite using `[p.as_sum, map_sum]`. Use `sum_mem fun m _ => ?_` and prove the remaining obligations. Rewrite using `[jetLin_monomial]`. Conclude with `monomial_mem _ ((coeff_isAlgebraic hp m).mul (hJ _))`.
-/
theorem jetLin_mem (J : (DVar ι a b →₀ ℕ) → ℂ) (hJ : ∀ m, IsAlgebraic ℚ (J m))
    {p : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ} (hp : p ∈ algPol _) :
    jetLin J p ∈ algPol (ι × Fin b × Fin b) := by
  rw [p.as_sum, map_sum]
  refine sum_mem fun m _ => ?_
  rw [jetLin_monomial]
  exact monomial_mem _ ((coeff_isAlgebraic hp m).mul (hJ _))

/- English proof (translation)
Unfold `jetMap`. Simplify using `only [LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply]`. Use `jetLin_mem J hJ (subD_mem (mul_mem hP (prod_mem fun τ _ => pow_mem (frDet_mem τ) _)))` and prove the remaining obligations.
-/
theorem jetMap_mem (J : (DVar ι a b →₀ ℕ) → ℂ) (hJ : ∀ m, IsAlgebraic ℚ (J m)) (nn : ι → ℕ)
    {P : Pol ℂ ι a} (hP : P ∈ algPol (ι × Fin a × Fin a)) :
    jetMap J nn P ∈ algPol (ι × Fin b × Fin b) := by
  unfold jetMap
  simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply]
  refine jetLin_mem J hJ (subD_mem (mul_mem hP (prod_mem fun τ _ => pow_mem (frDet_mem τ) _)))

/- English proof (translation)
Use `set A := algebraicClosure ℚ ℂ`. Take `⟨pr, hpr⟩` from `LinearMap.exists_leftInverse_of_injective (Algebra.linearMap A ℂ) (LinearMap.ker_eq_bot.2 (algebraMap A ℂ).injective)`. Establish `hp : ∀ c : A, pr (algebraMap A ℂ c) = c` using `fun c => LinearMap.congr_fun hpr c`. Establish `key : ∑ k, x k • v k = ∑ k, (algebraMap A ℂ (pr (x k))) • v k`. Use extensionality with `m`.

Establish `hcoef : ∀ k, ∃ c : A, (v k).coeff m = algebraMap A ℂ c` using `fun k => by`. Take `⟨q, hq⟩` from `hvA k`. Conclude with `⟨q.coeff m, by rw [← hq, coeff_map]⟩`. Use `choose c hc using hcoef`. Take `⟨q, hq⟩` from `hQ`.

Establish `h1 : (∑ k, x k • v k).coeff m = algebraMap A ℂ (pr ((∑ k, x k • v k).coeff m))`. Rewrite using `[← hq, coeff_map, hp]`. Rewrite using `[h1]`. Simplify using `only [coeff_sum, coeff_smul, smul_eq_mul, hc, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Establish `: x k * algebraMap A ℂ (c k) = c k • x k` using `by rw [Algebra.smul_def, mul_comm]`. Rewrite using `[this, map_smul, smul_eq_mul, map_mul, mul_comm]`. Establish `h0` using `Fintype.linearIndependent_iff.1 hv (fun k => x k - algebraMap A ℂ (pr (x k))) (by simp only [sub_smul, Finset.sum_sub_distrib, key, sub_self]) k`. Rewrite using `[sub_eq_zero.1 h0]`. Conclude with `mem_algebraicClosure_iff.1 (pr (x k)).2`.
-/
theorem descent {σ κ : Type} [Fintype κ] (v : κ → MvPolynomial σ ℂ) (hv : LinearIndependent ℂ v)
    (hvA : ∀ k, v k ∈ algPol σ) (x : κ → ℂ) (hQ : ∑ k, x k • v k ∈ algPol σ) (k : κ) :
    IsAlgebraic ℚ (x k) := by
  set A := algebraicClosure ℚ ℂ
  obtain ⟨pr, hpr⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap A ℂ)
    (LinearMap.ker_eq_bot.2 (algebraMap A ℂ).injective)
  have hp : ∀ c : A, pr (algebraMap A ℂ c) = c := fun c => LinearMap.congr_fun hpr c
  have key : ∑ k, x k • v k = ∑ k, (algebraMap A ℂ (pr (x k))) • v k := by
    ext m
    have hcoef : ∀ k, ∃ c : A, (v k).coeff m = algebraMap A ℂ c := fun k => by
      obtain ⟨q, hq⟩ := hvA k
      exact ⟨q.coeff m, by rw [← hq, coeff_map]⟩
    choose c hc using hcoef
    obtain ⟨q, hq⟩ := hQ
    have h1 : (∑ k, x k • v k).coeff m = algebraMap A ℂ (pr ((∑ k, x k • v k).coeff m)) := by
      rw [← hq, coeff_map, hp]
    rw [h1]
    simp only [coeff_sum, coeff_smul, smul_eq_mul, hc, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : x k * algebraMap A ℂ (c k) = c k • x k := by rw [Algebra.smul_def, mul_comm]
    rw [this, map_smul, smul_eq_mul, map_mul, mul_comm]
  have h0 := Fintype.linearIndependent_iff.1 hv (fun k => x k - algebraMap A ℂ (pr (x k)))
    (by simp only [sub_smul, Finset.sum_sub_distrib, key, sub_self]) k
  rw [sub_eq_zero.1 h0]
  exact mem_algebraicClosure_iff.1 (pr (x k)).2

/- English proof (translation)
Introduce `ι _ a b lam lam' J nn hJ hV i j`. Establish `hQV : jetMap J nn (bVVfun ℂ lam j) ∈ VV ℂ lam'` using `hV J _ (by rw [← bVV_coe]; exact (bVV ℂ lam j).2)`. Establish `hop : jetOp lam lam' J nn (bVV ℂ lam j) = ⟨_, hQV⟩`. Simplify using `only [jetOp, retrVV, LinearMap.comp_apply, Submodule.subtype_apply, bVV_coe]`. Conclude with `Submodule.projectionOnto_apply_left _ ⟨_, hQV⟩`.

Rewrite using `[hop]`. Establish `hsum : jetMap J nn (bVVfun ℂ lam j) = ∑ k, (bVV ℂ lam').repr ⟨_, hQV⟩ k • bVVfun ℂ lam' k`. Use `congrArg Subtype.val ((bVV ℂ lam').sum_repr ⟨_, hQV⟩)` as an intermediate fact. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, bVV_coe] at this`. Conclude with `this.symm`.

Use `descent (bVVfun ℂ lam') (bVVfun_spec ℂ lam').1 (bVVfun_mem lam') _ ?_ i` and prove the remaining obligations. Rewrite using `[← hsum]`. Conclude with `jetMap_mem J hJ nn (bVVfun_mem lam j)`.
-/
theorem repr_jetOp_isAlgebraic : ∀ {ι : Type} [Fintype ι] {a b : ℕ} (lam : ι → Formalism.BasicNotions.DomWeight a)
    (lam' : ι → Formalism.BasicNotions.DomWeight b) (J : (DVar ι a b →₀ ℕ) → ℂ) (nn : ι → ℕ), (∀ m, IsAlgebraic ℚ (J m)) →
    JetInVV ℂ lam lam' nn → ∀ (i : Formalism.L2.DIV.VVIdx lam') (j : Formalism.L2.DIV.VVIdx lam),
    IsAlgebraic ℚ ((Formalism.L2.DIV.bVV ℂ lam').repr (jetOp lam lam' J nn (Formalism.L2.DIV.bVV ℂ lam j)) i) := by
  intro ι _ a b lam lam' J nn hJ hV i j
  have hQV : jetMap J nn (bVVfun ℂ lam j) ∈ VV ℂ lam' :=
    hV J _ (by rw [← bVV_coe]; exact (bVV ℂ lam j).2)
  have hop : jetOp lam lam' J nn (bVV ℂ lam j) = ⟨_, hQV⟩ := by
    simp only [jetOp, retrVV, LinearMap.comp_apply, Submodule.subtype_apply, bVV_coe]
    exact Submodule.projectionOnto_apply_left _ ⟨_, hQV⟩
  rw [hop]
  have hsum : jetMap J nn (bVVfun ℂ lam j) =
      ∑ k, (bVV ℂ lam').repr ⟨_, hQV⟩ k • bVVfun ℂ lam' k := by
    have := congrArg Subtype.val ((bVV ℂ lam').sum_repr ⟨_, hQV⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, bVV_coe] at this
    exact this.symm
  refine descent (bVVfun ℂ lam') (bVVfun_spec ℂ lam').1 (bVVfun_mem lam') _ ?_ i
  rw [← hsum]
  exact jetMap_mem J hJ nn (bVVfun_mem lam j)

end GlobalTheory.JetAlg
