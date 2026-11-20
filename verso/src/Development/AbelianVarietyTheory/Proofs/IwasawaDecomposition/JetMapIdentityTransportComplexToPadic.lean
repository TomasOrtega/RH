import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.ThetaIsometryFactsHold
import Formalism.LocalRingCardinality.FactDelDualNabla
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DominantWeightPolynomialFunctionalMinorsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.JetTransport

open MvPolynomial Finsupp

variable {ι : Type} [Fintype ι] {a b : ℕ}

open Classical in

noncomputable def wD (ι : Type) (a b : ℕ) : ((ι × Fin b × Fin b) ⊕ DVar ι a b) → (ι → ℕ) :=
  Sum.elim 0 fun x => Pi.single x.1 1

open Classical in

noncomputable def wF (ι : Type) (a : ℕ) : (ι × Fin a × Fin a) → (ι → ℕ) := fun v => Pi.single v.1 1

/- English proof (translation)
Rewrite using `[weight_apply, Finsupp.sum_fintype _ _ (by intro; simp)]`. Simplify using `[wF, Finset.sum_apply, Pi.single_apply, Fintype.sum_prod_type]`. Rewrite using `[Fintype.sum_eq_single τ (fun x hx => by simp [Ne.symm hx])]`. Simplify using the standard rewrite rules.
-/
lemma weight_wF (e : (ι × Fin a × Fin a) →₀ ℕ) (τ : ι) :
    weight (wF ι a) e τ = ∑ α, ∑ s, e (τ, α, s) := by
  classical
  rw [weight_apply, Finsupp.sum_fintype _ _ (by intro; simp)]
  simp [wF, Finset.sum_apply, Pi.single_apply, Fintype.sum_prod_type]
  rw [Fintype.sum_eq_single τ (fun x hx => by simp [Ne.symm hx])]
  simp

/- English proof (translation)
Rewrite using `[weight_apply, Finsupp.sum_fintype _ _ (by intro; simp)]`. Simplify using `[wD, Finset.sum_apply, Pi.single_apply, Fintype.sum_prod_type, Fintype.sum_sum_type]`. Rewrite using `[Fintype.sum_eq_single τ (fun x hx => by simp [Ne.symm hx])]`. Simplify using the standard rewrite rules.
-/
lemma weight_wD (u : ((ι × Fin b × Fin b) ⊕ DVar ι a b) →₀ ℕ) (τ : ι) :
    weight (wD ι a b) u τ = ∑ β, ∑ α, u (Sum.inr (τ, β, α)) := by
  classical
  rw [weight_apply, Finsupp.sum_fintype _ _ (by intro; simp)]
  simp [wD, Finset.sum_apply, Pi.single_apply, Fintype.sum_prod_type, Fintype.sum_sum_type]
  rw [Fintype.sum_eq_single τ (fun x hx => by simp [Ne.symm hx])]
  simp

/- English proof (translation)
Simplify using `[jetMap]`.
-/
lemma jetMap_zero {K : Type} [Field K] (J : (DVar ι a b →₀ ℕ) → K) (P : Formalism.L2.DIV.Pol K ι a) :
    jetMap J (fun _ => 0) P = jetLin J (subD K ι a b P) := by
  simp [jetMap]

/- English proof (translation)
Establish `: (monomial u c : MvPolynomial _ K) = c • basisMonomials _ K u`. Rewrite using `[coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[this]`. Unfold `jetLin`. Rewrite using `[LinearMap.map_smul, Module.Basis.constr_basis, smul_monomial, smul_eq_mul]`.
-/
lemma jetLin_monomial {K : Type} [Field K] (J : (DVar ι a b →₀ ℕ) → K)
    (u : ((ι × Fin b × Fin b) ⊕ DVar ι a b) →₀ ℕ) (c : K) :
    jetLin J (monomial u c) = monomial (u.comapDomain Sum.inl Sum.inl_injective.injOn)
      (c * J (u.comapDomain Sum.inr Sum.inr_injective.injOn)) := by
  have : (monomial u c : MvPolynomial _ K) = c • basisMonomials _ K u := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [this]
  unfold jetLin
  rw [LinearMap.map_smul, Module.Basis.constr_basis, smul_monomial, smul_eq_mul]

/- English proof (translation)
Proceed by induction on `Q using MvPolynomial.induction_on' with`. Consider the case `monomial u c => simp [jetLin_monomial, map_monomial]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`.
-/
lemma jetLin_map {K K' : Type} [Field K] [Field K'] (f : K →+* K') (J : (DVar ι a b →₀ ℕ) → K)
    (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) :
    jetLin (f ∘ J) (map f Q) = map f (jetLin J Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial u c => simp [jetLin_monomial, map_monomial]
  | add p q hp hq => simp only [map_add, hp, hq]

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C c => simp [subD]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p v hp`. Rewrite using `[map_mul, map_X, map_mul, hp, map_mul, map_mul]`.

Use `congr 1`. Simplify using `only [subD, aeval_X]`. Apply the tactic sequence `split_ifs <;> simp [map_sum]`.
-/
lemma subD_map {K K' : Type} [Field K] [Field K'] (f : K →+* K') (P : Formalism.L2.DIV.Pol K ι a) :
    subD K' ι a b (map f P) = map f (subD K ι a b P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [subD]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, map_X, map_mul, hp, map_mul, map_mul]
    congr 1
    simp only [subD, aeval_X]
    split_ifs <;> simp [map_sum]

/- English proof (translation)
Simplify using `only [subD, aeval_X]`. Use `split_ifs with h`. Apply `IsWeightedHomogeneous.sum` to reduce the goal to its premises. Introduce `β _`. Use `(isWeightedHomogeneous_X K (wD ι a b) (Sum.inl (v.1, β, (⟨v.2.2.1, h⟩ : Fin b)))).mul (isWeightedHomogeneous_X K (wD ι a b) (Sum.inr (v.1, β, v.2.1)))` as an intermediate fact.

Simplify `this` using `[wD, wF]`. Conclude with `isWeightedHomogeneous_zero _ _ _`.
-/
lemma subD_X_hom {K : Type} [Field K] (v : ι × Fin a × Fin a) :
    IsWeightedHomogeneous (wD ι a b) (subD K ι a b (X v)) (wF ι a v) := by
  simp only [subD, aeval_X]
  split_ifs with h
  · apply IsWeightedHomogeneous.sum
    intro β _
    have := (isWeightedHomogeneous_X K (wD ι a b) (Sum.inl (v.1, β, (⟨v.2.2.1, h⟩ : Fin b)))).mul
      (isWeightedHomogeneous_X K (wD ι a b) (Sum.inr (v.1, β, v.2.1)))
    simpa [wD, wF] using this
  · exact isWeightedHomogeneous_zero _ _ _

/- English proof (translation)
Rewrite using `[P.as_sum, map_sum]`. Apply `IsWeightedHomogeneous.sum` to reduce the goal to its premises. Introduce `e he`. Establish `hw : weight (wF ι a) e = n` using `hP (MvPolynomial.mem_support_iff.mp he)`. Rewrite using `[subD, aeval_monomial, algebraMap_eq]`.

Apply `IsWeightedHomogeneous.C_mul` to reduce the goal to its premises. Rewrite using `[← hw, weight_apply]`. Apply `IsWeightedHomogeneous.prod` to reduce the goal to its premises. Introduce `v _`. Simplify `(subD_X_hom (b := b) (K := K) v).pow (e v)` using `only [subD, aeval_X]`.
-/
lemma subD_hom {K : Type} [Field K] (P : Formalism.L2.DIV.Pol K ι a) (n : ι → ℕ)
    (hP : IsWeightedHomogeneous (wF ι a) P n) :
    IsWeightedHomogeneous (wD ι a b) (subD K ι a b P) n := by
  rw [P.as_sum, map_sum]
  apply IsWeightedHomogeneous.sum
  intro e he
  have hw : weight (wF ι a) e = n := hP (MvPolynomial.mem_support_iff.mp he)
  rw [subD, aeval_monomial, algebraMap_eq]
  apply IsWeightedHomogeneous.C_mul
  rw [← hw, weight_apply]
  apply IsWeightedHomogeneous.prod
  intro v _
  simpa only [subD, aeval_X] using (subD_X_hom (b := b) (K := K) v).pow (e v)

/- English proof (translation)
Rewrite using `[Q.as_sum, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun u hu => ?_` and prove the remaining obligations. Rewrite using `[jetLin_monomial, jetLin_monomial, hJ]`. Introduce `τ`. Establish `hw` using `congrFun (hQ (MvPolynomial.mem_support_iff.mp hu)) τ`.

Rewrite `hw` using `[weight_wD]`. Simplify `hw` using `[Finsupp.comapDomain_apply]`.
-/
lemma jetLin_congr {K : Type} [Field K] (J₁ J₂ : (DVar ι a b →₀ ℕ) → K) (n : ι → ℕ)
    (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) (hQ : IsWeightedHomogeneous (wD ι a b) Q n)
    (hJ : ∀ m : DVar ι a b →₀ ℕ, (∀ τ, ∑ β, ∑ α, m (τ, β, α) = n τ) → J₁ m = J₂ m) :
    jetLin J₁ Q = jetLin J₂ Q := by
  rw [Q.as_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [jetLin_monomial, jetLin_monomial, hJ]
  intro τ
  have hw := congrFun (hQ (MvPolynomial.mem_support_iff.mp hu)) τ
  rw [weight_wD] at hw
  simpa [Finsupp.comapDomain_apply] using hw

end GlobalTheory.JetTransport

/- English proof (translation)
Introduce `D p _ lam a b J J' n r A P hJ hP h`. Set `x : (DVar D.what₂.Tau a b →₀ ℕ) → Qbar` to `fun m => if hm : ∀ τ, ∑ β, ∑ α, m (τ, β, α) = n τ then (hJ m hm).choose else 0`. Establish `hx1 : ∀ m : DVar D.what₂.Tau a b →₀ ℕ, (∀ τ, ∑ β, ∑ α, m (τ, β, α) = n τ) → J m = (algebraMap Qbar ℂ ∘ x) m`. Introduce `m hm`. Simplify using `only [x, Function.comp_apply, dif_pos hm]`.

Conclude with `(hJ m hm).choose_spec.1.symm`. Establish `hx2 : ∀ m : DVar D.what₂.Tau a b →₀ ℕ, (∀ τ, ∑ β, ∑ α, m (τ, β, α) = n τ) → J' m = (lam ∘ x) m`. Introduce `m hm`. Simplify using `only [x, Function.comp_apply, dif_pos hm]`. Conclude with `(hJ m hm).choose_spec.2.symm`.

Establish `hPw : ∀ {K : Type} [Field K] (f : Qbar →+* K), MvPolynomial.IsWeightedHomogeneous (GlobalTheory.JetTransport.wF D.what₂.Tau a) (MvPolynomial.map f P) n`. Introduce `K _ f d hd`. Use function extensionality and compare the values at `τ`. Rewrite using `[GlobalTheory.JetTransport.weight_wF]`. Use `hP d (MvPolynomial.mem_support_iff.mpr fun h0 => hd ?_) τ` and prove the remaining obligations.

Rewrite using `[MvPolynomial.coeff_map, h0, map_zero]`. Establish `key : ∀ {K : Type} [Field K] (f : Qbar →+* K) (JK : (DVar D.what₂.Tau a b →₀ ℕ) → K), (∀ m : DVar D.what₂.Tau a b →₀ ℕ, (∀ τ, ∑ β, ∑ α, m (τ, β, α) = n τ) → JK m = (f ∘ x) m) → jetMap JK (fun _ => 0) (MvPolynomial.map f P) = MvPolynomial.map f (jetMap x (fun _ => 0) P)`. Introduce `K _ f JK hJK`. Rewrite using `[GlobalTheory.JetTransport.jetMap_zero, GlobalTheory.JetTransport.jetMap_zero, ← GlobalTheory.JetTransport.jetLin_map, ← GlobalTheory.JetTransport.subD_map]`. Conclude with `GlobalTheory.JetTransport.jetLin_congr _ _ n _ (GlobalTheory.JetTransport.subD_hom _ n (hPw f)) hJK`.

Establish `hA : A = MvPolynomial.C r * jetMap x (fun _ => 0) P`. Apply `MvPolynomial.map_injective (algebraMap Qbar ℂ) (algebraMap Qbar ℂ).injective` to reduce the goal to its premises. Rewrite using `[h, key (algebraMap Qbar ℂ) J hx1, map_mul, MvPolynomial.map_C]`. Both sides reduce to the same expression. Rewrite using `[hA, map_mul, MvPolynomial.map_C, key lam J' hx2]`.
-/
theorem GlobalTheory.jetMapTransport : ∀ (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {a b : ℕ}
    (J : (DVar D.what₂.Tau a b →₀ ℕ) → ℂ) (J' : (DVar D.what₂.Tau a b →₀ ℕ) → ℂ_[p]) (n : D.what₂.Tau → ℕ) (r : Qbar)
    (A : MvPolynomial (GL3Theta.FrV D b) Qbar) (P : MvPolynomial (GL3Theta.FrV D a) Qbar)
    (hJ : ∀ m : DVar D.what₂.Tau a b →₀ ℕ, (∀ τ, ∑ β, ∑ α, m (τ, β, α) = n τ) → ∃ x : Qbar, (x : ℂ) = J m ∧ lam x = J' m)
    (hP : ∀ e ∈ P.support, ∀ τ, ∑ α, ∑ s, e (τ, α, s) = n τ)
    (h : MvPolynomial.map (algebraMap Qbar ℂ) A = MvPolynomial.C (r : ℂ) * jetMap J (fun _ => 0) (MvPolynomial.map (algebraMap Qbar ℂ) P)), MvPolynomial.map lam A = MvPolynomial.C (lam r) * jetMap J' (fun _ => 0) (MvPolynomial.map lam P) := by
  intro D p _ lam a b J J' n r A P hJ hP h
  classical
  let x : (DVar D.what₂.Tau a b →₀ ℕ) → Qbar := fun m =>
    if hm : ∀ τ, ∑ β, ∑ α, m (τ, β, α) = n τ then (hJ m hm).choose else 0
  have hx1 : ∀ m : DVar D.what₂.Tau a b →₀ ℕ, (∀ τ, ∑ β, ∑ α, m (τ, β, α) = n τ) →
      J m = (algebraMap Qbar ℂ ∘ x) m := by
    intro m hm
    simp only [x, Function.comp_apply, dif_pos hm]
    exact (hJ m hm).choose_spec.1.symm
  have hx2 : ∀ m : DVar D.what₂.Tau a b →₀ ℕ, (∀ τ, ∑ β, ∑ α, m (τ, β, α) = n τ) →
      J' m = (lam ∘ x) m := by
    intro m hm
    simp only [x, Function.comp_apply, dif_pos hm]
    exact (hJ m hm).choose_spec.2.symm
  have hPw : ∀ {K : Type} [Field K] (f : Qbar →+* K),
      MvPolynomial.IsWeightedHomogeneous (GlobalTheory.JetTransport.wF D.what₂.Tau a) (MvPolynomial.map f P) n := by
    intro K _ f d hd
    funext τ
    rw [GlobalTheory.JetTransport.weight_wF]
    refine hP d (MvPolynomial.mem_support_iff.mpr fun h0 => hd ?_) τ
    rw [MvPolynomial.coeff_map, h0, map_zero]
  have key : ∀ {K : Type} [Field K] (f : Qbar →+* K) (JK : (DVar D.what₂.Tau a b →₀ ℕ) → K),
      (∀ m : DVar D.what₂.Tau a b →₀ ℕ, (∀ τ, ∑ β, ∑ α, m (τ, β, α) = n τ) → JK m = (f ∘ x) m) →
      jetMap JK (fun _ => 0) (MvPolynomial.map f P) = MvPolynomial.map f (jetMap x (fun _ => 0) P) := by
    intro K _ f JK hJK
    rw [GlobalTheory.JetTransport.jetMap_zero, GlobalTheory.JetTransport.jetMap_zero, ← GlobalTheory.JetTransport.jetLin_map,
      ← GlobalTheory.JetTransport.subD_map]
    exact GlobalTheory.JetTransport.jetLin_congr _ _ n _ (GlobalTheory.JetTransport.subD_hom _ n (hPw f)) hJK
  have hA : A = MvPolynomial.C r * jetMap x (fun _ => 0) P := by
    apply MvPolynomial.map_injective (algebraMap Qbar ℂ) (algebraMap Qbar ℂ).injective
    rw [h, key (algebraMap Qbar ℂ) J hx1, map_mul, MvPolynomial.map_C]
    rfl
  rw [hA, map_mul, MvPolynomial.map_C, key lam J' hx2]
