import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicValuationThetaKernelJetBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetKapIff
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.BvvInt

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section
open Formalism.L2.Ker MvPolynomial

private noncomputable abbrev zPol (σ : Type) : Subring (MvPolynomial σ ℂ) :=
  (MvPolynomial.map (Int.castRingHom ℂ)).range

/- English proof (translation)
Assemble the required witnesses or components as `⟨X v, map_X _ _⟩`.
-/
private theorem zX_mem {σ : Type} (v : σ) : (X v : MvPolynomial σ ℂ) ∈ zPol σ := ⟨X v, map_X _ _⟩

/- English proof (translation)
Take `⟨q, rfl⟩` from `RingHom.mem_range.mp hp`. Conclude with `⟨q.coeff m, by simp [MvPolynomial.coeff_map]⟩`.
-/
private theorem zcoeff {σ : Type} {p : MvPolynomial σ ℂ} (hp : p ∈ zPol σ) (m : σ →₀ ℕ) :
    ∃ z : ℤ, p.coeff m = (z : ℂ) := by
  obtain ⟨q, rfl⟩ := RingHom.mem_range.mp hp
  exact ⟨q.coeff m, by simp [MvPolynomial.coeff_map]⟩

/- English proof (translation)
Use `choose M' hM' using fun p q => RingHom.mem_range.mp (h p q)`. Use `RingHom.mem_range.mpr ⟨(Matrix.of M').det, ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.map_det]`. Use `congr 1`. Use `Matrix.ext fun p q => ?_` and prove the remaining obligations.

Simplify using `using hM' p q`.
-/
private theorem zdet_mem {σ : Type} {s : ℕ} (M : Matrix (Fin s) (Fin s) (MvPolynomial σ ℂ))
    (h : ∀ p q, M p q ∈ zPol σ) : M.det ∈ zPol σ := by
  choose M' hM' using fun p q => RingHom.mem_range.mp (h p q)
  refine RingHom.mem_range.mpr ⟨(Matrix.of M').det, ?_⟩
  rw [RingHom.map_det]
  congr 1
  refine Matrix.ext fun p q => ?_
  simpa using hM' p q

/- English proof (translation)
Take `⟨q, rfl⟩` from `RingHom.mem_range.mp hp`. Use `clear hp`. Proceed by induction on `q using MvPolynomial.induction_on with`. Consider the case `C z`. Use `RingHom.mem_range.mpr ⟨C z, ?_⟩` and prove the remaining obligations.

Simplify using `[MvPolynomial.algebraMap_eq]`. Consider the case `add p q hp' hq'`. Rewrite using `[map_add, map_add]`. Conclude with `add_mem hp' hq'`. Consider the case `mul_X p v hp'`.

Rewrite using `[map_mul, map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X]`. Conclude with `mul_mem hp' (hg v)`.
-/
private theorem zaeval_mem {σ τ : Type} {p : MvPolynomial σ ℂ} (hp : p ∈ zPol σ) (g : σ → MvPolynomial τ ℂ)
    (hg : ∀ v, g v ∈ zPol τ) : aeval g p ∈ zPol τ := by
  obtain ⟨q, rfl⟩ := RingHom.mem_range.mp hp
  clear hp
  induction q using MvPolynomial.induction_on with
  | C z =>
    refine RingHom.mem_range.mpr ⟨C z, ?_⟩
    simp [MvPolynomial.algebraMap_eq]
  | add p q hp' hq' =>
    rw [map_add, map_add]
    exact add_mem hp' hq'
  | mul_X p v hp' =>
    rw [map_mul, map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X]
    exact mul_mem hp' (hg v)

variable {ι : Type} [Fintype ι] {a b : ℕ}

/- English proof (translation)
Unfold `subD`. Use `zaeval_mem hP _ fun v => ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `sum_mem fun β _ => mul_mem (zX_mem _) (zX_mem _)`. Conclude with `zero_mem _`.
-/
private theorem zsubD_mem {P : Pol ℂ ι a} (hP : P ∈ zPol (ι × Fin a × Fin a)) :
    subD ℂ ι a b P ∈ zPol ((ι × Fin b × Fin b) ⊕ DVar ι a b) := by
  unfold subD
  refine zaeval_mem hP _ fun v => ?_
  split_ifs
  · exact sum_mem fun β _ => mul_mem (zX_mem _) (zX_mem _)
  · exact zero_mem _

/- English proof (translation)
Establish `e : (monomial m c : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ) = c • (basisMonomials _ ℂ) m`. Rewrite using `[MvPolynomial.coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[e, map_smul]`. Simplify using `only [jetLin, Module.Basis.constr_basis, smul_monomial, smul_eq_mul]`.
-/
private theorem jetLin_mono (J : (DVar ι a b →₀ ℕ) → ℂ) (m : (ι × Fin b × Fin b) ⊕ DVar ι a b →₀ ℕ) (c : ℂ) :
    jetLin J (monomial m c) =
      monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn) (c * J (m.comapDomain Sum.inr Sum.inr_injective.injOn)) := by
  have e : (monomial m c : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ) =
      c • (basisMonomials _ ℂ) m := by
    rw [MvPolynomial.coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_smul]
  simp only [jetLin, Module.Basis.constr_basis, smul_monomial, smul_eq_mul]

open Classical in
/- English proof (translation)
Rewrite using `[p.as_sum, map_sum]`. Use `sum_mem fun μ _ => ?_` and prove the remaining obligations. Rewrite using `[jetLin_mono]`. Take `⟨z, hz⟩` from `zcoeff hp μ`. Use `RingHom.mem_range.mpr ⟨monomial (μ.comapDomain Sum.inl Sum.inl_injective.injOn) (z * if μ.comapDomain Sum.inr Sum.inr_injective.injOn = k then 1 else 0), ?_⟩` and prove the remaining obligations.

Rewrite using `[MvPolynomial.map_monomial, hz]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem jetLin_zmem (k : DVar ι a b →₀ ℕ)
    {p : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ} (hp : p ∈ zPol _) :
    jetLin (fun m => if m = k then (1 : ℂ) else 0) p ∈ zPol (ι × Fin b × Fin b) := by
  rw [p.as_sum, map_sum]
  refine sum_mem fun μ _ => ?_
  rw [jetLin_mono]
  obtain ⟨z, hz⟩ := zcoeff hp μ
  refine RingHom.mem_range.mpr ⟨monomial (μ.comapDomain Sum.inl Sum.inl_injective.injOn)
    (z * if μ.comapDomain Sum.inr Sum.inr_injective.injOn = k then 1 else 0), ?_⟩
  rw [MvPolynomial.map_monomial, hz]
  split_ifs <;> simp

open Classical in
/- English proof (translation)
Establish `hsplit : ∀ J' : (DVar ι a b →₀ ℕ) → ℂ, jetLin J' p = ∑ μ ∈ p.support, monomial (μ.comapDomain Sum.inl Sum.inl_injective.injOn) (coeff μ p * J' (μ.comapDomain Sum.inr Sum.inr_injective.injOn))`. Introduce `J'`. Use `conv_lhs => rw [p.as_sum]`. Rewrite using `[map_sum]`. Simplify using `only [jetLin_mono]`.

Use `⟨p.support.image (fun μ => μ.comapDomain Sum.inr Sum.inr_injective.injOn), fun J => ?_⟩` and prove the remaining obligations. Rewrite using `[hsplit J]`. Simplify using `only [hsplit, Finset.smul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun μ hμ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_eq_single (μ.comapDomain Sum.inr Sum.inr_injective.injOn)]`. Simplify using `[smul_monomial, mul_comm]`. Introduce `k _ hk`. Simplify using `[Ne.symm hk]`. Introduce `h`.

Conclude with `absurd (Finset.mem_image_of_mem _ hμ) h`.
-/
private theorem jetLin_split (p : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ) :
    ∃ S : Finset (DVar ι a b →₀ ℕ), ∀ J : (DVar ι a b →₀ ℕ) → ℂ,
      jetLin J p = ∑ k ∈ S, J k • jetLin (fun m => if m = k then (1 : ℂ) else 0) p := by
  have hsplit : ∀ J' : (DVar ι a b →₀ ℕ) → ℂ, jetLin J' p = ∑ μ ∈ p.support,
      monomial (μ.comapDomain Sum.inl Sum.inl_injective.injOn)
        (coeff μ p * J' (μ.comapDomain Sum.inr Sum.inr_injective.injOn)) := by
    intro J'
    conv_lhs => rw [p.as_sum]
    rw [map_sum]
    simp only [jetLin_mono]
  refine ⟨p.support.image (fun μ => μ.comapDomain Sum.inr Sum.inr_injective.injOn), fun J => ?_⟩
  rw [hsplit J]
  simp only [hsplit, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [Finset.sum_eq_single (μ.comapDomain Sum.inr Sum.inr_injective.injOn)]
  · simp [smul_monomial, mul_comm]
  · intro k _ hk
    simp [Ne.symm hk]
  · intro h
    exact absurd (Finset.mem_image_of_mem _ hμ) h

end

/- English proof (translation)
Introduce `ι _ a b lam lam' n hV j i`. Take `⟨P, hP⟩ : ∃ P, P = bVVfun ℂ lam j` from `⟨_, rfl⟩`. Establish `hPmem : P ∈ VV ℂ lam`. Rewrite using `[hP, ← bVV_coe]`. Conclude with `((bVV ℂ lam) j).2`.

Establish `hPz : P ∈ zPol (ι × Fin a × Fin a)`. Take `⟨Q, hQ⟩` from `bVVfun_int ℂ lam j`. Rewrite using `[hP]`. Conclude with `RingHom.mem_range.mpr ⟨Q, hQ.symm⟩`. Establish `hdet : ∀ τ, Formalism.L2.Ker.frDet ℂ a τ ∈ zPol (ι × Fin a × Fin a)` using `fun τ => zdet_mem _ (fun p q => zX_mem _)`.

Establish `hsh : P * ∏ τ, Formalism.L2.Ker.frDet ℂ a τ ^ n τ ∈ zPol (ι × Fin a × Fin a)` using `mul_mem hPz (prod_mem fun τ _ => pow_mem (hdet τ) _)`. Take `⟨Q, hQ⟩ : ∃ Q, Q = Formalism.L2.Ker.subD ℂ ι a b (P * ∏ τ, Formalism.L2.Ker.frDet ℂ a τ ^ n τ)` from `⟨_, rfl⟩`. Establish `hQz : Q ∈ zPol _`. Rewrite using `[hQ]`. Conclude with `zsubD_mem hsh`.

Establish `hJQ : ∀ J, Formalism.L2.Ker.jetMap J n P = Formalism.L2.Ker.jetLin J Q`. Introduce `J`. Rewrite using `[hQ]`. Both sides reduce to the same expression. Take `⟨S, hS⟩` from `jetLin_split Q`.

Establish `hint : ∀ k, ∃ z : ℤ, (bVV ℂ lam').repr ⟨Formalism.L2.Ker.jetMap (fun m => if m = k then (1 : ℂ) else 0) n P, hV _ P hPmem⟩ i = z`. Introduce `k`. Apply `UpperTheory.WildA.bvvInt` to reduce the goal to its premises. Introduce `m`. Apply `zcoeff` to reduce the goal to its premises.

Use `show Formalism.L2.Ker.jetMap (fun m => if m = k then (1 : ℂ) else 0) n P ∈ _`. Rewrite using `[hJQ]`. Conclude with `jetLin_zmem k hQz`. Use `choose z hz using hint`. Use `⟨∑ k ∈ S, Finsupp.single k (z k), fun J => ?_⟩` and prove the remaining obligations.

Establish `hop : Formalism.L2.Ker.jetOp lam lam' J n (bVV ℂ lam j) = ⟨Formalism.L2.Ker.jetMap J n P, hV J P hPmem⟩` using `by show Formalism.L2.Ker.retrVV ℂ lam' (Formalism.L2.Ker.jetMap J n ((bVV ℂ lam j : Pol ℂ ι a))) = _`. Establish `hb : ((bVV ℂ lam j : Pol ℂ ι a)) = P` using `by rw [bVV_coe, hP]`. Rewrite using `[hb]`. Conclude with `Submodule.projectionOnto_apply_left _ ⟨_, hV J P hPmem⟩`. Establish `hsum : (⟨Formalism.L2.Ker.jetMap J n P, hV J P hPmem⟩ : VV ℂ lam') = ∑ k ∈ S, J k • (⟨Formalism.L2.Ker.jetMap (fun m => if m = k then (1 : ℂ) else 0) n P, hV _ P hPmem⟩ : VV ℂ lam')`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul, hJQ]`. Conclude with `hS J`. Rewrite using `[hop, hsum, map_sum, Finsupp.finset_sum_apply]`.

Simplify using `only [map_smul, Finsupp.smul_apply, smul_eq_mul, hz]`. Rewrite using `[← Finsupp.sum_finset_sum_index (by simp) (by intros; push_cast; ring)]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.sum_single_index (by simp), mul_comm]`.
-/
theorem UpperTheory.WildA.jetInt :
    ∀ {ι : Type} [Fintype ι] {a b : ℕ} (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ),
      Formalism.L2.Ker.JetInVV ℂ lam lam' n → ∀ (j : VVIdx lam) (i : VVIdx lam'),
      ∃ c : (Formalism.L2.Ker.DVar ι a b →₀ ℕ) →₀ ℤ, ∀ J : (Formalism.L2.Ker.DVar ι a b →₀ ℕ) → ℂ,
        (bVV ℂ lam').repr (Formalism.L2.Ker.jetOp lam lam' J n (bVV ℂ lam j)) i = c.sum fun m z => (z : ℂ) * J m := by
  intro ι _ a b lam lam' n hV j i
  classical
  obtain ⟨P, hP⟩ : ∃ P, P = bVVfun ℂ lam j := ⟨_, rfl⟩
  have hPmem : P ∈ VV ℂ lam := by
    rw [hP, ← bVV_coe]
    exact ((bVV ℂ lam) j).2
  have hPz : P ∈ zPol (ι × Fin a × Fin a) := by
    obtain ⟨Q, hQ⟩ := bVVfun_int ℂ lam j
    rw [hP]
    exact RingHom.mem_range.mpr ⟨Q, hQ.symm⟩
  have hdet : ∀ τ, Formalism.L2.Ker.frDet ℂ a τ ∈ zPol (ι × Fin a × Fin a) := fun τ =>
    zdet_mem _ (fun p q => zX_mem _)
  have hsh : P * ∏ τ, Formalism.L2.Ker.frDet ℂ a τ ^ n τ ∈ zPol (ι × Fin a × Fin a) :=
    mul_mem hPz (prod_mem fun τ _ => pow_mem (hdet τ) _)
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = Formalism.L2.Ker.subD ℂ ι a b (P * ∏ τ, Formalism.L2.Ker.frDet ℂ a τ ^ n τ) := ⟨_, rfl⟩
  have hQz : Q ∈ zPol _ := by
    rw [hQ]
    exact zsubD_mem hsh
  have hJQ : ∀ J, Formalism.L2.Ker.jetMap J n P = Formalism.L2.Ker.jetLin J Q := by
    intro J
    rw [hQ]
    rfl
  obtain ⟨S, hS⟩ := jetLin_split Q
  have hint : ∀ k, ∃ z : ℤ, (bVV ℂ lam').repr
      ⟨Formalism.L2.Ker.jetMap (fun m => if m = k then (1 : ℂ) else 0) n P, hV _ P hPmem⟩ i = z := by
    intro k
    apply UpperTheory.WildA.bvvInt
    intro m
    apply zcoeff
    show Formalism.L2.Ker.jetMap (fun m => if m = k then (1 : ℂ) else 0) n P ∈ _
    rw [hJQ]
    exact jetLin_zmem k hQz
  choose z hz using hint
  refine ⟨∑ k ∈ S, Finsupp.single k (z k), fun J => ?_⟩
  have hop : Formalism.L2.Ker.jetOp lam lam' J n (bVV ℂ lam j) = ⟨Formalism.L2.Ker.jetMap J n P, hV J P hPmem⟩ := by
    show Formalism.L2.Ker.retrVV ℂ lam' (Formalism.L2.Ker.jetMap J n ((bVV ℂ lam j : Pol ℂ ι a))) = _
    have hb : ((bVV ℂ lam j : Pol ℂ ι a)) = P := by rw [bVV_coe, hP]
    rw [hb]
    exact Submodule.projectionOnto_apply_left _ ⟨_, hV J P hPmem⟩
  have hsum : (⟨Formalism.L2.Ker.jetMap J n P, hV J P hPmem⟩ : VV ℂ lam') =
      ∑ k ∈ S, J k • (⟨Formalism.L2.Ker.jetMap (fun m => if m = k then (1 : ℂ) else 0) n P, hV _ P hPmem⟩ : VV ℂ lam') := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul, hJQ]
    exact hS J
  rw [hop, hsum, map_sum, Finsupp.finset_sum_apply]
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, hz]
  rw [← Finsupp.sum_finset_sum_index (by simp) (by intros; push_cast; ring)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finsupp.sum_single_index (by simp), mul_comm]
