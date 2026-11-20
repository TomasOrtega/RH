import Mathlib
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleDistinctUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenericDetPowMulHw
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyDirectSumEquivOfFinrankLe
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSemisimpleRepresentationTprodOfIsIrreducibleAl

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open Formalism.REAL (fockF)
open scoped DirectSum TensorProduct Kronecker Matrix

noncomputable section

namespace GlobalTheory.GLDuality.Compl

/- English proof (translation)
Use `(totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)` and prove the remaining obligations. Use `(totalDegree_mul _ _).trans ?_` and prove the remaining obligations. Rewrite using `[totalDegree_C, zero_add]`. Conclude with `(totalDegree_X j).le`.
-/
private theorem totalDegree_sum_C_mul_X_le_one {σ : Type} [Fintype σ] (A : Matrix σ σ ℂ) (i : σ) :
    (∑ j, C (A i j) * X j : MvPolynomial σ ℂ).totalDegree ≤ 1 := by
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  exact (totalDegree_X j).le

/- English proof (translation)
Use `conv_lhs => rw [P.as_sum, map_sum]`. Use `(totalDegree_finsetSum _ _).trans (Finset.sup_le fun m hm => ?_)` and prove the remaining obligations. Rewrite using `[sub, aeval_monomial, algebraMap_eq]`. Use `(totalDegree_mul _ _).trans ?_` and prove the remaining obligations. Rewrite using `[totalDegree_C, zero_add, Finsupp.prod]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem totalDegree_linSub_le {σ : Type} [Fintype σ] (A : Matrix σ σ ℂ) (P : MvPolynomial σ ℂ) :
    (sub A P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum, map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun m hm => ?_)
  rw [sub, aeval_monomial, algebraMap_eq]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add, Finsupp.prod]
  calc _ ≤ ∑ i ∈ m.support, ((∑ j, C (A i j) * X j : MvPolynomial σ ℂ) ^ m i).totalDegree :=
        totalDegree_finsetProd _ _
    _ ≤ ∑ i ∈ m.support, m i := Finset.sum_le_sum fun i _ =>
        (totalDegree_pow _ _).trans
          ((Nat.mul_le_mul_left (m i) (totalDegree_sum_C_mul_X_le_one A i)).trans (le_of_eq (mul_one _)))
    _ ≤ P.totalDegree := le_totalDegree hm

def fockLin {σ : Type} (g : MvPolynomial σ ℂ) : MvPolynomial σ ℂ →ₗ[ℂ] ℂ where
  toFun f := fockF f g
  map_add' _ _ := Formalism.REAL.fischerInner_add_left _ _ _
  map_smul' c f := by
    rw [smul_eq_C_mul, LFocks_C_mul_left]
    rfl

def orth {σ : Type} (K : Submodule ℂ (MvPolynomial σ ℂ)) : Submodule ℂ (MvPolynomial σ ℂ) :=
  ⨅ m : K, LinearMap.ker (fockLin (m : MvPolynomial σ ℂ))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h m hm`. Conclude with `LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 h ⟨m, hm⟩)`. Introduce `h`. Conclude with `(Submodule.mem_iInf _).2 fun m => LinearMap.mem_ker.2 (h m m.2)`.
-/
theorem mem_orth {σ : Type} {K : Submodule ℂ (MvPolynomial σ ℂ)} {v : MvPolynomial σ ℂ} :
    v ∈ orth K ↔ ∀ m ∈ K, fockF v m = 0 := by
  constructor
  · intro h m hm
    exact LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 h ⟨m, hm⟩)
  · intro h
    exact (Submodule.mem_iInf _).2 fun m => LinearMap.mem_ker.2 (h m m.2)

/- English proof (translation)
Rewrite using `[Formalism.REAL.fischerInner_sum_right]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_eq_C_mul, Formalism.GradedWeylDivisibility.LFocks_C_mul_right]`.
-/
private theorem fockF_sum_smul_right {σ ι : Type} (s : Finset ι) (c : ι → ℂ) (b : ι → MvPolynomial σ ℂ)
    (v : MvPolynomial σ ℂ) :
    fockF v (∑ i ∈ s, c i • b i) = ∑ i ∈ s, star (c i) * fockF v (b i) := by
  rw [Formalism.REAL.fischerInner_sum_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_C_mul, Formalism.GradedWeylDivisibility.LFocks_C_mul_right]

/- English proof (translation)
Use `haveI : FiniteDimensional ℂ K := Submodule.finiteDimensional_of_le h.le`. Establish `hlt : Module.finrank ℂ K < Module.finrank ℂ U` using `Submodule.finrank_lt_finrank_of_lt h`. Set `b` to `Module.finBasis ℂ K`. Set `Φ : U →ₗ[ℂ] (Fin (Module.finrank ℂ K) → ℂ)` to `LinearMap.pi fun i => (fockLin ((b i : K) : MvPolynomial σ ℂ)).comp U.subtype`. Establish `hker : LinearMap.ker Φ ≠ ⊥`.

Introduce `hbot`. Establish `h1` using `LinearMap.finrank_range_add_finrank_ker Φ`. Rewrite `h1` using `[hbot, finrank_bot, add_zero]`. Establish `h2 : Module.finrank ℂ (LinearMap.range Φ) ≤ Module.finrank ℂ K`. Simplify using `using Submodule.finrank_le (LinearMap.range Φ)`.

Use linear arithmetic over natural numbers and integers. Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hker`. Introduce `hbot`. Apply `hx0` to reduce the goal to its premises. Establish `hmem : (x : MvPolynomial σ ℂ) ∈ U ⊓ orth K`.

Use `⟨x.2, mem_orth.2 fun m hm => ?_⟩` and prove the remaining obligations. Establish `hm' : m = ∑ i, (b.repr ⟨m, hm⟩ i) • ((b i : K) : MvPolynomial σ ℂ)`. Establish `e` using `congrArg Subtype.val (b.sum_repr ⟨m, hm⟩)`. Rewrite `e` using `[Submodule.coe_sum]`. Simplify `e.symm` using `only [Submodule.coe_smul]`.

Rewrite using `[hm', fockF_sum_smul_right]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Establish `h0 : fockF (x : MvPolynomial σ ℂ) ((b i : K) : MvPolynomial σ ℂ) = 0` using `congrFun (LinearMap.mem_ker.1 hx) i`. Rewrite using `[h0, mul_zero]`. Rewrite `hmem` using `[hbot]`.

Conclude with `Submodule.coe_eq_zero.1 ((Submodule.mem_bot ℂ).1 hmem)`.
-/
theorem inf_orth_ne_bot {σ : Type} (U K : Submodule ℂ (MvPolynomial σ ℂ)) [FiniteDimensional ℂ U] (h : K < U) :
    U ⊓ orth K ≠ ⊥ := by
  classical
  haveI : FiniteDimensional ℂ K := Submodule.finiteDimensional_of_le h.le
  have hlt : Module.finrank ℂ K < Module.finrank ℂ U := Submodule.finrank_lt_finrank_of_lt h
  let b := Module.finBasis ℂ K

  let Φ : U →ₗ[ℂ] (Fin (Module.finrank ℂ K) → ℂ) :=
    LinearMap.pi fun i => (fockLin ((b i : K) : MvPolynomial σ ℂ)).comp U.subtype
  have hker : LinearMap.ker Φ ≠ ⊥ := by
    intro hbot
    have h1 := LinearMap.finrank_range_add_finrank_ker Φ
    rw [hbot, finrank_bot, add_zero] at h1
    have h2 : Module.finrank ℂ (LinearMap.range Φ) ≤ Module.finrank ℂ K := by
      simpa using Submodule.finrank_le (LinearMap.range Φ)
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  intro hbot
  apply hx0
  have hmem : (x : MvPolynomial σ ℂ) ∈ U ⊓ orth K := by
    refine ⟨x.2, mem_orth.2 fun m hm => ?_⟩
    have hm' : m = ∑ i, (b.repr ⟨m, hm⟩ i) • ((b i : K) : MvPolynomial σ ℂ) := by
      have e := congrArg Subtype.val (b.sum_repr ⟨m, hm⟩)
      rw [Submodule.coe_sum] at e
      simpa only [Submodule.coe_smul] using e.symm
    rw [hm', fockF_sum_smul_right]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h0 : fockF (x : MvPolynomial σ ℂ) ((b i : K) : MvPolynomial σ ℂ) = 0 :=
      congrFun (LinearMap.mem_ker.1 hx) i
    rw [h0, mul_zero]
  rw [hbot] at hmem
  exact Submodule.coe_eq_zero.1 ((Submodule.mem_bot ℂ).1 hmem)

/- English proof (translation)
Establish `e : (((h : Matrix (Fin n') (Fin n') ℂ) ⊗ₖ (g : Matrix (Fin n) (Fin n) ℂ))ᵀ)ᴴ = (((star h : GL (Fin n') ℂ) : Matrix (Fin n') (Fin n') ℂ) ⊗ₖ ((star g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))ᵀ`. Rewrite using `[Units.coe_star, Units.coe_star, Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose, ← Matrix.conjTranspose_kronecker]`. Use extensionality with `a b`. Both sides reduce to the same expression. Rewrite using `[matRep_apply, matRep_apply, Formalism.GradedWeylDivisibility.fockSubAdj, e]`.
-/
theorem fockF_matRep {n n' : ℕ} (g : GL (Fin n) ℂ) (h : GL (Fin n') ℂ) (v m : MvPolynomial (Fin n' × Fin n) ℂ) :
    fockF (matRep n n' (g, h) v) m = fockF v (matRep n n' (star g, star h) m) := by
  have e : (((h : Matrix (Fin n') (Fin n') ℂ) ⊗ₖ (g : Matrix (Fin n) (Fin n) ℂ))ᵀ)ᴴ =
      (((star h : GL (Fin n') ℂ) : Matrix (Fin n') (Fin n') ℂ) ⊗ₖ
        ((star g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))ᵀ := by
    rw [Units.coe_star, Units.coe_star, Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose,
      ← Matrix.conjTranspose_kronecker]
    ext a b
    rfl
  rw [matRep_apply, matRep_apply, Formalism.GradedWeylDivisibility.fockSubAdj, e]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨p, hp⟩ : ∃ p, p ∉ M := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hM (eq_top_iff.2 fun x _ => hc x)`. Set `U` to `restrictTotalDegree (Fin n' × Fin n) ℂ p.totalDegree`.

Establish `hpU : p ∈ U` using `(mem_restrictTotalDegree _ _ _).2 le_rfl`. Establish `hdeg : ∀ (a : GL (Fin n) ℂ) (c : GL (Fin n') ℂ) (w : MvPolynomial (Fin n' × Fin n) ℂ), w ∈ U → matRep n n' (a, c) w ∈ U`. Introduce `a c w hw`. Rewrite `hw`, the goal using `[mem_restrictTotalDegree]`. Rewrite using `[matRep_apply]`.

Conclude with `(totalDegree_linSub_le _ _).trans hw`. Establish `hKU : M ⊓ U < U` using `lt_of_le_of_ne inf_le_right fun hEq => by`. Establish `hK : p ∈ M ⊓ U` using `by rw [hEq]; exact hpU`. Conclude with `hp hK.1`. Use `⟨U ⊓ orth (M ⊓ U), inf_orth_ne_bot U (M ⊓ U) hKU, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[eq_bot_iff]`. Introduce and unpack `v ⟨⟨hvU, hvO⟩, hvM⟩`. Rewrite using `[Submodule.mem_bot]`. Assume the negation of the conclusion as `hv0`. Establish `h0 : fockF v v = 0` using `mem_orth.1 hvO v ⟨hvM, hvU⟩`.

Establish `hpos` using `(Formalism.GradedWeylDivisibility.fockPos _ v hv0).1`. Rewrite `hpos` using `[h0, Complex.zero_re]`. Conclude with `lt_irrefl _ hpos`. Introduce and unpack `⟨a, c⟩ v ⟨hvU, hvO⟩`. Use `⟨hdeg a c v hvU, mem_orth.2 fun m hm => ?_⟩` and prove the remaining obligations.

Rewrite using `[fockF_matRep]`. Conclude with `mem_orth.1 hvO _ ⟨hst (star a, star c) m hm.1, hdeg _ _ m hm.2⟩`.
-/
theorem exists_stable_disjoint (n n' : ℕ) (M : Submodule ℂ (MvPolynomial (Fin n' × Fin n) ℂ)) (hM : M ≠ ⊤)
    (hst : ∀ p : GL (Fin n) ℂ × GL (Fin n') ℂ, ∀ v ∈ M, matRep n n' p v ∈ M) :
    ∃ N : Submodule ℂ (MvPolynomial (Fin n' × Fin n) ℂ), N ≠ ⊥ ∧ N ⊓ M = ⊥ ∧
      ∀ p : GL (Fin n) ℂ × GL (Fin n') ℂ, ∀ v ∈ N, matRep n n' p v ∈ N := by
  classical
  obtain ⟨p, hp⟩ : ∃ p, p ∉ M := by
    by_contra hc
    push_neg at hc
    exact hM (eq_top_iff.2 fun x _ => hc x)

  let U := restrictTotalDegree (Fin n' × Fin n) ℂ p.totalDegree
  have hpU : p ∈ U := (mem_restrictTotalDegree _ _ _).2 le_rfl
  have hdeg : ∀ (a : GL (Fin n) ℂ) (c : GL (Fin n') ℂ) (w : MvPolynomial (Fin n' × Fin n) ℂ),
      w ∈ U → matRep n n' (a, c) w ∈ U := by
    intro a c w hw
    rw [mem_restrictTotalDegree] at hw ⊢
    rw [matRep_apply]
    exact (totalDegree_linSub_le _ _).trans hw
  have hKU : M ⊓ U < U := lt_of_le_of_ne inf_le_right fun hEq => by
    have hK : p ∈ M ⊓ U := by rw [hEq]; exact hpU
    exact hp hK.1
  refine ⟨U ⊓ orth (M ⊓ U), inf_orth_ne_bot U (M ⊓ U) hKU, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro v ⟨⟨hvU, hvO⟩, hvM⟩
    rw [Submodule.mem_bot]
    by_contra hv0
    have h0 : fockF v v = 0 := mem_orth.1 hvO v ⟨hvM, hvU⟩
    have hpos := (Formalism.GradedWeylDivisibility.fockPos _ v hv0).1
    rw [h0, Complex.zero_re] at hpos
    exact lt_irrefl _ hpos
  · rintro ⟨a, c⟩ v ⟨hvU, hvO⟩
    refine ⟨hdeg a c v hvU, mem_orth.2 fun m hm => ?_⟩
    rw [fockF_matRep]
    exact mem_orth.1 hvO _ ⟨hst (star a, star c) m hm.1, hdeg _ _ m hm.2⟩

end GlobalTheory.GLDuality.Compl
