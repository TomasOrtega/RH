import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupDualTangentLinearKillsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstFormalGroupLawNatMultipleEqCoboundarySum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPowerSeriesFamilyToFractionsFormalGroupLawNat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapAlgebraMapPowerSeriesEvalTwoGroups
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffSubstOfForallConstantCoeffZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffPowerSeriesEvalTwoGroupsMemIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvMemIdealSmulAddP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstEqZeroOfDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualBasisCoordMemMaximalIdealOfForallApply
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TangentIndep

/- English proof (translation)
The claim follows from `_root_.GlobalTheory.QLog.subst_nmul_eq R d μ hμ g n`.
-/
theorem subst_nmul_eq (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (g : MvPowerSeries (Fin d) R) (n : ℕ) :
    subst (nmul μ n) g = C (constantCoeff g) + (n : R) • g +
      ∑ k ∈ Finset.range n, at2 (cob1 μ g) (nmul μ k) (fun i => X i) := _root_.GlobalTheory.QLog.subst_nmul_eq R d μ hμ g n

/- English proof (translation)
The claim follows from `_root_.GlobalTheory.QLog.up_nmul R S d μ hμ n`.
-/
theorem up_nmul_eq (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) :
    up S (nmul μ n) = nmul (up S μ) n := _root_.GlobalTheory.QLog.up_nmul R S d μ hμ n

/- English proof (translation)
The claim follows from `_root_.GlobalTheory.QLog.map_algebraMap_powerSeriesEvalTwoGroups R S d τ t u v hu hv`.
-/
theorem map_at2_eq (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (d : ℕ) (τ : Type)
    (t : MvPowerSeries (Fin d ⊕ Fin d) R) (u v : Fin d → MvPowerSeries τ R)
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    map (algebraMap R S) (at2 t u v) = at2 (map (algebraMap R S) t) (up S u) (up S v) := _root_.GlobalTheory.QLog.map_algebraMap_powerSeriesEvalTwoGroups R S d τ t u v hu hv

/- English proof (translation)
The claim follows from `_root_.GlobalTheory.constantCoeff_subst_of_constantCoeff_zero R σ τ a ha g`.
-/
theorem constantCoeff_subst_eq (R : Type) [CommRing R] (σ τ : Type) [Finite σ] (a : σ → MvPowerSeries τ R)
    (ha : ∀ i, constantCoeff (a i) = 0) (g : MvPowerSeries σ R) :
    constantCoeff (subst a g) = constantCoeff g := _root_.GlobalTheory.constantCoeff_subst_of_constantCoeff_zero R σ τ a ha g

/- English proof (translation)
The claim follows from `_root_.GlobalTheory.IdealAt2.coeff_powerSeriesEvalTwoGroups_mem_ideal R d τ I t u v hu hv ht α`.
-/
theorem coeff_powerSeriesEvalTwoGroups_mem_ideal (R : Type) [CommRing R] (d : ℕ) (τ : Type) (I : Ideal R)
    (t : MvPowerSeries (Fin d ⊕ Fin d) R) (u v : Fin d → MvPowerSeries τ R)
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    (ht : ∀ α, coeff α t ∈ I) (α : τ →₀ ℕ) : coeff α (at2 t u v) ∈ I := _root_.GlobalTheory.IdealAt2.coeff_powerSeriesEvalTwoGroups_mem_ideal R d τ I t u v hu hv ht α

/- English proof (translation)
The claim follows from `_root_.GlobalTheory.Chart.ev_mem_ideal_smul_add_p p O G d c n I h hh`.
-/
theorem ev_mem_smul_add (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d)
    (n : ℕ) (I : Ideal O) (h : MvPowerSeries (Fin d) O) (hh : ∀ α, coeff α h ∈ I) :
    ∃ a ∈ I • (⊤ : Submodule O (G.A n)), ∃ b : G.A n, c.ev n h = a + (p : G.A n) * b := _root_.GlobalTheory.Chart.ev_mem_ideal_smul_add_p p O G d c n I h hh

/- English proof (translation)
The claim follows from `_root_.GlobalTheory.EvMul.ev_subst_nmul p O G d c n k h`.
-/
theorem ev_subst_nmul (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O]
    (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (n k : ℕ) (h : MvPowerSeries (Fin d) O) :
    c.ev n (subst (nmul c.μ k) h) = PDiv.mulBy O (G.A n) k (c.ev n h) := _root_.GlobalTheory.EvMul.ev_subst_nmul p O G d c n k h

/- English proof (translation)
The claim follows from `_root_.GlobalTheory.dualBasis_coord_mem_maximalIdeal O M k lb l hl j`.
-/
theorem repr_mem_maximalIdeal (O : Type) [CommRing O] [IsLocalRing O] (M : Type) [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] (k : ℕ) (lb : Module.Basis (Fin k) O (Module.Dual O M))
    (l : Module.Dual O M) (hl : ∀ w, l w ∈ IsLocalRing.maximalIdeal O) (j : Fin k) :
    lb.repr l j ∈ IsLocalRing.maximalIdeal O := _root_.GlobalTheory.dualBasis_coord_mem_maximalIdeal O M k lb l hl j

/- English proof (translation)
Proceed by induction on `k generalizing i with`. Consider the case `zero => simp [nmul]`. Consider the case `succ k ih`. Establish `h : nmul μ (k + 1) = op μ (nmul μ k) (fun i => X i)`. Simplify using `only [nmul]`.

Rewrite using `[Function.iterate_succ_apply']`. Rewrite using `[h, op, at2, constantCoeff_subst_eq R _ _ _ (fun x => by cases x with | inl a => exact ih a | inr a => simp), hμ]`.
-/
theorem nmul_const (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (k : ℕ) (i : Fin d) : constantCoeff (nmul μ k i) = 0 := by
  induction k generalizing i with
  | zero => simp [nmul]
  | succ k ih =>
    have h : nmul μ (k + 1) = op μ (nmul μ k) (fun i => X i) := by
      simp only [nmul]; rw [Function.iterate_succ_apply']
    rw [h, op, at2, constantCoeff_subst_eq R _ _ _ (fun x => by cases x with | inl a => exact ih a | inr a => simp), hμ]

/- English proof (translation)
Unfold `at2`. Conclude with `subst_add (hasSubst_of_constantCoeff_zero fun x => by cases x with | inl i => exact hu i | inr i => exact hv i) a b`.
-/
theorem powerSeriesEvalTwoGroups_add (R : Type) [CommRing R] (d : ℕ) (τ : Type) (a b : MvPowerSeries (Fin d ⊕ Fin d) R)
    (u v : Fin d → MvPowerSeries τ R)
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    at2 (a + b) u v = at2 a u v + at2 b u v := by
  unfold at2
  exact subst_add (hasSubst_of_constantCoeff_zero fun x => by cases x with | inl i => exact hu i | inr i => exact hv i) a b

/- English proof (translation)
Simplify using `only [cob1, inL, inR, map_sub]`. Rewrite using `[constantCoeff_subst_eq R _ _ _ hμ, constantCoeff_subst_eq R _ _ _ (fun _ => constantCoeff_X _), constantCoeff_subst_eq R _ _ _ (fun _ => constantCoeff_X _)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem constantCoeff_formalGroupLawCoboundaryOne (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (g : MvPowerSeries (Fin d) R) :
    constantCoeff (cob1 μ g) = - constantCoeff g := by
  simp only [cob1, inL, inR, map_sub]
  rw [constantCoeff_subst_eq R _ _ _ hμ, constantCoeff_subst_eq R _ _ _ (fun _ => constantCoeff_X _), constantCoeff_subst_eq R _ _ _ (fun _ => constantCoeff_X _)]
  ring

/- English proof (translation)
Establish `hμE : ∀ i, constantCoeff (up E μ i) = 0` using `fun i => by simp [up, hμ]`. Use `⟨?_, fun i => ?_, fun α => ?_⟩` and prove the remaining obligations. Simplify using `[hf.1, hg.1]`. Take `⟨x, -, hx⟩` from `hf.2.1 i`. Take `⟨y, -, hy⟩` from `hg.2.1 i`.

Use `⟨x + a * y, trivial, ?_⟩` and prove the remaining obligations. Simplify using `only [lin] at hx hy ⊢`. Rewrite using `[map_add, coeff_smul, hx, hy, map_add, map_mul]`. Take `⟨x, -, hx⟩` from `hf.2.2 α`. Take `⟨y, -, hy⟩` from `hg.2.2 α`.

Use `⟨x + a * y, trivial, ?_⟩` and prove the remaining obligations. Rewrite using `[formalCoboundary_add hμE, formalCoboundary_smul hμE, map_add, coeff_smul, hx, hy, map_add, map_mul]`.
-/
theorem QL_comb (O E : Type) [CommRing O] [CommRing E] [Algebra O E] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (f g : MvPowerSeries (Fin d) E) (a : O) (hf : QL μ ⊤ f) (hg : QL μ ⊤ g) :
    QL μ ⊤ (f + algebraMap O E a • g) := by
  have hμE : ∀ i, constantCoeff (up E μ i) = 0 := fun i => by simp [up, hμ]
  refine ⟨?_, fun i => ?_, fun α => ?_⟩
  · simp [hf.1, hg.1]
  · obtain ⟨x, -, hx⟩ := hf.2.1 i
    obtain ⟨y, -, hy⟩ := hg.2.1 i
    refine ⟨x + a * y, trivial, ?_⟩
    simp only [lin] at hx hy ⊢
    rw [map_add, coeff_smul, hx, hy, map_add, map_mul]
  · obtain ⟨x, -, hx⟩ := hf.2.2 α
    obtain ⟨y, -, hy⟩ := hg.2.2 α
    refine ⟨x + a * y, trivial, ?_⟩
    rw [formalCoboundary_add hμE, formalCoboundary_smul hμE, map_add, coeff_smul, hx, hy, map_add, map_mul]

/- English proof (translation)
Introduce `p _ K _ _ _ v O _ _ _ _ _ hv G d c E _ _ hF k e lb hQL hLie hlog b s hH j`. Use `haveI : ValuationRing O := ValuationRing.of_integers v hv`. Establish `hmem : ∀ o : O, o ∈ IsLocalRing.maximalIdeal O ↔ ¬IsUnit o` using `fun o => IsLocalRing.mem_maximalIdeal o`. Establish `hpm : (p : O) ∈ IsLocalRing.maximalIdeal O` using `(hmem _).2 Fact.out`. Establish `hμ : ∀ i, constantCoeff (c.μ i) = 0` using `c.isLaw.const`.

Set `f` to `comb (Sum.elim 0 b) e`. Set `l : G.dual.Lie` to `∑ j, b j • lb j`. Establish `lin : ∀ (f g : MvPowerSeries (Fin d) E) (l l' : G.dual.Lie) (a : O), c.IsLie f l → c.IsLie g l' → QL c.μ ⊤ f → QL c.μ ⊤ g → c.IsLie (f + algebraMap O E a • g) (l + a • l')` using `fun f g l l' a hf hg => (_root_.GlobalTheory.LieLin.main p K v O hv G d c E hF f g l l' a hf hg).1`. Establish `h00 : c.IsLie (0 : MvPowerSeries (Fin d) E) 0`. Use `lin _ _ _ _ (-1) (hLie j) (hLie j) (hQL _) (hQL _)` as an intermediate fact.

Simplify using `using this`. Establish `hsum : ∀ S : Finset (Fin k), QL c.μ ⊤ (∑ i ∈ S, algebraMap O E (b i) • e (Sum.inr i)) ∧ c.IsLie (∑ i ∈ S, algebraMap O E (b i) • e (Sum.inr i)) (∑ i ∈ S, b i • lb i)`. Introduce `S`. Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty`.

Use `⟨?_, by simpa using h00⟩` and prove the remaining obligations. Simplify using `using QL_comb O E d c.μ hμ _ _ (-1) (hQL (Sum.inr j)) (hQL (Sum.inr j))`. Consider the case `insert a S ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, add_comm, add_comm (b a • lb a)]`. Conclude with `⟨QL_comb O E d c.μ hμ _ _ (b a) ih.1 (hQL _), lin _ _ _ _ (b a) ih.2 (hLie a) ih.1 (hQL _)⟩`.

Establish `hf_eq : f = ∑ i, algebraMap O E (b i) • e (Sum.inr i)`. Simplify using `[f, comb, Fintype.sum_sum_type]`. Establish `hfl : c.IsLie f l` using `by rw [hf_eq]; exact (hsum Finset.univ).2`. Establish `hμE : ∀ i, constantCoeff (up E c.μ i) = 0` using `fun i => by simp [up, hμ]`. Use `choose t ht using hH`.

Set `T : MvPowerSeries (Fin d ⊕ Fin d) O` to `fun α => t α`. Establish `hT : ∀ α, coeff α T = t α` using `fun α => rfl`. Establish `hcob : cob1 (up E c.μ) f = map (algebraMap O E) (cob1 c.μ s + T)`. Use extensionality with `α`. Establish `h` using `(ht α).2`.

Rewrite `h` using `[map_sub, sub_eq_iff_eq_add]`. Rewrite using `[map_add, map_add, h]`. Simplify using `only [coeff_map, hT]`. Expand and normalize the polynomial expressions, which then agree. Establish `hf0 : constantCoeff f = algebraMap O E (constantCoeff s - t 0)`.

Establish `h` using `(ht 0).2`. Rewrite `h` using `[coeff_zero_eq_constantCoeff_apply, map_sub, constantCoeff_formalGroupLawCoboundaryOne E d _ hμE, constantCoeff_map, constantCoeff_formalGroupLawCoboundaryOne O d _ hμ]`. Rewrite using `[map_sub, ← h, map_neg]`. Expand and normalize the polynomial expressions, which then agree. Establish `hnc` using `nmul_const O d c.μ hμ`.

Set `s' : MvPowerSeries (Fin d) O` to `-C (constantCoeff s - t 0) - ∑ k ∈ Finset.range p, at2 (cob1 c.μ s + T) (nmul c.μ k) (fun i => X i)`. Establish `hX : up E (fun i : Fin d => (X i : MvPowerSeries (Fin d) O)) = fun i => X i`. Use function extensionality and compare the values at `i`. Simplify using `[up, map_X]`. Establish `hs' : map (algebraMap O E) s' = defect c.μ (p ^ 1) f`.

Rewrite using `[defect, pow_one, up_nmul_eq O E d c.μ hμ, subst_nmul_eq E d _ hμE f p, hcob, hf0]`. Simplify using `only [s', map_sub, map_neg, map_sum, map_C]`. Rewrite using `[Finset.sum_congr rfl (fun k _ => map_at2_eq O E d (Fin d) _ _ _ (hnc k) (fun i => constantCoeff_X i))]`. Simplify using `only [hX, up_nmul_eq O E d c.μ hμ]`. Normalize the expressions using the abelian group laws.

Establish `hs'2 : s' = C (t 0) + (p : O) • s - subst (nmul c.μ p) s - ∑ k ∈ Finset.range p, at2 T (nmul c.μ k) (fun i => X i)`. Rewrite using `[subst_nmul_eq O d c.μ hμ s p]`. Simplify using `only [s']`. Rewrite using `[Finset.sum_congr rfl (fun k _ => powerSeriesEvalTwoGroups_add O d (Fin d) _ _ _ _ (hnc k) (fun i => constantCoeff_X i)), Finset.sum_add_distrib, map_sub]`. Normalize the expressions using the abelian group laws.

Establish `key : ∀ w : G.dual.omega, l w ∈ IsLocalRing.maximalIdeal O`. Introduce `w`. Take `⟨φ₀, hφ₀⟩` from `AugCot.d_surjective _ (w.1 1)`. Use `set φ : CartierDual O (G.A 1) := φ₀ - algebraMap O _ (Coalgebra.counit (R := O) φ₀) with hφdef`. Establish `hφd : PDiv.dUnit O φ = w.1 1`.

Rewrite using `[hφdef, PDiv.dUnit, map_sub, AugCot.d_algebraMap, sub_zero]`. Conclude with `hφ₀`. Establish `hφ1 : φ 1 = 0`. Rewrite using `[hφdef]`. Simplify using `[Algebra.algebraMap_eq_smul_one, CartierDual.counit_apply]`.

Establish `hL` using `hfl.2 1 w φ s' hφd hs'`. Establish `hA : ∀ r : O, φ (algebraMap O (G.A 1) r) = 0` using `fun r => by`. Rewrite using `[Algebra.algebraMap_eq_smul_one, map_smul, hφ1, smul_zero]`. Establish `hev : φ (c.ev 1 s') ∈ IsLocalRing.maximalIdeal O`. Establish `h1` using `G.mulBy_pow_self 1 (c.ev 1 s)`.

Rewrite `h1` using `[pow_one]`. Establish `hC : c.ev 1 (C (t 0)) = algebraMap O _ (t 0)` using `(c.ev 1).commutes (t 0)`. Rewrite using `[hs'2]`. Simplify using `only [map_sub, map_add, map_smul, map_sum, ev_subst_nmul p O G d c 1 p s, h1, hC]`. Establish `hA' : ∀ r : O, φ.ofConv (algebraMap O (G.A 1) r) = 0` using `hA`.

Rewrite using `[hA', hA', zero_add, sub_zero, smul_eq_mul]`. Use `Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hpm) (Ideal.sum_mem _ fun k _ => ?_)` and prove the remaining obligations. Take `⟨a, ha, b', hb'⟩` from `ev_mem_smul_add p O G d c 1 (IsLocalRing.maximalIdeal O) _ (coeff_powerSeriesEvalTwoGroups_mem_ideal O d (Fin d) _ T _ _ (hnc k) (fun i => constantCoeff_X i) (fun α => (hmem _).2 (ht α).1))`. Rewrite using `[hb', map_add]`. Use `Ideal.add_mem _ ?_ ?_` and prove the remaining obligations.

Establish `hle : IsLocalRing.maximalIdeal O • (⊤ : Submodule O (G.A 1)) ≤ Submodule.comap φ.ofConv (IsLocalRing.maximalIdeal O)` using `Submodule.smul_le.2 fun r hr x _ => by`. Rewrite using `[Submodule.mem_comap, map_smul, smul_eq_mul]`. Conclude with `Ideal.mul_mem_right _ _ hr`. Conclude with `hle ha`. Rewrite using `[← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]`.

Conclude with `Ideal.mul_mem_right _ _ hpm`. Take `⟨q, hq⟩` from `hL`. Establish `: l w = (p : O) ^ 1 * q + φ (c.ev 1 s')` using `by rw [← hq]; ring`. Rewrite using `[this]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_right _ _ (by simpa using hpm)) hev`.

Take `⟨hfin, hproj⟩` from `GlobalTheory.PDiv.omega_finite_projective p K v O hv G.dual`. Establish `h6` using `repr_mem_maximalIdeal O G.dual.omega k lb l key j`. Establish `hrep : lb.repr l j = b j`. Establish `: l = lb.equivFun.symm b` using `by rw [Module.Basis.equivFun_symm_apply]`. Rewrite using `[← Module.Basis.equivFun_apply, this, LinearEquiv.apply_symm_apply]`.

Rewrite `h6` using `[hrep]`. Conclude with `(hmem _).1 h6`.
-/
theorem tangent_coords_nonunit : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) E) (lb : Module.Basis (Fin k) O G.dual.Lie), (∀ i, QL c.μ ⊤ (e i)) → (∀ j, c.IsLie (e (Sum.inr j)) (lb j)) → (∀ i, cob1 (up E c.μ) (e (Sum.inl i)) = 0) → ∀ (b : Fin k → O) (s : MvPowerSeries (Fin d) O), (∀ α, ∃ o : O, ¬IsUnit o ∧ coeff α (cob1 (up E c.μ) (comb (Sum.elim 0 b) e) - map (algebraMap O E) (cob1 c.μ s)) = algebraMap O E o) → ∀ j, ¬IsUnit (b j) := by
  intro p _ K _ _ _ v O _ _ _ _ _ hv G d c E _ _ hF k e lb hQL hLie hlog b s hH j
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  have hmem : ∀ o : O, o ∈ IsLocalRing.maximalIdeal O ↔ ¬IsUnit o := fun o => IsLocalRing.mem_maximalIdeal o
  have hpm : (p : O) ∈ IsLocalRing.maximalIdeal O := (hmem _).2 Fact.out
  have hμ : ∀ i, constantCoeff (c.μ i) = 0 := c.isLaw.const
  let f := comb (Sum.elim 0 b) e
  let l : G.dual.Lie := ∑ j, b j • lb j
  have lin : ∀ (f g : MvPowerSeries (Fin d) E) (l l' : G.dual.Lie) (a : O), c.IsLie f l → c.IsLie g l' →
      QL c.μ ⊤ f → QL c.μ ⊤ g → c.IsLie (f + algebraMap O E a • g) (l + a • l') :=
    fun f g l l' a hf hg => (_root_.GlobalTheory.LieLin.main p K v O hv G d c E hF f g l l' a hf hg).1
  have h00 : c.IsLie (0 : MvPowerSeries (Fin d) E) 0 := by
    have := lin _ _ _ _ (-1) (hLie j) (hLie j) (hQL _) (hQL _)
    simpa using this
  have hsum : ∀ S : Finset (Fin k), QL c.μ ⊤ (∑ i ∈ S, algebraMap O E (b i) • e (Sum.inr i)) ∧
      c.IsLie (∑ i ∈ S, algebraMap O E (b i) • e (Sum.inr i)) (∑ i ∈ S, b i • lb i) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      refine ⟨?_, by simpa using h00⟩
      simpa using QL_comb O E d c.μ hμ _ _ (-1) (hQL (Sum.inr j)) (hQL (Sum.inr j))
    | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, add_comm, add_comm (b a • lb a)]
      exact ⟨QL_comb O E d c.μ hμ _ _ (b a) ih.1 (hQL _), lin _ _ _ _ (b a) ih.2 (hLie a) ih.1 (hQL _)⟩
  have hf_eq : f = ∑ i, algebraMap O E (b i) • e (Sum.inr i) := by
    simp [f, comb, Fintype.sum_sum_type]
  have hfl : c.IsLie f l := by rw [hf_eq]; exact (hsum Finset.univ).2

  have hμE : ∀ i, constantCoeff (up E c.μ i) = 0 := fun i => by simp [up, hμ]
  choose t ht using hH
  let T : MvPowerSeries (Fin d ⊕ Fin d) O := fun α => t α
  have hT : ∀ α, coeff α T = t α := fun α => rfl
  have hcob : cob1 (up E c.μ) f = map (algebraMap O E) (cob1 c.μ s + T) := by
    ext α
    have h := (ht α).2
    rw [map_sub, sub_eq_iff_eq_add] at h
    rw [map_add, map_add, h]
    simp only [coeff_map, hT]
    ring
  have hf0 : constantCoeff f = algebraMap O E (constantCoeff s - t 0) := by
    have h := (ht 0).2
    rw [coeff_zero_eq_constantCoeff_apply, map_sub, constantCoeff_formalGroupLawCoboundaryOne E d _ hμE, constantCoeff_map,
      constantCoeff_formalGroupLawCoboundaryOne O d _ hμ] at h
    rw [map_sub, ← h, map_neg]; ring
  have hnc := nmul_const O d c.μ hμ
  let s' : MvPowerSeries (Fin d) O := -C (constantCoeff s - t 0) -
    ∑ k ∈ Finset.range p, at2 (cob1 c.μ s + T) (nmul c.μ k) (fun i => X i)
  have hX : up E (fun i : Fin d => (X i : MvPowerSeries (Fin d) O)) = fun i => X i := by
    funext i; simp [up, map_X]
  have hs' : map (algebraMap O E) s' = defect c.μ (p ^ 1) f := by
    rw [defect, pow_one, up_nmul_eq O E d c.μ hμ, subst_nmul_eq E d _ hμE f p, hcob, hf0]
    simp only [s', map_sub, map_neg, map_sum, map_C]
    rw [Finset.sum_congr rfl (fun k _ => map_at2_eq O E d (Fin d) _ _ _ (hnc k) (fun i => constantCoeff_X i))]
    simp only [hX, up_nmul_eq O E d c.μ hμ]
    abel
  have hs'2 : s' = C (t 0) + (p : O) • s - subst (nmul c.μ p) s -
      ∑ k ∈ Finset.range p, at2 T (nmul c.μ k) (fun i => X i) := by
    rw [subst_nmul_eq O d c.μ hμ s p]
    simp only [s']
    rw [Finset.sum_congr rfl (fun k _ => powerSeriesEvalTwoGroups_add O d (Fin d) _ _ _ _ (hnc k) (fun i => constantCoeff_X i)),
      Finset.sum_add_distrib, map_sub]
    abel
  have key : ∀ w : G.dual.omega, l w ∈ IsLocalRing.maximalIdeal O := by
    intro w
    obtain ⟨φ₀, hφ₀⟩ := AugCot.d_surjective _ (w.1 1)
    set φ : CartierDual O (G.A 1) := φ₀ - algebraMap O _ (Coalgebra.counit (R := O) φ₀) with hφdef
    have hφd : PDiv.dUnit O φ = w.1 1 := by
      rw [hφdef, PDiv.dUnit, map_sub, AugCot.d_algebraMap, sub_zero]; exact hφ₀
    have hφ1 : φ 1 = 0 := by
      rw [hφdef]
      simp [Algebra.algebraMap_eq_smul_one, CartierDual.counit_apply]

    have hL := hfl.2 1 w φ s' hφd hs'
    have hA : ∀ r : O, φ (algebraMap O (G.A 1) r) = 0 := fun r => by
      rw [Algebra.algebraMap_eq_smul_one, map_smul, hφ1, smul_zero]
    have hev : φ (c.ev 1 s') ∈ IsLocalRing.maximalIdeal O := by
      have h1 := G.mulBy_pow_self 1 (c.ev 1 s)
      rw [pow_one] at h1
      have hC : c.ev 1 (C (t 0)) = algebraMap O _ (t 0) := (c.ev 1).commutes (t 0)
      rw [hs'2]
      simp only [map_sub, map_add, map_smul, map_sum, ev_subst_nmul p O G d c 1 p s, h1, hC]
      have hA' : ∀ r : O, φ.ofConv (algebraMap O (G.A 1) r) = 0 := hA
      rw [hA', hA', zero_add, sub_zero, smul_eq_mul]
      refine Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hpm) (Ideal.sum_mem _ fun k _ => ?_)
      obtain ⟨a, ha, b', hb'⟩ := ev_mem_smul_add p O G d c 1 (IsLocalRing.maximalIdeal O) _
        (coeff_powerSeriesEvalTwoGroups_mem_ideal O d (Fin d) _ T _ _ (hnc k) (fun i => constantCoeff_X i) (fun α => (hmem _).2 (ht α).1))
      rw [hb', map_add]
      refine Ideal.add_mem _ ?_ ?_
      · have hle : IsLocalRing.maximalIdeal O • (⊤ : Submodule O (G.A 1)) ≤
            Submodule.comap φ.ofConv (IsLocalRing.maximalIdeal O) :=
          Submodule.smul_le.2 fun r hr x _ => by
            rw [Submodule.mem_comap, map_smul, smul_eq_mul]
            exact Ideal.mul_mem_right _ _ hr
        exact hle ha
      · rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
        exact Ideal.mul_mem_right _ _ hpm
    obtain ⟨q, hq⟩ := hL
    have : l w = (p : O) ^ 1 * q + φ (c.ev 1 s') := by rw [← hq]; ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (by simpa using hpm)) hev
  obtain ⟨hfin, hproj⟩ := GlobalTheory.PDiv.omega_finite_projective p K v O hv G.dual
  have h6 := repr_mem_maximalIdeal O G.dual.omega k lb l key j
  have hrep : lb.repr l j = b j := by
    have : l = lb.equivFun.symm b := by rw [Module.Basis.equivFun_symm_apply]
    rw [← Module.Basis.equivFun_apply, this, LinearEquiv.apply_symm_apply]
  rw [hrep] at h6
  exact (hmem _).1 h6

end GlobalTheory.TangentIndep
