import Mathlib
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Formalism.LocalRingCardinality.DataKerP
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.SharpRestriction.Divisibility.ZetaProductPairs
import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilOperatorVacuumExactConstantEvenRank
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterTrivialAtInertPrimes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitaryExtension
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsWeilOfVacuum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddEqOfEven
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSqMulGaussianLatticeTranslateEqShifted
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTwoTorsionCMPointAllConjugates
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaVacuaConjugatesCmPoints
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTaylorCoeffsAlgebraicAtComplexMultiplicatio
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicData
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorCoeffConjugateSeries
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilRepresentationCommHeisenbergIntertwiner
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaFunctionsAllLevelsClosure
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLocalComponentUnitaryMatrix
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTriv

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.TrueTheta

/- English proof (translation)
Use `letI := D.host.cmStar`. Introduce `γ`. Use `(mem_ratG_intG D n).2.2.1 _ ?_` and prove the remaining obligations. Use `Matrix.mem_unitaryGroup_iff.1 γ.2` as an intermediate fact. Use `this using 2` and compare the differences between its conclusion and the goal.

Use extensionality with `i j`. Simplify using `[Matrix.star_apply, AdLattice.star_eq_conj]`.
-/
theorem exists_rat {D : D7} {n : ℕ} : letI := D.host.cmStar
    ∀ γ : Matrix.unitaryGroup (Fin n) D.host.E, ∃ γA : GA D n,
      IsRat D (γA : GL (Fin n) (AE D)) (γ : Matrix (Fin n) (Fin n) D.host.E) := by
  letI := D.host.cmStar
  intro γ
  refine (mem_ratG_intG D n).2.2.1 _ ?_
  have := Matrix.mem_unitaryGroup_iff.1 γ.2
  convert this using 2
  ext i j
  simp [Matrix.star_apply, AdLattice.star_eq_conj]

/- English proof (translation)
Use `choose n hn hy using fun i => GlobalTheory.HeckeVal.exists_denom D (y i)`. Use `⟨∏ i, n i, Finset.prod_pos fun i _ => hn i, fun i => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩ : n i ∣ ∏ i, n i` from `Finset.dvd_prod_of_mem _ (Finset.mem_univ i)`. Rewrite using `[hc, Nat.cast_mul, mul_comm (n i : AE D), mul_assoc]`. Conclude with `mul_mem (natCast_mem _ c) (hy i)`.
-/
theorem fin_denom (D : D7) {ι : Type} [Fintype ι] (y : ι → AE D) : ∃ m : ℕ, 0 < m ∧ ∀ i, (m : AE D) * y i ∈ OhE D := by
  choose n hn hy using fun i => GlobalTheory.HeckeVal.exists_denom D (y i)
  refine ⟨∏ i, n i, Finset.prod_pos fun i _ => hn i, fun i => ?_⟩
  obtain ⟨c, hc⟩ : n i ∣ ∏ i, n i := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  rw [hc, Nat.cast_mul, mul_comm (n i : AE D), mul_assoc]
  exact mul_mem (natCast_mem _ c) (hy i)

/- English proof (translation)
Rewrite using `[← map_natCast (inc D), ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn.ne'), map_one]`.
-/
theorem inc_inv_nat (D : D7) {n : ℕ} (hn : 0 < n) : inc D (n : D.host.E)⁻¹ * (n : AE D) = 1 := by
  rw [← map_natCast (inc D), ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn.ne'), map_one]

/- English proof (translation)
Take `⟨n, hn, hy⟩` from `GlobalTheory.HeckeVal.exists_denom D y`. Take `⟨r, -, w, hw, e⟩` from `GlobalTheory.HeckeVal.exists_approx D (n * m) (Nat.mul_pos hn hm) _ hy`. Use `⟨(n : D.host.E)⁻¹ * r, -w, neg_mem hw, ?_⟩` and prove the remaining obligations. Establish `h` using `inc_inv_nat D hn`. Rewrite using `[map_mul]`.

Move the coercions through the operations in `at e`. Take the linear combination `(-inc D (n : D.host.E)⁻¹) * e + (y - m * w) * h`.
-/
theorem approx (D : D7) (y : AE D) {m : ℕ} (hm : 0 < m) : ∃ b : D.host.E, ∃ s ∈ OhE D, inc D b = y + (m : AE D) * s := by
  obtain ⟨n, hn, hy⟩ := GlobalTheory.HeckeVal.exists_denom D y
  obtain ⟨r, -, w, hw, e⟩ := GlobalTheory.HeckeVal.exists_approx D (n * m) (Nat.mul_pos hn hm) _ hy
  refine ⟨(n : D.host.E)⁻¹ * r, -w, neg_mem hw, ?_⟩
  have h := inc_inv_nat D hn
  rw [map_mul]
  push_cast at e
  linear_combination (-inc D (n : D.host.E)⁻¹) * e + (y - m * w) * h

/- English proof (translation)
Take `⟨k, hk, hu⟩` from `GlobalTheory.HeckeVal.exists_denom D ((u⁻¹ : (AE D)ˣ) : AE D)`. Take `⟨b, s, hs, e⟩` from `approx D (u * y) (Nat.mul_pos hm hk)`. Use `⟨b, _, mul_mem hu hs, ?_⟩` and prove the remaining obligations. Rewrite using `[e]`. Use `push_cast`.

Take the linear combination `y * u.inv_mul`.
-/
theorem approxU (D : D7) (u : (AE D)ˣ) (y : AE D) {m : ℕ} (hm : 0 < m) :
    ∃ b : D.host.E, ∃ s ∈ OhE D, ((u⁻¹ : (AE D)ˣ) : AE D) * inc D b = y + (m : AE D) * s := by
  obtain ⟨k, hk, hu⟩ := GlobalTheory.HeckeVal.exists_denom D ((u⁻¹ : (AE D)ˣ) : AE D)
  obtain ⟨b, s, hs, e⟩ := approx D (u * y) (Nat.mul_pos hm hk)
  refine ⟨b, _, mul_mem hu hs, ?_⟩
  rw [e]
  push_cast
  linear_combination y * u.inv_mul

/- English proof (translation)
Introduce `D N L hL`. Use `letI := D.host.cmStar`. Choose the witnesses or unpack the hypotheses as in `⟨m, hm2, hm⟩ : ∃ m : ℕ, 2 ≤ m ∧ ∀ x ∈ L, ∀ i, (m : AE D) * inc D (x i) ∈ OhE D := by`. Take `⟨S, hS⟩` from `hL.1`. Take `⟨m, h0, hm⟩` from `fin_denom D (fun p : S × Fin N => inc D ((p.1 : Fin N → D.host.E) p.2))`.

Use `⟨2 * m, by omega, fun x hx i => ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.cast_mul, mul_assoc]`. Use `mul_mem (natCast_mem _ 2) ?_` and prove the remaining obligations. Rewrite `hx` using `[← hS]`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x hx => exact hm (⟨x, hx⟩, i)`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [Pi.add_apply, map_add, mul_add]`. Conclude with `add_mem hx hy`. Consider the case `smul a x _ hx`.

Rewrite using `[Pi.smul_apply, Algebra.smul_def, map_mul, mul_left_comm]`. Conclude with `mul_mem (VacMove.inc_int D a) hx`. Take `⟨γ, s, hs, h1, -⟩` from `GlobalTheory.RepEqAt.repExS D m (by omega) N ⟨L, hL⟩ ⟨stdL D N, GlobalTheory.VacuumScalar.sd_of_moves (GlobalTheory.VacuumScalar.moves_one D N)⟩`. Establish `hs0 : 0 < s` using `Nat.pos_of_ne_zero (by rintro rfl; simp at hs; omega)`. Take `⟨hsep, hcpl⟩` from `GlobalTheory.IntAdeleComplete.integral_separated_complete D`.

Take `⟨f₀, hf₀, hff₀, ⟨w, hw, hfw⟩, h3⟩` from `GlobalTheory.IdealIdele.exists_idem (OhE D) hsep hcpl m (by omega)`. Take `⟨v, hv, hfv⟩` from `h3 s hs0 hs.symm`. Establish `hv'` using `congrArg (sgA D) hfv`. Rewrite `hv'` using `[map_sub, map_one, map_mul, map_natCast]`. Establish `hff' : sgA D f₀ * sgA D f₀ = sgA D f₀` using `by rw [← map_mul, hff₀]`.

Choose the witnesses or unpack the hypotheses as in `⟨e, he, hse, ⟨v₁, hv₁, e1⟩, w₁, hw₁, e2⟩ : ∃ e : AE D, e * e = e ∧ sgA D e = e ∧ (∃ v ∈ OhE D, e = (s : AE D) * v) ∧ ∃ w ∈ OhE D, 1 - e = (m : AE D) * w := by`. Use `⟨1 - f₀ * sgA D f₀, ?_, ?_, ⟨v + f₀ * sgA D v, add_mem hv (mul_mem hf₀ (VacMove.sgA_mem D hv)), ?_⟩, w * sgA D f₀, mul_mem hw (VacMove.sgA_mem D hf₀), ?_⟩` and prove the remaining obligations. Take the linear combination `(sgA D f₀ * sgA D f₀) * hff₀ + f₀ * hff'`. Rewrite using `[map_sub, map_one, map_mul, VacMove.sgA_sgA, mul_comm]`. Take the linear combination `hfv + f₀ * hv'`.

Take the linear combination `sgA D f₀ * hfw`. Take `⟨γA, hγ⟩` from `exists_rat γ`. Take `⟨M, hM⟩` from `GlobalTheory.VacuumScalar.exists_moves (GlobalTheory.VacuumScalar.cutG e he hse γA)⁻¹`. Establish `hMs` using `GlobalTheory.VacuumScalar.sd_of_moves hM`. Establish `hle : L ≤ M`.

Introduce `x hx`. Rewrite using `[hM x]`. Introduce `i`. Rewrite using `[Subgroup.coe_inv, inv_inv]`. Express the relevant statement in the definitionally equal form `((e • ((γA : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) + (1 - e) • 1).mulVec _) i ∈ _`.

Establish `hγ' : ((γA : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) = _` using `hγ`. Rewrite using `[Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hγ', Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, e2]`. Establish `t1` using `(RingHom.map_mulVec (inc D) (γ : Matrix (Fin N) (Fin N) D.host.E) x i).symm`. Establish `t2` using `(GlobalTheory.VacuumScalar.moves_one D N _).1 (h1 _ ⟨x, hx, rfl⟩) i`. Rewrite `t2` using `[OneMemClass.coe_one, inv_one, Units.val_one, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast]`.

Use `add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[e1, mul_comm (s : AE D), mul_assoc]`. Use `mul_mem hv₁ ?_` and prove the remaining obligations. Use `t2 using 2` and compare the differences between its conclusion and the goal. Conclude with `t1`.

Rewrite using `[mul_comm (m : AE D), mul_assoc]`. Conclude with `mul_mem hw₁ (hm x hx i)`. Establish `: L = M` using `le_antisymm hle fun y hy => (hL.2.2 y).2 fun x hx => (hMs.2.2 y).1 hy x (hle hx)`. Conclude with `⟨_, this ▸ hM⟩`.
-/
theorem exists_moves_of_selfDual : ∀ (D : D7) (N : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), SD D L → ∃ g : GA D N, Moves D (g : GL (Fin N) (AE D)) L := by
  intro D N L hL
  letI := D.host.cmStar
  obtain ⟨m, hm2, hm⟩ : ∃ m : ℕ, 2 ≤ m ∧ ∀ x ∈ L, ∀ i, (m : AE D) * inc D (x i) ∈ OhE D := by
    obtain ⟨S, hS⟩ := hL.1
    obtain ⟨m, h0, hm⟩ := fin_denom D (fun p : S × Fin N => inc D ((p.1 : Fin N → D.host.E) p.2))
    refine ⟨2 * m, by omega, fun x hx i => ?_⟩
    rw [Nat.cast_mul, mul_assoc]
    refine mul_mem (natCast_mem _ 2) ?_
    rw [← hS] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hm (⟨x, hx⟩, i)
    | zero => simp
    | add x y _ _ hx hy => rw [Pi.add_apply, map_add, mul_add]; exact add_mem hx hy
    | smul a x _ hx =>
      rw [Pi.smul_apply, Algebra.smul_def, map_mul, mul_left_comm]
      exact mul_mem (VacMove.inc_int D a) hx
  obtain ⟨γ, s, hs, h1, -⟩ := GlobalTheory.RepEqAt.repExS D m (by omega) N ⟨L, hL⟩
    ⟨stdL D N, GlobalTheory.VacuumScalar.sd_of_moves (GlobalTheory.VacuumScalar.moves_one D N)⟩
  have hs0 : 0 < s := Nat.pos_of_ne_zero (by rintro rfl; simp at hs; omega)
  obtain ⟨hsep, hcpl⟩ := GlobalTheory.IntAdeleComplete.integral_separated_complete D
  obtain ⟨f₀, hf₀, hff₀, ⟨w, hw, hfw⟩, h3⟩ := GlobalTheory.IdealIdele.exists_idem (OhE D) hsep hcpl m (by omega)
  obtain ⟨v, hv, hfv⟩ := h3 s hs0 hs.symm
  have hv' := congrArg (sgA D) hfv
  rw [map_sub, map_one, map_mul, map_natCast] at hv'
  have hff' : sgA D f₀ * sgA D f₀ = sgA D f₀ := by rw [← map_mul, hff₀]
  obtain ⟨e, he, hse, ⟨v₁, hv₁, e1⟩, w₁, hw₁, e2⟩ : ∃ e : AE D, e * e = e ∧ sgA D e = e ∧
      (∃ v ∈ OhE D, e = (s : AE D) * v) ∧ ∃ w ∈ OhE D, 1 - e = (m : AE D) * w := by
    refine ⟨1 - f₀ * sgA D f₀, ?_, ?_, ⟨v + f₀ * sgA D v, add_mem hv (mul_mem hf₀ (VacMove.sgA_mem D hv)), ?_⟩,
      w * sgA D f₀, mul_mem hw (VacMove.sgA_mem D hf₀), ?_⟩
    · linear_combination (sgA D f₀ * sgA D f₀) * hff₀ + f₀ * hff'
    · rw [map_sub, map_one, map_mul, VacMove.sgA_sgA, mul_comm]
    · linear_combination hfv + f₀ * hv'
    · linear_combination sgA D f₀ * hfw
  obtain ⟨γA, hγ⟩ := exists_rat γ
  obtain ⟨M, hM⟩ := GlobalTheory.VacuumScalar.exists_moves (GlobalTheory.VacuumScalar.cutG e he hse γA)⁻¹
  have hMs := GlobalTheory.VacuumScalar.sd_of_moves hM
  have hle : L ≤ M := by
    intro x hx
    rw [hM x]
    intro i
    rw [Subgroup.coe_inv, inv_inv]
    change ((e • ((γA : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) + (1 - e) • 1).mulVec _) i ∈ _
    have hγ' : ((γA : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) = _ := hγ
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hγ', Pi.add_apply, Pi.smul_apply,
      Pi.smul_apply, smul_eq_mul, smul_eq_mul, e2]
    have t1 := (RingHom.map_mulVec (inc D) (γ : Matrix (Fin N) (Fin N) D.host.E) x i).symm
    have t2 := (GlobalTheory.VacuumScalar.moves_one D N _).1 (h1 _ ⟨x, hx, rfl⟩) i
    rw [OneMemClass.coe_one, inv_one, Units.val_one, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul, map_mul,
      map_natCast] at t2
    refine add_mem ?_ ?_
    · rw [e1, mul_comm (s : AE D), mul_assoc]
      refine mul_mem hv₁ ?_
      convert t2 using 2
      exact t1
    · rw [mul_comm (m : AE D), mul_assoc]
      exact mul_mem hw₁ (hm x hx i)
  have : L = M := le_antisymm hle fun y hy => (hL.2.2 y).2 fun x hx => (hMs.2.2 y).1 hy x (hle hx)
  exact ⟨_, this ▸ hM⟩

/- English proof (translation)
Introduce `D`. Use `⟨fun u v 𝔞 𝔟 hu hv a => ⟨fun ha => ?_, fun ha => ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Use `Submodule.mul_induction_on ha (fun x hx y hy => ?_) fun x y hx hy => ?_` and prove the remaining obligations. Use `mul_mem ((hu x).1 hx) ((hv y).1 hy)` as an intermediate fact. Rewrite using `[mul_inv, Units.val_mul, map_mul]`.

Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_add, mul_add]`. Conclude with `add_mem hx hy`. Take `⟨k₁, hk₁, h₁⟩` from `GlobalTheory.HeckeVal.exists_denom D ((u⁻¹ : (AE D)ˣ) : AE D)`.

Take `⟨k₂, hk₂, h₂⟩` from `GlobalTheory.HeckeVal.exists_denom D (u : AE D)`. Rewrite `ha` using `[mul_inv, Units.val_mul]`. Take `⟨b, s, hs, e1⟩` from `approxU D u 1 (Nat.mul_pos hk₁ hk₂)`. Take `⟨c, t, ht, e2⟩` from `approxU D v (((u⁻¹ : (AE D)ˣ) : AE D) * ((v⁻¹ : (AE D)ˣ) : AE D) * inc D a) (Nat.mul_pos hk₁ hk₂)`. Establish `hb : b ∈ 𝔞` using `(hu b).2 (e1 ▸ add_mem (one_mem _) (mul_mem (natCast_mem _ _) hs))`.

Establish `hc : c ∈ 𝔟` using `(hv c).2 (e2 ▸ add_mem ha (mul_mem (natCast_mem _ _) ht))`. Establish `hk : (k₁ : D.host.E) ∈ 𝔞` using `(hu _).2 (by rw [map_natCast, mul_comm]; exact h₁)`. Establish `hr : (k₁ : D.host.E)⁻¹ * (a - b * c) ∈ 𝔟`. Rewrite using `[hv]`. Use `neg_mem (mul_mem h₂ (add_mem (add_mem (mul_mem hs ha) ht) (mul_mem (natCast_mem _ (k₁ * k₂)) (mul_mem hs ht))))` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Establish `h` using `inc_inv_nat D hk₁`. Establish `h'` using `u.mul_inv`. Establish `eb : inc D b = u * (1 + ((k₁ * k₂ : ℕ) : AE D) * s)` using `by rw [← e1, Units.mul_inv_cancel_left]`. Rewrite using `[map_mul, map_sub, map_mul, mul_left_comm, mul_sub, mul_left_comm _ (inc D b), e2, eb]`.

Use `push_cast`. Generalize the expression as in `((u⁻¹ : (AE D)ˣ) : AE D) = u' at *`. Generalize the expression as in `((v⁻¹ : (AE D)ˣ) : AE D) = v' at *`. Take the linear combination `(-(k₂ * u * (s * (u' * v' * inc D a) + t + k₁ * k₂ * (s * t)))) * h - inc D (k₁ : D.host.E)⁻¹ * v' * inc D a * h'`. Use `add_mem (Submodule.mul_mem_mul hk hr) (Submodule.mul_mem_mul hb hc)` as an intermediate fact.

Rewrite `this` using `[mul_inv_cancel_left₀ (Nat.cast_ne_zero.2 hk₁.ne'), sub_add_cancel]`. Then use the resulting hypothesis. Establish `key : ∀ u v : (AE D)ˣ, (∀ a, ((u⁻¹ : (AE D)ˣ) : AE D) * inc D a ∈ OhE D → ((v⁻¹ : (AE D)ˣ) : AE D) * inc D a ∈ OhE D) → ((u * v⁻¹ : (AE D)ˣ) : AE D) ∈ OhE D`. Introduce `u v h`. Take `⟨k, hk, h₁⟩` from `GlobalTheory.HeckeVal.exists_denom D ((u * v⁻¹ : (AE D)ˣ) : AE D)`. Take `⟨b, s, hs, e1⟩` from `approxU D u 1 hk`.

Establish `eb : inc D b = u * (1 + (k : AE D) * s)` using `by rw [← e1, Units.mul_inv_cancel_left]`. Use `sub_mem (h b (e1 ▸ add_mem (one_mem _) (mul_mem (natCast_mem _ _) hs))) (mul_mem h₁ hs)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[eb, Units.val_mul]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `u v h`. Use `⟨key u v fun a => (h a).1, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_inv_rev, inv_inv]`. Conclude with `key v u fun a => (h a).2`. Introduce and unpack `𝔞 ⟨𝔟, -, hab⟩`.

Establish `hint : ∀ x ∈ 𝔞, ∀ y ∈ 𝔟, IsIntegral ℤ (x * y)` using `fun x hx y hy => by`. Use `Submodule.mul_mem_mul hx hy` as an intermediate fact. Rewrite `this` using `[hab, Submodule.mem_one]`. Take `⟨r, hr⟩` from `this`. Rewrite using `[← hr]`.

Conclude with `r.isIntegral_coe`. Establish `h1 : (1 : D.host.E) ∈ 𝔞 * 𝔟` using `by rw [hab, Submodule.mem_one]; exact ⟨1, map_one _⟩`. Choose the witnesses or unpack the hypotheses as in `⟨a₀, ha₀, b₀, hb₀, h0⟩ : ∃ a ∈ 𝔞, ∃ b ∈ 𝔟, a * b ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Conclude with `one_ne_zero (Submodule.mul_induction_on (C := fun x => x = 0) h1 h fun x y hx hy => by rw [hx, hy, add_zero])`. Establish `hb0 : b₀ ≠ 0` using `right_ne_zero_of_mul h0`. Set `B : Ideal (𝓞 D.host.E)` to `Submodule.comap (LinearMap.toSpanSingleton (𝓞 D.host.E) D.host.E b₀⁻¹) 𝔞`. Establish `hB : ∀ r : 𝓞 D.host.E, r ∈ B ↔ (r : D.host.E) * b₀⁻¹ ∈ 𝔞` using `fun r => Iff.rfl`. Establish `hBa : ∀ a ∈ 𝔞, ∃ r : 𝓞 D.host.E, r ∈ B ∧ (r : D.host.E) = a * b₀` using `fun a ha => by`.

Use `⟨⟨a * b₀, hint a ha b₀ hb₀⟩, (hB _).2 ?_, rfl⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `a * b₀ * b₀⁻¹ ∈ 𝔞`. Rewrite using `[mul_inv_cancel_right₀ hb0]` and apply the resulting hypothesis. Take `⟨y, y1, k, b, w, hb, hw, ey⟩` from `GlobalTheory.IdealIdele.exists_idele_generator D B (fun h => by`. Take `⟨r, hr, e⟩` from `hBa a₀ ha₀`.

Rewrite `hr` using `[h, Ideal.mem_bot]`. Conclude with `h0 (by rw [← e, hr]; rfl))`. Use `⟨y * (Units.map (inc D).toMonoidHom (Units.mk0 b₀ hb0))⁻¹, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[mul_inv, inv_inv, Units.val_mul]`. Express the relevant statement in the definitionally equal form `_ ↔ ((y⁻¹ : (AE D)ˣ) : AE D) * inc D b₀ * inc D a ∈ OhE D`.

Rewrite using `[mul_assoc, ← map_mul, mul_comm b₀]`. Use `⟨fun ha => ?_, fun ha => ?_⟩` and prove the remaining obligations. Take `⟨r, hr, e⟩` from `hBa a ha`. Rewrite using `[← e]`. Conclude with `y1 r hr`.

Establish `hβ : ∀ β ∈ 𝔟, IsIntegral ℤ (β * a)` using `fun β hβ => by`. Rewrite using `[← GlobalTheory.HeckeVal.inc_mem_iff]`. Establish `: inc D (β * a) = (∑ i, inc D ((b i : D.host.E) * b₀⁻¹ * β) * w i) * (((y⁻¹ : (AE D)ˣ) : AE D) * inc D (a * b₀))`. Establish `e : ∑ i, inc D ((b i : D.host.E) * b₀⁻¹ * β) * w i = y * inc D (b₀⁻¹ * β)`. Rewrite using `[ey, Finset.sum_mul]`.

Conclude with `Finset.sum_congr rfl fun i _ => by rw [mul_assoc, map_mul]; ring`. Rewrite using `[e, mul_comm (y : AE D), mul_assoc, Units.mul_inv_cancel_left, ← map_mul]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`.

Conclude with `mul_mem (sum_mem fun i _ => mul_mem ((GlobalTheory.HeckeVal.inc_mem_iff D _).2 (hint _ ((hB _).1 (hb i)) β hβ)) (hw i)) ha`. Rewrite using `[← one_mul a]`. Use `Submodule.mul_induction_on (C := fun x => x * a ∈ 𝔞) h1 (fun x hx β hβ' => ?_) fun x y hx hy => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, mul_comm]`. Conclude with `𝔞.smul_mem (⟨_, hβ β hβ'⟩ : 𝓞 D.host.E) hx`.

Rewrite using `[add_mul]`. Conclude with `add_mem hx hy`.
-/
theorem idele_ideal_laws : ∀ (D : D7), (∀ (u v : (AE D)ˣ) (𝔞 𝔟 : IdE D), (∀ a, a ∈ 𝔞 ↔ ((u⁻¹ : (AE D)ˣ) : AE D) * inc D a ∈ OhE D) → (∀ a, a ∈ 𝔟 ↔ ((v⁻¹ : (AE D)ˣ) : AE D) * inc D a ∈ OhE D) → ∀ a, a ∈ 𝔞 * 𝔟 ↔ (((u * v)⁻¹ : (AE D)ˣ) : AE D) * inc D a ∈ OhE D) ∧ (∀ (u v : (AE D)ˣ), (∀ a, ((u⁻¹ : (AE D)ˣ) : AE D) * inc D a ∈ OhE D ↔ ((v⁻¹ : (AE D)ˣ) : AE D) * inc D a ∈ OhE D) → IntU D (u * v⁻¹)) ∧ (∀ 𝔞 : IdE D, N1 D 𝔞 → ∃ u : (AE D)ˣ, ∀ a, a ∈ 𝔞 ↔ ((u⁻¹ : (AE D)ˣ) : AE D) * inc D a ∈ OhE D) := by
  intro D
  refine ⟨fun u v 𝔞 𝔟 hu hv a => ⟨fun ha => ?_, fun ha => ?_⟩, ?_, ?_⟩
  · refine Submodule.mul_induction_on ha (fun x hx y hy => ?_) fun x y hx hy => ?_
    · have := mul_mem ((hu x).1 hx) ((hv y).1 hy)
      rw [mul_inv, Units.val_mul, map_mul]
      convert this using 1
      ring
    · rw [map_add, mul_add]; exact add_mem hx hy
  · obtain ⟨k₁, hk₁, h₁⟩ := GlobalTheory.HeckeVal.exists_denom D ((u⁻¹ : (AE D)ˣ) : AE D)
    obtain ⟨k₂, hk₂, h₂⟩ := GlobalTheory.HeckeVal.exists_denom D (u : AE D)
    rw [mul_inv, Units.val_mul] at ha
    obtain ⟨b, s, hs, e1⟩ := approxU D u 1 (Nat.mul_pos hk₁ hk₂)
    obtain ⟨c, t, ht, e2⟩ := approxU D v (((u⁻¹ : (AE D)ˣ) : AE D) * ((v⁻¹ : (AE D)ˣ) : AE D) * inc D a)
      (Nat.mul_pos hk₁ hk₂)
    have hb : b ∈ 𝔞 := (hu b).2 (e1 ▸ add_mem (one_mem _) (mul_mem (natCast_mem _ _) hs))
    have hc : c ∈ 𝔟 := (hv c).2 (e2 ▸ add_mem ha (mul_mem (natCast_mem _ _) ht))
    have hk : (k₁ : D.host.E) ∈ 𝔞 := (hu _).2 (by rw [map_natCast, mul_comm]; exact h₁)
    have hr : (k₁ : D.host.E)⁻¹ * (a - b * c) ∈ 𝔟 := by
      rw [hv]
      have := neg_mem (mul_mem h₂ (add_mem (add_mem (mul_mem hs ha) ht) (mul_mem (natCast_mem _ (k₁ * k₂)) (mul_mem hs ht))))
      convert this using 1
      have h := inc_inv_nat D hk₁
      have h' := u.mul_inv
      have eb : inc D b = u * (1 + ((k₁ * k₂ : ℕ) : AE D) * s) := by rw [← e1, Units.mul_inv_cancel_left]
      rw [map_mul, map_sub, map_mul, mul_left_comm, mul_sub, mul_left_comm _ (inc D b), e2, eb]
      push_cast
      generalize ((u⁻¹ : (AE D)ˣ) : AE D) = u' at *
      generalize ((v⁻¹ : (AE D)ˣ) : AE D) = v' at *
      linear_combination (-(k₂ * u * (s * (u' * v' * inc D a) + t + k₁ * k₂ * (s * t)))) * h -
        inc D (k₁ : D.host.E)⁻¹ * v' * inc D a * h'
    have := add_mem (Submodule.mul_mem_mul hk hr) (Submodule.mul_mem_mul hb hc)
    rwa [mul_inv_cancel_left₀ (Nat.cast_ne_zero.2 hk₁.ne'), sub_add_cancel] at this
  · have key : ∀ u v : (AE D)ˣ, (∀ a, ((u⁻¹ : (AE D)ˣ) : AE D) * inc D a ∈ OhE D →
        ((v⁻¹ : (AE D)ˣ) : AE D) * inc D a ∈ OhE D) → ((u * v⁻¹ : (AE D)ˣ) : AE D) ∈ OhE D := by
      intro u v h
      obtain ⟨k, hk, h₁⟩ := GlobalTheory.HeckeVal.exists_denom D ((u * v⁻¹ : (AE D)ˣ) : AE D)
      obtain ⟨b, s, hs, e1⟩ := approxU D u 1 hk
      have eb : inc D b = u * (1 + (k : AE D) * s) := by rw [← e1, Units.mul_inv_cancel_left]
      have := sub_mem (h b (e1 ▸ add_mem (one_mem _) (mul_mem (natCast_mem _ _) hs))) (mul_mem h₁ hs)
      convert this using 1
      rw [eb, Units.val_mul]
      ring
    intro u v h
    refine ⟨key u v fun a => (h a).1, ?_⟩
    rw [mul_inv_rev, inv_inv]
    exact key v u fun a => (h a).2
  · rintro 𝔞 ⟨𝔟, -, hab⟩
    have hint : ∀ x ∈ 𝔞, ∀ y ∈ 𝔟, IsIntegral ℤ (x * y) := fun x hx y hy => by
      have := Submodule.mul_mem_mul hx hy
      rw [hab, Submodule.mem_one] at this
      obtain ⟨r, hr⟩ := this
      rw [← hr]; exact r.isIntegral_coe
    have h1 : (1 : D.host.E) ∈ 𝔞 * 𝔟 := by rw [hab, Submodule.mem_one]; exact ⟨1, map_one _⟩
    obtain ⟨a₀, ha₀, b₀, hb₀, h0⟩ : ∃ a ∈ 𝔞, ∃ b ∈ 𝔟, a * b ≠ 0 := by
      by_contra h
      push_neg at h
      exact one_ne_zero (Submodule.mul_induction_on (C := fun x => x = 0) h1 h fun x y hx hy => by rw [hx, hy, add_zero])
    have hb0 : b₀ ≠ 0 := right_ne_zero_of_mul h0
    let B : Ideal (𝓞 D.host.E) := Submodule.comap (LinearMap.toSpanSingleton (𝓞 D.host.E) D.host.E b₀⁻¹) 𝔞
    have hB : ∀ r : 𝓞 D.host.E, r ∈ B ↔ (r : D.host.E) * b₀⁻¹ ∈ 𝔞 := fun r => Iff.rfl
    have hBa : ∀ a ∈ 𝔞, ∃ r : 𝓞 D.host.E, r ∈ B ∧ (r : D.host.E) = a * b₀ := fun a ha => by
      refine ⟨⟨a * b₀, hint a ha b₀ hb₀⟩, (hB _).2 ?_, rfl⟩
      change a * b₀ * b₀⁻¹ ∈ 𝔞
      rwa [mul_inv_cancel_right₀ hb0]
    obtain ⟨y, y1, k, b, w, hb, hw, ey⟩ := GlobalTheory.IdealIdele.exists_idele_generator D B (fun h => by
      obtain ⟨r, hr, e⟩ := hBa a₀ ha₀
      rw [h, Ideal.mem_bot] at hr
      exact h0 (by rw [← e, hr]; rfl))
    refine ⟨y * (Units.map (inc D).toMonoidHom (Units.mk0 b₀ hb0))⁻¹, fun a => ?_⟩
    rw [mul_inv, inv_inv, Units.val_mul]
    change _ ↔ ((y⁻¹ : (AE D)ˣ) : AE D) * inc D b₀ * inc D a ∈ OhE D
    rw [mul_assoc, ← map_mul, mul_comm b₀]
    refine ⟨fun ha => ?_, fun ha => ?_⟩
    · obtain ⟨r, hr, e⟩ := hBa a ha
      rw [← e]; exact y1 r hr
    have hβ : ∀ β ∈ 𝔟, IsIntegral ℤ (β * a) := fun β hβ => by
      rw [← GlobalTheory.HeckeVal.inc_mem_iff]
      have : inc D (β * a) = (∑ i, inc D ((b i : D.host.E) * b₀⁻¹ * β) * w i) *
          (((y⁻¹ : (AE D)ˣ) : AE D) * inc D (a * b₀)) := by
        have e : ∑ i, inc D ((b i : D.host.E) * b₀⁻¹ * β) * w i = y * inc D (b₀⁻¹ * β) := by
          rw [ey, Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by rw [mul_assoc, map_mul]; ring
        rw [e, mul_comm (y : AE D), mul_assoc, Units.mul_inv_cancel_left, ← map_mul]
        congr 1
        field_simp
      rw [this]
      exact mul_mem (sum_mem fun i _ => mul_mem ((GlobalTheory.HeckeVal.inc_mem_iff D _).2 (hint _ ((hB _).1 (hb i)) β hβ)) (hw i)) ha
    rw [← one_mul a]
    refine Submodule.mul_induction_on (C := fun x => x * a ∈ 𝔞) h1 (fun x hx β hβ' => ?_) fun x y hx hy => ?_
    · rw [mul_assoc, mul_comm]
      exact 𝔞.smul_mem (⟨_, hβ β hβ'⟩ : 𝓞 D.host.E) hx
    · rw [add_mul]; exact add_mem hx hy

/- English proof (translation)
Rewrite using `[Matrix.det_apply']`. Conclude with `sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => h _ _)`.
-/
theorem det_mem {A : Type} [CommRing A] (S : Subring A) {n : ℕ} {X : Matrix (Fin n) (Fin n) A} (h : ∀ i j, X i j ∈ S) :
    X.det ∈ S := by
  rw [Matrix.det_apply']
  exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => h _ _)

/- English proof (translation)
Set `Y : Matrix (Fin n) (Fin n) S` to `Matrix.of fun i j => ⟨X i j, h i j⟩`. Take `⟨t, ht⟩ : ∃ t : S, (1 + (m : S) • Y).det = 1 + (m : S) * t` from `⟨Y.trace + (Polynomial.eval (m : S) _) * m, by rw [Matrix.det_one_add_smul]; ring_nf⟩`. Use `⟨t, t.2, ?_⟩` and prove the remaining obligations. Use `congrArg S.subtype ht` as an intermediate fact. Rewrite `this` using `[RingHom.map_det, map_add, map_add, map_one, map_one, map_mul, map_natCast]`.

Use `Eq.trans ?_ this` and prove the remaining obligations. Use `congr 2`.
-/
theorem det_one_add {A : Type} [CommRing A] (S : Subring A) {n : ℕ} {X : Matrix (Fin n) (Fin n) A} (h : ∀ i j, X i j ∈ S)
    (m : ℕ) : ∃ t ∈ S, (1 + (m : A) • X).det = 1 + (m : A) * t := by
  let Y : Matrix (Fin n) (Fin n) S := Matrix.of fun i j => ⟨X i j, h i j⟩
  obtain ⟨t, ht⟩ : ∃ t : S, (1 + (m : S) • Y).det = 1 + (m : S) * t :=
    ⟨Y.trace + (Polynomial.eval (m : S) _) * m, by rw [Matrix.det_one_add_smul]; ring_nf⟩
  refine ⟨t, t.2, ?_⟩
  have := congrArg S.subtype ht
  rw [RingHom.map_det, map_add, map_add, map_one, map_one, map_mul, map_natCast] at this
  refine Eq.trans ?_ this
  congr 2

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Conclude with `sum_mem fun l _ => mul_mem (h i l) (h' l j)`.
-/
theorem mul_int {A : Type} [CommRing A] (S : Subring A) {n : ℕ} {X Y : Matrix (Fin n) (Fin n) A} (h : ∀ i j, X i j ∈ S)
    (h' : ∀ i j, Y i j ∈ S) (i j : Fin n) : (X * Y) i j ∈ S := by
  rw [Matrix.mul_apply]
  exact sum_mem fun l _ => mul_mem (h i l) (h' l j)

section Abstract

variable {E A : Type} [Field E] [NumberField E] [CommRing A] {S : Subring A} {ι : E →+* A} {N : ℕ}
  {g₁ g₂ : GL (Fin N) A} {L₁ L₂ : Submodule (𝓞 E) (Fin N → E)}

/- English proof (translation)
Establish `key : ∀ v : Fin N → E, (fun j => ι (B.mulVec v j)) = (B.map ι).mulVec fun j => ι (v j)` using `fun v => funext fun j => RingHom.map_mulVec ι B v j`. Establish `hmv : ∀ {M : Matrix (Fin N) (Fin N) A} {v : Fin N → A}, (∀ i j, M i j ∈ S) → (∀ i, v i ∈ S) → ∀ i, M.mulVec v i ∈ S` using `fun hM hv i => by`. Simplify using `only [Matrix.mulVec, dotProduct]`. Conclude with `sum_mem fun j _ => mul_mem (hM i j) (hv j)`. Prove the components needed by the constructor for the conclusion.

Introduce `h i j set X := ((g₂⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) * B.map ι * (g₁ : Matrix (Fin N) (Fin N) A) with hX`. Take `⟨m, hm, dm⟩` from `hden (fun p : Fin N × Fin N => X p.1 p.2)`. Take `⟨n, hn, dn⟩` from `hden (fun p : Fin N × Fin N => ((g₁⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) p.1 p.2)`. Use `choose v s hs e using fun k => happ (((g₁ : Matrix (Fin N) (Fin N) A).mulVec (Pi.single j 1)) k) (Nat.mul_pos hm hn)`. Establish `hw` using `hmv (M := (n : A) • ((g₁⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A)) (fun i j => dn (i, j)) hs`.

Use `set w := ((n : A) • ((g₁⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A)).mulVec s with hwd`. Establish `ev : (fun k => ι (v k)) = (g₁ : Matrix (Fin N) (Fin N) A).mulVec (Pi.single j 1 + (m : A) • w)`. Rewrite using `[Matrix.mulVec_add, Matrix.mulVec_smul, hwd, Matrix.mulVec_mulVec, Matrix.mul_smul, Units.mul_inv, Matrix.smul_mulVec, Matrix.one_mulVec]`. Use function extensionality and compare the values at `k`. Simplify using `only [e, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_mul, mul_assoc]`.

Establish `hv : v ∈ L₁` using `(m₁ v).2 fun k => by`. Rewrite using `[ev, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Pi.add_apply, Pi.single_apply]`. Use `add_mem ?_ (mul_mem (natCast_mem _ _) (hw k))` and prove the remaining obligations. Use `split_ifs`. Conclude with `one_mem _`.

Conclude with `zero_mem _`. Establish `h1` using `(m₂ _).1 (h v hv) i`. Rewrite `h1` using `[key, ev, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hX, Matrix.mulVec_add, Matrix.mulVec_smul, ← Matrix.smul_mulVec, Matrix.mulVec_single_one, Pi.add_apply]`. Use `sub_mem h1 (hmv (M := (m : A) • X) (fun i j => dm (i, j)) hw i)` as an intermediate fact. Rewrite `this` using `[add_sub_cancel_right]`. Then use the resulting hypothesis.

Introduce `h v hv`. Rewrite using `[m₂]`. Introduce `i`. Use `hmv h ((m₁ v).1 hv) i` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_mulVec, mul_assoc, Units.mul_inv, mul_one, ← Matrix.mulVec_mulVec, ← key]`. Then use the resulting hypothesis.
-/
theorem maps_iff (hden : ∀ {κ : Type} [Fintype κ] (y : κ → A), ∃ m : ℕ, 0 < m ∧ ∀ i, (m : A) * y i ∈ S)
    (happ : ∀ (y : A) {m : ℕ}, 0 < m → ∃ b : E, ∃ s ∈ S, ι b = y + (m : A) * s)
    (m₁ : ∀ x, x ∈ L₁ ↔ ∀ i, (((g₁⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A).mulVec fun j => ι (x j)) i ∈ S)
    (m₂ : ∀ x, x ∈ L₂ ↔ ∀ i, (((g₂⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A).mulVec fun j => ι (x j)) i ∈ S)
    (B : Matrix (Fin N) (Fin N) E) :
    (∀ v ∈ L₁, B.mulVec v ∈ L₂) ↔ ∀ i j, (((g₂⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) * B.map ι *
      (g₁ : Matrix (Fin N) (Fin N) A)) i j ∈ S := by
  have key : ∀ v : Fin N → E, (fun j => ι (B.mulVec v j)) = (B.map ι).mulVec fun j => ι (v j) :=
    fun v => funext fun j => RingHom.map_mulVec ι B v j
  have hmv : ∀ {M : Matrix (Fin N) (Fin N) A} {v : Fin N → A}, (∀ i j, M i j ∈ S) → (∀ i, v i ∈ S) →
      ∀ i, M.mulVec v i ∈ S := fun hM hv i => by
    simp only [Matrix.mulVec, dotProduct]
    exact sum_mem fun j _ => mul_mem (hM i j) (hv j)
  constructor
  · intro h i j
    set X := ((g₂⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) * B.map ι * (g₁ : Matrix (Fin N) (Fin N) A) with hX
    obtain ⟨m, hm, dm⟩ := hden (fun p : Fin N × Fin N => X p.1 p.2)
    obtain ⟨n, hn, dn⟩ := hden (fun p : Fin N × Fin N => ((g₁⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) p.1 p.2)
    choose v s hs e using fun k => happ (((g₁ : Matrix (Fin N) (Fin N) A).mulVec (Pi.single j 1)) k) (Nat.mul_pos hm hn)
    have hw := hmv (M := (n : A) • ((g₁⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A)) (fun i j => dn (i, j)) hs
    set w := ((n : A) • ((g₁⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A)).mulVec s with hwd
    have ev : (fun k => ι (v k)) = (g₁ : Matrix (Fin N) (Fin N) A).mulVec (Pi.single j 1 + (m : A) • w) := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, hwd, Matrix.mulVec_mulVec, Matrix.mul_smul, Units.mul_inv,
        Matrix.smul_mulVec, Matrix.one_mulVec]
      funext k
      simp only [e, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_mul, mul_assoc]
    have hv : v ∈ L₁ := (m₁ v).2 fun k => by
      rw [ev, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Pi.add_apply, Pi.single_apply]
      refine add_mem ?_ (mul_mem (natCast_mem _ _) (hw k))
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    have h1 := (m₂ _).1 (h v hv) i
    rw [key, ev, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hX, Matrix.mulVec_add, Matrix.mulVec_smul,
      ← Matrix.smul_mulVec, Matrix.mulVec_single_one, Pi.add_apply] at h1
    have := sub_mem h1 (hmv (M := (m : A) • X) (fun i j => dm (i, j)) hw i)
    rwa [add_sub_cancel_right] at this
  · intro h v hv
    rw [m₂]
    intro i
    have := hmv h ((m₁ v).1 hv) i
    rwa [Matrix.mulVec_mulVec, mul_assoc, Units.mul_inv, mul_one, ← Matrix.mulVec_mulVec, ← key] at this

/- English proof (translation)
Use `set J := Submodule.span (𝓞 E) {x | ∃ B : Matrix (Fin N) (Fin N) E, (∀ v ∈ L₁, B.mulVec v ∈ L₂) ∧ x = B.det} with hJ`. Use `set u : Aˣ := Matrix.GeneralLinearGroup.det (g₁⁻¹ * g₂) with hu`. Establish `hdet : ∀ B : Matrix (Fin N) (Fin N) E, ((u⁻¹ : Aˣ) : A) * ι B.det = (((g₂⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) * B.map ι * (g₁ : Matrix (Fin N) (Fin N) A)).det`. Introduce `B`. Rewrite using `[hu, ← map_inv, mul_inv_rev, inv_inv, Matrix.GeneralLinearGroup.val_det_apply, Units.val_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, RingHom.map_det, RingHom.mapMatrix_apply]`.

Expand and normalize the polynomial expressions, which then agree. Prove the components needed by the constructor for the conclusion. Introduce `ha`. Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨B, hA, rfl⟩` from `hx`. Rewrite using `[hdet]`. Conclude with `det_mem _ ((maps_iff hden happ m₁ m₂ B).1 hA)`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add, mul_add]`.

Conclude with `add_mem hx hy`. Consider the case `smul c x _ hx`. Rewrite using `[Algebra.smul_def, map_mul, mul_left_comm]`. Conclude with `mul_mem ((hint _).2 c.isIntegral_coe) hx`. Introduce `ha set G₁ : Matrix (Fin N) (Fin N) A := (g₁ : Matrix (Fin N) (Fin N) A) with hG₁ set G₂ : Matrix (Fin N) (Fin N) A := ((g₂⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) with hG₂`.

Take `⟨n₁, hn₁, d₁⟩` from `hden (fun p : Fin N × Fin N => G₁ p.1 p.2)`. Take `⟨n₂, hn₂, d₂⟩` from `hden (fun p : Fin N × Fin N => G₂ p.1 p.2)`. Take `⟨k, hk, dk⟩` from `hden (fun _ : Unit => (u : A))`. Use `replace dk := dk ()`. Establish `hsand : ∀ X : Matrix (Fin N) (Fin N) A, (∀ i j, X i j ∈ S) → ∀ i j, (G₂ * (((n₁ * n₂ : ℕ) : A) • X) * G₁) i j ∈ S`.

Introduce `X hX`. Establish `: G₂ * (((n₁ * n₂ : ℕ) : A) • X) * G₁ = ((n₂ : A) • G₂) * X * ((n₁ : A) • G₁)`. Simplify using `only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Nat.cast_mul]`. Rewrite using `[this]`. Conclude with `mul_int _ (mul_int _ (fun i j => d₂ (i, j)) hX) fun i j => d₁ (i, j)`.

Establish `hn : 0 < n₁ * n₂` using `Nat.mul_pos hn₁ hn₂`. Generalize the expression as in `n₁ * n₂ = n at hsand hn`. Establish `hnJ : ((n ^ N : ℕ) : E) ∈ J`. Use `Submodule.subset_span ⟨(n : E) • 1, (maps_iff hden happ m₁ m₂ _).2 ?_, by simp⟩` and prove the remaining obligations. Establish `: ((n : E) • (1 : Matrix (Fin N) (Fin N) E)).map ι = (n : A) • 1`.

Use extensionality with `i j`. Apply the tactic sequence `by_cases h : i = j <;> simp [Matrix.one_apply, h]`. Rewrite using `[this]`. Use `hsand 1 fun i j => ?_` and prove the remaining obligations. Rewrite using `[Matrix.one_apply]`.

Use `split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`. Establish `hnN : 0 < n ^ N` using `pow_pos hn N`. Generalize the expression as in `n ^ N = l at hnJ hnN`.

Establish `hm : 0 < l * k` using `Nat.mul_pos hnN hk`. Use `choose b s hs e using fun i j => happ (((g₂ * g₁⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) i j) (Nat.mul_pos hm hn)`. Establish `eA : G₂ * (Matrix.of b).map ι * G₁ = 1 + ((l * k : ℕ) : A) • (G₂ * ((n : A) • Matrix.of s) * G₁)`. Establish `: (Matrix.of b).map ι = ((g₂ * g₁⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) + ((l * k : ℕ) : A) • (n : A) • Matrix.of s`. Use extensionality with `i j`.

Simplify using `only [Matrix.map_apply, Matrix.of_apply, e, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Nat.cast_mul, mul_assoc]`. Rewrite using `[this, mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, hG₁, hG₂, ← Units.val_mul, ← Units.val_mul]`. Simplify using the standard rewrite rules. Establish `hX` using `hsand (Matrix.of s) hs`. Establish `hAJ : (Matrix.of b).det ∈ J`.

Use `Submodule.subset_span ⟨_, (maps_iff hden happ m₁ m₂ _).2 fun i j => ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[eA, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]`. Use `add_mem ?_ (mul_mem (natCast_mem _ _) (hX i j))` and prove the remaining obligations. Use `split_ifs`. Conclude with `one_mem _`.

Conclude with `zero_mem _`. Take `⟨t, ht, et⟩` from `det_one_add _ hX (l * k)`. Rewrite `et` using `[← eA, ← hdet]`. Take `⟨r, w, hw, er⟩` from `happ (((u⁻¹ : Aˣ) : A) * ι a) hm`. Establish `hr' : ι r ∈ S` using `er ▸ add_mem ha (mul_mem (natCast_mem _ _) hw)`.

Establish `hr` using `(hint r).1 hr'`. Establish `hc : IsIntegral ℤ ((l : E)⁻¹ * (a - r * (Matrix.of b).det))`. Rewrite using `[← hint]`. Use `mul_mem dk (sub_mem (neg_mem hw) (mul_mem hr' ht))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Establish `h : ι (l : E)⁻¹ * (l : A) = 1`. Rewrite using `[← map_natCast ι, ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hnN.ne'), map_one]`. Establish `h'` using `u.mul_inv`. Rewrite using `[map_mul, map_sub, map_mul]`. Move the coercions through the operations in `at et er`.

Generalize the expression as in `((u⁻¹ : Aˣ) : A) = u' at *`. Take the linear combination `(-ι (l : E)⁻¹ * u) * er - (ι (l : E)⁻¹ * u * ι r) * et + (k * u * (-w - ι r * t)) * h - ι (l : E)⁻¹ * (ι a - ι r * ι (Matrix.of b).det) * h'`. Use `add_mem ((J).smul_mem (⟨_, hc⟩ : 𝓞 E) hnJ) ((J).smul_mem (⟨_, hr⟩ : 𝓞 E) hAJ)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Express the relevant statement in the definitionally equal form `a = (l : E)⁻¹ * (a - r * (Matrix.of b).det) * l + r * (Matrix.of b).det`.

Establish `: (l : E) ≠ 0` using `Nat.cast_ne_zero.2 hnN.ne'`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mem_det_iff (hden : ∀ {κ : Type} [Fintype κ] (y : κ → A), ∃ m : ℕ, 0 < m ∧ ∀ i, (m : A) * y i ∈ S)
    (happ : ∀ (y : A) {m : ℕ}, 0 < m → ∃ b : E, ∃ s ∈ S, ι b = y + (m : A) * s)
    (hint : ∀ e, ι e ∈ S ↔ IsIntegral ℤ e)
    (m₁ : ∀ x, x ∈ L₁ ↔ ∀ i, (((g₁⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A).mulVec fun j => ι (x j)) i ∈ S)
    (m₂ : ∀ x, x ∈ L₂ ↔ ∀ i, (((g₂⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A).mulVec fun j => ι (x j)) i ∈ S)
    (a : E) : a ∈ Submodule.span (𝓞 E)
      {x | ∃ B : Matrix (Fin N) (Fin N) E, (∀ v ∈ L₁, B.mulVec v ∈ L₂) ∧ x = B.det} ↔
      (((Matrix.GeneralLinearGroup.det (g₁⁻¹ * g₂))⁻¹ : Aˣ) : A) * ι a ∈ S := by
  set J := Submodule.span (𝓞 E) {x | ∃ B : Matrix (Fin N) (Fin N) E, (∀ v ∈ L₁, B.mulVec v ∈ L₂) ∧ x = B.det} with hJ
  set u : Aˣ := Matrix.GeneralLinearGroup.det (g₁⁻¹ * g₂) with hu
  have hdet : ∀ B : Matrix (Fin N) (Fin N) E, ((u⁻¹ : Aˣ) : A) * ι B.det =
      (((g₂⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) * B.map ι *
        (g₁ : Matrix (Fin N) (Fin N) A)).det := by
    intro B
    rw [hu, ← map_inv, mul_inv_rev, inv_inv, Matrix.GeneralLinearGroup.val_det_apply, Units.val_mul, Matrix.det_mul,
      Matrix.det_mul, Matrix.det_mul, RingHom.map_det, RingHom.mapMatrix_apply]
    ring
  constructor
  · intro ha
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨B, hA, rfl⟩ := hx
      rw [hdet]
      exact det_mem _ ((maps_iff hden happ m₁ m₂ B).1 hA)
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, mul_add]; exact add_mem hx hy
    | smul c x _ hx =>
      rw [Algebra.smul_def, map_mul, mul_left_comm]
      exact mul_mem ((hint _).2 c.isIntegral_coe) hx
  · intro ha
    set G₁ : Matrix (Fin N) (Fin N) A := (g₁ : Matrix (Fin N) (Fin N) A) with hG₁
    set G₂ : Matrix (Fin N) (Fin N) A := ((g₂⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) with hG₂
    obtain ⟨n₁, hn₁, d₁⟩ := hden (fun p : Fin N × Fin N => G₁ p.1 p.2)
    obtain ⟨n₂, hn₂, d₂⟩ := hden (fun p : Fin N × Fin N => G₂ p.1 p.2)
    obtain ⟨k, hk, dk⟩ := hden (fun _ : Unit => (u : A))
    replace dk := dk ()
    have hsand : ∀ X : Matrix (Fin N) (Fin N) A, (∀ i j, X i j ∈ S) →
        ∀ i j, (G₂ * (((n₁ * n₂ : ℕ) : A) • X) * G₁) i j ∈ S := by
      intro X hX
      have : G₂ * (((n₁ * n₂ : ℕ) : A) • X) * G₁ = ((n₂ : A) • G₂) * X * ((n₁ : A) • G₁) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Nat.cast_mul]
      rw [this]
      exact mul_int _ (mul_int _ (fun i j => d₂ (i, j)) hX) fun i j => d₁ (i, j)
    have hn : 0 < n₁ * n₂ := Nat.mul_pos hn₁ hn₂
    generalize n₁ * n₂ = n at hsand hn
    have hnJ : ((n ^ N : ℕ) : E) ∈ J := by
      refine Submodule.subset_span ⟨(n : E) • 1, (maps_iff hden happ m₁ m₂ _).2 ?_, by simp⟩
      have : ((n : E) • (1 : Matrix (Fin N) (Fin N) E)).map ι = (n : A) • 1 := by
        ext i j
        by_cases h : i = j <;> simp [Matrix.one_apply, h]
      rw [this]
      refine hsand 1 fun i j => ?_
      rw [Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    have hnN : 0 < n ^ N := pow_pos hn N
    generalize n ^ N = l at hnJ hnN
    have hm : 0 < l * k := Nat.mul_pos hnN hk
    choose b s hs e using fun i j => happ (((g₂ * g₁⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) i j)
      (Nat.mul_pos hm hn)
    have eA : G₂ * (Matrix.of b).map ι * G₁ = 1 + ((l * k : ℕ) : A) • (G₂ * ((n : A) • Matrix.of s) * G₁) := by
      have : (Matrix.of b).map ι = ((g₂ * g₁⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) +
          ((l * k : ℕ) : A) • (n : A) • Matrix.of s := by
        ext i j
        simp only [Matrix.map_apply, Matrix.of_apply, e, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Nat.cast_mul,
          mul_assoc]
      rw [this, mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, hG₁, hG₂, ← Units.val_mul, ← Units.val_mul]
      simp
    have hX := hsand (Matrix.of s) hs
    have hAJ : (Matrix.of b).det ∈ J := by
      refine Submodule.subset_span ⟨_, (maps_iff hden happ m₁ m₂ _).2 fun i j => ?_, rfl⟩
      rw [eA, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
      refine add_mem ?_ (mul_mem (natCast_mem _ _) (hX i j))
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    obtain ⟨t, ht, et⟩ := det_one_add _ hX (l * k)
    rw [← eA, ← hdet] at et
    obtain ⟨r, w, hw, er⟩ := happ (((u⁻¹ : Aˣ) : A) * ι a) hm
    have hr' : ι r ∈ S := er ▸ add_mem ha (mul_mem (natCast_mem _ _) hw)
    have hr := (hint r).1 hr'
    have hc : IsIntegral ℤ ((l : E)⁻¹ * (a - r * (Matrix.of b).det)) := by
      rw [← hint]
      have := mul_mem dk (sub_mem (neg_mem hw) (mul_mem hr' ht))
      convert this using 1
      have h : ι (l : E)⁻¹ * (l : A) = 1 := by
        rw [← map_natCast ι, ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hnN.ne'), map_one]
      have h' := u.mul_inv
      rw [map_mul, map_sub, map_mul]
      push_cast at et er
      generalize ((u⁻¹ : Aˣ) : A) = u' at *
      linear_combination (-ι (l : E)⁻¹ * u) * er - (ι (l : E)⁻¹ * u * ι r) * et +
        (k * u * (-w - ι r * t)) * h - ι (l : E)⁻¹ * (ι a - ι r * ι (Matrix.of b).det) * h'
    have := add_mem ((J).smul_mem (⟨_, hc⟩ : 𝓞 E) hnJ)
      ((J).smul_mem (⟨_, hr⟩ : 𝓞 E) hAJ)
    convert this using 1
    change a = (l : E)⁻¹ * (a - r * (Matrix.of b).det) * l + r * (Matrix.of b).det
    have : (l : E) ≠ 0 := Nat.cast_ne_zero.2 hnN.ne'
    field_simp
    ring

end Abstract

/- English proof (translation)
Introduce `D _ _ _ _ _ m₁ m₂ a` and use `mem_det_iff (fin_denom D) (approx D) (GlobalTheory.HeckeVal.inc_mem_iff D) m₁ m₂ a`.
-/
theorem mem_detId_iff : ∀ (D : D7) (N : ℕ) (g₁ g₂ : GL (Fin N) (AE D)) (L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Moves D g₁ L₁ → Moves D g₂ L₂ → ∀ a, a ∈ detId D L₁ L₂ ↔ (((Matrix.GeneralLinearGroup.det (g₁⁻¹ * g₂))⁻¹ : (AE D)ˣ) : AE D) * inc D a ∈ OhE D :=
  fun D _ _ _ _ _ m₁ m₂ a => mem_det_iff (fin_denom D) (approx D) (GlobalTheory.HeckeVal.inc_mem_iff D) m₁ m₂ a

/- English proof (translation)
Use `haveI : Algebra.IsAlgebraic ℚ Qbar := algebraicClosure.isAlgebraic ℚ ℂ`. Use `haveI : IsAlgClosure ℚ Qbar := algebraicClosure.isAlgClosure ℚ ℂ`. Use `haveI : IsGalois ℚ Qbar := IsAlgClosure.isGalois ℚ Qbar`. Use `haveI := hS.to_subtype`. Use `haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) := IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral`.

Use `⟨(IntermediateField.adjoin ℚ S).map Qbar.val, (IntermediateField.equivMap _ Qbar.val).toLinearEquiv.finiteDimensional, fun x hx => ⟨x, ?_, rfl⟩⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `x ∈ IntermediateField.adjoin ℚ S`. Rewrite using `[← InfiniteGalois.fixedField_fixingSubgroup (IntermediateField.adjoin ℚ S), IntermediateField.mem_fixedField_iff]`. Introduce `σ hσ`. Conclude with `hx σ fun s hs => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ s (IntermediateField.subset_adjoin _ _ hs)`.
-/
theorem exists_field (S : Set Qbar) (hS : S.Finite) : ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧
    ∀ x : Qbar, (∀ σ : Qbar ≃ₐ[ℚ] Qbar, (∀ s ∈ S, σ s = s) → σ x = x) → (x : ℂ) ∈ M := by
  haveI : Algebra.IsAlgebraic ℚ Qbar := algebraicClosure.isAlgebraic ℚ ℂ
  haveI : IsAlgClosure ℚ Qbar := algebraicClosure.isAlgClosure ℚ ℂ
  haveI : IsGalois ℚ Qbar := IsAlgClosure.isGalois ℚ Qbar
  haveI := hS.to_subtype
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  refine ⟨(IntermediateField.adjoin ℚ S).map Qbar.val,
    (IntermediateField.equivMap _ Qbar.val).toLinearEquiv.finiteDimensional, fun x hx => ⟨x, ?_, rfl⟩⟩
  change x ∈ IntermediateField.adjoin ℚ S
  rw [← InfiniteGalois.fixedField_fixingSubgroup (IntermediateField.adjoin ℚ S), IntermediateField.mem_fixedField_iff]
  intro σ hσ
  exact hx σ fun s hs => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ s (IntermediateField.subset_adjoin _ _ hs)

/- English proof (translation)
Take `⟨b, κ, hb, ⟨hκQ, hκ1⟩, rfl⟩` from `h`. Establish `hG` using `(GlobalTheory.InducedType.induced_type D).1`. Take `⟨hd, h0, hth⟩` from `GlobalTheory.Vacuum.evenTheta_properties_curveLattice D cc δ hC t0 ht`. Take `⟨-, -, hpar, hmem, -⟩` from `GlobalTheory.T.coords_along_orthonormal_realSubfield_basis D hG cc δ N N' _ b hb`. Establish `hκn : ‖κ‖ = 1` using `hκ1 (Qbar : IntermediateField ℚ ℂ).val.toRingHom`.

Establish `hκ0 : κ ≠ 0` using `by rintro rfl; simp at hκn`. Take `⟨-, -, -, u3⟩` from `GlobalTheory.theta_translation_intertwiner_unitary D cc δ hC N N' _ _ (Or.inl ⟨_, b, hb, rfl⟩) (Or.inr ⟨_, _, hL, hL', rfl⟩) _ (GlobalTheory.ProdTheta.pullB_mem_ThSp D _ N N' _ b _ hpar hmem hd hth)`. Introduce `h`. Establish `h1 : Iop D (tor0 D cc δ) (LaB D (tor0 D cc δ) b) (La D (tor0 D cc δ) L L') (pullB D (tor0 D cc δ) b (GL3Theta.th0 (lamOf D cc δ) t0)) = fun _ => 0`. Use function extensionality and compare the values at `z`.

Conclude with `(mul_eq_zero.1 (congrFun h z)).resolve_left hκ0`. Rewrite `u3` using `[h1]`. Establish `h2` using `congrFun u3 0`. Simplify using `[Iop, U, pullB, coordB, h0] at h2`.
-/
theorem ne_zero_of_like {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} (hC : Crv D cc δ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) {N N' : ℕ} {L L'} (hL : SD D L) (hL' : SD D L') {G : VC D N N' → ℂ}
    (h : ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G) : G ≠ 0 := by
  obtain ⟨b, κ, hb, ⟨hκQ, hκ1⟩, rfl⟩ := h
  have hG := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨hd, h0, hth⟩ := GlobalTheory.Vacuum.evenTheta_properties_curveLattice D cc δ hC t0 ht
  obtain ⟨-, -, hpar, hmem, -⟩ := GlobalTheory.T.coords_along_orthonormal_realSubfield_basis D hG cc δ N N' _ b hb
  have hκn : ‖κ‖ = 1 := hκ1 (Qbar : IntermediateField ℚ ℂ).val.toRingHom
  have hκ0 : κ ≠ 0 := by rintro rfl; simp at hκn
  obtain ⟨-, -, -, u3⟩ := GlobalTheory.theta_translation_intertwiner_unitary D cc δ hC N N' _ _ (Or.inl ⟨_, b, hb, rfl⟩)
    (Or.inr ⟨_, _, hL, hL', rfl⟩) _ (GlobalTheory.ProdTheta.pullB_mem_ThSp D _ N N' _ b _ hpar hmem hd hth)
  intro h
  have h1 : Iop D (tor0 D cc δ) (LaB D (tor0 D cc δ) b) (La D (tor0 D cc δ) L L')
      (pullB D (tor0 D cc δ) b (GL3Theta.th0 (lamOf D cc δ) t0)) = fun _ => 0 := by
    funext z
    exact (mul_eq_zero.1 (congrFun h z)).resolve_left hκ0
  rw [h1] at u3
  have h2 := congrFun u3 0
  simp [Iop, U, pullB, coordB, h0] at h2

/- English proof (translation)
Introduce `D cc δ hC t0 ht N N' hev e0 he L L' hL hL' c hc`. Establish `hG1` using `(GlobalTheory.InducedType.induced_type D).1`. Establish `s0` using `GlobalTheory.VacuumScalar.sd_of_moves (GlobalTheory.VacuumScalar.moves_one D N)`. Establish `s0'` using `GlobalTheory.VacuumScalar.sd_of_moves (GlobalTheory.VacuumScalar.moves_one D N')`. Establish `k0 : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N')` using `Or.inr ⟨_, _, s0, s0', rfl⟩`.

Establish `k1 : KLat D (tor0 D cc δ) (La D (tor0 D cc δ) L L')` using `Or.inr ⟨_, _, hL, hL', rfl⟩`. Establish `huni` using `GlobalTheory.theta_translation_intertwiner_unitary D cc δ hC N N' _ _ k0 k1`. Establish `hQ` using `(GlobalTheory.ThetaAlgebraic.taylor_algebraic D cc δ hC t0 ht N N' _ _ s0 s0' hev e0 he.2.2.2.1).2.2.2.1 L L' hL hL'`. Establish `hD` using `((GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hG1).2 cc δ hC).1`. Establish `hTh` using `(huni e0 he.1).2.1`.

Express the relevant statement in the definitionally equal form `CoefIn D (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L L') e0) Qbar at hQ`. Establish `hne : Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L L') e0 ≠ 0` using `fun h => ne_zero_of_like hC ht s0 s0' he.2.2.2.1 (by rw [← (huni e0 he.1).2.2.2, h, GlobalTheory.VacuumScalar.Iop_zero])`. Establish `hconj` using `fun ρ => GlobalTheory.ThetaConj.useConj_all D cc δ hC t0 ht N N' _ _ s0 s0' hev e0 he.2.2.2.1 Qbar ρ hD he.2.1`. Use `set G := Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L L') e0 with hGdef`. Choose the witnesses or unpack the hypotheses as in `⟨α₀, hα₀⟩ : ∃ α, TaylorLogMetric.taylor D G α ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Use `hne (funext fun z => ?_)` and prove the remaining obligations. Use `GlobalTheory.EntireTaylor.hasSum_taylor_mono D N N' G hTh.1 z` as an intermediate fact. Simplify using `only [h, zero_mul] at this`.

Conclude with `this.unique hasSum_zero`. Set `φ : D.what₂.Tau → D.host.E →ₐ[ℚ] Qbar` to `fun τ => RingHom.toRatAlgHom { toFun := fun x => ⟨embT D τ x, hD.1 τ x⟩ map_one' := Subtype.ext (map_one _) map_mul' := fun x y => Subtype.ext (map_mul _ x y) map_zero' := Subtype.ext (map_zero _) map_add' := fun x y => Subtype.ext (map_add _ x y) }`. Set `bs` to `Module.finBasis ℚ D.host.E`. Take `⟨M, hM, hfix⟩` from `exists_field (Set.range (fun p : D.what₂.Tau × Fin _ => φ p.1 (bs p.2)) ∪ {⟨_, hD.2.1⟩, ⟨_, hD.2.2⟩, ⟨c, hc⟩, ⟨_, hQ α₀⟩}) ((Set.finite_range _).union (Set.toFinite _))`. Use `⟨M, hM, fun α => ?_⟩` and prove the remaining obligations.

Establish `e1 : TaylorLogMetric.taylor D (c • G) α = c * TaylorLogMetric.taylor D G α` using `GlobalTheory.ThetaConj.taylor_mul D c hTh.1 α`. Rewrite using `[e1]`. Use `mul_mem (hfix ⟨c, hc⟩ fun σ h => h _ (by simp)) (hfix ⟨_, hQ α⟩ fun σ h => ?_)` and prove the remaining obligations. Set `ρ : Qbar →ₐ[ℚ] ℂ` to `Qbar.val.comp (σ : Qbar →ₐ[ℚ] Qbar)`. Establish `hcj : ∀ (x : ℂ) (hx : x ∈ Qbar), cj Qbar ρ x = (σ ⟨x, hx⟩ : ℂ)` using `fun x hx => by`.

Rewrite using `[GlobalTheory.ThetaConj.cj_of_mem _ _ hx]`. Both sides reduce to the same expression. Establish `hlam : lamConj Qbar ρ (lamOf D cc δ) = lamOf D cc δ` using `GlobalTheory.ThetaConj.lamConj_eq_self (GlobalTheory.CurveLattice.lattice_of_curve D hG1 cc δ hC).1 ((hcj _ hD.2.1).trans (congrArg Subtype.val (h _ (by simp)))) ((hcj _ hD.2.2).trans (congrArg Subtype.val (h _ (by simp))))`. Establish `htor : torConj D (tor0 D cc δ) Qbar ρ = tor0 D cc δ`. Establish `: (fun τ x => cj Qbar ρ (embT D τ x)) = fun τ x => embT D τ x`.

Use function extensionality and compare the values at `τ x`. Establish `e : ((σ : Qbar →ₐ[ℚ] Qbar).comp (φ τ)).toLinearMap = (φ τ).toLinearMap` using `bs.ext fun i => h _ (Or.inl ⟨(τ, i), rfl⟩)`. Conclude with `(hcj _ (hD.1 τ x)).trans (congrArg Subtype.val (LinearMap.congr_fun e x))`. Conclude with `congrArg₂ Tor.mk this hlam`. Take `⟨c1, c2, c3⟩` from `hconj ρ`.

Take `⟨sg, hsg, c4⟩` from `c3 L L' hL hL' hQ`. Establish `c5` using `c2 t0 (hlam.symm ▸ ht)`. Rewrite `c1`, `c4`, `c5` using `[htor]`. Establish `u` using `huni _ c1`. Apply the tactic sequence `have hsg0 : sg ≠ 0 := by rcases hsg with rfl | rfl <;> simp`.

Establish `hF : fnConj D Qbar ρ G ∈ ThSp D (tor0 D cc δ) (La D (tor0 D cc δ) L L')` using `c4 ▸ GlobalTheory.InertSign.ThSp_smul sg u.2.1`. Establish `hF0 : fnConj D Qbar ρ G ≠ 0`. Introduce `h0`. Establish `h1` using `(smul_eq_zero.1 (c4.symm.trans h0)).resolve_left hsg0`. Use `ne_zero_of_like hC ht s0 s0' c5 ?_` and prove the remaining obligations.

Rewrite using `[← u.2.2.2]`. Conclude with `(congrArg _ h1).trans (GlobalTheory.VacuumScalar.Iop_zero _ _)`. Take `⟨a, ha⟩` from `(GlobalTheory.ThetaLine.theta_line D hG1 cc δ hC N N' _ k1).1 _ hF _ hTh hne`. Establish `ht'` using `(GlobalTheory.ConjSeries.taylor_fnConj D N N' Qbar ρ G hF.1 hF0).1`. Establish `e2 : ∀ β, (σ ⟨_, hQ β⟩ : ℂ) = a * TaylorLogMetric.taylor D G β` using `fun β => by`.

Rewrite using `[← hcj, ← ht', ha]`. Conclude with `GlobalTheory.ThetaConj.taylor_mul D a hTh.1 β`. Establish `e3` using `e2 α₀`. Rewrite `e3` using `[h _ (by simp)]`. Establish `ha1 : a = 1` using `mul_right_cancel₀ hα₀ (e3.symm.trans (one_mul _).symm)`.

Conclude with `Subtype.ext (by rw [e2, ha1, one_mul])`.
-/
theorem exists_coef_field : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (N N' : ℕ), Even (N * N') → ∀ e0 : VC D N N' → ℂ, oddE0 D cc δ t0 N N' e0 → ∀ (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D L → SD D L' → ∀ c ∈ Qbar, ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ CoefIn D (c • Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L L') e0) M := by
  intro D cc δ hC t0 ht N N' hev e0 he L L' hL hL' c hc
  have hG1 := (GlobalTheory.InducedType.induced_type D).1
  have s0 := GlobalTheory.VacuumScalar.sd_of_moves (GlobalTheory.VacuumScalar.moves_one D N)
  have s0' := GlobalTheory.VacuumScalar.sd_of_moves (GlobalTheory.VacuumScalar.moves_one D N')
  have k0 : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') := Or.inr ⟨_, _, s0, s0', rfl⟩
  have k1 : KLat D (tor0 D cc δ) (La D (tor0 D cc δ) L L') := Or.inr ⟨_, _, hL, hL', rfl⟩
  have huni := GlobalTheory.theta_translation_intertwiner_unitary D cc δ hC N N' _ _ k0 k1
  have hQ := (GlobalTheory.ThetaAlgebraic.taylor_algebraic D cc δ hC t0 ht N N' _ _ s0 s0' hev e0 he.2.2.2.1).2.2.2.1 L L' hL hL'
  have hD := ((GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hG1).2 cc δ hC).1
  have hTh := (huni e0 he.1).2.1
  change CoefIn D (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L L') e0) Qbar at hQ
  have hne : Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L L') e0 ≠ 0 := fun h =>
    ne_zero_of_like hC ht s0 s0' he.2.2.2.1 (by rw [← (huni e0 he.1).2.2.2, h, GlobalTheory.VacuumScalar.Iop_zero])
  have hconj := fun ρ => GlobalTheory.ThetaConj.useConj_all D cc δ hC t0 ht N N' _ _ s0 s0' hev e0 he.2.2.2.1 Qbar ρ hD he.2.1
  set G := Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L L') e0 with hGdef
  obtain ⟨α₀, hα₀⟩ : ∃ α, TaylorLogMetric.taylor D G α ≠ 0 := by
    by_contra h
    push_neg at h
    refine hne (funext fun z => ?_)
    have := GlobalTheory.EntireTaylor.hasSum_taylor_mono D N N' G hTh.1 z
    simp only [h, zero_mul] at this
    exact this.unique hasSum_zero
  let φ : D.what₂.Tau → D.host.E →ₐ[ℚ] Qbar := fun τ =>
    RingHom.toRatAlgHom
      { toFun := fun x => ⟨embT D τ x, hD.1 τ x⟩
        map_one' := Subtype.ext (map_one _)
        map_mul' := fun x y => Subtype.ext (map_mul _ x y)
        map_zero' := Subtype.ext (map_zero _)
        map_add' := fun x y => Subtype.ext (map_add _ x y) }
  let bs := Module.finBasis ℚ D.host.E
  obtain ⟨M, hM, hfix⟩ := exists_field (Set.range (fun p : D.what₂.Tau × Fin _ => φ p.1 (bs p.2)) ∪
    {⟨_, hD.2.1⟩, ⟨_, hD.2.2⟩, ⟨c, hc⟩, ⟨_, hQ α₀⟩}) ((Set.finite_range _).union (Set.toFinite _))
  refine ⟨M, hM, fun α => ?_⟩
  have e1 : TaylorLogMetric.taylor D (c • G) α = c * TaylorLogMetric.taylor D G α := GlobalTheory.ThetaConj.taylor_mul D c hTh.1 α
  rw [e1]
  refine mul_mem (hfix ⟨c, hc⟩ fun σ h => h _ (by simp)) (hfix ⟨_, hQ α⟩ fun σ h => ?_)
  let ρ : Qbar →ₐ[ℚ] ℂ := Qbar.val.comp (σ : Qbar →ₐ[ℚ] Qbar)
  have hcj : ∀ (x : ℂ) (hx : x ∈ Qbar), cj Qbar ρ x = (σ ⟨x, hx⟩ : ℂ) := fun x hx => by
    rw [GlobalTheory.ThetaConj.cj_of_mem _ _ hx]; rfl
  have hlam : lamConj Qbar ρ (lamOf D cc δ) = lamOf D cc δ :=
    GlobalTheory.ThetaConj.lamConj_eq_self (GlobalTheory.CurveLattice.lattice_of_curve D hG1 cc δ hC).1
      ((hcj _ hD.2.1).trans (congrArg Subtype.val (h _ (by simp))))
      ((hcj _ hD.2.2).trans (congrArg Subtype.val (h _ (by simp))))
  have htor : torConj D (tor0 D cc δ) Qbar ρ = tor0 D cc δ := by
    have : (fun τ x => cj Qbar ρ (embT D τ x)) = fun τ x => embT D τ x := by
      funext τ x
      have e : ((σ : Qbar →ₐ[ℚ] Qbar).comp (φ τ)).toLinearMap = (φ τ).toLinearMap :=
        bs.ext fun i => h _ (Or.inl ⟨(τ, i), rfl⟩)
      exact (hcj _ (hD.1 τ x)).trans (congrArg Subtype.val (LinearMap.congr_fun e x))
    exact congrArg₂ Tor.mk this hlam
  obtain ⟨c1, c2, c3⟩ := hconj ρ
  obtain ⟨sg, hsg, c4⟩ := c3 L L' hL hL' hQ
  have c5 := c2 t0 (hlam.symm ▸ ht)
  rw [htor] at c1 c4 c5
  have u := huni _ c1
  have hsg0 : sg ≠ 0 := by rcases hsg with rfl | rfl <;> simp
  have hF : fnConj D Qbar ρ G ∈ ThSp D (tor0 D cc δ) (La D (tor0 D cc δ) L L') :=
    c4 ▸ GlobalTheory.InertSign.ThSp_smul sg u.2.1
  have hF0 : fnConj D Qbar ρ G ≠ 0 := by
    intro h0
    have h1 := (smul_eq_zero.1 (c4.symm.trans h0)).resolve_left hsg0
    refine ne_zero_of_like hC ht s0 s0' c5 ?_
    rw [← u.2.2.2]
    exact (congrArg _ h1).trans (GlobalTheory.VacuumScalar.Iop_zero _ _)
  obtain ⟨a, ha⟩ := (GlobalTheory.ThetaLine.theta_line D hG1 cc δ hC N N' _ k1).1 _ hF _ hTh hne
  have ht' := (GlobalTheory.ConjSeries.taylor_fnConj D N N' Qbar ρ G hF.1 hF0).1
  have e2 : ∀ β, (σ ⟨_, hQ β⟩ : ℂ) = a * TaylorLogMetric.taylor D G β := fun β => by
    rw [← hcj, ← ht', ha]
    exact GlobalTheory.ThetaConj.taylor_mul D a hTh.1 β
  have e3 := e2 α₀
  rw [h _ (by simp)] at e3
  have ha1 : a = 1 := mul_right_cancel₀ hα₀ (e3.symm.trans (one_mul _).symm)
  exact Subtype.ext (by rw [e2, ha1, one_mul])

open GlobalTheory.NormSum.UnramHecke GlobalTheory.VacuumScalar

/- English proof (translation)
Take `⟨κ, hκ, hnorm⟩` from `exists_unitary_extension (((ratio D).comp (incU D)).coprod (intUnits D).subtype) ((infChar D 1)⁻¹.comp (MonoidHom.fst _ _)) (by`. Introduce and unpack `⟨a, u⟩ h`. Establish `h' : ratio D (incU D a) * (u : (AE D)ˣ) = 1` using `h`. Establish `hm : ratio D (incU D a) ∈ intUnits D`. Rewrite using `[eq_inv_of_mul_eq_one_left h']`.

Conclude with `inv_mem u.2`. Use `show (infChar D 1 a)⁻¹ = 1`. Rewrite using `[infChar_eq_one D 1 a hm, inv_one])`. Use the proof step `(by`. Introduce and unpack `⟨a, u⟩`.

Use `show ‖(((infChar D 1 a)⁻¹ : ℂˣ) : ℂ)‖ = 1`. Rewrite using `[Units.val_inv_eq_inv_val, norm_inv, norm_infChar, inv_one])`. Establish `hint : ∀ u, IntU D u → κ u = 1`. Introduce `u hu`. Use `hκ (1, ⟨_, hu⟩)` as an intermediate fact.

Simplify using `using this`. Establish `hint' : ∀ (k : ℤ) u, IntU D u → ((zpowGroupHom k).comp (κ.comp (ratio D))) u = 1`. Introduce `k u hu`. Use `show κ (ratio D u) ^ k = 1`. Rewrite using `[hint _ (show ratio D u ∈ intUnits D from div_mem hu (sgU_mem D hu)), one_zpow]`.

Use `⟨κ, hint, fun N k hN => ⟨ { f := (zpowGroupHom k).comp (κ.comp (ratio D)) n := fun _ => 2 * k unitary := fun x => ?_ cont := ⟨1, one_pos, fun u hu _ => hint' k u hu⟩ aut := fun a => ?_ norm := fun x => ?_ par := fun _ => (even_two_mul k).sub ((Int.even_coe_nat N).2 hN) unr := fun …` and prove the remaining obligations. Use `show ‖((κ (ratio D x) ^ k : ℂˣ) : ℂ)‖ = 1`. Rewrite using `[Units.val_zpow_eq_zpow_val, norm_zpow, hnorm, one_zpow]`. Establish `h1 : κ (ratio D (incU D a)) = (infChar D 1 a)⁻¹`. Use `hκ (a, 1)` as an intermediate fact.

Simplify using `using this`. Use `show ((κ (ratio D (incU D a)) ^ k : ℂˣ) : ℂ) * _ = 1`. Establish `h2 : ∏ τ, (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ^ (2 * k) = ((infChar D 1 a : ℂˣ) : ℂ) ^ k`. Rewrite using `[infChar_val, ← Finset.prod_zpow]`. Conclude with `Finset.prod_congr rfl fun τ _ => by rw [← zpow_mul, mul_one]`.

Rewrite using `[h1, h2, ← Units.val_zpow_eq_zpow_val, ← Units.val_mul, ← mul_zpow, inv_mul_cancel, one_zpow, Units.val_one]`. Use `show κ (ratio D (x * sgU D x)) ^ k = 1`. Rewrite using `[ratio_apply, map_mul (sgU D), sgU_sgU, mul_comm (sgU D x), div_self', map_one, one_zpow]`.
-/
theorem exists_base (D : D7) : ∃ κ : (AE D)ˣ →* ℂˣ, (∀ u, IntU D u → κ u = 1) ∧
    ∀ (N : ℕ) (k : ℤ), Even N → ∃ ψ : HeckeU D N, (∀ τ, ψ.n τ = 2 * k) ∧ ∀ x, ψ.f x = κ (ratio D x) ^ k := by
  obtain ⟨κ, hκ, hnorm⟩ := exists_unitary_extension
    (((ratio D).comp (incU D)).coprod (intUnits D).subtype)
    ((infChar D 1)⁻¹.comp (MonoidHom.fst _ _))
    (by
      rintro ⟨a, u⟩ h
      have h' : ratio D (incU D a) * (u : (AE D)ˣ) = 1 := h
      have hm : ratio D (incU D a) ∈ intUnits D := by
        rw [eq_inv_of_mul_eq_one_left h']; exact inv_mem u.2
      show (infChar D 1 a)⁻¹ = 1
      rw [infChar_eq_one D 1 a hm, inv_one])
    (by
      rintro ⟨a, u⟩
      show ‖(((infChar D 1 a)⁻¹ : ℂˣ) : ℂ)‖ = 1
      rw [Units.val_inv_eq_inv_val, norm_inv, norm_infChar, inv_one])
  have hint : ∀ u, IntU D u → κ u = 1 := by
    intro u hu
    have := hκ (1, ⟨_, hu⟩)
    simpa using this
  have hint' : ∀ (k : ℤ) u, IntU D u → ((zpowGroupHom k).comp (κ.comp (ratio D))) u = 1 := by
    intro k u hu
    show κ (ratio D u) ^ k = 1
    rw [hint _ (show ratio D u ∈ intUnits D from div_mem hu (sgU_mem D hu)), one_zpow]
  refine ⟨κ, hint, fun N k hN => ⟨
          { f := (zpowGroupHom k).comp (κ.comp (ratio D))
            n := fun _ => 2 * k
            unitary := fun x => ?_
            cont := ⟨1, one_pos, fun u hu _ => hint' k u hu⟩
            aut := fun a => ?_
            norm := fun x => ?_
            par := fun _ => (even_two_mul k).sub ((Int.even_coe_nat N).2 hN)
            unr := fun u hu _ => hint' k u hu }, fun _ => rfl, fun _ => rfl⟩⟩
  · show ‖((κ (ratio D x) ^ k : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_zpow_eq_zpow_val, norm_zpow, hnorm, one_zpow]
  · have h1 : κ (ratio D (incU D a)) = (infChar D 1 a)⁻¹ := by
      have := hκ (a, 1)
      simpa using this
    show ((κ (ratio D (incU D a)) ^ k : ℂˣ) : ℂ) * _ = 1
    have h2 : ∏ τ, (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ^ (2 * k) =
        ((infChar D 1 a : ℂˣ) : ℂ) ^ k := by
      rw [infChar_val, ← Finset.prod_zpow]
      exact Finset.prod_congr rfl fun τ _ => by rw [← zpow_mul, mul_one]
    rw [h1, h2, ← Units.val_zpow_eq_zpow_val, ← Units.val_mul, ← mul_zpow, inv_mul_cancel, one_zpow, Units.val_one]
  · show κ (ratio D (x * sgU D x)) ^ k = 1
    rw [ratio_apply, map_mul (sgU D), sgU_sgU, mul_comm (sgU D x), div_self', map_one, one_zpow]

def scal {D : D7} (κ : (AE D)ˣ →* ℂˣ) {N N' : ℕ} (g : GA D N) (g' : GA D N') : ℂˣ :=
  κ (Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D))) ^ ((N' / 2 : ℕ) : ℤ) *
    κ (Matrix.GeneralLinearGroup.det (g' : GL (Fin N') (AE D))) ^ (-((N / 2 : ℕ) : ℤ))

/- English proof (translation)
Take `⟨κ, hint, hψ⟩` from `exists_base D`. Take `⟨ε, hε, a1, a2, h3⟩` from `VacMove.exists_half_idem D`. Establish `h1 : (ε + sgA D ε) * (ε + sgA D ε) = ε + sgA D ε`. Establish `a3 : sgA D ε * sgA D ε = sgA D ε` using `by rw [← map_mul, a1]`. Take the linear combination `a1 + a3 + 2 * a2`.

Establish `h2 : sgA D (ε + sgA D ε) = ε + sgA D ε` using `by rw [map_add, VacMove.sgA_sgA, add_comm]`. Establish `hsol` using `fun (n : ℕ) (g : GA D n) => exists_solution a1 a2 h1 h2 g`. Establish `heO : ε + sgA D ε ∈ OhE D` using `add_mem hε (VacMove.sgA_mem D hε)`. Generalize the expression as in `ε + sgA D ε = e at h1 h2 h3 hsol heO`. Set `P : (AE D)ˣ →* (AE D)ˣ` to `Units.map (cut e h1)`.

Establish `hP : ∀ x, ((P x : (AE D)ˣ) : AE D) = e * x + (1 - e)` using `fun x => by`. Express the relevant statement in the definitionally equal form `e * x + (1 - e) * 1 = _`. Rewrite using `[mul_one]`. Use `⟨κ.comp P, fun u hu => hint _ ⟨?_, ?_⟩, fun z hz => ?_, fun cc δ hc N N' hN hN' e0 he h0 => ?_⟩` and prove the remaining obligations. Rewrite using `[hP]`.

Conclude with `add_mem (mul_mem heO hu.1) (sub_mem (one_mem _) heO)`. Rewrite using `[← map_inv, hP]`. Conclude with `add_mem (mul_mem heO hu.2) (sub_mem (one_mem _) heO)`. Take `⟨ψ, hn, hf⟩` from `hψ 0 1 Even.zero`. Take `⟨b, hb⟩` from `GlobalTheory.RatEqui.exists_root D _ hz`.

Establish `hv` using `GlobalTheory.RatEqui.char_value ψ 1 z b hb (fun _ => 1) (fun τ => by rw [hn]; ring)`. Establish `hz' : incU D z = ratio D (incU D b)`. Rewrite using `[ratio_apply, eq_div_iff_mul_eq']`. Use `ext`. Express the relevant statement in the definitionally equal form `inc D z * sgA D (inc D b) = inc D b`.

Rewrite using `[GlobalTheory.NormSum.PtsMem.sgA_inc, ← map_mul, ← hb]`. Establish `hs : P (sgU D (incU D b)) = sgU D (P (incU D b))`. Use `ext`. Express the relevant statement in the definitionally equal form `_ = sgA D (P (incU D b) : (AE D)ˣ)`. Rewrite using `[hP, hP, map_add, map_mul, map_sub, map_one, h2]`.

Both sides reduce to the same expression. Establish `hsplit : incU D b = P (incU D b) * Units.map (cut (1 - e) (compl_idem h1)) (incU D b)` using `Units.ext (cut_mul_cut e h1 (incU D b : AE D)).1.symm`. Establish `htriv : ψ.f (Units.map (cut (1 - e) (compl_idem h1)) (incU D b)) = 1`. Use `GlobalTheory.InertTrivial.character_trivial_at_inert D _ Even.zero ψ _ fun q hq hi => ?_` and prove the remaining obligations. Use `VacMove.zeroAt_mul D hq ((h3 q hq).2 hi) ((incU D b : AE D) - 1) using 1` and compare the differences between its conclusion and the goal.

Express the relevant statement in the definitionally equal form `(1 - e) * (incU D b : AE D) + (1 - (1 - e)) * 1 - 1 = _`. Expand and normalize the polynomial expressions, which then agree. Establish `: κ (P (incU D z)) = ψ.f (incU D b)` using `by conv_rhs => rw [hsplit, map_mul, htriv, mul_one, hf, zpow_one]`. Rewrite using `[hz', ratio_apply, ratio_apply, map_div P, hs]`. Rewrite using `[MonoidHom.comp_apply, this, ← zpow_one (ψ.f _), hv]`.

Simplify using the standard rewrite rules. Take `⟨ψ, hn, hf⟩` from `hψ N (-((N / 2 : ℕ) : ℤ)) hN`. Take `⟨ψ', hn', hf'⟩` from `hψ N' ((N' / 2 : ℕ) : ℤ) hN'`. Take `⟨W, w1, w2, w3, w4⟩` from `GlobalTheory.FinWeil.exists_weil D cc δ hc N N' hN hN' e0 he h0 ψ ψ'`. Use `⟨W, fun τ => ?_, fun τ => ?_, fun g g' L L' hL hL' => ?_⟩` and prove the remaining obligations.

Rewrite using `[w1, w3, hn]`. Take `⟨k, rfl⟩` from `hN`. Use linear arithmetic over natural numbers and integers. Rewrite using `[w2, w4, hn']`. Take `⟨k, rfl⟩` from `hN'`.

Use linear arithmetic over natural numbers and integers. Take `⟨y, b2, b1, -⟩` from `hsol N g`. Take `⟨y', c2, c1, -⟩` from `hsol N' g'`. Establish `hr : ∀ {n : ℕ} (g : GA D n) (y : (AE D)ˣ), y = Matrix.GeneralLinearGroup.det ((cutG e h1 h2 g : GA D n) : GL (Fin n) (AE D)) * sgU D y → ratio D y = P (Matrix.GeneralLinearGroup.det (g : GL (Fin n) (AE D)))`. Introduce `n g y hy`.

Rewrite using `[ratio_apply, div_eq_iff_eq_mul]`. Use `hy.trans ?_` and prove the remaining obligations. Use `congr 1`. Use `ext`. Rewrite using `[det_cutG, hP]`.

Establish `hsc : scal (κ.comp P) g g' = W.chV.f y' ^ W.ep * W.chV'.f y ^ W.ep'`. Rewrite using `[w1, w2, w3, w4, zpow_one, zpow_one, hf, hf', hr g y b2, hr g' y' c2, mul_comm]`. Both sides reduce to the same expression. Take `⟨c, hO⟩` from `GlobalTheory.VacuumExact.exists_scalar hc he W hL hL'`. Take `⟨Ls, hLs⟩` from `exists_moves (cutG e h1 h2 g)`.

Take `⟨Ls', hLs'⟩` from `exists_moves (cutG e h1 h2 g')`. Take `⟨Li, hLi⟩` from `exists_moves (cutG (1 - e) (compl_idem h1) (compl_fixed h2) g)`. Take `⟨Li', hLi'⟩` from `exists_moves (cutG (1 - e) (compl_idem h1) (compl_fixed h2) g')`. Establish `hs : ∀ {n : ℕ} (k : GA D n), SuppSplit D ((cutG e h1 h2 k : GA D n) : GL (Fin n) (AE D))` using `fun k q hq hi => trivAt_cutG hq _ _ _ k ((h3 q hq).1 hi)`. Establish `hi : ∀ {n : ℕ} (k : GA D n), SuppInert D ((cutG (1 - e) (compl_idem h1) (compl_fixed h2) k : GA D n) : GL (Fin n) (AE D))` using `fun k q hq hi => trivAt_cutG hq _ _ _ k ((h3 q hq).2 hi)`.

Establish `hcc` using `scalar_mul hc he W (cutG_mul e h1 h2 g).1 (cutG_mul e h1 h2 g).2 (cutG_mul e h1 h2 g').1 (cutG_mul e h1 h2 g').2 (hs g) (hs g') (hi g) (hi g') hL hL' hLs hLs' hLi hLi' hO (W.split _ _ y y' Ls Ls' (hs g) (hs g') (fun q hq h => ⟨b1 q hq ((h3 q hq).1 h), c1 q hq ((h3 q hq).1 h)⟩) b2 …`. Rewrite `hcc` using `[Even.neg_one_pow ((hN.mul_right _).add (hN'.mul_right _)), one_mul]`. Use `⟨?_, by rw [hO, hcc, hsc]⟩` and prove the remaining obligations. Rewrite using `[hsc, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val]`. Conclude with `mul_mem (zpow_mem (GlobalTheory.HeckeVal.hecke_values D _ _ _).1.1 _) (zpow_mem (GlobalTheory.HeckeVal.hecke_values D _ _ _).1.1 _)`.
-/
theorem exists_kappa (D : D7) : ∃ κ : (AE D)ˣ →* ℂˣ, (∀ u, IntU D u → κ u = 1) ∧
    (∀ z : D.host.Eˣ, (z : D.host.E) * D.host.conj z = 1 → ((κ (incU D z) : ℂˣ) : ℂ) = ∏ τ, (embT D τ z)⁻¹) ∧
    ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ N N' : ℕ, Even N → Even N' →
      ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), e0 ≠ 0 → ∃ W : WeilO D cc δ N N' e0,
        (∀ τ, 2 * (0 : ℤ) = W.ep * W.chV.n τ + (N : ℤ)) ∧ (∀ τ, 2 * (0 : ℤ) = W.ep' * W.chV'.n τ - (N' : ℤ)) ∧
        ∀ (g : GA D N) (g' : GA D N') L L', Moves D (g : GL (Fin N) (AE D)) L → Moves D (g' : GL (Fin N') (AE D)) L' →
          ((scal κ g g' : ℂˣ) : ℂ) ∈ Qbar ∧ W.Om g g' e0 = ((scal κ g g' : ℂˣ) : ℂ) •
            Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L L') e0 := by
  obtain ⟨κ, hint, hψ⟩ := exists_base D
  obtain ⟨ε, hε, a1, a2, h3⟩ := VacMove.exists_half_idem D
  have h1 : (ε + sgA D ε) * (ε + sgA D ε) = ε + sgA D ε := by
    have a3 : sgA D ε * sgA D ε = sgA D ε := by rw [← map_mul, a1]
    linear_combination a1 + a3 + 2 * a2
  have h2 : sgA D (ε + sgA D ε) = ε + sgA D ε := by rw [map_add, VacMove.sgA_sgA, add_comm]
  have hsol := fun (n : ℕ) (g : GA D n) => exists_solution a1 a2 h1 h2 g
  have heO : ε + sgA D ε ∈ OhE D := add_mem hε (VacMove.sgA_mem D hε)
  generalize ε + sgA D ε = e at h1 h2 h3 hsol heO
  let P : (AE D)ˣ →* (AE D)ˣ := Units.map (cut e h1)
  have hP : ∀ x, ((P x : (AE D)ˣ) : AE D) = e * x + (1 - e) := fun x => by
    change e * x + (1 - e) * 1 = _
    rw [mul_one]
  refine ⟨κ.comp P, fun u hu => hint _ ⟨?_, ?_⟩, fun z hz => ?_, fun cc δ hc N N' hN hN' e0 he h0 => ?_⟩
  · rw [hP]; exact add_mem (mul_mem heO hu.1) (sub_mem (one_mem _) heO)
  · rw [← map_inv, hP]; exact add_mem (mul_mem heO hu.2) (sub_mem (one_mem _) heO)
  · obtain ⟨ψ, hn, hf⟩ := hψ 0 1 Even.zero
    obtain ⟨b, hb⟩ := GlobalTheory.RatEqui.exists_root D _ hz
    have hv := GlobalTheory.RatEqui.char_value ψ 1 z b hb (fun _ => 1) (fun τ => by rw [hn]; ring)
    have hz' : incU D z = ratio D (incU D b) := by
      rw [ratio_apply, eq_div_iff_mul_eq']
      ext
      change inc D z * sgA D (inc D b) = inc D b
      rw [GlobalTheory.NormSum.PtsMem.sgA_inc, ← map_mul, ← hb]
    have hs : P (sgU D (incU D b)) = sgU D (P (incU D b)) := by
      ext
      change _ = sgA D (P (incU D b) : (AE D)ˣ)
      rw [hP, hP, map_add, map_mul, map_sub, map_one, h2]
      rfl
    have hsplit : incU D b = P (incU D b) * Units.map (cut (1 - e) (compl_idem h1)) (incU D b) :=
      Units.ext (cut_mul_cut e h1 (incU D b : AE D)).1.symm
    have htriv : ψ.f (Units.map (cut (1 - e) (compl_idem h1)) (incU D b)) = 1 := by
      refine GlobalTheory.InertTrivial.character_trivial_at_inert D _ Even.zero ψ _ fun q hq hi => ?_
      convert VacMove.zeroAt_mul D hq ((h3 q hq).2 hi) ((incU D b : AE D) - 1) using 1
      change (1 - e) * (incU D b : AE D) + (1 - (1 - e)) * 1 - 1 = _
      ring
    have : κ (P (incU D z)) = ψ.f (incU D b) := by
      conv_rhs => rw [hsplit, map_mul, htriv, mul_one, hf, zpow_one]
      rw [hz', ratio_apply, ratio_apply, map_div P, hs]
    rw [MonoidHom.comp_apply, this, ← zpow_one (ψ.f _), hv]
    simp
  · obtain ⟨ψ, hn, hf⟩ := hψ N (-((N / 2 : ℕ) : ℤ)) hN
    obtain ⟨ψ', hn', hf'⟩ := hψ N' ((N' / 2 : ℕ) : ℤ) hN'
    obtain ⟨W, w1, w2, w3, w4⟩ := GlobalTheory.FinWeil.exists_weil D cc δ hc N N' hN hN' e0 he h0 ψ ψ'
    refine ⟨W, fun τ => ?_, fun τ => ?_, fun g g' L L' hL hL' => ?_⟩
    · rw [w1, w3, hn]; obtain ⟨k, rfl⟩ := hN; omega
    · rw [w2, w4, hn']; obtain ⟨k, rfl⟩ := hN'; omega
    obtain ⟨y, b2, b1, -⟩ := hsol N g
    obtain ⟨y', c2, c1, -⟩ := hsol N' g'
    have hr : ∀ {n : ℕ} (g : GA D n) (y : (AE D)ˣ),
        y = Matrix.GeneralLinearGroup.det ((cutG e h1 h2 g : GA D n) : GL (Fin n) (AE D)) * sgU D y →
        ratio D y = P (Matrix.GeneralLinearGroup.det (g : GL (Fin n) (AE D))) := by
      intro n g y hy
      rw [ratio_apply, div_eq_iff_eq_mul]
      refine hy.trans ?_
      congr 1
      ext
      rw [det_cutG, hP]
    have hsc : scal (κ.comp P) g g' = W.chV.f y' ^ W.ep * W.chV'.f y ^ W.ep' := by
      rw [w1, w2, w3, w4, zpow_one, zpow_one, hf, hf', hr g y b2, hr g' y' c2, mul_comm]
      rfl
    obtain ⟨c, hO⟩ := GlobalTheory.VacuumExact.exists_scalar hc he W hL hL'
    obtain ⟨Ls, hLs⟩ := exists_moves (cutG e h1 h2 g)
    obtain ⟨Ls', hLs'⟩ := exists_moves (cutG e h1 h2 g')
    obtain ⟨Li, hLi⟩ := exists_moves (cutG (1 - e) (compl_idem h1) (compl_fixed h2) g)
    obtain ⟨Li', hLi'⟩ := exists_moves (cutG (1 - e) (compl_idem h1) (compl_fixed h2) g')
    have hs : ∀ {n : ℕ} (k : GA D n), SuppSplit D ((cutG e h1 h2 k : GA D n) : GL (Fin n) (AE D)) :=
      fun k q hq hi => trivAt_cutG hq _ _ _ k ((h3 q hq).1 hi)
    have hi : ∀ {n : ℕ} (k : GA D n),
        SuppInert D ((cutG (1 - e) (compl_idem h1) (compl_fixed h2) k : GA D n) : GL (Fin n) (AE D)) :=
      fun k q hq hi => trivAt_cutG hq _ _ _ k ((h3 q hq).2 hi)
    have hcc := scalar_mul hc he W (cutG_mul e h1 h2 g).1 (cutG_mul e h1 h2 g).2 (cutG_mul e h1 h2 g').1
      (cutG_mul e h1 h2 g').2 (hs g) (hs g') (hi g) (hi g') hL hL' hLs hLs' hLi hLi' hO
      (W.split _ _ y y' Ls Ls' (hs g) (hs g')
        (fun q hq h => ⟨b1 q hq ((h3 q hq).1 h), c1 q hq ((h3 q hq).1 h)⟩) b2 c2 hLs hLs')
      (GlobalTheory.InertSign.vacuum_inert D cc δ hc N N' (hN.mul_right N') e0 he W _ _ Li Li' (hi g) (hi g') hLi hLi')
    rw [Even.neg_one_pow ((hN.mul_right _).add (hN'.mul_right _)), one_mul] at hcc
    refine ⟨?_, by rw [hO, hcc, hsc]⟩
    rw [hsc, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val]
    exact mul_mem (zpow_mem (GlobalTheory.HeckeVal.hecke_values D _ _ _).1.1 _) (zpow_mem (GlobalTheory.HeckeVal.hecke_values D _ _ _).1.1 _)

/- English proof (translation)
Take `⟨i1, i2, i3⟩` from `idele_ideal_laws D`. Set `χ : IdE D → ℂ` to `fun 𝔞 => if h : ∃ u : (AE D)ˣ, ∀ a, a ∈ 𝔞 ↔ ((u⁻¹ : (AE D)ˣ) : AE D) * inc D a ∈ OhE D then ((κ h.choose : ℂˣ) : ℂ) else 0`. Establish `hχ : ∀ (u : (AE D)ˣ) (𝔞 : IdE D), (∀ a, a ∈ 𝔞 ↔ ((u⁻¹ : (AE D)ˣ) : AE D) * inc D a ∈ OhE D) → χ 𝔞 = ((κ u : ℂˣ) : ℂ)`. Introduce `u 𝔞 hu`. Establish `h : ∃ u : (AE D)ˣ, ∀ a, a ∈ 𝔞 ↔ ((u⁻¹ : (AE D)ˣ) : AE D) * inc D a ∈ OhE D` using `⟨u, hu⟩`.

Use `h1 _ (i2 h.choose u fun a => (h.choose_spec a).symm.trans (hu a))` as an intermediate fact. Rewrite `this` using `[map_mul, map_inv, mul_inv_eq_one]`. Simplify using `only [χ, dif_pos h, this]`. Use `⟨χ, ⟨fun 𝔞 𝔟 ha hb => ?_, fun z => ?_⟩, fun n g₁ g₂ L₁ L₂ m₁ m₂ => hχ _ _ (mem_detId_iff D n _ _ L₁ L₂ m₁ m₂)⟩` and prove the remaining obligations. Take `⟨u, hu⟩` from `i3 𝔞 ha`.

Take `⟨v, hv⟩` from `i3 𝔟 hb`. Rewrite using `[hχ _ _ (i1 u v 𝔞 𝔟 hu hv), hχ _ _ hu, hχ _ _ hv, map_mul, Units.val_mul]`. Use `letI := D.host.cmStar`. Establish `hz : (z : D.host.E) * D.host.conj z = 1`. Rewrite using `[← AdLattice.star_eq_conj]`.

Conclude with `z.2.2`. Establish `hz0 : (z : D.host.E) ≠ 0` using `left_ne_zero_of_mul_eq_one hz`. Rewrite using `[hχ (incU D (Units.mk0 _ hz0)), h2 _ hz]`. Both sides reduce to the same expression. Introduce `a`.

Rewrite using `[← map_inv]`. Express the relevant statement in the definitionally equal form `_ ↔ inc D (z : D.host.E)⁻¹ * inc D a ∈ OhE D`. Rewrite using `[← map_mul, GlobalTheory.HeckeVal.inc_mem_iff, Submodule.mem_span_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, rfl⟩`.

Rewrite using `[Algebra.smul_def, mul_comm, mul_inv_cancel_right₀ hz0]`. Conclude with `b.isIntegral_coe`. Introduce `h`. Use `⟨⟨_, h⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(z : D.host.E)⁻¹ * a * z = a`.

Clear the denominators using the available nonvanishing facts.
-/
theorem exists_chi (D : D7) (κ : (AE D)ˣ →* ℂˣ) (h1 : ∀ u, IntU D u → κ u = 1)
    (h2 : ∀ z : D.host.Eˣ, (z : D.host.E) * D.host.conj z = 1 → ((κ (incU D z) : ℂˣ) : ℂ) = ∏ τ, (embT D τ z)⁻¹) :
    ∃ χ : IdE D → ℂ, IsChi D χ ∧ ∀ (n : ℕ) (g₁ g₂ : GA D n) L₁ L₂, Moves D (g₁ : GL (Fin n) (AE D)) L₁ →
      Moves D (g₂ : GL (Fin n) (AE D)) L₂ →
      χ (detId D L₁ L₂) = ((κ (Matrix.GeneralLinearGroup.det ((g₁⁻¹ * g₂ : GA D n) : GL (Fin n) (AE D))) : ℂˣ) : ℂ) := by
  obtain ⟨i1, i2, i3⟩ := idele_ideal_laws D
  let χ : IdE D → ℂ := fun 𝔞 =>
    if h : ∃ u : (AE D)ˣ, ∀ a, a ∈ 𝔞 ↔ ((u⁻¹ : (AE D)ˣ) : AE D) * inc D a ∈ OhE D then ((κ h.choose : ℂˣ) : ℂ) else 0
  have hχ : ∀ (u : (AE D)ˣ) (𝔞 : IdE D), (∀ a, a ∈ 𝔞 ↔ ((u⁻¹ : (AE D)ˣ) : AE D) * inc D a ∈ OhE D) →
      χ 𝔞 = ((κ u : ℂˣ) : ℂ) := by
    intro u 𝔞 hu
    have h : ∃ u : (AE D)ˣ, ∀ a, a ∈ 𝔞 ↔ ((u⁻¹ : (AE D)ˣ) : AE D) * inc D a ∈ OhE D := ⟨u, hu⟩
    have := h1 _ (i2 h.choose u fun a => (h.choose_spec a).symm.trans (hu a))
    rw [map_mul, map_inv, mul_inv_eq_one] at this
    simp only [χ, dif_pos h, this]
  refine ⟨χ, ⟨fun 𝔞 𝔟 ha hb => ?_, fun z => ?_⟩, fun n g₁ g₂ L₁ L₂ m₁ m₂ => hχ _ _ (mem_detId_iff D n _ _ L₁ L₂ m₁ m₂)⟩
  · obtain ⟨u, hu⟩ := i3 𝔞 ha
    obtain ⟨v, hv⟩ := i3 𝔟 hb
    rw [hχ _ _ (i1 u v 𝔞 𝔟 hu hv), hχ _ _ hu, hχ _ _ hv, map_mul, Units.val_mul]
  · letI := D.host.cmStar
    have hz : (z : D.host.E) * D.host.conj z = 1 := by
      rw [← AdLattice.star_eq_conj]; exact z.2.2
    have hz0 : (z : D.host.E) ≠ 0 := left_ne_zero_of_mul_eq_one hz
    rw [hχ (incU D (Units.mk0 _ hz0)), h2 _ hz]
    · rfl
    intro a
    rw [← map_inv]
    change _ ↔ inc D (z : D.host.E)⁻¹ * inc D a ∈ OhE D
    rw [← map_mul, GlobalTheory.HeckeVal.inc_mem_iff, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨b, rfl⟩
      rw [Algebra.smul_def, mul_comm, mul_inv_cancel_right₀ hz0]
      exact b.isIntegral_coe
    · intro h
      refine ⟨⟨_, h⟩, ?_⟩
      change (z : D.host.E)⁻¹ * a * z = a
      field_simp

/- English proof (translation)
Take `⟨Lt, h1, -, -, h4, -⟩` from `exists_lattice_of_adelic_point D n`. Establish `hu` using `mul_eq_one_comm.1 ((mem_ratG_intG D n).2.2.2.1 γA γ h)`. Establish `hu'` using `(mem_ratG_intG D n).2.2.2.1 γA γ h`. Rewrite using `[GlobalTheory.InertSign.moves_unique hL (h1 g).1]`. Introduce `x`.

Rewrite using `[← (h1 (γA * g)).1 x]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `(h4 γA g γ h y).1 hy`. Introduce `hx`.

Establish `e : γ.mulVec ((γ.map D.host.conj).transpose.mulVec x) = x`. Rewrite using `[Matrix.mulVec_mulVec, hu', Matrix.one_mulVec]`. Conclude with `⟨_, (h4 γA g γ h _).2 (e.symm ▸ hx), e⟩`.
-/
theorem moves_smulLat {D : D7} {n : ℕ} {γA g : GA D n} {γ : Matrix (Fin n) (Fin n) D.host.E} {L}
    (h : IsRat D (γA : GL (Fin n) (AE D)) γ) (hL : Moves D (g : GL (Fin n) (AE D)) L) :
    letI := D.host.cmStar
    Moves D ((γA * g : GA D n) : GL (Fin n) (AE D)) (SDLat.smulLat γ L) := by
  obtain ⟨Lt, h1, -, -, h4, -⟩ := exists_lattice_of_adelic_point D n
  have hu := mul_eq_one_comm.1 ((mem_ratG_intG D n).2.2.2.1 γA γ h)
  have hu' := (mem_ratG_intG D n).2.2.2.1 γA γ h
  rw [GlobalTheory.InertSign.moves_unique hL (h1 g).1]
  intro x
  rw [← (h1 (γA * g)).1 x]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (h4 γA g γ h y).1 hy
  · intro hx
    have e : γ.mulVec ((γ.map D.host.conj).transpose.mulVec x) = x := by
      rw [Matrix.mulVec_mulVec, hu', Matrix.one_mulVec]
    exact ⟨_, (h4 γA g γ h _).2 (e.symm ▸ hx), e⟩

end GlobalTheory.TrueTheta
