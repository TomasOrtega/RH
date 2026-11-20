import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FsOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableProdPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtalePolynomialSubstitution
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleAffinePolynomialCoordsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernRealClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointsMapHolomorphicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormOneAddMulSmulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasPullbackEqChartExpression
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormPullbackHolomorphicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityPullbackEqNormSqDetMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDensityPushforwardIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCellFrameOfSpans
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleHermitianLinePullbackForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReprEqZeroOfCardNe
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open GlobalTheory.Points
open scoped Classical ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FibLoc

open Set Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open GlobalTheory.FibTriv (prodPt basePt)
open scoped ENNReal ComplexConjugate

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, Subalgebra.coe_mul, Subalgebra.coe_mul, map_mul, h, ih]`.
-/
theorem pull_prod {n m : ℕ} (L : V n →L[ℂ] V m) {ι : Type} (s : Finset ι) (f : ι → Ev m) (g : ι → Ev n)
    (h : ∀ a, pull L (f a : Alt m) = g a) : pull L ((∏ a ∈ s, f a : Ev m) : Alt m) = (∏ a ∈ s, g a : Ev n) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, Subalgebra.coe_mul, Subalgebra.coe_mul, map_mul, h, ih]

/- English proof (translation)
Use `Subtype.ext ?_` and prove the remaining obligations. Break down `h with rfl | rfl` into its components or cases. Use `Subalgebra.mem_center_iff.1 (sym (a, b)).2 (dz a)` as an intermediate fact. Express the relevant statement in the definitionally equal form `(sym (a, b) : Alt n) * (dz a * dzb a) = 0`. Rewrite using `[← mul_assoc, ← this]`.

Express the relevant statement in the definitionally equal form `dz a * (dz a * dzb b) * dzb a = 0`. Rewrite using `[← mul_assoc, dz, ExteriorAlgebra.ι_sq_zero, zero_mul, zero_mul]`. Use `Subalgebra.mem_center_iff.1 (sym (b, b)).2 (dzb b)` as an intermediate fact. Express the relevant statement in the definitionally equal form `dz a * dzb b * (sym (b, b) : Alt n) = 0`. Rewrite using `[mul_assoc, this]`.

Express the relevant statement in the definitionally equal form `dz a * (dz b * dzb b * dzb b) = 0`. Rewrite using `[mul_assoc, dzb, ExteriorAlgebra.ι_sq_zero, mul_zero, mul_zero]`.
-/
theorem sym_mul_sym {n : ℕ} {a b c : Fin n} (h : a = c ∨ b = c) : (sym (a, b) * sym (c, c) : Ev n) = 0 := by
  refine Subtype.ext ?_
  rcases h with rfl | rfl
  · have := Subalgebra.mem_center_iff.1 (sym (a, b)).2 (dz a)
    change (sym (a, b) : Alt n) * (dz a * dzb a) = 0
    rw [← mul_assoc, ← this]
    change dz a * (dz a * dzb b) * dzb a = 0
    rw [← mul_assoc, dz, ExteriorAlgebra.ι_sq_zero, zero_mul, zero_mul]
  · have := Subalgebra.mem_center_iff.1 (sym (b, b)).2 (dzb b)
    change dz a * dzb b * (sym (b, b) : Alt n) = 0
    rw [mul_assoc, this]
    change dz a * (dz b * dzb b * dzb b) = 0
    rw [mul_assoc, dzb, ExteriorAlgebra.ι_sq_zero, mul_zero, mul_zero]

variable {d : ℕ} (L : V (d + 1) →L[ℂ] V d) (hL : ∀ v a, L v a = v a.castSucc)

include hL in

/- English proof (translation)
Use `pull_prod L _ _ _ fun a => ?_` and prove the remaining obligations. Establish `e (b : Fin (d + 1)) : L (coordVec b) a = if b = a.castSucc then 1 else 0`. Rewrite using `[hL]`. Simplify using `[coordVec, EuclideanSpace.single_apply, eq_comm]`. Rewrite using `[Subalgebra.coe_smul, Subalgebra.coe_smul, map_smul]`.

Use `congr 1`. Express the relevant statement in the definitionally equal form `pull L (dz a * dzb a) = dz _ * dzb _`. Rewrite using `[map_mul, (pull_dz L a).1, (pull_dz L a).2]`. Simplify using `[e, apply_ite]`.
-/
theorem pull_vol : pull L (vol d : Alt d) =
    (∏ a : Fin d, (Complex.I / 2) • sym (a.castSucc, a.castSucc) : Ev (d + 1)) := by
  refine pull_prod L _ _ _ fun a => ?_
  have e (b : Fin (d + 1)) : L (coordVec b) a = if b = a.castSucc then 1 else 0 := by
    rw [hL]; simp [coordVec, EuclideanSpace.single_apply, eq_comm]
  rw [Subalgebra.coe_smul, Subalgebra.coe_smul, map_smul]
  congr 1
  change pull L (dz a * dzb a) = dz _ * dzb _
  rw [map_mul, (pull_dz L a).1, (pull_dz L a).2]
  simp [e, apply_ite]

/- English proof (translation)
Take `⟨c, hc, e⟩` from `vol_eq d`. Establish `hv : (bas d).repr (vol d : Alt d) Finset.univ = c` using `by simp [e]`. Use `conv_lhs => rw [← (bas d).sum_repr β]`. Rewrite using `[map_sum, Finset.mul_sum, dens, map_sum, Finsupp.finset_sum_apply, Finset.sum_eq_single Finset.univ _ (by simp)]`. Simplify using `only [dens, hv, e, map_smul, mul_smul_comm, Finsupp.smul_apply, smul_eq_mul, Module.Basis.repr_self, Finsupp.single_eq_same]`.

Clear the denominators using the available nonvanishing facts. Introduce `S _ hS`. Establish `hc : S.card < d + d` using `by simpa using Finset.card_lt_card (Finset.ssubset_univ_iff.2 hS)`. Establish `hm : pull L (bas d S) ∈ ⋀[ℂ]^S.card (Fin (d + 1) ⊕ Fin (d + 1) → ℂ)`. Rewrite using `[bas, ExteriorAlgebra.basis_apply, pull, ExteriorAlgebra.map_apply_ιMulti, ← exteriorPower.ιMulti_apply_coe]`.

Conclude with `Subtype.prop _`. Establish `hm' : (sym x : Alt (d + 1)) * pull L (bas d S) ∈ ⋀[ℂ]^(S.card + 1 + 1) (Fin (d + 1) ⊕ Fin (d + 1) → ℂ)`. Express the relevant statement in the definitionally equal form `dz _ * dzb _ * _ ∈ LinearMap.range _ ^ _`. Rewrite using `[pow_succ', pow_succ', mul_assoc]`. Conclude with `Submodule.mul_mem_mul ⟨_, rfl⟩ (Submodule.mul_mem_mul ⟨_, rfl⟩ hm)`.

Establish `h0 : (bas (d + 1)).repr ((sym x : Alt (d + 1)) * pull L (bas d S)) Finset.univ = 0` using `exterior_repr_univ_of_mem _ (by omega) hm'`. Rewrite using `[map_smul, mul_smul_comm, map_smul, Finsupp.smul_apply, h0, smul_zero]`.
-/
theorem dens_sym_mul_pull (x : Fin (d + 1) × Fin (d + 1)) (β : Alt d) :
    dens ((sym x : Alt (d + 1)) * pull L β) = dens ((sym x : Alt (d + 1)) * pull L (vol d : Alt d)) * dens β := by
  obtain ⟨c, hc, e⟩ := vol_eq d
  have hv : (bas d).repr (vol d : Alt d) Finset.univ = c := by simp [e]
  conv_lhs => rw [← (bas d).sum_repr β]
  rw [map_sum, Finset.mul_sum, dens, map_sum, Finsupp.finset_sum_apply, Finset.sum_eq_single Finset.univ _ (by simp)]
  · simp only [dens, hv, e, map_smul, mul_smul_comm, Finsupp.smul_apply, smul_eq_mul, Module.Basis.repr_self,
      Finsupp.single_eq_same]
    field_simp
  · intro S _ hS
    have hc : S.card < d + d := by simpa using Finset.card_lt_card (Finset.ssubset_univ_iff.2 hS)
    have hm : pull L (bas d S) ∈ ⋀[ℂ]^S.card (Fin (d + 1) ⊕ Fin (d + 1) → ℂ) := by
      rw [bas, ExteriorAlgebra.basis_apply, pull, ExteriorAlgebra.map_apply_ιMulti, ← exteriorPower.ιMulti_apply_coe]
      exact Subtype.prop _
    have hm' : (sym x : Alt (d + 1)) * pull L (bas d S) ∈ ⋀[ℂ]^(S.card + 1 + 1) (Fin (d + 1) ⊕ Fin (d + 1) → ℂ) := by
      change dz _ * dzb _ * _ ∈ LinearMap.range _ ^ _
      rw [pow_succ', pow_succ', mul_assoc]
      exact Submodule.mul_mem_mul ⟨_, rfl⟩ (Submodule.mul_mem_mul ⟨_, rfl⟩ hm)
    have h0 : (bas (d + 1)).repr ((sym x : Alt (d + 1)) * pull L (bas d S)) Finset.univ = 0 :=
      exterior_repr_univ_of_mem _ (by omega) hm'
    rw [map_smul, mul_smul_comm, map_smul, Finsupp.smul_apply, h0, smul_zero]

include hL in

/- English proof (translation)
Establish `key (a b : Fin (d + 1)) : dens ((sym (a, b) : Alt (d + 1)) * pull L (vol d : Alt d)) = if a = Fin.last d ∧ b = Fin.last d then 2 / Complex.I else 0`. Rewrite using `[pull_vol L hL, ← Subalgebra.coe_mul]`. Use `split_ifs with h`. Take `⟨rfl, rfl⟩` from `h`. Establish `: (sym (Fin.last d, Fin.last d) * ∏ a : Fin d, (Complex.I / 2) • sym (a.castSucc, a.castSucc) : Ev (d + 1)) = (2 / Complex.I) • vol (d + 1)`.

Rewrite using `[vol, Fin.prod_univ_castSucc, mul_smul_comm, smul_smul, mul_comm (sym _)]`. Clear the denominators using the available nonvanishing facts. Simplify using the standard rewrite rules. Rewrite using `[this, Subalgebra.coe_smul]`. Use `dens_vol (d + 1)` as an intermediate fact.

Simplify using `only [dens, map_smul, Finsupp.smul_apply, smul_eq_mul] at this ⊢`. Rewrite using `[mul_div_assoc, this, mul_one]`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c : Fin d, a = c.castSucc ∨ b = c.castSucc := by`. Distinguish the cases in `ha : a = Fin.last d`. Take `⟨c, rfl⟩` from `Fin.exists_castSucc_eq.2 fun hb : b = Fin.last d => h ⟨ha, hb⟩`.

Conclude with `⟨c, .inr rfl⟩`. Take `⟨c, rfl⟩` from `Fin.exists_castSucc_eq.2 ha`. Conclude with `⟨c, .inl rfl⟩`. Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ c), ← mul_assoc, mul_smul_comm, sym_mul_sym hc]`. Simplify using `[dens]`.

Establish `hs (a b : Fin (d + 1)) (t : ℂ) : dens (t • ((sym (a, b) : Alt (d + 1)) * pull L β)) = t * ((if a = Fin.last d ∧ b = Fin.last d then 2 / Complex.I else 0) * dens β)`. Rewrite using `[← key, ← dens_sym_mul_pull]`. Simplify using `only [dens, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_div_assoc]`. Establish `hsum {ι : Type} (s : Finset ι) (f : ι → Alt (d + 1)) : dens (∑ i ∈ s, f i) = ∑ i ∈ s, dens (f i)`. Simplify using `only [dens, map_sum, Finsupp.finset_sum_apply, Finset.sum_div]`.

Simplify using `only [ofValues, AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_smul, Finset.sum_mul, smul_mul_assoc, hsum, hs, ite_and]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dens_ofValues_mul_pull (α : V (d + 1) → V (d + 1) → ℂ) (β : Alt d) :
    dens ((ofValues α : Alt (d + 1)) * pull L β) =
      2 / Complex.I * α (coordVec (Fin.last d)) (coordVec (Fin.last d)) * dens β := by
  have key (a b : Fin (d + 1)) : dens ((sym (a, b) : Alt (d + 1)) * pull L (vol d : Alt d)) =
      if a = Fin.last d ∧ b = Fin.last d then 2 / Complex.I else 0 := by
    rw [pull_vol L hL, ← Subalgebra.coe_mul]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      have : (sym (Fin.last d, Fin.last d) * ∏ a : Fin d, (Complex.I / 2) • sym (a.castSucc, a.castSucc) : Ev (d + 1)) =
          (2 / Complex.I) • vol (d + 1) := by
        rw [vol, Fin.prod_univ_castSucc, mul_smul_comm, smul_smul, mul_comm (sym _)]
        field_simp
        simp
      rw [this, Subalgebra.coe_smul]
      have := dens_vol (d + 1)
      simp only [dens, map_smul, Finsupp.smul_apply, smul_eq_mul] at this ⊢
      rw [mul_div_assoc, this, mul_one]
    · obtain ⟨c, hc⟩ : ∃ c : Fin d, a = c.castSucc ∨ b = c.castSucc := by
        by_cases ha : a = Fin.last d
        · obtain ⟨c, rfl⟩ := Fin.exists_castSucc_eq.2 fun hb : b = Fin.last d => h ⟨ha, hb⟩
          exact ⟨c, .inr rfl⟩
        · obtain ⟨c, rfl⟩ := Fin.exists_castSucc_eq.2 ha
          exact ⟨c, .inl rfl⟩
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ c), ← mul_assoc, mul_smul_comm, sym_mul_sym hc]
      simp [dens]
  have hs (a b : Fin (d + 1)) (t : ℂ) : dens (t • ((sym (a, b) : Alt (d + 1)) * pull L β)) =
      t * ((if a = Fin.last d ∧ b = Fin.last d then 2 / Complex.I else 0) * dens β) := by
    rw [← key, ← dens_sym_mul_pull]
    simp only [dens, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_div_assoc]
  have hsum {ι : Type} (s : Finset ι) (f : ι → Alt (d + 1)) : dens (∑ i ∈ s, f i) = ∑ i ∈ s, dens (f i) := by
    simp only [dens, map_sum, Finsupp.finset_sum_apply, Finset.sum_div]
  simp only [ofValues, AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_smul, Finset.sum_mul, smul_mul_assoc, hsum, hs,
    ite_and]
  simp
  ring

/- English proof (translation)
Establish `h1` using `Complex.pos_iff.1 (hG.diag_pos (i := 1))`. Establish `h0` using `Complex.pos_iff.1 (hG.diag_pos (i := 0))`. Establish `h10 : G 1 0 = conj (G 0 1)` using `(hG.1.apply 1 0).symm`. Establish `e1 : G 1 1 = ((G 1 1).re : ℂ)` using `Complex.ext (by simp) (by simp [← h1.2])`. Establish `e0 : G 0 0 = ((G 0 0).re : ℂ)` using `Complex.ext (by simp) (by simp [← h0.2])`.

Establish `hne : (G 1 1).re ≠ 0` using `h1.1.ne'`. Rewrite using `[FibCos.nrm, Matrix.det_fin_two, h10, e1, e0]`. Generalize the expression as in `(G 1 1).re = s at *`. Simplify using `only [Complex.sq_norm, Complex.normSq_apply, Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.sub_re, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem nrm_eq {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) (x : ℂ) :
    FibCos.nrm G x = (‖x + G 0 1 / G 1 1‖ ^ 2 + G.det.re / (G 1 1).re ^ 2) * (G 1 1).re := by
  have h1 := Complex.pos_iff.1 (hG.diag_pos (i := 1))
  have h0 := Complex.pos_iff.1 (hG.diag_pos (i := 0))
  have h10 : G 1 0 = conj (G 0 1) := (hG.1.apply 1 0).symm
  have e1 : G 1 1 = ((G 1 1).re : ℂ) := Complex.ext (by simp) (by simp [← h1.2])
  have e0 : G 0 0 = ((G 0 0).re : ℂ) := Complex.ext (by simp) (by simp [← h0.2])
  have hne : (G 1 1).re ≠ 0 := h1.1.ne'
  rw [FibCos.nrm, Matrix.det_fin_two, h10, e1, e0]
  generalize (G 1 1).re = s at *
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.sub_re, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  field_simp
  ring

/- English proof (translation)
Establish `h1 : 0 < (G 1 1).re` using `(Complex.pos_iff.1 (hG.diag_pos (i := 1))).1`. Establish `hd : 0 < G.det.re` using `(Complex.pos_iff.1 hG.det_pos).1`. Rewrite using `[nrm_eq hG]`. Check the signs of the components of the expression.
-/
theorem nrm_pos {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) (x : ℂ) : 0 < FibCos.nrm G x := by
  have h1 : 0 < (G 1 1).re := (Complex.pos_iff.1 (hG.diag_pos (i := 1))).1
  have hd : 0 < G.det.re := (Complex.pos_iff.1 hG.det_pos).1
  rw [nrm_eq hG]
  positivity

/- English proof (translation)
Establish `h1 : 0 < (G 1 1).re` using `(Complex.pos_iff.1 (hG.diag_pos (i := 1))).1`. Establish `hd : 0 < G.det.re` using `(Complex.pos_iff.1 hG.det_pos).1`. Establish `hp (x : ℂ) : 0 < ‖x + G 0 1 / G 1 1‖ ^ 2 + G.det.re / (G 1 1).re ^ 2` using `by positivity`. Establish `hφ : ContDiffAt ℂ 2 (fun x : ℂ => x + G 0 1 / G 1 1) x` using `by fun_prop`. Establish `e : (fun x => Real.log (FibCos.nrm G x)) = fun x => Real.log (‖x + G 0 1 / G 1 1‖ ^ 2 + G.det.re / (G 1 1).re ^ 2) + Real.log (G 1 1).re`.

Use function extensionality and compare the values at `fun x => by rw [nrm_eq hG, Real.log_mul (hp x).ne' h1.ne']`. Establish `hf : fderiv ℂ (fun x : ℂ => x + G 0 1 / G 1 1) x 1 = 1` using `by simp`. Rewrite using `[e, leviForm_add_const _ (contDiffAt_log_normSq_add_comp hφ (hp x).ne'), leviForm_log_normSq_add_comp hφ (hp x).ne', hf, nrm_eq hG]`. Use `(hp x).ne'` as an intermediate fact. Generalize the expression as in `x + G 0 1 / G 1 1 = z at *`.

Establish `h' : ((‖z‖ ^ 2 + G.det.re / (G 1 1).re ^ 2 : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast this`. Simplify using `only [inner, Complex.star_def, map_one, one_mul, mul_one, Complex.conj_mul']`. Rewrite using `[← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_div, ← Complex.ofReal_div, ← Complex.ofReal_sub]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem leviForm_log_nrm {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) (x : ℂ) :
    leviForm (fun x => Real.log (FibCos.nrm G x)) x 1 1 = ((G.det.re / FibCos.nrm G x ^ 2 : ℝ) : ℂ) := by
  have h1 : 0 < (G 1 1).re := (Complex.pos_iff.1 (hG.diag_pos (i := 1))).1
  have hd : 0 < G.det.re := (Complex.pos_iff.1 hG.det_pos).1
  have hp (x : ℂ) : 0 < ‖x + G 0 1 / G 1 1‖ ^ 2 + G.det.re / (G 1 1).re ^ 2 := by positivity
  have hφ : ContDiffAt ℂ 2 (fun x : ℂ => x + G 0 1 / G 1 1) x := by fun_prop
  have e : (fun x => Real.log (FibCos.nrm G x)) = fun x =>
      Real.log (‖x + G 0 1 / G 1 1‖ ^ 2 + G.det.re / (G 1 1).re ^ 2) + Real.log (G 1 1).re :=
    funext fun x => by rw [nrm_eq hG, Real.log_mul (hp x).ne' h1.ne']
  have hf : fderiv ℂ (fun x : ℂ => x + G 0 1 / G 1 1) x 1 = 1 := by simp
  rw [e, leviForm_add_const _ (contDiffAt_log_normSq_add_comp hφ (hp x).ne'),
    leviForm_log_normSq_add_comp hφ (hp x).ne', hf, nrm_eq hG]
  have := (hp x).ne'
  generalize x + G 0 1 / G 1 1 = z at *
  have h' : ((‖z‖ ^ 2 + G.det.re / (G 1 1).re ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast this
  simp only [inner, Complex.star_def, map_one, one_mul, mul_one, Complex.conj_mul']
  rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_div, ← Complex.ofReal_div,
    ← Complex.ofReal_sub]
  congr 1
  field_simp
  ring

/- English proof (translation)
Establish `h1 : MeasurePreserving (fun z : V d × ℂ => (z.2, z.1.ofLp)) volume volume` using `(Measure.measurePreserving_swap (μ := (volume : Measure (Fin d → ℂ))) (ν := (volume : Measure ℂ))).comp ((volume_preserving_ofLp_complex (Fin d)).prod (MeasurePreserving.id volume))`. Establish `h2` using `(volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℂ) (Fin.last d)).symm`. Establish `h5 : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin (d + 1) → ℂ)) volume volume` using `MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin (d + 1) → ℂ)).symm (volume_preserving_ofLp_complex (Fin (d + 1)))`. Use `h5.comp (h2.comp h1) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `z`.

Simplify using `[prodPt, MeasurableEquiv.piFinSuccAbove, Fin.insertNth_last', Fin.snocEquiv]`.
-/
theorem measurePreserving_prodPt (d : ℕ) :
    MeasurePreserving (fun z : V d × ℂ => prodPt z.1 z.2) volume volume := by
  have h1 : MeasurePreserving (fun z : V d × ℂ => (z.2, z.1.ofLp)) volume volume :=
    (Measure.measurePreserving_swap (μ := (volume : Measure (Fin d → ℂ))) (ν := (volume : Measure ℂ))).comp
      ((volume_preserving_ofLp_complex (Fin d)).prod (MeasurePreserving.id volume))
  have h2 := (volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℂ) (Fin.last d)).symm
  have h5 : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin (d + 1) → ℂ)) volume volume :=
    MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin (d + 1) → ℂ)).symm
      (volume_preserving_ofLp_complex (Fin (d + 1)))
  convert h5.comp (h2.comp h1) using 1
  funext z
  simp [prodPt, MeasurableEquiv.piFinSuccAbove, Fin.insertNth_last', Fin.snocEquiv]

/- English proof (translation)
Establish `hK' : Measurable fun b => ∫⁻ x, K b x` using `hK.lintegral_prod_right`. Establish `hIm` using `ChartGlue.measurableSet_image e hS hSe`. Establish `hIt : e '' S ⊆ e.target` using `by rintro _ ⟨b, hb, rfl⟩; exact e.map_source (hSe hb)`. Establish `hsy : AEMeasurable e.symm (volume.restrict e.target)` using `e.continuousOn_symm.aemeasurable e.open_target.measurableSet`. Establish `hbc : Continuous (basePt (d` using `d)) := FibTriv.differentiable_basePt.continuous`.

Establish `hR : ∫⁻ b in S, (∫⁻ x, K b x) ∂ChartGlue.chartMeas e ρ = ∫⁻ z in e '' S, (∫⁻ x, K (e.symm z) x) * ρ (e.symm z)`. Rewrite using `[← lintegral_indicator hS, ChartGlue.chartMeas, lintegral_map' (hK'.indicator hS).aemeasurable (hsy.mono_ac (withDensity_absolutelyContinuous _ _)), lintegral_withDensity_eq_lintegral_mul₀ (g := fun z => S.indicator (fun b => ∫⁻ x, K b x) (e.symm z)) hρ ((hK'.indicator hS).comp_a …`. Use `setLIntegral_congr_fun e.open_target.measurableSet fun z hz => ?_` and prove the remaining obligations. Distinguish the cases in `hz' : z ∈ e '' S`. Establish `: e.symm z ∈ S`.

Take `⟨b, hb, rfl⟩` from `hz'`. Rewrite using `[e.left_inv (hSe hb)]` and apply the resulting hypothesis. Simplify using `[hz', this, mul_comm]`. Establish `: e.symm z ∉ S` using `fun h => hz' ⟨_, h, e.right_inv hz⟩`. Simplify using `[hz', this]`.

Establish `hA : e' '' (e'.source ∩ (f ⁻¹' S ∩ T)) = e' '' (e'.source ∩ T) ∩ basePt ⁻¹' (e '' S)`. Use extensionality with `v`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, ⟨hy, h₁, h₂⟩, rfl⟩`. Conclude with `⟨⟨y, ⟨hy, h₂⟩, rfl⟩, _, h₁, (hb y hy).symm⟩`.

Introduce and unpack `⟨⟨y, ⟨hy, h₂⟩, rfl⟩, b, h₁, h₃⟩`. Use `⟨y, ⟨hy, ?_, h₂⟩, rfl⟩` and prove the remaining obligations. Rewrite `h₃` using `[hb y hy]`. Rewrite using `[mem_preimage, ← e.injOn (hSe h₁) (hs y hy) h₃]` and apply the resulting hypothesis. Establish `hm` using `(measurePreserving_prodPt d).restrict_preimage (hbc.measurable hIm)`.

Establish `hp : (fun z : V d × ℂ => prodPt z.1 z.2) ⁻¹' (basePt ⁻¹' (e '' S)) = (e '' S) ×ˢ univ`. Use extensionality with `z`. Simplify using the standard rewrite rules. Establish `hemb : MeasurableEmbedding fun z : V d × ℂ => prodPt z.1 z.2` using `(Homeomorph.measurableEmbedding ⟨⟨fun z => prodPt z.1 z.2, fun v => (basePt v, v (Fin.last d)), fun z => by simp, fun v => by simp⟩, FibTriv.differentiable_prodPt.continuous, hbc.prodMk (by fun_prop)⟩ :)`. Establish `hTm` using `ChartGlue.measurableSet_image e' hT' inter_subset_left`.

Establish `h₁ : AEMeasurable e.symm (volume.restrict (e '' S))` using `hsy.mono_measure (Measure.restrict_mono hIt le_rfl)`. Establish `h₂ : AEMeasurable (ρ ∘ e.symm) (volume.restrict (e '' S))` using `hρ.mono_measure (Measure.restrict_mono hIt le_rfl)`. Rewrite using `[hR, ChartGlue.chartMeas_apply _ _ hT, hA, ← Measure.restrict_restrict hTm, ← lintegral_indicator hTm, setLIntegral_congr_fun (hbc.measurable hIm) (g := fun v => K (e.symm (basePt v)) (v (Fin.last d)) * ρ (e.symm (basePt v))) (fun v hv => ?_), ← hm.lintegral_comp_emb hemb, hp, Me …`. Simplify using `only [FibTriv.basePt_prodPt, FibTriv.prodPt_last]`. Rewrite using `[lintegral_prod (fun a : V d × ℂ => K (e.symm a.1) a.2 * ρ (e.symm a.1)) ((hK.comp_aemeasurable (h₁.comp_fst.prodMk measurable_snd.aemeasurable)).mul h₂.comp_fst)]`.

Use `lintegral_congr fun z => ?_` and prove the remaining obligations. Simplify using `only`. Conclude with `lintegral_mul_const (f := K (e.symm z)) _ (hK.comp measurable_prodMk_left)`. Establish `hv' : v ∈ e'.target` using `ht ▸ hIt hv`. Establish `hy` using `e'.map_target hv'`.

Use `h _ hy` as an intermediate fact. Rewrite `this` using `[← e.left_inv (hs _ hy), ← hb _ hy, e'.right_inv hv']`. Use `beta_reduce`. Rewrite using `[← this]`. Distinguish the cases in `hT : e'.symm v ∈ T`.

Rewrite using `[indicator_of_mem hT, indicator_of_mem (show v ∈ e' '' (e'.source ∩ T) from ⟨_, ⟨hy, hT⟩, e'.right_inv hv'⟩)]`. Rewrite using `[indicator_of_notMem hT, indicator_of_notMem]`. Introduce and unpack `⟨y, ⟨h₁, h₂⟩, rfl⟩`. Conclude with `hT (by rwa [e'.left_inv h₁])`.
-/
theorem chartMeas_prod {X Y : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] {d : ℕ} (e : OpenPartialHomeomorph X (V d))
    (e' : OpenPartialHomeomorph Y (V (d + 1))) (f : Y → X) (hs : ∀ y ∈ e'.source, f y ∈ e.source)
    (ht : e'.target = basePt ⁻¹' e.target) (hb : ∀ y ∈ e'.source, basePt (e' y) = e (f y))
    (ρ : X → ℝ≥0∞) (hρ : AEMeasurable (ρ ∘ e.symm) (volume.restrict e.target)) (ρ' : Y → ℝ≥0∞)
    (K : X → ℂ → ℝ≥0∞) (hK : Measurable (Function.uncurry K)) {T : Set Y}
    (h : ∀ y ∈ e'.source, T.indicator ρ' y = K (f y) (e' y (Fin.last d)) * ρ (f y))
    {S : Set X} (hS : MeasurableSet S) (hSe : S ⊆ e.source) (hT : MeasurableSet (f ⁻¹' S ∩ T))
    (hT' : MeasurableSet (e'.source ∩ T)) :
    ChartGlue.chartMeas e' ρ' (f ⁻¹' S ∩ T) = ∫⁻ b in S, (∫⁻ x, K b x) ∂ChartGlue.chartMeas e ρ := by
  have hK' : Measurable fun b => ∫⁻ x, K b x := hK.lintegral_prod_right
  have hIm := ChartGlue.measurableSet_image e hS hSe
  have hIt : e '' S ⊆ e.target := by rintro _ ⟨b, hb, rfl⟩; exact e.map_source (hSe hb)
  have hsy : AEMeasurable e.symm (volume.restrict e.target) :=
    e.continuousOn_symm.aemeasurable e.open_target.measurableSet
  have hbc : Continuous (basePt (d := d)) := FibTriv.differentiable_basePt.continuous
  have hR : ∫⁻ b in S, (∫⁻ x, K b x) ∂ChartGlue.chartMeas e ρ =
      ∫⁻ z in e '' S, (∫⁻ x, K (e.symm z) x) * ρ (e.symm z) := by
    rw [← lintegral_indicator hS, ChartGlue.chartMeas, lintegral_map' (hK'.indicator hS).aemeasurable
      (hsy.mono_ac (withDensity_absolutelyContinuous _ _)),
      lintegral_withDensity_eq_lintegral_mul₀ (g := fun z => S.indicator (fun b => ∫⁻ x, K b x) (e.symm z)) hρ
        ((hK'.indicator hS).comp_aemeasurable hsy),
      ← inter_eq_left.2 hIt, ← Measure.restrict_restrict hIm, ← lintegral_indicator hIm]
    refine setLIntegral_congr_fun e.open_target.measurableSet fun z hz => ?_
    by_cases hz' : z ∈ e '' S
    · have : e.symm z ∈ S := by
        obtain ⟨b, hb, rfl⟩ := hz'
        rwa [e.left_inv (hSe hb)]
      simp [hz', this, mul_comm]
    · have : e.symm z ∉ S := fun h => hz' ⟨_, h, e.right_inv hz⟩
      simp [hz', this]
  have hA : e' '' (e'.source ∩ (f ⁻¹' S ∩ T)) = e' '' (e'.source ∩ T) ∩ basePt ⁻¹' (e '' S) := by
    ext v
    constructor
    · rintro ⟨y, ⟨hy, h₁, h₂⟩, rfl⟩
      exact ⟨⟨y, ⟨hy, h₂⟩, rfl⟩, _, h₁, (hb y hy).symm⟩
    · rintro ⟨⟨y, ⟨hy, h₂⟩, rfl⟩, b, h₁, h₃⟩
      refine ⟨y, ⟨hy, ?_, h₂⟩, rfl⟩
      rw [hb y hy] at h₃
      rwa [mem_preimage, ← e.injOn (hSe h₁) (hs y hy) h₃]
  have hm := (measurePreserving_prodPt d).restrict_preimage (hbc.measurable hIm)
  have hp : (fun z : V d × ℂ => prodPt z.1 z.2) ⁻¹' (basePt ⁻¹' (e '' S)) = (e '' S) ×ˢ univ := by
    ext z; simp
  have hemb : MeasurableEmbedding fun z : V d × ℂ => prodPt z.1 z.2 :=
    (Homeomorph.measurableEmbedding ⟨⟨fun z => prodPt z.1 z.2, fun v => (basePt v, v (Fin.last d)), fun z => by simp,
      fun v => by simp⟩, FibTriv.differentiable_prodPt.continuous, hbc.prodMk (by fun_prop)⟩ :)
  have hTm := ChartGlue.measurableSet_image e' hT' inter_subset_left
  have h₁ : AEMeasurable e.symm (volume.restrict (e '' S)) := hsy.mono_measure (Measure.restrict_mono hIt le_rfl)
  have h₂ : AEMeasurable (ρ ∘ e.symm) (volume.restrict (e '' S)) := hρ.mono_measure (Measure.restrict_mono hIt le_rfl)
  rw [hR, ChartGlue.chartMeas_apply _ _ hT, hA, ← Measure.restrict_restrict hTm, ← lintegral_indicator hTm,
    setLIntegral_congr_fun (hbc.measurable hIm)
      (g := fun v => K (e.symm (basePt v)) (v (Fin.last d)) * ρ (e.symm (basePt v))) (fun v hv => ?_),
    ← hm.lintegral_comp_emb hemb, hp, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  · simp only [FibTriv.basePt_prodPt, FibTriv.prodPt_last]
    rw [lintegral_prod (fun a : V d × ℂ => K (e.symm a.1) a.2 * ρ (e.symm a.1))
      ((hK.comp_aemeasurable (h₁.comp_fst.prodMk measurable_snd.aemeasurable)).mul h₂.comp_fst)]
    refine lintegral_congr fun z => ?_
    dsimp only
    exact lintegral_mul_const (f := K (e.symm z)) _ (hK.comp measurable_prodMk_left)
  · have hv' : v ∈ e'.target := ht ▸ hIt hv
    have hy := e'.map_target hv'
    have := h _ hy
    rw [← e.left_inv (hs _ hy), ← hb _ hy, e'.right_inv hv'] at this
    beta_reduce
    rw [← this]
    by_cases hT : e'.symm v ∈ T
    · rw [indicator_of_mem hT, indicator_of_mem (show v ∈ e' '' (e'.source ∩ T) from ⟨_, ⟨hy, hT⟩, e'.right_inv hv'⟩)]
    · rw [indicator_of_notMem hT, indicator_of_notMem]
      rintro ⟨y, ⟨h₁, h₂⟩, rfl⟩
      exact hT (by rwa [e'.left_inv h₁])

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

/- English proof (translation)
Set `ι : MvPolynomial (Fin (d + 1)) k →+* MvPolynomial N (MvPolynomial (Fin d) k)` to `eval₂Hom (C.comp C) (Fin.snoc (α := fun _ => MvPolynomial N (MvPolynomial (Fin d) k)) (fun j => C (X j)) (X default))`. Set `κ : MvPolynomial N (MvPolynomial (Fin d) k) →+* MvPolynomial (Fin (d + 1)) k` to `eval₂Hom (eval₂Hom C fun j => X j.castSucc) fun _ => X (Fin.last d)`. Establish `h1 : κ.comp ι = RingHom.id _`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`.

Simplify using `[ι, κ]`. Introduce `j`. Apply the tactic sequence `induction j using Fin.lastCases <;> simp [ι, κ]`. Establish `h2 : ι.comp κ = RingHom.id _`. Apply `MvPolynomial.ringHom_ext'` to reduce the goal to its premises.

Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`. Simplify using `[ι, κ]`. Introduce `j`. Simplify using `[ι, κ]`.

Introduce `j`. Take `rfl : j = default` from `Subsingleton.elim _ _`. Simplify using `[ι, κ]`. Establish `hι : Function.Bijective ι` using `Function.bijective_iff_has_inverse.2 ⟨κ, fun x => DFunLike.congr_fun h1 x, fun x => DFunLike.congr_fun h2 x⟩`. Establish `key : eval₂Hom (f.comp α) (Fin.snoc (α` using `fun _ => R) (fun j => f (t j)) (n default)) = (eval₂Hom f n).comp ((MvPolynomial.map (eval₂Hom α t)).comp ι) := by`.

Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`. Simplify using `[ι]`. Introduce `j`. Apply the tactic sequence `induction j using Fin.lastCases <;> simp [ι]`.

Rewrite using `[key]`. Conclude with `RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective hι) (etale_mvPolynomial_map_of_etale _ hg)) (RingHom.Etale.of_bijective hΦ)`.
-/
theorem etale_snoc {k A R N : Type} [CommRing k] [CommRing A] [CommRing R] [Unique N] (α : k →+* A) {d : ℕ}
    (t : Fin d → A) (f : A →+* R) (n : N → R) (hg : (eval₂Hom α t).Etale) (hΦ : Function.Bijective (eval₂Hom f n)) :
    (eval₂Hom (f.comp α) (Fin.snoc (α := fun _ => R) (fun j => f (t j)) (n default))).Etale := by
  let ι : MvPolynomial (Fin (d + 1)) k →+* MvPolynomial N (MvPolynomial (Fin d) k) :=
    eval₂Hom (C.comp C) (Fin.snoc (α := fun _ => MvPolynomial N (MvPolynomial (Fin d) k)) (fun j => C (X j)) (X default))
  let κ : MvPolynomial N (MvPolynomial (Fin d) k) →+* MvPolynomial (Fin (d + 1)) k :=
    eval₂Hom (eval₂Hom C fun j => X j.castSucc) fun _ => X (Fin.last d)
  have h1 : κ.comp ι = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [ι, κ]
    · intro j
      induction j using Fin.lastCases <;> simp [ι, κ]
  have h2 : ι.comp κ = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext'
    · apply MvPolynomial.ringHom_ext
      · intro r; simp [ι, κ]
      · intro j; simp [ι, κ]
    · intro j
      obtain rfl : j = default := Subsingleton.elim _ _
      simp [ι, κ]
  have hι : Function.Bijective ι :=
    Function.bijective_iff_has_inverse.2 ⟨κ, fun x => DFunLike.congr_fun h1 x, fun x => DFunLike.congr_fun h2 x⟩
  have key : eval₂Hom (f.comp α) (Fin.snoc (α := fun _ => R) (fun j => f (t j)) (n default)) =
      (eval₂Hom f n).comp ((MvPolynomial.map (eval₂Hom α t)).comp ι) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [ι]
    · intro j
      induction j using Fin.lastCases <;> simp [ι]
  rw [key]
  exact RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective hι) (etale_mvPolynomial_map_of_etale _ hg))
    (RingHom.Etale.of_bijective hΦ)

/- English proof (translation)
Establish `hy0 : y ∈ ptsIn q σ c₀.U` using `c₀.source_subset hy`. Take `⟨f, hfV, hf⟩` from `c₀.affine.exists_basicOpen_le (V := U) ⟨_, mem_ptsIn.1 hU⟩ (mem_ptsIn.1 hy0)`. Establish `hle : B.basicOpen f ≤ c₀.U` using `B.basicOpen_le f`. Establish `hE : (eval₂Hom (algX q (B.basicOpen f)) (fun a => resG B hle (c₀.x a))).Etale`. Establish `e : eval₂Hom (algX q (B.basicOpen f)) (fun a => resG B hle (c₀.x a)) = (resG B hle).comp (eval₂Hom (algX q c₀.U) c₀.x)`.

Rewrite using `[MvPolynomial.comp_eval₂Hom, GlobalTheory.TopForm.resG_comp_algX]`. Rewrite using `[e]`. Establish `hR : (resG B hle).Etale`. Use `letI : Algebra Γ(B, c₀.U) Γ(B, B.basicOpen f) := (resG B hle).toAlgebra`. Use `haveI : IsLocalization.Away f Γ(B, B.basicOpen f) := c₀.affine.isLocalization_basicOpen f`.

Conclude with `RingHom.etale_algebraMap.2 (Algebra.Etale.of_isLocalizationAway f)`. Conclude with `RingHom.Etale.stableUnderComposition _ _ c₀.etale hR`. Take `⟨c, hc, hU, -⟩` from `AlgChart.exists_of_etale (c₀.affine.basicOpen f) _ hE (mem_ptsIn.2 hf)`. Conclude with `⟨c, hc, hU ▸ hfV⟩`.
-/
theorem exists_chart_le {k : Type} [CommRing k] {B : Scheme.{0}} {q : B ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ}
    (c₀ : AlgChart q σ d) {y : CxPts q σ} (hy : y ∈ c₀.e.source) {U : B.Opens} (hU : y ∈ ptsIn q σ U) :
    ∃ c : AlgChart q σ d, y ∈ c.e.source ∧ c.U ≤ U := by
  have hy0 : y ∈ ptsIn q σ c₀.U := c₀.source_subset hy
  obtain ⟨f, hfV, hf⟩ := c₀.affine.exists_basicOpen_le (V := U) ⟨_, mem_ptsIn.1 hU⟩ (mem_ptsIn.1 hy0)
  have hle : B.basicOpen f ≤ c₀.U := B.basicOpen_le f
  have hE : (eval₂Hom (algX q (B.basicOpen f)) (fun a => resG B hle (c₀.x a))).Etale := by
    have e : eval₂Hom (algX q (B.basicOpen f)) (fun a => resG B hle (c₀.x a)) =
        (resG B hle).comp (eval₂Hom (algX q c₀.U) c₀.x) := by
      rw [MvPolynomial.comp_eval₂Hom, GlobalTheory.TopForm.resG_comp_algX]
    rw [e]
    have hR : (resG B hle).Etale := by
      letI : Algebra Γ(B, c₀.U) Γ(B, B.basicOpen f) := (resG B hle).toAlgebra
      haveI : IsLocalization.Away f Γ(B, B.basicOpen f) := c₀.affine.isLocalization_basicOpen f
      exact RingHom.etale_algebraMap.2 (Algebra.Etale.of_isLocalizationAway f)
    exact RingHom.Etale.stableUnderComposition _ _ c₀.etale hR
  obtain ⟨c, hc, hU, -⟩ := AlgChart.exists_of_etale (c₀.affine.basicOpen f) _ hE (mem_ptsIn.2 hf)
  exact ⟨c, hc, hU ▸ hfV⟩

open GlobalTheory.CellChart in

/- English proof (translation)
Set `s : V (d + 1) → CxPts p σ` to `fun v => if h : basePt v ∈ c.e.target then cellPt π w hW hWa n hΦ (c.source_subset (c.e.map_target h)) (fun _ => v (Fin.last d)) else cellPt π w hW hWa n hΦ (c.source_subset hb₀) 0`. Establish `s_eq {v} (h : basePt v ∈ c.e.target) : s v = cellPt π w hW hWa n hΦ (c.source_subset (c.e.map_target h)) (fun _ => v (Fin.last d))` using `dif_pos h`. Establish `s_mem {v} (h : basePt v ∈ c.e.target) : s v ∈ ptsIn p σ W` using `by rw [s_eq h]; exact cellPt_mem ..`. Establish `s_map {v} (h : basePt v ∈ c.e.target) : PtsOver.map π w (spMap σ) (s v) = c.e.symm (basePt v)`. Rewrite using `[s_eq h]`.

Conclude with `map_cellPt _ _ _ _ _ _ c.affine _ _`. Establish `s_n {v} (h : basePt v ∈ c.e.target) (a : N) : ev p σ W (n a) (s v) = v (Fin.last d)`. Rewrite using `[s_eq h]`. Conclude with `ev_n_cellPt ..`. Establish `hT : IsOpen (basePt ⁻¹' c.e.target)` using `c.e.open_target.preimage FibTriv.differentiable_basePt.continuous`.

Establish `holo (g : Γ(Y, W)) : DifferentiableOn ℂ (ev p σ W g ∘ s) (basePt ⁻¹' c.e.target)`. Express the relevant statement in the definitionally equal form `DifferentiableOn ℂ (fun v => ev p σ W g (s v)) _`. Take `⟨P, rfl⟩` from `hΦ.2 g`. Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a`.

Use `((c.holo c.U a).comp FibTriv.differentiable_basePt.differentiableOn fun v hv => ⟨hv, c.source_subset (c.e.map_target hv)⟩).congr fun v hv => ?_` and prove the remaining obligations. Rewrite using `[eval₂Hom_C, ev_appLE π w hW (s_mem hv), s_map hv]`. Both sides reduce to the same expression. Consider the case `add P Q hP hQ`. Simplify using `only [map_add, ev_add]`.

Conclude with `hP.add hQ`. Consider the case `mul_X P a hP`. Establish `hd : DifferentiableOn ℂ (fun v : V (d + 1) => v (Fin.last d)) (basePt ⁻¹' c.e.target)` using `by fun_prop`. Simplify using `only [map_mul, ev_mul, eval₂Hom_X']`. Conclude with `hP.mul (hd.congr fun v hv => s_n hv a)`.

Establish `H` using `holo_of_affine hWa hT (fun v hv => s_mem hv) holo`. Set `e : OpenPartialHomeomorph (CxPts p σ) (V (d + 1))` to `{ toFun y := prodPt (c.e (PtsOver.map π w (spMap σ) y)) (ev p σ W (n default) y) invFun := s source := PtsOver.map π w (spMap σ) ⁻¹' c.e.source ∩ ptsIn p σ W target := basePt ⁻¹' c.e.target map_source' y hy := by`. Rewrite using `[mem_preimage, FibTriv.basePt_prodPt]`. Conclude with `c.e.map_source hy.1`. Use the proof step `map_target' v hv := ⟨by rw [mem_preimage, s_map hv]; exact c.e.map_target hv, s_mem hv⟩`.

Use the proof step `left_inv' y hy := by`. Rewrite using `[s_eq (by rw [FibTriv.basePt_prodPt]; exact c.e.map_source hy.1)]`. Use `(cellPt_congr π w hW hWa n hΦ _ (map_mem π w hW hy.2) ?_ ?_).trans (cellPt_self π w hW hWa n hΦ hy.2)` and prove the remaining obligations. Rewrite using `[FibTriv.basePt_prodPt, c.e.left_inv hy.1]`. Use function extensionality and compare the values at `a`.

Rewrite using `[FibTriv.prodPt_last, Subsingleton.elim a default]`. Use the proof step `right_inv' v hv := by rw [s_map hv, c.e.right_inv hv, s_n hv, FibTriv.prodPt_basePt]`. Use `open_source := ((PtsOver.continuous_map π w _).isOpen_preimage _ c.e.open_source).inter (isOpen_ptsIn W)`. Use `open_target := hT`. Use `continuousOn_toFun := FibTriv.differentiable_prodPt.continuous.comp_continuousOn ((c.e.continuousOn.comp (PtsOver.continuous_map π w _).continuousOn fun y hy => hy.1).prodMk ((continuousOn_ev (n default)).mono inter_subset_right))`.

Use `continuousOn_invFun := H.1 }`. Use `⟨⟨e, W, hWa, Fin.snoc (α := fun _ => Γ(Y, W)) (fun j => (π.appLE c.U W hW).hom (c.x j)) (n default), ?_, inter_subset_right, fun y hy j => ?_, H.2⟩, rfl, rfl, rfl, fun _ => rfl⟩` and prove the remaining obligations. Rewrite using `[← algX_eq π w hW]`. Conclude with `etale_snoc _ _ _ _ c.etale hΦ`. Express the relevant statement in the definitionally equal form `prodPt _ _ j = _`.

Proceed by induction on `j using Fin.lastCases`. Simplify using the standard rewrite rules. Rewrite using `[FibTriv.prodPt_castSucc, Fin.snoc_castSucc, c.apply_eq _ hy.1, ev_appLE π w hW hy.2]`.
-/
theorem exists_prod_chart {k : Type} [CommRing k] {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} (π : Y ⟶ B)
    (w : π ≫ q = p) {σ : k →+* ℂ} {d : ℕ} (c : AlgChart q σ d) {W : Y.Opens} (hW : W ≤ π ⁻¹ᵁ c.U)
    (hWa : IsAffineOpen W) {N : Type} [Unique N] (n : N → Γ(Y, W))
    (hΦ : Function.Bijective (eval₂Hom (π.appLE c.U W hW).hom n)) {b₀ : CxPts q σ} (hb₀ : b₀ ∈ c.e.source) :
    ∃ c' : AlgChart p σ (d + 1), c'.U = W ∧ c'.e.source = PtsOver.map π w (spMap σ) ⁻¹' c.e.source ∩ ptsIn p σ W ∧
      c'.e.target = basePt ⁻¹' c.e.target ∧
      ∀ y, c'.e y = prodPt (c.e (PtsOver.map π w (spMap σ) y)) (ev p σ W (n default) y) := by
  let s : V (d + 1) → CxPts p σ := fun v => if h : basePt v ∈ c.e.target then
    cellPt π w hW hWa n hΦ (c.source_subset (c.e.map_target h)) (fun _ => v (Fin.last d))
    else cellPt π w hW hWa n hΦ (c.source_subset hb₀) 0
  have s_eq {v} (h : basePt v ∈ c.e.target) :
      s v = cellPt π w hW hWa n hΦ (c.source_subset (c.e.map_target h)) (fun _ => v (Fin.last d)) := dif_pos h
  have s_mem {v} (h : basePt v ∈ c.e.target) : s v ∈ ptsIn p σ W := by rw [s_eq h]; exact cellPt_mem ..
  have s_map {v} (h : basePt v ∈ c.e.target) : PtsOver.map π w (spMap σ) (s v) = c.e.symm (basePt v) := by
    rw [s_eq h]; exact map_cellPt _ _ _ _ _ _ c.affine _ _
  have s_n {v} (h : basePt v ∈ c.e.target) (a : N) : ev p σ W (n a) (s v) = v (Fin.last d) := by
    rw [s_eq h]; exact ev_n_cellPt ..
  have hT : IsOpen (basePt ⁻¹' c.e.target) := c.e.open_target.preimage FibTriv.differentiable_basePt.continuous
  have holo (g : Γ(Y, W)) : DifferentiableOn ℂ (ev p σ W g ∘ s) (basePt ⁻¹' c.e.target) := by
    change DifferentiableOn ℂ (fun v => ev p σ W g (s v)) _
    obtain ⟨P, rfl⟩ := hΦ.2 g
    induction P using MvPolynomial.induction_on with
    | C a =>
      refine ((c.holo c.U a).comp FibTriv.differentiable_basePt.differentiableOn fun v hv =>
        ⟨hv, c.source_subset (c.e.map_target hv)⟩).congr fun v hv => ?_
      rw [eval₂Hom_C, ev_appLE π w hW (s_mem hv), s_map hv]
      rfl
    | add P Q hP hQ =>
      simp only [map_add, ev_add]
      exact hP.add hQ
    | mul_X P a hP =>
      have hd : DifferentiableOn ℂ (fun v : V (d + 1) => v (Fin.last d)) (basePt ⁻¹' c.e.target) := by fun_prop
      simp only [map_mul, ev_mul, eval₂Hom_X']
      exact hP.mul (hd.congr fun v hv => s_n hv a)
  have H := holo_of_affine hWa hT (fun v hv => s_mem hv) holo
  let e : OpenPartialHomeomorph (CxPts p σ) (V (d + 1)) :=
    { toFun y := prodPt (c.e (PtsOver.map π w (spMap σ) y)) (ev p σ W (n default) y)
      invFun := s
      source := PtsOver.map π w (spMap σ) ⁻¹' c.e.source ∩ ptsIn p σ W
      target := basePt ⁻¹' c.e.target
      map_source' y hy := by
        rw [mem_preimage, FibTriv.basePt_prodPt]
        exact c.e.map_source hy.1
      map_target' v hv := ⟨by rw [mem_preimage, s_map hv]; exact c.e.map_target hv, s_mem hv⟩
      left_inv' y hy := by
        rw [s_eq (by rw [FibTriv.basePt_prodPt]; exact c.e.map_source hy.1)]
        refine (cellPt_congr π w hW hWa n hΦ _ (map_mem π w hW hy.2) ?_ ?_).trans (cellPt_self π w hW hWa n hΦ hy.2)
        · rw [FibTriv.basePt_prodPt, c.e.left_inv hy.1]
        · funext a
          rw [FibTriv.prodPt_last, Subsingleton.elim a default]
      right_inv' v hv := by rw [s_map hv, c.e.right_inv hv, s_n hv, FibTriv.prodPt_basePt]
      open_source := ((PtsOver.continuous_map π w _).isOpen_preimage _ c.e.open_source).inter (isOpen_ptsIn W)
      open_target := hT
      continuousOn_toFun := FibTriv.differentiable_prodPt.continuous.comp_continuousOn
        ((c.e.continuousOn.comp (PtsOver.continuous_map π w _).continuousOn fun y hy => hy.1).prodMk
          ((continuousOn_ev (n default)).mono inter_subset_right))
      continuousOn_invFun := H.1 }
  refine ⟨⟨e, W, hWa, Fin.snoc (α := fun _ => Γ(Y, W)) (fun j => (π.appLE c.U W hW).hom (c.x j)) (n default), ?_,
    inter_subset_right, fun y hy j => ?_, H.2⟩, rfl, rfl, rfl, fun _ => rfl⟩
  · rw [← algX_eq π w hW]
    exact etale_snoc _ _ _ _ c.etale hΦ
  · change prodPt _ _ j = _
    induction j using Fin.lastCases
    · simp
    · rw [FibTriv.prodPt_castSucc, Fin.snoc_castSucc, c.apply_eq _ hy.1, ev_appLE π w hW hy.2]

/- English proof (translation)
Use `ChartGlue.glueMeas_apply A.e _ A.holo (fun i j y hi hj => ?_) i hT h` and prove the remaining obligations. Establish `e` using `hα.compat ⟨(i, y), hi⟩ ⟨(j, y), hj⟩ rfl`. Rewrite `e` using `[← A.loc_crd α ⟨(i, y), hi⟩, ← A.loc_crd α ⟨(j, y), hj⟩]`. Rewrite using `[← ENNReal.ofReal_mul (sq_nonneg _)]`. Use `congrArg ENNReal.ofReal ((congrArg (fun β => ((ε : ℤ) : ℝ) * (dens β).re) e).trans ?_)` and prove the remaining obligations.

Use `beta_reduce`. Rewrite using `[dens_pull, Complex.re_ofReal_mul, mul_left_comm]`. Both sides reduce to the same expression.
-/
theorem part_eq_chartMeas {M : Type} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
    {n : ℕ} (A : HolAtlas M n) {α : A.Fld} (hα : A.IsForm α) (ε : ℤˣ) (i : A.ι) {T : Set M} (hT : MeasurableSet T)
    (h : T ⊆ (A.e i).source) : A.part α ε T =
      ChartGlue.chartMeas (A.e i) (fun y => ENNReal.ofReal ((ε : ℤ) * (dens (A.loc α i (A.e i y))).re)) T := by
  refine ChartGlue.glueMeas_apply A.e _ A.holo (fun i j y hi hj => ?_) i hT h
  have e := hα.compat ⟨(i, y), hi⟩ ⟨(j, y), hj⟩ rfl
  rw [← A.loc_crd α ⟨(i, y), hi⟩, ← A.loc_crd α ⟨(j, y), hj⟩] at e
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  refine congrArg ENNReal.ofReal ((congrArg (fun β => ((ε : ℤ) : ℝ) * (dens β).re) e).trans ?_)
  beta_reduce
  rw [dens_pull, Complex.re_ofReal_mul, mul_left_comm]
  rfl

/- English proof (translation)
Use `set b := pick (L.φ σ).isLB y`. Establish `hb : y ∈ ptsIn p σ (L.B.U b)` using `mem_pick _ y`. Establish `ho` using `ChartGlue.isOpen_over a.e (isOpen_ptsIn (p := p) (σ := σ) (L.B.U c ⊓ L.B.U b))`. Establish `hm` using `ChartGlue.mem_over a.e hy (mem_ptsIn_inf.2 ⟨hc, hb⟩)`. Establish `hf : ContDiffAt ℂ 2 (gv p σ L.B c b ∘ a.e.symm) (a.e y)` using `(SCV.analyticAt_of_differentiableOn (a.holo _ (L.B.g c b).val) (ho.mem_nhds hm)).contDiffAt`.

Establish `h0 : (gv p σ L.B c b ∘ a.e.symm) (a.e y) ≠ 0` using `ev_ne_zero hm.2 (L.B.g c b).isUnit`. Establish `hC` using `(L.cInf σ).contDiffAt a hy hc`. Establish `hlog : ContDiffAt ℝ 2 (fun v => Real.log (‖(gv p σ L.B c b ∘ a.e.symm) v‖ ^ 2)) (a.e y)` using `((hf.restrict_scalars ℝ).norm_sq ℂ).log (by simpa using h0)`. Establish `key : leviForm (fun v => (L.φ σ).φ b (a.e.symm v)) (a.e y) = leviForm (fun v => (L.φ σ).φ c (a.e.symm v)) (a.e y)`. Rewrite using `[leviForm_congr (u' := fun v => (L.φ σ).φ c (a.e.symm v) + -Real.log (‖(gv p σ L.B c b ∘ a.e.symm) v‖ ^ 2)), leviForm_add hC hlog.neg, leviForm_neg, leviForm_log_normSq_eq_zero hf h0, neg_zero, add_zero]`.

Use `filter_upwards [ho.mem_nhds hm] with v hv`. Rewrite using `[(L.φ σ).trans c b _ (mem_ptsIn_inf.1 hv.2).1 (mem_ptsIn_inf.1 hv.2).2, sub_eq_add_neg]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `ofValues (HermFrame.ddc (fun v => (L.φ σ).φ b (a.e.symm v)) (a.e y)) = _`. Unfold `HermFrame.ddc`.

Rewrite using `[key]`.
-/
theorem c1F_eq_matForm_hessL {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (hX : IsRegVar p D) (σ : k →+* ℂ)
    (L : HermLB p) (a : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ a.e.source) (c : L.B.ι) (hc : y ∈ ptsIn p σ (L.B.U c)) :
    c1F hX σ L ⟨(a, y), hy⟩ = ofValues (HermFrame.ddc (fun v => (L.φ σ).φ c (a.e.symm v)) (a.e y)) := by
  set b := pick (L.φ σ).isLB y
  have hb : y ∈ ptsIn p σ (L.B.U b) := mem_pick _ y
  have ho := ChartGlue.isOpen_over a.e (isOpen_ptsIn (p := p) (σ := σ) (L.B.U c ⊓ L.B.U b))
  have hm := ChartGlue.mem_over a.e hy (mem_ptsIn_inf.2 ⟨hc, hb⟩)
  have hf : ContDiffAt ℂ 2 (gv p σ L.B c b ∘ a.e.symm) (a.e y) :=
    (SCV.analyticAt_of_differentiableOn (a.holo _ (L.B.g c b).val) (ho.mem_nhds hm)).contDiffAt
  have h0 : (gv p σ L.B c b ∘ a.e.symm) (a.e y) ≠ 0 := ev_ne_zero hm.2 (L.B.g c b).isUnit
  have hC := (L.cInf σ).contDiffAt a hy hc
  have hlog : ContDiffAt ℝ 2 (fun v => Real.log (‖(gv p σ L.B c b ∘ a.e.symm) v‖ ^ 2)) (a.e y) :=
    ((hf.restrict_scalars ℝ).norm_sq ℂ).log (by simpa using h0)
  have key : leviForm (fun v => (L.φ σ).φ b (a.e.symm v)) (a.e y) =
      leviForm (fun v => (L.φ σ).φ c (a.e.symm v)) (a.e y) := by
    rw [leviForm_congr (u' := fun v => (L.φ σ).φ c (a.e.symm v) +
        -Real.log (‖(gv p σ L.B c b ∘ a.e.symm) v‖ ^ 2)), leviForm_add hC hlog.neg,
      leviForm_neg, leviForm_log_normSq_eq_zero hf h0, neg_zero, add_zero]
    filter_upwards [ho.mem_nhds hm] with v hv
    rw [(L.φ σ).trans c b _ (mem_ptsIn_inf.1 hv.2).1 (mem_ptsIn_inf.1 hv.2).2, sub_eq_add_neg]
    rfl
  change ofValues (HermFrame.ddc (fun v => (L.φ σ).φ b (a.e.symm v)) (a.e y)) = _
  unfold HermFrame.ddc
  rw [key]

section Cell

open GlobalTheory.FlagCell GlobalTheory.HermFrame
open GlobalTheory.FlagFibre (Low)
open GlobalTheory.QCoh (pullbackSections)

variable {k : Type} [CommRing k] {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} (π : Y ⟶ B) (w : π ≫ q = p)
  {σ : k →+* ℂ} {E : B.Modules} (cE : Chart E 2) {W : Y.Opens} (hW : W ≤ π ⁻¹ᵁ cE.U) (n : Low 2 → Γ(Y, W))

/- English proof (translation)
Establish `hc : y ∈ ptsIn p σ (π ⁻¹ᵁ cE.U)` using `mem_ptsIn.2 (hW (mem_ptsIn.1 hy))`. Establish `hc' : PtsOver.map π w (spMap σ) y ∈ ptsIn q σ cE.U` using `hc`. Establish `k₀ : (cE.pull h.isVB π).crd p σ (pullbackSections π E hW (cE.e 0)) y = ![1, 0]`. Rewrite using `[cE.crd_pull h.isVB π w _ hW hy hc, cE.crd_frame hc']`. Use function extensionality and compare the values at `a`.

Apply the tactic sequence `fin_cases a <;> simp`. Establish `k₁ : (cE.pull h.isVB π).crd p σ (pullCol π cE.e hW (uniR n) 0) y = ![1, ev p σ W (n ⟨(1, 0), by decide⟩) y]`. Use function extensionality and compare the values at `a`. Simplify using `only [pullCol, Chart.crd_sum, Chart.crd_smul, cE.crd_pull h.isVB π w _ hW hy hc, cE.crd_frame hc', Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Use `fin_cases a`.

Conclude with `(ev_eq hy _).trans (map_one _)`. Both sides reduce to the same expression. Simplify using `only [(h.pull π w).form_eq (cE.pull h.isVB π) hc _ _ hy, h.pull_G π w cE hc', k₀, k₁]`. Apply the tactic sequence `refine ⟨congrArg Complex.re ?_, ?_, ?_⟩ <;>`. Simplify using `[HermFrame.form, dotProduct, Matrix.mulVec, Fin.sum_univ_two, ← Complex.mul_conj']`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_vals (h : Met q σ E 2) {y : CxPts p σ} (hy : y ∈ ptsIn p σ W) :
    ((h.pull π w).form (pullCol π cE.e hW (uniR n) 0) (pullCol π cE.e hW (uniR n) 0) y).re =
      FibCos.nrm (h.G cE (PtsOver.map π w (spMap σ) y)) (ev p σ W (n ⟨(1, 0), by decide⟩) y) ∧
    (h.pull π w).form (pullCol π cE.e hW (uniR n) 0) (pullbackSections π E hW (cE.e 0)) y =
      h.G cE (PtsOver.map π w (spMap σ) y) 0 0 +
        ev p σ W (n ⟨(1, 0), by decide⟩) y * h.G cE (PtsOver.map π w (spMap σ) y) 1 0 ∧
    (h.pull π w).form (pullbackSections π E hW (cE.e 0)) (pullbackSections π E hW (cE.e 0)) y =
      h.G cE (PtsOver.map π w (spMap σ) y) 0 0 := by
  have hc : y ∈ ptsIn p σ (π ⁻¹ᵁ cE.U) := mem_ptsIn.2 (hW (mem_ptsIn.1 hy))
  have hc' : PtsOver.map π w (spMap σ) y ∈ ptsIn q σ cE.U := hc
  have k₀ : (cE.pull h.isVB π).crd p σ (pullbackSections π E hW (cE.e 0)) y = ![1, 0] := by
    rw [cE.crd_pull h.isVB π w _ hW hy hc, cE.crd_frame hc']
    funext a
    fin_cases a <;> simp
  have k₁ : (cE.pull h.isVB π).crd p σ (pullCol π cE.e hW (uniR n) 0) y = ![1, ev p σ W (n ⟨(1, 0), by decide⟩) y] := by
    funext a
    simp only [pullCol, Chart.crd_sum, Chart.crd_smul, cE.crd_pull h.isVB π w _ hW hy hc, cE.crd_frame hc',
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    fin_cases a
    · exact (ev_eq hy _).trans (map_one _)
    · rfl
  simp only [(h.pull π w).form_eq (cE.pull h.isVB π) hc _ _ hy, h.pull_G π w cE hc', k₀, k₁]
  refine ⟨congrArg Complex.re ?_, ?_, ?_⟩ <;>
    simp [HermFrame.form, dotProduct, Matrix.mulVec, Fin.sum_univ_two, ← Complex.mul_conj']
  ring

variable {h : VMetric q E 2} (H : h.IsCInf) {fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2}
  (hs : Spans fl W (pullCol π cE.e hW (uniR n)))

include hs in

/- English proof (translation)
Take `⟨s, t, h₁, h₂, h₃⟩` from `hs.exists_adaptedChart 0`. Set `a : VBExt.AdaptedChart (VMetric.stepSeq fl 0) (0 : Fin 2) 1` to `⟨W, s, t, h₁, h₂⟩`. Use `⟨a.quot, rfl, fun y hy => ?_⟩` and prove the remaining obligations. Establish `e` using `Met.quot_G (((h.pull π w).stepMet fl 0).met σ) (VMetric.stepSeq_shortExact fl 0) (fl.isVB (Fin.castSucc 0)) (fl.isVB_gr 0) a hy`. Rewrite using `[← (form_vals π w cE hW n (h.met σ) hy).1]`.

Use `congrArg (fun z : ℂ => -Real.log z.re) ((congrArg Matrix.det e).trans ((Matrix.det_fin_one _).trans ?_))` and prove the remaining obligations. Establish `key (H : Matrix (Fin 0 ⊕ Fin 1) (Fin 0 ⊕ Fin 1) ℂ) : quotGram H 0 0 = H (.inr 0) (.inr 0)`. Simplify using `[quotGram, Matrix.toBlocks₂₂]`. Use `(key _).trans ((Met.form_restrict _ (fl.isSubbundle (Fin.succ 0)) (fl.isVB (Fin.succ 0)) _ _ hy).trans ?_)` and prove the remaining obligations. Conclude with `congrArg₂ (fun s t => ((h.met σ).pull π w).form s t y) (h₃ (.inr 0)) (h₃ (.inr 0))`.
-/
theorem exists_weight : ∃ c : (VMetric.grLB fl 0 (H.pull π w)).B.ι, (VMetric.grLB fl 0 (H.pull π w)).B.U c = W ∧
    ∀ y ∈ ptsIn p σ W, ((VMetric.grLB fl 0 (H.pull π w)).φ σ).φ c y =
      -Real.log (FibCos.nrm ((h.met σ).G cE (PtsOver.map π w (spMap σ) y)) (ev p σ W (n ⟨(1, 0), by decide⟩) y)) := by
  obtain ⟨s, t, h₁, h₂, h₃⟩ := hs.exists_adaptedChart 0
  let a : VBExt.AdaptedChart (VMetric.stepSeq fl 0) (0 : Fin 2) 1 := ⟨W, s, t, h₁, h₂⟩
  refine ⟨a.quot, rfl, fun y hy => ?_⟩
  have e := Met.quot_G (((h.pull π w).stepMet fl 0).met σ) (VMetric.stepSeq_shortExact fl 0)
    (fl.isVB (Fin.castSucc 0)) (fl.isVB_gr 0) a hy
  rw [← (form_vals π w cE hW n (h.met σ) hy).1]
  refine congrArg (fun z : ℂ => -Real.log z.re) ((congrArg Matrix.det e).trans ((Matrix.det_fin_one _).trans ?_))
  have key (H : Matrix (Fin 0 ⊕ Fin 1) (Fin 0 ⊕ Fin 1) ℂ) : quotGram H 0 0 = H (.inr 0) (.inr 0) := by
    simp [quotGram, Matrix.toBlocks₂₂]
  refine (key _).trans ((Met.form_restrict _ (fl.isSubbundle (Fin.succ 0)) (fl.isVB (Fin.succ 0)) _ _ hy).trans ?_)
  exact congrArg₂ (fun s t => ((h.met σ).pull π w).form s t y) (h₃ (.inr 0)) (h₃ (.inr 0))

include hs in

/- English proof (translation)
Take `⟨s, -, e⟩` from `hs 1`. Establish `hG` using `(h.met σ).posDef cE (PtsOver.map π w (spMap σ) y) (mem_ptsIn.2 (hW (mem_ptsIn.1 hy)))`. Take `⟨h₁, h₂, h₃⟩` from `form_vals π w cE hW n (h.met σ) hy`. Use `hv W (s ⟨0, by decide⟩) (pullbackSections π M hW m) y hy` as an intermediate fact. Rewrite `this` using `[QCoh.pullback_map_app_pullbackSections, hm, e, ← Met.conj_form, Complex.norm_conj]`.

Use `erw [h₁, h₂, h₃] at this`. Establish `h0 : 0 < ((h.met σ).G cE (PtsOver.map π w (spMap σ) y) 0 0).re` using `(Complex.pos_iff.1 (hG.diag_pos (i := 0))).1`. Rewrite using `[FibCos.cos, this, eq_div_iff (mul_pos h0 (nrm_pos hG _)).ne']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cosSq_eq {M : B.Modules} (l : M ⟶ E) (m : Γ(M, cE.U)) (hm : l.app cE.U m = cE.e 0) {v : CxPts p σ → ℝ}
    (hv : CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map l) v)
    {y : CxPts p σ} (hy : y ∈ ptsIn p σ W) :
    v y = FibCos.cos ((h.met σ).G cE (PtsOver.map π w (spMap σ) y)) (ev p σ W (n ⟨(1, 0), by decide⟩) y) := by
  obtain ⟨s, -, e⟩ := hs 1
  have hG := (h.met σ).posDef cE (PtsOver.map π w (spMap σ) y) (mem_ptsIn.2 (hW (mem_ptsIn.1 hy)))
  obtain ⟨h₁, h₂, h₃⟩ := form_vals π w cE hW n (h.met σ) hy
  have := hv W (s ⟨0, by decide⟩) (pullbackSections π M hW m) y hy
  rw [QCoh.pullback_map_app_pullbackSections, hm, e, ← Met.conj_form, Complex.norm_conj] at this
  erw [h₁, h₂, h₃] at this
  have h0 : 0 < ((h.met σ).G cE (PtsOver.map π w (spMap σ) y) 0 0).re := (Complex.pos_iff.1 (hG.diag_pos (i := 0))).1
  rw [FibCos.cos, this, eq_div_iff (mul_pos h0 (nrm_pos hG _)).ne']
  ring

end Cell

/- English proof (translation)
Set `L : V (d + 1) →L[ℂ] V d` to `LinearMap.toContinuousLinearMap { toFun := basePt, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }`. Establish `hL : fderiv ℂ basePt v = L` using `L.fderiv`. Set `ψ : ℂ → V (d + 1)` to `fun t => prodPt (basePt v) 0 + t • coordVec (Fin.last d)`. Establish `hψ (t : ℂ) : ψ t = prodPt (basePt v) t`. Use extensionality with `a`.

Apply the tactic sequence `induction a using Fin.lastCases <;> simp [ψ, coordVec, EuclideanSpace.single_apply, Fin.castSucc_ne_last]`. Establish `hv : ψ (v (Fin.last d)) = v` using `by rw [hψ, FibTriv.prodPt_basePt]`. Establish `hd : fderiv ℂ ψ (v (Fin.last d)) 1 = coordVec (Fin.last d)`. Establish `: HasFDerivAt ψ _ _` using `((hasFDerivAt_id (𝕜 := ℂ) (v (Fin.last d))).smul_const (coordVec (Fin.last d))).const_add _`. Rewrite using `[this.fderiv]`.

Simplify using the standard rewrite rules. Establish `hl` using `leviForm_comp_holo (u := u) (φ := ψ) (z := v (Fin.last d)) (by rwa [hv]) (by fun_prop) 1 1`. Simplify using `only [hψ, hG'] at hl`. Rewrite `hl` using `[leviForm_neg, ← hψ, hv, hd, ContinuousLinearMap.neg_apply, ContinuousLinearMap.neg_apply, leviForm_log_nrm hG]`. Establish `h0 : dens (pull L (γ * β)) = 0` using `by rw [dens, PullTop.repr_pull_univ, zero_div]`.

Establish `hsub (a b : Alt (d + 1)) : dens (a - b) = dens a - dens b` using `by simp [dens, sub_div]`. Rewrite using `[hL, sub_mul, ← map_mul, hsub, h0, sub_zero, dens_ofValues_mul_pull L fun _ _ => rfl, HermFrame.ddc, ← hl, HermFrame.kappa, FibCos.fs]`. Use `congr 1`. Use `(nrm_pos hG (v (Fin.last d))).ne'` as an intermediate fact. Use `push_cast`.

Clear the denominators using the available nonvanishing facts.
-/
theorem dens_fibre {d : ℕ} {u : V (d + 1) → ℝ} {v : V (d + 1)} (hu : ContDiffAt ℝ 2 u v)
    {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) (hG' : ∀ x, u (prodPt (basePt v) x) = -Real.log (FibCos.nrm G x))
    (γ β : Alt d) : dens (((ofValues (HermFrame.ddc u v) : Alt (d + 1)) - pull (fderiv ℂ basePt v) γ) *
      pull (fderiv ℂ basePt v) β) = (-FibCos.fs G (v (Fin.last d)) : ℝ) * dens β := by
  let L : V (d + 1) →L[ℂ] V d := LinearMap.toContinuousLinearMap
    { toFun := basePt, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hL : fderiv ℂ basePt v = L := L.fderiv
  let ψ : ℂ → V (d + 1) := fun t => prodPt (basePt v) 0 + t • coordVec (Fin.last d)
  have hψ (t : ℂ) : ψ t = prodPt (basePt v) t := by
    ext a
    induction a using Fin.lastCases <;> simp [ψ, coordVec, EuclideanSpace.single_apply, Fin.castSucc_ne_last]
  have hv : ψ (v (Fin.last d)) = v := by rw [hψ, FibTriv.prodPt_basePt]
  have hd : fderiv ℂ ψ (v (Fin.last d)) 1 = coordVec (Fin.last d) := by
    have : HasFDerivAt ψ _ _ := ((hasFDerivAt_id (𝕜 := ℂ) (v (Fin.last d))).smul_const (coordVec (Fin.last d))).const_add _
    rw [this.fderiv]
    simp
  have hl := leviForm_comp_holo (u := u) (φ := ψ) (z := v (Fin.last d)) (by rwa [hv]) (by fun_prop) 1 1
  simp only [hψ, hG'] at hl
  rw [leviForm_neg, ← hψ, hv, hd, ContinuousLinearMap.neg_apply, ContinuousLinearMap.neg_apply, leviForm_log_nrm hG] at hl
  have h0 : dens (pull L (γ * β)) = 0 := by rw [dens, PullTop.repr_pull_univ, zero_div]
  have hsub (a b : Alt (d + 1)) : dens (a - b) = dens a - dens b := by simp [dens, sub_div]
  rw [hL, sub_mul, ← map_mul, hsub, h0, sub_zero, dens_ofValues_mul_pull L fun _ _ => rfl, HermFrame.ddc, ← hl,
    HermFrame.kappa, FibCos.fs]
  congr 1
  have := (nrm_pos hG (v (Fin.last d))).ne'
  push_cast
  field_simp

/- English proof (translation)
Establish `h (i j) : Measurable fun z : X × ℂ => G z.1 i j` using `(hG i j).comp measurable_fst`. Establish `hc : Measurable fun z : X × ℂ => conj z.2` using `Complex.continuous_conj.measurable.comp measurable_snd`. Establish `hn : Measurable fun z : X × ℂ => FibCos.nrm (G z.1) z.2` using `Complex.measurable_re.comp ((((h 0 0).add (measurable_snd.mul (h 1 0))).add (hc.mul (h 0 1))).add ((Complex.measurable_ofReal.comp (measurable_snd.norm.pow_const 2)).mul (h 1 1)))`. Establish `hd : Measurable fun z : X × ℂ => (G z.1).det.re`. Simplify using `only [Matrix.det_fin_two]`.

Conclude with `Complex.measurable_re.comp (((h 0 0).mul (h 1 1)).sub ((h 0 1).mul (h 1 0)))`. Conclude with `((measurable_const.indicator hJ).comp ((((h 0 0).add (measurable_snd.mul (h 1 0))).norm.pow_const 2).div ((Complex.measurable_re.comp (h 0 0)).mul hn))).mul (hd.div ((hn.pow_const 2).const_mul _)).ennreal_ofReal`.
-/
theorem measurable_kernel {X : Type} [MeasurableSpace X] {G : X → Matrix (Fin 2) (Fin 2) ℂ}
    (hG : ∀ i j, Measurable fun b => G b i j) {J : Set ℝ} (hJ : MeasurableSet J) :
    Measurable (Function.uncurry fun b x => J.indicator (fun _ => (1 : ℝ≥0∞)) (FibCos.cos (G b) x) *
      ENNReal.ofReal (FibCos.fs (G b) x)) := by
  have h (i j) : Measurable fun z : X × ℂ => G z.1 i j := (hG i j).comp measurable_fst
  have hc : Measurable fun z : X × ℂ => conj z.2 := Complex.continuous_conj.measurable.comp measurable_snd
  have hn : Measurable fun z : X × ℂ => FibCos.nrm (G z.1) z.2 :=
    Complex.measurable_re.comp ((((h 0 0).add (measurable_snd.mul (h 1 0))).add (hc.mul (h 0 1))).add
      ((Complex.measurable_ofReal.comp (measurable_snd.norm.pow_const 2)).mul (h 1 1)))
  have hd : Measurable fun z : X × ℂ => (G z.1).det.re := by
    simp only [Matrix.det_fin_two]
    exact Complex.measurable_re.comp (((h 0 0).mul (h 1 1)).sub ((h 0 1).mul (h 1 0)))
  exact ((measurable_const.indicator hJ).comp ((((h 0 0).add (measurable_snd.mul (h 1 0))).norm.pow_const 2).div
    ((Complex.measurable_re.comp (h 0 0)).mul hn))).mul (hd.div ((hn.pow_const 2).const_mul _)).ennreal_ofReal

/- English proof (translation)
Introduce `k _ B Y _ _ q p d hB hY π w E h H flB fl hfl A σ v hv φ hφ ε b₀`. Use `haveI := CxPts.secondCountableTopology_of_isProjOver σ hB.isProjOver`. Use `haveI := CxPts.secondCountableTopology_of_isProjOver σ hY.isProjOver`. Take `⟨c₀, hc₀⟩` from `(hB.atlas σ).cover b₀`. Take `⟨c, hc, hle⟩` from `exists_chart_le c₀ hc₀ (mem_frameAt flB b₀)`.

Set `a` to `(frameAt flB b₀).mid (lineSC_shortExact flB)`. Set `cE : Chart E 2` to `⟨c.U, fun l => Twist.resM E hle (a.e l), a.isFrame.res hle⟩`. Take `⟨W, hW, hWa, n, hΦ, hs⟩` from `GlobalTheory.T.flag_bundle_affine_polynomial_coords B Y π Unit (fun _ => 2) (fun _ => E) (fun _ => fl) hfl (fun _ => h.isVB) c.U c.affine (fun _ => cE.e) fun _ => cE.isFrame`. Use `letI : Unique (Σ _ : Unit, FlagFibre.Low 2) := ⟨⟨⟨(), ⟨(1, 0), by decide⟩⟩⟩, by`. Introduce and unpack `⟨⟨⟩, ⟨⟨i, j⟩, hij⟩⟩`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij (by decide)⟩`. Take `⟨c', hU, hsrc, htgt, hc'⟩` from `exists_prod_chart π w c hW hWa n hΦ hc`. Use `set f := PtsOver.map π w (spMap σ)`. Use `set G := (h.met σ).G cE`. Establish `hG (b) (hb : b ∈ c.e.source) : (G b).PosDef` using `(h.met σ).posDef cE b (c.source_subset hb)`.

Establish `hGm (i j) : Measurable fun b => G b i j`. Establish `h₁ : ContinuousOn (fun b => G b i j) (ptsIn q σ cE.U)` using `fun b hb => (H σ cE b hb i j).continuousAt.continuousWithinAt`. Establish `h₂ : ContinuousOn (fun b => G b i j) (ptsIn q σ cE.U)ᶜ` using `(continuousOn_const (c := 0)).congr fun b hb => by simp only [G, (h.met σ).G_of_notMem cE hb]; rfl`. Simplify using `using h₁.measurable_piecewise h₂ (isOpen_ptsIn _).measurableSet`. Use `⟨c.e.source, c.e.open_source, hc, G, hG, fun S hS hSc J hJ => ?_⟩` and prove the remaining obligations.

Establish `hfm : Measurable f` using `(PtsOver.continuous_map π w _).measurable`. Establish `hT : MeasurableSet (v ⁻¹' J)` using `CosSqMeas.measurable_cosSq k B Y q p d hB hY π w E h H flB fl hfl A σ v hv hJ`. Establish `hf` using `GlobalTheory.T.points_map_holomorphic k B q d hB σ Y p (d + 1) hY π w`. Establish `hpull` using `GlobalTheory.T.first_chern_form_pullback k B q d hB σ Y p (d + 1) hY π w`. Establish `hc₁ (L : HermLB p)` using `(GlobalTheory.T.firstChern_real_closed k Y p (d + 1) hY σ L).1.1`.

Use `set α := evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) (X 0 - X 3) * pullF hB hY σ π w φ`. Establish `hαe : α = (fld _ (c1F hY σ (VMetric.grLB fl 0 (H.pull π w))) + (-1 : ℂ) • fld _ (c1F hY σ ((VMetric.grLB flB 0 H).pull π w))) * pullF hB hY σ π w φ`. Use `congrArg (· * pullF hB hY σ π w φ) (funext fun x => ?_)` and prove the remaining obligations. Simplify using `only [evalF, fld, map_sub, map_X, aeval_X, Pi.add_apply, Pi.smul_apply, neg_one_smul, ← sub_eq_add_neg, AddSubgroupClass.coe_sub]`. Conclude with `sub_eq_add_neg _ _`.

Establish `hαx (x : (hY.atlas σ).Pt) : α x = ((c1F hY σ (VMetric.grLB fl 0 (H.pull π w)) x : Alt (d + 1)) - pullF hB hY σ π w (fld _ (c1F hB σ (VMetric.grLB flB 0 H))) x) * pullF hB hY σ π w φ x`. Rewrite using `[hαe, hpull, Pi.mul_apply, Pi.add_apply, Pi.smul_apply, neg_one_smul, ← sub_eq_add_neg, fld]`. Establish `halg` using `(GlobalTheory.T.isForm_one_add_mul_smul _ _ (hY.atlas σ)).2`. Establish `hα : (hY.atlas σ).IsForm α`. Rewrite using `[hαe]`.

Conclude with `(halg 1 _ _ (halg 1 _ _ (hc₁ _) (halg (-1) _ _ (hc₁ _) (hc₁ (A.pull π w))).2.2).1 (GlobalTheory.T.holAtlas_isForm_pullback_holomorphic _ _ _ _ _ _ _ _ hf hφ)).2.1`. Establish `hbase (y) : basePt (c'.e y) = c.e (f y)` using `by rw [hc', FibTriv.basePt_prodPt]`. Establish `hlast (y) : c'.e y (Fin.last d) = ev p σ W (n default) y` using `by rw [hc', FibTriv.prodPt_last]`. Establish `hA : MeasurableSet (f ⁻¹' S ∩ v ⁻¹' J)` using `(hfm hS).inter hT`. Establish `hnull : (hY.atlas σ).part α ε ((f ⁻¹' S ∩ v ⁻¹' J) \ c'.e.source) = 0`.

Use `measure_mono_null (t := (ptsIn p σ c'.U)ᶜ) (fun y hy hy' => hy.2 ?_) (MixDens.part_compl_ptsIn hY.toIsArithVar (fun c y => (ε : ℤ) * (dens ((hY.atlas σ).loc α c (c.e y))).re) c' ⟨_, c'.e.map_target (x := prodPt (c.e b₀) 0) (by` and prove the remaining obligations. Rewrite using `[htgt, mem_preimage, FibTriv.basePt_prodPt]`. Conclude with `c.e.map_source hc)⟩)`. Rewrite using `[hsrc]`. Conclude with `⟨hSc hy.1.1, hU ▸ hy'⟩`.

Rewrite using `[← measure_inter_add_sdiff _ c'.e.open_source.measurableSet, hnull, add_zero, part_eq_chartMeas _ hα ε c' (hA.inter c'.e.open_source.measurableSet) inter_subset_right, (Measure.restrict_congr_meas hS).2 fun T hTS hT => part_eq_chartMeas _ hφ (-ε) c hT (hTS.trans hSc)]`. Use `(ChartGlue.chartMeas_apply_of_subset c'.e _ (hA.inter c'.e.open_source.measurableSet) inter_subset_right).trans ?_` and prove the remaining obligations. Rewrite using `[inter_comm _ c'.e.source]`. Use `(ChartGlue.chartMeas_apply c'.e (fun y => ENNReal.ofReal ((ε : ℤ) * (dens ((hY.atlas σ).loc α c' (c'.e y))).re)) hA).symm.trans (chartMeas_prod c.e c'.e f (fun y hy => (hsrc ▸ hy).1) htgt (fun y _ => hbase y) _ ?_ _ _ (measurable_kernel hGm hJ) (fun y hy => ?_) hS hSc hA (c'.e.op …` and prove the remaining obligations. Establish `h₁ : ContinuousOn (fun z => ENNReal.ofReal (((-ε : ℤˣ) : ℤ) * (dens ((hB.atlas σ).loc φ c z)).re)) c.e.target` using `ENNReal.continuous_ofReal.comp_continuousOn (continuousOn_const.mul (Complex.continuous_re.comp_continuousOn ((hφ.smooth c Finset.univ).continuousOn.div_const _)))`.

Use `(h₁.congr fun z hz => ?_).aemeasurable c.e.open_target.measurableSet` and prove the remaining obligations. Conclude with `congrArg (fun z => ENNReal.ofReal (((-ε : ℤˣ) : ℤ) * (dens ((hB.atlas σ).loc φ c z)).re)) (c.e.right_inv hz)`. Establish `hy'` using `hsrc ▸ hy`. Take `⟨i, hi, hwt⟩` from `exists_weight (σ := σ) π w cE hW (fun s => n ⟨(), s⟩) H (hs ())`. Establish `hvy` using `cosSq_eq π w cE hW (fun s => n ⟨(), s⟩) (hs ()) (flB.ι 1) (Twist.resM _ hle ((frameAt flB b₀).e 0)) (Twist.app_resM _ _ _) hv hy'.2`.

Establish `hder : fderiv ℂ (c.e ∘ f ∘ c'.e.symm) (c'.e y) = fderiv ℂ basePt (c'.e y)`. Use `Filter.EventuallyEq.fderiv_eq ?_` and prove the remaining obligations. Use `filter_upwards [c'.e.open_target.mem_nhds (c'.e.map_source hy)] with z hz`. Rewrite using `[Function.comp_apply, Function.comp_apply, ← hbase, c'.e.right_inv hz]`. Establish `hp (β) (hβ : (hB.atlas σ).IsForm β) : pullF hB hY σ π w β ⟨(c', y), hy⟩ = pull (fderiv ℂ basePt (c'.e y)) (β ⟨(c, f y), hy'.1⟩)`.

Rewrite using `[← hder]`. Conclude with `pullback_eq_chart _ _ _ _ _ _ _ _ hf hβ ⟨(c', y), hy⟩ c hy'.1`. Establish `hden : dens ((hY.atlas σ).loc α c' (c'.e y)) = (-FibCos.fs (G (f y)) (c'.e y (Fin.last d)) : ℝ) * dens ((hB.atlas σ).loc φ c (c.e (f y)))`. Use `(congrArg dens ((hY.atlas σ).loc_crd α ⟨(c', y), hy⟩)).trans ?_` and prove the remaining obligations. Rewrite using `[show (hB.atlas σ).loc φ c (c.e (f y)) = _ from (hB.atlas σ).loc_crd φ ⟨(c, f y), hy'.1⟩, hαx ⟨(c', y), hy⟩, hp _ hφ, hp _ (GlobalTheory.T.firstChern_real_closed k B q d hB σ _).1.1, c1F_eq_matForm_hessL hY σ _ c' hy i (hi ▸ hy'.2)]`.

Use `dens_fibre ((HermLB.cInf _ σ).contDiffAt c' hy (hi ▸ hy'.2)) (hG _ hy'.1) (fun x => ?_) _ _` and prove the remaining obligations. Establish `hx : prodPt (basePt (c'.e y)) x ∈ c'.e.target`. Rewrite using `[htgt, mem_preimage, FibTriv.basePt_prodPt, ← mem_preimage, ← htgt]`. Conclude with `c'.e.map_source hy`. Establish `hz` using `hsrc ▸ c'.e.map_target hx`.

Establish `e₁` using `hbase (c'.e.symm (prodPt (basePt (c'.e y)) x))`. Establish `e₂` using `hlast (c'.e.symm (prodPt (basePt (c'.e y)) x))`. Rewrite `e₁`, `e₂` using `[c'.e.right_inv hx]`. Rewrite `e₁` using `[FibTriv.basePt_prodPt, hbase]`. Rewrite `e₂` using `[FibTriv.prodPt_last]`.

Rewrite using `[hwt _ hz.2, c.e.injOn hy'.1 hz.1 (e₁.trans (by rw [hbase]))]`. Conclude with `congrArg (fun x => -Real.log (FibCos.nrm _ x)) e₂.symm`. Establish `hfs : 0 ≤ FibCos.fs (G (f y)) (c'.e y (Fin.last d))` using `div_nonneg (Complex.pos_iff.1 (hG _ hy'.1).det_pos).1.le (by positivity)`. Express the relevant statement in the definitionally equal form `_ = J.indicator _ (FibCos.cos (G (f y)) (c'.e y (Fin.last d))) * _ * ENNReal.ofReal (((-ε : ℤˣ) : ℤ) * (dens ((hB.atlas σ).loc φ c (c.e (f y)))).re)`. Rewrite using `[hlast y, show FibCos.cos (G (f y)) (ev p σ W (n default) y) = v y from hvy.symm, ← hlast y]`.

Distinguish the cases in `hJy : v y ∈ J`. Rewrite using `[indicator_of_mem hJy, indicator_of_mem (show y ∈ v ⁻¹' J from hJy), one_mul, hden, Complex.re_ofReal_mul, ← ENNReal.ofReal_mul hfs]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[indicator_of_notMem hJy, indicator_of_notMem (show y ∉ v ⁻¹' J from hJy), zero_mul, zero_mul]`.
-/
theorem local_product : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    ∀ φ : (hB.atlas σ).Fld, (hB.atlas σ).IsForm φ → ∀ ε : ℤˣ, ∀ b₀ : CxPts q σ,
      ∃ U : Set (CxPts q σ), IsOpen U ∧ b₀ ∈ U ∧ ∃ G : CxPts q σ → Matrix (Fin 2) (Fin 2) ℂ, (∀ b ∈ U, (G b).PosDef) ∧
        ∀ S : Set (CxPts q σ), MeasurableSet S → S ⊆ U → ∀ J : Set ℝ, MeasurableSet J →
          (hY.atlas σ).part (evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) (X 0 - X 3) * pullF hB hY σ π w φ) ε
              (PtsOver.map π w (spMap σ) ⁻¹' S ∩ v ⁻¹' J) =
            ∫⁻ b in S, (∫⁻ x : ℂ, J.indicator (fun _ => (1 : ENNReal)) (GlobalTheory.FibCos.cos (G b) x) *
              ENNReal.ofReal (GlobalTheory.FibCos.fs (G b) x)) ∂((hB.atlas σ).part φ (-ε)) := by
  intro k _ B Y _ _ q p d hB hY π w E h H flB fl hfl A σ v hv φ hφ ε b₀
  haveI := CxPts.secondCountableTopology_of_isProjOver σ hB.isProjOver
  haveI := CxPts.secondCountableTopology_of_isProjOver σ hY.isProjOver
  obtain ⟨c₀, hc₀⟩ := (hB.atlas σ).cover b₀
  obtain ⟨c, hc, hle⟩ := exists_chart_le c₀ hc₀ (mem_frameAt flB b₀)
  let a := (frameAt flB b₀).mid (lineSC_shortExact flB)
  let cE : Chart E 2 := ⟨c.U, fun l => Twist.resM E hle (a.e l), a.isFrame.res hle⟩
  obtain ⟨W, hW, hWa, n, hΦ, hs⟩ := GlobalTheory.T.flag_bundle_affine_polynomial_coords B Y π Unit (fun _ => 2) (fun _ => E) (fun _ => fl) hfl
    (fun _ => h.isVB) c.U c.affine (fun _ => cE.e) fun _ => cE.isFrame
  letI : Unique (Σ _ : Unit, FlagFibre.Low 2) := ⟨⟨⟨(), ⟨(1, 0), by decide⟩⟩⟩, by
    rintro ⟨⟨⟩, ⟨⟨i, j⟩, hij⟩⟩
    fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij (by decide)⟩
  obtain ⟨c', hU, hsrc, htgt, hc'⟩ := exists_prod_chart π w c hW hWa n hΦ hc
  set f := PtsOver.map π w (spMap σ)
  set G := (h.met σ).G cE
  have hG (b) (hb : b ∈ c.e.source) : (G b).PosDef := (h.met σ).posDef cE b (c.source_subset hb)
  have hGm (i j) : Measurable fun b => G b i j := by
    have h₁ : ContinuousOn (fun b => G b i j) (ptsIn q σ cE.U) := fun b hb =>
      (H σ cE b hb i j).continuousAt.continuousWithinAt
    have h₂ : ContinuousOn (fun b => G b i j) (ptsIn q σ cE.U)ᶜ :=
      (continuousOn_const (c := 0)).congr fun b hb => by simp only [G, (h.met σ).G_of_notMem cE hb]; rfl
    simpa using h₁.measurable_piecewise h₂ (isOpen_ptsIn _).measurableSet
  refine ⟨c.e.source, c.e.open_source, hc, G, hG, fun S hS hSc J hJ => ?_⟩
  have hfm : Measurable f := (PtsOver.continuous_map π w _).measurable
  have hT : MeasurableSet (v ⁻¹' J) :=
    CosSqMeas.measurable_cosSq k B Y q p d hB hY π w E h H flB fl hfl A σ v hv hJ
  have hf := GlobalTheory.T.points_map_holomorphic k B q d hB σ Y p (d + 1) hY π w
  have hpull := GlobalTheory.T.first_chern_form_pullback k B q d hB σ Y p (d + 1) hY π w
  have hc₁ (L : HermLB p) := (GlobalTheory.T.firstChern_real_closed k Y p (d + 1) hY σ L).1.1
  set α := evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) (X 0 - X 3) * pullF hB hY σ π w φ
  have hαe : α = (fld _ (c1F hY σ (VMetric.grLB fl 0 (H.pull π w))) +
      (-1 : ℂ) • fld _ (c1F hY σ ((VMetric.grLB flB 0 H).pull π w))) * pullF hB hY σ π w φ := by
    refine congrArg (· * pullF hB hY σ π w φ) (funext fun x => ?_)
    simp only [evalF, fld, map_sub, map_X, aeval_X, Pi.add_apply, Pi.smul_apply, neg_one_smul, ← sub_eq_add_neg,
      AddSubgroupClass.coe_sub]
    exact sub_eq_add_neg _ _
  have hαx (x : (hY.atlas σ).Pt) : α x = ((c1F hY σ (VMetric.grLB fl 0 (H.pull π w)) x : Alt (d + 1)) -
      pullF hB hY σ π w (fld _ (c1F hB σ (VMetric.grLB flB 0 H))) x) * pullF hB hY σ π w φ x := by
    rw [hαe, hpull, Pi.mul_apply, Pi.add_apply, Pi.smul_apply, neg_one_smul, ← sub_eq_add_neg, fld]
  have halg := (GlobalTheory.T.isForm_one_add_mul_smul _ _ (hY.atlas σ)).2
  have hα : (hY.atlas σ).IsForm α := by
    rw [hαe]
    exact (halg 1 _ _ (halg 1 _ _ (hc₁ _) (halg (-1) _ _ (hc₁ _) (hc₁ (A.pull π w))).2.2).1
      (GlobalTheory.T.holAtlas_isForm_pullback_holomorphic _ _ _ _ _ _ _ _ hf hφ)).2.1
  have hbase (y) : basePt (c'.e y) = c.e (f y) := by rw [hc', FibTriv.basePt_prodPt]
  have hlast (y) : c'.e y (Fin.last d) = ev p σ W (n default) y := by rw [hc', FibTriv.prodPt_last]
  have hA : MeasurableSet (f ⁻¹' S ∩ v ⁻¹' J) := (hfm hS).inter hT
  have hnull : (hY.atlas σ).part α ε ((f ⁻¹' S ∩ v ⁻¹' J) \ c'.e.source) = 0 := by
    refine measure_mono_null (t := (ptsIn p σ c'.U)ᶜ) (fun y hy hy' => hy.2 ?_) (MixDens.part_compl_ptsIn hY.toIsArithVar
      (fun c y => (ε : ℤ) * (dens ((hY.atlas σ).loc α c (c.e y))).re) c'
      ⟨_, c'.e.map_target (x := prodPt (c.e b₀) 0) (by
        rw [htgt, mem_preimage, FibTriv.basePt_prodPt]; exact c.e.map_source hc)⟩)
    rw [hsrc]
    exact ⟨hSc hy.1.1, hU ▸ hy'⟩
  rw [← measure_inter_add_sdiff _ c'.e.open_source.measurableSet, hnull, add_zero,
    part_eq_chartMeas _ hα ε c' (hA.inter c'.e.open_source.measurableSet) inter_subset_right,
    (Measure.restrict_congr_meas hS).2 fun T hTS hT => part_eq_chartMeas _ hφ (-ε) c hT (hTS.trans hSc)]
  refine (ChartGlue.chartMeas_apply_of_subset c'.e _ (hA.inter c'.e.open_source.measurableSet) inter_subset_right).trans ?_
  rw [inter_comm _ c'.e.source]
  refine (ChartGlue.chartMeas_apply c'.e
    (fun y => ENNReal.ofReal ((ε : ℤ) * (dens ((hY.atlas σ).loc α c' (c'.e y))).re)) hA).symm.trans
    (chartMeas_prod c.e c'.e f (fun y hy => (hsrc ▸ hy).1) htgt
    (fun y _ => hbase y) _ ?_ _ _ (measurable_kernel hGm hJ) (fun y hy => ?_) hS hSc hA
    (c'.e.open_source.measurableSet.inter hT))
  · have h₁ : ContinuousOn (fun z => ENNReal.ofReal (((-ε : ℤˣ) : ℤ) * (dens ((hB.atlas σ).loc φ c z)).re)) c.e.target :=
      ENNReal.continuous_ofReal.comp_continuousOn (continuousOn_const.mul (Complex.continuous_re.comp_continuousOn
        ((hφ.smooth c Finset.univ).continuousOn.div_const _)))
    refine (h₁.congr fun z hz => ?_).aemeasurable c.e.open_target.measurableSet
    exact congrArg (fun z => ENNReal.ofReal (((-ε : ℤˣ) : ℤ) * (dens ((hB.atlas σ).loc φ c z)).re)) (c.e.right_inv hz)
  have hy' := hsrc ▸ hy
  obtain ⟨i, hi, hwt⟩ := exists_weight (σ := σ) π w cE hW (fun s => n ⟨(), s⟩) H (hs ())
  have hvy := cosSq_eq π w cE hW (fun s => n ⟨(), s⟩) (hs ()) (flB.ι 1) (Twist.resM _ hle ((frameAt flB b₀).e 0))
    (Twist.app_resM _ _ _) hv hy'.2
  have hder : fderiv ℂ (c.e ∘ f ∘ c'.e.symm) (c'.e y) = fderiv ℂ basePt (c'.e y) := by
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [c'.e.open_target.mem_nhds (c'.e.map_source hy)] with z hz
    rw [Function.comp_apply, Function.comp_apply, ← hbase, c'.e.right_inv hz]
  have hp (β) (hβ : (hB.atlas σ).IsForm β) : pullF hB hY σ π w β ⟨(c', y), hy⟩ =
      pull (fderiv ℂ basePt (c'.e y)) (β ⟨(c, f y), hy'.1⟩) := by
    rw [← hder]
    exact pullback_eq_chart _ _ _ _ _ _ _ _ hf hβ ⟨(c', y), hy⟩ c hy'.1
  have hden : dens ((hY.atlas σ).loc α c' (c'.e y)) =
      (-FibCos.fs (G (f y)) (c'.e y (Fin.last d)) : ℝ) * dens ((hB.atlas σ).loc φ c (c.e (f y))) := by
    refine (congrArg dens ((hY.atlas σ).loc_crd α ⟨(c', y), hy⟩)).trans ?_
    rw [show (hB.atlas σ).loc φ c (c.e (f y)) = _ from (hB.atlas σ).loc_crd φ ⟨(c, f y), hy'.1⟩, hαx ⟨(c', y), hy⟩,
      hp _ hφ, hp _ (GlobalTheory.T.firstChern_real_closed k B q d hB σ _).1.1, c1F_eq_matForm_hessL hY σ _ c' hy i (hi ▸ hy'.2)]
    refine dens_fibre ((HermLB.cInf _ σ).contDiffAt c' hy (hi ▸ hy'.2)) (hG _ hy'.1) (fun x => ?_) _ _
    have hx : prodPt (basePt (c'.e y)) x ∈ c'.e.target := by
      rw [htgt, mem_preimage, FibTriv.basePt_prodPt, ← mem_preimage, ← htgt]
      exact c'.e.map_source hy
    have hz := hsrc ▸ c'.e.map_target hx
    have e₁ := hbase (c'.e.symm (prodPt (basePt (c'.e y)) x))
    have e₂ := hlast (c'.e.symm (prodPt (basePt (c'.e y)) x))
    rw [c'.e.right_inv hx] at e₁ e₂
    rw [FibTriv.basePt_prodPt, hbase] at e₁
    rw [FibTriv.prodPt_last] at e₂
    rw [hwt _ hz.2, c.e.injOn hy'.1 hz.1 (e₁.trans (by rw [hbase]))]
    exact congrArg (fun x => -Real.log (FibCos.nrm _ x)) e₂.symm
  have hfs : 0 ≤ FibCos.fs (G (f y)) (c'.e y (Fin.last d)) :=
    div_nonneg (Complex.pos_iff.1 (hG _ hy'.1).det_pos).1.le (by positivity)
  change _ = J.indicator _ (FibCos.cos (G (f y)) (c'.e y (Fin.last d))) * _ *
    ENNReal.ofReal (((-ε : ℤˣ) : ℤ) * (dens ((hB.atlas σ).loc φ c (c.e (f y)))).re)
  rw [hlast y, show FibCos.cos (G (f y)) (ev p σ W (n default) y) = v y from hvy.symm, ← hlast y]
  by_cases hJy : v y ∈ J
  · rw [indicator_of_mem hJy, indicator_of_mem (show y ∈ v ⁻¹' J from hJy), one_mul, hden, Complex.re_ofReal_mul,
      ← ENNReal.ofReal_mul hfs]
    congr 1
    push_cast
    ring
  · rw [indicator_of_notMem hJy, indicator_of_notMem (show y ∉ v ⁻¹' J from hJy), zero_mul, zero_mul]

end GlobalTheory.FibLoc
