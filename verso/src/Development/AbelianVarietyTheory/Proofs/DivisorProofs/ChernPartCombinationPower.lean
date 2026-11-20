import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartOverProperClosedEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralIndependentOfCoefficient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernDensDetWeightEqNegLeviLog

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open GlobalTheory.Points GlobalTheory.HermFrame
open scoped Classical

namespace GlobalTheory.ChernTop

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp [add_comm]`. Consider the case `succ m ih`. Rewrite using `[pow_succ, ih]`. Use `push_cast`.

Take the linear combination `((m : R) + 1) * S ^ m * ht`.
-/
theorem add_pow_of_sq_zero {R : Type} [CommRing R] (S t : R) (ht : t * t = 0) (m : ℕ) :
    (t + S) ^ (m + 1) = S ^ (m + 1) + ((m : R) + 1) * t * S ^ m := by
  induction m with
  | zero => simp [add_comm]
  | succ m ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination ((m : R) + 1) * S ^ m * ht

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha, add_pow_of_sq_zero _ _ (ht a), add_pow_of_sq_zero _ _ (ht a), pow_succ _ (s.card + 1), ih.1, ih.2, Nat.factorial_succ]`. Use `push_cast`.

Apply the tactic sequence `constructor <;> ring`.
-/
theorem sum_pow_card {R α : Type} [CommRing R] (t : α → R) (ht : ∀ a, t a * t a = 0) (s : Finset α) :
    (∑ a ∈ s, t a) ^ s.card = (s.card.factorial : R) * ∏ a ∈ s, t a ∧ (∑ a ∈ s, t a) ^ (s.card + 1) = 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha,
      add_pow_of_sq_zero _ _ (ht a), add_pow_of_sq_zero _ _ (ht a), pow_succ _ (s.card + 1), ih.1, ih.2,
      Nat.factorial_succ]
    push_cast
    constructor <;> ring

variable {n : ℕ}

def rowForm (a : Fin n) : (Fin n → ℂ) →ₗ[ℂ] Ev n := Fintype.linearCombination ℂ fun b => sym (a, b)

/- English proof (translation)
Simplify using `only [rowForm, Fintype.linearCombination_apply, AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_smul, sym, map_sum, map_smul, Finset.mul_sum, mul_smul_comm, dzb]`.
-/
theorem coe_rowForm (a : Fin n) (u : Fin n → ℂ) :
    (rowForm a u : Alt n) = dz a * ExteriorAlgebra.ι ℂ (∑ b, u b • Pi.single (Sum.inr b : Fin n ⊕ Fin n) (1 : ℂ)) := by
  simp only [rowForm, Fintype.linearCombination_apply, AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_smul, sym,
    map_sum, map_smul, Finset.mul_sum, mul_smul_comm, dzb]

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Subalgebra.coe_mul, ← Subalgebra.mem_center_iff.1 (rowForm a u).2, coe_rowForm a']`. Establish `h` using `Subalgebra.mem_center_iff.1 (rowForm a u).2`. Rewrite using `[mul_assoc, h, coe_rowForm, mul_assoc, ExteriorAlgebra.ι_sq_zero, mul_zero, mul_zero]`. Both sides reduce to the same expression.
-/
theorem rowForm_mul_same (a a' : Fin n) (u : Fin n → ℂ) : rowForm a u * rowForm a' u = 0 := by
  apply Subtype.ext
  rw [Subalgebra.coe_mul, ← Subalgebra.mem_center_iff.1 (rowForm a u).2, coe_rowForm a']
  have h := Subalgebra.mem_center_iff.1 (rowForm a u).2
  rw [mul_assoc, h, coe_rowForm, mul_assoc, ExteriorAlgebra.ι_sq_zero, mul_zero, mul_zero]
  rfl

def densL (n : ℕ) : Ev n →ₗ[ℂ] ℂ where
  toFun α := dens (α : Alt n)
  map_add' α β := by simp [dens, add_div]
  map_smul' c α := by simp [dens, mul_div_assoc]

def rowDeterminantForm (n : ℕ) : (Fin n → ℂ) [⋀^Fin n]→ₗ[ℂ] ℂ where
  toMultilinearMap := (densL n).compMultilinearMap
    ((MultilinearMap.mkPiAlgebra ℂ (Fin n) (Ev n)).compLinearMap rowForm)
  map_eq_zero_of_eq' v i j h hij := by
    change densL n (∏ a, rowForm a (v a)) = 0
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      ← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨hij.symm, Finset.mem_univ j⟩), ← mul_assoc, h,
      rowForm_mul_same, zero_mul, map_zero]

/- English proof (translation)
Establish `h` using `congrArg (· A) ((rowDeterminantForm n).eq_smul_basis_det (Pi.basisFun ℂ (Fin n)))`. Establish `h₁ : (Complex.I / 2) ^ n * rowDeterminantForm n (Pi.basisFun ℂ (Fin n)) = 1`. Rewrite using `[← dens_vol n]`. Express the relevant statement in the definitionally equal form `_ * densL n (∏ a, rowForm a (Pi.basisFun ℂ (Fin n) a)) = densL n (vol n)`. Rewrite using `[vol, Finset.prod_smul, map_smul, Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]`.

Simplify using `[rowForm]`. Express the relevant statement in the definitionally equal form `_ * rowDeterminantForm n A = _`. Use `(congrArg _ h).trans ((mul_assoc _ _ _).symm.trans ?_)` and prove the remaining obligations. Rewrite using `[h₁, one_mul]`. Conclude with `Pi.basisFun_det_apply _`.
-/
theorem dens_prod_rowForm (A : Matrix (Fin n) (Fin n) ℂ) :
    (Complex.I / 2) ^ n * densL n (∏ a, rowForm a (A a)) = A.det := by
  have h := congrArg (· A) ((rowDeterminantForm n).eq_smul_basis_det (Pi.basisFun ℂ (Fin n)))
  have h₁ : (Complex.I / 2) ^ n * rowDeterminantForm n (Pi.basisFun ℂ (Fin n)) = 1 := by
    rw [← dens_vol n]
    change _ * densL n (∏ a, rowForm a (Pi.basisFun ℂ (Fin n) a)) = densL n (vol n)
    rw [vol, Finset.prod_smul, map_smul, Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    simp [rowForm]
  change _ * rowDeterminantForm n A = _
  refine (congrArg _ h).trans ((mul_assoc _ _ _).symm.trans ?_)
  rw [h₁, one_mul]
  exact Pi.basisFun_det_apply _

def matForm (n : ℕ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Ev n where
  toFun H := kappa • ∑ a, rowForm a (H a)
  map_add' H H' := by
    rw [← smul_add, ← Finset.sum_add_distrib]
    exact congrArg _ (Finset.sum_congr rfl fun a _ => map_add _ _ _)
  map_smul' c H := by
    rw [RingHom.id_apply, smul_comm, Finset.smul_sum (r := c)]
    exact congrArg _ (Finset.sum_congr rfl fun a _ => map_smul (rowForm a) c (H a))

/- English proof (translation)
Establish `h` using `(sum_pow_card (fun a => rowForm a (H a)) (fun a => rowForm_mul_same a a _) Finset.univ).1`. Rewrite `h` using `[Finset.card_univ, Fintype.card_fin]`. Express the relevant statement in the definitionally equal form `densL n ((kappa • ∑ a, rowForm a (H a)) ^ n) = _`. Establish `e : kappa = (Real.pi : ℂ)⁻¹ * (Complex.I / 2)`. Rewrite using `[kappa]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[smul_pow, h, ← nsmul_eq_mul, map_smul, map_nsmul, ← dens_prod_rowForm, e]`. Simplify using `only [smul_eq_mul, nsmul_eq_mul, mul_pow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dens_matForm_pow (H : Matrix (Fin n) (Fin n) ℂ) :
    dens ((matForm n H ^ n : Ev n) : Alt n) = ((n.factorial / Real.pi ^ n : ℝ) : ℂ) * H.det := by
  have h := (sum_pow_card (fun a => rowForm a (H a)) (fun a => rowForm_mul_same a a _) Finset.univ).1
  rw [Finset.card_univ, Fintype.card_fin] at h
  change densL n ((kappa • ∑ a, rowForm a (H a)) ^ n) = _
  have e : kappa = (Real.pi : ℂ)⁻¹ * (Complex.I / 2) := by
    rw [kappa]; ring
  rw [smul_pow, h, ← nsmul_eq_mul, map_smul, map_nsmul, ← dens_prod_rowForm, e]
  simp only [smul_eq_mul, nsmul_eq_mul, mul_pow]
  push_cast
  ring

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} {σ : k →+* ℂ}

abbrev hessL (L : HermLB p) (c : AlgChart p σ D) (y : CxPts p σ) : Matrix (Fin D) (Fin D) ℂ :=
  c.hess (L.φ σ) (pick (L.φ σ).isLB y) y

variable {c : AlgChart p σ D} {y : CxPts p σ}

/- English proof (translation)
Establish `hd` using `(L.cInf σ).contDiffAt c hy (mem_pick (L.φ σ).isLB y)`. Express the relevant statement in the definitionally equal form `ofValues _ = kappa • ∑ a, rowForm a _`. Simplify using `only [ofValues, rowForm, Fintype.linearCombination_apply, Finset.smul_sum, smul_smul]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Use `congr 1`.

Conclude with `congrArg (kappa * ·) (CurveDens.cHess_apply_eq_ddbar (contDiffAt_ofReal_comp hd) a b).symm`.
-/
theorem c1F_eq_matForm_hessL (hX : IsRegVar p D) (L : HermLB p) (hy : y ∈ c.e.source) :
    c1F hX σ L ⟨(c, y), hy⟩ = matForm D (hessL L c y) := by
  have hd := (L.cInf σ).contDiffAt c hy (mem_pick (L.φ σ).isLB y)
  change ofValues _ = kappa • ∑ a, rowForm a _
  simp only [ofValues, rowForm, Fintype.linearCombination_apply, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  exact congrArg (kappa * ·) (CurveDens.cHess_apply_eq_ddbar (contDiffAt_ofReal_comp hd) a b).symm

/- English proof (translation)
Establish `ha` using `mem_pick (L.φ σ).isLB y`. Establish `hb` using `mem_pick (M.φ σ).isLB y`. Conclude with `(c.hess_eq ((L.tens M).cInf σ) hy (i := (pick (L.φ σ).isLB y, pick (M.φ σ).isLB y)) (mem_ptsIn_inf.2 ⟨ha, hb⟩) (mem_pick _ y)).trans (FlatMass.hess_tens (L.cInf σ) (M.cInf σ) hy ha hb)`.
-/
theorem hessL_tens (L M : HermLB p) (hy : y ∈ c.e.source) : hessL (L.tens M) c y = hessL L c y + hessL M c y := by
  have ha := mem_pick (L.φ σ).isLB y
  have hb := mem_pick (M.φ σ).isLB y
  exact (c.hess_eq ((L.tens M).cInf σ) hy (i := (pick (L.φ σ).isLB y, pick (M.φ σ).isLB y))
    (mem_ptsIn_inf.2 ⟨ha, hb⟩) (mem_pick _ y)).trans (FlatMass.hess_tens (L.cInf σ) (M.cInf σ) hy ha hb)

/- English proof (translation)
Establish `ha` using `mem_pick (L.φ σ).isLB y`. Conclude with `(c.hess_eq (L.dual.cInf σ) hy (i := (pick (L.φ σ).isLB y : L.B.ι)) ha (mem_pick _ y)).trans (FlatMass.hess_dual (L.cInf σ) hy ha)`.
-/
theorem hessL_dual (L : HermLB p) (hy : y ∈ c.e.source) : hessL L.dual c y = -hessL L c y := by
  have ha := mem_pick (L.φ σ).isLB y
  exact (c.hess_eq (L.dual.cInf σ) hy (i := (pick (L.φ σ).isLB y : L.B.ι)) ha (mem_pick _ y)).trans
    (FlatMass.hess_dual (L.cInf σ) hy ha)

/- English proof (translation)
Establish `ha` using `mem_pick (L.φ σ).isLB y`. Use `(c.hess_eq ((L.pow m).cInf σ) hy (i := fun _ => pick (L.φ σ).isLB y) (mem_pow_iff.2 ha) (mem_pick _ y)).trans ((FlatMass.hess_zpow (L.cInf σ) hy (m : ℤ) _ ha).trans ?_)` and prove the remaining obligations. Rewrite using `[Int.cast_natCast]`.
-/
theorem hessL_pow (L : HermLB p) (m : ℕ) (hy : y ∈ c.e.source) : hessL (L.pow m) c y = (m : ℂ) • hessL L c y := by
  have ha := mem_pick (L.φ σ).isLB y
  refine (c.hess_eq ((L.pow m).cInf σ) hy (i := fun _ => pick (L.φ σ).isLB y) (mem_pow_iff.2 ha)
    (mem_pick _ y)).trans ((FlatMass.hess_zpow (L.cInf σ) hy (m : ℤ) _ ha).trans ?_)
  rw [Int.cast_natCast]

/- English proof (translation)
Rewrite using `[zp, hessL_tens _ _ hy, hessL_dual _ hy, hessL_pow _ _ hy, hessL_pow _ _ hy, ← sub_eq_add_neg, ← sub_smul]`. Use `congr 1`. Conclude with `Int.toNat_sub_toNat_neg m` after adjusting the coercions.
-/
theorem hessL_zp (L : HermLB p) (m : ℤ) (hy : y ∈ c.e.source) : hessL (zp L m) c y = (m : ℂ) • hessL L c y := by
  rw [zp, hessL_tens _ _ hy, hessL_dual _ hy, hessL_pow _ _ hy, hessL_pow _ _ hy, ← sub_eq_add_neg, ← sub_smul]
  congr 1
  exact_mod_cast Int.toNat_sub_toNat_neg m

/- English proof (translation)
Rewrite using `[comb, ← Finset.sum_map_toList]`. Proceed by induction on `(Finset.univ : Finset ι).toList with`. Consider the case `nil => exact FlatMass.cHess_zero _`. Consider the case `cons i l ih => rw [List.foldr_cons, hessL_tens _ _ hy, ih, hessL_zp _ _ hy, List.map_cons, List.sum_cons]`.
-/
theorem hessL_comb {ι : Type} [Fintype ι] (L : ι → HermLB p) (m : ι → ℤ) (hy : y ∈ c.e.source) :
    hessL (comb L m) c y = ∑ i, (m i : ℂ) • hessL (L i) c y := by
  rw [comb, ← Finset.sum_map_toList]
  induction (Finset.univ : Finset ι).toList with
  | nil => exact FlatMass.cHess_zero _
  | cons i l ih => rw [List.foldr_cons, hessL_tens _ _ hy, ih, hessL_zp _ _ hy, List.map_cons, List.sum_cons]

/- English proof (translation)
Introduce `k _ X p D hX σ ι _ L n ε`. Establish `key (c : AlgChart p σ D) (y) (hy : y ∈ c.e.source) : c.chernDens ((comb L n).φ σ) y = (dens ((hX.atlas σ).loc (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D)) c (c.e y))).re`. Use `Eq.trans ?_ (congrArg (fun t => (dens t).re) ((hX.atlas σ).loc_crd _ ⟨(c, y), hy⟩)).symm` and prove the remaining obligations. Establish `e : aeval (fun i => c1F hX σ (L i) ⟨(c, y), hy⟩) ((lin (fun i => (n i : ℝ)) ^ D).map (algebraMap ℝ ℂ)) = matForm D (hessL (comb L n) c y) ^ D`. Rewrite using `[hessL_comb L n hy]`.

Simplify using `only [lin, map_pow, map_sum, map_mul, map_C, map_X, aeval_C, aeval_X, map_smul, c1F_eq_matForm_hessL hX _ hy]`. Simplify using `[Algebra.smul_def]`. Express the relevant statement in the definitionally equal form `_ = (dens ((aeval (fun i => c1F hX σ (L i) ⟨(c, y), hy⟩) ((lin (fun i => (n i : ℝ)) ^ D).map (algebraMap ℝ ℂ)) : Ev D) : Alt D)).re`. Rewrite using `[e, dens_matForm_pow, Complex.re_ofReal_mul]`. Both sides reduce to the same expression.

Use `iSup_congr fun c => congrArg (Measure.map _) (withDensity_congr_ae ?_)` and prove the remaining obligations. Use `filter_upwards [ae_restrict_mem c.e.open_target.measurableSet] with v hv`. Conclude with `congrArg (fun t => ENNReal.ofReal (_ * t)) (key c _ (c.e.map_target hv))`.
-/
theorem chernPart_comb_eq_part : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (hX : IsRegVar p D) (σ : k →+* ℂ)
    {ι : Type} [Fintype ι] (L : ι → HermLB p) (n : ι → ℤ) (ε : ℤˣ),
    ((comb L n).φ σ).chernPart D ε = (hX.atlas σ).part (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D)) ε := by
  intro k _ X p D hX σ ι _ L n ε
  have key (c : AlgChart p σ D) (y) (hy : y ∈ c.e.source) : c.chernDens ((comb L n).φ σ) y =
      (dens ((hX.atlas σ).loc (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D))
        c (c.e y))).re := by
    refine Eq.trans ?_ (congrArg (fun t => (dens t).re) ((hX.atlas σ).loc_crd _ ⟨(c, y), hy⟩)).symm
    have e : aeval (fun i => c1F hX σ (L i) ⟨(c, y), hy⟩) ((lin (fun i => (n i : ℝ)) ^ D).map (algebraMap ℝ ℂ)) =
        matForm D (hessL (comb L n) c y) ^ D := by
      rw [hessL_comb L n hy]
      simp only [lin, map_pow, map_sum, map_mul, map_C, map_X, aeval_C, aeval_X, map_smul, c1F_eq_matForm_hessL hX _ hy]
      simp [Algebra.smul_def]
    change _ = (dens ((aeval (fun i => c1F hX σ (L i) ⟨(c, y), hy⟩)
      ((lin (fun i => (n i : ℝ)) ^ D).map (algebraMap ℝ ℂ)) : Ev D) : Alt D)).re
    rw [e, dens_matForm_pow, Complex.re_ofReal_mul]
    rfl
  refine iSup_congr fun c => congrArg (Measure.map _) (withDensity_congr_ae ?_)
  filter_upwards [ae_restrict_mem c.e.open_target.measurableSet] with v hv
  exact congrArg (fun t => ENNReal.ofReal (_ * t)) (key c _ (c.e.map_target hv))

end GlobalTheory.ChernTop
