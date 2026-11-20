import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColumnData
import Formalism.LocalToGlobal.KernelLattices.ColumnData.LinkThIndep
import Formalism.LocalToGlobal.KernelLattices.ColumnData.LinkThU
import Formalism.GL3MeanSquares.HookFormulaTorsion.SquareEqDiagOfQuadraticEven

noncomputable section

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Classical
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

variable {D : Car} {N N' : ℕ}

/- English proof (translation)
Unfold `Hf`. Rewrite using `[← add_div]`. Use `congr 1`. Simplify using `only [Pi.add_apply, add_mul, Finset.sum_add_distrib]`.
-/
theorem Hf_add_left (T : Tor D) (x x' y : VC D N N') :
    Hf D T (x + x') y = Hf D T x y + Hf D T x' y := by
  unfold Hf
  rw [← add_div]
  congr 1
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Unfold `Hf`. Rewrite using `[map_div₀]`. Use `congr 1`. Simplify using `only [map_sum, map_mul, Complex.conj_conj]`. Use `Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.
-/
theorem Hf_herm (T : Tor D) (x y : VC D N N') :
    Hf D T y x = starRingEnd ℂ (Hf D T x y) := by
  unfold Hf
  rw [map_div₀]
  congr 1
  · simp only [map_sum, map_mul, Complex.conj_conj]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => ?_
    ring
  · simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem U_eq_heis (T : Tor D) (x : VC D N N') (G : VC D N N' → ℂ) :
    U D T x G = Formalism.HermitianLattices.WeilRepresentation.Heisenberg₂ (Hf D T) x G := rfl

def cf (T : Tor D) (x y : VC D N N') : ℂ :=
  Complex.exp (-((Real.pi : ℂ) * Complex.I * ((Hf D T x y).im : ℂ)))

/- English proof (translation)
Rewrite using `[Hf_herm T (y + y') x, Hf_add_left T y y' x, map_add, ← Hf_herm T y x, ← Hf_herm T y' x]`.
-/
private theorem Hf_add_right_lemma (T : Tor D) (x y y' : VC D N N') :
    Hf D T x (y + y') = Hf D T x y + Hf D T x y' := by
  rw [Hf_herm T (y + y') x, Hf_add_left T y y' x, map_add, ← Hf_herm T y x, ← Hf_herm T y' x]

/- English proof (translation)
Establish `hc : starRingEnd ℂ (Hf D T x y) = Hf D T x y - 2 * ((Hf D T x y).im : ℂ) * Complex.I`. Apply the tactic sequence `apply Complex.ext <;> simp <;> ring`. Simplify using `only [U, cf]`. Rewrite using `[add_assoc z x y, Hf_add_left T z x y, Hf_add_right_lemma T z x y, Hf_add_left T x y (x + y), Hf_add_right_lemma T x x y, Hf_add_right_lemma T y x y, Hf_herm T x y, hc]`. Rewrite using `[mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add]`.

Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem U_U (T : Tor D) (x y : VC D N N') (G : VC D N N' → ℂ) (z : VC D N N') :
    U D T x (U D T y G) z = cf T x y * U D T (x + y) G z := by
  have hc : starRingEnd ℂ (Hf D T x y) = Hf D T x y - 2 * ((Hf D T x y).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp <;> ring
  simp only [U, cf]
  rw [add_assoc z x y, Hf_add_left T z x y, Hf_add_right_lemma T z x y, Hf_add_left T x y (x + y),
    Hf_add_right_lemma T x x y, Hf_add_right_lemma T y x y, Hf_herm T x y, hc]
  rw [mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add]
  congr 2
  ring

/- English proof (translation)
Simplify using `only [U]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem U_smul (T : Tor D) (x : VC D N N') (c : ℂ) (G : VC D N N' → ℂ) (z : VC D N N') :
    U D T x (fun w => c * G w) z = c * U D T x G z := by
  simp only [U]
  ring

/- English proof (translation)
Simplify using `[U]`.
-/
theorem U_zero_fn (T : Tor D) (x : VC D N N') (z : VC D N N') :
    U D T x (fun _ => (0 : ℂ)) z = 0 := by
  simp [U]

def SemiChar (T : Tor D) (La' : AddSubgroup (VC D N N')) : Prop :=
  ∀ x ∈ La', ∀ y ∈ La', al D T (x + y) = al D T x * al D T y * cf T x y

/- English proof (translation)
Establish `hG' : Differentiable ℂ G ∧ ∀ x ∈ La', ∀ z, al D T x * U D T x G z = G z` using `hG`. Use function extensionality and compare the values at `w`. Conclude with `hG'.2 y hy w`.
-/
theorem fix_eq (T : Tor D) {La' : AddSubgroup (VC D N N')} {G : VC D N N' → ℂ}
    (hG : G ∈ ThSp D T La') {y : VC D N N'} (hy : y ∈ La') :
    (fun w => al D T y * U D T y G w) = G := by
  have hG' : Differentiable ℂ G ∧ ∀ x ∈ La', ∀ z, al D T x * U D T x G z = G z := hG
  funext w
  exact hG'.2 y hy w

/- English proof (translation)
Use `conv_lhs => rw [← fix_eq T hG hy]`. Rewrite using `[U_smul T x (al D T y) (U D T y G) z, U_U T x y G z]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem two_step (T : Tor D) {La' : AddSubgroup (VC D N N')} {G : VC D N N' → ℂ}
    (hG : G ∈ ThSp D T La') {y : VC D N N'} (hy : y ∈ La') (x z : VC D N N') :
    al D T x * U D T x G z = al D T x * al D T y * cf T x y * U D T (x + y) G z := by
  conv_lhs => rw [← fix_eq T hG hy]
  rw [U_smul T x (al D T y) (U D T y G) z, U_U T x y G z]
  ring

/- English proof (translation)
Take `⟨z₀, hz₀⟩` from `hne`. Unfold `SemiChar`. Introduce `x hx y hy`. Establish `h1` using `congrFun (fix_eq T hG (La'.add_mem hx hy)) z₀`. Establish `h2` using `congrFun (fix_eq T hG hx) z₀`.

Establish `h3` using `two_step T hG hy x z₀`. Apply the tactic sequence `try dsimp only at h1`. Apply the tactic sequence `try dsimp only at h2`. Establish `hu : U D T (x + y) G z₀ ≠ 0`. Introduce `h0`.

Apply `hz₀` to reduce the goal to its premises. Rewrite using `[← h1, h0, mul_zero]`. Apply `mul_right_cancel₀ hu` to reduce the goal to its premises. Rewrite using `[h1, ← h3, h2]`.
-/
theorem semiChar_of_ne_zero (T : Tor D) {La' : AddSubgroup (VC D N N')} {G : VC D N N' → ℂ}
    (hG : G ∈ ThSp D T La') (hne : ∃ z, G z ≠ 0) : SemiChar T La' := by
  obtain ⟨z₀, hz₀⟩ := hne
  unfold SemiChar
  intro x hx y hy
  have h1 := congrFun (fix_eq T hG (La'.add_mem hx hy)) z₀
  have h2 := congrFun (fix_eq T hG hx) z₀
  have h3 := two_step T hG hy x z₀
  try dsimp only at h1
  try dsimp only at h2
  have hu : U D T (x + y) G z₀ ≠ 0 := by
    intro h0
    apply hz₀
    rw [← h1, h0, mul_zero]
  apply mul_right_cancel₀ hu
  rw [h1, ← h3, h2]

/- English proof (translation)
Rewrite using `[hS x hx y hy₂]`. Conclude with `(two_step T hG hy₁ x z).symm`.
-/
theorem rep_shift (T : Tor D) {La₁ La₂ : AddSubgroup (VC D N N')} (hS : SemiChar T La₂)
    {G : VC D N N' → ℂ} (hG : G ∈ ThSp D T La₁) {x y : VC D N N'} (hx : x ∈ La₂)
    (hy₁ : y ∈ La₁) (hy₂ : y ∈ La₂) (z : VC D N N') :
    al D T (x + y) * U D T (x + y) G z = al D T x * U D T x G z := by
  rw [hS x hx y hy₂]
  exact (two_step T hG hy₁ x z).symm

/- English proof (translation)
Establish `h` using `(QuotientAddGroup.eq).mp hab`. Rewrite `h` using `[AddSubgroup.mem_addSubgroupOf]`. Establish `hb : (b : VC D N N') = (a : VC D N N') + ((-a + b : La₂) : VC D N N')`. Use `push_cast`. Normalize the expressions using the abelian group laws.

Rewrite using `[hb]`. Conclude with `rep_shift T hS hG a.2 h (-a + b).2 z`.
-/
theorem term_indep (T : Tor D) {La₁ La₂ : AddSubgroup (VC D N N')} (hS : SemiChar T La₂)
    {G : VC D N N' → ℂ} (hG : G ∈ ThSp D T La₁) (a b : La₂)
    (hab : (a : La₂ ⧸ La₁.addSubgroupOf La₂) = (b : La₂ ⧸ La₁.addSubgroupOf La₂))
    (z : VC D N N') :
    al D T (b : VC D N N') * U D T (b : VC D N N') G z =
      al D T (a : VC D N N') * U D T (a : VC D N N') G z := by
  have h := (QuotientAddGroup.eq).mp hab
  rw [AddSubgroup.mem_addSubgroupOf] at h
  have hb : (b : VC D N N') = (a : VC D N N') + ((-a + b : La₂) : VC D N N') := by
    push_cast
    abel
  rw [hb]
  exact rep_shift T hS hG a.2 h (-a + b).2 z

/- English proof (translation)
The claim follows from `term_indep T hS hG a (Quotient.out (a : La₂ ⧸ La₁.addSubgroupOf La₂)) (Quotient.out_eq _).symm z`.
-/
theorem term_out (T : Tor D) {La₁ La₂ : AddSubgroup (VC D N N')} (hS : SemiChar T La₂)
    {G : VC D N N' → ℂ} (hG : G ∈ ThSp D T La₁) (a : La₂) (z : VC D N N') :
    al D T ((Quotient.out (a : La₂ ⧸ La₁.addSubgroupOf La₂) : La₂) : VC D N N') *
        U D T ((Quotient.out (a : La₂ ⧸ La₁.addSubgroupOf La₂) : La₂) : VC D N N') G z =
      al D T (a : VC D N N') * U D T (a : VC D N N') G z := term_indep T hS hG a (Quotient.out (a : La₂ ⧸ La₁.addSubgroupOf La₂))
    (Quotient.out_eq _).symm z

/- English proof (translation)
Simplify using `only [Iop]`. Use `congr 1`. Apply `finsum_congr` to reduce the goal to its premises. Introduce `q`. Conclude with `term_indep T hS hG _ _ (by rw [hs q]; exact (Quotient.out_eq q).symm) z`.
-/
theorem Iop_eq_section (T : Tor D) {La₁ La₂ : AddSubgroup (VC D N N')} (hS : SemiChar T La₂)
    {G : VC D N N' → ℂ} (hG : G ∈ ThSp D T La₁) (s : La₂ ⧸ La₁.addSubgroupOf La₂ → La₂)
    (hs : ∀ q, (s q : La₂ ⧸ La₁.addSubgroupOf La₂) = q) (z : VC D N N') :
    Iop D T La₁ La₂ G z = ((Real.sqrt ((La₁.addSubgroupOf La₂).index : ℝ))⁻¹ : ℂ) *
      ∑ᶠ q : La₂ ⧸ La₁.addSubgroupOf La₂,
        al D T ((s q : La₂) : VC D N N') * U D T ((s q : La₂) : VC D N N') G z := by
  simp only [Iop]
  congr 1
  apply finsum_congr
  intro q
  exact term_indep T hS hG _ _ (by rw [hs q]; exact (Quotient.out_eq q).symm) z

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Classical
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

variable {D : Car} {N N' : ℕ}

/- English proof (translation)
Unfold `Hf`. Use `first`. Consider the case `fun_prop`. Consider the case `exact (Differentiable.sum fun τ _ => Differentiable.sum fun i _ => Differentiable.sum fun j _ => ((differentiable_apply j).comp ((differentiable_apply i).comp (differentiable_apply τ))).mul_const _).div_const _`.
-/
theorem Hf_diff (T : Tor D) (x : VC D N N') :
    Differentiable ℂ (fun z : VC D N N' => Hf D T z x) := by
  unfold Hf
  first
  | fun_prop
  | exact (Differentiable.sum fun τ _ => Differentiable.sum fun i _ => Differentiable.sum fun j _ =>
      ((differentiable_apply j).comp ((differentiable_apply i).comp
        (differentiable_apply τ))).mul_const _).div_const _

/- English proof (translation)
Establish `hU : U D T x G = fun z => G (z + x) * Complex.exp (-(Real.pi : ℂ) * Hf D T z x - (Real.pi : ℂ) * Hf D T x x / 2)`. Use function extensionality and compare the values at `z`. Both sides reduce to the same expression. Rewrite using `[hU]`. Establish `hH` using `Hf_diff T x`.

Use `first`. Consider the case `exact (hG.comp (differentiable_id.add_const x)).mul ((((differentiable_const _).mul hH).sub (differentiable_const _)).cexp)`. Consider the case `fun_prop`.
-/
theorem U_diff (T : Tor D) (x : VC D N N') {G : VC D N N' → ℂ} (hG : Differentiable ℂ G) :
    Differentiable ℂ (U D T x G) := by
  have hU : U D T x G = fun z => G (z + x) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T z x - (Real.pi : ℂ) * Hf D T x x / 2) := by
    funext z
    rfl
  rw [hU]
  have hH := Hf_diff T x
  first
  | exact (hG.comp (differentiable_id.add_const x)).mul
      ((((differentiable_const _).mul hH).sub (differentiable_const _)).cexp)
  | fun_prop

/- English proof (translation)
Simplify using `only [U, Finset.sum_mul]`.
-/
theorem U_sum (T : Tor D) {Q : Type*} [Fintype Q] (x : VC D N N') (F : Q → VC D N N' → ℂ)
    (z : VC D N N') : U D T x (fun w => ∑ q, F q w) z = ∑ q, U D T x (F q) z := by
  simp only [U, Finset.sum_mul]

/- English proof (translation)
Establish `hG' : Differentiable ℂ G ∧ ∀ x ∈ La₁, ∀ z, al D T x * U D T x G z = G z` using `hG`. Use `show Differentiable ℂ (Iop D T La₁ La₂ G) ∧ ∀ x ∈ La₂, ∀ z, al D T x * U D T x (Iop D T La₁ La₂ G) z = Iop D T La₁ La₂ G z`. Distinguish the cases in `hfin : Finite (La₂ ⧸ La₁.addSubgroupOf La₂)`. Use `haveI := Fintype.ofFinite (La₂ ⧸ La₁.addSubgroupOf La₂)`. Establish `hfun : Iop D T La₁ La₂ G = fun w => ((Real.sqrt ((La₁.addSubgroupOf La₂).index : ℝ))⁻¹ : ℂ) * ∑ q : La₂ ⧸ La₁.addSubgroupOf La₂, al D T ((Quotient.out q : La₂) : VC D N N') * U D T ((Quotient.out q : La₂) : VC D N N') G w`.

Use function extensionality and compare the values at `w`. Simplify using `only [Iop, finsum_eq_sum_of_fintype]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hfun]`. Establish `hd : ∀ q : La₂ ⧸ La₁.addSubgroupOf La₂, Differentiable ℂ (fun w => al D T ((Quotient.out q : La₂) : VC D N N') * U D T ((Quotient.out q : La₂) : VC D N N') G w)` using `fun q => (U_diff T _ hG'.1).const_mul _`.

Use `first`. Consider the case `exact (Differentiable.fun_sum fun q _ => hd q).const_mul _`. Consider the case `fun_prop`. Consider the case `exact (by simpa using (Differentiable.sum (u := Finset.univ) fun q _ => hd q)).const_mul _`. Introduce `x hx z`.

Establish `key : ∀ q : La₂ ⧸ La₁.addSubgroupOf La₂, al D T x * U D T x (fun w => al D T ((Quotient.out q : La₂) : VC D N N') * U D T ((Quotient.out q : La₂) : VC D N N') G w) z = al D T ((Quotient.out (((⟨x, hx⟩ : La₂) : La₂ ⧸ La₁.addSubgroupOf La₂) + q) : La₂) : VC D N N') * U D T ((Quotie …`. Introduce `q`. Rewrite using `[U_smul T x _ (U D T ((Quotient.out q : La₂) : VC D N N') G) z, U_U T x _ G z, ← mul_assoc, ← mul_assoc, ← hS x hx _ (Quotient.out q).2]`. Establish `h1 : ((Quotient.out q : La₂) : La₂ ⧸ La₁.addSubgroupOf La₂) = q` using `Quotient.out_eq q`. Establish `h2 : ((Quotient.out (((⟨x, hx⟩ : La₂) : La₂ ⧸ La₁.addSubgroupOf La₂) + q) : La₂) : La₂ ⧸ La₁.addSubgroupOf La₂) = ((⟨x, hx⟩ : La₂) : La₂ ⧸ La₁.addSubgroupOf La₂) + q` using `Quotient.out_eq _`.

Establish `hab : (((⟨x, hx⟩ : La₂) + Quotient.out q : La₂) : La₂ ⧸ La₁.addSubgroupOf La₂) = ((Quotient.out (((⟨x, hx⟩ : La₂) : La₂ ⧸ La₁.addSubgroupOf La₂) + q) : La₂) : La₂ ⧸ La₁.addSubgroupOf La₂)`. Rewrite using `[h2, QuotientAddGroup.mk_add, h1]`. Conclude with `(term_indep T hS hG _ _ hab z).symm`. Simplify using `only [hfun]`. Rewrite using `[U_smul T x _ _ z, U_sum T x _ z, mul_left_comm (al D T x)]`.

Use `congr 1`. Rewrite using `[Finset.mul_sum, Finset.sum_congr rfl fun q _ => key q]`. Apply the tactic sequence `exact Fintype.sum_equiv (Equiv.addLeft (((⟨x, hx⟩ : La₂) : La₂ ⧸ La₁.addSubgroupOf La₂))) _ _ (fun q => by first | rfl | simp only [Equiv.coe_addLeft])`. Use `haveI : Infinite (La₂ ⧸ La₁.addSubgroupOf La₂) := not_finite_iff_infinite.mp hfin`. Establish `hidx : (La₁.addSubgroupOf La₂).index = 0` using `by first`.

Consider the case `exact AddSubgroup.index_eq_zero_of_infinite`. Consider the case `exact AddSubgroup.index_eq_zero_iff_infinite.mpr inferInstance`. Establish `h0 : Iop D T La₁ La₂ G = fun _ => 0`. Use function extensionality and compare the values at `z`. Simplify using `[Iop, hidx]`.

Rewrite using `[h0]`. Use `⟨differentiable_const _, fun x _ z => ?_⟩` and prove the remaining obligations. Simplify using `[U]`.
-/
theorem Iop_mem_ThSp (T : Tor D) {La₁ La₂ : AddSubgroup (VC D N N')} (hS : SemiChar T La₂)
    {G : VC D N N' → ℂ} (hG : G ∈ ThSp D T La₁) : Iop D T La₁ La₂ G ∈ ThSp D T La₂ := by
  classical
  have hG' : Differentiable ℂ G ∧ ∀ x ∈ La₁, ∀ z, al D T x * U D T x G z = G z := hG
  show Differentiable ℂ (Iop D T La₁ La₂ G) ∧
    ∀ x ∈ La₂, ∀ z, al D T x * U D T x (Iop D T La₁ La₂ G) z = Iop D T La₁ La₂ G z
  by_cases hfin : Finite (La₂ ⧸ La₁.addSubgroupOf La₂)
  · haveI := Fintype.ofFinite (La₂ ⧸ La₁.addSubgroupOf La₂)
    have hfun : Iop D T La₁ La₂ G = fun w =>
        ((Real.sqrt ((La₁.addSubgroupOf La₂).index : ℝ))⁻¹ : ℂ) *
          ∑ q : La₂ ⧸ La₁.addSubgroupOf La₂,
            al D T ((Quotient.out q : La₂) : VC D N N') *
              U D T ((Quotient.out q : La₂) : VC D N N') G w := by
      funext w
      simp only [Iop, finsum_eq_sum_of_fintype]
    refine ⟨?_, ?_⟩
    · rw [hfun]
      have hd : ∀ q : La₂ ⧸ La₁.addSubgroupOf La₂, Differentiable ℂ (fun w =>
          al D T ((Quotient.out q : La₂) : VC D N N') *
            U D T ((Quotient.out q : La₂) : VC D N N') G w) :=
        fun q => (U_diff T _ hG'.1).const_mul _
      first
      | exact (Differentiable.fun_sum fun q _ => hd q).const_mul _
      | fun_prop
      | exact (by simpa using (Differentiable.sum (u := Finset.univ) fun q _ => hd q)).const_mul _
    · intro x hx z
      have key : ∀ q : La₂ ⧸ La₁.addSubgroupOf La₂,
          al D T x * U D T x (fun w => al D T ((Quotient.out q : La₂) : VC D N N') *
            U D T ((Quotient.out q : La₂) : VC D N N') G w) z =
          al D T ((Quotient.out (((⟨x, hx⟩ : La₂) : La₂ ⧸ La₁.addSubgroupOf La₂) + q) : La₂) :
              VC D N N') *
            U D T ((Quotient.out (((⟨x, hx⟩ : La₂) : La₂ ⧸ La₁.addSubgroupOf La₂) + q) : La₂) :
              VC D N N') G z := by
        intro q
        rw [U_smul T x _ (U D T ((Quotient.out q : La₂) : VC D N N') G) z, U_U T x _ G z,
          ← mul_assoc, ← mul_assoc, ← hS x hx _ (Quotient.out q).2]
        have h1 : ((Quotient.out q : La₂) : La₂ ⧸ La₁.addSubgroupOf La₂) = q := Quotient.out_eq q
        have h2 : ((Quotient.out (((⟨x, hx⟩ : La₂) : La₂ ⧸ La₁.addSubgroupOf La₂) + q) : La₂) :
            La₂ ⧸ La₁.addSubgroupOf La₂) = ((⟨x, hx⟩ : La₂) : La₂ ⧸ La₁.addSubgroupOf La₂) + q :=
          Quotient.out_eq _
        have hab : (((⟨x, hx⟩ : La₂) + Quotient.out q : La₂) : La₂ ⧸ La₁.addSubgroupOf La₂) =
            ((Quotient.out (((⟨x, hx⟩ : La₂) : La₂ ⧸ La₁.addSubgroupOf La₂) + q) : La₂) :
              La₂ ⧸ La₁.addSubgroupOf La₂) := by
          rw [h2, QuotientAddGroup.mk_add, h1]
        exact (term_indep T hS hG _ _ hab z).symm
      simp only [hfun]
      rw [U_smul T x _ _ z, U_sum T x _ z, mul_left_comm (al D T x)]
      congr 1
      rw [Finset.mul_sum, Finset.sum_congr rfl fun q _ => key q]
      exact Fintype.sum_equiv
        (Equiv.addLeft (((⟨x, hx⟩ : La₂) : La₂ ⧸ La₁.addSubgroupOf La₂))) _ _
        (fun q => by first | rfl | simp only [Equiv.coe_addLeft])
  · haveI : Infinite (La₂ ⧸ La₁.addSubgroupOf La₂) := not_finite_iff_infinite.mp hfin
    have hidx : (La₁.addSubgroupOf La₂).index = 0 := by
      first
      | exact AddSubgroup.index_eq_zero_of_infinite
      | exact AddSubgroup.index_eq_zero_iff_infinite.mpr inferInstance
    have h0 : Iop D T La₁ La₂ G = fun _ => 0 := by
      funext z
      simp [Iop, hidx]
    rw [h0]
    refine ⟨differentiable_const _, fun x _ z => ?_⟩
    simp [U]

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Classical
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

variable {D : Car} {N N' : ℕ}

/- English proof (translation)
Establish `hG' : Differentiable ℂ G ∧ ∀ x ∈ La₁, ∀ z, al D T x * U D T x G z = G z` using `hG`. Use function extensionality and compare the values at `z`. Establish `htop : La₁.addSubgroupOf La₂ = ⊤` using `AddSubgroup.addSubgroupOf_eq_top.mpr hle`. Establish `hidx : (La₁.addSubgroupOf La₂).index = 1`. Rewrite using `[htop, AddSubgroup.index_top]`.

Use `haveI hsub : Subsingleton (La₂ ⧸ La₁.addSubgroupOf La₂) := by`. Prove the components needed by the constructor for the conclusion. Introduce `a b`. Take `⟨a, rfl⟩` from `QuotientAddGroup.mk_surjective a`. Take `⟨b, rfl⟩` from `QuotientAddGroup.mk_surjective b`.

Rewrite using `[QuotientAddGroup.eq, htop]`. Conclude with `AddSubgroup.mem_top _`. Use `haveI : Unique (La₂ ⧸ La₁.addSubgroupOf La₂) := uniqueOfSubsingleton 0`. Establish `hterm : ∀ q : La₂ ⧸ La₁.addSubgroupOf La₂, al D T ((Quotient.out q : La₂) : VC D N N') * U D T ((Quotient.out q : La₂) : VC D N N') G z = G z` using `fun q => hG'.2 _ (hle (Quotient.out q).2) z`. Simplify using `only [Iop, hterm, finsum_unique]`.

Simplify using `[hidx]`.
-/
theorem Iop_of_le (T : Tor D) {La₁ La₂ : AddSubgroup (VC D N N')} (hle : La₂ ≤ La₁)
    {G : VC D N N' → ℂ} (hG : G ∈ ThSp D T La₁) : Iop D T La₁ La₂ G = G := by
  classical
  have hG' : Differentiable ℂ G ∧ ∀ x ∈ La₁, ∀ z, al D T x * U D T x G z = G z := hG
  funext z
  have htop : La₁.addSubgroupOf La₂ = ⊤ := AddSubgroup.addSubgroupOf_eq_top.mpr hle
  have hidx : (La₁.addSubgroupOf La₂).index = 1 := by
    rw [htop, AddSubgroup.index_top]
  haveI hsub : Subsingleton (La₂ ⧸ La₁.addSubgroupOf La₂) := by
    constructor
    intro a b
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective b
    rw [QuotientAddGroup.eq, htop]
    exact AddSubgroup.mem_top _
  haveI : Unique (La₂ ⧸ La₁.addSubgroupOf La₂) := uniqueOfSubsingleton 0
  have hterm : ∀ q : La₂ ⧸ La₁.addSubgroupOf La₂,
      al D T ((Quotient.out q : La₂) : VC D N N') * U D T ((Quotient.out q : La₂) : VC D N N') G z =
        G z :=
    fun q => hG'.2 _ (hle (Quotient.out q).2) z
  simp only [Iop, hterm, finsum_unique]
  simp [hidx]

/- English proof (translation)
Rewrite using `[Iop_of_le T le_rfl hG]`.
-/
theorem IopIso_diag (D : Car) (T : Tor D) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (G : VC D N N' → ℂ)
    (hG : G ∈ Th D T L L') :
    normSq D T (La D T L L') (Iop D T (La D T L L') (La D T L L') G) =
      normSq D T (La D T L L') G := by
  rw [Iop_of_le T le_rfl hG]

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Classical
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

variable {D : Car} {N N' : ℕ}

def HfInt (T : Tor D) (La' : AddSubgroup (VC D N N')) : Prop :=
  ∀ x ∈ La', ∀ y ∈ La', ∃ a b : ℤ, Even (a - b) ∧
    Hf D T x y = (((a : ℝ) / Real.sqrt D.host.d : ℝ) : ℂ) + (b : ℂ) * Complex.I

/- English proof (translation)
Use `first`. Consider the case `exact Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.zero_lt_of_lt D.host.qd_big.2))`. Consider the case `(apply Real.sqrt_pos.mpr; have h := D.host.qd_big.2; exact_mod_cast (by omega : 0 < D.host.d))`.
-/
theorem sqrt_d_pos (D : Car) : 0 < Real.sqrt D.host.d := by
  first
  | exact Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.zero_lt_of_lt D.host.qd_big.2))
  | (apply Real.sqrt_pos.mpr; have h := D.host.qd_big.2; exact_mod_cast (by omega : 0 < D.host.d))

/- English proof (translation)
Rewrite using `[Hf_herm T (y + y') x, Hf_add_left T y y' x, map_add, ← Hf_herm T y x, ← Hf_herm T y' x]`.
-/
theorem Hf_add_right (T : Tor D) (x y y' : VC D N N') :
    Hf D T x (y + y') = Hf D T x y + Hf D T x y' := by
  rw [Hf_herm T (y + y') x, Hf_add_left T y y' x, map_add, ← Hf_herm T y x, ← Hf_herm T y' x]

/- English proof (translation)
Establish `h` using `congrArg Complex.im (Hf_herm T x x)`. Simplify using `only [Complex.conj_im] at h`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem Hf_self_im (T : Tor D) (x : VC D N N') : (Hf D T x x).im = 0 := by
  have h := congrArg Complex.im (Hf_herm T x x)
  simp only [Complex.conj_im] at h
  linarith

/- English proof (translation)
Simplify using `using congrArg Complex.re (Hf_herm T x y)`.
-/
theorem Hf_re_swap (T : Tor D) (x y : VC D N N') : (Hf D T y x).re = (Hf D T x y).re := by
  simpa using congrArg Complex.re (Hf_herm T x y)

/- English proof (translation)
Take `⟨a, b, hab, hH⟩` from `hI x hx x hx`. Establish `hb0 : b = 0`. Establish `h` using `congrArg Complex.im hH`. Rewrite `h` using `[Hf_self_im]`. Simplify using `only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im] at h`.

Establish `h' : (b : ℝ) = 0` using `by linarith`. Conclude with `h'` after adjusting the coercions. Take `⟨m, hm⟩` from `hab`. Establish `ha : a = 2 * m` using `by omega`. Establish `haR : (a : ℝ) = 2 * (m : ℝ)` using `by exact_mod_cast ha`.

Establish `hre : (Hf D T x x).re = (a : ℝ) / Real.sqrt D.host.d`. Rewrite using `[hH]`. Simplify using `only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im]`. Expand and normalize the polynomial expressions, which then agree. Establish `hs : Real.sqrt D.host.d ≠ 0` using `(sqrt_d_pos D).ne'`.

Use `⟨m, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hre, haR]`. Rewrite using `[hre, haR]`. Establish `hm' : Real.sqrt D.host.d / 2 * (2 * (m : ℝ) / Real.sqrt D.host.d) = (m : ℝ) * (Real.sqrt D.host.d / Real.sqrt D.host.d) * (2 / 2)`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hm', div_self hs, div_self (two_ne_zero : (2 : ℝ) ≠ 0), mul_one, mul_one, round_intCast]`.
-/
theorem self_int (T : Tor D) {La' : AddSubgroup (VC D N N')} (hI : HfInt T La')
    {x : VC D N N'} (hx : x ∈ La') :
    ∃ m : ℤ, (Hf D T x x).re = 2 * m / Real.sqrt D.host.d ∧
      round (Real.sqrt D.host.d / 2 * (Hf D T x x).re) = m := by
  obtain ⟨a, b, hab, hH⟩ := hI x hx x hx
  have hb0 : b = 0 := by
    have h := congrArg Complex.im hH
    rw [Hf_self_im] at h
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.intCast_re, Complex.intCast_im] at h
    have h' : (b : ℝ) = 0 := by linarith
    exact_mod_cast h'
  obtain ⟨m, hm⟩ := hab
  have ha : a = 2 * m := by omega
  have haR : (a : ℝ) = 2 * (m : ℝ) := by exact_mod_cast ha
  have hre : (Hf D T x x).re = (a : ℝ) / Real.sqrt D.host.d := by
    rw [hH]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.intCast_re, Complex.intCast_im]
    ring
  have hs : Real.sqrt D.host.d ≠ 0 := (sqrt_d_pos D).ne'
  refine ⟨m, ?_, ?_⟩
  · rw [hre, haR]
  · rw [hre, haR]
    have hm' : Real.sqrt D.host.d / 2 * (2 * (m : ℝ) / Real.sqrt D.host.d) =
        (m : ℝ) * (Real.sqrt D.host.d / Real.sqrt D.host.d) * (2 / 2) := by
      ring
    rw [hm', div_self hs, div_self (two_ne_zero : (2 : ℝ) ≠ 0), mul_one, mul_one, round_intCast]

/- English proof (translation)
Establish `h0 : (-1 : ℂ) ≠ 0` using `by norm_num`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem neg_one_zpow_congr {n m : ℤ} (h : Even (n - m)) : (-1 : ℂ) ^ n = (-1 : ℂ) ^ m := by
  have h0 : (-1 : ℂ) ≠ 0 := by norm_num
  calc (-1 : ℂ) ^ n = (-1 : ℂ) ^ ((n - m) + m) := by rw [sub_add_cancel]
    _ = (-1 : ℂ) ^ (n - m) * (-1 : ℂ) ^ m := zpow_add₀ h0 _ _
    _ = (-1 : ℂ) ^ m := by rw [Even.neg_one_zpow h, one_mul]

/- English proof (translation)
Unfold `cf`. Rewrite using `[hb, ← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cf_int (T : Tor D) (x y : VC D N N') (b : ℤ) (hb : (Hf D T x y).im = b) :
    cf T x y = (-1 : ℂ) ^ (-b) := by
  unfold cf
  rw [hb, ← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

/- English proof (translation)
Unfold `SemiChar`. Introduce `x hx y hy`. Take `⟨mx, hmx, hrx⟩` from `self_int T hI hx`. Take `⟨my, hmy, hry⟩` from `self_int T hI hy`. Take `⟨a, b, hab, hxy⟩` from `hI x hx y hy`.

Establish `hs : Real.sqrt D.host.d ≠ 0` using `(sqrt_d_pos D).ne'`. Establish `hre : (Hf D T x y).re = (a : ℝ) / Real.sqrt D.host.d`. Rewrite using `[hxy]`. Simplify using `only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im]`. Expand and normalize the polynomial expressions, which then agree.

Establish `him : (Hf D T x y).im = b`. Rewrite using `[hxy]`. Simplify using `only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsum : (Hf D T (x + y) (x + y)).re = (Hf D T x x).re + (Hf D T y y).re + 2 * (Hf D T x y).re`.

Rewrite using `[Hf_add_left T x y (x + y), Hf_add_right T x x y, Hf_add_right T y x y, Complex.add_re, Complex.add_re, Complex.add_re, Hf_re_swap T x y]`. Expand and normalize the polynomial expressions, which then agree. Establish `hr : round (Real.sqrt D.host.d / 2 * (Hf D T (x + y) (x + y)).re) = mx + my + a`. Rewrite using `[hsum, hmx, hmy, hre]`. Establish `h4 : Real.sqrt D.host.d / 2 * (2 * (mx : ℝ) / Real.sqrt D.host.d + 2 * (my : ℝ) / Real.sqrt D.host.d + 2 * ((a : ℝ) / Real.sqrt D.host.d)) = ((mx : ℝ) + my + a) * (Real.sqrt D.host.d / Real.sqrt D.host.d) * (2 / 2)`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h4, div_self hs, div_self (two_ne_zero : (2 : ℝ) ≠ 0), mul_one, mul_one]`. Conclude with `round_intCast (mx + my + a)` after adjusting the coercions. Unfold `al`. Rewrite using `[hr, hrx, hry, cf_int T x y b him, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]`.

Apply `neg_one_zpow_congr` to reduce the goal to its premises. Take `⟨k, hk⟩` from `hab`. Conclude with `⟨k + b, by omega⟩`.
-/
theorem semiChar_of_HfInt (T : Tor D) {La' : AddSubgroup (VC D N N')} (hI : HfInt T La') :
    SemiChar T La' := by
  unfold SemiChar
  intro x hx y hy
  obtain ⟨mx, hmx, hrx⟩ := self_int T hI hx
  obtain ⟨my, hmy, hry⟩ := self_int T hI hy
  obtain ⟨a, b, hab, hxy⟩ := hI x hx y hy
  have hs : Real.sqrt D.host.d ≠ 0 := (sqrt_d_pos D).ne'
  have hre : (Hf D T x y).re = (a : ℝ) / Real.sqrt D.host.d := by
    rw [hxy]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.intCast_re, Complex.intCast_im]
    ring
  have him : (Hf D T x y).im = b := by
    rw [hxy]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.intCast_re, Complex.intCast_im]
    ring
  have hsum : (Hf D T (x + y) (x + y)).re =
      (Hf D T x x).re + (Hf D T y y).re + 2 * (Hf D T x y).re := by
    rw [Hf_add_left T x y (x + y), Hf_add_right T x x y, Hf_add_right T y x y, Complex.add_re,
      Complex.add_re, Complex.add_re, Hf_re_swap T x y]
    ring
  have hr : round (Real.sqrt D.host.d / 2 * (Hf D T (x + y) (x + y)).re) = mx + my + a := by
    rw [hsum, hmx, hmy, hre]
    have h4 : Real.sqrt D.host.d / 2 * (2 * (mx : ℝ) / Real.sqrt D.host.d +
        2 * (my : ℝ) / Real.sqrt D.host.d + 2 * ((a : ℝ) / Real.sqrt D.host.d)) =
        ((mx : ℝ) + my + a) * (Real.sqrt D.host.d / Real.sqrt D.host.d) * (2 / 2) := by
      ring
    rw [h4, div_self hs, div_self (two_ne_zero : (2 : ℝ) ≠ 0), mul_one, mul_one]
    exact_mod_cast round_intCast (mx + my + a)
  unfold al
  rw [hr, hrx, hry, cf_int T x y b him,
    ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  apply neg_one_zpow_congr
  obtain ⟨k, hk⟩ := hab
  exact ⟨k + b, by omega⟩

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Classical
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

/- English proof (translation)
Use `haveI : IsNoetherian ℤ R := by first`. Consider the case `exact isNoetherian_of_isNoetherianRing_of_finite ℤ R`. Consider the case `infer_instance`. Establish `hinj : Function.Injective (AddSubgroup.inclusion hle).toIntLinearMap`. Introduce `a b h`.

Conclude with `AddSubgroup.inclusion_injective hle h`. Use `haveI : Module.Finite ℤ La₂ := Module.Finite.of_injective _ hinj`. Use `haveI : Module.Finite ℤ (La₂ ⧸ La₁.addSubgroupOf La₂) := Module.Finite.of_surjective (QuotientAddGroup.mk' (La₁.addSubgroupOf La₂)).toIntLinearMap (QuotientAddGroup.mk'_surjective _)`. Apply `Module.finite_of_fg_torsion` to reduce the goal to its premises. Introduce `q`.

Use `⟨⟨k, mem_nonZeroDivisors_of_ne_zero hk⟩, ?_⟩` and prove the remaining obligations. Take `⟨z, rfl⟩` from `QuotientAddGroup.mk_surjective q`. Use `show k • (QuotientAddGroup.mk z : La₂ ⧸ La₁.addSubgroupOf La₂) = 0`. Rewrite using `[show k • (QuotientAddGroup.mk z : La₂ ⧸ La₁.addSubgroupOf La₂) = QuotientAddGroup.mk (k • z) from (map_zsmul (QuotientAddGroup.mk' (La₁.addSubgroupOf La₂)) k z).symm]`. Rewrite using `[QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]`.

Simplify using `using hkR z (hle z.2)`.
-/
theorem finite_quot_of_smul {V : Type*} [AddCommGroup V] (La₁ La₂ R : AddSubgroup V)
    [Module.Finite ℤ R] (hle : La₂ ≤ R) (k : ℤ) (hk : k ≠ 0) (hkR : ∀ z ∈ R, k • z ∈ La₁) :
    Finite (La₂ ⧸ La₁.addSubgroupOf La₂) := by
  classical
  haveI : IsNoetherian ℤ R := by
    first
    | exact isNoetherian_of_isNoetherianRing_of_finite ℤ R
    | infer_instance
  have hinj : Function.Injective (AddSubgroup.inclusion hle).toIntLinearMap := by
    intro a b h
    exact AddSubgroup.inclusion_injective hle h
  haveI : Module.Finite ℤ La₂ := Module.Finite.of_injective _ hinj
  haveI : Module.Finite ℤ (La₂ ⧸ La₁.addSubgroupOf La₂) :=
    Module.Finite.of_surjective (QuotientAddGroup.mk' (La₁.addSubgroupOf La₂)).toIntLinearMap
      (QuotientAddGroup.mk'_surjective _)
  apply Module.finite_of_fg_torsion
  intro q
  refine ⟨⟨k, mem_nonZeroDivisors_of_ne_zero hk⟩, ?_⟩
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective q
  show k • (QuotientAddGroup.mk z : La₂ ⧸ La₁.addSubgroupOf La₂) = 0
  rw [show k • (QuotientAddGroup.mk z : La₂ ⧸ La₁.addSubgroupOf La₂) =
      QuotientAddGroup.mk (k • z) from
      (map_zsmul (QuotientAddGroup.mk' (La₁.addSubgroupOf La₂)) k z).symm]
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  simpa using hkR z (hle z.2)

variable {D : Car}

/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Establish `hM' : (M : ℂ) ≠ 0` using `by exact_mod_cast hM`. Simplify using `only [Finset.sum_apply]`. Establish `h1 : ∀ i0 : Fin N', i0 ≠ i → (∑ j0 : Fin N, FL.ins D i0 j0 (fun τ => δ * n * embT D τ ((A i0 j0 : 𝓞 D.host.E) : D.host.E)) τ i j) = 0`. Introduce `i0 hi0`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `j0 _`. Simplify using `[FL.ins, Ne.symm hi0]`. Establish `h2 : ∀ j0 : Fin N, j0 ≠ j → FL.ins D i j0 (fun τ => δ * n * embT D τ ((A i j0 : 𝓞 D.host.E) : D.host.E)) τ i j = 0`. Introduce `j0 hj0`.

Simplify using `[FL.ins, Ne.symm hj0]`. Establish `h3 : FL.ins D i j (fun τ => δ * n * embT D τ ((A i j : 𝓞 D.host.E) : D.host.E)) τ i j = δ * n * embT D τ ((A i j : 𝓞 D.host.E) : D.host.E)` using `if_pos ⟨rfl, rfl⟩`. Rewrite using `[Fintype.sum_eq_single i h1, Fintype.sum_eq_single j h2, h3]`. Use `show ((n : ℤ) * M) • (δ / M * embT D τ ((A i j : 𝓞 D.host.E) : D.host.E)) = _`. Rewrite using `[zsmul_eq_mul]`.

Use `push_cast`. Use `first`. Consider the case `(rw [show ((n : ℂ) * (M : ℂ)) * (δ / (M : ℂ) * embT D τ ((A i j : 𝓞 D.host.E) : D.host.E)) = δ * n * embT D τ ((A i j : 𝓞 D.host.E) : D.host.E) * ((M : ℂ) / (M : ℂ)) by ring, div_self hM', mul_one])`. Consider the case `(field_simp; ring)`. Consider the case `field_simp`.
-/
theorem Phi_smul_eq {N N' : ℕ} (δ : ℂ) (M : ℤ) (hM : M ≠ 0) (n : ℕ)
    (A : Fin N' → Fin N → 𝓞 D.host.E) :
    ((n : ℤ) * M) • FL.Phi D (N := N) (N' := N') (δ / M) A =
      ∑ i0 : Fin N', ∑ j0 : Fin N,
        FL.ins D i0 j0 (fun τ => δ * n * embT D τ ((A i0 j0 : 𝓞 D.host.E) : D.host.E)) := by
  funext τ i j
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM
  simp only [Finset.sum_apply]
  have h1 : ∀ i0 : Fin N', i0 ≠ i → (∑ j0 : Fin N, FL.ins D i0 j0
      (fun τ => δ * n * embT D τ ((A i0 j0 : 𝓞 D.host.E) : D.host.E)) τ i j) = 0 := by
    intro i0 hi0
    apply Finset.sum_eq_zero
    intro j0 _
    simp [FL.ins, Ne.symm hi0]
  have h2 : ∀ j0 : Fin N, j0 ≠ j → FL.ins D i j0
      (fun τ => δ * n * embT D τ ((A i j0 : 𝓞 D.host.E) : D.host.E)) τ i j = 0 := by
    intro j0 hj0
    simp [FL.ins, Ne.symm hj0]
  have h3 : FL.ins D i j (fun τ => δ * n * embT D τ ((A i j : 𝓞 D.host.E) : D.host.E)) τ i j =
      δ * n * embT D τ ((A i j : 𝓞 D.host.E) : D.host.E) := if_pos ⟨rfl, rfl⟩
  rw [Fintype.sum_eq_single i h1, Fintype.sum_eq_single j h2, h3]
  show ((n : ℤ) * M) • (δ / M * embT D τ ((A i j : 𝓞 D.host.E) : D.host.E)) = _
  rw [zsmul_eq_mul]
  push_cast
  first
  | (rw [show ((n : ℂ) * (M : ℂ)) * (δ / (M : ℂ) * embT D τ ((A i j : 𝓞 D.host.E) : D.host.E)) =
        δ * n * embT D τ ((A i j : 𝓞 D.host.E) : D.host.E) * ((M : ℂ) / (M : ℂ)) by ring,
      div_self hM', mul_one])
  | (field_simp; ring)
  | field_simp

/- English proof (translation)
Take `⟨M, hM, hup⟩` from `FL.La_upper D L₂ L₂' h₂ cc δ`. Take `⟨n, hn, hlow⟩` from `FL.La_lower D L₁ L₁' h₁ cc hcc δ`. Use `haveI : Module.Finite ℤ (FL.Phi D (N := N) (N' := N') (δ / M)).range := Module.Finite.of_surjective (FL.Phi D (N := N) (N' := N') (δ / M)).rangeRestrict.toIntLinearMap (AddMonoidHom.rangeRestrict_surjective _)`. Use `finite_quot_of_smul _ _ _ hup ((n : ℤ) * M) (mul_ne_zero (by exact_mod_cast hn) hM) ?_` and prove the remaining obligations. Introduce and unpack `z ⟨A, rfl⟩`.

Rewrite using `[Phi_smul_eq δ M hM n A]`. Conclude with `AddSubgroup.sum_mem _ fun i0 _ => AddSubgroup.sum_mem _ fun j0 _ => hlow i0 j0 (A i0 j0)`.
-/
theorem La_index_finite (cc : Ideal (𝓞 D.host.K)) (hcc : IsCurveIdeal D cc) (δ : ℂ) {N N' : ℕ}
    (L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L₁' L₂' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (h₁ : admitted D N N' L₁ L₁') (h₂ : admitted D N N' L₂ L₂') :
    Finite (La D (tor0 D cc δ) L₂ L₂' ⧸
      (La D (tor0 D cc δ) L₁ L₁').addSubgroupOf (La D (tor0 D cc δ) L₂ L₂')) := by
  obtain ⟨M, hM, hup⟩ := FL.La_upper D L₂ L₂' h₂ cc δ
  obtain ⟨n, hn, hlow⟩ := FL.La_lower D L₁ L₁' h₁ cc hcc δ
  haveI : Module.Finite ℤ (FL.Phi D (N := N) (N' := N') (δ / M)).range :=
    Module.Finite.of_surjective (FL.Phi D (N := N) (N' := N') (δ / M)).rangeRestrict.toIntLinearMap
      (AddMonoidHom.rangeRestrict_surjective _)
  refine finite_quot_of_smul _ _ _ hup ((n : ℤ) * M)
    (mul_ne_zero (by exact_mod_cast hn) hM) ?_
  rintro z ⟨A, rfl⟩
  rw [Phi_smul_eq δ M hM n A]
  exact AddSubgroup.sum_mem _ fun i0 _ => AddSubgroup.sum_mem _ fun j0 _ => hlow i0 j0 (A i0 j0)

/- English proof (translation)
Use `haveI := La_index_finite cc hcc δ L₁ L₂ L₁' L₂' h₁ h₂`. Conclude with `AddSubgroup.index_ne_zero_of_finite`.
-/
theorem La_index_ne_zero (cc : Ideal (𝓞 D.host.K)) (hcc : IsCurveIdeal D cc) (δ : ℂ) {N N' : ℕ}
    (L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L₁' L₂' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (h₁ : admitted D N N' L₁ L₁') (h₂ : admitted D N N' L₂ L₂') :
    ((La D (tor0 D cc δ) L₁ L₁').addSubgroupOf (La D (tor0 D cc δ) L₂ L₂')).index ≠ 0 := by
  haveI := La_index_finite cc hcc δ L₁ L₂ L₁' L₂' h₁ h₂
  exact AddSubgroup.index_ne_zero_of_finite

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO

end
