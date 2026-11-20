import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.GlobalTheory.GL3.LinkThetaStatementFamily
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylPoint
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.TensorBasis
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Th1.H

section Num

variable {S : Finset ℕ}

/- English proof (translation)
Unfold `TaylorLogMetric.lamC`. Rewrite using `[dif_pos h]`.
-/
theorem lamC_of_mem {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {x : ℂ} (h : x ∈ TaylorLogMetric.Qbar) : TaylorLogMetric.lamC lam x = lam ⟨x, h⟩ := by
  unfold TaylorLogMetric.lamC; rw [dif_pos h]

/- English proof (translation)
Rewrite using `[lamC_of_mem lam hx, lamC_of_mem lam hy, lamC_of_mem lam (add_mem hx hy), ← map_add]`. Both sides reduce to the same expression.
-/
theorem lamC_add {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {x y : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (hy : y ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam (x + y) = TaylorLogMetric.lamC lam x + TaylorLogMetric.lamC lam y := by
  rw [lamC_of_mem lam hx, lamC_of_mem lam hy, lamC_of_mem lam (add_mem hx hy), ← map_add]; rfl

/- English proof (translation)
Rewrite using `[lamC_of_mem lam hx, lamC_of_mem lam hy, lamC_of_mem lam (mul_mem hx hy), ← map_mul]`. Both sides reduce to the same expression.
-/
theorem lamC_mul {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {x y : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (hy : y ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam (x * y) = TaylorLogMetric.lamC lam x * TaylorLogMetric.lamC lam y := by
  rw [lamC_of_mem lam hx, lamC_of_mem lam hy, lamC_of_mem lam (mul_mem hx hy), ← map_mul]; rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨zero_mem _, fun p _ lam _ => by rw [lamC_of_mem lam (zero_mem _)]; simp [show (⟨0, zero_mem _⟩ : TaylorLogMetric.Qbar) = 0 from rfl]⟩`.
-/
theorem IntOff.zero : IntOff S 0 :=
  ⟨zero_mem _, fun p _ lam _ => by rw [lamC_of_mem lam (zero_mem _)]; simp [show (⟨0, zero_mem _⟩ : TaylorLogMetric.Qbar) = 0 from rfl]⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨one_mem _, fun p _ lam _ => by rw [lamC_of_mem lam (one_mem _)]; simp [show (⟨1, one_mem _⟩ : TaylorLogMetric.Qbar) = 1 from rfl]⟩`.
-/
theorem IntOff.one : IntOff S 1 :=
  ⟨one_mem _, fun p _ lam _ => by rw [lamC_of_mem lam (one_mem _)]; simp [show (⟨1, one_mem _⟩ : TaylorLogMetric.Qbar) = 1 from rfl]⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨add_mem hx.1 hy.1, fun p _ lam hp => by rw [lamC_add lam hx.1 hy.1] exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx.2 p lam hp) (hy.2 p lam hp))⟩`.
-/
theorem IntOff.add {x y : ℂ} (hx : IntOff S x) (hy : IntOff S y) : IntOff S (x + y) :=
  ⟨add_mem hx.1 hy.1, fun p _ lam hp => by
    rw [lamC_add lam hx.1 hy.1]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx.2 p lam hp) (hy.2 p lam hp))⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨mul_mem hx.1 hy.1, fun p _ lam hp => by rw [lamC_mul lam hx.1 hy.1, norm_mul] exact mul_le_one₀ (hx.2 p lam hp) (norm_nonneg _) (hy.2 p lam hp)⟩`.
-/
theorem IntOff.mul {x y : ℂ} (hx : IntOff S x) (hy : IntOff S y) : IntOff S (x * y) :=
  ⟨mul_mem hx.1 hy.1, fun p _ lam hp => by
    rw [lamC_mul lam hx.1 hy.1, norm_mul]
    exact mul_le_one₀ (hx.2 p lam hp) (norm_nonneg _) (hy.2 p lam hp)⟩

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using IntOff.zero`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`. Conclude with `(h a (Finset.mem_insert_self _ _)).add (ih fun k hk => h k (Finset.mem_insert_of_mem hk))`.
-/
theorem IntOff.sum {κ : Type} (s : Finset κ) (f : κ → ℂ) (h : ∀ k ∈ s, IntOff S (f k)) : IntOff S (∑ k ∈ s, f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IntOff.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

/- English proof (translation)
Establish `hz : z ∈ TaylorLogMetric.Qbar`. Rewrite using `[mem_algebraicClosure_iff]`. Use `⟨Polynomial.X ^ n - 1, ?_, by simp [h]⟩` and prove the remaining obligations. Conclude with `Polynomial.X_pow_sub_C_ne_zero hn (1 : ℚ)`. Use `⟨hz, fun p _ lam _ => ?_⟩` and prove the remaining obligations.

Rewrite using `[lamC_of_mem lam hz]`. Establish `h1 : (lam ⟨z, hz⟩) ^ n = 1`. Rewrite using `[← map_pow]`. Establish `: (⟨z, hz⟩ : TaylorLogMetric.Qbar) ^ n = 1` using `Subtype.ext (by simpa using h)`. Rewrite using `[this, map_one]`.

Establish `h2 : ‖lam ⟨z, hz⟩‖ ^ n = 1` using `by rw [← norm_pow, h1, norm_one]`. Conclude with `((pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2).le`.
-/
theorem IntOff.of_pow {z : ℂ} {n : ℕ} (hn : 0 < n) (h : z ^ n = 1) : IntOff S z := by
  have hz : z ∈ TaylorLogMetric.Qbar := by
    rw [mem_algebraicClosure_iff]
    refine ⟨Polynomial.X ^ n - 1, ?_, by simp [h]⟩
    exact Polynomial.X_pow_sub_C_ne_zero hn (1 : ℚ)
  refine ⟨hz, fun p _ lam _ => ?_⟩
  rw [lamC_of_mem lam hz]
  have h1 : (lam ⟨z, hz⟩) ^ n = 1 := by
    rw [← map_pow]
    have : (⟨z, hz⟩ : TaylorLogMetric.Qbar) ^ n = 1 := Subtype.ext (by simpa using h)
    rw [this, map_one]
  have h2 : ‖lam ⟨z, hz⟩‖ ^ n = 1 := by rw [← norm_pow, h1, norm_one]
  exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2).le

/- English proof (translation)
Use `IntOff.of_pow (n := 2 * n) (by omega) ?_` and prove the remaining obligations. Rewrite using `[← Complex.exp_nat_mul]`. Establish `h' : ((n : ℂ)) * (r : ℂ) = (m : ℂ)` using `by exact_mod_cast h`. Establish `: ((2 * n : ℕ) : ℂ) * ((k : ℂ) * ((Real.pi : ℂ) * Complex.I * (r : ℂ))) = ((k * m : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)`. Use `push_cast`.

Take the linear combination `(2 * (k : ℂ) * (Real.pi : ℂ) * Complex.I) * h'`. Rewrite using `[this]`. Conclude with `Complex.exp_int_mul_two_pi_mul_I _`.
-/
theorem IntOff.exp_rat {r : ℝ} {n : ℕ} (hn : 0 < n) {m : ℤ} (h : (n : ℝ) * r = (m : ℝ)) (k : ℤ) :
    IntOff S (Complex.exp ((k : ℂ) * ((Real.pi : ℂ) * Complex.I * (r : ℂ)))) := by
  refine IntOff.of_pow (n := 2 * n) (by omega) ?_
  rw [← Complex.exp_nat_mul]
  have h' : ((n : ℂ)) * (r : ℂ) = (m : ℂ) := by exact_mod_cast h
  have : ((2 * n : ℕ) : ℂ) * ((k : ℂ) * ((Real.pi : ℂ) * Complex.I * (r : ℂ))) = ((k * m : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    linear_combination (2 * (k : ℂ) * (Real.pi : ℂ) * Complex.I) * h'
  rw [this]
  exact Complex.exp_int_mul_two_pi_mul_I _

/- English proof (translation)
Establish `h1` using `PadicComplex.norm_extends' p (a : ℚ_[p])`. Rewrite `h1` using `[(Padic.norm_natCast_eq_one_iff).2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 h), map_natCast, PadicComplex.coe_natCast]`. Conclude with `h1`.
-/
theorem norm_natCast_of_not_dvd {p : ℕ} [Fact p.Prime] {a : ℕ} (h : ¬ p ∣ a) : ‖(a : ℂ_[p])‖ = 1 := by
  have h1 := PadicComplex.norm_extends' p (a : ℚ_[p])
  rw [(Padic.norm_natCast_eq_one_iff).2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 h), map_natCast, PadicComplex.coe_natCast] at h1
  exact h1

/- English proof (translation)
Establish `ha : ((a : ℂ)⁻¹) ∈ TaylorLogMetric.Qbar` using `inv_mem (natCast_mem _ a)`. Use `⟨ha, fun p _ lam hp => ?_⟩` and prove the remaining obligations. Rewrite using `[lamC_of_mem lam ha]`. Establish `e : (⟨(a : ℂ)⁻¹, ha⟩ : TaylorLogMetric.Qbar) = ((a : TaylorLogMetric.Qbar))⁻¹` using `Subtype.ext (by simp)`. Rewrite using `[e, map_inv₀, map_natCast, norm_inv, norm_natCast_of_not_dvd fun hd => hp (h.2 p Fact.out hd)]`.

Simplify using the standard rewrite rules.
-/
theorem IntOff.inv_nat {a : ℕ} (h : SNum S a) : IntOff S ((a : ℂ)⁻¹) := by
  have ha : ((a : ℂ)⁻¹) ∈ TaylorLogMetric.Qbar := inv_mem (natCast_mem _ a)
  refine ⟨ha, fun p _ lam hp => ?_⟩
  rw [lamC_of_mem lam ha]
  have e : (⟨(a : ℂ)⁻¹, ha⟩ : TaylorLogMetric.Qbar) = ((a : TaylorLogMetric.Qbar))⁻¹ := Subtype.ext (by simp)
  rw [e, map_inv₀, map_natCast, norm_inv, norm_natCast_of_not_dvd fun hd => hp (h.2 p Fact.out hd)]
  simp

/- English proof (translation)
Assemble the required witnesses or components as `⟨Nat.mul_pos ha.1 hb.1, fun q hq hd => (hq.dvd_mul.1 hd).elim (ha.2 q hq) (hb.2 q hq)⟩`.
-/
theorem SNum.mul {a b : ℕ} (ha : SNum S a) (hb : SNum S b) : SNum S (a * b) :=
  ⟨Nat.mul_pos ha.1 hb.1, fun q hq hd => (hq.dvd_mul.1 hd).elim (ha.2 q hq) (hb.2 q hq)⟩

end Num

section Gen

variable {V : Type} [AddCommGroup V] [Module ℂ V] {S : Finset ℕ}

/- English proof (translation)
Take `⟨a, ha, hax⟩` from `hx`. Take `⟨b, hb, hby⟩` from `hy`. Use `⟨a * b, ha.mul hb, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `Λ.add_mem ?_ ?_` and prove the remaining obligations.

Rewrite using `[mul_comm, mul_smul]`. Conclude with `Λ.nsmul_mem hax b`. Rewrite using `[mul_smul]`. Conclude with `Λ.nsmul_mem hby a`.
-/
theorem TorS.add {Λ : AddSubgroup V} {x y : V} (hx : TorS Λ S x) (hy : TorS Λ S y) : TorS Λ S (x + y) := by
  obtain ⟨a, ha, hax⟩ := hx
  obtain ⟨b, hb, hby⟩ := hy
  refine ⟨a * b, ha.mul hb, ?_⟩
  rw [smul_add]
  refine Λ.add_mem ?_ ?_
  · rw [mul_comm, mul_smul]; exact Λ.nsmul_mem hax b
  · rw [mul_smul]; exact Λ.nsmul_mem hby a

/- English proof (translation)
Take `⟨a, ha, hax⟩` from `hx`. Conclude with `⟨a, ha, by rw [smul_neg]; exact Λ.neg_mem hax⟩`.
-/
theorem TorS.neg {Λ : AddSubgroup V} {x : V} (hx : TorS Λ S x) : TorS Λ S (-x) := by
  obtain ⟨a, ha, hax⟩ := hx
  exact ⟨a, ha, by rw [smul_neg]; exact Λ.neg_mem hax⟩

/- English proof (translation)
Simplify using `only [altE, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul, Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem altE_nsmul (H : Sesq V) (a b : ℕ) (x y : V) : altE H (a • x) (b • y) = (a : ℝ) * (b : ℝ) * altE H x y := by
  simp only [altE, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul, Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
  ring

/- English proof (translation)
Simplify using `only [qOf, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem qOf_nsmul (H : Sesq V) (c : ℝ) (a : ℕ) (x : V) : qOf c H (a • x) = (a : ℝ) * (a : ℝ) * qOf c H x := by
  simp only [qOf, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  ring

/- English proof (translation)
Take `⟨a, ha, hax⟩` from `hx`. Take `⟨b, hb, hby⟩` from `hy`. Take `⟨m, hm⟩` from `hL.2.1 _ hax _ hby`. Use `IntOff.exp_rat (n := a * b) (Nat.mul_pos ha.1 hb.1) (m := m) ?_ k` and prove the remaining obligations. Rewrite using `[← hm, altE_nsmul]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem IntOff.expE {H : Sesq V} {c : ℝ} {Λ : AddSubgroup V} (hL : LatInt H c Λ) {x y : V} (hx : TorS Λ S x) (hy : TorS Λ S y) (k : ℤ) :
    IntOff S (Complex.exp ((k : ℂ) * ((Real.pi : ℂ) * Complex.I * (altE H x y : ℂ)))) := by
  obtain ⟨a, ha, hax⟩ := hx
  obtain ⟨b, hb, hby⟩ := hy
  obtain ⟨m, hm⟩ := hL.2.1 _ hax _ hby
  refine IntOff.exp_rat (n := a * b) (Nat.mul_pos ha.1 hb.1) (m := m) ?_ k
  rw [← hm, altE_nsmul]; push_cast; ring

/- English proof (translation)
Take `⟨a, ha, hax⟩` from `hx`. Take `⟨m, hm⟩` from `hL.2.2 _ hax`. Use `IntOff.exp_rat (S := S) (r := qOf c H x) (n := a * a) (Nat.mul_pos ha.1 ha.1) (m := m) (by rw [← hm, qOf_nsmul]; push_cast; ring) 1` as an intermediate fact. Simplify `this` using `[alphaQ]`.
-/
theorem IntOff.expQ {H : Sesq V} {c : ℝ} {Λ : AddSubgroup V} (hL : LatInt H c Λ) {x : V} (hx : TorS Λ S x) :
    IntOff S (alphaQ c H x) := by
  obtain ⟨a, ha, hax⟩ := hx
  obtain ⟨m, hm⟩ := hL.2.2 _ hax
  have := IntOff.exp_rat (S := S) (r := qOf c H x) (n := a * a) (Nat.mul_pos ha.1 ha.1) (m := m) (by rw [← hm, qOf_nsmul]; push_cast; ring) 1
  simpa [alphaQ] using this

/- English proof (translation)
Use `IntOff.expE hL ht hy 2` as an intermediate fact. Establish `e : (brk H y t)⁻¹ = Complex.exp (((2 : ℤ) : ℂ) * ((Real.pi : ℂ) * Complex.I * (altE H t y : ℂ)))`. Rewrite using `[brk, ← Complex.exp_neg]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `this`.
-/
theorem IntOff.brkInv {H : Sesq V} {c : ℝ} {Λ : AddSubgroup V} (hL : LatInt H c Λ) {y t : V} (hy : TorS Λ S y) (ht : TorS Λ S t) :
    IntOff S (brk H y t)⁻¹ := by
  have := IntOff.expE hL ht hy 2
  have e : (brk H y t)⁻¹ = Complex.exp (((2 : ℤ) : ℂ) * ((Real.pi : ℂ) * Complex.I * (altE H t y : ℂ))) := by
    rw [brk, ← Complex.exp_neg]; congr 1; push_cast; ring
  rw [e]; exact this

/- English proof (translation)
Establish `e : hatS H 1 SA Φ y = (SA.card : ℂ)⁻¹ * ∑ t ∈ SA, Φ t * (brk H y t)⁻¹`. Simplify using `[hatS, div_eq_mul_inv]`. Rewrite using `[e]`. Conclude with `(IntOff.inv_nat hc).mul (IntOff.sum _ _ fun t ht => (hΦ t ht).mul (IntOff.brkInv hL hy (hA t ht)))`.
-/
theorem IntOff.hat {H : Sesq V} {c : ℝ} {Λ : AddSubgroup V} (hL : LatInt H c Λ) {SA : Finset V} (hA : ∀ x ∈ SA, TorS Λ S x)
    (hc : SNum S SA.card) {Φ : V → ℂ} (hΦ : ∀ s ∈ SA, IntOff S (Φ s)) {y : V} (hy : TorS Λ S y) : IntOff S (hatS H 1 SA Φ y) := by
  have e : hatS H 1 SA Φ y = (SA.card : ℂ)⁻¹ * ∑ t ∈ SA, Φ t * (brk H y t)⁻¹ := by
    simp [hatS, div_eq_mul_inv]
  rw [e]
  exact (IntOff.inv_nat hc).mul (IntOff.sum _ _ fun t ht => (hΦ t ht).mul (IntOff.brkInv hL hy (hA t ht)))

/- English proof (translation)
Use `⟨s.card, fun k => r (s.equivFin.symm k), fun k => t (s.equivFin.symm k), fun k => hr _ (Finset.coe_mem _), fun k => ht _ (Finset.coe_mem _), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `z`. Rewrite using `[← Finset.sum_coe_sort s]`. Conclude with `(Equiv.sum_comp s.equivFin.symm fun k : s => r k * opU H (t k) e z).symm`.
-/
theorem isKerG_of_finset {κ : Type} (H : Sesq V) (Λ : AddSubgroup V) (e : V → ℂ) (s : Finset κ) (r : κ → ℂ) (t : κ → V)
    (hr : ∀ k ∈ s, IntOff S (r k)) (ht : ∀ k ∈ s, TorS Λ S (t k)) :
    IsKerG H Λ S e fun z => ∑ k ∈ s, r k * opU H (t k) e z := by
  refine ⟨s.card, fun k => r (s.equivFin.symm k), fun k => t (s.equivFin.symm k), fun k => hr _ (Finset.coe_mem _),
    fun k => ht _ (Finset.coe_mem _), ?_⟩
  funext z
  rw [← Finset.sum_coe_sort s]
  exact (Equiv.sum_comp s.equivFin.symm fun k : s => r k * opU H (t k) e z).symm

/- English proof (translation)
Simplify using `only [opU, Finset.sum_mul]`.
-/
theorem opU_sum {κ : Type} (H : Sesq V) (x : V) (s : Finset κ) (f : κ → V → ℂ) (z : V) :
    opU H x (fun v => ∑ k ∈ s, f k v) z = ∑ k ∈ s, opU H x (f k) z := by
  simp only [opU, Finset.sum_mul]

/- English proof (translation)
Establish `h : xiS H α vol SA SB Φ e = fun v => ∑ y ∈ SB, (hatS H vol SA Φ y * α y) * opU H y e v` using `rfl`. Rewrite using `[h, opU_sum]`. Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Rewrite using `[opU_smul, heisenbergMul V H hH x y e z]`. Establish `: -(Real.pi : ℂ) * Complex.I * (altE H x y : ℂ) = ((-1 : ℤ) : ℂ) * ((Real.pi : ℂ) * Complex.I * (altE H x y : ℂ))` using `by push_cast; ring`.

Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem opU_xiS (H : Sesq V) (hH : IsHerm H) (α : V → ℂ) (vol : ℝ) (SA SB : Finset V) (Φ e : V → ℂ) (x z : V) :
    opU H x (xiS H α vol SA SB Φ e) z = ∑ y ∈ SB, (hatS H vol SA Φ y * α y *
      Complex.exp (((-1 : ℤ) : ℂ) * ((Real.pi : ℂ) * Complex.I * (altE H x y : ℂ)))) * opU H (x + y) e z := by
  have h : xiS H α vol SA SB Φ e = fun v => ∑ y ∈ SB, (hatS H vol SA Φ y * α y) * opU H y e v := rfl
  rw [h, opU_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [opU_smul, heisenbergMul V H hH x y e z]
  have : -(Real.pi : ℂ) * Complex.I * (altE H x y : ℂ) = ((-1 : ℤ) : ℂ) * ((Real.pi : ℂ) * Complex.I * (altE H x y : ℂ)) := by
    push_cast; ring
  rw [this]; ring

/- English proof (translation)
Introduce `V _ _ H c Λ S SX SA SB Φ e hL hX hA hB hc hΦ`. Establish `h : xiL H (alphaQ c H) 1 SX SA SB Φ e = fun z => ∑ k ∈ SX ×ˢ SB, (alphaQ c H k.1 * (hatS H 1 SA (fun s => Φ (s - k.1)) k.2 * alphaQ c H k.2 * Complex.exp (((-1 : ℤ) : ℂ) * ((Real.pi : ℂ) * Complex.I * (altE H k.1 k.2 : ℂ))))) * opU H (k.1 + k.2) e z`. Use function extensionality and compare the values at `z`. Rewrite using `[Finset.sum_product]`. Simplify using `only [xiL]`.

Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[opU_xiS H hL.1, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun y _ => by ring`. Rewrite using `[h]`. Use `isKerG_of_finset H Λ e _ _ _ (fun k hk => ?_) fun k hk => ?_` and prove the remaining obligations.

Take `⟨h1, h2⟩` from `Finset.mem_product.1 hk`. Conclude with `(IntOff.expQ hL (hX _ h1)).mul (((IntOff.hat hL hA hc (fun s hs => hΦ _ h1 s hs) (hB _ h2)).mul (IntOff.expQ hL (hB _ h2))).mul (IntOff.expE hL (hX _ h1) (hB _ h2) (-1)))`. Take `⟨h1, h2⟩` from `Finset.mem_product.1 hk`. Conclude with `(hX _ h1).add (hB _ h2)`.
-/
theorem twist_lattice_kernel : XiLKer := by
  intro V _ _ H c Λ S SX SA SB Φ e hL hX hA hB hc hΦ
  have h : xiL H (alphaQ c H) 1 SX SA SB Φ e = fun z => ∑ k ∈ SX ×ˢ SB,
      (alphaQ c H k.1 * (hatS H 1 SA (fun s => Φ (s - k.1)) k.2 * alphaQ c H k.2 *
        Complex.exp (((-1 : ℤ) : ℂ) * ((Real.pi : ℂ) * Complex.I * (altE H k.1 k.2 : ℂ))))) * opU H (k.1 + k.2) e z := by
    funext z
    rw [Finset.sum_product]
    simp only [xiL]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [opU_xiS H hL.1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [h]
  refine isKerG_of_finset H Λ e _ _ _ (fun k hk => ?_) fun k hk => ?_
  · obtain ⟨h1, h2⟩ := Finset.mem_product.1 hk
    exact (IntOff.expQ hL (hX _ h1)).mul (((IntOff.hat hL hA hc (fun s hs => hΦ _ h1 s hs) (hB _ h2)).mul (IntOff.expQ hL (hB _ h2))).mul
      (IntOff.expE hL (hX _ h1) (hB _ h2) (-1)))
  · obtain ⟨h1, h2⟩ := Finset.mem_product.1 hk
    exact (hX _ h1).add (hB _ h2)

end Gen

/- English proof (translation)
Introduce `D T e S N N' L L' Θ`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, r, t, hr, ht, h⟩`. Conclude with `⟨n, r, t, fun k => (hr k).1, fun k p _ lam hp => (hr k).2 p lam hp, fun k => by obtain ⟨a, ha, h2⟩ := ht k; exact ⟨a, ha.1, ha.2, h2⟩, h⟩`. Introduce and unpack `⟨n, r, t, h1, h2, h3, h⟩`.

Conclude with `⟨n, r, t, fun k => ⟨h1 k, fun p _ lam hp => h2 k p lam hp⟩, fun k => by obtain ⟨a, ha, hb, hc⟩ := h3 k; exact ⟨a, ⟨ha, hb⟩, hc⟩, h⟩`.
-/
theorem kernel_comparison_holds : KerBridge := by
  intro D T e S N N' L L' Θ
  constructor
  · rintro ⟨n, r, t, hr, ht, h⟩
    exact ⟨n, r, t, fun k => (hr k).1, fun k p _ lam hp => (hr k).2 p lam hp,
      fun k => by obtain ⟨a, ha, h2⟩ := ht k; exact ⟨a, ha.1, ha.2, h2⟩, h⟩
  · rintro ⟨n, r, t, h1, h2, h3, h⟩
    exact ⟨n, r, t, fun k => ⟨h1 k, fun p _ lam hp => h2 k p lam hp⟩,
      fun k => by obtain ⟨a, ha, hb, hc⟩ := h3 k; exact ⟨a, ⟨ha, hb⟩, hc⟩, h⟩

section Tw

open Formalism.HermitianLatticesTheory Formalism.L2.Col

variable {E : Type} [Field E] [NumberField E] [StarRing E]
variable {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]

/- English proof (translation)
Establish `hc0 : (c : E) ≠ 0` using `Nat.cast_ne_zero.2 hc.ne'`. Use `mem_of_forall_locP M fun Q => ?_` and prove the remaining obligations. Establish `h` using `(mem_twO M c e x).1 hx Q`. Break down `he Q with h1 | h1 | h1` into its components or cases. Rewrite `h` using `[h1, zpow_one]`.

Establish `e1 : c • x = (c : E) • ((c : E) • ((c : E)⁻¹ • x))`. Rewrite using `[smul_smul (c : E) (c : E)⁻¹, mul_inv_cancel₀ hc0, one_smul, Nat.cast_smul_eq_nsmul]`. Rewrite using `[e1]`. Conclude with `nat_smul_mem _ c (nat_smul_mem _ c h)`. Rewrite `h` using `[h1, zpow_zero, inv_one, one_smul]`.

Conclude with `nsmul_mem h c`. Rewrite `h` using `[h1, zpow_neg_one, inv_inv, Nat.cast_smul_eq_nsmul]`. Conclude with `h`.
-/
theorem tw_nsmul_mem (M : Submodule (𝓞 E) W) (c : ℕ) (hc : 0 < c) (e : HeightOneSpectrum (𝓞 E) → ℤ)
    (he : ∀ Q, e Q = 1 ∨ e Q = 0 ∨ e Q = -1) {x : W} (hx : x ∈ twist₂ M c e) : c • x ∈ M := by
  have hc0 : (c : E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  refine mem_of_forall_locP M fun Q => ?_
  have h := (mem_twO M c e x).1 hx Q
  rcases he Q with h1 | h1 | h1
  · rw [h1, zpow_one] at h
    have e1 : c • x = (c : E) • ((c : E) • ((c : E)⁻¹ • x)) := by
      rw [smul_smul (c : E) (c : E)⁻¹, mul_inv_cancel₀ hc0, one_smul, Nat.cast_smul_eq_nsmul]
    rw [e1]
    exact nat_smul_mem _ c (nat_smul_mem _ c h)
  · rw [h1, zpow_zero, inv_one, one_smul] at h
    exact nsmul_mem h c
  · rw [h1, zpow_neg_one, inv_inv, Nat.cast_smul_eq_nsmul] at h
    exact h

/- English proof (translation)
Establish `hc0 : (c : E) ≠ 0` using `Nat.cast_ne_zero.2 hc.ne'`. Use `(mem_twO M c e _).2 fun Q => ?_` and prove the remaining obligations. Establish `h` using `le_locP' M Q hx`. Rewrite using `[← Nat.cast_smul_eq_nsmul E, smul_smul]`. Break down `he Q with h1 | h1 | h1` into its components or cases.

Rewrite using `[h1, zpow_one, inv_mul_cancel₀ hc0, one_smul]`. Conclude with `h`. Rewrite using `[h1, zpow_zero, inv_one, one_mul]`. Conclude with `nat_smul_mem _ c h`. Rewrite using `[h1, zpow_neg_one, inv_inv, ← smul_smul]`.

Conclude with `nat_smul_mem _ c (nat_smul_mem _ c h)`.
-/
theorem nsmul_mem_tw (M : Submodule (𝓞 E) W) (c : ℕ) (hc : 0 < c) (e : HeightOneSpectrum (𝓞 E) → ℤ)
    (he : ∀ Q, e Q = 1 ∨ e Q = 0 ∨ e Q = -1) {x : W} (hx : x ∈ M) : c • x ∈ twist₂ M c e := by
  have hc0 : (c : E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  refine (mem_twO M c e _).2 fun Q => ?_
  have h := le_locP' M Q hx
  rw [← Nat.cast_smul_eq_nsmul E, smul_smul]
  rcases he Q with h1 | h1 | h1
  · rw [h1, zpow_one, inv_mul_cancel₀ hc0, one_smul]; exact h
  · rw [h1, zpow_zero, inv_one, one_mul]; exact nat_smul_mem _ c h
  · rw [h1, zpow_neg_one, inv_inv, ← smul_smul]; exact nat_smul_mem _ c (nat_smul_mem _ c h)

/- English proof (translation)
Apply the tactic sequence `rcases expS_cases SS Q with h | h | h <;> rw [h] <;> simp`.
-/
theorem negExpS_cases (SS : Finset (HeightOneSpectrum (𝓞 E))) (Q : HeightOneSpectrum (𝓞 E)) :
    -expS SS Q = 1 ∨ -expS SS Q = 0 ∨ -expS SS Q = -1 := by
  rcases expS_cases SS Q with h | h | h <;> rw [h] <;> simp

/- English proof (translation)
Introduce `E _ _ _ ι _ a b emb δ AA0 SS N N' c hc`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `x ⟨s, hs, rfl⟩`. Conclude with `⟨c • s, tw_nsmul_mem _ c hc _ (negExpS_cases SS) hs, map_nsmul _ _ _⟩`. Introduce and unpack `x ⟨s, hs, rfl⟩`.

Conclude with `⟨c • s, tw_nsmul_mem _ c hc _ (expS_cases SS) hs, map_nsmul _ _ _⟩`. Introduce and unpack `x ⟨s, hs, rfl⟩`. Conclude with `⟨c • s, nsmul_mem_tw _ c hc _ (expS_cases SS) hs, map_nsmul _ _ _⟩`.
-/
theorem half_periods_torsion : HalvesTor := by
  intro E _ _ _ ι _ a b emb δ AA0 SS N N' c hc
  refine ⟨?_, ?_, ?_⟩
  · rintro x ⟨s, hs, rfl⟩
    exact ⟨c • s, tw_nsmul_mem _ c hc _ (negExpS_cases SS) hs, map_nsmul _ _ _⟩
  · rintro x ⟨s, hs, rfl⟩
    exact ⟨c • s, tw_nsmul_mem _ c hc _ (expS_cases SS) hs, map_nsmul _ _ _⟩
  · rintro x ⟨s, hs, rfl⟩
    exact ⟨c • s, nsmul_mem_tw _ c hc _ (expS_cases SS) hs, map_nsmul _ _ _⟩

end Tw

/- English proof (translation)
Use `⟨Nat.pos_of_ne_zero h0, fun q hq hd => ?_⟩` and prove the remaining obligations. Establish `: Fact q.Prime` using `⟨hq⟩`. Establish `: (Λ₁.addSubgroupOf Λ₂).FiniteIndex` using `⟨h0⟩`. Establish `: Finite (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂)` using `AddSubgroup.finite_quotient_of_finiteIndex`. Take `⟨x, hx⟩` from `exists_prime_addOrderOf_dvd_card' (G := Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) q hd`.

Establish `h1 : c • x = 0`. Proceed by induction on `x using QuotientAddGroup.induction_on with`. Consider the case `H y`. Rewrite using `[← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]`. Conclude with `AddSubgroup.mem_addSubgroupOf.2 (hk y y.2)`.

Establish `h2` using `addOrderOf_dvd_of_nsmul_eq_zero h1`. Rewrite `h2` using `[hx]`. Conclude with `hS.2 q hq h2`.
-/
theorem snum_relIdx {V : Type} [AddCommGroup V] {S : Finset ℕ} (Λ₁ Λ₂ : AddSubgroup V) (c : ℕ) (hS : SNum S c) (h0 : relIdx Λ₁ Λ₂ ≠ 0)
    (hk : ∀ x ∈ Λ₂, c • x ∈ Λ₁) : SNum S (relIdx Λ₁ Λ₂) := by
  refine ⟨Nat.pos_of_ne_zero h0, fun q hq hd => ?_⟩
  have : Fact q.Prime := ⟨hq⟩
  have : (Λ₁.addSubgroupOf Λ₂).FiniteIndex := ⟨h0⟩
  have : Finite (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) := AddSubgroup.finite_quotient_of_finiteIndex
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) q hd
  have h1 : c • x = 0 := by
    induction x using QuotientAddGroup.induction_on with
    | H y =>
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
      exact AddSubgroup.mem_addSubgroupOf.2 (hk y y.2)
  have h2 := addOrderOf_dvd_of_nsmul_eq_zero h1
  rw [hx] at h2
  exact hS.2 q hq h2

/- English proof (translation)
Introduce `E _ _ _ ι _ a b emb δ d sc AA0 SS N N' c S Ξ θ hL h1 h2 h3 hS hΞ`. Take `⟨tA, tB, tL⟩` from `half_periods_torsion E ι a b emb δ AA0 SS N N' c hS.1`. Establish `r1` using `repsOf_spec _ _ h1`. Establish `r2` using `repsOf_spec _ _ h2`. Establish `r3` using `repsOf_spec _ _ h3`.

Use `twist_lattice_kernel _ (HV sc) (Real.sqrt d / 2) (LamC emb δ AA0 N N') S _ _ _ _ θ hL (fun x hx => ⟨c, hS, tA x (r1.1 x hx)⟩) (fun x hx => ⟨c, hS, tA x (r2.1 x hx).2⟩) (fun x hx => ⟨c, hS, tB x (r3.1 x hx)⟩) ?_ ?_` and prove the remaining obligations. Rewrite using `[(cosetRepsExist _ _ _ h2).2 _ r2]`. Conclude with `snum_relIdx _ _ c hS h2 fun x hx => tL x hx.1`. Introduce `x _ s _`. Unfold `onV`.

Use `split_ifs`. Conclude with `hΞ _`. Conclude with `IntOff.zero`.
-/
theorem theta_coset_kernel : ThCKer := by
  intro E _ _ _ ι _ a b emb δ d sc AA0 SS N N' c S Ξ θ hL h1 h2 h3 hS hΞ
  obtain ⟨tA, tB, tL⟩ := half_periods_torsion E ι a b emb δ AA0 SS N N' c hS.1
  have r1 := repsOf_spec _ _ h1
  have r2 := repsOf_spec _ _ h2
  have r3 := repsOf_spec _ _ h3
  refine twist_lattice_kernel _ (HV sc) (Real.sqrt d / 2) (LamC emb δ AA0 N N') S _ _ _ _ θ hL
    (fun x hx => ⟨c, hS, tA x (r1.1 x hx)⟩) (fun x hx => ⟨c, hS, tA x (r2.1 x hx).2⟩) (fun x hx => ⟨c, hS, tB x (r3.1 x hx)⟩) ?_ ?_
  · rw [(cosetRepsExist _ _ _ h2).2 _ r2]
    exact snum_relIdx _ _ c hS h2 fun x hx => tL x hx.1
  · intro x _ s _
    unfold onV
    split_ifs
    · exact hΞ _
    · exact IntOff.zero

section Read

open Formalism.L2.Col

variable {D : D7} {X : Fields} (s : Seam D X) {a b : ℕ}

/- English proof (translation)
Establish `h` using `Equiv.sum_comp s.iT fun τ' => ∑ i, ∑ j, z τ' i j * (starRingEnd ℂ) (w τ' i j)`. Use `show ((A⁻¹ : ℝ) : ℂ) * (∑ τ, ∑ i, ∑ j, z (s.iT τ) i j * (starRingEnd ℂ) (w (s.iT τ) i j)) = _`. Rewrite using `[h, formV_apply]`. Use `push_cast`. Rewrite using `[div_eq_inv_mul]`.
-/
theorem HV_push (A : ℝ) (z w : TaylorLogMetric.VC D a b) :
    HV A⁻¹ (fun τ => z (s.iT τ) : VV X.Tau a b) (fun τ => w (s.iT τ)) = formV A D.what₂.Tau a b z w := by
  have h := Equiv.sum_comp s.iT fun τ' => ∑ i, ∑ j, z τ' i j * (starRingEnd ℂ) (w τ' i j)
  show ((A⁻¹ : ℝ) : ℂ) * (∑ τ, ∑ i, ∑ j, z (s.iT τ) i j * (starRingEnd ℂ) (w (s.iT τ) i j)) = _
  rw [h, formV_apply]
  push_cast
  rw [div_eq_inv_mul]

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Simplify using `[Seam.pt]`.
-/
theorem pt_iT (t : VCx X.Tau a b) : (fun τ => s.pt t (s.iT τ)) = t := by
  funext τ; simp [Seam.pt]

/- English proof (translation)
Establish `h1` using `HV_push s A z (s.pt t)`. Establish `h2` using `HV_push s A (s.pt t) (s.pt t)`. Rewrite `h1`, `h2` using `[pt_iT]`. Unfold `opU`. Rewrite using `[h1, h2]`.

Use `congr 2`. Use function extensionality and compare the values at `τ`. Simplify using `[Seam.pt]`.
-/
theorem push_opU (A : ℝ) (t : VCx X.Tau a b) (F : VCx X.Tau a b → ℂ) (z : TaylorLogMetric.VC D a b) :
    opU (HV A⁻¹) t F (fun τ => z (s.iT τ)) = opU (formV A D.what₂.Tau a b) (s.pt t) (s.push F) z := by
  have h1 := HV_push s A z (s.pt t)
  have h2 := HV_push s A (s.pt t) (s.pt t)
  rw [pt_iT] at h1 h2
  unfold opU
  rw [h1, h2]
  congr 2
  funext τ
  simp [Seam.pt]

/- English proof (translation)
Introduce `D X u C r s A T e S0 i hyp c c'`. Take `⟨hsc, hlev, h⟩` from `hyp`. Take `⟨he, hlat, hint, i1, i2, i3, hX⟩` from `h c c'`. Take `⟨n, ρ, t, hρ, ht, hΘ⟩` from `theta_coset_kernel _ _ _ _ (X.embC A.σ₀) A.δ A.d A.sc A.AA r.SS (r.N i c) (r.N (i + 1) c') r.lev S0 (r.Xi i c c') (A.e _ _ (r.N i c) (r.N (i + 1) c')) hint i1 i2 i3 hlev hX`. Use `(kernel_comparison_holds D T e S0 _ _ _ _ _).1 ⟨n, ρ, fun k => s.pt (t k), hρ, fun k => ?_, ?_⟩` and prove the remaining obligations.

Take `⟨a, ha, h2⟩` from `ht k`. Conclude with `⟨a, ha, hlat _ h2⟩`. Use function extensionality and compare the values at `z`. Unfold `KerRead.Th Seam.push`. Rewrite using `[hΘ]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hsc, push_opU, he]`.
-/
theorem reading_is_kernel : ReadIsKer := by
  intro D X u C r s A T e S0 i hyp c c'
  obtain ⟨hsc, hlev, h⟩ := hyp
  obtain ⟨he, hlat, hint, i1, i2, i3, hX⟩ := h c c'
  obtain ⟨n, ρ, t, hρ, ht, hΘ⟩ := theta_coset_kernel _ _ _ _ (X.embC A.σ₀) A.δ A.d A.sc A.AA r.SS (r.N i c) (r.N (i + 1) c') r.lev S0
    (r.Xi i c c') (A.e _ _ (r.N i c) (r.N (i + 1) c')) hint i1 i2 i3 hlev hX
  refine (kernel_comparison_holds D T e S0 _ _ _ _ _).1 ⟨n, ρ, fun k => s.pt (t k), hρ, fun k => ?_, ?_⟩
  · obtain ⟨a, ha, h2⟩ := ht k
    exact ⟨a, ha, hlat _ h2⟩
  · funext z
    unfold KerRead.Th Seam.push
    rw [hΘ]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hsc, push_opU, he]

end Read

section Wt

open MvPolynomial Formalism.L2.DIV

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {a b n : ℕ}

/- English proof (translation)
Establish `e : ∏ r : Fin a, f (Fin.castLE h r) = ∏ r ∈ Finset.univ.map (Fin.castLEEmb h), f r`. Rewrite using `[Finset.prod_map]`. Both sides reduce to the same expression. Rewrite using `[e]`. Use `(Finset.prod_subset (Finset.subset_univ _) fun r _ hr => h0 r ?_).symm` and prove the remaining obligations.

Assume the negation of the conclusion as `hlt`. Conclude with `hr (Finset.mem_map.2 ⟨⟨r.1, not_le.1 hlt⟩, Finset.mem_univ _, rfl⟩)`.
-/
theorem prod_castLE {M : Type} [CommMonoid M] (h : a ≤ b) (f : Fin b → M) (h0 : ∀ r : Fin b, a ≤ r.1 → f r = 1) :
    ∏ r, f r = ∏ r : Fin a, f (Fin.castLE h r) := by
  have e : ∏ r : Fin a, f (Fin.castLE h r) = ∏ r ∈ Finset.univ.map (Fin.castLEEmb h), f r := by
    rw [Finset.prod_map]; rfl
  rw [e]
  refine (Finset.prod_subset (Finset.subset_univ _) fun r _ hr => h0 r ?_).symm
  by_contra hlt
  exact hr (Finset.mem_map.2 ⟨⟨r.1, not_le.1 hlt⟩, Finset.mem_univ _, rfl⟩)

/- English proof (translation)
Establish `e : ∑ r : Fin a, f (Fin.castLE h r) = ∑ r ∈ Finset.univ.map (Fin.castLEEmb h), f r`. Rewrite using `[Finset.sum_map]`. Both sides reduce to the same expression. Rewrite using `[e]`. Use `(Finset.sum_subset (Finset.subset_univ _) fun r _ hr => h0 r ?_).symm` and prove the remaining obligations.

Assume the negation of the conclusion as `hlt`. Conclude with `hr (Finset.mem_map.2 ⟨⟨r.1, not_le.1 hlt⟩, Finset.mem_univ _, rfl⟩)`.
-/
theorem sum_castLE {M : Type} [AddCommMonoid M] (h : a ≤ b) (f : Fin b → M) (h0 : ∀ r : Fin b, a ≤ r.1 → f r = 0) :
    ∑ r, f r = ∑ r : Fin a, f (Fin.castLE h r) := by
  have e : ∑ r : Fin a, f (Fin.castLE h r) = ∑ r ∈ Finset.univ.map (Fin.castLEEmb h), f r := by
    rw [Finset.sum_map]; rfl
  rw [e]
  refine (Finset.sum_subset (Finset.subset_univ _) fun r _ hr => h0 r ?_).symm
  by_contra hlt
  exact hr (Finset.mem_map.2 ⟨⟨r.1, not_le.1 hlt⟩, Finset.mem_univ _, rfl⟩)

def liftL (φ : Pol K ι b →ₐ[K] Pol K ι b) :
    MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K →ₐ[K] MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K :=
  aeval (Sum.elim (fun v => rename Sum.inl (φ (X v))) fun w => X (Sum.inr w))

/- English proof (translation)
Establish `h : ((liftL (a` using `a) φ).comp (rename Sum.inl)) = (rename Sum.inl).comp φ := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `[liftL]`. Conclude with `DFunLike.congr_fun h f`.
-/
theorem liftL_inl (φ : Pol K ι b →ₐ[K] Pol K ι b) (f : Pol K ι b) :
    liftL (a := a) φ (rename Sum.inl f) = rename Sum.inl (φ f) := by
  have h : ((liftL (a := a) φ).comp (rename Sum.inl)) = (rename Sum.inl).comp φ := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [liftL]
  exact DFunLike.congr_fun h f

/- English proof (translation)
Establish `h : ((liftL (a` using `a) φ).comp (rename Sum.inr)) = rename Sum.inr := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `[liftL]`. Conclude with `DFunLike.congr_fun h g`.
-/
theorem liftL_inr (φ : Pol K ι b →ₐ[K] Pol K ι b) (g : MvPolynomial (DVar ι a b) K) :
    liftL (a := a) φ (rename Sum.inr g) = rename Sum.inr g := by
  have h : ((liftL (a := a) φ).comp (rename Sum.inr)) = rename Sum.inr := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [liftL]
  exact DFunLike.congr_fun h g

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on' with`. Consider the case `monomial p d`. Rewrite using `[rename_monomial, rename_monomial, monomial_mul, jetLin_mixed, smul_monomial, smul_eq_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Consider the case `add f g hf hg => rw [map_add, add_mul, map_add, hf, hg, smul_add]`.
-/
theorem jetLin_inl_mul (J : (DVar ι a b →₀ ℕ) → K) (f : Pol K ι b) (q : DVar ι a b →₀ ℕ) (c : K) :
    jetLin J (rename Sum.inl f * rename Sum.inr (monomial q c)) = (c * J q) • f := by
  induction f using MvPolynomial.induction_on' with
  | monomial p d =>
    rw [rename_monomial, rename_monomial, monomial_mul, jetLin_mixed, smul_monomial, smul_eq_mul]
    congr 1
    ring
  | add f g hf hg => rw [map_add, add_mul, map_add, hf, hg, smul_add]

/- English proof (translation)
Proceed by induction on `R using MvPolynomial.induction_on' with`. Consider the case `monomial m c`. Rewrite using `[split_mono m]`. Use `set p := m.comapDomain Sum.inl Sum.inl_injective.injOn`. Use `set q := m.comapDomain Sum.inr Sum.inr_injective.injOn`.

Establish `h : (monomial (p.mapDomain Sum.inl + q.mapDomain Sum.inr) c : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) = rename Sum.inl (monomial p 1) * rename Sum.inr (monomial q c)`. Rewrite using `[rename_monomial, rename_monomial, monomial_mul, one_mul]`. Rewrite using `[h, map_mul, liftL_inl, liftL_inr, jetLin_inl_mul, jetLin_inl_mul, map_smul]`. Consider the case `add f g hf hg => rw [map_add, map_add, map_add, map_add, hf, hg]`.
-/
theorem jetLin_liftL (J : (DVar ι a b →₀ ℕ) → K) (φ : Pol K ι b →ₐ[K] Pol K ι b)
    (R : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) : jetLin J (liftL φ R) = φ (jetLin J R) := by
  induction R using MvPolynomial.induction_on' with
  | monomial m c =>
    rw [split_mono m]
    set p := m.comapDomain Sum.inl Sum.inl_injective.injOn
    set q := m.comapDomain Sum.inr Sum.inr_injective.injOn
    have h : (monomial (p.mapDomain Sum.inl + q.mapDomain Sum.inr) c : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) =
        rename Sum.inl (monomial p 1) * rename Sum.inr (monomial q c) := by
      rw [rename_monomial, rename_monomial, monomial_mul, one_mul]
    rw [h, map_mul, liftL_inl, liftL_inr, jetLin_inl_mul, jetLin_inl_mul, map_smul]
  | add f g hf hg => rw [map_add, map_add, map_add, map_add, hf, hg]

def resB (h : a ≤ b) (β : ι → Matrix (Fin b) (Fin b) K) : ι → Matrix (Fin a) (Fin a) K :=
  fun τ r s => β τ (Fin.castLE h r) (Fin.castLE h s)

/- English proof (translation)
Introduce `τ` and use `⟨fun _ _ hrs => (hβ τ).1 _ _ hrs, fun _ => (hβ τ).2 _⟩`.
-/
theorem isBor_resB (h : a ≤ b) {β : ι → Matrix (Fin b) (Fin b) K} (hβ : IsBor β) : IsBor (resB h β) :=
  fun τ => ⟨fun _ _ hrs => (hβ τ).1 _ _ hrs, fun _ => (hβ τ).2 _⟩

/- English proof (translation)
Establish `e : (liftL (colSub β)).comp (subD K ι a b) = (subD K ι a b).comp (colSub (resB h β))`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `⟨τ, α, s⟩`. Establish `hs : s.1 < b` using `lt_of_lt_of_le s.2 h`. Simplify using `only [AlgHom.comp_apply, subD, colSub, aeval_X, dif_pos hs, map_sum, map_mul, liftL, Sum.elim_inl, Sum.elim_inr, rename_X, algHom_C, algebraMap_eq]`.

Establish `h1 : ∀ r : Fin a, (r : ℕ) < b` using `fun r => lt_of_lt_of_le r.2 h`. Simplify using `only [dif_pos (h1 _)]`. Simplify using `only [Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Rewrite using `[sum_castLE h]`.

Use `Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun β' _ => ?_` and prove the remaining obligations. Simplify using `only [resB]`. Rewrite using `[mul_assoc]`. Both sides reduce to the same expression. Introduce `r hr`.

Use `Finset.sum_eq_zero fun β' _ => ?_` and prove the remaining obligations. Rewrite using `[(hβ τ).1 r ⟨s.1, hs⟩ (Fin.lt_def.2 (lt_of_lt_of_le s.2 hr)), C_0, zero_mul, zero_mul]`. Conclude with `DFunLike.congr_fun e Q`.
-/
theorem liftL_subD (h : a ≤ b) {β : ι → Matrix (Fin b) (Fin b) K} (hβ : IsBor β) (Q : Pol K ι a) :
    liftL (colSub β) (subD K ι a b Q) = subD K ι a b (colSub (resB h β) Q) := by
  have e : (liftL (colSub β)).comp (subD K ι a b) = (subD K ι a b).comp (colSub (resB h β)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨τ, α, s⟩
    have hs : s.1 < b := lt_of_lt_of_le s.2 h
    simp only [AlgHom.comp_apply, subD, colSub, aeval_X, dif_pos hs, map_sum, map_mul, liftL, Sum.elim_inl, Sum.elim_inr, rename_X,
      algHom_C, algebraMap_eq]
    have h1 : ∀ r : Fin a, (r : ℕ) < b := fun r => lt_of_lt_of_le r.2 h
    simp only [dif_pos (h1 _)]
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    rw [sum_castLE h]
    · refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun β' _ => ?_
      simp only [resB]
      rw [mul_assoc]
      rfl
    · intro r hr
      refine Finset.sum_eq_zero fun β' _ => ?_
      rw [(hβ τ).1 r ⟨s.1, hs⟩ (Fin.lt_def.2 (lt_of_lt_of_le s.2 hr)), C_0, zero_mul, zero_mul]
  exact DFunLike.congr_fun e Q

/- English proof (translation)
Unfold `jetMap`. Simplify using `only [LinearMap.comp_apply, LinearMap.mulRight_apply, pow_zero, Finset.prod_const_one, mul_one, AlgHom.toLinearMap_apply]`.
-/
theorem jetMap_zero (J : (DVar ι a b →₀ ℕ) → K) (Q : Pol K ι a) : jetMap J (fun _ => 0) Q = jetLin J (subD K ι a b Q) := by
  unfold jetMap
  simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, pow_zero, Finset.prod_const_one, mul_one, AlgHom.toLinearMap_apply]

/- English proof (translation)
Introduce `K _ ι _ a b h J ν Q hQ β hβ`. Rewrite using `[jetMap_zero, ← jetLin_liftL, liftL_subD h hβ, hQ _ (isBor_resB h hβ), map_smul, map_smul]`. Use `congr 1`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[prod_castLE h]`.

Use `Finset.prod_congr rfl fun r _ => ?_` and prove the remaining obligations. Simplify using `only [resB, extNu]`. Rewrite using `[dif_pos (show ((Fin.castLE h r : Fin b) : ℕ) < a from r.2)]`. Both sides reduce to the same expression. Introduce `r hr`.

Simplify using `only [extNu]`. Rewrite using `[dif_neg (not_lt.2 hr), pow_zero]`.
-/
theorem jet_weight : JetWt := by
  intro K _ ι _ a b h J ν Q hQ β hβ
  rw [jetMap_zero, ← jetLin_liftL, liftL_subD h hβ, hQ _ (isBor_resB h hβ), map_smul, map_smul]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [prod_castLE h]
  · refine Finset.prod_congr rfl fun r _ => ?_
    simp only [resB, extNu]
    rw [dif_pos (show ((Fin.castLE h r : Fin b) : ℕ) < a from r.2)]
    rfl
  · intro r hr
    simp only [extNu]
    rw [dif_neg (not_lt.2 hr), pow_zero]

end Wt

section BaseCh

open MvPolynomial Formalism.L2.DIV

variable {K L : Type} [Field K] [Field L] {ι : Type} [Fintype ι] {a b : ℕ}

/- English proof (translation)
Proceed by induction on `R using MvPolynomial.induction_on' with`. Consider the case `monomial m c => rw [jetLin_monomial, map_monomial, map_monomial, jetLin_monomial, map_mul]`. Consider the case `add f g hf hg => simp only [map_add, hf, hg]`.
-/
theorem map_jetLin (σ : K →+* L) (J : (DVar ι a b →₀ ℕ) → K) (R : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) :
    map σ (jetLin J R) = jetLin (fun m => σ (J m)) (map σ R) := by
  induction R using MvPolynomial.induction_on' with
  | monomial m c => rw [jetLin_monomial, map_monomial, map_monomial, jetLin_monomial, map_mul]
  | add f g hf hg => simp only [map_add, hf, hg]

/- English proof (translation)
Establish `e : (map σ).comp (subD K ι a b).toRingHom = ((subD L ι a b).toRingHom).comp (map σ)`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `c`. Simplify using `[subD]`. Introduce `v`.

Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, subD, aeval_X, map_X]`. Apply the tactic sequence `split_ifs <;> simp`. Conclude with `RingHom.congr_fun e P`.
-/
theorem map_subD (σ : K →+* L) (P : Pol K ι a) : map σ (subD K ι a b P) = subD L ι a b (map σ P) := by
  have e : (map σ).comp (subD K ι a b).toRingHom = ((subD L ι a b).toRingHom).comp (map σ) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [subD]
    · intro v
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, subD, aeval_X, map_X]
      split_ifs <;> simp
  exact RingHom.congr_fun e P

/- English proof (translation)
Unfold `frDet`. Rewrite using `[RingHom.map_det]`. Use `congr 1`. Use extensionality with `α s`. Simplify using the standard rewrite rules.
-/
theorem map_frDet (σ : K →+* L) (τ : ι) : map σ (frDet K a τ) = frDet L a τ := by
  unfold frDet
  rw [RingHom.map_det]
  congr 1
  ext α s
  simp

/- English proof (translation)
Unfold `jetMap`. Simplify using `only [LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply]`. Rewrite using `[map_jetLin, map_subD, map_mul, map_prod]`. Simplify using `only [map_pow, map_frDet]`.
-/
theorem map_jetMap (σ : K →+* L) (J : (DVar ι a b →₀ ℕ) → K) (n : ι → ℕ) (P : Pol K ι a) :
    map σ (jetMap J n P) = jetMap (fun m => σ (J m)) n (map σ P) := by
  unfold jetMap
  simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply]
  rw [map_jetLin, map_subD, map_mul, map_prod]
  simp only [map_pow, map_frDet]

/- English proof (translation)
Apply `(basisMonomials ((ι × Fin b × Fin b) ⊕ DVar ι a b) K).ext` to reduce the goal to its premises. Introduce `m`. Rewrite using `[LinearMap.smul_apply]`. Simplify using `only [coe_basisMonomials, jetLin_monomial, one_mul, smul_monomial, smul_eq_mul]`.
-/
theorem jetLin_scal (c : K) (J : (DVar ι a b →₀ ℕ) → K) : jetLin (fun m => c * J m) = c • jetLin J := by
  apply (basisMonomials ((ι × Fin b × Fin b) ⊕ DVar ι a b) K).ext
  intro m
  rw [LinearMap.smul_apply]
  simp only [coe_basisMonomials, jetLin_monomial, one_mul, smul_monomial, smul_eq_mul]

/- English proof (translation)
Unfold `jetMap`. Rewrite using `[jetLin_scal]`. Both sides reduce to the same expression.
-/
theorem jetMap_scal (c : K) (J : (DVar ι a b →₀ ℕ) → K) (n : ι → ℕ) (P : Pol K ι a) :
    jetMap (fun m => c * J m) n P = c • jetMap J n P := by
  unfold jetMap
  rw [jetLin_scal]
  rfl

/- English proof (translation)
Rewrite using `[jetMap_zero]`. Both sides reduce to the same expression.
-/
theorem jetMap_shift (J : (DVar ι a b →₀ ℕ) → K) (n : ι → ℕ) (P : Pol K ι a) :
    jetMap J n P = jetMap J (fun _ => 0) (P * ∏ τ, frDet K a τ ^ n τ) := by
  rw [jetMap_zero]
  rfl

end BaseCh

section UnfG

open MvPolynomial Formalism.L2.DIV

variable {ι : Type} [Fintype ι] {a b : ℕ} {Y Y' : Type}

/- English proof (translation)
Unfold `frDet`. Rewrite using `[RingHom.map_det]`. Use `congr 1`. Use extensionality with `α k`. Simplify using the standard rewrite rules.
-/
theorem eval_frDet (v : ι × Fin a × Fin a → ℂ) (τ : ι) : eval v (frDet ℂ a τ) = (Matrix.of fun α k => v (τ, α, k)).det := by
  unfold frDet
  rw [RingHom.map_det]
  congr 1
  ext α k
  simp

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `Q hQ`. Establish `h0 : Q * ∏ τ, frDet ℂ a τ = 0`. Apply `MvPolynomial.funext` to reduce the goal to its premises. Introduce `v`.

Rewrite using `[map_mul, map_zero, map_prod]`. Simplify using `only [eval_frDet]`. Distinguish the cases in `h : ∀ τ, (Matrix.of fun α k => v (τ, α, k) : Matrix (Fin a) (Fin a) ℂ).det ≠ 0`. Take `⟨y, hy⟩` from `hr (fun τ => Matrix.of fun α k => v (τ, α, k)) h`. Establish `h1` using `congrFun hQ y`.

Establish `h2 : eval v Q = 0`. Establish `: frPolyG fr Q y = eval v Q` using `by show eval (fun k : ι × Fin a × Fin a => fr y k.1 k.2.1 k.2.2) Q = _`. Rewrite using `[hy]`. Both sides reduce to the same expression. Rewrite using `[← this, h1]`.

Both sides reduce to the same expression. Rewrite using `[h2, zero_mul]`. Use `push Not at h`. Take `⟨τ, hτ⟩` from `h`. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ τ) hτ, mul_zero]`.

Break down `mul_eq_zero.1 h0 with h | h` into its components or cases. Conclude with `h`. It suffices to derive a contradiction. Establish `h1` using `congrArg (eval fun k : ι × Fin a × Fin a => if k.2.1 = k.2.2 then (1 : ℂ) else 0) h`. Rewrite `h1` using `[map_prod, map_zero]`.

Simplify using `only [eval_frDet] at h1`. Establish `h2 : ∀ τ : ι, (Matrix.of fun α k : Fin a => (if α = k then (1 : ℂ) else 0)).det = 1`. Introduce `τ`. Establish `: (Matrix.of fun α k : Fin a => (if α = k then (1 : ℂ) else 0)) = 1`. Use extensionality with `α k`.

Simplify using `[Matrix.one_apply]`. Rewrite using `[this, Matrix.det_one]`. Conclude with `one_ne_zero ((Finset.prod_eq_one fun τ _ => h2 τ).symm.trans h1)`.
-/
theorem frPolyG_inj (fr : Y → ι → Matrix (Fin a) (Fin a) ℂ)
    (hr : ∀ f : ι → Matrix (Fin a) (Fin a) ℂ, (∀ τ, (f τ).det ≠ 0) → ∃ y, fr y = f) : Function.Injective (frPolyG fr) := by
  rw [injective_iff_map_eq_zero]
  intro Q hQ
  have h0 : Q * ∏ τ, frDet ℂ a τ = 0 := by
    apply MvPolynomial.funext
    intro v
    rw [map_mul, map_zero, map_prod]
    simp only [eval_frDet]
    by_cases h : ∀ τ, (Matrix.of fun α k => v (τ, α, k) : Matrix (Fin a) (Fin a) ℂ).det ≠ 0
    · obtain ⟨y, hy⟩ := hr (fun τ => Matrix.of fun α k => v (τ, α, k)) h
      have h1 := congrFun hQ y
      have h2 : eval v Q = 0 := by
        have : frPolyG fr Q y = eval v Q := by
          show eval (fun k : ι × Fin a × Fin a => fr y k.1 k.2.1 k.2.2) Q = _
          rw [hy]; rfl
        rw [← this, h1]; rfl
      rw [h2, zero_mul]
    · push Not at h
      obtain ⟨τ, hτ⟩ := h
      rw [Finset.prod_eq_zero (Finset.mem_univ τ) hτ, mul_zero]
  rcases mul_eq_zero.1 h0 with h | h
  · exact h
  · exfalso
    have h1 := congrArg (eval fun k : ι × Fin a × Fin a => if k.2.1 = k.2.2 then (1 : ℂ) else 0) h
    rw [map_prod, map_zero] at h1
    simp only [eval_frDet] at h1
    have h2 : ∀ τ : ι, (Matrix.of fun α k : Fin a => (if α = k then (1 : ℂ) else 0)).det = 1 := by
      intro τ
      have : (Matrix.of fun α k : Fin a => (if α = k then (1 : ℂ) else 0)) = 1 := by
        ext α k; simp [Matrix.one_apply]
      rw [this, Matrix.det_one]
    exact one_ne_zero ((Finset.prod_eq_one fun τ _ => h2 τ).symm.trans h1)

/- English proof (translation)
The claim follows from `Classical.epsilon_spec (p := fun g => g ∘ₗ frPolyG fr = LinearMap.id) (LinearMap.exists_leftInverse_of_injective _ (LinearMap.ker_eq_bot.2 hinj))`.
-/
theorem frInvG_spec {fr : Y → ι → Matrix (Fin a) (Fin a) ℂ} (hinj : Function.Injective (frPolyG fr)) :
    frInvG fr ∘ₗ frPolyG fr = LinearMap.id :=
  Classical.epsilon_spec (p := fun g => g ∘ₗ frPolyG fr = LinearMap.id)
    (LinearMap.exists_leftInverse_of_injective _ (LinearMap.ker_eq_bot.2 hinj))

/- English proof (translation)
Establish `h : frInvG fr (frPolyG fr Q) = Q` using `LinearMap.congr_fun (frInvG_spec hinj) Q`. Unfold `unfG`. Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, h]`.
-/
theorem unfG_frPolyG {fr : Y → ι → Matrix (Fin a) (Fin a) ℂ} (hinj : Function.Injective (frPolyG fr)) (fr' : Y' → ι → Matrix (Fin b) (Fin b) ℂ)
    (cD : ι → ℂ) (Θ : VCx ι a b → ℂ) (Q : Pol ℂ ι a) :
    unfG fr fr' cD Θ (frPolyG fr Q) = frPolyG fr' (jetMap (jetC cD Θ) (fun _ => 0) Q) := by
  have h : frInvG fr (frPolyG fr Q) = Q := LinearMap.congr_fun (frInvG_spec hinj) Q
  unfold unfG
  rw [LinearMap.comp_apply, LinearMap.comp_apply, h]

/- English proof (translation)
Use function extensionality and compare the values at `y`. Use `show (∏ τ, (fr y τ).det ^ sS τ) * ((∏ τ, (fr y τ).det ^ sh τ) * eval₂ σ (fun k : ι × Fin a × Fin a => fr y k.1 k.2.1 k.2.2) P) = eval (fun k : ι × Fin a × Fin a => fr y k.1 k.2.1 k.2.2) (map σ P * ∏ τ, frDet ℂ a τ ^ n τ)`. Rewrite using `[map_mul, eval_map, map_prod, ← mul_assoc, ← Finset.prod_mul_distrib, mul_comm]`. Use `congr 1`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Rewrite using `[map_pow, eval_frDet, ← zpow_add₀ (hdet y τ), add_comm, hn, zpow_natCast]`. Both sides reduce to the same expression.
-/
theorem mulFun_evG {K : Type} [Field K] {fr : Y → ι → Matrix (Fin a) (Fin a) ℂ} (hdet : ∀ y τ, (fr y τ).det ≠ 0) (σ : K →+* ℂ) (sh sS : ι → ℤ) (n : ι → ℕ)
    (hn : ∀ τ, sh τ + sS τ = n τ) (P : Pol K ι a) :
    mulFun (fun y => ∏ τ, (fr y τ).det ^ sS τ) (evG fr sh σ P) = frPolyG fr (map σ P * ∏ τ, frDet ℂ a τ ^ n τ) := by
  funext y
  show (∏ τ, (fr y τ).det ^ sS τ) * ((∏ τ, (fr y τ).det ^ sh τ) * eval₂ σ (fun k : ι × Fin a × Fin a => fr y k.1 k.2.1 k.2.2) P) =
    eval (fun k : ι × Fin a × Fin a => fr y k.1 k.2.1 k.2.2) (map σ P * ∏ τ, frDet ℂ a τ ^ n τ)
  rw [map_mul, eval_map, map_prod, ← mul_assoc, ← Finset.prod_mul_distrib, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_pow, eval_frDet, ← zpow_add₀ (hdet y τ), add_comm, hn, zpow_natCast]
  rfl

/- English proof (translation)
Introduce `K _ ι _ a b Y Y' fr fr' hinj hdet σ cD Θ J z hJ sh sS sD n hn P`. Establish `h1 : mulFun (fun y => ∏ τ, (fr y τ).det ^ sS τ) (evG fr sh σ P) = frPolyG fr (map σ P * ∏ τ, frDet ℂ a τ ^ n τ)`. Use function extensionality and compare the values at `y`. Use `show (∏ τ, (fr y τ).det ^ sS τ) * ((∏ τ, (fr y τ).det ^ sh τ) * eval₂ σ (fun k : ι × Fin a × Fin a => fr y k.1 k.2.1 k.2.2) P) = eval (fun k : ι × Fin a × Fin a => fr y k.1 k.2.1 k.2.2) (map σ P * ∏ τ, frDet ℂ a τ ^ n τ)`. Rewrite using `[map_mul, eval_map, map_prod, ← mul_assoc, ← Finset.prod_mul_distrib, mul_comm]`.

Use `congr 1`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow, eval_frDet, ← zpow_add₀ (hdet y τ), add_comm, hn, zpow_natCast]`. Both sides reduce to the same expression. Rewrite using `[h1, unfG_frPolyG hinj, ← jetMap_shift]`.

Use function extensionality and compare the values at `y'`. Use `show (∏ τ, (fr' y' τ).det ^ (-sD τ)) * eval₂ σ (fun k : ι × Fin b × Fin b => fr' y' k.1 k.2.1 k.2.2) (jetMap J n P) = z * ((∏ τ, (fr' y' τ).det ^ sD τ)⁻¹ * eval (fun k : ι × Fin b × Fin b => fr' y' k.1 k.2.1 k.2.2) (jetMap (jetC cD Θ) n (map σ P)))`. Rewrite using `[← eval_map, map_jetMap, funext hJ, jetMap_scal, smul_eval, ← Finset.prod_inv_distrib]`. Simplify using `only [zpow_neg]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem unfolding_gl_eval : UnfGEv := by
  intro K _ ι _ a b Y Y' fr fr' hinj hdet σ cD Θ J z hJ sh sS sD n hn P
  have h1 : mulFun (fun y => ∏ τ, (fr y τ).det ^ sS τ) (evG fr sh σ P) = frPolyG fr (map σ P * ∏ τ, frDet ℂ a τ ^ n τ) := by
    funext y
    show (∏ τ, (fr y τ).det ^ sS τ) * ((∏ τ, (fr y τ).det ^ sh τ) * eval₂ σ (fun k : ι × Fin a × Fin a => fr y k.1 k.2.1 k.2.2) P) =
      eval (fun k : ι × Fin a × Fin a => fr y k.1 k.2.1 k.2.2) (map σ P * ∏ τ, frDet ℂ a τ ^ n τ)
    rw [map_mul, eval_map, map_prod, ← mul_assoc, ← Finset.prod_mul_distrib, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_pow, eval_frDet, ← zpow_add₀ (hdet y τ), add_comm, hn, zpow_natCast]
    rfl
  rw [h1, unfG_frPolyG hinj, ← jetMap_shift]
  funext y'
  show (∏ τ, (fr' y' τ).det ^ (-sD τ)) * eval₂ σ (fun k : ι × Fin b × Fin b => fr' y' k.1 k.2.1 k.2.2) (jetMap J n P) =
    z * ((∏ τ, (fr' y' τ).det ^ sD τ)⁻¹ * eval (fun k : ι × Fin b × Fin b => fr' y' k.1 k.2.1 k.2.2) (jetMap (jetC cD Θ) n (map σ P)))
  rw [← eval_map, map_jetMap, funext hJ, jetMap_scal, smul_eval, ← Finset.prod_inv_distrib]
  simp only [zpow_neg]
  ring

/- English proof (translation)
Use function extensionality and compare the values at `y`. Simplify using `only [evG, smul_eq_C_mul, eval₂_mul, eval₂_C, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem evG_smul {K : Type} [Field K] (fr : Y → ι → Matrix (Fin a) (Fin a) ℂ) (sh : ι → ℤ) (σ : K →+* ℂ) (k : K) (P : Pol K ι a) :
    evG fr sh σ (k • P) = σ k • evG fr sh σ P := by
  funext y
  simp only [evG, smul_eq_C_mul, eval₂_mul, eval₂_C, Pi.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Establish `e : (eval fun k : ι × Fin a × Fin a => fr y k.1 k.2.1 k.2.2).comp (colSub β).toRingHom = eval fun k : ι × Fin a × Fin a => (fr y k.1 * β k.1) k.2.1 k.2.2`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `c`. Simplify using `[colSub]`. Introduce `v`.

Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, colSub, aeval_X, map_sum, map_mul, eval_C, eval_X, Matrix.mul_apply]`. Conclude with `Finset.sum_congr rfl fun r _ => mul_comm _ _`. Conclude with `RingHom.congr_fun e Q`.
-/
theorem frPolyG_colSub (fr : Y → ι → Matrix (Fin a) (Fin a) ℂ) (β : ι → Matrix (Fin a) (Fin a) ℂ) (Q : Pol ℂ ι a) (y : Y) :
    frPolyG fr (colSub β Q) y = eval (fun k : ι × Fin a × Fin a => (fr y k.1 * β k.1) k.2.1 k.2.2) Q := by
  have e : (eval fun k : ι × Fin a × Fin a => fr y k.1 k.2.1 k.2.2).comp (colSub β).toRingHom =
      eval fun k : ι × Fin a × Fin a => (fr y k.1 * β k.1) k.2.1 k.2.2 := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [colSub]
    · intro v
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, colSub, aeval_X, map_sum, map_mul, eval_C, eval_X,
        Matrix.mul_apply]
      exact Finset.sum_congr rfl fun r _ => mul_comm _ _
  exact RingHom.congr_fun e Q

/- English proof (translation)
The claim follows from `Matrix.det_of_isUpperTriangular fun r s h => (hβ τ).1 r s h`.
-/
theorem det_bor {β : ι → Matrix (Fin a) (Fin a) ℂ} (hβ : IsBor β) (τ : ι) : (β τ).det = ∏ r, β τ r r :=
  Matrix.det_of_isUpperTriangular fun r s h => (hβ τ).1 r s h

/- English proof (translation)
Simplify using `only [mul_zpow, Finset.prod_mul_distrib]`. Rewrite using `[mul_assoc, mul_comm]`. Use `congr 1`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Rewrite using `[det_bor hβ, ← Finset.prod_zpow, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[← zpow_add₀ ((hβ τ).2 r), add_comm, hν, zpow_natCast]`.
-/
theorem bor_id {β : ι → Matrix (Fin a) (Fin a) ℂ} (hβ : IsBor β) (d : ι → ℂ) (lam : ι → Fin a → ℤ) (sS : ι → ℤ) (ν : ι → Fin a → ℕ)
    (hν : ∀ τ r, lam τ r + sS τ = ν τ r) :
    (∏ τ, (d τ * (β τ).det) ^ sS τ) * ∏ τ, ∏ r, β τ r r ^ lam τ r = (∏ τ, ∏ r, β τ r r ^ ν τ r) * ∏ τ, d τ ^ sS τ := by
  simp only [mul_zpow, Finset.prod_mul_distrib]
  rw [mul_assoc, mul_comm]
  congr 1
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [det_bor hβ, ← Finset.prod_zpow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun r _ => ?_
  rw [← zpow_add₀ ((hβ τ).2 r), add_comm, hν, zpow_natCast]

/- English proof (translation)
Introduce `ι _ a Y fr hr lam sS ν hν F`. Establish `hdet : ∀ y τ, (fr y τ).det ≠ 0` using `fun y => (hr (fr y)).1 ⟨y, rfl⟩`. Establish `hinj : Function.Injective (frPolyG fr)` using `frPolyG_inj fr fun f hf => (hr f).2 hf`. Establish `hP : ∀ y, (∏ τ, (fr y τ).det ^ sS τ) ≠ 0` using `fun y => Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (hdet y τ)`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨Q, hQ, rfl⟩`. Use `⟨⟨fun y => (∏ τ, (fr y τ).det ^ sS τ)⁻¹ * frPolyG fr Q y, ⟨⟨Q * ∏ τ, frDet ℂ a τ ^ (-sS τ).toNat, fun τ => (sS τ).toNat, ?_⟩, ?_⟩, ?_⟩, Q, rfl⟩` and prove the remaining obligations. Introduce `y show (∏ τ, (fr y τ).det ^ sS τ)⁻¹ * eval (fun k : ι × Fin a × Fin a => fr y k.1 k.2.1 k.2.2) Q * ∏ τ, (fr y τ).det ^ (sS τ).toNat = eval (fun k : ι × Fin a × Fin a => fr y k.1 k.2.1 k.2.2) (Q * ∏ τ, frDet ℂ a τ ^ (-sS τ).toNat)`. Rewrite using `[map_mul, map_prod, mul_comm (∏ τ, (fr y τ).det ^ sS τ)⁻¹, mul_assoc, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]`. Use `congr 1`.

Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow, eval_frDet, ← zpow_neg, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hdet y τ)]`. Use `congr 1`. Use `Int.toNat_sub_toNat_neg (sS τ)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Introduce `y y₂ β hβ h2`. Establish `e1 : frPolyG fr Q y₂ = (∏ τ, ∏ r, β τ r r ^ ν τ r) * frPolyG fr Q y`. Use `frPolyG_colSub fr β Q y` as an intermediate fact. Rewrite `this` using `[hQ β hβ]`. Use `show eval (fun k : ι × Fin a × Fin a => fr y₂ k.1 k.2.1 k.2.2) Q = _`.

Simplify using `only [h2]`. Rewrite using `[← this]`. Simplify using the standard rewrite rules. Establish `e2` using `bor_id hβ (fun τ => (fr y τ).det) lam sS ν hν`. Establish `e3 : (∏ τ, (fr y₂ τ).det ^ sS τ) = ∏ τ, ((fr y τ).det * (β τ).det) ^ sS τ` using `Finset.prod_congr rfl fun τ _ => by rw [h2, Matrix.det_mul]`.

Use `show (∏ τ, (fr y₂ τ).det ^ sS τ)⁻¹ * frPolyG fr Q y₂ = _ * ((∏ τ, (fr y τ).det ^ sS τ)⁻¹ * frPolyG fr Q y)`. Rewrite using `[e1, inv_mul_eq_iff_eq_mul₀ (hP y₂), e3, ← mul_assoc, ← mul_assoc, e2, mul_assoc (∏ τ, ∏ r, β τ r r ^ ν τ r), mul_assoc, mul_inv_cancel₀ (hP y), one_mul]`. Use function extensionality and compare the values at `y show _ = (∏ τ, (fr y τ).det ^ sS τ) * ((∏ τ, (fr y τ).det ^ sS τ)⁻¹ * frPolyG fr Q y)`. Rewrite using `[mul_inv_cancel_left₀ (hP y)]`. Introduce and unpack `⟨⟨f, ⟨-, hw⟩, hF⟩, Q, hQ⟩`.

Use `⟨Q, fun β hβ => hinj ?_, hQ⟩` and prove the remaining obligations. Use function extensionality and compare the values at `y`. Take `⟨y₂, h2⟩` from `(hr fun τ => fr y τ * β τ).2 fun τ => by`. Rewrite using `[Matrix.det_mul, det_bor hβ]`. Conclude with `mul_ne_zero (hdet y τ) (Finset.prod_ne_zero_iff.2 fun r _ => (hβ τ).2 r)`.

Establish `h2' : ∀ τ, fr y₂ τ = fr y τ * β τ` using `fun τ => congrFun h2 τ`. Establish `e0 : ∀ y, frPolyG fr Q y = (∏ τ, (fr y τ).det ^ sS τ) * f y` using `fun y => by rw [← hQ, hF]; rfl`. Establish `e1 : frPolyG fr (colSub β Q) y = frPolyG fr Q y₂`. Rewrite using `[frPolyG_colSub]`. Use `show _ = eval (fun k : ι × Fin a × Fin a => fr y₂ k.1 k.2.1 k.2.2) Q`.

Simplify using `only [h2']`. Establish `e2` using `bor_id hβ (fun τ => (fr y τ).det) lam sS ν hν`. Establish `e3 : (∏ τ, (fr y₂ τ).det ^ sS τ) = ∏ τ, ((fr y τ).det * (β τ).det) ^ sS τ` using `Finset.prod_congr rfl fun τ _ => by rw [h2', Matrix.det_mul]`. Rewrite using `[e1, map_smul, Pi.smul_apply, smul_eq_mul, e0, e0, hw y y₂ β hβ h2', e3, ← mul_assoc, e2, mul_assoc]`.
-/
theorem sharp_vector_formula : SharpVIs := by
  intro ι _ a Y fr hr lam sS ν hν F
  have hdet : ∀ y τ, (fr y τ).det ≠ 0 := fun y => (hr (fr y)).1 ⟨y, rfl⟩
  have hinj : Function.Injective (frPolyG fr) := frPolyG_inj fr fun f hf => (hr f).2 hf
  have hP : ∀ y, (∏ τ, (fr y τ).det ^ sS τ) ≠ 0 := fun y => Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (hdet y τ)
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    refine ⟨⟨fun y => (∏ τ, (fr y τ).det ^ sS τ)⁻¹ * frPolyG fr Q y, ⟨⟨Q * ∏ τ, frDet ℂ a τ ^ (-sS τ).toNat, fun τ => (sS τ).toNat, ?_⟩, ?_⟩, ?_⟩, Q, rfl⟩
    · intro y
      show (∏ τ, (fr y τ).det ^ sS τ)⁻¹ * eval (fun k : ι × Fin a × Fin a => fr y k.1 k.2.1 k.2.2) Q * ∏ τ, (fr y τ).det ^ (sS τ).toNat =
        eval (fun k : ι × Fin a × Fin a => fr y k.1 k.2.1 k.2.2) (Q * ∏ τ, frDet ℂ a τ ^ (-sS τ).toNat)
      rw [map_mul, map_prod, mul_comm (∏ τ, (fr y τ).det ^ sS τ)⁻¹, mul_assoc, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
      congr 1
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [map_pow, eval_frDet, ← zpow_neg, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hdet y τ)]
      congr 1
      have := Int.toNat_sub_toNat_neg (sS τ)
      omega
    · intro y y₂ β hβ h2
      have e1 : frPolyG fr Q y₂ = (∏ τ, ∏ r, β τ r r ^ ν τ r) * frPolyG fr Q y := by
        have := frPolyG_colSub fr β Q y
        rw [hQ β hβ] at this
        show eval (fun k : ι × Fin a × Fin a => fr y₂ k.1 k.2.1 k.2.2) Q = _
        simp only [h2]
        rw [← this]
        simp
      have e2 := bor_id hβ (fun τ => (fr y τ).det) lam sS ν hν
      have e3 : (∏ τ, (fr y₂ τ).det ^ sS τ) = ∏ τ, ((fr y τ).det * (β τ).det) ^ sS τ :=
        Finset.prod_congr rfl fun τ _ => by rw [h2, Matrix.det_mul]
      show (∏ τ, (fr y₂ τ).det ^ sS τ)⁻¹ * frPolyG fr Q y₂ = _ * ((∏ τ, (fr y τ).det ^ sS τ)⁻¹ * frPolyG fr Q y)
      rw [e1, inv_mul_eq_iff_eq_mul₀ (hP y₂), e3, ← mul_assoc, ← mul_assoc, e2, mul_assoc (∏ τ, ∏ r, β τ r r ^ ν τ r), mul_assoc,
        mul_inv_cancel₀ (hP y), one_mul]
    · funext y
      show _ = (∏ τ, (fr y τ).det ^ sS τ) * ((∏ τ, (fr y τ).det ^ sS τ)⁻¹ * frPolyG fr Q y)
      rw [mul_inv_cancel_left₀ (hP y)]
  · rintro ⟨⟨f, ⟨-, hw⟩, hF⟩, Q, hQ⟩
    refine ⟨Q, fun β hβ => hinj ?_, hQ⟩
    funext y
    obtain ⟨y₂, h2⟩ := (hr fun τ => fr y τ * β τ).2 fun τ => by
      rw [Matrix.det_mul, det_bor hβ]
      exact mul_ne_zero (hdet y τ) (Finset.prod_ne_zero_iff.2 fun r _ => (hβ τ).2 r)
    have h2' : ∀ τ, fr y₂ τ = fr y τ * β τ := fun τ => congrFun h2 τ
    have e0 : ∀ y, frPolyG fr Q y = (∏ τ, (fr y τ).det ^ sS τ) * f y := fun y => by rw [← hQ, hF]; rfl
    have e1 : frPolyG fr (colSub β Q) y = frPolyG fr Q y₂ := by
      rw [frPolyG_colSub]
      show _ = eval (fun k : ι × Fin a × Fin a => fr y₂ k.1 k.2.1 k.2.2) Q
      simp only [h2']
    have e2 := bor_id hβ (fun τ => (fr y τ).det) lam sS ν hν
    have e3 : (∏ τ, (fr y₂ τ).det ^ sS τ) = ∏ τ, ((fr y τ).det * (β τ).det) ^ sS τ :=
      Finset.prod_congr rfl fun τ _ => by rw [h2', Matrix.det_mul]
    rw [e1, map_smul, Pi.smul_apply, smul_eq_mul, e0, e0, hw y y₂ β hβ h2', e3, ← mul_assoc, e2, mul_assoc]

end UnfG

section VVWt

open MvPolynomial Formalism.L2.DIV Formalism.GradedWeylDivisibility

variable {K : Type} [Field K] {r n : ℕ}

def colSub1 (β : Matrix (Fin n) (Fin n) K) : MvPolynomial (Fin r × Fin n) K →ₐ[K] MvPolynomial (Fin r × Fin n) K :=
  aeval fun v => ∑ w : Fin n, C (β w v.2) * X (v.1, w)

def colSc (t : Fin n) (d : K) : MvPolynomial (Fin r × Fin n) K →ₐ[K] MvPolynomial (Fin r × Fin n) K :=
  aeval fun v => C (if v.2 = t then d else 1) * X v

def colAddS (t : Fin n) (S : Finset (Fin n)) (c : Fin n → K) : MvPolynomial (Fin r × Fin n) K →ₐ[K] MvPolynomial (Fin r × Fin n) K :=
  aeval fun v => if v.2 = t then X v + ∑ l ∈ S, C (c l) * X (v.1, l) else X v

/- English proof (translation)
Establish `hk` using `(lsat_mem_dualWeyl.1 hF).2 l j h`. Establish `h1` using `congrArg (fun g => g F) (lsat_spec_colAddGen (r := r) l j c)`. Establish `h2` using `congrArg (fun g => g F) (lsat_spec_rename (r := r) (n := n) c)`. Simplify using `only [AlgHom.coe_comp, Function.comp_apply, AlgHom.id_apply] at h1 h2`. Rewrite using `[← h1, hk, h2]`.
-/
theorem colAdd_inv {ν : Fin n → ℕ} {F : MvPolynomial (Fin r × Fin n) K} (hF : F ∈ dualWeyl K r n ν) (l j : Fin n) (h : l < j) (c : K) :
    colAdd K l j c F = F := by
  have hk := (lsat_mem_dualWeyl.1 hF).2 l j h
  have h1 := congrArg (fun g => g F) (lsat_spec_colAddGen (r := r) l j c)
  have h2 := congrArg (fun g => g F) (lsat_spec_rename (r := r) (n := n) c)
  simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.id_apply] at h1 h2
  rw [← h1, hk, h2]

/- English proof (translation)
Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `only [colAddS, colAdd, AlgHom.comp_apply, aeval_X]`. Use `split_ifs with h`. Rewrite using `[map_add, map_mul, aeval_X, aeval_X, algHom_C, if_pos h, if_neg hl, Finset.sum_insert hS]`.

Simplify using `only [algebraMap_eq]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[aeval_X, if_neg h]`.
-/
theorem colAddS_insert (t l : Fin n) (hl : l ≠ t) (S : Finset (Fin n)) (hS : l ∉ S) (c : Fin n → K) :
    (colAddS (r := r) t (insert l S) c) = (colAddS t S c).comp (colAdd K l t (c l)) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [colAddS, colAdd, AlgHom.comp_apply, aeval_X]
  split_ifs with h
  · rw [map_add, map_mul, aeval_X, aeval_X, algHom_C, if_pos h, if_neg hl, Finset.sum_insert hS]
    simp only [algebraMap_eq]
    ring
  · rw [aeval_X, if_neg h]

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty`. Establish `: colAddS (r` using `r) t ∅ c = AlgHom.id K _ := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`.

Simplify using `[colAddS]`. Rewrite using `[this]`. Both sides reduce to the same expression. Consider the case `insert l S hl ih`. Rewrite using `[colAddS_insert t l (hS l (Finset.mem_insert_self _ _)).ne S hl c, AlgHom.comp_apply, colAdd_inv hF l t (hS l (Finset.mem_insert_self _ _)), ih fun x hx => hS x (Finset.mem_insert_of_mem hx)]`.
-/
theorem colAddS_inv {ν : Fin n → ℕ} {F : MvPolynomial (Fin r × Fin n) K} (hF : F ∈ dualWeyl K r n ν) (t : Fin n) (c : Fin n → K)
    (S : Finset (Fin n)) (hS : ∀ l ∈ S, l < t) : colAddS t S c F = F := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have : colAddS (r := r) t ∅ c = AlgHom.id K _ := by
      apply MvPolynomial.algHom_ext
      intro v
      simp [colAddS]
    rw [this]; rfl
  | insert l S hl ih =>
    rw [colAddS_insert t l (hS l (Finset.mem_insert_self _ _)).ne S hl c, AlgHom.comp_apply,
      colAdd_inv hF l t (hS l (Finset.mem_insert_self _ _)), ih fun x hx => hS x (Finset.mem_insert_of_mem hx)]

/- English proof (translation)
Establish `h1 : colSc t d (monomial m c) = C c * m.prod fun v k => (C (if v.2 = t then d else 1) * X v : MvPolynomial (Fin r × Fin n) K) ^ k`. Rewrite using `[colSc, aeval_monomial]`. Both sides reduce to the same expression. Establish `h2 : (m.prod fun v k => (C (if v.2 = t then d else 1) * X v : MvPolynomial (Fin r × Fin n) K) ^ k) = C (m.prod fun v k => (if v.2 = t then d else 1) ^ k) * m.prod fun v k => X v ^ k`. Simplify using `only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_prod, C_pow]`.

Establish `h3 : (m.prod fun v k => (if v.2 = t then d else (1 : K)) ^ k) = d ^ (∑ a : Fin r, m (a, t))`. Rewrite using `[Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type, ← Finset.prod_pow_eq_pow_sum]`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_eq_single t]`. Simplify using the standard rewrite rules.

Introduce `s _ hs`. Simplify using `[hs]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Rewrite using `[h1, h2, h3, monomial_eq, smul_eq_C_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem colSc_monomial (t : Fin n) (d : K) (m : Fin r × Fin n →₀ ℕ) (c : K) :
    colSc t d (monomial m c) = (d ^ (∑ a : Fin r, m (a, t))) • monomial m c := by
  classical
  have h1 : colSc t d (monomial m c) = C c * m.prod fun v k => (C (if v.2 = t then d else 1) * X v : MvPolynomial (Fin r × Fin n) K) ^ k := by
    rw [colSc, aeval_monomial]; rfl
  have h2 : (m.prod fun v k => (C (if v.2 = t then d else 1) * X v : MvPolynomial (Fin r × Fin n) K) ^ k) =
      C (m.prod fun v k => (if v.2 = t then d else 1) ^ k) * m.prod fun v k => X v ^ k := by
    simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_prod, C_pow]
  have h3 : (m.prod fun v k => (if v.2 = t then d else (1 : K)) ^ k) = d ^ (∑ a : Fin r, m (a, t)) := by
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [Finset.prod_eq_single t]
    · simp
    · intro s _ hs
      simp [hs]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h1, h2, h3, monomial_eq, smul_eq_C_mul]
  ring

/- English proof (translation)
Use `conv_lhs => rw [F.as_sum]`. Use `conv_rhs => rw [F.as_sum]`. Rewrite using `[map_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Rewrite using `[colSc_monomial]`.

Use `congr 2`. Establish `h` using `hF (mem_support_iff.1 hm)`. Establish `h2` using `congrFun h t`. Rewrite using `[← h2, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun i => zero_smul ℕ (colW r n i)), Finset.sum_apply, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_eq_single t]`. Simplify using `[colW]`. Introduce `s _ hs`. Simplify using `[colW, hs]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem colSc_hom {ν : Fin n → ℕ} {F : MvPolynomial (Fin r × Fin n) K} (hF : IsWeightedHomogeneous (colW r n) F ν) (t : Fin n) (d : K) :
    colSc t d F = (d ^ ν t) • F := by
  classical
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [colSc_monomial]
  congr 2
  have h := hF (mem_support_iff.1 hm)
  have h2 := congrFun h t
  rw [← h2, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun i => zero_smul ℕ (colW r n i)), Finset.sum_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single t]
  · simp [colW]
  · intro s _ hs
    simp [colW, hs]
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Rewrite using `[← Finset.sum_filter_add_sum_filter_not Finset.univ (· < t), add_comm]`. Use `congr 1`. Rewrite using `[Finset.sum_eq_single t]`. Introduce `w hw hne`. Establish `h1 : ¬ w < t` using `(Finset.mem_filter.1 hw).2`.

Conclude with `h w (lt_of_le_of_ne (not_lt.1 h1) (Ne.symm hne))`. Introduce `h1`. Conclude with `(h1 (by simp)).elim`.
-/
theorem sum_split (t : Fin n) {M : Type} [AddCommMonoid M] (f : Fin n → M) (h : ∀ w, t < w → f w = 0) :
    ∑ w, f w = f t + ∑ l ∈ Finset.univ.filter (· < t), f l := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· < t), add_comm]
  congr 1
  rw [Finset.sum_eq_single t]
  · intro w hw hne
    have h1 : ¬ w < t := (Finset.mem_filter.1 hw).2
    exact h w (lt_of_le_of_ne (not_lt.1 h1) (Ne.symm hne))
  · intro h1
    exact (h1 (by simp)).elim

def colOne (β : Matrix (Fin n) (Fin n) K) (t : Fin n) : MvPolynomial (Fin r × Fin n) K →ₐ[K] MvPolynomial (Fin r × Fin n) K :=
  aeval fun v => if v.2 = t then ∑ w : Fin n, C (β w t) * X (v.1, w) else X v

/- English proof (translation)
Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `only [colOne, colSc, colAddS, AlgHom.comp_apply, aeval_X]`. Use `split_ifs with h`. Rewrite using `[sum_split t _ fun w hw => by rw [hβ w t hw, C_0, zero_mul]]`.

Rewrite using `[map_add, aeval_X, if_pos h, map_sum]`. Use `congr 1`. Take `⟨a, s⟩` from `v`. Simplify using `only at h`. Substitute `h` using the available equality.

Both sides reduce to the same expression. Use `Finset.sum_congr rfl fun l hl => ?_` and prove the remaining obligations. Rewrite using `[map_mul, aeval_X, algHom_C, if_neg (Finset.mem_filter.1 hl).2.ne, C_1, one_mul]`. Both sides reduce to the same expression. Rewrite using `[aeval_X, if_neg h, C_1, one_mul]`.
-/
theorem colOne_eq (β : Matrix (Fin n) (Fin n) K) (hβ : ∀ w s, s < w → β w s = 0) (t : Fin n) :
    colOne (r := r) β t = (colSc t (β t t)).comp (colAddS t (Finset.univ.filter (· < t)) fun l => β l t) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [colOne, colSc, colAddS, AlgHom.comp_apply, aeval_X]
  split_ifs with h
  · rw [sum_split t _ fun w hw => by rw [hβ w t hw, C_0, zero_mul]]
    rw [map_add, aeval_X, if_pos h, map_sum]
    congr 1
    · obtain ⟨a, s⟩ := v
      simp only at h
      subst h
      rfl
    · refine Finset.sum_congr rfl fun l hl => ?_
      rw [map_mul, aeval_X, algHom_C, if_neg (Finset.mem_filter.1 hl).2.ne, C_1, one_mul]
      rfl
  · rw [aeval_X, if_neg h, C_1, one_mul]

/- English proof (translation)
Rewrite using `[colOne_eq β hβ, AlgHom.comp_apply, colAddS_inv hF t _ _ (fun l hl => (Finset.mem_filter.1 hl).2), colSc_hom (lsat_mem_dualWeyl.1 hF).1]`.
-/
theorem colOne_good {ν : Fin n → ℕ} {F : MvPolynomial (Fin r × Fin n) K} (hF : F ∈ dualWeyl K r n ν) (β : Matrix (Fin n) (Fin n) K)
    (hβ : ∀ w s, s < w → β w s = 0) (t : Fin n) : colOne β t F = (β t t ^ ν t) • F := by
  rw [colOne_eq β hβ, AlgHom.comp_apply, colAddS_inv hF t _ _ (fun l hl => (Finset.mem_filter.1 hl).2), colSc_hom (lsat_mem_dualWeyl.1 hF).1]

open Classical in

def cutCol (β : Matrix (Fin n) (Fin n) K) (t : Fin n) : Matrix (Fin n) (Fin n) K :=
  fun w s => if s = t then (if w = t then 1 else 0) else β w s

/- English proof (translation)
Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `⟨a, s⟩`. Simplify using `only [colSub1, colOne, AlgHom.comp_apply, aeval_X]`. Use `split_ifs with h`. Substitute `h` using the available equality.

Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, algHom_C, aeval_X]`. Distinguish the cases in `hw : s < w`. Simplify using `[hβ w s hw]`.

Establish `hc : ∀ x, cutCol β s x w = if x = w then 1 else 0`. Introduce `x`. Unfold `cutCol`. Distinguish the cases in `h1 : w = s`. Substitute `h1` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[if_neg h1]`. Conclude with `hid w (lt_of_le_of_ne (not_lt.1 hw) h1) x`. Simplify using `only [hc]`. Rewrite using `[Finset.sum_eq_single w]`.

Simplify using the standard rewrite rules. Introduce `x _ hx`. Simplify using `[hx]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.

Rewrite using `[aeval_X]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Simplify using `[cutCol, h]`.
-/
theorem colSub1_cut (β : Matrix (Fin n) (Fin n) K) (t : Fin n) (hid : ∀ s, s < t → ∀ w, β w s = if w = s then 1 else 0)
    (hβ : ∀ w s, s < w → β w s = 0) : colSub1 (r := r) β = (colSub1 (cutCol β t)).comp (colOne β t) := by
  classical
  apply MvPolynomial.algHom_ext
  rintro ⟨a, s⟩
  simp only [colSub1, colOne, AlgHom.comp_apply, aeval_X]
  split_ifs with h
  · subst h
    rw [map_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [map_mul, algHom_C, aeval_X]
    by_cases hw : s < w
    · simp [hβ w s hw]
    · have hc : ∀ x, cutCol β s x w = if x = w then 1 else 0 := by
        intro x
        unfold cutCol
        by_cases h1 : w = s
        · subst h1; simp
        · rw [if_neg h1]
          exact hid w (lt_of_le_of_ne (not_lt.1 hw) h1) x
      simp only [hc]
      rw [Finset.sum_eq_single w]
      · simp
      · intro x _ hx
        simp [hx]
      · intro h; exact absurd (Finset.mem_univ _) h
  · rw [aeval_X]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp [cutCol, h]

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `t ht β _ hid`. Establish `h1 : ∀ s w : Fin n, β w s = if w = s then 1 else 0` using `fun s w => hid s (by omega) w`.

Establish `h2 : colSub1 (r` using `r) β = AlgHom.id K _ := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `⟨a, s⟩`. Simplify using `only [colSub1, aeval_X, h1, AlgHom.id_apply]`. Rewrite using `[Finset.sum_eq_single s]`.

Simplify using the standard rewrite rules. Introduce `x _ hx`. Simplify using `[hx]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.

Rewrite using `[h2, AlgHom.id_apply, Finset.prod_eq_one (fun x _ => by rw [h1, if_pos rfl, one_pow]), one_smul]`. Consider the case `succ k ih`. Introduce `t ht β hβ hid`. Establish `htn : t < n` using `by omega`. Use `set tt : Fin n := ⟨t, htn⟩ with htt`.

Establish `hu : ∀ w s, s < w → cutCol β tt w s = 0`. Introduce `w s hsw`. Unfold `cutCol`. Distinguish the cases in `h1 : s = tt`. Rewrite using `[if_pos h1, if_neg (by rw [← h1]; exact hsw.ne')]`.

Rewrite using `[if_neg h1]`. Conclude with `hβ w s hsw`. Establish `hi : ∀ s : Fin n, s.1 < t + 1 → ∀ w, cutCol β tt w s = if w = s then 1 else 0`. Introduce `s hs w`. Unfold `cutCol`.

Distinguish the cases in `h1 : s = tt`. Rewrite using `[if_pos h1, h1]`. Rewrite using `[if_neg h1]`. Use `hid s ?_ w` and prove the remaining obligations. Establish `: s.1 ≠ t` using `fun h => h1 (Fin.ext h)`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[colSub1_cut β tt (fun s hs => hid s hs) hβ, AlgHom.comp_apply, colOne_good hF β hβ tt, map_smul, ih (t + 1) (by omega) (cutCol β tt) hu hi, smul_smul]`. Use `congr 1`. Rewrite using `[← Finset.mul_prod_erase Finset.univ (fun x => cutCol β tt x x ^ ν x) (Finset.mem_univ tt), ← Finset.mul_prod_erase Finset.univ (fun x => β x x ^ ν x) (Finset.mem_univ tt)]`. Establish `e1 : cutCol β tt tt tt = 1` using `by simp [cutCol]`.

Rewrite using `[e1, one_pow, one_mul]`. Use `congr 1`. Use `Finset.prod_congr rfl fun x hx => ?_` and prove the remaining obligations. Establish `: x ≠ tt` using `(Finset.mem_erase.1 hx).1`. Simplify using `[cutCol, this]`.
-/
theorem colSub1_good {ν : Fin n → ℕ} {F : MvPolynomial (Fin r × Fin n) K} (hF : F ∈ dualWeyl K r n ν) :
    ∀ (k t : ℕ), t + k = n → ∀ β : Matrix (Fin n) (Fin n) K, (∀ w s, s < w → β w s = 0) →
      (∀ s : Fin n, s.1 < t → ∀ w, β w s = if w = s then 1 else 0) → colSub1 β F = (∏ x, β x x ^ ν x) • F := by
  classical
  intro k
  induction k with
  | zero =>
    intro t ht β _ hid
    have h1 : ∀ s w : Fin n, β w s = if w = s then 1 else 0 := fun s w => hid s (by omega) w
    have h2 : colSub1 (r := r) β = AlgHom.id K _ := by
      apply MvPolynomial.algHom_ext
      rintro ⟨a, s⟩
      simp only [colSub1, aeval_X, h1, AlgHom.id_apply]
      rw [Finset.sum_eq_single s]
      · simp
      · intro x _ hx
        simp [hx]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [h2, AlgHom.id_apply, Finset.prod_eq_one (fun x _ => by rw [h1, if_pos rfl, one_pow]), one_smul]
  | succ k ih =>
    intro t ht β hβ hid
    have htn : t < n := by omega
    set tt : Fin n := ⟨t, htn⟩ with htt
    have hu : ∀ w s, s < w → cutCol β tt w s = 0 := by
      intro w s hsw
      unfold cutCol
      by_cases h1 : s = tt
      · rw [if_pos h1, if_neg (by rw [← h1]; exact hsw.ne')]
      · rw [if_neg h1]; exact hβ w s hsw
    have hi : ∀ s : Fin n, s.1 < t + 1 → ∀ w, cutCol β tt w s = if w = s then 1 else 0 := by
      intro s hs w
      unfold cutCol
      by_cases h1 : s = tt
      · rw [if_pos h1, h1]
      · rw [if_neg h1]
        refine hid s ?_ w
        have : s.1 ≠ t := fun h => h1 (Fin.ext h)
        omega
    rw [colSub1_cut β tt (fun s hs => hid s hs) hβ, AlgHom.comp_apply, colOne_good hF β hβ tt, map_smul,
      ih (t + 1) (by omega) (cutCol β tt) hu hi, smul_smul]
    congr 1
    rw [← Finset.mul_prod_erase Finset.univ (fun x => cutCol β tt x x ^ ν x) (Finset.mem_univ tt),
      ← Finset.mul_prod_erase Finset.univ (fun x => β x x ^ ν x) (Finset.mem_univ tt)]
    have e1 : cutCol β tt tt tt = 1 := by simp [cutCol]
    rw [e1, one_pow, one_mul]
    congr 1
    refine Finset.prod_congr rfl fun x hx => ?_
    have : x ≠ tt := (Finset.mem_erase.1 hx).1
    simp [cutCol, this]

/- English proof (translation)
The claim follows from `colSub1_good hF n 0 (by omega) β hβ fun s hs => absurd hs (Nat.not_lt_zero _)`.
-/
theorem dualWeyl_bor {ν : Fin n → ℕ} {F : MvPolynomial (Fin r × Fin n) K} (hF : F ∈ dualWeyl K r n ν) (β : Matrix (Fin n) (Fin n) K)
    (hβ : ∀ w s, s < w → β w s = 0) : colSub1 β F = (∏ x, β x x ^ ν x) • F :=
  colSub1_good hF n 0 (by omega) β hβ fun s hs => absurd hs (Nat.not_lt_zero _)

variable {ι : Type} [Fintype ι]

/- English proof (translation)
Establish `e : (colSub β).comp (blockEmb K τ) = (blockEmb K τ).comp (colSub1 (β τ))`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `⟨a, s⟩`. Simplify using `[colSub, blockEmb, colSub1]`. Conclude with `DFunLike.congr_fun e F`.
-/
theorem colSub_blockEmb (β : ι → Matrix (Fin n) (Fin n) K) (τ : ι) (F : MvPolynomial (Fin n × Fin n) K) :
    colSub β (blockEmb K τ F) = blockEmb K τ (colSub1 (β τ) F) := by
  have e : (colSub β).comp (blockEmb K τ) = (blockEmb K τ).comp (colSub1 (β τ)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    simp [colSub, blockEmb, colSub1]
  exact DFunLike.congr_fun e F

/- English proof (translation)
Unfold `DIV.VV tensorLat`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `P ⟨F, hF, rfl⟩ β hβ`. Rewrite using `[map_prod]`. Simplify using `only [colSub_blockEmb]`.

Establish `h : ∀ τ, blockEmb K τ (colSub1 (β τ) (F τ)) = (∏ x, β τ x x ^ (lam τ).natW x) • blockEmb K τ (F τ)`. Introduce `τ`. Rewrite using `[dualWeyl_bor (hF τ) (β τ) (hβ τ).1, map_smul]`. Simplify using `only [h]`. Rewrite using `[Finset.prod_smul]`.
-/
theorem VV_le_WtPol (lam : ι → DomWeight n) : DIV.VV K lam ≤ WtPol K fun τ r => (lam τ).natW r := by
  unfold DIV.VV tensorLat
  rw [Submodule.span_le]
  rintro P ⟨F, hF, rfl⟩ β hβ
  rw [map_prod]
  simp only [colSub_blockEmb]
  have h : ∀ τ, blockEmb K τ (colSub1 (β τ) (F τ)) = (∏ x, β τ x x ^ (lam τ).natW x) • blockEmb K τ (F τ) := by
    intro τ
    rw [dualWeyl_bor (hF τ) (β τ) (hβ τ).1, map_smul]
  simp only [h]
  rw [Finset.prod_smul]

/- English proof (translation)
Unfold `frDet`. Rewrite using `[AlgHom.map_det]`. Establish `e : (colSub β).mapMatrix (Matrix.of fun α s : Fin n => (X (τ, α, s) : Pol K ι n)) = (Matrix.of fun α s : Fin n => (X (τ, α, s) : Pol K ι n)) * (β τ).map C`. Use `Matrix.ext fun α s => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply]`.

Use `show colSub β (X (τ, α, s) : Pol K ι n) = ∑ x : Fin n, (X (τ, α, x) : Pol K ι n) * C (β τ x s)`. Simplify using `only [colSub, aeval_X]`. Conclude with `Finset.sum_congr rfl fun x _ => mul_comm (C (β τ x s)) (X (τ, α, x) : Pol K ι n)`. Rewrite using `[e, Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_of_isUpperTriangular (fun x s h => (hβ τ).1 x s h), smul_eq_C_mul, mul_comm]`.
-/
theorem colSub_frDet (β : ι → Matrix (Fin n) (Fin n) K) (hβ : IsBor β) (τ : ι) :
    colSub β (frDet K n τ) = (∏ x, β τ x x) • frDet K n τ := by
  unfold frDet
  rw [AlgHom.map_det]
  have e : (colSub β).mapMatrix (Matrix.of fun α s : Fin n => (X (τ, α, s) : Pol K ι n)) =
      (Matrix.of fun α s : Fin n => (X (τ, α, s) : Pol K ι n)) * (β τ).map C := by
    refine Matrix.ext fun α s => ?_
    rw [Matrix.mul_apply]
    show colSub β (X (τ, α, s) : Pol K ι n) = ∑ x : Fin n, (X (τ, α, x) : Pol K ι n) * C (β τ x s)
    simp only [colSub, aeval_X]
    exact Finset.sum_congr rfl fun x _ => mul_comm (C (β τ x s)) (X (τ, α, x) : Pol K ι n)
  rw [e, Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_of_isUpperTriangular (fun x s h => (hβ τ).1 x s h),
    smul_eq_C_mul, mul_comm]

/- English proof (translation)
Introduce `K _ ι _ n lam k P hP β hβ`. Rewrite using `[map_mul, VV_le_WtPol lam hP β hβ, map_prod]`. Simplify using `only [map_pow, colSub_frDet β hβ, smul_pow]`. Rewrite using `[Finset.prod_smul, smul_mul_smul_comm]`. Use `congr 1`.

Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_pow, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun x _ => (pow_add _ _ _).symm`.
-/
theorem vv_in_weight : VVInWt := by
  intro K _ ι _ n lam k P hP β hβ
  rw [map_mul, VV_le_WtPol lam hP β hβ, map_prod]
  simp only [map_pow, colSub_frDet β hβ, smul_pow]
  rw [Finset.prod_smul, smul_mul_smul_comm]
  congr 1
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun x _ => (pow_add _ _ _).symm

end VVWt

section WtVVA

open MvPolynomial Formalism.L2.DIV Formalism.GradedWeylDivisibility

variable {K : Type} [Field K] {r n : ℕ}

/- English proof (translation)
Proceed by induction on `F using MvPolynomial.induction_on' with`. Consider the case `monomial m' c`. Rewrite using `[colSc_monomial, coeff_smul, coeff_monomial, smul_eq_mul]`. Use `split_ifs with h`. Rewrite using `[h]`.

Simplify using the standard rewrite rules. Consider the case `add f g hf hg => rw [map_add, coeff_add, coeff_add, hf, hg, mul_add]`.
-/
theorem coeff_colSc (t : Fin n) (d : K) (F : MvPolynomial (Fin r × Fin n) K) (m : Fin r × Fin n →₀ ℕ) :
    coeff m (colSc t d F) = d ^ (∑ a : Fin r, m (a, t)) * coeff m F := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial m' c =>
    rw [colSc_monomial, coeff_smul, coeff_monomial, smul_eq_mul]
    split_ifs with h
    · rw [h]
    · simp
  | add f g hf hg => rw [map_add, coeff_add, coeff_add, hf, hg, mul_add]

/- English proof (translation)
Establish `h0 : (Polynomial.X ^ a - Polynomial.X ^ b : Polynomial K) = 0`. Apply `Polynomial.eq_zero_of_infinite_isRoot` to reduce the goal to its premises. Use `Set.Infinite.mono ?_ (Set.finite_singleton (0 : K)).infinite_compl` and prove the remaining obligations. Introduce `x hx`. Simplify using `only [Set.mem_ofPred_eq, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]`.

Rewrite using `[h x hx, sub_self]`. Establish `h1` using `congrArg Polynomial.natDegree (sub_eq_zero.1 h0)`. Simplify using `using h1`.
-/
theorem pow_inj_of_infinite [Infinite K] {a b : ℕ} (h : ∀ x : K, x ≠ 0 → x ^ a = x ^ b) : a = b := by
  have h0 : (Polynomial.X ^ a - Polynomial.X ^ b : Polynomial K) = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono ?_ (Set.finite_singleton (0 : K)).infinite_compl
    intro x hx
    simp only [Set.mem_ofPred_eq, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    rw [h x hx, sub_self]
  have h1 := congrArg Polynomial.natDegree (sub_eq_zero.1 h0)
  simpa using h1

/- English proof (translation)
Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `⟨a, s⟩`. Simplify using `only [colSub1, colSc, aeval_X]`. Rewrite using `[Finset.sum_eq_single s]`. Rewrite using `[Matrix.diagonal_apply_eq]`.

Introduce `w _ hw`. Rewrite using `[Matrix.diagonal_apply_ne _ hw, C_0, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem colSub1_diag (t : Fin n) (d : K) :
    colSub1 (r := r) (Matrix.diagonal fun s => if s = t then d else 1) = colSc t d := by
  classical
  apply MvPolynomial.algHom_ext
  rintro ⟨a, s⟩
  simp only [colSub1, colSc, aeval_X]
  rw [Finset.sum_eq_single s]
  · rw [Matrix.diagonal_apply_eq]
  · intro w _ hw
    rw [Matrix.diagonal_apply_ne _ hw, C_0, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `⟨a, s⟩`. Simplify using `only [colSub1, colAdd, aeval_X]`. Establish `e : ∀ w : Fin n, (C (if w = s then (1 : K) else if w = l ∧ s = j then c else 0) * X (a, w) : MvPolynomial (Fin r × Fin n) K) = (if w = s then X (a, w) else 0) + (if w = l then (if s = j then C c * X (a, w) else 0) else 0)`. Introduce `w`.

Distinguish the cases in `h1 : w = s`. Distinguish the cases in `h2 : w = l`. Establish `h3 : s ≠ j` using `fun h => hlj (h2.symm.trans (h1.trans h))`. Simplify using `[h1, h3]`. Establish `h2' : s ≠ l` using `fun h => h2 (h1.trans h)`.

Simplify using `[h1, h2']`. Distinguish the cases in `h2 : w = l`. Apply the tactic sequence `by_cases h3 : s = j <;> simp [h1, h2, h3, hlj]`. Simplify using `[h1, h2]`. Simplify using `only [e, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.

Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem colSub1_trans (l j : Fin n) (hlj : l ≠ j) (c : K) :
    colSub1 (r := r) (fun w s => if w = s then 1 else if w = l ∧ s = j then c else 0) = colAdd K l j c := by
  classical
  apply MvPolynomial.algHom_ext
  rintro ⟨a, s⟩
  simp only [colSub1, colAdd, aeval_X]
  have e : ∀ w : Fin n, (C (if w = s then (1 : K) else if w = l ∧ s = j then c else 0) * X (a, w) : MvPolynomial (Fin r × Fin n) K) =
      (if w = s then X (a, w) else 0) + (if w = l then (if s = j then C c * X (a, w) else 0) else 0) := by
    intro w
    by_cases h1 : w = s
    · by_cases h2 : w = l
      · have h3 : s ≠ j := fun h => hlj (h2.symm.trans (h1.trans h))
        simp [h1, h3]
      · have h2' : s ≠ l := fun h => h2 (h1.trans h)
        simp [h1, h2']
    · by_cases h2 : w = l
      · by_cases h3 : s = j <;> simp [h1, h2, h3, hlj]
      · simp [h1, h2]
  simp only [e, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  split_ifs <;> simp

/- English proof (translation)
Use `(dualWeylModuleMemIff K r n ν F).2 ⟨?_, ?_⟩` and prove the remaining obligations. Introduce `m hm`. Use function extensionality and compare the values at `t`. Establish `h1 : ∀ x : K, x ≠ 0 → x ^ (∑ a : Fin r, m (a, t)) = x ^ ν t`. Introduce `x hx`.

Establish `h2` using `h (Matrix.diagonal fun s => if s = t then x else 1) (fun w s hws => Matrix.diagonal_apply_ne _ hws.ne') (fun w => by rw [Matrix.diagonal_apply_eq]; split_ifs; exacts [hx, one_ne_zero])`. Rewrite `h2` using `[colSub1_diag]`. Establish `h3` using `congrArg (coeff m) h2`. Rewrite `h3` using `[coeff_colSc, coeff_smul, smul_eq_mul]`. Establish `h4 : (∏ y, (Matrix.diagonal (fun s => if s = t then x else 1) : Matrix (Fin n) (Fin n) K) y y ^ ν y) = x ^ ν t`.

Rewrite using `[Finset.prod_eq_single t]`. Rewrite using `[Matrix.diagonal_apply_eq, if_pos rfl]`. Introduce `y _ hy`. Rewrite using `[Matrix.diagonal_apply_eq, if_neg hy, one_pow]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`. Rewrite `h3` using `[h4]`. Conclude with `mul_right_cancel₀ hm h3`. Rewrite using `[← pow_inj_of_infinite h1, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun i => zero_smul ℕ (colW r n i)), Finset.sum_apply, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_eq_single t]`. Simplify using `[colW]`. Introduce `s _ hs`. Simplify using `[colW, hs]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`. Introduce `l j hlj c`. Establish `h2` using `h (fun w s => if w = s then 1 else if w = l ∧ s = j then c else 0) (fun w s hws => by`. Rewrite using `[if_neg hws.ne', if_neg]`. Introduce and unpack `⟨rfl, rfl⟩`.

Conclude with `absurd hlj (not_lt.2 hws.le))`. Use the proof step `(fun w => by simp)`. Rewrite `h2` using `[colSub1_trans l j hlj.ne]`. Rewrite using `[h2]`. Simplify using the standard rewrite rules.
-/
theorem mem_dualWeyl_of_bor [Infinite K] {ν : Fin n → ℕ} {F : MvPolynomial (Fin r × Fin n) K}
    (h : ∀ β : Matrix (Fin n) (Fin n) K, (∀ w s, s < w → β w s = 0) → (∀ w, β w w ≠ 0) → colSub1 β F = (∏ x, β x x ^ ν x) • F) :
    F ∈ dualWeyl K r n ν := by
  classical
  refine (dualWeylModuleMemIff K r n ν F).2 ⟨?_, ?_⟩
  · intro m hm
    funext t
    have h1 : ∀ x : K, x ≠ 0 → x ^ (∑ a : Fin r, m (a, t)) = x ^ ν t := by
      intro x hx
      have h2 := h (Matrix.diagonal fun s => if s = t then x else 1) (fun w s hws => Matrix.diagonal_apply_ne _ hws.ne')
        (fun w => by rw [Matrix.diagonal_apply_eq]; split_ifs; exacts [hx, one_ne_zero])
      rw [colSub1_diag] at h2
      have h3 := congrArg (coeff m) h2
      rw [coeff_colSc, coeff_smul, smul_eq_mul] at h3
      have h4 : (∏ y, (Matrix.diagonal (fun s => if s = t then x else 1) : Matrix (Fin n) (Fin n) K) y y ^ ν y) = x ^ ν t := by
        rw [Finset.prod_eq_single t]
        · rw [Matrix.diagonal_apply_eq, if_pos rfl]
        · intro y _ hy
          rw [Matrix.diagonal_apply_eq, if_neg hy, one_pow]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [h4] at h3
      exact mul_right_cancel₀ hm h3
    rw [← pow_inj_of_infinite h1, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun i => zero_smul ℕ (colW r n i)), Finset.sum_apply,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single t]
    · simp [colW]
    · intro s _ hs
      simp [colW, hs]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro l j hlj c
    have h2 := h (fun w s => if w = s then 1 else if w = l ∧ s = j then c else 0)
      (fun w s hws => by
        rw [if_neg hws.ne', if_neg]
        rintro ⟨rfl, rfl⟩
        exact absurd hlj (not_lt.2 hws.le))
      (fun w => by simp)
    rw [colSub1_trans l j hlj.ne] at h2
    rw [h2]
    simp

end WtVVA

section WtVVB

open MvPolynomial Formalism.L2.DIV Formalism.GradedWeylDivisibility

variable {K : Type} [Field K] {n : ℕ} {ι : Type}

abbrev Off (ι : Type) (n : ℕ) (τ : ι) : Type := {v : ι × Fin n × Fin n // v.1 ≠ τ}

open Classical in

def psi (τ : ι) : Pol K ι n →ₐ[K] MvPolynomial (Off ι n τ) (MvPolynomial (Fin n × Fin n) K) :=
  aeval fun v => if h : v.1 = τ then C (X v.2) else X ⟨v, h⟩

def psi' (τ : ι) : MvPolynomial (Off ι n τ) (MvPolynomial (Fin n × Fin n) K) →+* Pol K ι n :=
  eval₂Hom (blockEmb K τ).toRingHom fun w => X w.1

/- English proof (translation)
Establish `e : (psi' (K` using `K) (n := n) τ).comp (psi τ).toRingHom = RingHom.id _ := by`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `c`. Simplify using `[psi, psi', blockEmb, MvPolynomial.algebraMap_apply]`. Introduce and unpack `⟨t, v⟩`.

Distinguish the cases in `h : t = τ`. Substitute `h` using the available equality. Simplify using `[psi, psi', blockEmb]`. Simplify using `[psi, psi', h]`. Conclude with `RingHom.congr_fun e Q`.
-/
theorem psi'_psi (τ : ι) (Q : Pol K ι n) : psi' τ (psi τ Q) = Q := by
  have e : (psi' (K := K) (n := n) τ).comp (psi τ).toRingHom = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [psi, psi', blockEmb, MvPolynomial.algebraMap_apply]
    · rintro ⟨t, v⟩
      by_cases h : t = τ
      · subst h
        simp [psi, psi', blockEmb]
      · simp [psi, psi', h]
  exact RingHom.congr_fun e Q

/- English proof (translation)
Proceed by induction on `G using MvPolynomial.induction_on with`. Consider the case `C a => simp [blockEmb, MvPolynomial.algebraMap_apply]`. Consider the case `add p q hp hq => rw [map_add, map_add, hp, hq, map_add]`. Consider the case `mul_X p v hp`. Rewrite using `[map_mul, map_mul, hp, map_mul]`.

Simplify using `[blockEmb, psi]`.
-/
theorem psi_blockEmb (τ : ι) (G : MvPolynomial (Fin n × Fin n) K) : psi τ (blockEmb K τ G) = C G := by
  induction G using MvPolynomial.induction_on with
  | C a => simp [blockEmb, MvPolynomial.algebraMap_apply]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p v hp =>
    rw [map_mul, map_mul, hp, map_mul]
    simp [blockEmb, psi]

/- English proof (translation)
Establish `e : (psi (K` using `K) (n := n) τ).toRingHom.comp (psi' τ) = RingHom.id _ := by`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `G`. Simplify using `only [RingHom.comp_apply, psi', coe_eval₂Hom, eval₂_C, RingHom.id_apply]`. Conclude with `psi_blockEmb τ G`.

Introduce `w`. Simplify using `[psi, psi', w.2]`. Conclude with `RingHom.congr_fun e p`.
-/
theorem psi_psi' (τ : ι) (p : MvPolynomial (Off ι n τ) (MvPolynomial (Fin n × Fin n) K)) : psi τ (psi' τ p) = p := by
  have e : (psi (K := K) (n := n) τ).toRingHom.comp (psi' τ) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro G
      simp only [RingHom.comp_apply, psi', coe_eval₂Hom, eval₂_C, RingHom.id_apply]
      exact psi_blockEmb τ G
    · intro w
      simp [psi, psi', w.2]
  exact RingHom.congr_fun e p

open Classical in
/- English proof (translation)
Establish `e : (psi (K` using `K) (n := n) τ).toRingHom.comp (colSub (Function.update (1 : ι → Matrix (Fin n) (Fin n) K) τ β)).toRingHom = (map (colSub1 β).toRingHom).comp (psi τ).toRingHom := by`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `c`. Simplify using `[MvPolynomial.algebraMap_apply]`. Introduce and unpack `⟨t, a, s⟩`.

Distinguish the cases in `h : t = τ`. Substitute `h` using the available equality. Simplify using `[psi, colSub, colSub1, MvPolynomial.algebraMap_apply]`. Simplify using `[psi, colSub, h, Matrix.one_apply]`. Conclude with `RingHom.congr_fun e Q`.
-/
theorem psi_colSub [Fintype ι] (τ : ι) (β : Matrix (Fin n) (Fin n) K) (Q : Pol K ι n) :
    psi τ (colSub (Function.update (1 : ι → Matrix (Fin n) (Fin n) K) τ β) Q) = map (colSub1 β).toRingHom (psi τ Q) := by
  have e : (psi (K := K) (n := n) τ).toRingHom.comp (colSub (Function.update (1 : ι → Matrix (Fin n) (Fin n) K) τ β)).toRingHom =
      (map (colSub1 β).toRingHom).comp (psi τ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [MvPolynomial.algebraMap_apply]
    · rintro ⟨t, a, s⟩
      by_cases h : t = τ
      · subst h
        simp [psi, colSub, colSub1, MvPolynomial.algebraMap_apply]
      · simp [psi, colSub, h, Matrix.one_apply]
  exact RingHom.congr_fun e Q

/- English proof (translation)
Apply `mem_dualWeyl_of_bor` to reduce the goal to its premises. Introduce `β h1 h2`. Establish `hB : IsBor (Function.update (1 : ι → Matrix (Fin n) (Fin n) K) τ β)`. Introduce `σ`. Distinguish the cases in `h : σ = τ`.

Substitute `h` using the available equality. Rewrite using `[Function.update_self]`. Conclude with `⟨h1, h2⟩`. Rewrite using `[Function.update_of_ne h]`. Conclude with `⟨fun w s hws => Matrix.one_apply_ne hws.ne', fun w => by simp⟩`.

Establish `h3` using `congrArg (fun x => coeff r (psi τ x)) (hQ _ hB)`. Simplify using `only [psi_colSub, coeff_map, map_smul, coeff_smul] at h3`. Establish `h4 : (∏ σ, ∏ x, (Function.update (1 : ι → Matrix (Fin n) (Fin n) K) τ β) σ x x ^ ν σ x) = ∏ x, β x x ^ ν τ x`. Rewrite using `[Finset.prod_eq_single τ]`. Rewrite using `[Function.update_self]`.

Introduce `σ _ hσ`. Rewrite using `[Function.update_of_ne hσ]`. Simplify using the standard rewrite rules. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.

Rewrite `h3` using `[h4]`. Conclude with `h3`.
-/
theorem coeff_psi_mem [Fintype ι] [Infinite K] {ν : ι → Fin n → ℕ} {Q : Pol K ι n} (hQ : Q ∈ WtPol K ν) (τ : ι) (r : Off ι n τ →₀ ℕ) :
    coeff r (psi τ Q) ∈ dualWeyl K n n (ν τ) := by
  classical
  apply mem_dualWeyl_of_bor
  intro β h1 h2
  have hB : IsBor (Function.update (1 : ι → Matrix (Fin n) (Fin n) K) τ β) := by
    intro σ
    by_cases h : σ = τ
    · subst h
      rw [Function.update_self]
      exact ⟨h1, h2⟩
    · rw [Function.update_of_ne h]
      exact ⟨fun w s hws => Matrix.one_apply_ne hws.ne', fun w => by simp⟩
  have h3 := congrArg (fun x => coeff r (psi τ x)) (hQ _ hB)
  simp only [psi_colSub, coeff_map, map_smul, coeff_smul] at h3
  have h4 : (∏ σ, ∏ x, (Function.update (1 : ι → Matrix (Fin n) (Fin n) K) τ β) σ x x ^ ν σ x) = ∏ x, β x x ^ ν τ x := by
    rw [Finset.prod_eq_single τ]
    · rw [Function.update_self]
    · intro σ _ hσ
      rw [Function.update_of_ne hσ]
      simp
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h4] at h3
  exact h3

def gOf (τ : ι) (m : ι × Fin n × Fin n →₀ ℕ) : Fin n × Fin n →₀ ℕ := m.comapDomain (Prod.mk τ) (Prod.mk_right_injective τ).injOn

def rOf (τ : ι) (m : ι × Fin n × Fin n →₀ ℕ) : Off ι n τ →₀ ℕ := m.comapDomain Subtype.val Subtype.val_injective.injOn

/- English proof (translation)
Use extensionality with `⟨t, v⟩`. Distinguish the cases in `h : t = τ`. Substitute `h` using the available equality. Rewrite using `[Finsupp.add_apply, Finsupp.mapDomain_apply (Prod.mk_right_injective t), Finsupp.mapDomain_of_notMem_range, add_zero]`. Both sides reduce to the same expression.

Introduce and unpack `⟨w, hw⟩`. Conclude with `w.2 (congrArg Prod.fst hw)`. Rewrite using `[Finsupp.add_apply, Finsupp.mapDomain_of_notMem_range, zero_add]`. Conclude with `(Finsupp.mapDomain_apply Subtype.val_injective (rOf τ m) (⟨(t, v), h⟩ : Off ι n τ)).symm`. Introduce and unpack `⟨w, hw⟩`.

Conclude with `h (congrArg Prod.fst hw).symm`.
-/
theorem split_pos (τ : ι) (m : ι × Fin n × Fin n →₀ ℕ) :
    m = (gOf τ m).mapDomain (Prod.mk τ) + (rOf τ m).mapDomain Subtype.val := by
  ext ⟨t, v⟩
  by_cases h : t = τ
  · subst h
    rw [Finsupp.add_apply, Finsupp.mapDomain_apply (Prod.mk_right_injective t), Finsupp.mapDomain_of_notMem_range, add_zero]
    · rfl
    · rintro ⟨w, hw⟩
      exact w.2 (congrArg Prod.fst hw)
  · rw [Finsupp.add_apply, Finsupp.mapDomain_of_notMem_range, zero_add]
    · exact (Finsupp.mapDomain_apply Subtype.val_injective (rOf τ m) (⟨(t, v), h⟩ : Off ι n τ)).symm
    · rintro ⟨w, hw⟩
      exact h (congrArg Prod.fst hw).symm

/- English proof (translation)
Establish `h : (monomial (r.mapDomain Subtype.val) 1 : Pol K ι n) = r.prod fun w e => X w.1 ^ e`. Rewrite using `[monomial_eq, C_1, one_mul, Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]`. Rewrite using `[h, psi', coe_eval₂Hom, eval₂_monomial]`. Both sides reduce to the same expression.
-/
theorem psi'_monomial (τ : ι) (r : Off ι n τ →₀ ℕ) (G : MvPolynomial (Fin n × Fin n) K) :
    psi' τ (monomial r G) = blockEmb K τ G * monomial (r.mapDomain Subtype.val) 1 := by
  have h : (monomial (r.mapDomain Subtype.val) 1 : Pol K ι n) = r.prod fun w e => X w.1 ^ e := by
    rw [monomial_eq, C_1, one_mul, Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  rw [h, psi', coe_eval₂Hom, eval₂_monomial]
  rfl

/- English proof (translation)
Establish `h : (monomial m c : Pol K ι n) = psi' τ (monomial (rOf τ m) (monomial (gOf τ m) c))`. Rewrite using `[psi'_monomial, blockEmb, rename_monomial, monomial_mul, mul_one, ← split_pos]`. Rewrite using `[h, psi_psi']`.
-/
theorem psi_monomial (τ : ι) (m : ι × Fin n × Fin n →₀ ℕ) (c : K) :
    psi τ (monomial m c) = monomial (rOf τ m) (monomial (gOf τ m) c) := by
  have h : (monomial m c : Pol K ι n) = psi' τ (monomial (rOf τ m) (monomial (gOf τ m) c)) := by
    rw [psi'_monomial, blockEmb, rename_monomial, monomial_mul, mul_one, ← split_pos]
  rw [h, psi_psi']

def atPos (τ : ι) (π : MvPolynomial (Fin n × Fin n) K →ₗ[K] MvPolynomial (Fin n × Fin n) K) : Pol K ι n →ₗ[K] Pol K ι n :=
  (basisMonomials _ K).constr K fun m => psi' τ (monomial (rOf τ m) (π (monomial (gOf τ m) 1)))

/- English proof (translation)
Proceed by induction on `Q using MvPolynomial.induction_on' with`. Consider the case `monomial m c`. Establish `h : (monomial m c : Pol K ι n) = c • basisMonomials _ K m`. Rewrite using `[coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]`. Establish `h2 : (monomial (gOf τ m) c : MvPolynomial (Fin n × Fin n) K) = c • monomial (gOf τ m) 1`.

Rewrite using `[smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[psi_monomial, h, map_smul, atPos, Module.Basis.constr_basis, map_smul, psi_psi', coeff_smul, coeff_monomial, coeff_monomial, h2]`. Use `split_ifs`. Rewrite using `[map_smul]`. Rewrite using `[smul_zero, map_zero]`.

Consider the case `add f g hf hg => simp only [map_add, coeff_add, hf, hg]`.
-/
theorem coeff_psi_atPos (τ : ι) (π : MvPolynomial (Fin n × Fin n) K →ₗ[K] MvPolynomial (Fin n × Fin n) K) (Q : Pol K ι n)
    (r : Off ι n τ →₀ ℕ) : coeff r (psi τ (atPos τ π Q)) = π (coeff r (psi τ Q)) := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | monomial m c =>
    have h : (monomial m c : Pol K ι n) = c • basisMonomials _ K m := by
      rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
    have h2 : (monomial (gOf τ m) c : MvPolynomial (Fin n × Fin n) K) = c • monomial (gOf τ m) 1 := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [psi_monomial, h, map_smul, atPos, Module.Basis.constr_basis, map_smul, psi_psi', coeff_smul, coeff_monomial, coeff_monomial, h2]
    split_ifs
    · rw [map_smul]
    · rw [smul_zero, map_zero]
  | add f g hf hg => simp only [map_add, coeff_add, hf, hg]

/- English proof (translation)
Establish `e : psi τ (atPos τ π Q) = psi τ Q` using `MvPolynomial.ext _ _ fun r => by rw [coeff_psi_atPos, h r]`. Rewrite using `[← psi'_psi τ (atPos τ π Q), e, psi'_psi]`.
-/
theorem atPos_fixed (τ : ι) (π : MvPolynomial (Fin n × Fin n) K →ₗ[K] MvPolynomial (Fin n × Fin n) K) (Q : Pol K ι n)
    (h : ∀ r, π (coeff r (psi τ Q)) = coeff r (psi τ Q)) : atPos τ π Q = Q := by
  have e : psi τ (atPos τ π Q) = psi τ Q := MvPolynomial.ext _ _ fun r => by rw [coeff_psi_atPos, h r]
  rw [← psi'_psi τ (atPos τ π Q), e, psi'_psi]

/- English proof (translation)
Establish `e : psi τ (atPos τ π (blockEmb K τ G * R)) = psi τ (blockEmb K τ (π G) * R)`. Use `MvPolynomial.ext _ _ fun r => ?_` and prove the remaining obligations. Rewrite using `[coeff_psi_atPos, map_mul, map_mul, psi_blockEmb, psi_blockEmb, hR, coeff_C_mul, coeff_C_mul, coeff_map, mul_comm G, mul_comm (π G), ← smul_eq_C_mul, ← smul_eq_C_mul, map_smul]`. Rewrite using `[← psi'_psi τ (atPos τ π (blockEmb K τ G * R)), e, psi'_psi]`.
-/
theorem atPos_mul (τ : ι) (π : MvPolynomial (Fin n × Fin n) K →ₗ[K] MvPolynomial (Fin n × Fin n) K) (G : MvPolynomial (Fin n × Fin n) K)
    (R : Pol K ι n) (R' : MvPolynomial (Off ι n τ) K) (hR : psi τ R = map C R') :
    atPos τ π (blockEmb K τ G * R) = blockEmb K τ (π G) * R := by
  have e : psi τ (atPos τ π (blockEmb K τ G * R)) = psi τ (blockEmb K τ (π G) * R) := by
    refine MvPolynomial.ext _ _ fun r => ?_
    rw [coeff_psi_atPos, map_mul, map_mul, psi_blockEmb, psi_blockEmb, hR, coeff_C_mul, coeff_C_mul, coeff_map, mul_comm G, mul_comm (π G),
      ← smul_eq_C_mul, ← smul_eq_C_mul, map_smul]
  rw [← psi'_psi τ (atPos τ π (blockEmb K τ G * R)), e, psi'_psi]

/- English proof (translation)
Proceed by induction on `F using MvPolynomial.induction_on with`. Consider the case `C a => simp [blockEmb, MvPolynomial.algebraMap_apply]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p v hp`. Simplify using `only [map_mul, hp]`.

Simplify using `[blockEmb, psi, h]`.
-/
theorem psi_blockEmb_ne (τ σ : ι) (h : σ ≠ τ) (F : MvPolynomial (Fin n × Fin n) K) :
    psi τ (blockEmb K σ F) = map C (rename (fun v => (⟨(σ, v), h⟩ : Off ι n τ)) F) := by
  induction F using MvPolynomial.induction_on with
  | C a => simp [blockEmb, MvPolynomial.algebraMap_apply]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp]
    simp [blockEmb, psi, h]

open Classical in
/- English proof (translation)
Rewrite using `[← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ τ), ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ τ), Function.update_self]`. Establish `e1 : ∏ σ ∈ Finset.univ.erase τ, blockEmb K σ (Function.update F τ (π (F τ)) σ) = ∏ σ ∈ Finset.univ.erase τ, blockEmb K σ (F σ)` using `Finset.prod_congr rfl fun σ hσ => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hσ)]`. Rewrite using `[e1]`. Use `atPos_mul τ π (F τ) _ (∏ σ ∈ Finset.univ.erase τ, if h : σ = τ then 1 else rename (fun v => (⟨(σ, v), h⟩ : Off ι n τ)) (F σ)) ?_` and prove the remaining obligations. Rewrite using `[map_prod, map_prod]`.

Use `Finset.prod_congr rfl fun σ hσ => ?_` and prove the remaining obligations. Rewrite using `[dif_neg (Finset.ne_of_mem_erase hσ), psi_blockEmb_ne τ σ (Finset.ne_of_mem_erase hσ)]`.
-/
theorem atPos_prod [Fintype ι] (τ : ι) (π : MvPolynomial (Fin n × Fin n) K →ₗ[K] MvPolynomial (Fin n × Fin n) K)
    (F : ι → MvPolynomial (Fin n × Fin n) K) :
    atPos τ π (∏ σ, blockEmb K σ (F σ)) = ∏ σ, blockEmb K σ (Function.update F τ (π (F τ)) σ) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ τ), ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ τ), Function.update_self]
  have e1 : ∏ σ ∈ Finset.univ.erase τ, blockEmb K σ (Function.update F τ (π (F τ)) σ) = ∏ σ ∈ Finset.univ.erase τ, blockEmb K σ (F σ) :=
    Finset.prod_congr rfl fun σ hσ => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hσ)]
  rw [e1]
  refine atPos_mul τ π (F τ) _ (∏ σ ∈ Finset.univ.erase τ, if h : σ = τ then 1 else rename (fun v => (⟨(σ, v), h⟩ : Off ι n τ)) (F σ)) ?_
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun σ hσ => ?_
  rw [dif_neg (Finset.ne_of_mem_erase hσ), psi_blockEmb_ne τ σ (Finset.ne_of_mem_erase hσ)]

def TS [Fintype ι] (W : ι → Submodule K (MvPolynomial (Fin n × Fin n) K)) (S : Finset ι) : Submodule K (Pol K ι n) :=
  Submodule.span K {P | ∃ F : ι → MvPolynomial (Fin n × Fin n) K, (∀ σ ∈ S, F σ ∈ W σ) ∧ P = ∏ σ, blockEmb K σ (F σ)}

/- English proof (translation)
Rewrite using `[Q.as_sum]`. Use `Submodule.sum_mem _ fun m _ => ?_` and prove the remaining obligations. Establish `hm : m = ∑ t, (gOf t m).mapDomain (Prod.mk t)`. Use extensionality with `⟨t, v⟩`. Rewrite using `[Finsupp.finsetSum_apply, Finset.sum_eq_single t]`.

Conclude with `(Finsupp.mapDomain_apply (Prod.mk_right_injective t) (gOf t m) v).symm`. Introduce `σ _ hσ`. Use `Finsupp.mapDomain_of_notMem_range _ _ ?_` and prove the remaining obligations. Introduce and unpack `⟨w, hw⟩`. Conclude with `hσ (congrArg Prod.fst hw)`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Establish `h : (monomial m (coeff m Q) : Pol K ι n) = coeff m Q • ∏ σ, blockEmb K σ (monomial (gOf σ m) (1 : K))`. Rewrite using `[ldtensor_prod_monomial, smul_monomial, smul_eq_mul, mul_one, ← hm]`. Rewrite using `[h]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, fun σ hσ => absurd hσ (Finset.notMem_empty σ), rfl⟩)`.
-/
theorem mem_TS_empty [Fintype ι] (W : ι → Submodule K (MvPolynomial (Fin n × Fin n) K)) (Q : Pol K ι n) : Q ∈ TS W ∅ := by
  classical
  rw [Q.as_sum]
  refine Submodule.sum_mem _ fun m _ => ?_
  have hm : m = ∑ t, (gOf t m).mapDomain (Prod.mk t) := by
    ext ⟨t, v⟩
    rw [Finsupp.finsetSum_apply, Finset.sum_eq_single t]
    · exact (Finsupp.mapDomain_apply (Prod.mk_right_injective t) (gOf t m) v).symm
    · intro σ _ hσ
      refine Finsupp.mapDomain_of_notMem_range _ _ ?_
      rintro ⟨w, hw⟩
      exact hσ (congrArg Prod.fst hw)
    · intro h; exact absurd (Finset.mem_univ _) h
  have h : (monomial m (coeff m Q) : Pol K ι n) = coeff m Q • ∏ σ, blockEmb K σ (monomial (gOf σ m) (1 : K)) := by
    rw [ldtensor_prod_monomial, smul_monomial, smul_eq_mul, mul_one, ← hm]
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, fun σ hσ => absurd hσ (Finset.notMem_empty σ), rfl⟩)

/- English proof (translation)
Introduce `Q hQ`. Establish `key : ∀ S : Finset ι, Q ∈ TS (fun τ => dualWeyl K n n (ν τ)) S`. Introduce `S`. Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => exact mem_TS_empty _ Q`.

Consider the case `insert τ S _ ih`. Take `⟨T, hT⟩` from `Submodule.exists_isCompl (dualWeyl K n n (ν τ))`. Use `set π : MvPolynomial (Fin n × Fin n) K →ₗ[K] MvPolynomial (Fin n × Fin n) K := (dualWeyl K n n (ν τ)).subtype ∘ₗ Submodule.projectionOnto _ T hT with hπ`. Establish `hfix : atPos τ π Q = Q`. Use `atPos_fixed τ π Q fun r => ?_` and prove the remaining obligations.

Establish `h` using `Submodule.projectionOnto_apply_left hT (⟨coeff r (psi τ Q), coeff_psi_mem hQ τ r⟩ : dualWeyl K n n (ν τ))`. Establish `h' : Submodule.projectionOnto _ T hT (coeff r (psi τ Q)) = ⟨coeff r (psi τ Q), coeff_psi_mem hQ τ r⟩` using `h`. Rewrite using `[hπ, LinearMap.comp_apply, h']`. Both sides reduce to the same expression. Establish `hle : TS (fun τ => dualWeyl K n n (ν τ)) S ≤ (TS (fun τ => dualWeyl K n n (ν τ)) (insert τ S)).comap (atPos τ π)`.

Unfold `TS`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `P ⟨F, hF, rfl⟩`. Rewrite using `[SetLike.mem_coe, Submodule.mem_comap, atPos_prod]`. Use `Submodule.subset_span ⟨_, fun σ hσ => ?_, rfl⟩` and prove the remaining obligations.

Distinguish the cases in `h : σ = τ`. Substitute `h` using the available equality. Rewrite using `[Function.update_self]`. Conclude with `(Submodule.projectionOnto _ T hT (F σ)).2`. Rewrite using `[Function.update_of_ne h]`.

Conclude with `hF σ ((Finset.mem_insert.1 hσ).resolve_left h)`. Use `hle ih` as an intermediate fact. Rewrite `this` using `[Submodule.mem_comap, hfix]`. Conclude with `this`. Establish `h` using `key Finset.univ`.

Unfold `TS at h`. Unfold `tensorLat`. Use `Submodule.span_mono ?_ h` and prove the remaining obligations. Introduce and unpack `P ⟨F, hF, rfl⟩`. Conclude with `⟨F, fun s => hF s (Finset.mem_univ s), rfl⟩`.
-/
theorem wtPol_le_tensor [Fintype ι] [Infinite K] (ν : ι → Fin n → ℕ) :
    WtPol K ν ≤ tensorLat K K fun τ => dualWeyl K n n (ν τ) := by
  classical
  intro Q hQ
  have key : ∀ S : Finset ι, Q ∈ TS (fun τ => dualWeyl K n n (ν τ)) S := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact mem_TS_empty _ Q
    | insert τ S _ ih =>
      obtain ⟨T, hT⟩ := Submodule.exists_isCompl (dualWeyl K n n (ν τ))
      set π : MvPolynomial (Fin n × Fin n) K →ₗ[K] MvPolynomial (Fin n × Fin n) K :=
        (dualWeyl K n n (ν τ)).subtype ∘ₗ Submodule.projectionOnto _ T hT with hπ
      have hfix : atPos τ π Q = Q := by
        refine atPos_fixed τ π Q fun r => ?_
        have h := Submodule.projectionOnto_apply_left hT (⟨coeff r (psi τ Q), coeff_psi_mem hQ τ r⟩ : dualWeyl K n n (ν τ))
        have h' : Submodule.projectionOnto _ T hT (coeff r (psi τ Q)) = ⟨coeff r (psi τ Q), coeff_psi_mem hQ τ r⟩ := h
        rw [hπ, LinearMap.comp_apply, h']
        rfl
      have hle : TS (fun τ => dualWeyl K n n (ν τ)) S ≤ (TS (fun τ => dualWeyl K n n (ν τ)) (insert τ S)).comap (atPos τ π) := by
        unfold TS
        rw [Submodule.span_le]
        rintro P ⟨F, hF, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_comap, atPos_prod]
        refine Submodule.subset_span ⟨_, fun σ hσ => ?_, rfl⟩
        by_cases h : σ = τ
        · subst h
          rw [Function.update_self]
          exact (Submodule.projectionOnto _ T hT (F σ)).2
        · rw [Function.update_of_ne h]
          exact hF σ ((Finset.mem_insert.1 hσ).resolve_left h)
      have := hle ih
      rw [Submodule.mem_comap, hfix] at this
      exact this
  have h := key Finset.univ
  unfold TS at h
  unfold tensorLat
  refine Submodule.span_mono ?_ h
  rintro P ⟨F, hF, rfl⟩
  exact ⟨F, fun s => hF s (Finset.mem_univ s), rfl⟩

/- English proof (translation)
The claim follows from `wtPol_le_tensor fun τ => (lam τ).natW`.
-/
theorem WtInVV_core [Fintype ι] [Infinite K] (lam : ι → DomWeight n) : WtPol K (fun τ r => (lam τ).natW r) ≤ DIV.VV K lam :=
  wtPol_le_tensor fun τ => (lam τ).natW

end WtVVB

/- English proof (translation)
Introduce `_ _ _ _ _ _ lam` and use `WtInVV_core lam`.
-/
theorem weight_in_vv : WtInVV := fun _ _ _ _ _ _ lam => WtInVV_core lam

/- English proof (translation)
Introduce `h1 h2 K _ _ ι _ a b hab lam lam' n hw J P hP`. Rewrite using `[jetMap_shift]`. Apply `h2 K ι b lam'` to reduce the goal to its premises. Establish `e : (fun τ r => (lam' τ).natW r) = extNu b (fun τ r => (lam τ).natW r + n τ)`. Use function extensionality and compare the values at `τ r`.

Conclude with `hw τ r`. Rewrite using `[e]`. Conclude with `jet_weight K ι a b hab J _ _ (h1 K ι a lam n P hP)`.
-/
theorem jet_in_vv_reduction : JetInVVRed := by
  intro h1 h2 K _ _ ι _ a b hab lam lam' n hw J P hP
  rw [jetMap_shift]
  apply h2 K ι b lam'
  have e : (fun τ r => (lam' τ).natW r) = extNu b (fun τ r => (lam τ).natW r + n τ) := by
    funext τ r; exact hw τ r
  rw [e]
  exact jet_weight K ι a b hab J _ _ (h1 K ι a lam n P hP)

/- English proof (translation)
The claim follows from `jet_in_vv_reduction vv_in_weight h2 K ι a b hab lam lam' n hw`.
-/
theorem jetInVV_of_wtInVV (h2 : WtInVV) (K : Type) [Field K] [Infinite K] (ι : Type) [Fintype ι] (a b : ℕ) (hab : a ≤ b)
    (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ)
    (hw : ∀ τ r, (lam' τ).natW r = extNu b (fun τ r => (lam τ).natW r + n τ) τ r) : JetInVV K lam lam' n :=
  jet_in_vv_reduction vv_in_weight h2 K ι a b hab lam lam' n hw

/- English proof (translation)
The claim follows from `jetInVV_of_wtInVV weight_in_vv`.
-/
theorem jet_in_vv_of_weight : JetInVVOf := jetInVV_of_wtInVV weight_in_vv

section Unf

open MvPolynomial

/- English proof (translation)
Introduce `D u C O i hi`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `Q hQ`. Use `set Dt : MvPolynomial (GL3Theta.FrV D (D.R.N i)) ℂ := ∏ τ, frDet ℂ (D.R.N i) τ with hDt`. Establish `hev : ∀ v : GL3Theta.FrV D (D.R.N i) → ℂ, eval v Dt = ∏ τ, (Matrix.of fun α k => v (τ, α, k)).det`.

Introduce `v`. Rewrite using `[hDt, map_prod]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Unfold `frDet`. Rewrite using `[RingHom.map_det]`.

Use `congr 1`. Use extensionality with `α k`. Simplify using the standard rewrite rules. Establish `h0 : Q * Dt = 0`. Apply `MvPolynomial.funext` to reduce the goal to its premises.

Introduce `v`. Rewrite using `[map_mul, map_zero, hev]`. Distinguish the cases in `h : ∀ τ, (Matrix.of fun α k => v (τ, α, k) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ).det ≠ 0`. Take `⟨y, hy⟩` from `(O.frm_range i hi fun τ => Matrix.of fun α k => v (τ, α, k)).2 h`. Establish `h1` using `congrFun hQ y`.

Establish `h2 : eval v Q = 0`. Establish `: frPoly O i Q y = eval v Q` using `by show GL3Theta.evFr D Q (O.frm i y) = _`. Rewrite using `[hy]`. Both sides reduce to the same expression. Rewrite using `[← this, h1]`.

Both sides reduce to the same expression. Rewrite using `[h2, zero_mul]`. Use `push Not at h`. Take `⟨τ, hτ⟩` from `h`. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ τ) hτ, mul_zero]`.

Break down `mul_eq_zero.1 h0 with h | h` into its components or cases. Conclude with `h`. It suffices to derive a contradiction. Establish `h1` using `hev fun k => if k.2.1 = k.2.2 then 1 else 0`. Rewrite `h1` using `[h, map_zero]`.

Establish `h2 : ∀ τ : D.what₂.Tau, (Matrix.of fun α k : Fin (D.R.N i) => (if α = k then (1 : ℂ) else 0)).det = 1`. Introduce `τ`. Establish `: (Matrix.of fun α k : Fin (D.R.N i) => (if α = k then (1 : ℂ) else 0)) = 1`. Use extensionality with `α k`. Simplify using `[Matrix.one_apply]`.

Rewrite using `[this, Matrix.det_one]`. Conclude with `zero_ne_one (h1.trans (Finset.prod_eq_one fun τ _ => h2 τ))`.
-/
theorem frobenius_poly_injective : FrPolyInj := by
  intro D u C O i hi
  rw [injective_iff_map_eq_zero]
  intro Q hQ
  set Dt : MvPolynomial (GL3Theta.FrV D (D.R.N i)) ℂ := ∏ τ, frDet ℂ (D.R.N i) τ with hDt
  have hev : ∀ v : GL3Theta.FrV D (D.R.N i) → ℂ, eval v Dt = ∏ τ, (Matrix.of fun α k => v (τ, α, k)).det := by
    intro v
    rw [hDt, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    unfold frDet
    rw [RingHom.map_det]
    congr 1
    ext α k
    simp
  have h0 : Q * Dt = 0 := by
    apply MvPolynomial.funext
    intro v
    rw [map_mul, map_zero, hev]
    by_cases h : ∀ τ, (Matrix.of fun α k => v (τ, α, k) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ).det ≠ 0
    · obtain ⟨y, hy⟩ := (O.frm_range i hi fun τ => Matrix.of fun α k => v (τ, α, k)).2 h
      have h1 := congrFun hQ y
      have h2 : eval v Q = 0 := by
        have : frPoly O i Q y = eval v Q := by
          show GL3Theta.evFr D Q (O.frm i y) = _
          rw [hy]; rfl
        rw [← this, h1]; rfl
      rw [h2, zero_mul]
    · push Not at h
      obtain ⟨τ, hτ⟩ := h
      rw [Finset.prod_eq_zero (Finset.mem_univ τ) hτ, mul_zero]
  rcases mul_eq_zero.1 h0 with h | h
  · exact h
  · exfalso
    have h1 := hev fun k => if k.2.1 = k.2.2 then 1 else 0
    rw [h, map_zero] at h1
    have h2 : ∀ τ : D.what₂.Tau, (Matrix.of fun α k : Fin (D.R.N i) => (if α = k then (1 : ℂ) else 0)).det = 1 := by
      intro τ
      have : (Matrix.of fun α k : Fin (D.R.N i) => (if α = k then (1 : ℂ) else 0)) = 1 := by
        ext α k; simp [Matrix.one_apply]
      rw [this, Matrix.det_one]
    exact zero_ne_one (h1.trans (Finset.prod_eq_one fun τ _ => h2 τ))

/- English proof (translation)
The claim follows from `Classical.epsilon_spec (p := fun g => g ∘ₗ frPoly O i = LinearMap.id) (LinearMap.exists_leftInverse_of_injective _ (LinearMap.ker_eq_bot.2 (frobenius_poly_injective D u C O i hi)))`.
-/
theorem frInv_spec {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} (O : GL3Theta.LiftObj D C) {i : ℕ} (hi : i ≤ D.R.m) :
    frInv O i ∘ₗ frPoly O i = LinearMap.id :=
  Classical.epsilon_spec (p := fun g => g ∘ₗ frPoly O i = LinearMap.id)
    (LinearMap.exists_leftInverse_of_injective _ (LinearMap.ker_eq_bot.2 (frobenius_poly_injective D u C O i hi)))

/- English proof (translation)
Introduce `D u C O i hi Θ Q y'`. Establish `h : frInv O i (fun y => GL3Theta.evFr D Q (O.frm i y)) = Q` using `LinearMap.congr_fun (frInv_spec O hi) Q`. Unfold `unfC`. Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, h]`. Conclude with `jetMap_applyAt0 D O.dgen Θ Q (O.frm (i + 1) y')`.
-/
theorem unfolding_char_formula : UnfCFormula := by
  intro D u C O i hi Θ Q y'
  have h : frInv O i (fun y => GL3Theta.evFr D Q (O.frm i y)) = Q := LinearMap.congr_fun (frInv_spec O hi) Q
  unfold unfC
  rw [LinearMap.comp_apply, LinearMap.comp_apply, h]
  exact jetMap_applyAt0 D O.dgen Θ Q (O.frm (i + 1) y')

/- English proof (translation)
Proceed by induction on `s, hrs using Nat.le_induction with`. Consider the case `base => exact le_rfl`. Consider the case `succ n hn ih => exact (RowWeightLemmas.nuRow_anti D u i hi τ n hs).trans (ih (by omega))`.
-/
theorem nuRow_anti_le (D : D7) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) (r s : ℕ) (hrs : r ≤ s) (hs : s < D.R.N i) :
    DV.nuRow D u (i + 1) τ s ≤ DV.nuRow D u (i + 1) τ r := by
  induction s, hrs using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact (RowWeightLemmas.nuRow_anti D u i hi τ n hs).trans (ih (by omega))

/- English proof (translation)
Introduce `D u i hi τ r`. Take `⟨z, hz⟩` from `RowWeightLemmas.nuRow_int D u i hi τ r r.2`. Establish `hpos : 0 < DV.nuRow D u (i + 1) τ r` using `lt_of_lt_of_le (RowWeightLemmas.nuRow_last_pos D u i hi τ) (nuRow_anti_le D u i hi τ r _ (by have := r.2; omega) (by have := r.2; omega))`. Establish `hz0 : 0 < z` using `by rw [hz] at hpos; exact_mod_cast hpos`. Take `⟨n, rfl⟩` from `Int.eq_ofNat_of_zero_le hz0.le`.

Establish `: nuT D u i τ r = n`. Unfold `nuT`. Rewrite using `[hz]`. Simplify using the standard rewrite rules. Rewrite using `[this, hz]`.

Prove the components needed by the constructor for the conclusion. Simplify using the standard rewrite rules. Conclude with `hz0` after adjusting the coercions.
-/
theorem nu_t_identity : NuTIs := by
  intro D u i hi τ r
  obtain ⟨z, hz⟩ := RowWeightLemmas.nuRow_int D u i hi τ r r.2
  have hpos : 0 < DV.nuRow D u (i + 1) τ r :=
    lt_of_lt_of_le (RowWeightLemmas.nuRow_last_pos D u i hi τ) (nuRow_anti_le D u i hi τ r _ (by have := r.2; omega) (by have := r.2; omega))
  have hz0 : 0 < z := by rw [hz] at hpos; exact_mod_cast hpos
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz0.le
  have : nuT D u i τ r = n := by
    unfold nuT; rw [hz]; simp
  rw [this, hz]; constructor
  · simp
  · exact_mod_cast hz0

/- English proof (translation)
Introduce `c c' Q _` and use `h c c' Q`.
-/
theorem UnfIsAll.unfIs {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {O : GL3Theta.LiftObj D C} {i : ℕ} (h : UnfIsAll O i)
    (ν : D.what₂.Tau → Fin (D.R.N i) → ℕ) : UnfIs O i ν := fun c c' Q _ => h c c' Q

/- English proof (translation)
Unfold `Ranks.N`. Rewrite using `[Nat.add_mul]`. Use linear arithmetic over natural numbers and integers.
-/
theorem N_le_succ (R : Ranks) (i : ℕ) : R.N i ≤ R.N (i + 1) := by
  unfold Ranks.N
  rw [Nat.add_mul]
  omega

/- English proof (translation)
Introduce `hSP D u C O i hi ν f hf`. Establish `e1 : C.sharp i f = mulFun (fun y => ∏ τ, (O.frm i y τ).det ^ C.sSharp i τ) f`. Establish `e : (fun y => ∏ τ, (O.frm i y τ).det ^ C.sSharp i τ) = fun y => ∏ τ, (C.de i y τ) ^ (C.sSharp i τ)`. Use function extensionality and compare the values at `y`. Simplify using `only [O.frm_de i hi]`.

Rewrite using `[e]`. Both sides reduce to the same expression. Take `⟨Q, hQ⟩` from `hSP D.what₂.Tau (D.R.N i) (C.Y i) (O.frm i) (O.frm_range i hi) _ (C.sSharp i) ν (fun τ r => sub_add_cancel _ _) f hf`. Take `⟨Q', hQ', h⟩` from `(sharp_vector_formula D.what₂.Tau (D.R.N i) (C.Y i) (O.frm i) (O.frm_range i hi) _ (C.sSharp i) ν (fun τ r => sub_add_cancel _ _) (mulFun (fun y => ∏ τ, (O.frm i y τ).det ^ C.sSharp i τ) f)).2 ⟨⟨f, hf, rfl⟩, Q, hQ⟩`. Conclude with `⟨Q', hQ', e1.trans h⟩`.
-/
theorem forms_sharp_description : FormsSharp := by
  intro hSP D u C O i hi ν f hf
  have e1 : C.sharp i f = mulFun (fun y => ∏ τ, (O.frm i y τ).det ^ C.sSharp i τ) f := by
    have e : (fun y => ∏ τ, (O.frm i y τ).det ^ C.sSharp i τ) = fun y => ∏ τ, (C.de i y τ) ^ (C.sSharp i τ) := by
      funext y; simp only [O.frm_de i hi]
    rw [e]
    rfl
  obtain ⟨Q, hQ⟩ := hSP D.what₂.Tau (D.R.N i) (C.Y i) (O.frm i) (O.frm_range i hi) _ (C.sSharp i) ν (fun τ r => sub_add_cancel _ _) f hf
  obtain ⟨Q', hQ', h⟩ := (sharp_vector_formula D.what₂.Tau (D.R.N i) (C.Y i) (O.frm i) (O.frm_range i hi) _ (C.sSharp i) ν (fun τ r => sub_add_cancel _ _)
    (mulFun (fun y => ∏ τ, (O.frm i y τ).det ^ C.sSharp i τ) f)).2 ⟨⟨f, hf, rfl⟩, Q, hQ⟩
  exact ⟨Q', hQ', e1.trans h⟩

/- English proof (translation)
Introduce `D u C O i hi K _ σ c c' J z hJ sh n hn P`. Establish `h` using `unfolding_gl_eval K D.what₂.Tau (D.R.N i) (D.R.N (i + 1)) (C.Y i) (C.Y (i + 1)) (O.frm i) (O.frm (i + 1)) (frobenius_poly_injective D u C O i hi.le) (fun y => (O.frm_range i hi.le _).1 ⟨y, rfl⟩) σ O.dgen (O.Th i c c') J z hJ sh (C.sSharp i) (C.sDiv i) n hn P`. Rewrite using `[h]`. Establish `e1 : (fun y => ∏ τ, (O.frm i y τ).det ^ C.sSharp i τ) = fun y => ∏ τ, (C.de i y τ) ^ (C.sSharp i τ)`. Use function extensionality and compare the values at `y`.

Simplify using `only [O.frm_de i hi.le]`. Establish `e2 : (fun y' => (∏ τ, (O.frm (i + 1) y' τ).det ^ C.sDiv i τ)⁻¹) = fun y' => (∏ τ, (C.de (i + 1) y' τ) ^ (C.sDiv i τ))⁻¹`. Use function extensionality and compare the values at `y'`. Simplify using `only [O.frm_de (i + 1) hi]`. Rewrite using `[e1, e2]`.

Both sides reduce to the same expression.
-/
theorem chain_char_eval : ChainCEv := by
  intro D u C O i hi K _ σ c c' J z hJ sh n hn P
  have h := unfolding_gl_eval K D.what₂.Tau (D.R.N i) (D.R.N (i + 1)) (C.Y i) (C.Y (i + 1)) (O.frm i) (O.frm (i + 1)) (frobenius_poly_injective D u C O i hi.le)
    (fun y => (O.frm_range i hi.le _).1 ⟨y, rfl⟩) σ O.dgen (O.Th i c c') J z hJ sh (C.sSharp i) (C.sDiv i) n hn P
  rw [h]
  have e1 : (fun y => ∏ τ, (O.frm i y τ).det ^ C.sSharp i τ) = fun y => ∏ τ, (C.de i y τ) ^ (C.sSharp i τ) := by
    funext y; simp only [O.frm_de i hi.le]
  have e2 : (fun y' => (∏ τ, (O.frm (i + 1) y' τ).det ^ C.sDiv i τ)⁻¹) = fun y' => (∏ τ, (C.de (i + 1) y' τ) ^ (C.sDiv i τ))⁻¹ := by
    funext y'; simp only [O.frm_de (i + 1) hi]
  rw [e1, e2]
  rfl

/- English proof (translation)
Unfold `DIV.VV Formalism.GradedWeylDivisibility.tensorLat at hF ⊢`. Proceed by induction on `hF using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨f, hf, rfl⟩` from `hx`. Use `Submodule.subset_span ⟨fun τ => MvPolynomial.map σ (f τ), fun τ => Formalism.GradedWeylDivisibility.dualWeylMap K L σ n n _ _ (hf τ), ?_⟩` and prove the remaining obligations.

Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[Formalism.GradedWeylDivisibility.blockEmb, Formalism.GradedWeylDivisibility.blockEmb, MvPolynomial.map_rename]`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `smul c x _ hx`. Rewrite using `[MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem map_mem_VV {K L : Type} [Field K] [Field L] {ι : Type} [Fintype ι] {n : ℕ} (σ : K →+* L) (lam : ι → DomWeight n) (F : DIV.Pol K ι n)
    (hF : F ∈ DIV.VV K lam) : MvPolynomial.map σ F ∈ DIV.VV L lam := by
  unfold DIV.VV Formalism.GradedWeylDivisibility.tensorLat at hF ⊢
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    refine Submodule.subset_span ⟨fun τ => MvPolynomial.map σ (f τ), fun τ => Formalism.GradedWeylDivisibility.dualWeylMap K L σ n n _ _ (hf τ), ?_⟩
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Formalism.GradedWeylDivisibility.blockEmb, Formalism.GradedWeylDivisibility.blockEmb, MvPolynomial.map_rename]
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Introduce `D u C O i hi ν h K _ σ lam n hw c c' J z hJ sh hn P hP`. Establish `hs : C.sharp i (evG (O.frm i) sh σ P) = frPoly O i (MvPolynomial.map σ P * ∏ τ, frDet ℂ (D.R.N i) τ ^ n τ)`. Establish `h1` using `mulFun_evG (fr := O.frm i) (fun y => (O.frm_range i hi.le _).1 ⟨y, rfl⟩) σ sh (C.sSharp i) n hn P`. Establish `e1 : (fun y => ∏ τ, (O.frm i y τ).det ^ C.sSharp i τ) = fun y => ∏ τ, (C.de i y τ) ^ (C.sSharp i τ)`. Use function extensionality and compare the values at `y`.

Simplify using `only [O.frm_de i hi.le]`. Rewrite `h1` using `[e1]`. Conclude with `h1`. Establish `hQ : MvPolynomial.map σ P * ∏ τ, frDet ℂ (D.R.N i) τ ^ n τ ∈ WtPol ℂ ν`. Establish `h2` using `vv_in_weight ℂ D.what₂.Tau _ lam n (MvPolynomial.map σ P) (map_mem_VV σ lam P hP)`.

Establish `e : (fun τ r => (lam τ).natW r + n τ) = ν` using `by funext τ r; exact hw τ r`. Rewrite `h2` using `[e]`. Then use the resulting hypothesis. Rewrite using `[chain_char_eval D u C O i hi K σ c c' J z hJ sh n hn P]`. Use `show z • ((C.rhoDet i c * C.rhoDet' i c') • C.divDe i (C.unf i c c' (C.sharp i (evG (O.frm i) sh σ P)))) = (C.rhoDet i c * C.rhoDet' i c') • z • C.divDe i (unfC O i (O.Th i c c') (C.sharp i (evG (O.frm i) sh σ P)))`. Rewrite using `[hs, h c c' _ hQ, smul_comm]`.
-/
theorem tied_on_models : TiedOnModels := by
  intro D u C O i hi ν h K _ σ lam n hw c c' J z hJ sh hn P hP
  have hs : C.sharp i (evG (O.frm i) sh σ P) = frPoly O i (MvPolynomial.map σ P * ∏ τ, frDet ℂ (D.R.N i) τ ^ n τ) := by
    have h1 := mulFun_evG (fr := O.frm i) (fun y => (O.frm_range i hi.le _).1 ⟨y, rfl⟩) σ sh (C.sSharp i) n hn P
    have e1 : (fun y => ∏ τ, (O.frm i y τ).det ^ C.sSharp i τ) = fun y => ∏ τ, (C.de i y τ) ^ (C.sSharp i τ) := by
      funext y; simp only [O.frm_de i hi.le]
    rw [e1] at h1
    exact h1
  have hQ : MvPolynomial.map σ P * ∏ τ, frDet ℂ (D.R.N i) τ ^ n τ ∈ WtPol ℂ ν := by
    have h2 := vv_in_weight ℂ D.what₂.Tau _ lam n (MvPolynomial.map σ P) (map_mem_VV σ lam P hP)
    have e : (fun τ r => (lam τ).natW r + n τ) = ν := by funext τ r; exact hw τ r
    rwa [e] at h2
  rw [chain_char_eval D u C O i hi K σ c c' J z hJ sh n hn P]
  show z • ((C.rhoDet i c * C.rhoDet' i c') • C.divDe i (C.unf i c c' (C.sharp i (evG (O.frm i) sh σ P)))) =
    (C.rhoDet i c * C.rhoDet' i c') • z • C.divDe i (unfC O i (O.Th i c c') (C.sharp i (evG (O.frm i) sh σ P)))
  rw [hs, h c c' _ hQ, smul_comm]

/- English proof (translation)
Introduce `D u C O i hi ν h φ Q hQm hQ c' y'`. Rewrite using `[GL3Theta.lift_eqC D C O.mt O.dt O.c13 i hi φ c', Finset.sum_apply]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, smul_eq_mul, ColumnChain.divDe, mulFun, LinearMap.coe_mk, AddHom.coe_mk, hQ c, h c c' (Q c) (hQm c)]`. Rewrite using `[← unfolding_char_formula D u C O i hi.le]`.

Both sides reduce to the same expression.
-/
theorem lift_formula_compatible : LiftFormulaTied := by
  intro D u C O i hi ν h φ Q hQm hQ c' y'
  rw [GL3Theta.lift_eqC D C O.mt O.dt O.c13 i hi φ c', Finset.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, ColumnChain.divDe, mulFun, LinearMap.coe_mk, AddHom.coe_mk, hQ c, h c c' (Q c) (hQm c)]
  rw [← unfolding_char_formula D u C O i hi.le]
  rfl

end Unf

section Comb

/- English proof (translation)
Unfold `TaylorLogMetric.taylor`. Establish `h1 : (fun z => ∑ k, r k * F k z) = fun z => ∑ k ∈ Finset.univ, r k • F k z` using `rfl`. Rewrite using `[h1, iteratedFDeriv_sum (fun k _ => (hF k _).const_smul (r k)), Finset.sum_apply, _root_.sum_apply, Finset.sum_div]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `e : (fun x => r k • F k x) = r k • F k` using `rfl`.

Rewrite using `[e, iteratedFDeriv_const_smul_apply ((hF k _).contDiffAt), _root_.smul_apply, smul_eq_mul, mul_div_assoc]`.
-/
theorem taylor_sum (D : D7) {N N' n : ℕ} (r : Fin n → ℂ) (F : Fin n → TaylorLogMetric.VC D N N' → ℂ) (hF : ∀ k (m : ℕ), ContDiff ℂ m (F k))
    (α : TaylorLogMetric.Mono D N N') : TaylorLogMetric.taylor D (fun z => ∑ k, r k * F k z) α = ∑ k, r k * TaylorLogMetric.taylor D (F k) α := by
  unfold TaylorLogMetric.taylor
  have h1 : (fun z => ∑ k, r k * F k z) = fun z => ∑ k ∈ Finset.univ, r k • F k z := rfl
  rw [h1, iteratedFDeriv_sum (fun k _ => (hF k _).const_smul (r k)), Finset.sum_apply, _root_.sum_apply, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : (fun x => r k • F k x) = r k • F k := rfl
  rw [e, iteratedFDeriv_const_smul_apply ((hF k _).contDiffAt), _root_.smul_apply, smul_eq_mul, mul_div_assoc]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [lamC_of_mem lam (zero_mem _), show (⟨0, zero_mem _⟩ : TaylorLogMetric.Qbar) = 0 from rfl]`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, lamC_add lam (h a (Finset.mem_insert_self _ _)) (sum_mem fun k hk => h k (Finset.mem_insert_of_mem hk)), ih fun k hk => h k (Finset.mem_insert_of_mem hk)]`.
-/
theorem lamC_sum {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {κ : Type} (s : Finset κ) (f : κ → ℂ) (h : ∀ k ∈ s, f k ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam (∑ k ∈ s, f k) = ∑ k ∈ s, TaylorLogMetric.lamC lam (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [lamC_of_mem lam (zero_mem _), show (⟨0, zero_mem _⟩ : TaylorLogMetric.Qbar) = 0 from rfl]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      lamC_add lam (h a (Finset.mem_insert_self _ _)) (sum_mem fun k hk => h k (Finset.mem_insert_of_mem hk)),
      ih fun k hk => h k (Finset.mem_insert_of_mem hk)]

/- English proof (translation)
Introduce `D cc δ e hT S N N' L L' Θ hA hK p _ lam hp`. Take `⟨n, r, t, hr, hi, ht, hΘ⟩` from `hK`. Take `⟨hsm, halg⟩` from `hT N N' L L' hA`. Use `⟨n, fun k => TaylorLogMetric.lamC lam (r k), t, fun _ => L, fun _ => L', fun k => hi k p lam hp, fun k => ?_, fun _ => ⟨hA, ⟨1, Nat.coprime_one_left p, fun x hx => by simpa using hx, fun x hx => by simpa using hx⟩, ⟨1, Nat.coprime_one_left p, fun x hx => by simpa using hx, fun x …` and prove the remaining obligations. Take `⟨a, ha, hq, hm⟩` from `ht k`.

Use `⟨a, ha, ?_, hm⟩` and prove the remaining obligations. Rewrite using `[Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Fact.out]`. Conclude with `fun hd => hp (hq p Fact.out hd)`. Establish `hU : ∀ k (m : ℕ), ContDiff ℂ m (TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc δ) (t k) (e N N' L L'))` using `fun k m => by`. Rewrite using `[U_eq]`.

Conclude with `contDiff_opU (ι := D.what₂.Tau) (formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N N') (t k) (e N N' L L') m (hsm m)`. Establish `hq : ∀ k α, TaylorLogMetric.taylor D (TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc δ) (t k) (e N N' L L')) α ∈ TaylorLogMetric.Qbar` using `fun k α => halg (t k) (by obtain ⟨a, ha, -, hm⟩ := ht k; exact ⟨a, ha, hm⟩) α`. Use extensionality with `α`. Rewrite using `[map_sum]`. Establish `h1 : MvPowerSeries.coeff α (TaylorLogMetric.pSer D lam Θ) = TaylorLogMetric.lamC lam (TaylorLogMetric.taylor D Θ α)` using `rfl`.

Rewrite using `[h1, hΘ, taylor_sum D r _ hU, lamC_sum lam _ _ fun k _ => mul_mem (hr k) (hq k α)]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[lamC_mul lam (hr k) (hq k α), MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, MvPowerSeries.coeff_C_mul]`. Both sides reduce to the same expression.
-/
theorem kernel_combination_form : KerCombOf := by
  intro D cc δ e hT S N N' L L' Θ hA hK p _ lam hp
  obtain ⟨n, r, t, hr, hi, ht, hΘ⟩ := hK
  obtain ⟨hsm, halg⟩ := hT N N' L L' hA
  refine ⟨n, fun k => TaylorLogMetric.lamC lam (r k), t, fun _ => L, fun _ => L', fun k => hi k p lam hp, fun k => ?_,
    fun _ => ⟨hA, ⟨1, Nat.coprime_one_left p, fun x hx => by simpa using hx, fun x hx => by simpa using hx⟩,
      ⟨1, Nat.coprime_one_left p, fun x hx => by simpa using hx, fun x hx => by simpa using hx⟩⟩, ?_⟩
  · obtain ⟨a, ha, hq, hm⟩ := ht k
    refine ⟨a, ha, ?_, hm⟩
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Fact.out]
    exact fun hd => hp (hq p Fact.out hd)
  · have hU : ∀ k (m : ℕ), ContDiff ℂ m (TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc δ) (t k) (e N N' L L')) := fun k m => by
      rw [U_eq]
      exact contDiff_opU (ι := D.what₂.Tau) (formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N N') (t k) (e N N' L L') m (hsm m)
    have hq : ∀ k α, TaylorLogMetric.taylor D (TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc δ) (t k) (e N N' L L')) α ∈ TaylorLogMetric.Qbar := fun k α =>
      halg (t k) (by obtain ⟨a, ha, -, hm⟩ := ht k; exact ⟨a, ha, hm⟩) α
    ext α
    rw [map_sum]
    have h1 : MvPowerSeries.coeff α (TaylorLogMetric.pSer D lam Θ) = TaylorLogMetric.lamC lam (TaylorLogMetric.taylor D Θ α) := rfl
    rw [h1, hΘ, taylor_sum D r _ hU, lamC_sum lam _ _ fun k _ => mul_mem (hr k) (hq k α)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [lamC_mul lam (hr k) (hq k α), MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, MvPowerSeries.coeff_C_mul]
    rfl

end Comb

section Ent

/- English proof (translation)
Introduce `D L hT Gi Gl K Y cX ex t u μ i hi φ Q hQm hQ c' y'`. Rewrite using `[lift_formula_compatible D u _ (t.O u μ) i hi _ (t.unf u μ i hi) φ Q hQm hQ c' y']`. Simplify using `only [t.O_Th]`. Both sides reduce to the same expression.
-/
theorem compatible_lift_exists : TiedLift := by
  intro D L hT Gi Gl K Y cX ex t u μ i hi φ Q hQm hQ c' y'
  rw [lift_formula_compatible D u _ (t.O u μ) i hi _ (t.unf u μ i hi) φ Q hQm hQ c' y']
  simp only [t.O_Th]
  rfl

end Ent

section Tests

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)}

end Tests

section Cons

/- English proof (translation)
Introduce `D X u C r s A cc δ e S0 i hyp hT c c' hA p _ lam hp`. Conclude with `kernel_combination_form D cc δ e hT S0 _ _ _ _ _ hA (reading_is_kernel D X u C r s A _ e S0 i hyp c c') p lam hp`.
-/
theorem first_kernel_law_reading : FirstKernelLawReading := by
  intro D X u C r s A cc δ e S0 i hyp hT c c' hA p _ lam hp
  exact kernel_combination_form D cc δ e hT S0 _ _ _ _ _ hA (reading_is_kernel D X u C r s A _ e S0 i hyp c c') p lam hp

/- English proof (translation)
Introduce `E _ _ _ ι _ a b emb δ d sc AA0 N N' h`. Use `⟨herm_HV sc, fun x hx y hy => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Establish `: x ∈ dualLat (HV sc) (LamC emb δ AA0 N N')` using `by rw [h.1]; exact hx`. Conclude with `this y hy`. Conclude with `int_of_sign (h.2.1 x hx)`.
-/
theorem lattice_integral_of_facts : LatIntOfFacts := by
  intro E _ _ _ ι _ a b emb δ d sc AA0 N N' h
  refine ⟨herm_HV sc, fun x hx y hy => ?_, fun x hx => ?_⟩
  · have : x ∈ dualLat (HV sc) (LamC emb δ AA0 N N') := by rw [h.1]; exact hx
    exact this y hy
  · exact int_of_sign (h.2.1 x hx)

/- English proof (translation)
Introduce `D X s cc δ B χ cD`. Use `⟨rfl, fun a b N N' => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `z`. Use `show B.eNat χ a b (s.lat N) (s.lat N') (fun τ => z (s.iT (s.iT.symm τ))) = _`. Use `congr 1`.

Use function extensionality and compare the values at `τ`. Rewrite using `[Equiv.apply_symm_apply]`.
-/
theorem ambient_of_hypotheses : AmbOfHyp := by
  intro D X s cc δ B χ cD
  refine ⟨rfl, fun a b N N' => ?_⟩
  funext z
  show B.eNat χ a b (s.lat N) (s.lat N') (fun τ => z (s.iT (s.iT.symm τ))) = _
  congr 1
  funext τ
  rw [Equiv.apply_symm_apply]

end Cons

section Tests2

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)}

/- English proof (translation)
Establish `h : ∀ (n : ℕ) (_ : n = 0) (m : Fin n → TaylorLogMetric.VC D N N'), iteratedFDeriv ℂ n Θ 0 m = Θ 0`. Introduce `n hn m`. Substitute `hn` using the available equality. Simplify using the standard rewrite rules. Unfold `TaylorLogMetric.taylor`.

Rewrite using `[h _ (by simp)]`. Simplify using the standard rewrite rules.
-/
theorem taylor_zero {N N' : ℕ} (Θ : TaylorLogMetric.VC D N N' → ℂ) : TaylorLogMetric.taylor D Θ 0 = Θ 0 := by
  have h : ∀ (n : ℕ) (_ : n = 0) (m : Fin n → TaylorLogMetric.VC D N N'), iteratedFDeriv ℂ n Θ 0 m = Θ 0 := by
    intro n hn m; subst hn; simp
  unfold TaylorLogMetric.taylor
  rw [h _ (by simp)]
  simp

end Tests2

section SeamLatS

open Formalism.L2.Col

variable {D : D7} {X : Fields} (s : Seam D X) {a b : ℕ}

def matOf (y : HomE X.E a b) : Matrix (Fin b) (Fin a) D.host.E := fun i j => s.iE (y (Pi.single j 1) i)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Establish `hn : n = ∑ j, n j • (Pi.single j (1 : X.E) : Sp X.E a)`. Use extensionality with `k`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Use `conv_rhs => rw [hn]`.

Simplify using `only [Matrix.mulVec, dotProduct, matOf, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_mul]`. Conclude with `Finset.sum_congr rfl fun j _ => mul_comm _ _`.
-/
theorem matOf_mulVec (y : HomE X.E a b) (n : Sp X.E a) : (matOf s y).mulVec (fun j => s.iE (n j)) = fun i => s.iE (y n i) := by
  funext i
  have hn : n = ∑ j, n j • (Pi.single j (1 : X.E) : Sp X.E a) := by
    ext k; simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hn]
  simp only [Matrix.mulVec, dotProduct, matOf, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/- English proof (translation)
Use `Submodule.subset_span fun v hv => ?_` and prove the remaining obligations. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem v hv`. Take `⟨n, hn, rfl⟩` from `hv`. Rewrite using `[matOf_mulVec]`.

Conclude with `Submodule.subset_span ⟨y n, hy n hn, rfl⟩`. Consider the case `zero => rw [Matrix.mulVec_zero]`. Conclude with `zero_mem _`. Consider the case `add v w _ _ h1 h2 => rw [Matrix.mulVec_add]`. Conclude with `add_mem h1 h2`.

Consider the case `smul o v _ h => rw [Matrix.mulVec_smul]`. Conclude with `Submodule.smul_mem _ o h`.
-/
theorem matOf_mem (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) {y : HomE X.E a b} (hy : y ∈ homO N N') :
    matOf s y ∈ TaylorLogMetric.homL D (s.lat N) (s.lat N') := by
  refine Submodule.subset_span fun v hv => ?_
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨n, hn, rfl⟩ := hv
    rw [matOf_mulVec]
    exact Submodule.subset_span ⟨y n, hy n hn, rfl⟩
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add v w _ _ h1 h2 => rw [Matrix.mulVec_add]; exact add_mem h1 h2
  | smul o v _ h => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ o h

/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Use `show δ * s.σ₀ (X.emb (s.iT.symm τ) ((r • y) (Pi.single j 1) i)) = _`. Rewrite using `[hok.1, Equiv.apply_symm_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_mul]`. Both sides reduce to the same expression.
-/
theorem pt_embH (hok : s.Ok) (δ : ℂ) (r : X.E) (y : HomE X.E a b) :
    s.pt (embH (X.embC s.σ₀) δ (r • y)) = fun τ i j => δ * (TaylorLogMetric.embT D τ (s.iE r) * TaylorLogMetric.embT D τ (matOf s y i j)) := by
  funext τ i j
  show δ * s.σ₀ (X.emb (s.iT.symm τ) ((r • y) (Pi.single j 1) i)) = _
  rw [hok.1, Equiv.apply_symm_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_mul]
  rfl

/- English proof (translation)
Introduce `D X s cc δ B χ cD hok a b N N' t ht`. Take `⟨x, hx, rfl⟩` from `ht`. Establish `hadd : ∀ x y : HomE X.E a b, s.pt (embH (X.embC s.σ₀) δ (x + y)) = s.pt (embH (X.embC s.σ₀) δ x) + s.pt (embH (X.embC s.σ₀) δ y)`. Introduce `x y`. Rewrite using `[map_add]`.

Both sides reduce to the same expression. Establish `hzero : s.pt (embH (X.embC s.σ₀) δ (0 : HomE X.E a b)) = 0` using `by rw [map_zero]; rfl`. Establish `hgen : ∀ c ∈ cc, ∀ t0 ∈ D.host.AA0, ∀ y ∈ homO N N', s.pt (embH (X.embC s.σ₀) δ ((s.iE.symm ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t0)) • y)) ∈ TaylorLogMetric.La D B.tor (s.lat N) (s.lat N')`. Introduce `c hc t0 ht0 y hy`. Use `AddSubgroup.subset_closure ⟨δ * D.host.φ₀ (((c : D.host.K) : D.host.E)), AddSubgroup.subset_closure ⟨c, hc, rfl⟩, t0 • matOf s y, Submodule.subset_span ⟨t0, ht0, matOf s y, matOf_mem s N N' hy, rfl⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[pt_embH s hok]`. Use function extensionality and compare the values at `τ i j`. Rewrite using `[RingEquiv.apply_symm_apply, map_mul, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.embT_K D τ _ (c : D.host.K).2]`. Use `show _ = (δ * D.host.φ₀ (((c : D.host.K) : D.host.E))) * TaylorLogMetric.embT D τ (t0 * matOf s y i j)`. Rewrite using `[map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hsw : ∀ (o : 𝓞 X.E) (r : X.E) (y : HomE X.E a b), (o • r) • y = r • (o • y)`. Introduce `o r y`. Use `LinearMap.ext fun v => funext fun i => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.smul_apply, Pi.smul_apply, Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hAA : ∀ r ∈ (ambOf s B χ cD : Amb X).AA, ∀ y ∈ homO N N', s.pt (embH (X.embC s.σ₀) δ (r • y)) ∈ TaylorLogMetric.La D B.tor (s.lat N) (s.lat N')`. Introduce `r hr`. Proceed by induction on `hr using Submodule.closure_induction with`. Consider the case `zero => intro y _`.

Rewrite using `[zero_smul, hzero]`. Conclude with `zero_mem _`. Consider the case `add r1 r2 _ _ h1 h2 => intro y hy`. Rewrite using `[add_smul, hadd]`. Conclude with `add_mem (h1 y hy) (h2 y hy)`.

Consider the case `smul_mem o r hr`. Take `⟨c, hc, t0, ht0, rfl⟩` from `hr`. Introduce `y hy`. Rewrite using `[hsw]`. Conclude with `hgen c hc t0 ht0 _ ((homO N N').smul_mem o hy)`.

Establish `hx' : x ∈ perO (ambOf s B χ cD : Amb X).AA N N'` using `hx`. Use `show s.pt (embH (X.embC s.σ₀) δ x) ∈ _`. Proceed by induction on `hx' using Submodule.closure_induction with`. Consider the case `zero => rw [hzero]`. Conclude with `zero_mem _`.

Consider the case `add x1 x2 _ _ h1 h2 => rw [hadd]; exact add_mem (h1 (by assumption)) (h2 (by assumption))`. Consider the case `smul_mem o z hz`. Take `⟨r, hr, y, hy, rfl⟩` from `hz`. Establish `e : o • (r • y) = r • (o • y)` using `by rw [← hsw, smul_assoc]`. Rewrite using `[e]`.

Conclude with `hAA r hr _ ((homO N N').smul_mem o hy)`.
-/
theorem gluing_lattice_eq : SeamLat := by
  intro D X s cc δ B χ cD hok a b N N' t ht
  obtain ⟨x, hx, rfl⟩ := ht
  have hadd : ∀ x y : HomE X.E a b, s.pt (embH (X.embC s.σ₀) δ (x + y)) = s.pt (embH (X.embC s.σ₀) δ x) + s.pt (embH (X.embC s.σ₀) δ y) := by
    intro x y; rw [map_add]; rfl
  have hzero : s.pt (embH (X.embC s.σ₀) δ (0 : HomE X.E a b)) = 0 := by rw [map_zero]; rfl
  have hgen : ∀ c ∈ cc, ∀ t0 ∈ D.host.AA0, ∀ y ∈ homO N N',
      s.pt (embH (X.embC s.σ₀) δ ((s.iE.symm ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t0)) • y)) ∈ TaylorLogMetric.La D B.tor (s.lat N) (s.lat N') := by
    intro c hc t0 ht0 y hy
    refine AddSubgroup.subset_closure ⟨δ * D.host.φ₀ (((c : D.host.K) : D.host.E)), AddSubgroup.subset_closure ⟨c, hc, rfl⟩,
      t0 • matOf s y, Submodule.subset_span ⟨t0, ht0, matOf s y, matOf_mem s N N' hy, rfl⟩, ?_⟩
    rw [pt_embH s hok]
    funext τ i j
    rw [RingEquiv.apply_symm_apply, map_mul, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.embT_K D τ _ (c : D.host.K).2]
    show _ = (δ * D.host.φ₀ (((c : D.host.K) : D.host.E))) * TaylorLogMetric.embT D τ (t0 * matOf s y i j)
    rw [map_mul]; ring
  have hsw : ∀ (o : 𝓞 X.E) (r : X.E) (y : HomE X.E a b), (o • r) • y = r • (o • y) := by
    intro o r y
    refine LinearMap.ext fun v => funext fun i => ?_
    simp only [LinearMap.smul_apply, Pi.smul_apply, Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply]
    ring
  have hAA : ∀ r ∈ (ambOf s B χ cD : Amb X).AA, ∀ y ∈ homO N N',
      s.pt (embH (X.embC s.σ₀) δ (r • y)) ∈ TaylorLogMetric.La D B.tor (s.lat N) (s.lat N') := by
    intro r hr
    induction hr using Submodule.closure_induction with
    | zero => intro y _; rw [zero_smul, hzero]; exact zero_mem _
    | add r1 r2 _ _ h1 h2 => intro y hy; rw [add_smul, hadd]; exact add_mem (h1 y hy) (h2 y hy)
    | smul_mem o r hr =>
      obtain ⟨c, hc, t0, ht0, rfl⟩ := hr
      intro y hy
      rw [hsw]
      exact hgen c hc t0 ht0 _ ((homO N N').smul_mem o hy)
  have hx' : x ∈ perO (ambOf s B χ cD : Amb X).AA N N' := hx
  show s.pt (embH (X.embC s.σ₀) δ x) ∈ _
  induction hx' using Submodule.closure_induction with
  | zero => rw [hzero]; exact zero_mem _
  | add x1 x2 _ _ h1 h2 => rw [hadd]; exact add_mem (h1 (by assumption)) (h2 (by assumption))
  | smul_mem o z hz =>
    obtain ⟨r, hr, y, hy, rfl⟩ := hz
    have e : o • (r • y) = r • (o • y) := by rw [← hsw, smul_assoc]
    rw [e]
    exact hAA r hr _ ((homO N N').smul_mem o hy)

end SeamLatS

/- English proof (translation)
Introduce `D X s cc δ B χ cD hok hcc hδ a b N N' hA`. Establish `h0` using `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.delta_nonzero_link D cc hcc δ hδ`. Establish `hlat` using `gluing_lattice_eq D X s cc δ B χ cD hok a b N N'`. Establish `hH : ∀ x y : VCx X.Tau a b, HV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ x y = TaylorLogMetric.Hf D B.tor (s.pt x) (s.pt y)`. Introduce `x y`.

Use `HV_push s (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) (s.pt x) (s.pt y)` as an intermediate fact. Rewrite `this` using `[pt_iT, pt_iT]`. Conclude with `this`. Use `⟨herm_HV _, fun x hx y hy => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨p, q, -, hpq⟩` from `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.hermitian_form_integral_values D cc hcc δ hδ h0 a b _ _ hA _ (hlat x hx) _ (hlat y hy)`.

Use `⟨q, ?_⟩` and prove the remaining obligations. Use `show (HV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ x y).im = _`. Rewrite using `[hH, show B.tor = TaylorLogMetric.tor0 D cc δ from rfl, hpq]`. Simplify using the standard rewrite rules. Take `⟨m, hm⟩` from `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.rational_integrality_link D cc hcc δ hδ B a b _ _ hA _ (hlat x hx)`.

Use `⟨m, ?_⟩` and prove the remaining obligations. Use `show Real.sqrt D.host.d / 2 * (HV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ x x).re = _`. Rewrite using `[hH]`. Conclude with `hm`.
-/
theorem lattice_integral_gluing : LatIntSeam := by
  intro D X s cc δ B χ cD hok hcc hδ a b N N' hA
  have h0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.delta_nonzero_link D cc hcc δ hδ
  have hlat := gluing_lattice_eq D X s cc δ B χ cD hok a b N N'
  have hH : ∀ x y : VCx X.Tau a b, HV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ x y = TaylorLogMetric.Hf D B.tor (s.pt x) (s.pt y) := by
    intro x y
    have := HV_push s (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) (s.pt x) (s.pt y)
    rw [pt_iT, pt_iT] at this
    exact this
  refine ⟨herm_HV _, fun x hx y hy => ?_, fun x hx => ?_⟩
  · obtain ⟨p, q, -, hpq⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.hermitian_form_integral_values D cc hcc δ hδ h0 a b _ _ hA _ (hlat x hx) _ (hlat y hy)
    refine ⟨q, ?_⟩
    show (HV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ x y).im = _
    rw [hH, show B.tor = TaylorLogMetric.tor0 D cc δ from rfl, hpq]
    simp
  · obtain ⟨m, hm⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.rational_integrality_link D cc hcc δ hδ B a b _ _ hA _ (hlat x hx)
    refine ⟨m, ?_⟩
    show Real.sqrt D.host.d / 2 * (HV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ x x).re = _
    rw [hH]
    exact hm

section Fin

variable {V : Type} [AddCommGroup V]

/- English proof (translation)
Establish `h1 : (AddSubgroup.toIntSubmodule Λ).FG`. Rewrite using `[Submodule.fg_iff_addSubgroup_fg]`. Simplify using `using h`. Establish `: Module.Finite ℤ (AddSubgroup.toIntSubmodule Λ)` using `Module.Finite.iff_fg.2 h1`. Establish `hN : IsNoetherian ℤ (AddSubgroup.toIntSubmodule Λ)` using `inferInstance`.

Establish `h2 : (AddSubgroup.toIntSubmodule Λ').FG` using `isNoetherian_submodule.1 hN _ (fun x hx => hle hx)`. Rewrite `h2` using `[Submodule.fg_iff_addSubgroup_fg]`. Simplify using `using h2`.
-/
theorem fg_of_le_fg {Λ Λ' : AddSubgroup V} (h : Λ.FG) (hle : Λ' ≤ Λ) : Λ'.FG := by
  have h1 : (AddSubgroup.toIntSubmodule Λ).FG := by
    rw [Submodule.fg_iff_addSubgroup_fg]; simpa using h
  have : Module.Finite ℤ (AddSubgroup.toIntSubmodule Λ) := Module.Finite.iff_fg.2 h1
  have hN : IsNoetherian ℤ (AddSubgroup.toIntSubmodule Λ) := inferInstance
  have h2 : (AddSubgroup.toIntSubmodule Λ').FG := isNoetherian_submodule.1 hN _ (fun x hx => hle hx)
  rw [Submodule.fg_iff_addSubgroup_fg] at h2
  simpa using h2

/- English proof (translation)
Set `f : V →ₗ[ℤ] V` to `(c : ℤ) • LinearMap.id`. Establish `hfx : ∀ x, f x = c • x` using `fun x => by simp [f]`. Establish `hc0 : (c : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hc.ne'`. Establish `hf : Function.Injective f`. Introduce `x y hxy`.

Rewrite `hxy` using `[hfx, hfx, ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ]`. Use `congrArg (fun z => (c : ℂ)⁻¹ • z) hxy` as an intermediate fact. Simplify `this` using `[inv_smul_smul₀ hc0]`. Establish `h1 : ((AddSubgroup.toIntSubmodule A).map f).toAddSubgroup.FG`. Use `fg_of_le_fg h ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Rewrite using `[hfx]`. Conclude with `hk x hx`. Rewrite `h1` using `[← Submodule.fg_iff_addSubgroup_fg]`. Establish `h2` using `Submodule.fg_of_fg_map_injective f hf h1`.

Rewrite `h2` using `[Submodule.fg_iff_addSubgroup_fg]`. Simplify using `using h2`.
-/
theorem fg_of_nsmul [Module ℂ V] {Λ A : AddSubgroup V} (h : Λ.FG) (c : ℕ) (hc : 0 < c) (hk : ∀ x ∈ A, c • x ∈ Λ) : A.FG := by
  let f : V →ₗ[ℤ] V := (c : ℤ) • LinearMap.id
  have hfx : ∀ x, f x = c • x := fun x => by simp [f]
  have hc0 : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have hf : Function.Injective f := by
    intro x y hxy
    rw [hfx, hfx, ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ] at hxy
    have := congrArg (fun z => (c : ℂ)⁻¹ • z) hxy
    simpa [inv_smul_smul₀ hc0] using this
  have h1 : ((AddSubgroup.toIntSubmodule A).map f).toAddSubgroup.FG := by
    refine fg_of_le_fg h ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [hfx]
    exact hk x hx
  rw [← Submodule.fg_iff_addSubgroup_fg] at h1
  have h2 := Submodule.fg_of_fg_map_injective f hf h1
  rw [Submodule.fg_iff_addSubgroup_fg] at h2
  simpa using h2

/- English proof (translation)
Establish `: AddGroup.FG Λ₂` using `(AddGroup.fg_iff_addSubgroup_fg Λ₂).2 hfg`. Establish `ht : IsAddTorsion (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂)`. Introduce `x`. Use `isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨c, hc, ?_⟩` and prove the remaining obligations. Proceed by induction on `x using QuotientAddGroup.induction_on with`.

Consider the case `H y`. Rewrite using `[← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]`. Conclude with `AddSubgroup.mem_addSubgroupOf.2 (hk y y.2)`. Establish `: Finite (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂)` using `AddCommGroup.finite_of_fg_isAddTorsion _ ht`. Conclude with `AddSubgroup.index_ne_zero_of_finite`.
-/
theorem relIdx_ne_zero_of_tor (Λ₁ Λ₂ : AddSubgroup V) (c : ℕ) (hc : 0 < c) (hk : ∀ x ∈ Λ₂, c • x ∈ Λ₁) (hfg : Λ₂.FG) :
    relIdx Λ₁ Λ₂ ≠ 0 := by
  have : AddGroup.FG Λ₂ := (AddGroup.fg_iff_addSubgroup_fg Λ₂).2 hfg
  have ht : IsAddTorsion (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) := by
    intro x
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨c, hc, ?_⟩
    induction x using QuotientAddGroup.induction_on with
    | H y =>
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
      exact AddSubgroup.mem_addSubgroupOf.2 (hk y y.2)
  have : Finite (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) := AddCommGroup.finite_of_fg_isAddTorsion _ ht
  exact AddSubgroup.index_ne_zero_of_finite

end Fin

/- English proof (translation)
Introduce `E _ _ _ ι _ a b emb δ AA0 SS N N' c hc hfg`. Take `⟨tA, tB, tL⟩` from `half_periods_torsion E ι a b emb δ AA0 SS N N' c hc`. Conclude with `⟨relIdx_ne_zero_of_tor _ _ c hc tA (fg_of_nsmul hfg c hc tA), relIdx_ne_zero_of_tor _ _ c hc (fun x hx => tL x hx.1) (fg_of_le_fg hfg inf_le_left), relIdx_ne_zero_of_tor _ _ c hc tB (fg_of_nsmul hfg c hc tB)⟩`.
-/
theorem finite_index_of_fg : IdxOfFG := by
  intro E _ _ _ ι _ a b emb δ AA0 SS N N' c hc hfg
  obtain ⟨tA, tB, tL⟩ := half_periods_torsion E ι a b emb δ AA0 SS N N' c hc
  exact ⟨relIdx_ne_zero_of_tor _ _ c hc tA (fg_of_nsmul hfg c hc tA),
    relIdx_ne_zero_of_tor _ _ c hc (fun x hx => tL x hx.1) (fg_of_le_fg hfg inf_le_left),
    relIdx_ne_zero_of_tor _ _ c hc tB (fg_of_nsmul hfg c hc tB)⟩

section LamFGS

open Formalism.L2.Col Formalism.HermitianLatticesTheory

/- English proof (translation)
Establish `sa` using `stdLat_lattice (E := E) (n := a)`. Establish `sb` using `stdLat_lattice (E := E) (n := b)`. Take `⟨νa₁, ha₁0, ha₁⟩` from `exists_smul_le (stdLat E a) N sa.fg hsN`. Take `⟨νb₁, hb₁0, hb₁⟩` from `exists_smul_le N' (stdLat E b) hN' sb.span_eq_top`. Establish `h1` using `perO_scale AA0 N (stdLat E a) N' (stdLat E b) νa₁ νb₁ ha₁ hb₁`.

Establish `hone : Submodule.span E (((1 : Submodule (𝓞 E) E) : Submodule (𝓞 E) E) : Set E) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `x _`. Establish `h1 : (1 : E) ∈ Submodule.span E (((1 : Submodule (𝓞 E) E) : Submodule (𝓞 E) E) : Set E)` using `Submodule.subset_span (Submodule.one_le.1 le_rfl)`. Use `Submodule.smul_mem _ x h1` as an intermediate fact.

Simplify using `using this`. Take `⟨ν₀, h00, h0⟩` from `exists_smul_le AA0 (1 : Submodule (𝓞 E) E) hAA hone`. Establish `hM₀ : (perO AA0 (stdLat E a) (stdLat E b)).FG`. Use `fg_of_scale _ _ (homO_std_fg (E := E) (a := a) (b := b)) ν₀ h00 ?_` and prove the remaining obligations. Establish `hle : perO AA0 (stdLat E a) (stdLat E b) ≤ (homO (stdLat E a) (stdLat E b)).comap (ν₀ • (LinearMap.id : HomE E a b →ₗ[𝓞 E] HomE E a b))`.

Apply `Submodule.span_le.2` to reduce the goal to its premises. Introduce and unpack `_ ⟨r, hr, x, hx, rfl⟩`. Use `show ν₀ • (r • x) ∈ homO (stdLat E a) (stdLat E b)`. Take `⟨ρ, hρ⟩` from `Submodule.mem_one.1 (h0 r hr)`. Rewrite using `[smul_smul_eq_of (ν₀) r x ρ hρ]`.

Conclude with `Submodule.smul_mem _ ρ hx`. Conclude with `fun x hx => hle hx`. Conclude with `fg_of_scale _ _ hM₀ _ (mul_ne_zero ha₁0 hb₁0) h1`.
-/
theorem perO_fg {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ} (AA0 : Submodule (𝓞 E) E) (N : Submodule (𝓞 E) (Sp E a))
    (N' : Submodule (𝓞 E) (Sp E b)) (hN' : N'.FG) (hsN : Submodule.span E (N : Set (Sp E a)) = ⊤) (hAA : AA0.FG) : (perO AA0 N N').FG := by
  have sa := stdLat_lattice (E := E) (n := a)
  have sb := stdLat_lattice (E := E) (n := b)
  obtain ⟨νa₁, ha₁0, ha₁⟩ := exists_smul_le (stdLat E a) N sa.fg hsN
  obtain ⟨νb₁, hb₁0, hb₁⟩ := exists_smul_le N' (stdLat E b) hN' sb.span_eq_top
  have h1 := perO_scale AA0 N (stdLat E a) N' (stdLat E b) νa₁ νb₁ ha₁ hb₁
  have hone : Submodule.span E (((1 : Submodule (𝓞 E) E) : Submodule (𝓞 E) E) : Set E) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have h1 : (1 : E) ∈ Submodule.span E (((1 : Submodule (𝓞 E) E) : Submodule (𝓞 E) E) : Set E) :=
      Submodule.subset_span (Submodule.one_le.1 le_rfl)
    have := Submodule.smul_mem _ x h1
    simpa using this
  obtain ⟨ν₀, h00, h0⟩ := exists_smul_le AA0 (1 : Submodule (𝓞 E) E) hAA hone
  have hM₀ : (perO AA0 (stdLat E a) (stdLat E b)).FG := by
    refine fg_of_scale _ _ (homO_std_fg (E := E) (a := a) (b := b)) ν₀ h00 ?_
    have hle : perO AA0 (stdLat E a) (stdLat E b) ≤ (homO (stdLat E a) (stdLat E b)).comap
        (ν₀ • (LinearMap.id : HomE E a b →ₗ[𝓞 E] HomE E a b)) := by
      apply Submodule.span_le.2
      rintro _ ⟨r, hr, x, hx, rfl⟩
      show ν₀ • (r • x) ∈ homO (stdLat E a) (stdLat E b)
      obtain ⟨ρ, hρ⟩ := Submodule.mem_one.1 (h0 r hr)
      rw [smul_smul_eq_of (ν₀) r x ρ hρ]
      exact Submodule.smul_mem _ ρ hx
    exact fun x hx => hle hx
  exact fg_of_scale _ _ hM₀ _ (mul_ne_zero ha₁0 hb₁0) h1

/- English proof (translation)
Introduce `E _ _ _ ι _ a b emb δ AA0 N N' hN' hsN hAA`. Establish `hM` using `perO_fg AA0 N N' hN' hsN hAA`. Establish `h1 : Module.Finite (𝓞 E) (perO AA0 N N')` using `Module.Finite.iff_fg.2 hM`. Establish `h2 : Module.Finite ℤ (perO AA0 N N')` using `Module.Finite.trans (𝓞 E) _`. Establish `h3 : AddGroup.FG (perO AA0 N N')` using `Module.Finite.iff_addGroup_fg.1 h2`.

Establish `h4 : (perO AA0 N N').toAddSubgroup.FG` using `(AddGroup.fg_iff_addSubgroup_fg _).1 h3`. Take `⟨S, hS⟩` from `h4`. Use `⟨S.image (embH emb δ), ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.coe_image, ← AddMonoidHom.map_closure, hS]`. Both sides reduce to the same expression.
-/
theorem period_lattice_finitely_generated : LamFG := by
  intro E _ _ _ ι _ a b emb δ AA0 N N' hN' hsN hAA
  have hM := perO_fg AA0 N N' hN' hsN hAA
  have h1 : Module.Finite (𝓞 E) (perO AA0 N N') := Module.Finite.iff_fg.2 hM
  have h2 : Module.Finite ℤ (perO AA0 N N') := Module.Finite.trans (𝓞 E) _
  have h3 : AddGroup.FG (perO AA0 N N') := Module.Finite.iff_addGroup_fg.1 h2
  have h4 : (perO AA0 N N').toAddSubgroup.FG := (AddGroup.fg_iff_addSubgroup_fg _).1 h3
  obtain ⟨S, hS⟩ := h4
  classical
  refine ⟨S.image (embH emb δ), ?_⟩
  rw [Finset.coe_image, ← AddMonoidHom.map_closure, hS]
  rfl

end LamFGS

/- English proof (translation)
Establish `: Fact q.Prime` using `⟨hq⟩`. Use `P.isPrime` as an intermediate fact. Establish `: Finite (𝓞 E ⧸ P.asIdeal)` using `Ideal.finiteQuotientOfFreeOfNeBot P.asIdeal P.ne_bot`. Rewrite `h` using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Take `⟨x, hx⟩` from `exists_prime_addOrderOf_dvd_card' (G := 𝓞 E ⧸ P.asIdeal) q h`.

Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`. Rewrite `hx` using `[addOrderOf_zero]`. Conclude with `hq.one_lt.ne hx`. Establish `h1 : q • x = 0` using `by rw [← hx]; exact addOrderOf_nsmul_eq_zero x`.

Rewrite `h1` using `[nsmul_eq_mul]`. Establish `h2 : ((q : ℕ) : 𝓞 E ⧸ P.asIdeal) = 0` using `(mul_eq_zero.1 h1).resolve_right hx0`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast]`. Conclude with `h2`.
-/
theorem natCast_mem_of_dvd_absNorm {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {q : ℕ} (hq : q.Prime)
    (h : q ∣ Ideal.absNorm P.asIdeal) : (q : 𝓞 E) ∈ P.asIdeal := by
  have : Fact q.Prime := ⟨hq⟩
  have := P.isPrime
  have : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot P.asIdeal P.ne_bot
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := 𝓞 E ⧸ P.asIdeal) q h
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [addOrderOf_zero] at hx
    exact hq.one_lt.ne hx
  have h1 : q • x = 0 := by rw [← hx]; exact addOrderOf_nsmul_eq_zero x
  rw [nsmul_eq_mul] at h1
  have h2 : ((q : ℕ) : 𝓞 E ⧸ P.asIdeal) = 0 := (mul_eq_zero.1 h1).resolve_right hx0
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact h2

/- English proof (translation)
Introduce `D L hT Gi Gl K Y cX ex t u μ`. Take `⟨-, hlev, -⟩` from `t.rd_chain u μ`. Rewrite using `[hlev]`. Use `⟨modulus_pos t.sel (t.tup μ) (t.cst μ) (t.word u) (t.pr_ok.T_prime _).pos, fun q hq hd => ?_⟩` and prove the remaining obligations. Rewrite using `[t.O_S]`.

Establish `key : q ∣ ∏ P : Formalism.L2.Col.rowSG t.Pr t.sel (t.tup μ), Formalism.L2.Col.qOf P.1 → q ∈ insert (D.mem u).A.T (({D.host.g 0, D.host.g 1} : Finset ℕ) ∪ Y.Qp μ)`. Introduce `h`. Take `⟨P, -, hP⟩` from `(Prime.dvd_finsetProd_iff hq.prime _).1 h`. Use `Finset.mem_insert_of_mem ?_` and prove the remaining obligations. Break down `Finset.mem_union.1 P.2 with hG | hQ` into its components or cases.

Use `Finset.mem_union_left _ ?_` and prove the remaining obligations. Break down `Finset.mem_union.1 hG with h0 | h0` into its components or cases. Establish `e : Formalism.L2.Col.qOf P.1 = t.Pr.g 0` using `t.pr_ok.vG_norm 0 P.1 h0`. Rewrite `hP` using `[e]`. Rewrite using `[(Nat.prime_dvd_prime_iff_eq hq (t.pr_ok.g_prime 0)).1 hP, t.g_rec]`.

Simplify using the standard rewrite rules. Establish `e : Formalism.L2.Col.qOf P.1 = t.Pr.g 1` using `t.pr_ok.vG_norm 1 P.1 h0`. Rewrite `hP` using `[e]`. Rewrite using `[(Nat.prime_dvd_prime_iff_eq hq (t.pr_ok.g_prime 1)).1 hP, t.g_rec]`. Simplify using the standard rewrite rules.

Conclude with `Finset.mem_union_right _ ((t.Q_rec μ q).2 ⟨hq, P.1, hQ, natCast_mem_of_dvd_absNorm P.1 hq hP⟩)`. Unfold `levC Formalism.L2.Col.cAof Formalism.L2.Col.cBof at hd`. Break down `(Nat.Prime.dvd_mul hq).1 hd with h | h` into its components or cases. Conclude with `key (hq.dvd_of_dvd_pow h)`. Break down `(Nat.Prime.dvd_mul hq).1 h with h | h` into its components or cases.

Rewrite using `[(Nat.prime_dvd_prime_iff_eq hq (t.pr_ok.T_prime _)).1 h, t.T_rec]`. Conclude with `Finset.mem_insert_self _ _`. Conclude with `key (hq.dvd_of_dvd_pow h)`.
-/
theorem level_structure_counting : LevSNum := by
  classical
  intro D L hT Gi Gl K Y cX ex t u μ
  obtain ⟨-, hlev, -⟩ := t.rd_chain u μ
  rw [hlev]
  refine ⟨modulus_pos t.sel (t.tup μ) (t.cst μ) (t.word u) (t.pr_ok.T_prime _).pos, fun q hq hd => ?_⟩
  rw [t.O_S]
  have key : q ∣ ∏ P : Formalism.L2.Col.rowSG t.Pr t.sel (t.tup μ), Formalism.L2.Col.qOf P.1 →
      q ∈ insert (D.mem u).A.T (({D.host.g 0, D.host.g 1} : Finset ℕ) ∪ Y.Qp μ) := by
    intro h
    obtain ⟨P, -, hP⟩ := (Prime.dvd_finsetProd_iff hq.prime _).1 h
    refine Finset.mem_insert_of_mem ?_
    rcases Finset.mem_union.1 P.2 with hG | hQ
    · refine Finset.mem_union_left _ ?_
      rcases Finset.mem_union.1 hG with h0 | h0
      · have e : Formalism.L2.Col.qOf P.1 = t.Pr.g 0 := t.pr_ok.vG_norm 0 P.1 h0
        rw [e] at hP
        rw [(Nat.prime_dvd_prime_iff_eq hq (t.pr_ok.g_prime 0)).1 hP, t.g_rec]
        simp
      · have e : Formalism.L2.Col.qOf P.1 = t.Pr.g 1 := t.pr_ok.vG_norm 1 P.1 h0
        rw [e] at hP
        rw [(Nat.prime_dvd_prime_iff_eq hq (t.pr_ok.g_prime 1)).1 hP, t.g_rec]
        simp
    · exact Finset.mem_union_right _ ((t.Q_rec μ q).2 ⟨hq, P.1, hQ, natCast_mem_of_dvd_absNorm P.1 hq hP⟩)
  unfold levC Formalism.L2.Col.cAof Formalism.L2.Col.cBof at hd
  rcases (Nat.Prime.dvd_mul hq).1 hd with h | h
  · exact key (hq.dvd_of_dvd_pow h)
  · rcases (Nat.Prime.dvd_mul hq).1 h with h | h
    · rw [(Nat.prime_dvd_prime_iff_eq hq (t.pr_ok.T_prime _)).1 h, t.T_rec]
      exact Finset.mem_insert_self _ _
    · exact key (hq.dvd_of_dvd_pow h)

/- English proof (translation)
Introduce `D L hT Gi Gl K Y cX ex t h hfree u μ i hi`. Take `⟨hAA, h⟩` from `h`. Establish `h1` using `level_structure_counting D L hT Gi Gl K Y cX ex t u μ`. Establish `h2 : ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)), Formalism.L2.Col.IsSdLat ((t.rd u μ).N i c) ∧ Formalism.L2.Col.IsSdLat ((t.rd u μ).N (i + 1) c') ∧ ∀ x, IntOff (t.O u μ).S ((t.rd u μ).Xi i c c' x)` using `fun c c' => by`. Distinguish the cases in `hp : (t.rd u μ).pin (i + 1) c'`.

Conclude with `h u μ i hi c c' hp`. Conclude with `hfree u μ i hi c c' hp`. Take `⟨a1, a2⟩` from `ambient_of_hypotheses D t.X t.seam t.cc t.δ t.B t.χ t.cD`. Use `⟨a1, h1, fun c c' => ?_⟩` and prove the remaining obligations. Take `⟨s1, s2, hx⟩` from `h2 c c'`.

Take `⟨i1, i2, i3⟩` from `finite_index_of_fg _ _ _ _ (t.X.embC t.amb.σ₀) t.amb.δ t.amb.AA (t.rd u μ).SS ((t.rd u μ).N i c) ((t.rd u μ).N (i + 1) c') (t.rd u μ).lev h1.1 (period_lattice_finitely_generated _ _ _ _ _ _ _ _ _ s2.1.fg s1.1.span_eq_top hAA)`. Establish `hA : TaylorLogMetric.admitted D _ _ (t.seam.lat ((t.rd u μ).N i c)) (t.seam.lat ((t.rd u μ).N (i + 1) c'))`. Rewrite using `[← t.O_lat, ← t.O_lat]`. Conclude with `⟨factNEven _ _, factNEven _ _, ((t.O u μ).lat i c).2, ((t.O u μ).lat (i + 1) c').2⟩`. Conclude with `⟨a2 _ _ _ _, gluing_lattice_eq D t.X t.seam t.cc t.δ t.B t.χ t.cD t.seam_ok _ _ _ _, lattice_integral_gluing D t.X t.seam t.cc t.δ t.B t.χ t.cD t.seam_ok t.cc_ok t.δ_ok _ _ _ _ hA, i1, i2, i3, hx⟩`.
-/
theorem hypotheses_of_base_hypotheses : HypOfHyp0 := by
  intro D L hT Gi Gl K Y cX ex t h hfree u μ i hi
  obtain ⟨hAA, h⟩ := h
  have h1 := level_structure_counting D L hT Gi Gl K Y cX ex t u μ
  have h2 : ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)), Formalism.L2.Col.IsSdLat ((t.rd u μ).N i c) ∧
      Formalism.L2.Col.IsSdLat ((t.rd u μ).N (i + 1) c') ∧ ∀ x, IntOff (t.O u μ).S ((t.rd u μ).Xi i c c' x) := fun c c' => by
    by_cases hp : (t.rd u μ).pin (i + 1) c'
    · exact h u μ i hi c c' hp
    · exact hfree u μ i hi c c' hp
  obtain ⟨a1, a2⟩ := ambient_of_hypotheses D t.X t.seam t.cc t.δ t.B t.χ t.cD
  refine ⟨a1, h1, fun c c' => ?_⟩
  obtain ⟨s1, s2, hx⟩ := h2 c c'
  obtain ⟨i1, i2, i3⟩ := finite_index_of_fg _ _ _ _ (t.X.embC t.amb.σ₀) t.amb.δ t.amb.AA (t.rd u μ).SS ((t.rd u μ).N i c) ((t.rd u μ).N (i + 1) c')
    (t.rd u μ).lev h1.1 (period_lattice_finitely_generated _ _ _ _ _ _ _ _ _ s2.1.fg s1.1.span_eq_top hAA)
  have hA : TaylorLogMetric.admitted D _ _ (t.seam.lat ((t.rd u μ).N i c)) (t.seam.lat ((t.rd u μ).N (i + 1) c')) := by
    rw [← t.O_lat, ← t.O_lat]
    exact ⟨factNEven _ _, factNEven _ _, ((t.O u μ).lat i c).2, ((t.O u μ).lat (i + 1) c').2⟩
  exact ⟨a2 _ _ _ _, gluing_lattice_eq D t.X t.seam t.cc t.δ t.B t.χ t.cD t.seam_ok _ _ _ _,
    lattice_integral_gluing D t.X t.seam t.cc t.δ t.B t.χ t.cD t.seam_ok t.cc_ok t.δ_ok _ _ _ _ hA, i1, i2, i3, hx⟩

/- English proof (translation)
Introduce `D cc δ B χ hcc hδ h0 hS hA N N' L L' hAdm`. Use `⟨fun k => ?_, hA N N' L L' hAdm⟩` and prove the remaining obligations. Establish `h1` using `(B.thMoved_mem (B.latAll hcc hδ h0) (B.thZeroMem hS N N') hAdm).1`. Establish `h2 : ContDiff ℂ k (B.thMoved N N' L L')` using `h1.contDiff`. Conclude with `contDiff_const.mul h2`.
-/
theorem transcendence_algebraic_eigen : TransAlgENat := by
  intro D cc δ B χ hcc hδ h0 hS hA N N' L L' hAdm
  refine ⟨fun k => ?_, hA N N' L L' hAdm⟩
  have h1 := (B.thMoved_mem (B.latAll hcc hδ h0) (B.thZeroMem hS N N') hAdm).1
  have h2 : ContDiff ℂ k (B.thMoved N N' L L') := h1.contDiff
  exact contDiff_const.mul h2

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[O.lattice_integral_coordinates]`. Simplify using `only [StandardLatticesGL3.stdL, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]`. Use `forall_congr' fun k => ⟨fun h => ⟨⟨x k, h⟩, rfl⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨y, hy⟩`.

Rewrite using `[← hy]`. Conclude with `NumberField.RingOfIntegers.isIntegral_coe y`.
-/
theorem initial_lattice_eq_standard {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} (O : GL3Theta.LiftObj D C) (j : ℕ) :
    (O.L0 j).1 = StandardLatticesGL3.stdL D (D.R.N j) := by
  ext x
  rw [O.lattice_integral_coordinates]
  simp only [StandardLatticesGL3.stdL, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
  refine forall_congr' fun k => ⟨fun h => ⟨⟨x k, h⟩, rfl⟩, ?_⟩
  rintro ⟨y, hy⟩
  rw [← hy]
  exact NumberField.RingOfIntegers.isIntegral_coe y

section JetX

open MvPolynomial Formalism.L2.DIV

end JetX

namespace Test

open MvPolynomial Formalism.L2.DIV

abbrev Fr (n : ℕ) : Type := {f : Unit → Matrix (Fin n) (Fin n) ℂ // ∀ τ, (f τ).det ≠ 0}

def frV (n : ℕ) : Fr n → Unit → Matrix (Fin n) (Fin n) ℂ := Subtype.val

def nu10 : Unit → Fin 2 → ℕ := fun _ r => if r = 0 then 1 else 0

def firstFrameCoordinate : Pol ℂ Unit 2 := X ((), 0, 0)

def Th1 : VCx Unit 2 3 → ℂ := fun z => 1 + z () 0 0

def complementLatticeOfDatum : VCx Unit 2 3 →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 0).comp
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => Fin 2 → ℂ) 0).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Unit => Fin 3 → Fin 2 → ℂ) ()))

end Test

namespace Test

def x3 : ℂ := ⟨1 / 3, 0⟩

def y3 : ℂ := ⟨0, 1 / 3⟩

end Test

end Formalism.L2.Ker
