import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCStmt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MajorantIntegrals
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LatticeSummability
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelSizesJointMean
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PeriodLatticeFactsSplitOfGeneral
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocalConditionsAndQuotientSplitting
import Lemmata.GeneralBFactRightSide.Imports

namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology NumberField MeasureTheory
open scoped Pointwise

noncomputable section

open Classical

namespace Lat

/- English proof (translation)
Unfold `S6.rd`. Apply `Real.one_le_rpow _ (by positivity)` to reduce the goal to its premises. Establish `h` using `NumberField.discr_ne_zero E`. Establish `: (1 : ℤ) ≤ |discr E|` using `Int.one_le_abs h`. Conclude with `this` after adjusting the coercions.
-/
theorem rd_ge_one (E : Type) [Field E] [NumberField E] : 1 ≤ S6.rd E := by
  unfold S6.rd
  apply Real.one_le_rpow _ (by positivity)
  have h := NumberField.discr_ne_zero E
  have : (1 : ℤ) ≤ |discr E| := Int.one_le_abs h
  exact_mod_cast this

/- English proof (translation)
Introduce `Cs hCs`. Use `⟨Cs, hCs, ?_⟩` and prove the remaining obligations. Introduce `E _ _ _ Wp Wq _ _ _ _ S hg1 hg2 hU b n hb hn hthr`. Take `⟨-, hcard, hdeg⟩` from `Formalism.FourierDecayAlt.P.degreeFacts_statement E`. Establish `hf : S.f = S6.deg E`.

Rewrite using `[← hcard, ← Fintype.card_fin S.f]`. Conclude with `Fintype.card_congr S.pl`. Establish `hfpos : 0 < S.f` using `hf ▸ hdeg`. Establish `: Nonempty (Fin S.f)` using `⟨⟨0, hfpos⟩⟩`. Establish `hgN : 0 < S.g` using `Nat.mul_pos hg1 hg2`.

Establish `hg1R : (1 : ℝ) ≤ S.g` using `by exact_mod_cast hgN`. Establish `hgR : (0 : ℝ) < S.g` using `by linarith`. Establish `hrd1` using `rd_ge_one E`. Establish `hrd : 0 < S6.rd E` using `by linarith`. Take `⟨-, -, -, -, -, -, hN, -⟩` from `Formalism.FourierDecayAlt.P.block_lattices Formalism.FourierDecayAlt.P.lattice_facts_general Formalism.FourierDecayAlt.P.dualIdealEqLiftIdeal Formalism.FourierDecayAlt.P.scaledIdealNorm E hU S.g S.G.r b n hgN`.

Use `set ν : ℤ := S6.nuBlock S.G.r b n with hν`. Use `set x : ℝ := S6.rd E ^ ν with hx`. Establish `hxpos : 0 < x` using `zpow_pos hrd _`. Establish `hexp : ((2 * S.G.r + 4 : ℤ) - 2 * b - n) = ν + 1`. Simplify using `only [hν, S6.nuBlock]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `hN` using `[hexp, zpow_add₀ hrd.ne', zpow_one]`. Use `set m : ℝ := Finset.univ.inf' Finset.univ_nonempty (thr S b n) with hm`. Establish `hmpos : 0 < m`. Rewrite using `[hm, Finset.lt_inf'_iff]`.

Conclude with `fun v _ => hthr v`. Establish `hmle : ∀ v, m ≤ thr S b n v` using `fun v => Finset.inf'_le _ (Finset.mem_univ v)`. Use `⟨S.g / m, div_pos hgR hmpos, ?_⟩` and prove the remaining obligations. Use `set R : ℝ := S.g / m with hR`. Establish `hRpos : 0 < R` using `div_pos hgR hmpos`.

Use `set Nn : ℝ := (FractionalIdeal.absNorm (S6.dualIdl E S.g ν) : ℝ) with hNn`. Establish `hNn0 : 0 ≤ Nn`. Establish `: 0 < √Nn` using `by rw [hN]; positivity`. Conclude with `(Real.sqrt_pos.mp this).le`. Establish `hNinv : Nn⁻¹ = ((S.g : ℝ) * (x * S6.rd E)) ^ (2 * S.f)`.

Establish `h2 : Nn = (√Nn) ^ 2` using `(Real.sq_sqrt hNn0).symm`. Rewrite using `[h2, hN, ← hf]`. Rewrite using `[inv_pow, inv_inv, ← pow_mul, mul_comm S.f 2]`. Establish `hvol : S.base.vol b n = (∏ v, thr S b n v) ^ 2 * Nn⁻¹`. Simplify using `only [C.HidaSetting.base, C.HidaSetting.mkData, thr]`.

Rewrite using `[div_eq_mul_inv]`. Use `congr 2`. Conclude with `(Equiv.prod_comp S.pl (fun w => J.thrS S.G S.CA S.de S.de' S.T S.T' S.l b n w)).symm`. Establish `hdlB : KB.dlB S b n = x ^ 2 * (S6.rd E * (S.g : ℝ) ^ 3 / 2)`. Establish `e : S6.rd E ^ (2 * ν) = x ^ 2` using `by rw [hx, ← zpow_natCast, ← zpow_mul]; ring_nf`.

Simplify using `only [KB.dlB, D.deG]`. Rewrite using `[← hν, e]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hvol, hNinv, hdlB]`. Establish `key : ∀ v, x ^ 2 * (S6.rd E * (S.g : ℝ) ^ 3 / 2) * (Cs * (1 + (R * thr S b n v / S.g) ^ 2)) / R ^ 2 ≤ Cs * (thr S b n v ^ 2 * ((S.g : ℝ) * (x * S6.rd E)) ^ 2)`.

Introduce `v`. Establish `ht` using `hthr v`. Establish `h1 : (1 + (R * thr S b n v / S.g) ^ 2) / R ^ 2 ≤ 2 * thr S b n v ^ 2 / (S.g : ℝ) ^ 2`. Rewrite using `[div_le_div_iff₀ (by positivity) (by positivity)]`. Establish `hR' : R * m = S.g` using `by rw [hR]; field_simp`.

Establish `hmt : m ^ 2 ≤ thr S b n v ^ 2` using `pow_le_pow_left₀ hmpos.le (hmle v) 2`. Establish `: (S.g : ℝ) ^ 2 ≤ R ^ 2 * thr S b n v ^ 2`. Rewrite using `[← hR']`. Use polynomial arithmetic with `[sq_nonneg R]`. Establish `e : (1 + (R * thr S b n v / S.g) ^ 2) * (S.g : ℝ) ^ 2 = (S.g : ℝ) ^ 2 + R ^ 2 * thr S b n v ^ 2` using `by field_simp`.

Apply the tactic sequence `rw [e] <;> nlinarith`. Combine the equalities or inequalities in the displayed calculation. Clear the denominators using the available nonvanishing facts. Use `_ ≤ Cs * (thr S b n v ^ 2 * ((S.g : ℝ) * (x * S6.rd E)) ^ 2) * 1 := by`. Apply `mul_le_mul_of_nonneg_left _ (by positivity)` to reduce the goal to its premises.

Apply the tactic sequence `rw [div_le_one (by positivity)] <;> nlinarith`. Use `_ = _ := mul_one _`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Rewrite using `[pow_mul]`.

Use `_ ≤ ∏ v, Cs * (thr S b n v ^ 2 * ((S.g : ℝ) * (x * S6.rd E)) ^ 2) := Finset.prod_le_prod (fun v _ => by have := hthr v; positivity) (fun v _ => key v)`. Use `_ = Cs ^ S.f * ((∏ v, thr S b n v) ^ 2 * ((S.g : ℝ) * (x * S6.rd E)) ^ (2 * S.f)) := by`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm 2 S.f]`.
-/
theorem sizesSup : PBC.SizesSup := by
  intro Cs hCs
  refine ⟨Cs, hCs, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ S hg1 hg2 hU b n hb hn hthr
  obtain ⟨-, hcard, hdeg⟩ := Formalism.FourierDecayAlt.P.degreeFacts_statement E
  have hf : S.f = S6.deg E := by
    rw [← hcard, ← Fintype.card_fin S.f]; exact Fintype.card_congr S.pl
  have hfpos : 0 < S.f := hf ▸ hdeg
  have : Nonempty (Fin S.f) := ⟨⟨0, hfpos⟩⟩
  have hgN : 0 < S.g := Nat.mul_pos hg1 hg2
  have hg1R : (1 : ℝ) ≤ S.g := by exact_mod_cast hgN
  have hgR : (0 : ℝ) < S.g := by linarith
  have hrd1 := rd_ge_one E
  have hrd : 0 < S6.rd E := by linarith
  obtain ⟨-, -, -, -, -, -, hN, -⟩ := Formalism.FourierDecayAlt.P.block_lattices Formalism.FourierDecayAlt.P.lattice_facts_general
    Formalism.FourierDecayAlt.P.dualIdealEqLiftIdeal Formalism.FourierDecayAlt.P.scaledIdealNorm E hU S.g S.G.r b n hgN
  set ν : ℤ := S6.nuBlock S.G.r b n with hν
  set x : ℝ := S6.rd E ^ ν with hx
  have hxpos : 0 < x := zpow_pos hrd _
  have hexp : ((2 * S.G.r + 4 : ℤ) - 2 * b - n) = ν + 1 := by
    simp only [hν, S6.nuBlock]; ring
  rw [hexp, zpow_add₀ hrd.ne', zpow_one] at hN
  set m : ℝ := Finset.univ.inf' Finset.univ_nonempty (thr S b n) with hm
  have hmpos : 0 < m := by
    rw [hm, Finset.lt_inf'_iff]; exact fun v _ => hthr v
  have hmle : ∀ v, m ≤ thr S b n v := fun v => Finset.inf'_le _ (Finset.mem_univ v)
  refine ⟨S.g / m, div_pos hgR hmpos, ?_⟩
  set R : ℝ := S.g / m with hR
  have hRpos : 0 < R := div_pos hgR hmpos

  set Nn : ℝ := (FractionalIdeal.absNorm (S6.dualIdl E S.g ν) : ℝ) with hNn
  have hNn0 : 0 ≤ Nn := by
    have : 0 < √Nn := by rw [hN]; positivity
    exact (Real.sqrt_pos.mp this).le
  have hNinv : Nn⁻¹ = ((S.g : ℝ) * (x * S6.rd E)) ^ (2 * S.f) := by
    have h2 : Nn = (√Nn) ^ 2 := (Real.sq_sqrt hNn0).symm
    rw [h2, hN, ← hf]
    rw [inv_pow, inv_inv, ← pow_mul, mul_comm S.f 2]

  have hvol : S.base.vol b n = (∏ v, thr S b n v) ^ 2 * Nn⁻¹ := by
    simp only [C.HidaSetting.base, C.HidaSetting.mkData, thr]
    rw [div_eq_mul_inv]
    congr 2
    exact (Equiv.prod_comp S.pl (fun w => J.thrS S.G S.CA S.de S.de' S.T S.T' S.l b n w)).symm
  have hdlB : KB.dlB S b n = x ^ 2 * (S6.rd E * (S.g : ℝ) ^ 3 / 2) := by
    have e : S6.rd E ^ (2 * ν) = x ^ 2 := by rw [hx, ← zpow_natCast, ← zpow_mul]; ring_nf
    simp only [KB.dlB, D.deG]
    rw [← hν, e]
    field_simp
  rw [hvol, hNinv, hdlB]

  have key : ∀ v, x ^ 2 * (S6.rd E * (S.g : ℝ) ^ 3 / 2) * (Cs * (1 + (R * thr S b n v / S.g) ^ 2)) / R ^ 2 ≤
      Cs * (thr S b n v ^ 2 * ((S.g : ℝ) * (x * S6.rd E)) ^ 2) := by
    intro v
    have ht := hthr v
    have h1 : (1 + (R * thr S b n v / S.g) ^ 2) / R ^ 2 ≤ 2 * thr S b n v ^ 2 / (S.g : ℝ) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hR' : R * m = S.g := by rw [hR]; field_simp
      have hmt : m ^ 2 ≤ thr S b n v ^ 2 := pow_le_pow_left₀ hmpos.le (hmle v) 2
      have : (S.g : ℝ) ^ 2 ≤ R ^ 2 * thr S b n v ^ 2 := by
        rw [← hR']; nlinarith [sq_nonneg R]
      have e : (1 + (R * thr S b n v / S.g) ^ 2) * (S.g : ℝ) ^ 2 =
          (S.g : ℝ) ^ 2 + R ^ 2 * thr S b n v ^ 2 := by field_simp
      rw [e] <;> nlinarith
    calc x ^ 2 * (S6.rd E * (S.g : ℝ) ^ 3 / 2) * (Cs * (1 + (R * thr S b n v / S.g) ^ 2)) / R ^ 2
        = x ^ 2 * (S6.rd E * (S.g : ℝ) ^ 3 / 2) * Cs * ((1 + (R * thr S b n v / S.g) ^ 2) / R ^ 2) := by ring
      _ ≤ x ^ 2 * (S6.rd E * (S.g : ℝ) ^ 3 / 2) * Cs * (2 * thr S b n v ^ 2 / (S.g : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = Cs * (thr S b n v ^ 2 * ((S.g : ℝ) * (x * S6.rd E)) ^ 2) * (1 / ((S.g : ℝ) * S6.rd E)) := by
          field_simp
      _ ≤ Cs * (thr S b n v ^ 2 * ((S.g : ℝ) * (x * S6.rd E)) ^ 2) * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_one (by positivity)] <;> nlinarith
      _ = _ := mul_one _
  calc (∏ _v : Fin S.f, x ^ 2 * (S6.rd E * (S.g : ℝ) ^ 3 / 2)) *
        (∏ v, Cs * (1 + (R * thr S b n v / S.g) ^ 2)) / R ^ (2 * S.f)
      = ∏ v, x ^ 2 * (S6.rd E * (S.g : ℝ) ^ 3 / 2) * (Cs * (1 + (R * thr S b n v / S.g) ^ 2)) / R ^ 2 := by
        conv_rhs => rw [Finset.prod_div_distrib, Finset.prod_mul_distrib]
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [pow_mul]
    _ ≤ ∏ v, Cs * (thr S b n v ^ 2 * ((S.g : ℝ) * (x * S6.rd E)) ^ 2) :=
        Finset.prod_le_prod (fun v _ => by have := hthr v; positivity) (fun v _ => key v)
    _ = Cs ^ S.f * ((∏ v, thr S b n v) ^ 2 * ((S.g : ℝ) * (x * S6.rd E)) ^ (2 * S.f)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          ← pow_mul, mul_comm 2 S.f]

/- English proof (translation)
Unfold `crystallineComparison.psi`. Rewrite using `[← Complex.exp_add, ← mul_add, ← Finset.sum_add_distrib]`. Use `congr 2`. Use `Finset.sum_congr rfl (fun v _ => ?_)` and prove the remaining obligations. Simplify using `only [Pi.add_apply, map_add]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem psi_add {f : ℕ} (a b : crystallineComparison.V f) : crystallineComparison.psi (a + b) = crystallineComparison.psi a * crystallineComparison.psi b := by
  unfold crystallineComparison.psi
  rw [← Complex.exp_add, ← mul_add, ← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl (fun v _ => ?_)
  simp only [Pi.add_apply, map_add]
  ring

/- English proof (translation)
Simplify using `[crystallineComparison.psi]`.
-/
theorem psi_zero {f : ℕ} : crystallineComparison.psi (0 : crystallineComparison.V f) = 1 := by simp [crystallineComparison.psi]

/- English proof (translation)
Unfold `crystallineComparison.psi`. Use `congr 2`. Rewrite using `[Finset.sum_eq_single v]`. Simplify using the standard rewrite rules. Introduce `u _ hu`.

Simplify using `[hu]`. Simplify using the standard rewrite rules.
-/
theorem psi_single {f : ℕ} (v : Fin f) (w : ℂ) :
    crystallineComparison.psi (Pi.single v w : crystallineComparison.V f) = Complex.exp (2 * Real.pi * Complex.I * (w + (starRingEnd ℂ) w)) := by
  unfold crystallineComparison.psi
  congr 2
  rw [Finset.sum_eq_single v]
  · simp
  · intro u _ hu; simp [hu]
  · simp

/- English proof (translation)
Use function extensionality and compare the values at `u`. Distinguish the cases in `h : u = v`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`.
-/
theorem mul_single {f : ℕ} (σ : crystallineComparison.V f) (v : Fin f) (w : ℂ) :
    σ * (Pi.single v w : crystallineComparison.V f) = Pi.single v (σ v * w) := by
  funext u
  by_cases h : u = v
  · subst h; simp
  · simp [h]

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.general_b_fact_right_side.goal1 .. | (apply Bl.general_b_fact_right_side.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right_side.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_side.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_rig …`.
-/
theorem exp_eq_one_iff_int (x : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) = 1 ↔ ∃ n : ℤ, x = n := by
  first | exact Bl.general_b_fact_right_side.goal1 .. | (apply Bl.general_b_fact_right_side.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right_side.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_side.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_right_side.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_side.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_right_side.goal1 x

/- English proof (translation)
Apply the tactic sequence `apply Complex.ext <;> simp; ring`.
-/
theorem add_conj (w : ℂ) : w + (starRingEnd ℂ) w = ((2 * w.re : ℝ) : ℂ) := by
  apply Complex.ext <;> simp; ring

def gen (f : ℕ) (R : ℝ) (p : Fin f × Bool) : crystallineComparison.V f :=
  Pi.single p.1 (if p.2 then (R : ℂ) * Complex.I else (R : ℂ))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lstd_eq (f : ℕ) (R : ℝ) : Lstd f R = Submodule.span ℤ (Set.range (gen f R)) := rfl

def kerPsi {f : ℕ} (σ : crystallineComparison.V f) : AddSubgroup (crystallineComparison.V f) where
  carrier := {z | crystallineComparison.psi (σ * z) = 1}
  zero_mem' := by simp [psi_zero]
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [mul_add, psi_add, ha, hb, one_mul]
  neg_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    have h := psi_add (σ * -a) (σ * a)
    rw [← mul_add, neg_add_cancel, mul_zero, psi_zero, ha, mul_one] at h
    exact h.symm

/- English proof (translation)
Establish `hR' : (R : ℂ) ≠ 0` using `by exact_mod_cast hR.ne'`. Establish `hgen : ∀ v (β : Bool), crystallineComparison.psi (σ * gen f R (v, β)) = 1 ↔ ∃ n : ℤ, (if β then -(2 * R * (σ v).im) else 2 * R * (σ v).re) = n`. Introduce `v β`. Rewrite using `[gen, mul_single, psi_single, add_conj, ← exp_eq_one_iff_int]`. Use `congr! 4`.

Apply the tactic sequence `cases β <;> simp [Complex.mul_re, Complex.mul_im] <;> ring`. Prove the components needed by the constructor for the conclusion. Introduce `h v`. Take `⟨a, ha⟩` from `(hgen v false).1 (h _ (Submodule.subset_span ⟨(v, false), rfl⟩))`. Take `⟨c, hc⟩` from `(hgen v true).1 (h _ (Submodule.subset_span ⟨(v, true), rfl⟩))`.

Simplify using `only [if_false, if_true, Bool.false_eq_true] at ha hc`. Use `⟨a, -c, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_div_iff (by simp [hR'])]`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `[Complex.mul_re]`.

Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `[Complex.mul_im]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `h z hz`. Establish `hle : Lstd f R ≤ AddSubgroup.toIntSubmodule (kerPsi σ)`.

Rewrite using `[lstd_eq, Submodule.span_le]`. Introduce and unpack `_ ⟨⟨v, β⟩, rfl⟩`. Use `show crystallineComparison.psi (σ * gen f R (v, β)) = 1`. Rewrite using `[hgen]`. Take `⟨a, b, hab⟩` from `h v`.

Establish `h2 : σ v * (2 * (R : ℂ)) = (a : ℂ) + (b : ℂ) * Complex.I`. Rewrite using `[hab]`. Clear the denominators using the available nonvanishing facts. Establish `hre : 2 * R * (σ v).re = a`. Use `congrArg Complex.re h2` as an intermediate fact.

Simplify using `[Complex.mul_re] at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `him : 2 * R * (σ v).im = b`. Use `congrArg Complex.im h2` as an intermediate fact. Simplify using `[Complex.mul_im] at this`.

Combine the linear equalities and inequalities to obtain the conclusion. Consider the cases of `β`. Conclude with `⟨a, by simpa using hre⟩`. Conclude with `⟨-b, by simp [him]⟩`. Conclude with `hle hz`.
-/
theorem mem_dual_iff (f : ℕ) (R : ℝ) (hR : 0 < R) (σ : crystallineComparison.V f) :
    σ ∈ crystallineComparison.dualSet (Lstd f R) ↔
      ∀ v, ∃ a b : ℤ, σ v = ((a : ℂ) + (b : ℂ) * Complex.I) / (2 * (R : ℂ)) := by
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hgen : ∀ v (β : Bool), crystallineComparison.psi (σ * gen f R (v, β)) = 1 ↔
      ∃ n : ℤ, (if β then -(2 * R * (σ v).im) else 2 * R * (σ v).re) = n := by
    intro v β
    rw [gen, mul_single, psi_single, add_conj, ← exp_eq_one_iff_int]
    congr! 4
    cases β <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  constructor
  · intro h v
    obtain ⟨a, ha⟩ := (hgen v false).1 (h _ (Submodule.subset_span ⟨(v, false), rfl⟩))
    obtain ⟨c, hc⟩ := (hgen v true).1 (h _ (Submodule.subset_span ⟨(v, true), rfl⟩))
    simp only [if_false, if_true, Bool.false_eq_true] at ha hc
    refine ⟨a, -c, ?_⟩
    rw [eq_div_iff (by simp [hR'])]
    apply Complex.ext
    · simp [Complex.mul_re]; linarith
    · simp [Complex.mul_im]; linarith
  · intro h z hz
    have hle : Lstd f R ≤ AddSubgroup.toIntSubmodule (kerPsi σ) := by
      rw [lstd_eq, Submodule.span_le]
      rintro _ ⟨⟨v, β⟩, rfl⟩
      show crystallineComparison.psi (σ * gen f R (v, β)) = 1
      rw [hgen]
      obtain ⟨a, b, hab⟩ := h v
      have h2 : σ v * (2 * (R : ℂ)) = (a : ℂ) + (b : ℂ) * Complex.I := by
        rw [hab]; field_simp
      have hre : 2 * R * (σ v).re = a := by
        have := congrArg Complex.re h2
        simp [Complex.mul_re] at this; linarith
      have him : 2 * R * (σ v).im = b := by
        have := congrArg Complex.im h2
        simp [Complex.mul_im] at this; linarith
      cases β
      · exact ⟨a, by simpa using hre⟩
      · exact ⟨-b, by simp [him]⟩
    exact hle hz

def eqv (f : ℕ) : (Σ _ : Fin f, Fin 2) ≃ Fin f × Bool :=
  (Equiv.sigmaEquivProd (Fin f) (Fin 2)).trans (Equiv.prodCongr (Equiv.refl _) finTwoEquiv)

def b0 (f : ℕ) : Module.Basis (Fin f × Bool) ℝ (crystallineComparison.V f) :=
  (Pi.basis fun _ : Fin f => Complex.basisOneI).reindex (eqv f)

/- English proof (translation)
Apply the tactic sequence `cases β <;> simp [b0, eqv, Pi.basis_apply] <;> rfl`.
-/
theorem standard_lattice_basis_apply (f : ℕ) (v : Fin f) (β : Bool) :
    b0 f (v, β) = (Pi.single v (if β then Complex.I else 1) : crystallineComparison.V f) := by
  cases β <;> simp [b0, eqv, Pi.basis_apply] <;> rfl

/- English proof (translation)
Rewrite using `[b0, Module.Basis.repr_reindex_apply]`. Apply the tactic sequence `cases β <;> simp [eqv, Pi.basis_repr] <;> rfl`.
-/
theorem standard_lattice_basis_repr (f : ℕ) (m : crystallineComparison.V f) (v : Fin f) (β : Bool) :
    (b0 f).repr m (v, β) = if β then (m v).im else (m v).re := by
  rw [b0, Module.Basis.repr_reindex_apply]
  cases β <;> simp [eqv, Pi.basis_repr] <;> rfl

def bR (f : ℕ) (R : ℝ) (hR : 0 < R) : Module.Basis (Fin f × Bool) ℝ (crystallineComparison.V f) :=
  (b0 f).isUnitSMul (w := fun _ => R) (fun _ => hR.ne'.isUnit)

/- English proof (translation)
Use function extensionality and compare the values at `p`. Take `⟨v, β⟩` from `p`. Rewrite using `[bR, Module.Basis.isUnitSMul_apply, standard_lattice_basis_apply, gen]`. Apply the tactic sequence `cases β <;> funext u <;> by_cases h : u = v <;> simp_all [Complex.real_smul]`.
-/
theorem bR_eq (f : ℕ) (R : ℝ) (hR : 0 < R) : ⇑(bR f R hR) = gen f R := by
  funext p
  obtain ⟨v, β⟩ := p
  rw [bR, Module.Basis.isUnitSMul_apply, standard_lattice_basis_apply, gen]
  cases β <;> funext u <;> by_cases h : u = v <;> simp_all [Complex.real_smul]

/- English proof (translation)
Use extensionality with `m`. Simplify using `only [ZSpan.fundamentalDomain, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies, Prod.forall, standard_lattice_basis_repr, Bool.forall_bool, if_false, if_true, Bool.false_eq_true]`.
-/
theorem fundamentalDomain_standard_basis_eq (f : ℕ) : ZSpan.fundamentalDomain (b0 f) =
    Set.pi Set.univ (fun _ : Fin f => {z : ℂ | z.re ∈ Set.Ico (0 : ℝ) 1 ∧ z.im ∈ Set.Ico (0 : ℝ) 1}) := by
  ext m
  simp only [ZSpan.fundamentalDomain, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies, Prod.forall,
    standard_lattice_basis_repr, Bool.forall_bool, if_false, if_true, Bool.false_eq_true]

/- English proof (translation)
Establish `h : {z : ℂ | z.re ∈ Set.Ico (0 : ℝ) 1 ∧ z.im ∈ Set.Ico (0 : ℝ) 1} = Complex.measurableEquivRealProd ⁻¹' (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1)`. Use extensionality with `z`. Simplify using `[Complex.measurableEquivRealProd]`. Rewrite using `[h, Complex.volume_preserving_equiv_real_prod.measure_preimage ((measurableSet_Ico.prod measurableSet_Ico).nullMeasurableSet), Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico]`. Simplify using the standard rewrite rules.
-/
theorem vol_square : (volume : Measure ℂ) {z : ℂ | z.re ∈ Set.Ico (0 : ℝ) 1 ∧ z.im ∈ Set.Ico (0 : ℝ) 1} = 1 := by
  have h : {z : ℂ | z.re ∈ Set.Ico (0 : ℝ) 1 ∧ z.im ∈ Set.Ico (0 : ℝ) 1} =
      Complex.measurableEquivRealProd ⁻¹' (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1) := by
    ext z; simp [Complex.measurableEquivRealProd]
  rw [h, Complex.volume_preserving_equiv_real_prod.measure_preimage
    ((measurableSet_Ico.prod measurableSet_Ico).nullMeasurableSet), Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_Ico]
  simp

/- English proof (translation)
Rewrite using `[fundamentalDomain_standard_basis_eq, volume_pi_pi, Finset.prod_eq_one (fun _ _ => vol_square)]`.
-/
theorem volume_fundamentalDomain_standard_basis (f : ℕ) : (volume : Measure (crystallineComparison.V f)) (ZSpan.fundamentalDomain (b0 f)) = 1 := by
  rw [fundamentalDomain_standard_basis_eq, volume_pi_pi, Finset.prod_eq_one (fun _ _ => vol_square)]

/- English proof (translation)
Use extensionality with `m`. Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem₀ hR.ne']`. Simplify using `only [ZSpan.fundamentalDomain, Set.mem_ofPred_eq, bR, Module.Basis.repr_isUnitSMul, map_smul, Finsupp.smul_apply, smul_eq_mul]`. Apply the tactic sequence `constructor <;> intro h i <;> simpa [Units.smul_def, Units.val_inv_eq_inv_val, IsUnit.unit_spec] using h i`.
-/
theorem fd_bR (f : ℕ) (R : ℝ) (hR : 0 < R) :
    ZSpan.fundamentalDomain (bR f R hR) = R • ZSpan.fundamentalDomain (b0 f) := by
  ext m
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hR.ne']
  simp only [ZSpan.fundamentalDomain, Set.mem_ofPred_eq, bR, Module.Basis.repr_isUnitSMul, map_smul,
    Finsupp.smul_apply, smul_eq_mul]
  constructor <;> intro h i <;> simpa [Units.smul_def, Units.val_inv_eq_inv_val, IsUnit.unit_spec] using h i

/- English proof (translation)
Rewrite using `[Module.finrank_pi_fintype]`. Simplify using `[Complex.finrank_real_complex, mul_comm]`.
-/
theorem finrank_V (f : ℕ) : Module.finrank ℝ (crystallineComparison.V f) = 2 * f := by
  rw [Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, mul_comm]

/- English proof (translation)
Introduce `f R hR`. Rewrite using `[lstd_eq, ← bR_eq f R hR]`. Use `⟨inferInstance, inferInstance, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[ZLattice.covolume_eq_measure_fundamentalDomain _ _ (ZSpan.isAddFundamentalDomain (bR f R hR) volume), fd_bR, Measure.real, Measure.addHaar_smul, volume_fundamentalDomain_standard_basis, finrank_V]`. Simplify using `[abs_of_pos hR, hR.le]`.

Introduce `σ`. Rewrite using `[bR_eq, ← lstd_eq]`. Conclude with `mem_dual_iff f R hR σ`.
-/
theorem lstdFacts : PBC.LstdFacts := by
  intro f R hR
  rw [lstd_eq, ← bR_eq f R hR]
  refine ⟨inferInstance, inferInstance, ?_, ?_⟩
  · rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ (ZSpan.isAddFundamentalDomain (bR f R hR) volume),
      fd_bR, Measure.real, Measure.addHaar_smul, volume_fundamentalDomain_standard_basis, finrank_V]
    simp [abs_of_pos hR, hR.le]
  · intro σ
    rw [bR_eq, ← lstd_eq]
    exact mem_dual_iff f R hR σ

/- English proof (translation)
Unfold `crystallineComparison.mfac`. Distinguish the cases in `h : a = 0`. Simplify using `[h]`. Rewrite using `[if_neg (mul_ne_zero hg.ne' h), if_neg h]`. Use `congr 2`.

Clear the denominators using the available nonvanishing facts.
-/
theorem mfac_scale (K : ℕ) (L g a : ℝ) (hg : 0 < g) :
    crystallineComparison.mfac K L (g * a) = crystallineComparison.mfac K (L / g) a := by
  unfold crystallineComparison.mfac
  by_cases h : a = 0
  · simp [h]
  · rw [if_neg (mul_ne_zero hg.ne' h), if_neg h]
    congr 2
    field_simp

/- English proof (translation)
Unfold `crystallineComparison.mL`. Use `Finset.prod_congr rfl (fun v _ => ?_)` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hg, mfac_scale K _ g _ hg]`.
-/
theorem mL_scale {f : ℕ} (K : ℕ) (L : Fin f → ℝ) (g : ℝ) (hg : 0 < g) (σ : crystallineComparison.V f) :
    crystallineComparison.mL K L (g • σ) = crystallineComparison.mL K (fun v => L v / g) σ := by
  unfold crystallineComparison.mL
  refine Finset.prod_congr rfl (fun v _ => ?_)
  rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hg, mfac_scale K _ g _ hg]

/- English proof (translation)
Establish `had : 0 < a + δ` using `by linarith`. Unfold `crystallineComparison.mfac`. Rewrite using `[if_neg had.ne']`. Use `split_ifs with h0`. Substitute `h0` using the available equality.

Rewrite using `[min_eq_left (one_le_pow₀ ((one_le_div (by linarith)).mpr (by linarith)))]`. Establish `hapos : 0 < a` using `lt_of_le_of_ne ha (Ne.symm h0)`. Break down `le_or_gt a L with haL | haL` into its components or cases. Rewrite using `[min_eq_left (one_le_pow₀ ((one_le_div had).mpr (by linarith)))]`. Conclude with `min_le_left _ _`.

Apply `min_le_min_left` to reduce the goal to its premises. Apply `pow_le_pow_left₀ (div_nonneg hL ha)` to reduce the goal to its premises. Rewrite using `[div_le_div_iff₀ hapos had]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem mfac_shift0 (K : ℕ) {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ) {a : ℝ} (ha : 0 ≤ a) :
    crystallineComparison.mfac K L a ≤ crystallineComparison.mfac K (L + δ) (a + δ) := by
  have had : 0 < a + δ := by linarith
  unfold crystallineComparison.mfac
  rw [if_neg had.ne']
  split_ifs with h0
  · subst h0
    rw [min_eq_left (one_le_pow₀ ((one_le_div (by linarith)).mpr (by linarith)))]
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm h0)
    rcases le_or_gt a L with haL | haL
    · rw [min_eq_left (one_le_pow₀ ((one_le_div had).mpr (by linarith)))]
      exact min_le_left _ _
    · apply min_le_min_left
      apply pow_le_pow_left₀ (div_nonneg hL ha)
      rw [div_le_div_iff₀ hapos had]
      nlinarith

/- English proof (translation)
Establish `hmn : m ≠ 0 ∨ n ≠ 0`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Apply `h` to reduce the goal to its premises. Simplify using `[hc.1, hc.2]`.

Establish `hsq : (1 : ℝ) ≤ (m : ℝ) ^ 2 + (n : ℝ) ^ 2`. Break down `hmn with hm | hn` into its components or cases. Establish `: (1 : ℤ) ≤ m ^ 2` using `by nlinarith [Int.one_le_abs hm, sq_abs m]`. Establish `: (1 : ℝ) ≤ (m : ℝ) ^ 2` using `by exact_mod_cast this`. Use polynomial arithmetic with `[sq_nonneg (n : ℝ)]`.

Establish `: (1 : ℤ) ≤ n ^ 2` using `by nlinarith [Int.one_le_abs hn, sq_abs n]`. Establish `: (1 : ℝ) ≤ (n : ℝ) ^ 2` using `by exact_mod_cast this`. Use polynomial arithmetic with `[sq_nonneg (m : ℝ)]`. Rewrite using `[← Real.sqrt_one, Complex.norm_def, Complex.normSq_apply]`. Apply `Real.sqrt_le_sqrt` to reduce the goal to its premises.

Simplify using the standard rewrite rules. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem gauss_norm (m n : ℤ) (h : (m : ℂ) + (n : ℂ) * Complex.I ≠ 0) :
    1 ≤ ‖(m : ℂ) + (n : ℂ) * Complex.I‖ := by
  have hmn : m ≠ 0 ∨ n ≠ 0 := by
    by_contra hc; push Not at hc; apply h; simp [hc.1, hc.2]
  have hsq : (1 : ℝ) ≤ (m : ℝ) ^ 2 + (n : ℝ) ^ 2 := by
    rcases hmn with hm | hn
    · have : (1 : ℤ) ≤ m ^ 2 := by nlinarith [Int.one_le_abs hm, sq_abs m]
      have : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by exact_mod_cast this
      nlinarith [sq_nonneg (n : ℝ)]
    · have : (1 : ℤ) ≤ n ^ 2 := by nlinarith [Int.one_le_abs hn, sq_abs n]
      have : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast this
      nlinarith [sq_nonneg (m : ℝ)]
  rw [← Real.sqrt_one, Complex.norm_def, Complex.normSq_apply]
  apply Real.sqrt_le_sqrt
  simp; nlinarith

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨v, hv⟩ : ∃ v, σ v ≠ σ' v := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hne (funext h)`. Take `⟨a, b, hab⟩` from `(mem_dual_iff f R hR σ).1 hσ v`.

Take `⟨a', b', hab'⟩` from `(mem_dual_iff f R hR σ').1 hσ' v`. Establish `hR' : (2 * (R : ℂ)) ≠ 0` using `by simp [hR.ne']`. Establish `hd : σ v - σ' v = (((a - a' : ℤ) : ℂ) + ((b - b' : ℤ) : ℂ) * Complex.I) / (2 * (R : ℂ))`. Rewrite using `[hab, hab']`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hnz : (((a - a' : ℤ) : ℂ) + ((b - b' : ℤ) : ℂ) * Complex.I) ≠ 0`. Introduce `h0`. Apply `hv` to reduce the goal to its premises.

Rewrite using `[← sub_eq_zero, hd, h0, zero_div]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hd, norm_div]`. Use `congr 1`. Simplify using `[abs_of_pos hR]`.

Use `_ = ‖(σ - σ') v‖ := rfl`. Use `_ ≤ ‖σ - σ'‖ := norm_le_pi_norm (σ - σ') v`.
-/
theorem dual_sep (f : ℕ) (R : ℝ) (hR : 0 < R) (σ σ' : crystallineComparison.V f) (hσ : σ ∈ crystallineComparison.dualSet (Lstd f R))
    (hσ' : σ' ∈ crystallineComparison.dualSet (Lstd f R)) (hne : σ ≠ σ') : 1 / (2 * R) ≤ ‖σ - σ'‖ := by
  obtain ⟨v, hv⟩ : ∃ v, σ v ≠ σ' v := by
    by_contra h; push Not at h; exact hne (funext h)
  obtain ⟨a, b, hab⟩ := (mem_dual_iff f R hR σ).1 hσ v
  obtain ⟨a', b', hab'⟩ := (mem_dual_iff f R hR σ').1 hσ' v
  have hR' : (2 * (R : ℂ)) ≠ 0 := by simp [hR.ne']
  have hd : σ v - σ' v = (((a - a' : ℤ) : ℂ) + ((b - b' : ℤ) : ℂ) * Complex.I) / (2 * (R : ℂ)) := by
    rw [hab, hab']; push_cast; field_simp; ring
  have hnz : (((a - a' : ℤ) : ℂ) + ((b - b' : ℤ) : ℂ) * Complex.I) ≠ 0 := by
    intro h0; apply hv; rw [← sub_eq_zero, hd, h0, zero_div]
  calc 1 / (2 * R) ≤ ‖(((a - a' : ℤ) : ℂ) + ((b - b' : ℤ) : ℂ) * Complex.I)‖ / (2 * R) :=
        div_le_div_of_nonneg_right (gauss_norm _ _ hnz) (by positivity)
    _ = ‖σ v - σ' v‖ := by
        rw [hd, norm_div]; congr 1; simp [abs_of_pos hR]
    _ = ‖(σ - σ') v‖ := rfl
    _ ≤ ‖σ - σ'‖ := norm_le_pi_norm (σ - σ') v

/- English proof (translation)
Rewrite using `[Measure.real, volume_pi_ball _ hδ]`. Simplify using `only [Pi.zero_apply, Complex.volume_ball, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Rewrite using `[ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hδ.le]`. Simplify using `[mul_comm]`.
-/
theorem vol_ball_V (f : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    (volume : Measure (crystallineComparison.V f)).real (Metric.ball 0 δ) = (Real.pi * δ ^ 2) ^ f := by
  rw [Measure.real, volume_pi_ball _ hδ]
  simp only [Pi.zero_apply, Complex.volume_ball, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hδ.le]
  simp [mul_comm]

/- English proof (translation)
Use `⟨54, by norm_num, ?_⟩` and prove the remaining obligations. Introduce `f R g L hR hg hL`. Use `set K := C.Kst with hKdef`. Establish `hK : 2 < K` using `by simp [hKdef, C.Kst]`. Use `set large₂ : Fin f → ℝ := fun v => L v / g with hLg`.

Establish `hLg0 : ∀ v, 0 ≤ large₂ v` using `fun v => div_nonneg (hL v) hg.le`. Use `set δ : ℝ := 1 / (4 * R) with hδdef`. Establish `hδ : 0 < δ` using `by positivity`. Use `set L' : Fin f → ℝ := fun v => large₂ v + δ with hL'`. Establish `hL'pos : ∀ v, 0 < L' v` using `fun v => by simp only [hL']; linarith [hLg0 v]`.

Establish `hmaj` using `Formalism.FourierDecayAlt.P.MajorantIntegrals.majIntegralProd_ok f K L' hK hL'pos`. Establish `hint` using `hmaj.1`. Establish `hnn : ∀ y : crystallineComparison.V f, 0 ≤ crystallineComparison.mL K L' y` using `fun y => Finset.prod_nonneg (fun v _ => Formalism.FourierDecayAlt.P.LatticeSummability.mfac_nonneg K (hL'pos v).le _ (norm_nonneg _))`. Establish `hnn0 : ∀ y : crystallineComparison.V f, 0 ≤ crystallineComparison.mL K large₂ y` using `fun y => Finset.prod_nonneg (fun v _ => Formalism.FourierDecayAlt.P.LatticeSummability.mfac_nonneg K (hLg0 v) _ (norm_nonneg _))`. Use `set vb := (volume : Measure (crystallineComparison.V f)).real (Metric.ball 0 δ) with hvb`.

Establish `hvb0 : 0 < vb` using `by rw [hvb, vol_ball_V f δ hδ]; positivity`. Establish `hvbσ : ∀ σ : crystallineComparison.V f, (volume : Measure (crystallineComparison.V f)).real (Metric.ball σ δ) = vb`. Introduce `σ`. Rewrite using `[hvb, Measure.real, Measure.real, Measure.addHaar_ball_center]`. Establish `hpt : ∀ σ : crystallineComparison.V f, ∀ y ∈ Metric.ball σ δ, crystallineComparison.mL K large₂ σ ≤ crystallineComparison.mL K L' y`.

Introduce `σ y hy`. Apply `Finset.prod_le_prod (fun v _ => Formalism.FourierDecayAlt.P.LatticeSummability.mfac_nonneg K (hLg0 v) _ (norm_nonneg _))` to reduce the goal to its premises. Introduce `v _`. Establish `hyv : ‖y v‖ ≤ ‖σ v‖ + δ`. Establish `h1 : ‖y v - σ v‖ ≤ ‖y - σ‖` using `norm_le_pi_norm (y - σ) v`.

Establish `h2 : ‖y - σ‖ < δ` using `by rw [← dist_eq_norm]; exact hy`. Establish `h3 : ‖y v‖ ≤ ‖σ v‖ + ‖y v - σ v‖`. Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `(mfac_shift0 K (hLg0 v) hδ (norm_nonneg _)).trans (Formalism.FourierDecayAlt.P.LatticeSummability.mfac_anti K (hL'pos v) (norm_nonneg _) hyv)`.

Establish `hloc : ∀ σ : crystallineComparison.V f, crystallineComparison.mL K large₂ σ * vb ≤ ∫ y in Metric.ball σ δ, crystallineComparison.mL K L' y`. Introduce `σ`. Rewrite using `[← hvbσ σ, mul_comm, ← smul_eq_mul, ← setIntegral_const]`. Conclude with `setIntegral_mono_on (integrableOn_const (measure_ball_lt_top).ne) hint.integrableOn measurableSet_ball (fun y hy => hpt σ y hy)`. Establish `hsum : ∀ u : Finset (crystallineComparison.dualSet (Lstd f R)), ∑ σ ∈ u, crystallineComparison.mL K L (g • (σ : crystallineComparison.V f)) ≤ (∫ y, crystallineComparison.mL K L' y) / vb`.

Introduce `u`. Simplify using `only [mL_scale K L g hg]`. Rewrite using `[le_div_iff₀ hvb0, Finset.sum_mul]`. Establish `hdisj : Set.Pairwise (↑u : Set (crystallineComparison.dualSet (Lstd f R))) (Function.onFun Disjoint fun σ : crystallineComparison.dualSet (Lstd f R) => Metric.ball (σ : crystallineComparison.V f) δ)`. Introduce `σ _ σ' _ hne`.

Apply `Metric.ball_disjoint_ball` to reduce the goal to its premises. Use `dual_sep f R hR σ σ' σ.2 σ'.2 (fun h => hne (Subtype.ext h))` as an intermediate fact. Rewrite using `[dist_eq_norm]`. Establish `e : δ + δ = 1 / (2 * R)` using `by rw [hδdef]; field_simp; ring`. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the equalities or inequalities in the displayed calculation. Establish `hnng : ∀ σ : crystallineComparison.dualSet (Lstd f R), 0 ≤ crystallineComparison.mL K L (g • (σ : crystallineComparison.V f))` using `fun σ => Finset.prod_nonneg (fun v _ => Formalism.FourierDecayAlt.P.LatticeSummability.mfac_nonneg K (hL v) _ (norm_nonneg _))`. Establish `hS : Summable (fun σ : crystallineComparison.dualSet (Lstd f R) => crystallineComparison.mL K L (g • (σ : crystallineComparison.V f)))` using `summable_of_sum_le hnng hsum`. Use `⟨hS, (hS.tsum_le_of_sum_le hsum).trans ?_⟩` and prove the remaining obligations. Rewrite using `[hmaj.2, hvb, vol_ball_V f δ hδ, show (Real.pi * δ ^ 2) ^ f = ∏ _v : Fin f, (Real.pi * δ ^ 2) by simp]`.

Rewrite using `[← Finset.prod_div_distrib]`. Apply `Finset.prod_le_prod` to reduce the goal to its premises. Introduce `v _`. Establish `hK2 : (0 : ℝ) < (K : ℝ) - 2` using `by simp [hKdef, C.Kst]; norm_num`. Use `hL'pos v` as an intermediate fact.

Conclude with `div_nonneg (div_nonneg (by positivity) hK2.le) (by positivity)`. Introduce `v _`. Establish `hKr : (K : ℝ) = 5` using `by simp [hKdef, C.Kst]`. Rewrite using `[hKr]`. Use `set x : ℝ := R * L v / g with hxdef`.

Establish `hx0 : 0 ≤ x` using `by have := hL v; positivity`. Establish `hx : L' v = 4 * δ * x + δ` using `by show L v / g + δ = _`. Rewrite using `[hxdef, hδdef]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hx]`.

Establish `ht : 0 < Real.pi * δ ^ 2` using `by positivity`. Establish `e : Real.pi * (4 * δ * x + δ) ^ 2 * 5 / (5 - 2) / (Real.pi * δ ^ 2) = (4 * x + 1) ^ 2 * 5 / 3` using `by field_simp; ring`. Rewrite using `[e]`. Use polynomial arithmetic with `[sq_nonneg (x - 1)]`.
-/
theorem lstdSum : PBC.LstdSum := by
  refine ⟨54, by norm_num, ?_⟩
  intro f R g L hR hg hL
  set K := C.Kst with hKdef
  have hK : 2 < K := by simp [hKdef, C.Kst]
  set large₂ : Fin f → ℝ := fun v => L v / g with hLg
  have hLg0 : ∀ v, 0 ≤ large₂ v := fun v => div_nonneg (hL v) hg.le
  set δ : ℝ := 1 / (4 * R) with hδdef
  have hδ : 0 < δ := by positivity
  set L' : Fin f → ℝ := fun v => large₂ v + δ with hL'
  have hL'pos : ∀ v, 0 < L' v := fun v => by simp only [hL']; linarith [hLg0 v]
  have hmaj := Formalism.FourierDecayAlt.P.MajorantIntegrals.majIntegralProd_ok f K L' hK hL'pos
  have hint := hmaj.1
  have hnn : ∀ y : crystallineComparison.V f, 0 ≤ crystallineComparison.mL K L' y := fun y =>
    Finset.prod_nonneg (fun v _ => Formalism.FourierDecayAlt.P.LatticeSummability.mfac_nonneg K (hL'pos v).le _ (norm_nonneg _))
  have hnn0 : ∀ y : crystallineComparison.V f, 0 ≤ crystallineComparison.mL K large₂ y := fun y =>
    Finset.prod_nonneg (fun v _ => Formalism.FourierDecayAlt.P.LatticeSummability.mfac_nonneg K (hLg0 v) _ (norm_nonneg _))
  set vb := (volume : Measure (crystallineComparison.V f)).real (Metric.ball 0 δ) with hvb
  have hvb0 : 0 < vb := by rw [hvb, vol_ball_V f δ hδ]; positivity
  have hvbσ : ∀ σ : crystallineComparison.V f, (volume : Measure (crystallineComparison.V f)).real (Metric.ball σ δ) = vb := by
    intro σ; rw [hvb, Measure.real, Measure.real, Measure.addHaar_ball_center]
  have hpt : ∀ σ : crystallineComparison.V f, ∀ y ∈ Metric.ball σ δ, crystallineComparison.mL K large₂ σ ≤ crystallineComparison.mL K L' y := by
    intro σ y hy
    apply Finset.prod_le_prod (fun v _ => Formalism.FourierDecayAlt.P.LatticeSummability.mfac_nonneg K (hLg0 v) _ (norm_nonneg _))
    intro v _
    have hyv : ‖y v‖ ≤ ‖σ v‖ + δ := by
      have h1 : ‖y v - σ v‖ ≤ ‖y - σ‖ := norm_le_pi_norm (y - σ) v
      have h2 : ‖y - σ‖ < δ := by rw [← dist_eq_norm]; exact hy
      have h3 : ‖y v‖ ≤ ‖σ v‖ + ‖y v - σ v‖ := by
        calc ‖y v‖ = ‖σ v + (y v - σ v)‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      linarith
    exact (mfac_shift0 K (hLg0 v) hδ (norm_nonneg _)).trans
      (Formalism.FourierDecayAlt.P.LatticeSummability.mfac_anti K (hL'pos v) (norm_nonneg _) hyv)
  have hloc : ∀ σ : crystallineComparison.V f, crystallineComparison.mL K large₂ σ * vb ≤ ∫ y in Metric.ball σ δ, crystallineComparison.mL K L' y := by
    intro σ
    rw [← hvbσ σ, mul_comm, ← smul_eq_mul, ← setIntegral_const]
    exact setIntegral_mono_on (integrableOn_const (measure_ball_lt_top).ne) hint.integrableOn
      measurableSet_ball (fun y hy => hpt σ y hy)
  have hsum : ∀ u : Finset (crystallineComparison.dualSet (Lstd f R)),
      ∑ σ ∈ u, crystallineComparison.mL K L (g • (σ : crystallineComparison.V f)) ≤ (∫ y, crystallineComparison.mL K L' y) / vb := by
    intro u
    simp only [mL_scale K L g hg]
    rw [le_div_iff₀ hvb0, Finset.sum_mul]
    have hdisj : Set.Pairwise (↑u : Set (crystallineComparison.dualSet (Lstd f R)))
        (Function.onFun Disjoint fun σ : crystallineComparison.dualSet (Lstd f R) => Metric.ball (σ : crystallineComparison.V f) δ) := by
      intro σ _ σ' _ hne
      apply Metric.ball_disjoint_ball
      have := dual_sep f R hR σ σ' σ.2 σ'.2 (fun h => hne (Subtype.ext h))
      rw [dist_eq_norm]
      have e : δ + δ = 1 / (2 * R) := by rw [hδdef]; field_simp; ring
      linarith
    calc ∑ σ ∈ u, crystallineComparison.mL K large₂ (σ : crystallineComparison.V f) * vb
        ≤ ∑ σ ∈ u, ∫ y in Metric.ball (σ : crystallineComparison.V f) δ, crystallineComparison.mL K L' y :=
          Finset.sum_le_sum (fun σ _ => hloc σ)
      _ = ∫ y in ⋃ σ ∈ u, Metric.ball (σ : crystallineComparison.V f) δ, crystallineComparison.mL K L' y :=
          (integral_biUnion_finset u (fun σ _ => measurableSet_ball) hdisj
            (fun σ _ => hint.integrableOn)).symm
      _ ≤ ∫ y, crystallineComparison.mL K L' y := setIntegral_le_integral hint (Filter.Eventually.of_forall hnn)
  have hnng : ∀ σ : crystallineComparison.dualSet (Lstd f R), 0 ≤ crystallineComparison.mL K L (g • (σ : crystallineComparison.V f)) := fun σ =>
    Finset.prod_nonneg (fun v _ => Formalism.FourierDecayAlt.P.LatticeSummability.mfac_nonneg K (hL v) _ (norm_nonneg _))
  have hS : Summable (fun σ : crystallineComparison.dualSet (Lstd f R) => crystallineComparison.mL K L (g • (σ : crystallineComparison.V f))) :=
    summable_of_sum_le hnng hsum
  refine ⟨hS, (hS.tsum_le_of_sum_le hsum).trans ?_⟩

  rw [hmaj.2, hvb, vol_ball_V f δ hδ, show (Real.pi * δ ^ 2) ^ f = ∏ _v : Fin f, (Real.pi * δ ^ 2) by simp]
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_le_prod
  · intro v _
    have hK2 : (0 : ℝ) < (K : ℝ) - 2 := by simp [hKdef, C.Kst]; norm_num
    have := hL'pos v
    exact div_nonneg (div_nonneg (by positivity) hK2.le) (by positivity)
  intro v _
  have hKr : (K : ℝ) = 5 := by simp [hKdef, C.Kst]
  rw [hKr]
  set x : ℝ := R * L v / g with hxdef
  have hx0 : 0 ≤ x := by have := hL v; positivity
  have hx : L' v = 4 * δ * x + δ := by
    show L v / g + δ = _
    rw [hxdef, hδdef]; field_simp
  rw [hx]
  have ht : 0 < Real.pi * δ ^ 2 := by positivity
  have e : Real.pi * (4 * δ * x + δ) ^ 2 * 5 / (5 - 2) / (Real.pi * δ ^ 2) = (4 * x + 1) ^ 2 * 5 / 3 := by
    field_simp; ring
  rw [e]
  nlinarith [sq_nonneg (x - 1)]

end Lat

/- English proof (translation)
The claim follows from `Lat.lstdSum`.
-/
theorem pbc_lstdSum : PBC.LstdSum := Lat.lstdSum

/- English proof (translation)
The claim follows from `Lat.lstdFacts`.
-/
theorem pbc_lstdFacts : PBC.LstdFacts := Lat.lstdFacts

/- English proof (translation)
The claim follows from `Lat.sizesSup`.
-/
theorem pbc_sizesSup : PBC.SizesSup := Lat.sizesSup

end

end Formalism.FourierDecayAlt.P.PBC
