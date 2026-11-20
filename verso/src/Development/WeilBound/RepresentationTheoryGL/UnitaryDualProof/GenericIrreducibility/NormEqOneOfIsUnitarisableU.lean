import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIrreducibleSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitarisableSegmentTwistPrecedesAddOneLe

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix

namespace PositivityTheory.RgUd.UOrder

open GlobalTheory GlobalTheory.LocGL GlobalTheory.LocGL.UnitaryOrder

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def UnitCC {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin N) k) V) : Prop :=
  ∃ ω : kˣ →* ℂˣ, HasCentralChar ρ ω ∧ ∀ z, ‖(ω z : ℂ)‖ = 1

/- English proof (translation)
Take `⟨ω, hω, h1⟩` from `hU`. Take `⟨v, hv⟩` from `exists_ne (0 : X)`. Establish `e : c • v = (ω z : ℂ) • v` using `(hc v).symm.trans (hω z v)`. Establish `: c = (ω z : ℂ)` using `smul_left_injective ℂ hv e`. Rewrite using `[this, h1]`.
-/
theorem norm_eq_one_of_unitCC {N : ℕ} {X : Type} [AddCommGroup X] [Module ℂ X] [Nontrivial X]
    {ρ : Representation ℂ (GL (Fin N) k) X} (hU : UnitCC ρ) {z : kˣ} {c : ℂ}
    (hc : ∀ v, ρ (GeneralLinearGroup.scalar (Fin N) z) v = c • v) : ‖c‖ = 1 := by
  obtain ⟨ω, hω, h1⟩ := hU
  obtain ⟨v, hv⟩ := exists_ne (0 : X)
  have e : c • v = (ω z : ℂ) • v := (hc v).symm.trans (hω z v)
  have : c = (ω z : ℂ) := smul_left_injective ℂ hv e
  rw [this, h1]

/- English proof (translation)
Establish `h1` using `hasCentralChar_twist h (absPow k s)`. Rewrite `h1` using `[Fintype.card_fin]`. Conclude with `hasCentralChar_of_equiv (x.twEquiv _ _) h1`.
-/
theorem hasCentralChar_nu_u (x : IrrGL k) {ω : kˣ →* ℂˣ} (h : HasCentralChar x.rep ω) (s : ℂ) :
    HasCentralChar (x.nu s).rep (ω * absPow k s ^ x.1) := by
  have h1 := hasCentralChar_twist h (absPow k s)
  rw [Fintype.card_fin] at h1
  exact hasCentralChar_of_equiv (x.twEquiv _ _) h1

/- English proof (translation)
Establish `hz` using `nabs_pos' k z`. Establish `hω : ‖(ω z : ℂ)‖ ≠ 0` using `norm_ne_zero_iff.2 (ω z).ne_zero`. Rewrite using `[MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul, Units.val_pow_eq_pow_val, val_absPow_ofReal, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hz.le _), Real.log_mul hω (pow_ne_zero _ (Real.rpow_pos_of_pos hz _).ne'), Real.log_pow, Real.log_rp …`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem log_norm_mul_absPow_u (ω : kˣ →* ℂˣ) (t : ℝ) (d : ℕ) (z : kˣ) :
    Real.log ‖(((ω * absPow k (t : ℂ) ^ d) z : ℂˣ) : ℂ)‖ =
      Real.log ‖(ω z : ℂ)‖ + d * t * Real.log (nabs k z) := by
  have hz := nabs_pos' k z
  have hω : ‖(ω z : ℂ)‖ ≠ 0 := norm_ne_zero_iff.2 (ω z).ne_zero
  rw [MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul, Units.val_pow_eq_pow_val, val_absPow_ofReal,
    norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hz.le _),
    Real.log_mul hω (pow_ne_zero _ (Real.rpow_pos_of_pos hz _).ne'), Real.log_pow, Real.log_rpow hz]
  ring

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [Finset.sum_range_succ, add_mul, ih]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_range_mul_two_u (l : ℕ) : (∑ i ∈ Finset.range l, (i : ℝ)) * 2 = l * ((l : ℝ) - 1) := by
  induction l with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, add_mul, ih]; push_cast; ring

/- English proof (translation)
Take `⟨hd, hi, f, hf, -⟩` from `hL`. Establish `hterm : ∀ a : Fin Δ.len, HasCentralChar (Δ.term a).rep (ω * absPow k (((a : ℕ) : ℝ) : ℂ) ^ Δ.d)` using `fun a => by`. Establish `h` using `hasCentralChar_nu_u Δ.first hω ((a : ℕ) : ℂ)`. Rewrite using `[Complex.ofReal_natCast]`. Conclude with `h`.

Establish `hsc : ∀ v, δ.rep (GeneralLinearGroup.scalar (Fin δ.1) z) v = (∏ a : Fin Δ.len, (((ω * absPow k (((a : ℕ) : ℝ) : ℂ) ^ Δ.d) z : ℂˣ) : ℂ)) • v`. Introduce `v`. Take `⟨w, rfl⟩` from `hf v`. Establish `h1` using `GlobalTheory.BoundaryMaps.multiProd_scalar (stdBlocks (fun a => (Δ.term a).1) hd) (fun a => (Δ.term a).rep) _ hterm z w`. Rewrite using `[← f.isIntertwining]`.

Conclude with `(congrArg f h1).trans (map_smul f _ _)`. Use `haveI := Model.nontrivial_of_isIrreducible hi`. Establish `hc` using `congrArg Real.log (norm_eq_one_of_unitCC hU hsc)`. Rewrite `hc` using `[norm_prod, Real.log_one, Real.log_prod fun a _ => norm_ne_zero_iff.2 (Units.ne_zero _)]`. Simplify using `only [log_norm_mul_absPow_u] at hc`.

Rewrite `hc` using `[Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul, ← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun i => (i : ℝ)) Δ.len]`. Establish `hS` using `sum_range_mul_two_u Δ.len`. Establish `hl : (Δ.len : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 Δ.len_pos.ne'`. Apply `mul_left_cancel₀ hl` to reduce the goal to its premises. Take the linear combination `hc - ((Δ.d : ℝ) * Real.log (nabs k z) / 2) * hS`.
-/
theorem log_norm_centralChar_u {δ : IrrGL k} {Δ : Segment k} (hL : IsLSeg Δ δ.rep) (hU : UnitCC δ.rep)
    {ω : kˣ →* ℂˣ} (hω : HasCentralChar Δ.first.rep ω) (z : kˣ) :
    Real.log ‖(ω z : ℂ)‖ = -((Δ.d : ℝ) * ((Δ.len : ℝ) - 1) / 2) * Real.log (nabs k z) := by
  obtain ⟨hd, hi, f, hf, -⟩ := hL
  have hterm : ∀ a : Fin Δ.len,
      HasCentralChar (Δ.term a).rep (ω * absPow k (((a : ℕ) : ℝ) : ℂ) ^ Δ.d) := fun a => by
    have h := hasCentralChar_nu_u Δ.first hω ((a : ℕ) : ℂ)
    rw [Complex.ofReal_natCast]
    exact h
  have hsc : ∀ v, δ.rep (GeneralLinearGroup.scalar (Fin δ.1) z) v =
      (∏ a : Fin Δ.len, (((ω * absPow k (((a : ℕ) : ℝ) : ℂ) ^ Δ.d) z : ℂˣ) : ℂ)) • v := by
    intro v
    obtain ⟨w, rfl⟩ := hf v
    have h1 := GlobalTheory.BoundaryMaps.multiProd_scalar (stdBlocks (fun a => (Δ.term a).1) hd)
      (fun a => (Δ.term a).rep) _ hterm z w
    rw [← f.isIntertwining]
    exact (congrArg f h1).trans (map_smul f _ _)
  haveI := Model.nontrivial_of_isIrreducible hi
  have hc := congrArg Real.log (norm_eq_one_of_unitCC hU hsc)
  rw [norm_prod, Real.log_one, Real.log_prod fun a _ => norm_ne_zero_iff.2 (Units.ne_zero _)] at hc
  simp only [log_norm_mul_absPow_u] at hc
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.sum_mul, ← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun i => (i : ℝ)) Δ.len] at hc
  have hS := sum_range_mul_two_u Δ.len
  have hl : (Δ.len : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Δ.len_pos.ne'
  apply mul_left_cancel₀ hl
  linear_combination hc - ((Δ.d : ℝ) * Real.log (nabs k z) / 2) * hS

/- English proof (translation)
Take `⟨⟨-, -, hnsub⟩, j, hj, hfirst⟩` from `hP`. Establish `hf : Δ'.first.nu (y : ℂ) = (Δ.first.nu (x : ℂ)).nu (j : ℂ)` using `hfirst`. Establish `hρ' : Δ'.first = Δ.first.nu (((x + j - y : ℝ)) : ℂ)`. Establish `h1` using `congrArg (fun r => r.nu (-(y : ℂ))) hf`. Simplify using `only [IrrGL.nu_nu, add_neg_cancel, IrrGL.nu_zero] at h1`.

Rewrite using `[h1]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hd : Δ'.d = Δ.d` using `congrArg Sigma.fst hρ'`.

Take `⟨ω, -, hω⟩` from `exists_smooth_hasCentralChar Δ.first.2.rep.smooth Δ.first.2.rep.irr`. Establish `hω' : HasCentralChar Δ'.first.rep (ω * absPow k (((x + j - y : ℝ)) : ℂ) ^ Δ.first.1)`. Rewrite using `[hρ']`. Conclude with `hasCentralChar_nu_u _ hω _`. Take `⟨ϖ, hϖ⟩` from `exists_uniformizer k`.

Establish `hne : nabs k ϖ ≠ 1` using `fun e => uniformizer_lt_one.ne (hϖ ▸ (nabs_eq_one_iff ϖ).1 e)`. Establish `hL0 : Real.log (nabs k ϖ) ≠ 0` using `Real.log_ne_zero_of_pos_of_ne_one (nabs_pos' k ϖ) hne`. Establish `hA` using `log_norm_centralChar_u hL hU hω ϖ`. Establish `hA'` using `log_norm_centralChar_u hL' hU' hω' ϖ`. Rewrite `hA'` using `[log_norm_mul_absPow_u, hd]`.

Establish `hdL : (Δ.d : ℝ) * Real.log (nabs k ϖ) ≠ 0` using `mul_ne_zero (Nat.cast_ne_zero.2 Δ.d_pos.ne') hL0`. Establish `ht : x + j - y = ((Δ.len : ℝ) - Δ'.len) / 2`. Apply `mul_left_cancel₀ hdL` to reduce the goal to its premises. Establish `e1 : (Δ.first.1 : ℝ) = Δ.d` using `rfl`. Rewrite `hA'` using `[e1]`.

Take the linear combination `hA' - hA`. Establish `hlen : Δ.len < j + Δ'.len`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Apply `hnsub` to reduce the goal to its premises.

Introduce `w hw`. Take `⟨a, ha, rfl⟩` from `Segment.mem_carrier.1 hw`. Use `Segment.mem_carrier.2 ⟨j + a, ?_, ?_⟩` and prove the remaining obligations. Establish `ha' : a < Δ'.len` using `ha show j + a < Δ.len`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[hfirst, IrrGL.nu_nu]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hj1 : (1 : ℝ) ≤ j` using `by exact_mod_cast hj`. Establish `hl1 : (Δ.len : ℝ) + 1 ≤ j + Δ'.len` using `by exact_mod_cast hlen`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem add_one_le_of_precedes_u (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (δ δ' : IrrGL k) (Δ Δ' : Segment k) (hL : IsLSeg Δ δ.rep) (hU : UnitCC δ.rep) (hL' : IsLSeg Δ' δ'.rep)
    (hU' : UnitCC δ'.rep) (x y : ℝ) (hP : (Δ.nu x).Precedes (Δ'.nu y)) : x + 1 ≤ y := by
  obtain ⟨⟨-, -, hnsub⟩, j, hj, hfirst⟩ := hP
  have hf : Δ'.first.nu (y : ℂ) = (Δ.first.nu (x : ℂ)).nu (j : ℂ) := hfirst
  have hρ' : Δ'.first = Δ.first.nu (((x + j - y : ℝ)) : ℂ) := by
    have h1 := congrArg (fun r => r.nu (-(y : ℂ))) hf
    simp only [IrrGL.nu_nu, add_neg_cancel, IrrGL.nu_zero] at h1
    rw [h1]
    congr 1
    push_cast
    ring
  have hd : Δ'.d = Δ.d := congrArg Sigma.fst hρ'
  obtain ⟨ω, -, hω⟩ := exists_smooth_hasCentralChar Δ.first.2.rep.smooth Δ.first.2.rep.irr
  have hω' : HasCentralChar Δ'.first.rep (ω * absPow k (((x + j - y : ℝ)) : ℂ) ^ Δ.first.1) := by
    rw [hρ']
    exact hasCentralChar_nu_u _ hω _
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer k
  have hne : nabs k ϖ ≠ 1 := fun e => uniformizer_lt_one.ne (hϖ ▸ (nabs_eq_one_iff ϖ).1 e)
  have hL0 : Real.log (nabs k ϖ) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (nabs_pos' k ϖ) hne
  have hA := log_norm_centralChar_u hL hU hω ϖ
  have hA' := log_norm_centralChar_u hL' hU' hω' ϖ
  rw [log_norm_mul_absPow_u, hd] at hA'
  have hdL : (Δ.d : ℝ) * Real.log (nabs k ϖ) ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.2 Δ.d_pos.ne') hL0
  have ht : x + j - y = ((Δ.len : ℝ) - Δ'.len) / 2 := by
    apply mul_left_cancel₀ hdL
    have e1 : (Δ.first.1 : ℝ) = Δ.d := rfl
    rw [e1] at hA'
    linear_combination hA' - hA
  have hlen : Δ.len < j + Δ'.len := by
    by_contra hcon
    push_neg at hcon
    apply hnsub
    intro w hw
    obtain ⟨a, ha, rfl⟩ := Segment.mem_carrier.1 hw
    refine Segment.mem_carrier.2 ⟨j + a, ?_, ?_⟩
    · have ha' : a < Δ'.len := ha
      show j + a < Δ.len
      omega
    · rw [hfirst, IrrGL.nu_nu]
      push_cast
      rfl
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hl1 : (Δ.len : ℝ) + 1 ≤ j + Δ'.len := by exact_mod_cast hlen
  linarith

end PositivityTheory.RgUd.UOrder
