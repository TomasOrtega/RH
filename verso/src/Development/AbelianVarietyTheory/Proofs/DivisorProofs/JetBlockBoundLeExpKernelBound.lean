import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.BlockNumber

/- English proof (translation)
Establish `hr : ∀ l : Fin a, ((y l : ℚ) : ℝ) = (nu.w l : ℝ)` using `fun l => by rw [← hy l]; simp`. Establish `hs : ((∑ i ∈ Finset.range a, y i : ℚ) : ℝ) = (GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.size nu : ℝ)`. Rewrite using `[Finset.sum_range, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.size]`. Use `push_cast`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Rewrite using `[hr l]`. Use `Int.toNat_of_nonneg (h0 l)` as an intermediate fact. Conclude with `this.symm` after adjusting the coercions. Establish `hp : (∑ i ∈ Finset.range a, Formalism.LatticeIndexTer.ph ((y i : ℚ) : ℝ)) = ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.ph (nu.w i : ℝ)`. Rewrite using `[Finset.sum_range (fun i => Formalism.LatticeIndexTer.ph ((y i : ℚ) : ℝ))]`.

Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[hr l]`. Both sides reduce to the same expression. Rewrite using `[hs, hp]`. Use `set s := GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.size nu`.

Establish `hpos : (0 : ℝ) < 2 * (s : ℝ) + 2` using `by positivity`. Establish `e1 : (Real.exp L)⁻¹ ^ s = Real.exp (-((s : ℝ) * L))`. Rewrite using `[← Real.exp_neg, ← Real.exp_nat_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `e2 : (2 * (s : ℝ) + 2) ^ (2 * (a * b)) = Real.exp (2 * ((a : ℝ) * b) * Real.log (2 * (s : ℝ) + 2))` using `by conv_lhs => rw [← Real.exp_log hpos, ← Real.exp_nat_mul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, e2, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem factor_eq_exp {a : ℕ} (nu : DomWeight a) (y : ℕ → ℚ) (b : ℕ) (L : ℝ) (h0 : ∀ l, 0 ≤ nu.w l)
    (hy : ∀ l : Fin a, ((nu.w l : ℤ) : ℚ) = y l) :
    (Real.exp L)⁻¹ ^ GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.size nu * Real.exp 1 * (2 * (GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.size nu : ℝ) + 2) ^ (2 * (a * b)) *
      Real.exp (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.ph (nu.w i : ℝ)) =
    Real.exp (((∑ i ∈ Finset.range a, Formalism.LatticeIndexTer.ph ((y i : ℚ) : ℝ)) - ((∑ i ∈ Finset.range a, y i : ℚ) : ℝ) * L) +
      (1 + 2 * ((a : ℝ) * b) * Real.log (2 * ((∑ i ∈ Finset.range a, y i : ℚ) : ℝ) + 2))) := by
  have hr : ∀ l : Fin a, ((y l : ℚ) : ℝ) = (nu.w l : ℝ) := fun l => by rw [← hy l]; simp
  have hs : ((∑ i ∈ Finset.range a, y i : ℚ) : ℝ) = (GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.size nu : ℝ) := by
    rw [Finset.sum_range, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.size]
    push_cast
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hr l]
    have := Int.toNat_of_nonneg (h0 l)
    exact_mod_cast this.symm
  have hp : (∑ i ∈ Finset.range a, Formalism.LatticeIndexTer.ph ((y i : ℚ) : ℝ)) = ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.ph (nu.w i : ℝ) := by
    rw [Finset.sum_range (fun i => Formalism.LatticeIndexTer.ph ((y i : ℚ) : ℝ))]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hr l]; rfl
  rw [hs, hp]
  set s := GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.size nu
  have hpos : (0 : ℝ) < 2 * (s : ℝ) + 2 := by positivity
  have e1 : (Real.exp L)⁻¹ ^ s = Real.exp (-((s : ℝ) * L)) := by
    rw [← Real.exp_neg, ← Real.exp_nat_mul]; congr 1; ring
  have e2 : (2 * (s : ℝ) + 2) ^ (2 * (a * b)) = Real.exp (2 * ((a : ℝ) * b) * Real.log (2 * (s : ℝ) + 2)) := by
    conv_lhs => rw [← Real.exp_log hpos, ← Real.exp_nat_mul]
    congr 1; push_cast; ring
  rw [e1, e2, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1; ring

/- English proof (translation)
Establish `hT' : (1 : ℝ) ≤ T` using `by exact_mod_cast hT`. Establish `hGT : 1 ≤ G * T` using `one_le_mul_of_one_le_of_one_le hG hT'`. Establish `hx : (0 : ℝ) < 2 * (g : ℝ) * r + 1` using `by positivity`. Establish `h8 : (0 : ℝ) < 8 + 32 * (g : ℝ) * (r / 2)` using `by positivity`. Establish `e1 : Real.exp ((g : ℝ) * Real.log (8 + 32 * (g : ℝ) * (r / 2))) = 8 ^ g * (2 * (g : ℝ) * r + 1) ^ g`.

Rewrite using `[Real.exp_nat_mul, Real.exp_log h8, ← mul_pow]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : Real.exp (2 * (((C : ℝ) + 4) * A * Real.log (G * T))) = (G * T) ^ (2 * (C * A)) * (G * T) ^ (8 * A)`. Rewrite using `[← pow_add]`.

Use `conv_rhs => rw [← Real.exp_log (show (0 : ℝ) < G * T by linarith), ← Real.exp_nat_mul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e3 : Real.exp (L / 2) ^ 2 = Real.exp L`.

Rewrite using `[← Real.exp_nat_mul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Real.exp_add, Real.exp_add, e1, e2, mul_pow, mul_pow, mul_pow, e3, Real.sq_sqrt (by positivity), ← pow_mul, ← pow_mul]`.

Establish `b1 : G ^ (C * A * 2) ≤ (G * T) ^ (2 * (C * A))`. Rewrite using `[mul_comm (C * A) 2]`. Conclude with `pow_le_pow_left₀ (by linarith) (le_mul_of_one_le_right (by linarith) hT') _`. Establish `b2 : ((T : ℝ) * G) ^ (2 * (2 * g) * 2) ≤ (G * T) ^ (8 * A)`. Rewrite using `[mul_comm (T : ℝ) G]`.

Conclude with `pow_le_pow_right₀ hGT (by omega)`. Establish `b3 : (3 : ℝ) ≤ 8 ^ g`. Combine the equalities or inequalities in the displayed calculation. Establish `hG0 : 0 ≤ G` using `by linarith`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem sq_le_exp (C A g T : ℕ) (G r L : ℝ) (hG : 1 ≤ G) (hT : 1 ≤ T) (hr : 0 ≤ r) (hg : 1 ≤ g) (hA : g ≤ A) :
    (G ^ (C * A) * ((T : ℝ) * G) ^ (2 * (2 * g)) * Real.sqrt (3 * (2 * (g : ℝ) * r + 1) ^ g) * Real.exp (L / 2)) ^ 2 ≤
      Real.exp (L + ((g : ℝ) * Real.log (8 + 32 * (g : ℝ) * (r / 2)) + 2 * (((C : ℝ) + 4) * A * Real.log (G * T)))) := by
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hGT : 1 ≤ G * T := one_le_mul_of_one_le_of_one_le hG hT'
  have hx : (0 : ℝ) < 2 * (g : ℝ) * r + 1 := by positivity
  have h8 : (0 : ℝ) < 8 + 32 * (g : ℝ) * (r / 2) := by positivity
  have e1 : Real.exp ((g : ℝ) * Real.log (8 + 32 * (g : ℝ) * (r / 2))) = 8 ^ g * (2 * (g : ℝ) * r + 1) ^ g := by
    rw [Real.exp_nat_mul, Real.exp_log h8, ← mul_pow]; congr 1; ring
  have e2 : Real.exp (2 * (((C : ℝ) + 4) * A * Real.log (G * T))) = (G * T) ^ (2 * (C * A)) * (G * T) ^ (8 * A) := by
    rw [← pow_add]
    conv_rhs => rw [← Real.exp_log (show (0 : ℝ) < G * T by linarith), ← Real.exp_nat_mul]
    congr 1; push_cast; ring
  have e3 : Real.exp (L / 2) ^ 2 = Real.exp L := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [Real.exp_add, Real.exp_add, e1, e2, mul_pow, mul_pow, mul_pow, e3, Real.sq_sqrt (by positivity), ← pow_mul, ← pow_mul]
  have b1 : G ^ (C * A * 2) ≤ (G * T) ^ (2 * (C * A)) := by
    rw [mul_comm (C * A) 2]
    exact pow_le_pow_left₀ (by linarith) (le_mul_of_one_le_right (by linarith) hT') _
  have b2 : ((T : ℝ) * G) ^ (2 * (2 * g) * 2) ≤ (G * T) ^ (8 * A) := by
    rw [mul_comm (T : ℝ) G]
    exact pow_le_pow_right₀ hGT (by omega)
  have b3 : (3 : ℝ) ≤ 8 ^ g := by
    calc (3 : ℝ) ≤ 8 ^ 1 := by norm_num
      _ ≤ 8 ^ g := pow_le_pow_right₀ (by norm_num) hg
  have hG0 : 0 ≤ G := by linarith
  calc G ^ (C * A * 2) * ((T : ℝ) * G) ^ (2 * (2 * g) * 2) * (3 * (2 * (g : ℝ) * r + 1) ^ g) * Real.exp L
      ≤ (G * T) ^ (2 * (C * A)) * (G * T) ^ (8 * A) * (8 ^ g * (2 * (g : ℝ) * r + 1) ^ g) * Real.exp L := by gcongr
    _ = _ := by ring

/- English proof (translation)
Introduce `C`. Use `⟨(C : ℝ) + 4, by positivity, ?_⟩` and prove the remaining obligations. Introduce `N δ T i ι _ pl nu logOm logTh hi hT h0 hy`. Establish `hm` using `N.R.two_le_m`. Establish `hk` using `N.R.m_add_three_le_k`.

Establish `ha : 1 ≤ N.R.N i` using `by unfold Ranks.N; omega`. Establish `hb : 1 ≤ N.R.N (i + 1)` using `by unfold Ranks.N; omega`. Establish `hf : 1 ≤ N.R.f`. Establish `: 0 < N.R.ord` using `N.R.ord_pos`. Unfold `Ranks.f Ranks.n`.

Use linear arithmetic over natural numbers and integers. Establish `haN : N.R.N i ≤ N.Nm`. Unfold `NumDatum.Nm Ranks.N`. Conclude with `Nat.add_le_add_left (Nat.mul_le_mul_right _ hi.le) _`. Establish `hbN : N.R.N (i + 1) ≤ N.Nm`.

Unfold `NumDatum.Nm Ranks.N`. Conclude with `Nat.add_le_add_left (Nat.mul_le_mul_right _ hi) _`. Establish `hg : 1 ≤ N.R.f * N.R.N i * N.R.N (i + 1)` using `Nat.mul_pos (Nat.mul_pos hf ha) hb`. Establish `hA : N.R.f * N.R.N i * N.R.N (i + 1) ≤ N.R.f * N.R.m ^ 2 * N.Nm ^ 2`. Establish `h1 : 1 ≤ N.R.m ^ 2` using `Nat.one_le_pow _ _ (by omega)`.

Combine the equalities or inequalities in the displayed calculation. Establish `hG : (1 : ℝ) ≤ (N.g 0 : ℝ) * N.g 1` using `one_le_mul_of_one_le_of_one_le (by exact_mod_cast (N.g_prime 0).one_le) (by exact_mod_cast (N.g_prime 1).one_le)`. Establish `hr : 0 ≤ N.rd` using `by unfold NumDatum.rd Formalism.HC.HostRaw.rd; positivity`. Establish `key` using `sq_le_exp C _ _ T _ N.rd logTh hG (by omega) hr hg hA`. Establish `hprod` using `fun z : RPl N.R => factor_eq_exp (nu (pl z)) (N.nu δ (i + 1) z) (N.R.N (i + 1)) (logOm z) (h0 _) (hy z)`.

Unfold `GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.tmax`. Rewrite using `[← pl.prod_comp]`. Simplify using `only [Equiv.symm_apply_apply]`. Rewrite using `[Finset.prod_congr rfl fun z _ => hprod z, ← Real.exp_sum]`. Establish `e1 : C * N.R.f * N.R.m ^ 2 * N.Nm ^ 2 = C * (N.R.f * N.R.m ^ 2 * N.Nm ^ 2)` using `by ring`.

Establish `e2 : 2 * N.R.f * N.R.N i * N.R.N (i + 1) = 2 * (N.R.f * N.R.N i * N.R.N (i + 1))` using `by ring`. Establish `e3 : ((T * (N.g 0 * N.g 1) : ℕ) : ℝ) = (T : ℝ) * ((N.g 0 : ℝ) * N.g 1)` using `by push_cast; ring`. Rewrite using `[e1, e2, e3]`. Use `(mul_le_mul_of_nonneg_right key (Real.exp_pos _).le).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[← Real.exp_add]`.

Use `congr 1`. Unfold `kernelBound_sq NumDatum.nuAbs NumDatum.v`. Simplify using `only [Nat.add_sub_cancel, Finset.sum_add_distrib, Nat.cast_one, mul_one, Real.log_one]`. Use `push_cast`. Simplify using `only [mul_assoc]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem tmax_le_exp_kernelBound : ∀ C : ℕ, ∃ CK : ℝ, 0 ≤ CK ∧ ∀ (N : NumDatum) (δ : Code N) (T : ℕ) (i : ℕ) (ι : Type) [Fintype ι] (pl : RPl N.R ≃ ι) (nu : ι → DomWeight (N.R.N i)) (logOm : RPl N.R → ℝ) (logTh : ℝ), i < N.R.m → 2 ≤ T → (∀ τ l, 0 ≤ (nu τ).w l) → (∀ (z : RPl N.R) (l : Fin (N.R.N i)), (((nu (pl z)).w l : ℤ) : ℚ) = N.nu δ (i + 1) z l) → GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.tmax (N.R.N (i + 1)) nu (((N.g 0 : ℝ) * N.g 1) ^ (C * N.R.f * N.R.m ^ 2 * N.Nm ^ 2) * ((T * (N.g 0 * N.g 1) : ℕ) : ℝ) ^ (2 * (2 * N.R.f * N.R.N i * N.R.N (i + 1))) * Real.sqrt (3 * (2 * ((N.R.f * N.R.N i * N.R.N (i + 1) : ℕ) : ℝ) * N.rd + 1) ^ (N.R.f * N.R.N i * N.R.N (i + 1))) * Real.exp (logTh / 2)) (fun τ => Real.exp (logOm (pl.symm τ))) ≤ Real.exp (kernelBound_sq N δ T CK (i + 1) logOm logTh 1 1 1 1) := by
  intro C
  refine ⟨(C : ℝ) + 4, by positivity, ?_⟩
  intro N δ T i ι _ pl nu logOm logTh hi hT h0 hy
  have hm := N.R.two_le_m
  have hk := N.R.m_add_three_le_k
  have ha : 1 ≤ N.R.N i := by unfold Ranks.N; omega
  have hb : 1 ≤ N.R.N (i + 1) := by unfold Ranks.N; omega
  have hf : 1 ≤ N.R.f := by
    have : 0 < N.R.ord := N.R.ord_pos
    unfold Ranks.f Ranks.n; omega
  have haN : N.R.N i ≤ N.Nm := by
    unfold NumDatum.Nm Ranks.N
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hi.le) _
  have hbN : N.R.N (i + 1) ≤ N.Nm := by
    unfold NumDatum.Nm Ranks.N
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hi) _
  have hg : 1 ≤ N.R.f * N.R.N i * N.R.N (i + 1) := Nat.mul_pos (Nat.mul_pos hf ha) hb
  have hA : N.R.f * N.R.N i * N.R.N (i + 1) ≤ N.R.f * N.R.m ^ 2 * N.Nm ^ 2 := by
    have h1 : 1 ≤ N.R.m ^ 2 := Nat.one_le_pow _ _ (by omega)
    calc N.R.f * N.R.N i * N.R.N (i + 1) = N.R.f * 1 * (N.R.N i * N.R.N (i + 1)) := by ring
      _ ≤ N.R.f * N.R.m ^ 2 * (N.Nm * N.Nm) := by gcongr
      _ = _ := by ring
  have hG : (1 : ℝ) ≤ (N.g 0 : ℝ) * N.g 1 :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast (N.g_prime 0).one_le) (by exact_mod_cast (N.g_prime 1).one_le)
  have hr : 0 ≤ N.rd := by unfold NumDatum.rd Formalism.HC.HostRaw.rd; positivity
  have key := sq_le_exp C _ _ T _ N.rd logTh hG (by omega) hr hg hA
  have hprod := fun z : RPl N.R => factor_eq_exp (nu (pl z)) (N.nu δ (i + 1) z) (N.R.N (i + 1)) (logOm z) (h0 _) (hy z)
  unfold GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.tmax
  rw [← pl.prod_comp]
  simp only [Equiv.symm_apply_apply]
  rw [Finset.prod_congr rfl fun z _ => hprod z, ← Real.exp_sum]
  have e1 : C * N.R.f * N.R.m ^ 2 * N.Nm ^ 2 = C * (N.R.f * N.R.m ^ 2 * N.Nm ^ 2) := by ring
  have e2 : 2 * N.R.f * N.R.N i * N.R.N (i + 1) = 2 * (N.R.f * N.R.N i * N.R.N (i + 1)) := by ring
  have e3 : ((T * (N.g 0 * N.g 1) : ℕ) : ℝ) = (T : ℝ) * ((N.g 0 : ℝ) * N.g 1) := by push_cast; ring
  rw [e1, e2, e3]
  refine (mul_le_mul_of_nonneg_right key (Real.exp_pos _).le).trans (le_of_eq ?_)
  rw [← Real.exp_add]
  congr 1
  unfold kernelBound_sq NumDatum.nuAbs NumDatum.v
  simp only [Nat.add_sub_cancel, Finset.sum_add_distrib, Nat.cast_one, mul_one, Real.log_one]
  push_cast
  simp only [mul_assoc]
  ring

end GlobalTheory.BlockNumber
