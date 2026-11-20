import Mathlib
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice
import Formalism.HarderNarasimhan.FinalCor
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.TraceFormulaOfRankDegree
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.ESMulESOfNeZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.CharacteristicPolynomialCompatibility
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.NormAtAddLe
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.DegGeOfInj
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.FgOfLeL
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.DegTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.RankIdentity
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.PerSAlg
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.MemRangeIdem

noncomputable section

namespace PI.Dv.Tr

open PI.Dv Module NumberField

section Helpers

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]

open Classical in
/- English proof (translation)
Rewrite using `[phi_apply]`. Use `A.L.sum_mem fun h _ => ?_` and prove the remaining obligations. Establish `hint : IsIntegral ℤ ((((Q.chi h)⁻¹ : Kˣ) : K))` using `IsIntegral.of_pow Fintype.card_pos (by rw [chi_pow]; exact isIntegral_one)`. Establish `hmem : ρ (h : G) (ρ g y) ∈ A.L` using `hA.2.1 _ _ (hA.2.1 _ _ hy)`. Take `⟨r, hr⟩ : ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = (((Q.chi h)⁻¹ : Kˣ) : K)` from `⟨⟨_, hint⟩, rfl⟩`.

Rewrite using `[← hr, algebraMap_smul]`. Conclude with `A.L.smul_mem r hmem`.
-/
lemma epsSum_mem (A : Formalism.BasicNotions.HLat K) (ρ : Representation K G A.V) (hA : IsGLat A ρ) (Q : Pair K G) (g : G)
    (y : A.V) (hy : y ∈ A.L) : ρ.asAlgebraHom (epsSum Q * MonoidAlgebra.of K G g) y ∈ A.L := by
  rw [phi_apply]
  refine A.L.sum_mem fun h _ => ?_
  have hint : IsIntegral ℤ ((((Q.chi h)⁻¹ : Kˣ) : K)) :=
    IsIntegral.of_pow Fintype.card_pos (by rw [chi_pow]; exact isIntegral_one)
  have hmem : ρ (h : G) (ρ g y) ∈ A.L := hA.2.1 _ _ (hA.2.1 _ _ hy)
  obtain ⟨r, hr⟩ : ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = (((Q.chi h)⁻¹ : Kˣ) : K) := ⟨⟨_, hint⟩, rfl⟩
  rw [← hr, algebraMap_smul]
  exact A.L.smul_mem r hmem

open Classical in
/- English proof (translation)
Rewrite using `[phi_apply]`. Use `(normAt_sum_le' A.b A.X v _ _).trans (le_of_eq ?_)` and prove the remaining obligations. Establish `hterm : ∀ h : Q.H, Formalism.HermitianLatticesTheory.normAt A.b A.X v ((((Q.chi h)⁻¹ : Kˣ) : K) • ρ (h : G) (ρ g y)) = Formalism.HermitianLatticesTheory.normAt A.b A.X v y`. Introduce `h`. Rewrite using `[normAt_smul', hA.2.2, hA.2.2]`.

Establish `hn : ‖v.embedding ((((Q.chi h)⁻¹ : Kˣ) : K))‖ = 1` using `Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, chi_pow, map_one]) Fintype.card_ne_zero`. Rewrite using `[hn, one_mul]`. Simplify using `only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`.
-/
lemma epsSum_norm (A : Formalism.BasicNotions.HLat K) (ρ : Representation K G A.V) (hA : IsGLat A ρ) (Q : Pair K G) (g : G)
    (v : InfinitePlace K) (y : A.V) :
    Formalism.HermitianLatticesTheory.normAt A.b A.X v (ρ.asAlgebraHom (epsSum Q * MonoidAlgebra.of K G g) y) ≤
      (Fintype.card Q.H : ℝ) * Formalism.HermitianLatticesTheory.normAt A.b A.X v y := by
  rw [phi_apply]
  refine (normAt_sum_le' A.b A.X v _ _).trans (le_of_eq ?_)
  have hterm : ∀ h : Q.H, Formalism.HermitianLatticesTheory.normAt A.b A.X v ((((Q.chi h)⁻¹ : Kˣ) : K) • ρ (h : G) (ρ g y)) =
      Formalism.HermitianLatticesTheory.normAt A.b A.X v y := by
    intro h
    rw [normAt_smul', hA.2.2, hA.2.2]
    have hn : ‖v.embedding ((((Q.chi h)⁻¹ : Kˣ) : K))‖ = 1 :=
      Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, chi_pow, map_one]) Fintype.card_ne_zero
    rw [hn, one_mul]
  simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

open Classical in
/- English proof (translation)
Rewrite using `[epsSum_eq, smul_mul_assoc, map_smul, LinearMap.smul_apply]`.
-/
lemma epsSum_apply_smul {V : Type} [AddCommGroup V] [Module K V] (ρ : Representation K G V) (Q : Pair K G) (g : G)
    (y : V) : ρ.asAlgebraHom (epsSum Q * MonoidAlgebra.of K G g) y =
      ((Fintype.card Q.H : ℕ) : K) • ρ.asAlgebraHom (eps Q * MonoidAlgebra.of K G g) y := by
  rw [epsSum_eq, smul_mul_assoc, map_smul, LinearMap.smul_apply]

end Helpers

section Ranges

variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G] (T : GoodSet K G) (s : T.S)
  {V : Type} [AddCommGroup V] [Module K V] (ρ : Representation K G V)

/- English proof (translation)
Take `⟨z, rfl⟩` from `hy`. Rewrite using `[← Module.End.mul_apply, ← map_mul, ← mul_assoc, ← eS_comm, mul_assoc, eS_idem]`.
-/
lemma e_fix (Q : Pair K G) (y : V) (hy : y ∈ LinearMap.range (ρ.asAlgebraHom (eps Q * eS T s))) :
    ρ.asAlgebraHom (eS T s) y = y := by
  obtain ⟨z, rfl⟩ := hy
  rw [← Module.End.mul_apply, ← map_mul, ← mul_assoc, ← eS_comm, mul_assoc, eS_idem]

/- English proof (translation)
Use `⟨ρ.asAlgebraHom (eps Q * MonoidAlgebra.of K G g) y, ?_⟩` and prove the remaining obligations. Use `conv_rhs => rw [← hy]`. Rewrite using `[← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]`. Use `congr 2`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma move_range (Q _Q' : Pair K G) (g : G) (y : V) (hy : ρ.asAlgebraHom (eS T s) y = y) :
    ρ.asAlgebraHom (eps Q * MonoidAlgebra.of K G g) y ∈ LinearMap.range (ρ.asAlgebraHom (eps Q * eS T s)) := by
  refine ⟨ρ.asAlgebraHom (eps Q * MonoidAlgebra.of K G g) y, ?_⟩
  conv_rhs => rw [← hy]
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  congr 2
  calc eps Q * eS T s * (eps Q * MonoidAlgebra.of K G g)
      = eps Q * ((eps Q * MonoidAlgebra.of K G g) * eS T s) := by rw [mul_assoc, eS_comm]
    _ = (eps Q * eps Q) * MonoidAlgebra.of K G g * eS T s := by simp only [mul_assoc]
    _ = eps Q * MonoidAlgebra.of K G g * eS T s := by rw [eps_idem]

end Ranges

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `K _ _ _ _ G _ _ T P0 P hM A ρ hA s`. Establish `hfd : FiniteDimensional K A.V` using `Module.Finite.of_basis A.b`. Use `set ρR := Formalism.HermitianLatticesTheory.realize A.b A.X with hρR`. Use `set n := nS T P s with hndef`. Use `set r0 := rS T P0 A ρ s with hr0def`.

Use `set L1s := cut A ρ (eps P * eS T s) A.L with hL1sdef`. Use `set L0s := cut A ρ (eps P0 * eS T s) A.L with hL0sdef`. Use `set dK : ℝ := (finrank ℚ K : ℝ) with hdK`. Establish `hdK0 : 0 < dK` using `by rw [hdK]; exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)`. Establish `hL1s : L1s ≤ A.L` using `inf_le_left`.

Establish `hL0s : L0s ≤ A.L` using `inf_le_left`. Establish `lat : ∀ N : Submodule (𝓞 K) A.V, N ≤ A.L → Formalism.HN.IsLat ρR N` using `fun N hN => (Formalism.HN.plLat K A.V A.ι A.b A.X hA.1.1 N (fg_of_le_L A hA.1 N hN)).1`. Establish `hrkZ : ∀ N : Submodule (𝓞 K) A.V, N ≤ A.L → (Formalism.HN.rk ρR N : ℝ) = dK * (Formalism.HN.rkK N : ℝ)`. Introduce `N hN`. Rewrite using `[(Formalism.HN.plLat K A.V A.ι A.b A.X hA.1.1 N (fg_of_le_L A hA.1 N hN)).2.1]`.

Use `push_cast`. Both sides reduce to the same expression. Establish `hrk1 : Formalism.HN.rkK L1s = n * r0` using `by show rkL A (cut A ρ (eps P * eS T s) A.L) = _`. Rewrite using `[rkL_cut A hA.1, finrank_range_eps_mul_eS_eq_nS_mul T P0 P hM ρ s, hr0def, rS, rkL_cut A hA.1]`. Establish `hrk0 : Formalism.HN.rkK L0s = r0` using `rfl`.

Distinguish the cases in `hn0 : n = 0`. Establish `h1 : degL A L1s = 0`. Unfold `degL`. Rewrite using `[hrk1, hn0, zero_mul, Nat.cast_zero, zero_mul]`. Rewrite using `[h1, hn0]`.

Simplify using the standard rewrite rules. Establish `hn1 : 1 ≤ n` using `Nat.one_le_iff_ne_zero.mpr hn0`. Take `⟨cB, g, h, hlift, hN⟩` from `choose_gh T s P0 P (hM s)`. Use `set Pi0 : Submodule (𝓞 K) (Fin n → A.V) := Submodule.pi Set.univ (fun _ => L0s) with hPi0`. Use `set ρP := Formalism.HN.piReal (fun _ : Fin n => ρR) with hρP`.

Take `⟨hPiLat, hPirk, hPideg, -⟩` from `Formalism.HN.piSum (𝓞 K) (Fin n) (fun _ => A.V) (fun _ => _) (fun _ => ρR) (fun _ => L0s) (fun _ => lat _ hL0s)`. Establish `hnormP : ∀ x : Fin n → A.V, ‖ρP x‖ ^ 2 = ∑ j, ‖ρR (x j)‖ ^ 2`. Introduce `x`. Rewrite using `[hρP, PiLp.norm_sq_eq_of_L2]`. Both sides reduce to the same expression.

Establish `hcoord : ∀ (x : Fin n → A.V) j, ‖ρR (x j)‖ ≤ ‖ρP x‖`. Introduce `x j`. Establish `h1 : ‖ρR (x j)‖ ^ 2 ≤ ‖ρP x‖ ^ 2`. Rewrite using `[hnormP]`. Conclude with `Finset.single_le_sum (f := fun j => ‖ρR (x j)‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)`.

Conclude with `(pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1`. Establish `hmemPi : ∀ x : Fin n → A.V, x ∈ Pi0 ↔ ∀ j, x j ∈ L0s`. Introduce `x`. Simplify using `[hPi0, Submodule.mem_pi]`. Establish `hHpos : (0 : ℝ) < Fintype.card P.H` using `by exact_mod_cast Fintype.card_pos`.

Establish `hH0pos : (0 : ℝ) < Fintype.card P0.H` using `by exact_mod_cast Fintype.card_pos`. Establish `hnpos : (0 : ℝ) < n` using `by exact_mod_cast hn1`. Establish `hHK : ((Fintype.card P.H : ℕ) : K) ≠ 0` using `by exact_mod_cast Fintype.card_ne_zero`. Establish `hH0K : ((Fintype.card P0.H : ℕ) : K) ≠ 0` using `by exact_mod_cast Fintype.card_ne_zero`. Set `fΦ : (Fin n → A.V) →+ A.V` to `{ toFun := fun y => ∑ i, ρ.asAlgebraHom (epsSum P * MonoidAlgebra.of K G (g i)) (y i) map_zero' := by simp map_add' := by intro y z; simp [Finset.sum_add_distrib] }`.

Establish `hfΦ : ∀ y, fΦ y = ∑ i, ρ.asAlgebraHom (epsSum P * MonoidAlgebra.of K G (g i)) (y i)` using `fun y => rfl`. Establish `hΦ1 : ∀ y ∈ Pi0, fΦ y ∈ L1s`. Introduce `y hy`. Rewrite `hy` using `[hmemPi]`. Rewrite using `[hfΦ]`.

Use `Submodule.mem_inf.mpr ⟨A.L.sum_mem fun i _ => epsSum_mem A ρ hA P (g i) _ (Submodule.mem_inf.mp (hy i)).1, ?_⟩` and prove the remaining obligations. Use `show _ ∈ LinearMap.range (ρ.asAlgebraHom (eps P * eS T s))`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[epsSum_apply_smul]`. Conclude with `Submodule.smul_mem _ _ (move_range T s ρ P P0 (g i) (y i) (e_fix T s ρ P0 (y i) (Submodule.mem_inf.mp (hy i)).2))`.

Establish `hΦ2 : ∀ y ∈ Pi0, fΦ y = 0 → y = 0`. Introduce `y hy h0`. Rewrite `hy` using `[hmemPi]`. Rewrite `h0` using `[hfΦ]`. Simplify using `only [epsSum_apply_smul, ← Finset.smul_sum] at h0`.

Establish `h0'` using `(smul_eq_zero.mp h0).resolve_left hHK`. Conclude with `inj_phi T s P0 P cB g h hlift ρ hN y (fun i => (Submodule.mem_inf.mp (hy i)).2) h0'`. Establish `hΦ3 : ∀ y ∈ Pi0, ‖ρR (fΦ y)‖ ≤ ((n : ℝ) * Fintype.card P.H) * ‖ρP y‖`. Introduce `y _`. Rewrite using `[hfΦ, map_sum]`.

Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations. Establish `hterm : ∀ i, ‖ρR (ρ.asAlgebraHom (epsSum P * MonoidAlgebra.of K G (g i)) (y i))‖ ≤ (Fintype.card P.H : ℝ) * ‖ρP y‖`. Introduce `i`. Use `(realize_le A.b A.X (fun z => ρ.asAlgebraHom (epsSum P * MonoidAlgebra.of K G (g i)) z) (Fintype.card P.H : ℝ) hHpos.le (fun v z => epsSum_norm A ρ hA P (g i) v z) (y i)).trans ?_` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_left (hcoord y i) hHpos.le`.

Use `(Finset.sum_le_sum fun i _ => hterm i).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Set `fΨ : A.V →+ (Fin n → A.V)` to `{ toFun := fun x j => ρ.asAlgebraHom (epsSum P0 * MonoidAlgebra.of K G (h j)) x map_zero' := by funext j; simp map_add' := by intro x y; funext j; simp }`. Establish `hfΨ : ∀ x j, fΨ x j = ρ.asAlgebraHom (epsSum P0 * MonoidAlgebra.of K G (h j)) x` using `fun x j => rfl`.

Establish `hΨ1 : ∀ x ∈ L1s, fΨ x ∈ Pi0`. Introduce `x hx`. Rewrite using `[hmemPi]`. Introduce `j`. Rewrite using `[hfΨ]`.

Use `Submodule.mem_inf.mpr ⟨epsSum_mem A ρ hA P0 (h j) x (Submodule.mem_inf.mp hx).1, ?_⟩` and prove the remaining obligations. Use `show _ ∈ LinearMap.range (ρ.asAlgebraHom (eps P0 * eS T s))`. Rewrite using `[epsSum_apply_smul]`. Conclude with `Submodule.smul_mem _ _ (move_range T s ρ P0 P (h j) x (e_fix T s ρ P x (Submodule.mem_inf.mp hx).2))`. Establish `hΨ2 : ∀ x ∈ L1s, fΨ x = 0 → x = 0`.

Introduce `x hx h0`. Use `inj_psi T s P0 P cB g h hlift ρ hM hN x (Submodule.mem_inf.mp hx).2 fun j => ?_` and prove the remaining obligations. Use `congrFun h0 j` as an intermediate fact. Rewrite `this` using `[hfΨ, epsSum_apply_smul]`. Conclude with `(smul_eq_zero.mp this).resolve_left hH0K`.

Establish `hΨ3 : ∀ x ∈ L1s, ‖ρP (fΨ x)‖ ≤ ((n : ℝ) * Fintype.card P0.H) * ‖ρR x‖`. Introduce `x _`. Establish `hj : ∀ j, ‖ρR (fΨ x j)‖ ≤ (Fintype.card P0.H : ℝ) * ‖ρR x‖` using `fun j => realize_le A.b A.X (fun z => ρ.asAlgebraHom (epsSum P0 * MonoidAlgebra.of K G (h j)) z) (Fintype.card P0.H : ℝ) hH0pos.le (fun v z => epsSum_norm A ρ hA P0 (h j) v z) x`. Establish `h3 : ‖ρP (fΨ x)‖ ^ 2 ≤ (((n : ℝ) * Fintype.card P0.H) * ‖ρR x‖) ^ 2`. Rewrite using `[hnormP]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Use `_ ≤ (n : ℝ) ^ 2 * ((Fintype.card P0.H : ℝ) * ‖ρR x‖) ^ 2 := by`. Apply `mul_le_mul_of_nonneg_right _ (sq_nonneg _)` to reduce the goal to its premises. Establish `: (1 : ℝ) ≤ n` using `by exact_mod_cast hn1`.

Use the polynomial consequences of the given equalities and inequalities. Use `_ = (((n : ℝ) * Fintype.card P0.H) * ‖ρR x‖) ^ 2 := by ring`. Conclude with `(pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h3`. Establish `hrkPi : (Formalism.HN.rk ρP Pi0 : ℝ) = dK * ((n * r0 : ℕ) : ℝ)`. Rewrite using `[hρP, hPi0, hPirk]`.

Use `push_cast`. Rewrite using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hrkZ L0s hL0s, hrk0]`. Expand and normalize the polynomial expressions, which then agree. Establish `hrkL1 : (Formalism.HN.rk ρR L1s : ℝ) = dK * ((n * r0 : ℕ) : ℝ)` using `by rw [hrkZ L1s hL1s, hrk1]`. Establish `hdegPi : Formalism.HN.deg ρP Pi0 = (n : ℝ) * Formalism.HN.deg ρR L0s`.

Rewrite using `[hρP, hPi0, hPideg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Establish `degΦ` using `deg_ge_of_inj ρP ρR Pi0 L1s hPiLat (lat L1s hL1s) fΦ hΦ1 hΦ2 (by exact_mod_cast hrkPi.trans hrkL1.symm) ((n : ℝ) * Fintype.card P.H) (by positivity) hΦ3`. Establish `degΨ` using `deg_ge_of_inj ρR ρP L1s Pi0 (lat L1s hL1s) hPiLat fΨ hΨ1 hΨ2 (by exact_mod_cast hrkL1.trans hrkPi.symm) ((n : ℝ) * Fintype.card P0.H) (by positivity) hΨ3`. Rewrite `degΦ` using `[hrkPi, hdegPi]`. Rewrite `degΨ` using `[hrkL1, hdegPi]`.

Establish `hG1 : (1 : ℝ) ≤ Fintype.card G` using `by exact_mod_cast Fintype.card_pos`. Establish `hla : 0 ≤ laG G` using `Real.log_nonneg hG1`. Establish `hnG : (n : ℝ) ≤ Fintype.card G`. Establish `h1 : n ≤ finrank K (T.W s)` using `Submodule.finrank_le _`. Establish `h2` using `dim_sq_le T s`.

Establish `h3 : finrank K (T.W s) ≤ finrank K (T.W s) * finrank K (T.W s)` using `Nat.le_mul_self _`. Conclude with `h1.trans (h3.trans h2)` after adjusting the coercions. Establish `hHG : (Fintype.card P.H : ℝ) ≤ Fintype.card G` using `by exact_mod_cast Fintype.card_subtype_le _`. Establish `hH0G : (Fintype.card P0.H : ℝ) ≤ Fintype.card G` using `by exact_mod_cast Fintype.card_subtype_le _`. Establish `hlog1 : Real.log ((n : ℝ) * Fintype.card P.H) ≤ 2 * laG G`.

Rewrite using `[Real.log_mul hnpos.ne' hHpos.ne']`. Establish `a1` using `Real.log_le_log hnpos hnG`. Establish `a2` using `Real.log_le_log hHpos hHG`. Unfold `laG`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hlog2 : Real.log ((n : ℝ) * Fintype.card P0.H) ≤ 2 * laG G`. Rewrite using `[Real.log_mul hnpos.ne' hH0pos.ne']`. Establish `a1` using `Real.log_le_log hnpos hnG`. Establish `a2` using `Real.log_le_log hH0pos hH0G`. Unfold `laG`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hc1` using `degL_eq A hA.1 L1s hL1s`. Establish `hc0` using `degL_eq A hA.1 L0s hL0s`. Rewrite `hc1` using `[hrk1]`. Rewrite `hc0` using `[hrk0]`.

Use `set R0 : ℝ := ((n * r0 : ℕ) : ℝ) with hR0`. Establish `hR0nn : 0 ≤ R0` using `Nat.cast_nonneg _`. Establish `hexpr : degL A L1s - (n : ℝ) * degL A L0s = (2 / dK) * (Formalism.HN.deg ρR L1s - (n : ℝ) * Formalism.HN.deg ρR L0s)`. Rewrite using `[hc1, hc0, hR0]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hD1 : -(dK * R0 * (2 * laG G)) ≤ Formalism.HN.deg ρR L1s - (n : ℝ) * Formalism.HN.deg ρR L0s`. Use `mul_le_mul_of_nonneg_left hlog1 (by positivity : (0 : ℝ) ≤ dK * R0)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hD2 : Formalism.HN.deg ρR L1s - (n : ℝ) * Formalism.HN.deg ρR L0s ≤ dK * R0 * (2 * laG G)`.

Use `mul_le_mul_of_nonneg_left hlog2 (by positivity : (0 : ℝ) ≤ dK * R0)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hc : 0 < 2 / dK` using `by positivity`. Establish `e1 : (2 / dK) * (dK * R0 * (2 * laG G)) = 4 * R0 * laG G` using `by field_simp; ring`. Establish `m1` using `mul_le_mul_of_nonneg_left hD1 hc.le`.

Establish `m2` using `mul_le_mul_of_nonneg_left hD2 hc.le`. Rewrite `m1` using `[mul_neg, e1]`. Rewrite `m2` using `[e1]`. Establish `hRla : 0 ≤ R0 * laG G` using `mul_nonneg hR0nn hla`. Use `show |degL A L1s - (n : ℝ) * degL A L0s| ≤ 5 * laG G * R0`.

Rewrite using `[hexpr, abs_le]`. Apply the tactic sequence `constructor <;> linarith`.
-/
theorem perSBound : PerSBound := by
  intro K _ _ _ _ G _ _ T P0 P hM A ρ hA s
  classical
  have hfd : FiniteDimensional K A.V := Module.Finite.of_basis A.b
  set ρR := Formalism.HermitianLatticesTheory.realize A.b A.X with hρR
  set n := nS T P s with hndef
  set r0 := rS T P0 A ρ s with hr0def
  set L1s := cut A ρ (eps P * eS T s) A.L with hL1sdef
  set L0s := cut A ρ (eps P0 * eS T s) A.L with hL0sdef
  set dK : ℝ := (finrank ℚ K : ℝ) with hdK
  have hdK0 : 0 < dK := by rw [hdK]; exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have hL1s : L1s ≤ A.L := inf_le_left
  have hL0s : L0s ≤ A.L := inf_le_left
  have lat : ∀ N : Submodule (𝓞 K) A.V, N ≤ A.L → Formalism.HN.IsLat ρR N :=
    fun N hN => (Formalism.HN.plLat K A.V A.ι A.b A.X hA.1.1 N (fg_of_le_L A hA.1 N hN)).1
  have hrkZ : ∀ N : Submodule (𝓞 K) A.V, N ≤ A.L → (Formalism.HN.rk ρR N : ℝ) = dK * (Formalism.HN.rkK N : ℝ) := by
    intro N hN
    rw [(Formalism.HN.plLat K A.V A.ι A.b A.X hA.1.1 N (fg_of_le_L A hA.1 N hN)).2.1]
    push_cast
    rfl
  have hrk1 : Formalism.HN.rkK L1s = n * r0 := by
    show rkL A (cut A ρ (eps P * eS T s) A.L) = _
    rw [rkL_cut A hA.1, finrank_range_eps_mul_eS_eq_nS_mul T P0 P hM ρ s, hr0def, rS, rkL_cut A hA.1]
  have hrk0 : Formalism.HN.rkK L0s = r0 := rfl
  by_cases hn0 : n = 0
  · have h1 : degL A L1s = 0 := by
      unfold degL; rw [hrk1, hn0, zero_mul, Nat.cast_zero, zero_mul]
    rw [h1, hn0]
    simp
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  obtain ⟨cB, g, h, hlift, hN⟩ := choose_gh T s P0 P (hM s)
  set Pi0 : Submodule (𝓞 K) (Fin n → A.V) := Submodule.pi Set.univ (fun _ => L0s) with hPi0
  set ρP := Formalism.HN.piReal (fun _ : Fin n => ρR) with hρP
  obtain ⟨hPiLat, hPirk, hPideg, -⟩ := Formalism.HN.piSum (𝓞 K) (Fin n) (fun _ => A.V) (fun _ => _)
    (fun _ => ρR) (fun _ => L0s) (fun _ => lat _ hL0s)
  have hnormP : ∀ x : Fin n → A.V, ‖ρP x‖ ^ 2 = ∑ j, ‖ρR (x j)‖ ^ 2 := by
    intro x
    rw [hρP, PiLp.norm_sq_eq_of_L2]
    rfl
  have hcoord : ∀ (x : Fin n → A.V) j, ‖ρR (x j)‖ ≤ ‖ρP x‖ := by
    intro x j
    have h1 : ‖ρR (x j)‖ ^ 2 ≤ ‖ρP x‖ ^ 2 := by
      rw [hnormP]
      exact Finset.single_le_sum (f := fun j => ‖ρR (x j)‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1
  have hmemPi : ∀ x : Fin n → A.V, x ∈ Pi0 ↔ ∀ j, x j ∈ L0s := by
    intro x; simp [hPi0, Submodule.mem_pi]
  have hHpos : (0 : ℝ) < Fintype.card P.H := by exact_mod_cast Fintype.card_pos
  have hH0pos : (0 : ℝ) < Fintype.card P0.H := by exact_mod_cast Fintype.card_pos
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hHK : ((Fintype.card P.H : ℕ) : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hH0K : ((Fintype.card P0.H : ℕ) : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero

  let fΦ : (Fin n → A.V) →+ A.V :=
    { toFun := fun y => ∑ i, ρ.asAlgebraHom (epsSum P * MonoidAlgebra.of K G (g i)) (y i)
      map_zero' := by simp
      map_add' := by intro y z; simp [Finset.sum_add_distrib] }
  have hfΦ : ∀ y, fΦ y = ∑ i, ρ.asAlgebraHom (epsSum P * MonoidAlgebra.of K G (g i)) (y i) := fun y => rfl
  have hΦ1 : ∀ y ∈ Pi0, fΦ y ∈ L1s := by
    intro y hy
    rw [hmemPi] at hy
    rw [hfΦ]
    refine Submodule.mem_inf.mpr ⟨A.L.sum_mem fun i _ => epsSum_mem A ρ hA P (g i) _ (Submodule.mem_inf.mp (hy i)).1, ?_⟩
    show _ ∈ LinearMap.range (ρ.asAlgebraHom (eps P * eS T s))
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [epsSum_apply_smul]
    exact Submodule.smul_mem _ _ (move_range T s ρ P P0 (g i) (y i)
      (e_fix T s ρ P0 (y i) (Submodule.mem_inf.mp (hy i)).2))
  have hΦ2 : ∀ y ∈ Pi0, fΦ y = 0 → y = 0 := by
    intro y hy h0
    rw [hmemPi] at hy
    rw [hfΦ] at h0
    simp only [epsSum_apply_smul, ← Finset.smul_sum] at h0
    have h0' := (smul_eq_zero.mp h0).resolve_left hHK
    exact inj_phi T s P0 P cB g h hlift ρ hN y (fun i => (Submodule.mem_inf.mp (hy i)).2) h0'
  have hΦ3 : ∀ y ∈ Pi0, ‖ρR (fΦ y)‖ ≤ ((n : ℝ) * Fintype.card P.H) * ‖ρP y‖ := by
    intro y _
    rw [hfΦ, map_sum]
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ i, ‖ρR (ρ.asAlgebraHom (epsSum P * MonoidAlgebra.of K G (g i)) (y i))‖ ≤
        (Fintype.card P.H : ℝ) * ‖ρP y‖ := by
      intro i
      refine (realize_le A.b A.X (fun z => ρ.asAlgebraHom (epsSum P * MonoidAlgebra.of K G (g i)) z)
        (Fintype.card P.H : ℝ) hHpos.le (fun v z => epsSum_norm A ρ hA P (g i) v z) (y i)).trans ?_
      exact mul_le_mul_of_nonneg_left (hcoord y i) hHpos.le
    refine (Finset.sum_le_sum fun i _ => hterm i).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring

  let fΨ : A.V →+ (Fin n → A.V) :=
    { toFun := fun x j => ρ.asAlgebraHom (epsSum P0 * MonoidAlgebra.of K G (h j)) x
      map_zero' := by funext j; simp
      map_add' := by intro x y; funext j; simp }
  have hfΨ : ∀ x j, fΨ x j = ρ.asAlgebraHom (epsSum P0 * MonoidAlgebra.of K G (h j)) x := fun x j => rfl
  have hΨ1 : ∀ x ∈ L1s, fΨ x ∈ Pi0 := by
    intro x hx
    rw [hmemPi]
    intro j
    rw [hfΨ]
    refine Submodule.mem_inf.mpr ⟨epsSum_mem A ρ hA P0 (h j) x (Submodule.mem_inf.mp hx).1, ?_⟩
    show _ ∈ LinearMap.range (ρ.asAlgebraHom (eps P0 * eS T s))
    rw [epsSum_apply_smul]
    exact Submodule.smul_mem _ _ (move_range T s ρ P0 P (h j) x (e_fix T s ρ P x (Submodule.mem_inf.mp hx).2))
  have hΨ2 : ∀ x ∈ L1s, fΨ x = 0 → x = 0 := by
    intro x hx h0
    refine inj_psi T s P0 P cB g h hlift ρ hM hN x (Submodule.mem_inf.mp hx).2 fun j => ?_
    have := congrFun h0 j
    rw [hfΨ, epsSum_apply_smul] at this
    exact (smul_eq_zero.mp this).resolve_left hH0K
  have hΨ3 : ∀ x ∈ L1s, ‖ρP (fΨ x)‖ ≤ ((n : ℝ) * Fintype.card P0.H) * ‖ρR x‖ := by
    intro x _
    have hj : ∀ j, ‖ρR (fΨ x j)‖ ≤ (Fintype.card P0.H : ℝ) * ‖ρR x‖ := fun j =>
      realize_le A.b A.X (fun z => ρ.asAlgebraHom (epsSum P0 * MonoidAlgebra.of K G (h j)) z)
        (Fintype.card P0.H : ℝ) hH0pos.le (fun v z => epsSum_norm A ρ hA P0 (h j) v z) x
    have h3 : ‖ρP (fΨ x)‖ ^ 2 ≤ (((n : ℝ) * Fintype.card P0.H) * ‖ρR x‖) ^ 2 := by
      rw [hnormP]
      calc ∑ j, ‖ρR (fΨ x j)‖ ^ 2 ≤ ∑ j : Fin n, ((Fintype.card P0.H : ℝ) * ‖ρR x‖) ^ 2 :=
            Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hj j) 2
        _ = (n : ℝ) * ((Fintype.card P0.H : ℝ) * ‖ρR x‖) ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ (n : ℝ) ^ 2 * ((Fintype.card P0.H : ℝ) * ‖ρR x‖) ^ 2 := by
            apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
            have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
            nlinarith
        _ = (((n : ℝ) * Fintype.card P0.H) * ‖ρR x‖) ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h3

  have hrkPi : (Formalism.HN.rk ρP Pi0 : ℝ) = dK * ((n * r0 : ℕ) : ℝ) := by
    rw [hρP, hPi0, hPirk]
    push_cast
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hrkZ L0s hL0s, hrk0]
    ring
  have hrkL1 : (Formalism.HN.rk ρR L1s : ℝ) = dK * ((n * r0 : ℕ) : ℝ) := by rw [hrkZ L1s hL1s, hrk1]
  have hdegPi : Formalism.HN.deg ρP Pi0 = (n : ℝ) * Formalism.HN.deg ρR L0s := by
    rw [hρP, hPi0, hPideg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have degΦ := deg_ge_of_inj ρP ρR Pi0 L1s hPiLat (lat L1s hL1s) fΦ hΦ1 hΦ2
    (by exact_mod_cast hrkPi.trans hrkL1.symm) ((n : ℝ) * Fintype.card P.H) (by positivity) hΦ3
  have degΨ := deg_ge_of_inj ρR ρP L1s Pi0 (lat L1s hL1s) hPiLat fΨ hΨ1 hΨ2
    (by exact_mod_cast hrkL1.trans hrkPi.symm) ((n : ℝ) * Fintype.card P0.H) (by positivity) hΨ3
  rw [hrkPi, hdegPi] at degΦ
  rw [hrkL1, hdegPi] at degΨ

  have hG1 : (1 : ℝ) ≤ Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hla : 0 ≤ laG G := Real.log_nonneg hG1
  have hnG : (n : ℝ) ≤ Fintype.card G := by
    have h1 : n ≤ finrank K (T.W s) := Submodule.finrank_le _
    have h2 := dim_sq_le T s
    have h3 : finrank K (T.W s) ≤ finrank K (T.W s) * finrank K (T.W s) := Nat.le_mul_self _
    exact_mod_cast h1.trans (h3.trans h2)
  have hHG : (Fintype.card P.H : ℝ) ≤ Fintype.card G := by exact_mod_cast Fintype.card_subtype_le _
  have hH0G : (Fintype.card P0.H : ℝ) ≤ Fintype.card G := by exact_mod_cast Fintype.card_subtype_le _
  have hlog1 : Real.log ((n : ℝ) * Fintype.card P.H) ≤ 2 * laG G := by
    rw [Real.log_mul hnpos.ne' hHpos.ne']
    have a1 := Real.log_le_log hnpos hnG
    have a2 := Real.log_le_log hHpos hHG
    unfold laG; linarith
  have hlog2 : Real.log ((n : ℝ) * Fintype.card P0.H) ≤ 2 * laG G := by
    rw [Real.log_mul hnpos.ne' hH0pos.ne']
    have a1 := Real.log_le_log hnpos hnG
    have a2 := Real.log_le_log hH0pos hH0G
    unfold laG; linarith

  have hc1 := degL_eq A hA.1 L1s hL1s
  have hc0 := degL_eq A hA.1 L0s hL0s
  rw [hrk1] at hc1
  rw [hrk0] at hc0
  set R0 : ℝ := ((n * r0 : ℕ) : ℝ) with hR0
  have hR0nn : 0 ≤ R0 := Nat.cast_nonneg _
  have hexpr : degL A L1s - (n : ℝ) * degL A L0s =
      (2 / dK) * (Formalism.HN.deg ρR L1s - (n : ℝ) * Formalism.HN.deg ρR L0s) := by
    rw [hc1, hc0, hR0]
    push_cast
    ring
  have hD1 : -(dK * R0 * (2 * laG G)) ≤ Formalism.HN.deg ρR L1s - (n : ℝ) * Formalism.HN.deg ρR L0s := by
    have := mul_le_mul_of_nonneg_left hlog1 (by positivity : (0 : ℝ) ≤ dK * R0)
    linarith
  have hD2 : Formalism.HN.deg ρR L1s - (n : ℝ) * Formalism.HN.deg ρR L0s ≤ dK * R0 * (2 * laG G) := by
    have := mul_le_mul_of_nonneg_left hlog2 (by positivity : (0 : ℝ) ≤ dK * R0)
    linarith
  have hc : 0 < 2 / dK := by positivity
  have e1 : (2 / dK) * (dK * R0 * (2 * laG G)) = 4 * R0 * laG G := by field_simp; ring
  have m1 := mul_le_mul_of_nonneg_left hD1 hc.le
  have m2 := mul_le_mul_of_nonneg_left hD2 hc.le
  rw [mul_neg, e1] at m1
  rw [e1] at m2
  have hRla : 0 ≤ R0 * laG G := mul_nonneg hR0nn hla
  show |degL A L1s - (n : ℝ) * degL A L0s| ≤ 5 * laG G * R0
  rw [hexpr, abs_le]
  constructor <;> linarith

end PI.Dv.Tr
