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
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.TraceFiniteOrder

noncomputable section

namespace PI.Dv.Tr

open PI.Dv Module NumberField

section Alg2

variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]

/- English proof (translation)
Rewrite using `[eG, Finset.mul_sum, Finset.sum_eq_single s]`. Conclude with `eS_idem T s`. Introduce `t _ ht`. Conclude with `eS_orth T s t (Ne.symm ht)`. Simplify using the standard rewrite rules.
-/
lemma eS_mul_eG (T : GoodSet K G) (s : T.S) : eS T s * eG T = eS T s := by
  classical
  rw [eG, Finset.mul_sum, Finset.sum_eq_single s]
  · exact eS_idem T s
  · intro t _ ht; exact eS_orth T s t (Ne.symm ht)
  · simp

/- English proof (translation)
Rewrite using `[← eG_comm, eS_mul_eG]`.
-/
lemma eG_mul_eS (T : GoodSet K G) (s : T.S) : eG T * eS T s = eS T s := by
  rw [← eG_comm, eS_mul_eG]

/- English proof (translation)
Use `set U := Submodule.span K (Set.range (MonoidAlgebra.of K G)) with hU`. Establish `hmem : ∀ s, eS T s ∈ U` using `fun s => U.sum_mem fun y _ => U.smul_mem _ (Submodule.subset_span ⟨y, rfl⟩)`. Set `v : T.S → U` to `fun s => ⟨eS T s, hmem s⟩`. Establish `hli : LinearIndependent K (fun s => eS T s)`. Rewrite using `[Fintype.linearIndependent_iff]`.

Introduce `c hc t`. Establish `h1` using `congrArg (fun x => x * eS T t) hc`. Simplify using `only [Finset.sum_mul, smul_mul_assoc, zero_mul] at h1`. Rewrite `h1` using `[Finset.sum_eq_single t]`. Rewrite `h1` using `[eS_idem]`.

Break down `smul_eq_zero.mp h1 with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd h (eS_ne_zero T t)`. Introduce `s _ hs`. Rewrite using `[eS_orth T s t hs, smul_zero]`.

Simplify using the standard rewrite rules. Establish `hv : LinearIndependent K v` using `LinearIndependent.of_comp U.subtype hli`. Establish `h1` using `hv.fintype_card_le_finrank`. Establish `h2 : finrank K U ≤ Fintype.card G` using `finrank_range_le_card _`. Use linear arithmetic over natural numbers and integers.
-/
lemma card_S_le (T : GoodSet K G) : Fintype.card T.S ≤ Fintype.card G := by
  classical
  set U := Submodule.span K (Set.range (MonoidAlgebra.of K G)) with hU
  have hmem : ∀ s, eS T s ∈ U := fun s =>
    U.sum_mem fun y _ => U.smul_mem _ (Submodule.subset_span ⟨y, rfl⟩)
  let v : T.S → U := fun s => ⟨eS T s, hmem s⟩
  have hli : LinearIndependent K (fun s => eS T s) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc t
    have h1 := congrArg (fun x => x * eS T t) hc
    simp only [Finset.sum_mul, smul_mul_assoc, zero_mul] at h1
    rw [Finset.sum_eq_single t] at h1
    · rw [eS_idem] at h1
      rcases smul_eq_zero.mp h1 with h | h
      · exact h
      · exact absurd h (eS_ne_zero T t)
    · intro s _ hs; rw [eS_orth T s t hs, smul_zero]
    · simp
  have hv : LinearIndependent K v := LinearIndependent.of_comp U.subtype hli
  have h1 := hv.fintype_card_le_finrank
  have h2 : finrank K U ≤ Fintype.card G := finrank_range_le_card _
  omega

/- English proof (translation)
Establish `hall : ∀ a : MonoidAlgebra K G, (T.tau s).asAlgebraHom a ∈ Submodule.span K (Set.range (T.tau s))`. Introduce `a`. Proceed by induction on `a using MonoidAlgebra.induction_on with`. Consider the case `of y => rw [Representation.asAlgebraHom_of]`. Conclude with `Submodule.subset_span ⟨y, rfl⟩`.

Consider the case `add x y hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul r x hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ _ hx`. Establish `htop : Submodule.span K (Set.range (T.tau s)) = ⊤`.

Rewrite using `[eq_top_iff]`. Introduce `X _`. Take `⟨a, rfl⟩` from `T.irr s X`. Conclude with `hall a`. Establish `h1` using `finrank_range_le_card (R := K) (T.tau s : G → Module.End K (T.W s))`.

Rewrite `h1` using `[Set.finrank, htop, finrank_top, Module.finrank_linearMap]`. Conclude with `h1`.
-/
lemma dim_sq_le (T : GoodSet K G) (s : T.S) :
    finrank K (T.W s) * finrank K (T.W s) ≤ Fintype.card G := by
  have hall : ∀ a : MonoidAlgebra K G,
      (T.tau s).asAlgebraHom a ∈ Submodule.span K (Set.range (T.tau s)) := by
    intro a
    induction a using MonoidAlgebra.induction_on with
    | of y => rw [Representation.asAlgebraHom_of]; exact Submodule.subset_span ⟨y, rfl⟩
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul r x hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  have htop : Submodule.span K (Set.range (T.tau s)) = ⊤ := by
    rw [eq_top_iff]
    intro X _
    obtain ⟨a, rfl⟩ := T.irr s X
    exact hall a
  have h1 := finrank_range_le_card (R := K) (T.tau s : G → Module.End K (T.W s))
  rw [Set.finrank, htop, finrank_top, Module.finrank_linearMap] at h1
  exact h1

/- English proof (translation)
Take `⟨c, hc⟩` from `trace_mul_eS T s ρ`. Establish `hn : ∀ (Q : Pair K G), ((nS T Q s : ℕ) : K) = LinearMap.trace K (T.W s) ((T.tau s).asAlgebraHom (eps Q))`. Introduce `Q`. Rewrite using `[nS]`. Conclude with `finrank_range_idem _ (by rw [← map_mul, eps_idem])`.

Establish `hidS : ∀ (Q : Pair K G), (eps Q * eS T s) * (eps Q * eS T s) = eps Q * eS T s` using `fun Q => mul_idem (eps_idem Q) (eS_idem T s) (eS_comm T s (eps Q)).symm`. Apply `Nat.cast_injective (R := K)` to reduce the goal to its premises. Rewrite using `[finrank_range_idem _ (by rw [← map_mul, hidS]), Nat.cast_mul, finrank_range_idem _ (by rw [← map_mul, hidS]), hc, hc, ← hn, ← hn, hM s, Nat.cast_one, mul_one, mul_comm]`.
-/
theorem finrank_range_eps_mul_eS_eq_nS_mul (T : GoodSet K G) (P0 P : Pair K G) (hM : M1 T P0)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] (ρ : Representation K G V) (s : T.S) :
    finrank K (LinearMap.range (ρ.asAlgebraHom (eps P * eS T s))) =
      nS T P s * finrank K (LinearMap.range (ρ.asAlgebraHom (eps P0 * eS T s))) := by
  obtain ⟨c, hc⟩ := trace_mul_eS T s ρ
  have hn : ∀ (Q : Pair K G), ((nS T Q s : ℕ) : K) = LinearMap.trace K (T.W s) ((T.tau s).asAlgebraHom (eps Q)) := by
    intro Q
    rw [nS]
    exact finrank_range_idem _ (by rw [← map_mul, eps_idem])
  have hidS : ∀ (Q : Pair K G), (eps Q * eS T s) * (eps Q * eS T s) = eps Q * eS T s :=
    fun Q => mul_idem (eps_idem Q) (eS_idem T s) (eS_comm T s (eps Q)).symm
  apply Nat.cast_injective (R := K)
  rw [finrank_range_idem _ (by rw [← map_mul, hidS]), Nat.cast_mul,
    finrank_range_idem _ (by rw [← map_mul, hidS]), hc, hc, ← hn, ← hn, hM s, Nat.cast_one, mul_one, mul_comm]

/- English proof (translation)
Establish `hG : ((Fintype.card G : ℕ) : K) ≠ 0` using `by exact_mod_cast Fintype.card_ne_zero`. Rewrite using `[eS, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul]`. Use `congr 1`.

Clear the denominators using the available nonvanishing facts.
-/
lemma card_smul_eS (T : GoodSet K G) (s : T.S) :
    ((Fintype.card G : ℕ) : K) • eS T s =
      ∑ y : G, (((finrank K (T.W s) : ℕ) : K) * LinearMap.trace K (T.W s) (T.tau s y⁻¹)) •
        MonoidAlgebra.of K G y := by
  have hG : ((Fintype.card G : ℕ) : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [eS, Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [smul_smul]
  congr 1
  field_simp

end Alg2

section Lat

variable {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  {G : Type} [Group G] [Fintype G]

/- English proof (translation)
Assemble the required witnesses or components as `⟨(IsAlgClosed.lift (R := ℚ) (S := K) (M := ℂ)).toRingHom⟩`.
-/
lemma sigma0 (K : Type) [Field K] [NumberField K] : Nonempty (K →+* ℂ) :=
  ⟨(IsAlgClosed.lift (R := ℚ) (S := K) (M := ℂ)).toRingHom⟩

/- English proof (translation)
Take `⟨σ⟩` from `sigma0 K`. Establish `h` using `(trace_finite_order (T.tau s y) (Fintype.card G) Fintype.card_pos (by rw [← map_pow, pow_card_eq_one, map_one]) σ).2`. Establish `hd : IsIntegral ℤ (((finrank K (T.W s) : ℕ) : K))`. Use `isIntegral_algebraMap (R := ℤ) (A := K) (x := (finrank K (T.W s) : ℤ))` as an intermediate fact. Simplify using `using this`.

Conclude with `hd.mul h`.
-/
lemma chi_integral (T : GoodSet K G) (s : T.S) (y : G) :
    IsIntegral ℤ (((finrank K (T.W s) : ℕ) : K) * LinearMap.trace K (T.W s) (T.tau s y)) := by
  obtain ⟨σ⟩ := sigma0 K
  have h := (trace_finite_order (T.tau s y) (Fintype.card G) Fintype.card_pos
    (by rw [← map_pow, pow_card_eq_one, map_one]) σ).2
  have hd : IsIntegral ℤ (((finrank K (T.W s) : ℕ) : K)) := by
    have := isIntegral_algebraMap (R := ℤ) (A := K) (x := (finrank K (T.W s) : ℤ))
    simpa using this
  exact hd.mul h

/- English proof (translation)
Establish `h` using `(trace_finite_order (T.tau s y) (Fintype.card G) Fintype.card_pos (by rw [← map_pow, pow_card_eq_one, map_one]) σ).1`. Rewrite using `[map_mul, norm_mul, map_natCast, Complex.norm_natCast]`. Conclude with `mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)`.
-/
lemma chi_norm (T : GoodSet K G) (s : T.S) (y : G) (σ : K →+* ℂ) :
    ‖σ (((finrank K (T.W s) : ℕ) : K) * LinearMap.trace K (T.W s) (T.tau s y))‖ ≤
      (finrank K (T.W s) : ℝ) * (finrank K (T.W s) : ℝ) := by
  have h := (trace_finite_order (T.tau s y) (Fintype.card G) Fintype.card_pos
    (by rw [← map_pow, pow_card_eq_one, map_one]) σ).1
  rw [map_mul, norm_mul, map_natCast, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)

/- English proof (translation)
Rewrite using `[card_smul_eS, map_sum, LinearMap.sum_apply]`. Simplify using `only [map_smul, Representation.asAlgebraHom_of, LinearMap.smul_apply]`.
-/
lemma ge_apply {V : Type} [AddCommGroup V] [Module K V] (T : GoodSet K G) (ρ : Representation K G V)
    (s : T.S) (x : V) :
    ρ.asAlgebraHom (((Fintype.card G : ℕ) : K) • eS T s) x =
      ∑ y : G, (((finrank K (T.W s) : ℕ) : K) * LinearMap.trace K (T.W s) (T.tau s y⁻¹)) • ρ y x := by
  rw [card_smul_eS, map_sum, LinearMap.sum_apply]
  simp only [map_smul, Representation.asAlgebraHom_of, LinearMap.smul_apply]

/- English proof (translation)
Rewrite using `[ge_apply]`. Use `A.L.sum_mem fun y _ => ?_` and prove the remaining obligations. Take `⟨r, hr⟩ : ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = ((finrank K (T.W s) : ℕ) : K) * LinearMap.trace K (T.W s) (T.tau s y⁻¹)` from `⟨⟨_, chi_integral T s y⁻¹⟩, rfl⟩`. Rewrite using `[← hr, algebraMap_smul]`. Conclude with `A.L.smul_mem r (hA.2.1 y x hx)`.
-/
lemma ge_mem (T : GoodSet K G) (A : Formalism.BasicNotions.HLat K) (ρ : Representation K G A.V) (hA : IsGLat A ρ)
    (s : T.S) (x : A.V) (hx : x ∈ A.L) :
    ρ.asAlgebraHom (((Fintype.card G : ℕ) : K) • eS T s) x ∈ A.L := by
  rw [ge_apply]
  refine A.L.sum_mem fun y _ => ?_
  obtain ⟨r, hr⟩ : ∃ r : 𝓞 K, algebraMap (𝓞 K) K r =
      ((finrank K (T.W s) : ℕ) : K) * LinearMap.trace K (T.W s) (T.tau s y⁻¹) :=
    ⟨⟨_, chi_integral T s y⁻¹⟩, rfl⟩
  rw [← hr, algebraMap_smul]
  exact A.L.smul_mem r (hA.2.1 y x hx)

/- English proof (translation)
Rewrite using `[ge_apply]`. Use `(normAt_sum_le' A.b A.X v _ _).trans ?_` and prove the remaining obligations. Establish `hterm : ∀ y : G, Formalism.HermitianLatticesTheory.normAt A.b A.X v ((((finrank K (T.W s) : ℕ) : K) * LinearMap.trace K (T.W s) (T.tau s y⁻¹)) • ρ y x) ≤ ((finrank K (T.W s) : ℝ) * (finrank K (T.W s) : ℝ)) * Formalism.HermitianLatticesTheory.normAt A.b A.X v x`. Introduce `y`. Rewrite using `[normAt_smul', hA.2.2]`.

Conclude with `mul_le_mul_of_nonneg_right (chi_norm T s y⁻¹ v.embedding) (Real.sqrt_nonneg _)`. Use `(Finset.sum_le_sum fun y _ => hterm y).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma ge_norm (T : GoodSet K G) (A : Formalism.BasicNotions.HLat K) (ρ : Representation K G A.V) (hA : IsGLat A ρ)
    (s : T.S) (v : InfinitePlace K) (x : A.V) :
    Formalism.HermitianLatticesTheory.normAt A.b A.X v (ρ.asAlgebraHom (((Fintype.card G : ℕ) : K) • eS T s) x) ≤
      ((Fintype.card G : ℝ) * ((finrank K (T.W s) : ℝ) * (finrank K (T.W s) : ℝ))) *
        Formalism.HermitianLatticesTheory.normAt A.b A.X v x := by
  rw [ge_apply]
  refine (normAt_sum_le' A.b A.X v _ _).trans ?_
  have hterm : ∀ y : G, Formalism.HermitianLatticesTheory.normAt A.b A.X v
      ((((finrank K (T.W s) : ℕ) : K) * LinearMap.trace K (T.W s) (T.tau s y⁻¹)) • ρ y x) ≤
      ((finrank K (T.W s) : ℝ) * (finrank K (T.W s) : ℝ)) * Formalism.HermitianLatticesTheory.normAt A.b A.X v x := by
    intro y
    rw [normAt_smul', hA.2.2]
    exact mul_le_mul_of_nonneg_right (chi_norm T s y⁻¹ v.embedding) (Real.sqrt_nonneg _)
  refine (Finset.sum_le_sum fun y _ => hterm y).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

end Lat

section AlgEps

variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
lemma eG_eps_eS (T : GoodSet K G) (P : Pair K G) (s : T.S) :
    eps P * eG T * (eps P * eS T s) = eps P * eS T s := by
  calc eps P * eG T * (eps P * eS T s) = eps P * (eG T * eps P) * eS T s := by simp only [mul_assoc]
    _ = eps P * (eps P * eG T) * eS T s := by rw [eG_comm]
    _ = (eps P * eps P) * (eG T * eS T s) := by simp only [mul_assoc]
    _ = eps P * eS T s := by rw [eps_idem, eG_mul_eS]

/- English proof (translation)
Rewrite using `[← mul_assoc, ← eS_comm, mul_assoc]`. Use `split_ifs with h`. Substitute `h` using the available equality. Rewrite using `[eS_idem]`. Rewrite using `[eS_orth T t s (Ne.symm h), mul_zero]`.
-/
lemma eS_eps_eS (T : GoodSet K G) (P : Pair K G) (s t : T.S) :
    eS T t * (eps P * eS T s) = if s = t then eps P * eS T s else 0 := by
  rw [← mul_assoc, ← eS_comm, mul_assoc]
  split_ifs with h
  · subst h; rw [eS_idem]
  · rw [eS_orth T t s (Ne.symm h), mul_zero]

/- English proof (translation)
Rewrite using `[smul_mul_assoc, mul_smul_comm, ← mul_assoc, ← eS_comm, mul_assoc, eS_mul_eG]`.
-/
lemma eS_eps_eG (T : GoodSet K G) (P : Pair K G) (s : T.S) :
    ((Fintype.card G : ℕ) : K) • eS T s * (eps P * eG T) = eps P * eS T s * (((Fintype.card G : ℕ) : K) • eG T) := by
  rw [smul_mul_assoc, mul_smul_comm, ← mul_assoc, ← eS_comm, mul_assoc, eS_mul_eG]

/- English proof (translation)
Rewrite using `[← mul_assoc, ← eG_comm, mul_assoc, eG_idem]`.
-/
lemma eG_eps_eG (T : GoodSet K G) (P : Pair K G) : eG T * (eps P * eG T) = eps P * eG T := by
  rw [← mul_assoc, ← eG_comm, mul_assoc, eG_idem]

end AlgEps

/- English proof (translation)
Introduce `K _ _ _ _ G _ _ T P0 P hM A ρ hA`. Establish `hfd : FiniteDimensional K A.V` using `Module.Finite.of_basis A.b`. Use `set ρR := Formalism.HermitianLatticesTheory.realize A.b A.X with hρR`. Use `set L1 := cut A ρ (eps P * eG T) A.L with hL1def`. Use `set L1s : T.S → Submodule (𝓞 K) A.V := fun s => cut A ρ (eps P * eS T s) A.L with hL1sdef`.

Use `set Pi : Submodule (𝓞 K) (T.S → A.V) := Submodule.pi Set.univ L1s with hPidef`. Use `set ρP := Formalism.HN.piReal (fun _ : T.S => ρR) with hρP`. Use `set dK : ℝ := (finrank ℚ K : ℝ) with hdK`. Use `set R : ℕ := rkT T P0 P A ρ with hRdef`. Establish `hdK0 : 0 < dK` using `by rw [hdK]; exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)`.

Establish `hL1 : L1 ≤ A.L` using `inf_le_left`. Establish `hL1s : ∀ s, L1s s ≤ A.L` using `fun s => inf_le_left`. Establish `lat : ∀ N : Submodule (𝓞 K) A.V, N ≤ A.L → Formalism.HN.IsLat ρR N` using `fun N hN => (Formalism.HN.plLat K A.V A.ι A.b A.X hA.1.1 N (fg_of_le_L A hA.1 N hN)).1`. Establish `hrkZ : ∀ N : Submodule (𝓞 K) A.V, N ≤ A.L → (Formalism.HN.rk ρR N : ℝ) = dK * (Formalism.HN.rkK N : ℝ)`. Introduce `N hN`.

Rewrite using `[(Formalism.HN.plLat K A.V A.ι A.b A.X hA.1.1 N (fg_of_le_L A hA.1 N hN)).2.1]`. Use `push_cast`. Both sides reduce to the same expression. Take `⟨hPiLat, hPirk, hPideg, -⟩` from `Formalism.HN.piSum (𝓞 K) T.S (fun _ => A.V) (fun _ => _) (fun _ => ρR) L1s (fun s => lat _ (hL1s s))`. Establish `hrkK1 : Formalism.HN.rkK L1 = R` using `rankPart K G T P0 P hM A ρ hA`.

Establish `hrkKs : ∀ s, Formalism.HN.rkK (L1s s) = nS T P s * rS T P0 A ρ s`. Introduce `s`. Use `show rkL A (cut A ρ (eps P * eS T s) A.L) = _`. Rewrite using `[rkL_cut A hA.1, finrank_range_eps_mul_eS_eq_nS_mul T P0 P hM ρ s, rS, rkL_cut A hA.1]`. Establish `hRsum : ((R : ℕ) : ℝ) = ∑ s, ((Formalism.HN.rkK (L1s s) : ℕ) : ℝ)`.

Rewrite using `[hRdef, rkT]`. Use `push_cast`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[hrkKs s]`. Use `push_cast`.

Both sides reduce to the same expression. Establish `hrkPi : (Formalism.HN.rk ρP Pi : ℝ) = dK * R`. Rewrite using `[hρP, hPidef, hPirk]`. Use `push_cast`. Rewrite using `[hRsum, Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun s _ => hrkZ _ (hL1s s)`. Establish `hrk1 : (Formalism.HN.rk ρR L1 : ℝ) = dK * R` using `by rw [hrkZ L1 hL1, hrkK1]`. Establish `hnormP : ∀ x : T.S → A.V, ‖ρP x‖ ^ 2 = ∑ s, ‖ρR (x s)‖ ^ 2`. Introduce `x`. Rewrite using `[hρP, PiLp.norm_sq_eq_of_L2]`.

Both sides reduce to the same expression. Establish `hcardS : (Fintype.card T.S : ℝ) ≤ Fintype.card G` using `by exact_mod_cast card_S_le T`. Establish `hG1 : (1 : ℝ) ≤ Fintype.card G` using `by exact_mod_cast Fintype.card_pos`. Establish `hGpos : (0 : ℝ) < Fintype.card G` using `by linarith`. Establish `hmemPi : ∀ x : T.S → A.V, x ∈ Pi ↔ ∀ s, x s ∈ L1s s`.

Introduce `x`. Simplify using `[hPidef, Submodule.mem_pi]`. Set `fA : (T.S → A.V) →+ A.V` to `{ toFun := fun x => ∑ s, x s map_zero' := by simp map_add' := by intro x y; simp [Finset.sum_add_distrib] }`. Establish `hfA : ∀ x, fA x = ∑ s, x s` using `fun x => rfl`. Establish `hA1 : ∀ x ∈ Pi, fA x ∈ L1`.

Introduce `x hx`. Rewrite `hx` using `[hmemPi]`. Rewrite using `[hfA]`. Use `Submodule.mem_inf.mpr ⟨A.L.sum_mem fun s _ => (Submodule.mem_inf.mp (hx s)).1, ?_⟩` and prove the remaining obligations. Use `show ∑ s, x s ∈ LinearMap.range (ρ.asAlgebraHom (eps P * eG T))`.

Use `Submodule.sum_mem _ fun s _ => ?_` and prove the remaining obligations. Take `⟨z, hz⟩` from `(Submodule.mem_inf.mp (hx s)).2`. Use `⟨ρ.asAlgebraHom (eps P * eS T s) z, ?_⟩` and prove the remaining obligations. Rewrite using `[← Module.End.mul_apply, ← map_mul, eG_eps_eS, hz]`. Establish `hA2 : ∀ x ∈ Pi, fA x = 0 → x = 0`.

Introduce `x hx h0`. Rewrite `hx` using `[hmemPi]`. Use function extensionality and compare the values at `t`. Establish `hproj : ∀ s, ρ.asAlgebraHom (eS T t) (x s) = if s = t then x s else 0`. Introduce `s`.

Take `⟨z, hz⟩` from `(Submodule.mem_inf.mp (hx s)).2`. Rewrite using `[← hz, ← Module.End.mul_apply, ← map_mul, eS_eps_eS]`. Apply the tactic sequence `split_ifs <;> simp`. Use `congrArg (ρ.asAlgebraHom (eS T t)) h0` as an intermediate fact. Rewrite `this` using `[hfA, map_sum, map_zero]`.

Simplify using `only [hproj, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this`. Conclude with `this`. Establish `hA3 : ∀ x ∈ Pi, ‖ρR (fA x)‖ ≤ Real.sqrt (Fintype.card G) * ‖ρP x‖`. Introduce `x _`. Rewrite using `[hfA, map_sum]`.

Establish `h1 : ‖∑ s, ρR (x s)‖ ≤ ∑ s, ‖ρR (x s)‖` using `norm_sum_le _ _`. Establish `h2 : (∑ s, ‖ρR (x s)‖) ^ 2 ≤ (Fintype.card T.S : ℝ) * ∑ s, ‖ρR (x s)‖ ^ 2` using `sq_sum_le_card_mul_sum_sq`. Establish `h3 : ‖∑ s, ρR (x s)‖ ^ 2 ≤ (Real.sqrt (Fintype.card G) * ‖ρP x‖) ^ 2`. Rewrite using `[mul_pow, Real.sq_sqrt hGpos.le, hnormP]`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `(pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h3`. Establish `degA` using `deg_ge_of_inj ρP ρR Pi L1 hPiLat (lat L1 hL1) fA hA1 hA2 (by exact_mod_cast hrkPi.trans hrk1.symm) (Real.sqrt (Fintype.card G)) (Real.sqrt_pos.mpr hGpos) hA3`. Set `fB : A.V →+ (T.S → A.V)` to `{ toFun := fun x s => ρ.asAlgebraHom (((Fintype.card G : ℕ) : K) • eS T s) x map_zero' := by funext s; simp map_add' := by intro x y; funext s; simp }`. Establish `hfB : ∀ x s, fB x s = ρ.asAlgebraHom (((Fintype.card G : ℕ) : K) • eS T s) x` using `fun x s => rfl`. Establish `hB1 : ∀ x ∈ L1, fB x ∈ Pi`.

Introduce `x hx`. Rewrite using `[hmemPi]`. Introduce `s`. Rewrite using `[hfB]`. Use `Submodule.mem_inf.mpr ⟨ge_mem T A ρ hA s x (Submodule.mem_inf.mp hx).1, ?_⟩` and prove the remaining obligations.

Take `⟨z, hz⟩` from `(Submodule.mem_inf.mp hx).2`. Use `show _ ∈ LinearMap.range (ρ.asAlgebraHom (eps P * eS T s))`. Use `⟨ρ.asAlgebraHom (((Fintype.card G : ℕ) : K) • eG T) z, ?_⟩` and prove the remaining obligations. Rewrite using `[← hz, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, eS_eps_eG]`. Establish `hB2 : ∀ x ∈ L1, fB x = 0 → x = 0`.

Introduce `x hx h0`. Take `⟨z, hz⟩` from `(Submodule.mem_inf.mp hx).2`. Establish `hG0 : ((Fintype.card G : ℕ) : K) ≠ 0` using `by exact_mod_cast Fintype.card_ne_zero`. Establish `hes : ∀ s, ρ.asAlgebraHom (eS T s) x = 0`. Introduce `s`.

Use `congrFun h0 s` as an intermediate fact. Rewrite `this` using `[hfB, map_smul, LinearMap.smul_apply]`. Conclude with `(smul_eq_zero.mp this).resolve_left hG0`. Establish `hx' : ρ.asAlgebraHom (eG T) x = x`. Rewrite using `[← hz, ← Module.End.mul_apply, ← map_mul, eG_eps_eG]`.

Rewrite using `[← hx', eG, map_sum, LinearMap.sum_apply]`. Conclude with `Finset.sum_eq_zero fun s _ => hes s`. Establish `hB3 : ∀ x ∈ L1, ‖ρP (fB x)‖ ≤ Real.sqrt ((Fintype.card G : ℝ) ^ 5) * ‖ρR x‖`. Introduce `x _`. Establish `hs : ∀ s, ‖ρR (fB x s)‖ ≤ (Fintype.card G : ℝ) * (Fintype.card G : ℝ) * ‖ρR x‖`.

Introduce `s`. Establish `hds : ((finrank K (T.W s) : ℝ) * (finrank K (T.W s) : ℝ)) ≤ Fintype.card G`. Conclude with `dim_sq_le T s` after adjusting the coercions. Establish `h1` using `realize_le A.b A.X (fun y => fB y s) ((Fintype.card G : ℝ) * ((finrank K (T.W s) : ℝ) * (finrank K (T.W s) : ℝ))) (by positivity) (fun v y => ge_norm T A ρ hA s v y) x`. Use `h1.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))` and prove the remaining obligations.

Conclude with `mul_le_mul_of_nonneg_left hds hGpos.le`. Establish `h3 : ‖ρP (fB x)‖ ^ 2 ≤ (Real.sqrt ((Fintype.card G : ℝ) ^ 5) * ‖ρR x‖) ^ 2`. Rewrite using `[mul_pow, Real.sq_sqrt (by positivity), hnormP]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ (Fintype.card G : ℝ) * ((Fintype.card G : ℝ) ^ 4 * ‖ρR x‖ ^ 2) := mul_le_mul_of_nonneg_right hcardS (by positivity)`. Use `_ = (Fintype.card G : ℝ) ^ 5 * ‖ρR x‖ ^ 2 := by ring`. Conclude with `(pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h3`. Establish `degB` using `deg_ge_of_inj ρR ρP L1 Pi (lat L1 hL1) hPiLat fB hB1 hB2 (by exact_mod_cast hrk1.trans hrkPi.symm) (Real.sqrt ((Fintype.card G : ℝ) ^ 5)) (by positivity) hB3`.

Establish `hconv1` using `degL_eq A hA.1 L1 hL1`. Establish `hconvs : ∑ s, degL A (L1s s) = (2 / dK) * Formalism.HN.deg ρP Pi + (R : ℝ) * kap K`. Rewrite using `[hρP, hPidef, hPideg, hRsum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun s _ => degL_eq A hA.1 (L1s s) (hL1s s)`. Establish `hlogA : Real.log (Real.sqrt (Fintype.card G)) = laG G / 2`.

Rewrite using `[Real.log_sqrt hGpos.le]`. Both sides reduce to the same expression. Establish `hlogB : Real.log (Real.sqrt ((Fintype.card G : ℝ) ^ 5)) = 5 * laG G / 2`. Rewrite using `[Real.log_sqrt (by positivity), Real.log_pow]; unfold laG; push_cast; ring`. Establish `hla : 0 ≤ laG G` using `Real.log_nonneg hG1`.

Rewrite `degA` using `[hlogA, hrkPi]`. Rewrite `degB` using `[hlogB, hrk1]`. Use `show |degL A L1 - ∑ s, degL A (L1s s)| ≤ 5 * laG G * (R : ℝ)`. Rewrite using `[hconvs, hconv1, hrkK1]`. Establish `hR0 : (0 : ℝ) ≤ R` using `Nat.cast_nonneg _`.

Establish `hexpr : (2 / dK * Formalism.HN.deg ρR L1 + (R : ℝ) * kap K) - (2 / dK * Formalism.HN.deg ρP Pi + (R : ℝ) * kap K) = (2 / dK) * (Formalism.HN.deg ρR L1 - Formalism.HN.deg ρP Pi)` using `by ring`. Establish `hD1 : -(dK * R * (laG G / 2)) ≤ Formalism.HN.deg ρR L1 - Formalism.HN.deg ρP Pi` using `by linarith`. Establish `hD2 : Formalism.HN.deg ρR L1 - Formalism.HN.deg ρP Pi ≤ dK * R * (5 * laG G / 2)` using `by linarith`. Establish `hc : 0 < 2 / dK` using `by positivity`. Establish `e1 : (2 / dK) * (dK * R * (laG G / 2)) = R * laG G` using `by field_simp`.

Establish `e2 : (2 / dK) * (dK * R * (5 * laG G / 2)) = 5 * R * laG G` using `by field_simp`. Establish `m1` using `mul_le_mul_of_nonneg_left hD1 hc.le`. Establish `m2` using `mul_le_mul_of_nonneg_left hD2 hc.le`. Rewrite `m1` using `[mul_neg, e1]`. Rewrite `m2` using `[e2]`.

Establish `hRla : 0 ≤ R * laG G` using `mul_nonneg hR0 hla`. Rewrite using `[hexpr, abs_le]`. Apply the tactic sequence `constructor <;> linarith`.
-/
theorem splitBound : SplitBound := by
  intro K _ _ _ _ G _ _ T P0 P hM A ρ hA
  classical
  have hfd : FiniteDimensional K A.V := Module.Finite.of_basis A.b
  set ρR := Formalism.HermitianLatticesTheory.realize A.b A.X with hρR
  set L1 := cut A ρ (eps P * eG T) A.L with hL1def
  set L1s : T.S → Submodule (𝓞 K) A.V := fun s => cut A ρ (eps P * eS T s) A.L with hL1sdef
  set Pi : Submodule (𝓞 K) (T.S → A.V) := Submodule.pi Set.univ L1s with hPidef
  set ρP := Formalism.HN.piReal (fun _ : T.S => ρR) with hρP
  set dK : ℝ := (finrank ℚ K : ℝ) with hdK
  set R : ℕ := rkT T P0 P A ρ with hRdef
  have hdK0 : 0 < dK := by rw [hdK]; exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have hL1 : L1 ≤ A.L := inf_le_left
  have hL1s : ∀ s, L1s s ≤ A.L := fun s => inf_le_left
  have lat : ∀ N : Submodule (𝓞 K) A.V, N ≤ A.L → Formalism.HN.IsLat ρR N :=
    fun N hN => (Formalism.HN.plLat K A.V A.ι A.b A.X hA.1.1 N (fg_of_le_L A hA.1 N hN)).1
  have hrkZ : ∀ N : Submodule (𝓞 K) A.V, N ≤ A.L → (Formalism.HN.rk ρR N : ℝ) = dK * (Formalism.HN.rkK N : ℝ) := by
    intro N hN
    rw [(Formalism.HN.plLat K A.V A.ι A.b A.X hA.1.1 N (fg_of_le_L A hA.1 N hN)).2.1]
    push_cast
    rfl
  obtain ⟨hPiLat, hPirk, hPideg, -⟩ := Formalism.HN.piSum (𝓞 K) T.S (fun _ => A.V) (fun _ => _)
    (fun _ => ρR) L1s (fun s => lat _ (hL1s s))
  have hrkK1 : Formalism.HN.rkK L1 = R := rankPart K G T P0 P hM A ρ hA
  have hrkKs : ∀ s, Formalism.HN.rkK (L1s s) = nS T P s * rS T P0 A ρ s := by
    intro s
    show rkL A (cut A ρ (eps P * eS T s) A.L) = _
    rw [rkL_cut A hA.1, finrank_range_eps_mul_eS_eq_nS_mul T P0 P hM ρ s, rS, rkL_cut A hA.1]
  have hRsum : ((R : ℕ) : ℝ) = ∑ s, ((Formalism.HN.rkK (L1s s) : ℕ) : ℝ) := by
    rw [hRdef, rkT]
    push_cast
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hrkKs s]
    push_cast
    rfl
  have hrkPi : (Formalism.HN.rk ρP Pi : ℝ) = dK * R := by
    rw [hρP, hPidef, hPirk]
    push_cast
    rw [hRsum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => hrkZ _ (hL1s s)
  have hrk1 : (Formalism.HN.rk ρR L1 : ℝ) = dK * R := by rw [hrkZ L1 hL1, hrkK1]

  have hnormP : ∀ x : T.S → A.V, ‖ρP x‖ ^ 2 = ∑ s, ‖ρR (x s)‖ ^ 2 := by
    intro x
    rw [hρP, PiLp.norm_sq_eq_of_L2]
    rfl
  have hcardS : (Fintype.card T.S : ℝ) ≤ Fintype.card G := by exact_mod_cast card_S_le T
  have hG1 : (1 : ℝ) ≤ Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hGpos : (0 : ℝ) < Fintype.card G := by linarith
  have hmemPi : ∀ x : T.S → A.V, x ∈ Pi ↔ ∀ s, x s ∈ L1s s := by
    intro x
    simp [hPidef, Submodule.mem_pi]

  let fA : (T.S → A.V) →+ A.V :=
    { toFun := fun x => ∑ s, x s
      map_zero' := by simp
      map_add' := by intro x y; simp [Finset.sum_add_distrib] }
  have hfA : ∀ x, fA x = ∑ s, x s := fun x => rfl
  have hA1 : ∀ x ∈ Pi, fA x ∈ L1 := by
    intro x hx
    rw [hmemPi] at hx
    rw [hfA]
    refine Submodule.mem_inf.mpr ⟨A.L.sum_mem fun s _ => (Submodule.mem_inf.mp (hx s)).1, ?_⟩
    show ∑ s, x s ∈ LinearMap.range (ρ.asAlgebraHom (eps P * eG T))
    refine Submodule.sum_mem _ fun s _ => ?_
    obtain ⟨z, hz⟩ := (Submodule.mem_inf.mp (hx s)).2
    refine ⟨ρ.asAlgebraHom (eps P * eS T s) z, ?_⟩
    rw [← Module.End.mul_apply, ← map_mul, eG_eps_eS, hz]
  have hA2 : ∀ x ∈ Pi, fA x = 0 → x = 0 := by
    intro x hx h0
    rw [hmemPi] at hx
    funext t
    have hproj : ∀ s, ρ.asAlgebraHom (eS T t) (x s) = if s = t then x s else 0 := by
      intro s
      obtain ⟨z, hz⟩ := (Submodule.mem_inf.mp (hx s)).2
      rw [← hz, ← Module.End.mul_apply, ← map_mul, eS_eps_eS]
      split_ifs <;> simp
    have := congrArg (ρ.asAlgebraHom (eS T t)) h0
    rw [hfA, map_sum, map_zero] at this
    simp only [hproj, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    exact this
  have hA3 : ∀ x ∈ Pi, ‖ρR (fA x)‖ ≤ Real.sqrt (Fintype.card G) * ‖ρP x‖ := by
    intro x _
    rw [hfA, map_sum]
    have h1 : ‖∑ s, ρR (x s)‖ ≤ ∑ s, ‖ρR (x s)‖ := norm_sum_le _ _
    have h2 : (∑ s, ‖ρR (x s)‖) ^ 2 ≤ (Fintype.card T.S : ℝ) * ∑ s, ‖ρR (x s)‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have h3 : ‖∑ s, ρR (x s)‖ ^ 2 ≤ (Real.sqrt (Fintype.card G) * ‖ρP x‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hGpos.le, hnormP]
      calc ‖∑ s, ρR (x s)‖ ^ 2 ≤ (∑ s, ‖ρR (x s)‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ ≤ (Fintype.card T.S : ℝ) * ∑ s, ‖ρR (x s)‖ ^ 2 := h2
        _ ≤ (Fintype.card G : ℝ) * ∑ s, ‖ρR (x s)‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hcardS (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h3
  have degA := deg_ge_of_inj ρP ρR Pi L1 hPiLat (lat L1 hL1) fA hA1 hA2
    (by exact_mod_cast hrkPi.trans hrk1.symm) (Real.sqrt (Fintype.card G)) (Real.sqrt_pos.mpr hGpos) hA3

  let fB : A.V →+ (T.S → A.V) :=
    { toFun := fun x s => ρ.asAlgebraHom (((Fintype.card G : ℕ) : K) • eS T s) x
      map_zero' := by funext s; simp
      map_add' := by intro x y; funext s; simp }
  have hfB : ∀ x s, fB x s = ρ.asAlgebraHom (((Fintype.card G : ℕ) : K) • eS T s) x := fun x s => rfl
  have hB1 : ∀ x ∈ L1, fB x ∈ Pi := by
    intro x hx
    rw [hmemPi]
    intro s
    rw [hfB]
    refine Submodule.mem_inf.mpr ⟨ge_mem T A ρ hA s x (Submodule.mem_inf.mp hx).1, ?_⟩
    obtain ⟨z, hz⟩ := (Submodule.mem_inf.mp hx).2
    show _ ∈ LinearMap.range (ρ.asAlgebraHom (eps P * eS T s))
    refine ⟨ρ.asAlgebraHom (((Fintype.card G : ℕ) : K) • eG T) z, ?_⟩
    rw [← hz, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, eS_eps_eG]
  have hB2 : ∀ x ∈ L1, fB x = 0 → x = 0 := by
    intro x hx h0
    obtain ⟨z, hz⟩ := (Submodule.mem_inf.mp hx).2
    have hG0 : ((Fintype.card G : ℕ) : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have hes : ∀ s, ρ.asAlgebraHom (eS T s) x = 0 := by
      intro s
      have := congrFun h0 s
      rw [hfB, map_smul, LinearMap.smul_apply] at this
      exact (smul_eq_zero.mp this).resolve_left hG0
    have hx' : ρ.asAlgebraHom (eG T) x = x := by
      rw [← hz, ← Module.End.mul_apply, ← map_mul, eG_eps_eG]
    rw [← hx', eG, map_sum, LinearMap.sum_apply]
    exact Finset.sum_eq_zero fun s _ => hes s
  have hB3 : ∀ x ∈ L1, ‖ρP (fB x)‖ ≤ Real.sqrt ((Fintype.card G : ℝ) ^ 5) * ‖ρR x‖ := by
    intro x _
    have hs : ∀ s, ‖ρR (fB x s)‖ ≤ (Fintype.card G : ℝ) * (Fintype.card G : ℝ) * ‖ρR x‖ := by
      intro s
      have hds : ((finrank K (T.W s) : ℝ) * (finrank K (T.W s) : ℝ)) ≤ Fintype.card G := by
        exact_mod_cast dim_sq_le T s
      have h1 := realize_le A.b A.X (fun y => fB y s) ((Fintype.card G : ℝ) *
        ((finrank K (T.W s) : ℝ) * (finrank K (T.W s) : ℝ))) (by positivity)
        (fun v y => ge_norm T A ρ hA s v y) x
      refine h1.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      exact mul_le_mul_of_nonneg_left hds hGpos.le
    have h3 : ‖ρP (fB x)‖ ^ 2 ≤ (Real.sqrt ((Fintype.card G : ℝ) ^ 5) * ‖ρR x‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), hnormP]
      calc ∑ s, ‖ρR (fB x s)‖ ^ 2 ≤ ∑ s : T.S, ((Fintype.card G : ℝ) * (Fintype.card G : ℝ) * ‖ρR x‖) ^ 2 :=
            Finset.sum_le_sum fun s _ => pow_le_pow_left₀ (norm_nonneg _) (hs s) 2
        _ = (Fintype.card T.S : ℝ) * ((Fintype.card G : ℝ) ^ 4 * ‖ρR x‖ ^ 2) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
        _ ≤ (Fintype.card G : ℝ) * ((Fintype.card G : ℝ) ^ 4 * ‖ρR x‖ ^ 2) :=
            mul_le_mul_of_nonneg_right hcardS (by positivity)
        _ = (Fintype.card G : ℝ) ^ 5 * ‖ρR x‖ ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h3
  have degB := deg_ge_of_inj ρR ρP L1 Pi (lat L1 hL1) hPiLat fB hB1 hB2
    (by exact_mod_cast hrk1.trans hrkPi.symm) (Real.sqrt ((Fintype.card G : ℝ) ^ 5)) (by positivity) hB3

  have hconv1 := degL_eq A hA.1 L1 hL1
  have hconvs : ∑ s, degL A (L1s s) = (2 / dK) * Formalism.HN.deg ρP Pi + (R : ℝ) * kap K := by
    rw [hρP, hPidef, hPideg, hRsum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => degL_eq A hA.1 (L1s s) (hL1s s)
  have hlogA : Real.log (Real.sqrt (Fintype.card G)) = laG G / 2 := by
    rw [Real.log_sqrt hGpos.le]; rfl
  have hlogB : Real.log (Real.sqrt ((Fintype.card G : ℝ) ^ 5)) = 5 * laG G / 2 := by
    rw [Real.log_sqrt (by positivity), Real.log_pow]; unfold laG; push_cast; ring
  have hla : 0 ≤ laG G := Real.log_nonneg hG1
  rw [hlogA, hrkPi] at degA
  rw [hlogB, hrk1] at degB
  show |degL A L1 - ∑ s, degL A (L1s s)| ≤ 5 * laG G * (R : ℝ)
  rw [hconvs, hconv1, hrkK1]
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  have hexpr : (2 / dK * Formalism.HN.deg ρR L1 + (R : ℝ) * kap K) - (2 / dK * Formalism.HN.deg ρP Pi + (R : ℝ) * kap K) =
      (2 / dK) * (Formalism.HN.deg ρR L1 - Formalism.HN.deg ρP Pi) := by ring
  have hD1 : -(dK * R * (laG G / 2)) ≤ Formalism.HN.deg ρR L1 - Formalism.HN.deg ρP Pi := by linarith
  have hD2 : Formalism.HN.deg ρR L1 - Formalism.HN.deg ρP Pi ≤ dK * R * (5 * laG G / 2) := by linarith
  have hc : 0 < 2 / dK := by positivity
  have e1 : (2 / dK) * (dK * R * (laG G / 2)) = R * laG G := by field_simp
  have e2 : (2 / dK) * (dK * R * (5 * laG G / 2)) = 5 * R * laG G := by field_simp
  have m1 := mul_le_mul_of_nonneg_left hD1 hc.le
  have m2 := mul_le_mul_of_nonneg_left hD2 hc.le
  rw [mul_neg, e1] at m1
  rw [e2] at m2
  have hRla : 0 ≤ R * laG G := mul_nonneg hR0 hla
  rw [hexpr, abs_le]
  constructor <;> linarith

end PI.Dv.Tr
