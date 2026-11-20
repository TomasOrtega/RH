import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.AllPartsTransfer

open Module NumberField

noncomputable section

namespace Formalism.IndefR.LatticeTransfer

open Formalism.IndefR.TransferLatticeStatement

namespace CharacterLemmas

/- English proof (translation)
Rewrite using `[LinearMap.trace_eq_matrix_trace ℂ v h, Matrix.trace]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.diag_apply, LinearMap.toMatrix_apply, hv i, map_smul, Basis.repr_self]`. Simplify using the standard rewrite rules.
-/
theorem trace_of_diag {V I : Type*} [AddCommGroup V] [Module ℂ V] [Fintype I] [DecidableEq I]
    (v : Basis I ℂ V) (h : V →ₗ[ℂ] V) (c : I → ℂ) (hv : ∀ i, h (v i) = c i • v i) :
    LinearMap.trace ℂ V h = ∑ i, c i := by
  rw [LinearMap.trace_eq_matrix_trace ℂ v h, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, hv i, map_smul, Basis.repr_self]
  simp

/- English proof (translation)
Use `set s : Module.End ℂ V := ρ g with hs`. Use `set n := orderOf g with hn`. Establish `hn0 : 0 < n` using `orderOf_pos g`. Establish `hsn : s ^ n = 1` using `by rw [hs, ← map_pow, hn, pow_orderOf_eq_one, map_one]`. Establish `hsq : Squarefree (Polynomial.X ^ n - 1 : Polynomial ℂ)` using `(Polynomial.X_pow_sub_one_separable_iff.mpr (by exact_mod_cast hn0.ne')).squarefree`.

Establish `hss : s.IsSemisimple` using `Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq (by simp [hsn])`. Set `eigenDecomp` to `DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top s.eigenspaces_iSupIndep hss.iSup_eigenspace_eq_top`. Set `I` to `(ν : ℂ) × Fin (finrank ℂ (s.eigenspace ν))`. Set `v : Basis I ℂ V` to `eigenDecomp.collectedBasis fun μ ↦ finBasis ℂ (s.eigenspace μ)`. Establish `hI : Fintype I` using `FiniteDimensional.fintypeBasisIndex v`.

Set `μ : I → ℂ` to `Sigma.fst`. Establish `hsv (i : I) : s (v i) = μ i • v i` using `Module.End.mem_eigenspace_iff.mp (eigenDecomp.collectedBasis_mem _ i)`. Establish `hpow : ∀ (i : I) (k : ℕ), (s ^ k) (v i) = μ i ^ k • v i`. Introduce `i k`. Proceed by induction on `k with`.

Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ, Module.End.mul_apply, hsv, map_smul, ih, smul_smul, pow_succ, mul_comm]`. Establish `hμn : ∀ i, μ i ^ n = 1`. Introduce `i`.

Establish `h1` using `hpow i n`. Rewrite `h1` using `[hsn, Module.End.one_apply]`. Establish `h2 : (μ i ^ n - 1) • v i = 0` using `by rw [sub_smul, one_smul, ← h1, sub_self]`. Break down `smul_eq_zero.mp h2 with h3 | h3` into its components or cases. Conclude with `sub_eq_zero.mp h3`.

Conclude with `absurd h3 (v.ne_zero i)`. Establish `hμ0 : ∀ i, μ i ≠ 0`. Introduce `i h0`. Use `hμn i` as an intermediate fact. Rewrite `this` using `[h0, zero_pow hn0.ne']`.

Conclude with `zero_ne_one this`. Establish `hinv : ∀ i, ρ g⁻¹ (v i) = (starRingEnd ℂ) (μ i) • v i`. Introduce `i`. Establish `h1 : ρ g⁻¹ (s (v i)) = v i`. Rewrite using `[hs, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`.

Rewrite `h1` using `[hsv, map_smul]`. Establish `h2 : (μ i)⁻¹ = (starRingEnd ℂ) (μ i)` using `Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one (hμn i) hn0.ne')`. Rewrite using `[← h2]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[smul_smul, inv_mul_cancel₀ (hμ0 i), one_smul]`.

Use `_ = (μ i)⁻¹ • v i := by rw [h1]`. Conclude with `⟨I, hI, μ, (finrank_eq_card_basis v).symm, hμn, trace_of_diag v _ μ hsv, trace_of_diag v _ _ hinv⟩`.
-/
theorem eigen_data {G V : Type} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (g : G) :
    ∃ (I : Type) (_ : Fintype I) (μ : I → ℂ), Fintype.card I = finrank ℂ V ∧
      (∀ i, μ i ^ orderOf g = 1) ∧ LinearMap.trace ℂ V (ρ g) = ∑ i, μ i ∧
      LinearMap.trace ℂ V (ρ g⁻¹) = ∑ i, starRingEnd ℂ (μ i) := by
  classical
  set s : Module.End ℂ V := ρ g with hs
  set n := orderOf g with hn
  have hn0 : 0 < n := orderOf_pos g
  have hsn : s ^ n = 1 := by rw [hs, ← map_pow, hn, pow_orderOf_eq_one, map_one]
  have hsq : Squarefree (Polynomial.X ^ n - 1 : Polynomial ℂ) :=
    (Polynomial.X_pow_sub_one_separable_iff.mpr (by exact_mod_cast hn0.ne')).squarefree
  have hss : s.IsSemisimple :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq (by simp [hsn])
  let eigenDecomp := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    s.eigenspaces_iSupIndep hss.iSup_eigenspace_eq_top
  let I := (ν : ℂ) × Fin (finrank ℂ (s.eigenspace ν))
  let v : Basis I ℂ V := eigenDecomp.collectedBasis fun μ ↦ finBasis ℂ (s.eigenspace μ)
  have hI : Fintype I := FiniteDimensional.fintypeBasisIndex v
  let μ : I → ℂ := Sigma.fst
  have hsv (i : I) : s (v i) = μ i • v i :=
    Module.End.mem_eigenspace_iff.mp (eigenDecomp.collectedBasis_mem _ i)
  have hpow : ∀ (i : I) (k : ℕ), (s ^ k) (v i) = μ i ^ k • v i := by
    intro i k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, hsv, map_smul, ih, smul_smul, pow_succ, mul_comm]
  have hμn : ∀ i, μ i ^ n = 1 := by
    intro i
    have h1 := hpow i n
    rw [hsn, Module.End.one_apply] at h1
    have h2 : (μ i ^ n - 1) • v i = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 (v.ne_zero i)
  have hμ0 : ∀ i, μ i ≠ 0 := by
    intro i h0
    have := hμn i
    rw [h0, zero_pow hn0.ne'] at this
    exact zero_ne_one this
  have hinv : ∀ i, ρ g⁻¹ (v i) = (starRingEnd ℂ) (μ i) • v i := by
    intro i
    have h1 : ρ g⁻¹ (s (v i)) = v i := by
      rw [hs, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [hsv, map_smul] at h1
    have h2 : (μ i)⁻¹ = (starRingEnd ℂ) (μ i) :=
      Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one (hμn i) hn0.ne')
    rw [← h2]
    calc ρ g⁻¹ (v i) = (μ i)⁻¹ • (μ i • ρ g⁻¹ (v i)) := by
          rw [smul_smul, inv_mul_cancel₀ (hμ0 i), one_smul]
      _ = (μ i)⁻¹ • v i := by rw [h1]
  exact ⟨I, hI, μ, (finrank_eq_card_basis v).symm, hμn, trace_of_diag v _ μ hsv,
    trace_of_diag v _ _ hinv⟩

/- English proof (translation)
Take `⟨I, hI, μ, hcard, hμ, htr, htr'⟩` from `eigen_data ρ g`. Establish `hn : orderOf g ≠ 0` using `(orderOf_pos g).ne'`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[htr]`. Use `IsIntegral.sum _ fun i _ => ?_` and prove the remaining obligations.

Use `IsIntegral.of_pow (orderOf_pos g) ?_` and prove the remaining obligations. Rewrite using `[hμ i]`. Conclude with `isIntegral_one`. Rewrite using `[htr', htr, star_sum]`. Both sides reduce to the same expression.

Rewrite using `[htr]`. Combine the equalities or inequalities in the displayed calculation. Establish `h1 : ‖μ i‖ ^ orderOf g = 1` using `by rw [← norm_pow, hμ i, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 h1`. Use `_ = (finrank ℂ V : ℝ) := by simp [hcard]`.
-/
theorem char_complex {G V : Type} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (g : G) :
    IsIntegral ℤ (LinearMap.trace ℂ V (ρ g)) ∧
      LinearMap.trace ℂ V (ρ g⁻¹) = star (LinearMap.trace ℂ V (ρ g)) ∧
      ‖LinearMap.trace ℂ V (ρ g)‖ ≤ (finrank ℂ V : ℝ) := by
  obtain ⟨I, hI, μ, hcard, hμ, htr, htr'⟩ := eigen_data ρ g
  have hn : orderOf g ≠ 0 := (orderOf_pos g).ne'
  refine ⟨?_, ?_, ?_⟩
  · rw [htr]
    refine IsIntegral.sum _ fun i _ => ?_
    refine IsIntegral.of_pow (orderOf_pos g) ?_
    rw [hμ i]
    exact isIntegral_one
  · rw [htr', htr, star_sum]
    rfl
  · rw [htr]
    calc ‖∑ i, μ i‖ ≤ ∑ i, ‖μ i‖ := norm_sum_le _ _
      _ = ∑ _i : I, (1 : ℝ) := Finset.sum_congr rfl fun i _ => by
          have h1 : ‖μ i‖ ^ orderOf g = 1 := by rw [← norm_pow, hμ i, norm_one]
          exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 h1
      _ = (finrank ℂ V : ℝ) := by simp [hcard]

def repC {K : Type} [Field K] (σ : K →+* ℂ) {G : Type} [Group G] {T : Type} [AddCommGroup T]
    [Module K T] [FiniteDimensional K T] (τ : Representation K G T) :
    Representation ℂ G (Fin (finrank K T) → ℂ) :=
  ((Matrix.toLinAlgEquiv' : Matrix (Fin (finrank K T)) (Fin (finrank K T)) ℂ ≃ₐ[ℂ] _) :
      Matrix (Fin (finrank K T)) (Fin (finrank K T)) ℂ →* _).comp
    (((σ.mapMatrix : Matrix (Fin (finrank K T)) (Fin (finrank K T)) K →+* _) :
        Matrix (Fin (finrank K T)) (Fin (finrank K T)) K →* _).comp
      (((LinearMap.toMatrixAlgEquiv (Module.finBasis K T)) : (T →ₗ[K] T) →* _).comp τ))

/- English proof (translation)
Rewrite using `[LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin (finrank K T))), charOf, LinearMap.trace_eq_matrix_trace K (Module.finBasis K T) (τ g)]`. Simplify using `[repC, LinearMap.toMatrix_eq_toMatrix', Matrix.trace, map_sum, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]`.
-/
theorem trace_repC {K : Type} [Field K] (σ : K →+* ℂ) {G : Type} [Group G] {T : Type}
    [AddCommGroup T] [Module K T] [FiniteDimensional K T] (τ : Representation K G T) (g : G) :
    LinearMap.trace ℂ _ (repC σ τ g) = σ (charOf τ g) := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin (finrank K T))), charOf,
    LinearMap.trace_eq_matrix_trace K (Module.finBasis K T) (τ g)]
  simp [repC, LinearMap.toMatrix_eq_toMatrix', Matrix.trace, map_sum, LinearMap.toMatrixAlgEquiv_apply,
    LinearMap.toMatrix_apply]

end CharacterLemmas

open CharacterLemmas

/- English proof (translation)
Introduce `K _ _ G _ _ T _ _ _ τ g`. Establish `hmain : ∀ σ : K →+* ℂ, IsIntegral ℤ (σ (charOf τ g)) ∧ σ (charOf τ g⁻¹) = star (σ (charOf τ g)) ∧ ‖σ (charOf τ g)‖ ≤ (finrank K T : ℝ)`. Introduce `σ`. Take `⟨h1, h2, h3⟩` from `char_complex (repC σ τ) g`. Rewrite `h2` using `[trace_repC, trace_repC]`.

Rewrite `h1`, `h3` using `[trace_repC]`. Use `⟨h1, h2, ?_⟩` and prove the remaining obligations. Simplify using `using h3`. Take `⟨σ⟩ : Nonempty (K →+* ℂ)` from `by first`. Consider the case `exact inferInstance`.

Consider the case `exact ⟨(IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := K)).toRingHom⟩`. Use `⟨?_, fun σ' => ⟨(hmain σ').2.1, (hmain σ').2.2⟩⟩` and prove the remaining obligations. Conclude with `(isIntegral_algHom_iff σ.toIntAlgHom σ.injective).1 (hmain σ).1`.
-/
theorem charFacts : CharFacts := by
  intro K _ _ G _ _ T _ _ _ τ g
  have hmain : ∀ σ : K →+* ℂ, IsIntegral ℤ (σ (charOf τ g)) ∧
      σ (charOf τ g⁻¹) = star (σ (charOf τ g)) ∧ ‖σ (charOf τ g)‖ ≤ (finrank K T : ℝ) := by
    intro σ
    obtain ⟨h1, h2, h3⟩ := char_complex (repC σ τ) g
    rw [trace_repC, trace_repC] at h2
    rw [trace_repC] at h1 h3
    refine ⟨h1, h2, ?_⟩
    simpa using h3
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := by
    first
    | exact inferInstance
    | exact ⟨(IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := K)).toRingHom⟩
  refine ⟨?_, fun σ' => ⟨(hmain σ').2.1, (hmain σ').2.2⟩⟩
  exact (isIntegral_algHom_iff σ.toIntAlgHom σ.injective).1 (hmain σ).1

/- English proof (translation)
Introduce `K _ _ H _ _ χ`. Establish `hint : ∀ h, IsIntegral ℤ ((χ h : Kˣ) : K)`. Introduce `h`. Use `IsIntegral.of_pow (orderOf_pos h) ?_` and prove the remaining obligations. Rewrite using `[← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one]`.

Conclude with `isIntegral_one`. Set `φ : H →* 𝓞 K` to `{ toFun := fun h => ⟨((χ h : Kˣ) : K), hint h⟩ map_one' := by`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Use `show ((χ 1 : Kˣ) : K) = 1`. Rewrite using `[map_one, Units.val_one]`.

Use the proof step `map_mul' := fun a b => by`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Use `show ((χ (a * b) : Kˣ) : K) = ((χ a : Kˣ) : K) * ((χ b : Kˣ) : K)`. Rewrite using `[map_mul, Units.val_mul] }`. Conclude with `⟨φ.toHomUnits, fun h => rfl⟩`.
-/
theorem liftChar : LiftChar := by
  intro K _ _ H _ _ χ
  have hint : ∀ h, IsIntegral ℤ ((χ h : Kˣ) : K) := by
    intro h
    refine IsIntegral.of_pow (orderOf_pos h) ?_
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one]
    exact isIntegral_one
  let φ : H →* 𝓞 K :=
    { toFun := fun h => ⟨((χ h : Kˣ) : K), hint h⟩
      map_one' := by
        apply RingOfIntegers.ext
        show ((χ 1 : Kˣ) : K) = 1
        rw [map_one, Units.val_one]
      map_mul' := fun a b => by
        apply RingOfIntegers.ext
        show ((χ (a * b) : Kˣ) : K) = ((χ a : Kˣ) : K) * ((χ b : Kˣ) : K)
        rw [map_mul, Units.val_mul] }
  exact ⟨φ.toHomUnits, fun h => rfl⟩

/- English proof (translation)
Introduce `K _ _ G _ _ S T _ _ _ τ hgood s`. Take `⟨-, -, hsum⟩` from `h K G S T τ hgood`. Establish `hs` using `hsum s`. Take `⟨σ⟩ : Nonempty (K →+* ℂ)` from `by first`. Consider the case `exact inferInstance`.

Consider the case `exact ⟨(IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := K)).toRingHom⟩`. Establish `hdim : charOf (τ s) 1 = (finrank K (T s) : K)`. Unfold `charOf`. Rewrite using `[map_one, LinearMap.trace_one]`. Establish `hterm : ∀ x : G, σ (charOf (τ s) x⁻¹ * charOf (τ s) x) = ((‖σ (charOf (τ s) x)‖ ^ 2 : ℝ) : ℂ)`.

Introduce `x`. Rewrite using `[map_mul, ((charFacts K G (T s) (τ s) x).2 σ).1]`. Use `push_cast`. Conclude with `Complex.conj_mul' _`. Establish `e1` using `congrArg σ hs`.

Rewrite `e1` using `[map_sum, map_natCast]`. Rewrite `e1` using `[hterm]`. Establish `e2 : (∑ x : G, ‖σ (charOf (τ s) x)‖ ^ 2 : ℝ) = (Fintype.card G : ℝ)`. Conclude with `e1` after adjusting the coercions. Establish `key : ((finrank K (T s) : ℝ)) ^ 2 ≤ (Fintype.card G : ℝ)`.

Rewrite using `[← e2]`. Establish `h1 : ‖σ (charOf (τ s) 1)‖ ^ 2 = ((finrank K (T s) : ℝ)) ^ 2`. Rewrite using `[hdim, map_natCast, Complex.norm_natCast]`. Rewrite using `[← h1]`. Conclude with `Finset.single_le_sum (f := fun x : G => ‖σ (charOf (τ s) x)‖ ^ 2) (fun x _ => by positivity) (Finset.mem_univ 1)`.

Establish `key' : finrank K (T s) ^ 2 ≤ Fintype.card G` using `by exact_mod_cast key`. Use `⟨key', fun H χ => le_trans ?_ key'⟩` and prove the remaining obligations. Conclude with `Nat.pow_le_pow_left (Submodule.finrank_le _) 2`.
-/
theorem dimSq_of (h : Schur) : DimSq := by
  intro K _ _ G _ _ S T _ _ _ τ hgood s
  obtain ⟨-, -, hsum⟩ := h K G S T τ hgood
  have hs := hsum s
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := by
    first
    | exact inferInstance
    | exact ⟨(IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := K)).toRingHom⟩
  have hdim : charOf (τ s) 1 = (finrank K (T s) : K) := by
    unfold charOf
    rw [map_one, LinearMap.trace_one]
  have hterm : ∀ x : G, σ (charOf (τ s) x⁻¹ * charOf (τ s) x) =
      ((‖σ (charOf (τ s) x)‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [map_mul, ((charFacts K G (T s) (τ s) x).2 σ).1]
    push_cast
    exact Complex.conj_mul' _
  have e1 := congrArg σ hs
  rw [map_sum, map_natCast] at e1
  simp_rw [hterm] at e1
  have e2 : (∑ x : G, ‖σ (charOf (τ s) x)‖ ^ 2 : ℝ) = (Fintype.card G : ℝ) := by
    exact_mod_cast e1
  have key : ((finrank K (T s) : ℝ)) ^ 2 ≤ (Fintype.card G : ℝ) := by
    rw [← e2]
    have h1 : ‖σ (charOf (τ s) 1)‖ ^ 2 = ((finrank K (T s) : ℝ)) ^ 2 := by
      rw [hdim, map_natCast, Complex.norm_natCast]
    rw [← h1]
    exact Finset.single_le_sum (f := fun x : G => ‖σ (charOf (τ s) x)‖ ^ 2)
      (fun x _ => by positivity) (Finset.mem_univ 1)
  have key' : finrank K (T s) ^ 2 ≤ Fintype.card G := by exact_mod_cast key
  refine ⟨key', fun H χ => le_trans ?_ key'⟩
  exact Nat.pow_le_pow_left (Submodule.finrank_le _) 2

end Formalism.IndefR.LatticeTransfer
