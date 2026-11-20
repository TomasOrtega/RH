import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

namespace Flag

open MvPolynomial Finset

noncomputable section

/- English proof (translation)
Set `K : ℕ →o Ideal R` to `⟨fun n => RingHom.ker (φ ^ n), fun m n hmn x hx => by`. Simplify using `only [RingHom.mem_ker, RingHom.coe_pow] at hx ⊢`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hmn`. Rewrite using `[add_comm, Function.iterate_add_apply, hx, iterate_map_zero]⟩`. Establish `hsurj : ∀ n, Function.Surjective (φ^[n])` using `fun n => hφ.iterate n`.

Take `⟨n, hn⟩` from `(monotone_stabilizes_iff_noetherian (R := R) (M := R)).mpr (isNoetherianRing_iff.mp inferInstance) K`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Take `⟨y, rfl⟩` from `hsurj n x`. Establish `hy : y ∈ K (n + 1)` using `by show (φ ^ (n + 1)) y = 0`.

Rewrite using `[RingHom.coe_pow, Function.iterate_succ_apply', hx]`. Rewrite `hy` using `[← hn (n + 1) (Nat.le_succ n)]`. Establish `h' : (φ ^ n) y = 0` using `hy`. Simplify `h'` using `[RingHom.coe_pow]`.
-/
theorem injective_of_surjective_endo {R : Type*} [CommRing R] [IsNoetherianRing R]
    (φ : R →+* R) (hφ : Function.Surjective φ) : Function.Injective φ := by
  let K : ℕ →o Ideal R := ⟨fun n => RingHom.ker (φ ^ n), fun m n hmn x hx => by
    simp only [RingHom.mem_ker, RingHom.coe_pow] at hx ⊢
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [add_comm, Function.iterate_add_apply, hx, iterate_map_zero]⟩
  have hsurj : ∀ n, Function.Surjective (φ^[n]) := fun n => hφ.iterate n
  obtain ⟨n, hn⟩ := (monotone_stabilizes_iff_noetherian (R := R) (M := R)).mpr
    (isNoetherianRing_iff.mp inferInstance) K
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := hsurj n x
  have hy : y ∈ K (n + 1) := by
    show (φ ^ (n + 1)) y = 0
    rw [RingHom.coe_pow, Function.iterate_succ_apply', hx]
  rw [← hn (n + 1) (Nat.le_succ n)] at hy
  have h' : (φ ^ n) y = 0 := hy
  simpa [RingHom.coe_pow] using h'

/- English proof (translation)
Use `⟨X ⟨j - 1, by omega⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `powerSumHom N (X ⟨j - 1, by omega⟩) = _`. Simplify using `only [powerSumHom, aeval_X]`. Use `congr 1`. Use `show j - 1 + 1 = j`.

Use linear arithmetic over natural numbers and integers.
-/
theorem psum_mem_range (N j : ℕ) (hj1 : 1 ≤ j) (hjN : j ≤ N) :
    psum (Fin N) ℚ j ∈ (powerSumHom N).range := by
  refine ⟨X ⟨j - 1, by omega⟩, ?_⟩
  change powerSumHom N (X ⟨j - 1, by omega⟩) = _
  simp only [powerSumHom, aeval_X]
  congr 1
  show j - 1 + 1 = j
  omega

/- English proof (translation)
Proceed by induction on `k using Nat.strong_induction_on with`. Consider the case `_ k ih`. Break down `Nat.eq_zero_or_pos k with rfl | hk0` into its components or cases. Rewrite using `[esymm_zero]`. Conclude with `Subalgebra.one_mem _`.

Establish `hN` using `mul_esymm_eq_sum (Fin N) ℚ k`. Establish `hmem : (k : MvPolynomial (Fin N) ℚ) * esymm (Fin N) ℚ k ∈ (powerSumHom N).range`. Rewrite using `[hN]`. Use `Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) _) ?_` and prove the remaining obligations. Use `Subalgebra.sum_mem _ (fun a ha => ?_)` and prove the remaining obligations.

Take `⟨ha1', ha2⟩` from `Finset.mem_filter.mp ha`. Establish `ha1` using `Finset.HasAntidiagonal.mem_antidiagonal.mp ha1'`. Use `Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) _) (ih a.1 ha2 (by omega))) (psum_mem_range N a.2 (by omega) (by omega))` and prove the remaining obligations. Establish `hinv : esymm (Fin N) ℚ k = C ((k : ℚ)⁻¹) * ((k : MvPolynomial (Fin N) ℚ) * esymm (Fin N) ℚ k)`. Rewrite using `[← mul_assoc, show (k : MvPolynomial (Fin N) ℚ) = C (k : ℚ) by simp, ← C_mul, inv_mul_cancel₀ (by exact_mod_cast hk0.ne'), C_1, one_mul]`.

Rewrite using `[hinv]`. Conclude with `Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) hmem`.
-/
theorem esymm_mem_range (N k : ℕ) (hk : k ≤ N) :
    esymm (Fin N) ℚ k ∈ (powerSumHom N).range := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [esymm_zero]; exact Subalgebra.one_mem _
    have hN := mul_esymm_eq_sum (Fin N) ℚ k
    have hmem : (k : MvPolynomial (Fin N) ℚ) * esymm (Fin N) ℚ k ∈ (powerSumHom N).range := by
      rw [hN]
      refine Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) _) ?_
      refine Subalgebra.sum_mem _ (fun a ha => ?_)
      obtain ⟨ha1', ha2⟩ := Finset.mem_filter.mp ha
      have ha1 := Finset.HasAntidiagonal.mem_antidiagonal.mp ha1'
      refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _
        (Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) _)
        (ih a.1 ha2 (by omega))) (psum_mem_range N a.2 (by omega) (by omega))
    have hinv : esymm (Fin N) ℚ k = C ((k : ℚ)⁻¹) * ((k : MvPolynomial (Fin N) ℚ) * esymm (Fin N) ℚ k) := by
      rw [← mul_assoc, show (k : MvPolynomial (Fin N) ℚ) = C (k : ℚ) by simp, ← C_mul,
        inv_mul_cancel₀ (by exact_mod_cast hk0.ne'), C_1, one_mul]
    rw [hinv]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) hmem

/- English proof (translation)
Take `⟨Q, hQ⟩` from `esymmAlgHom_fin_surjective ℚ (le_refl N) ⟨P, hP⟩`. Establish `h1 : P = aeval (fun i : Fin N => esymm (Fin N) ℚ (i + 1)) Q`. Rewrite using `[← esymmAlgHom_apply, hQ]`. Establish `h2 : aeval (fun i : Fin N => esymm (Fin N) ℚ (i + 1)) Q ∈ (powerSumHom N).range`. Establish `hsub : Algebra.adjoin ℚ (Set.range fun i : Fin N => esymm (Fin N) ℚ (i + 1)) ≤ (powerSumHom N).range`.

Rewrite using `[Algebra.adjoin_le_iff]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `esymm_mem_range N _ (by omega)`. Conclude with `hsub (by rw [Algebra.adjoin_range_eq_range_aeval]; exact ⟨Q, rfl⟩)`. Rewrite using `[h1]`.

Conclude with `h2`.
-/
theorem exists_powerSumHom_eq {N : ℕ} {P : MvPolynomial (Fin N) ℚ} (hP : P.IsSymmetric) :
    ∃ S, powerSumHom N S = P := by
  obtain ⟨Q, hQ⟩ := esymmAlgHom_fin_surjective ℚ (le_refl N) ⟨P, hP⟩
  have h1 : P = aeval (fun i : Fin N => esymm (Fin N) ℚ (i + 1)) Q := by
    rw [← esymmAlgHom_apply, hQ]
  have h2 : aeval (fun i : Fin N => esymm (Fin N) ℚ (i + 1)) Q ∈ (powerSumHom N).range := by
    have hsub : Algebra.adjoin ℚ (Set.range fun i : Fin N => esymm (Fin N) ℚ (i + 1)) ≤
        (powerSumHom N).range := by
      rw [Algebra.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      exact esymm_mem_range N _ (by omega)
    exact hsub (by rw [Algebra.adjoin_range_eq_range_aeval]; exact ⟨Q, rfl⟩)
  rw [h1]
  exact h2

/- English proof (translation)
Establish `: powerSumHom N S ∈ symmetricSubalgebra (Fin N) ℚ`. Establish `hsub : (powerSumHom N).range ≤ symmetricSubalgebra (Fin N) ℚ`. Introduce and unpack `_ ⟨T, rfl⟩`. Simplify using `only [powerSumHom]`. Establish `: Algebra.adjoin ℚ (Set.range fun i : Fin N => psum (Fin N) ℚ (i.val + 1)) ≤ symmetricSubalgebra (Fin N) ℚ`.

Rewrite using `[Algebra.adjoin_le_iff]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `psum_isSymmetric (Fin N) ℚ _`. Conclude with `this (by rw [Algebra.adjoin_range_eq_range_aeval]; exact ⟨T, rfl⟩)`. Conclude with `hsub ⟨S, rfl⟩`.

Conclude with `this`.
-/
theorem powerSumHom_isSymmetric (N : ℕ) (S : MvPolynomial (Fin N) ℚ) :
    (powerSumHom N S).IsSymmetric := by
  have : powerSumHom N S ∈ symmetricSubalgebra (Fin N) ℚ := by
    have hsub : (powerSumHom N).range ≤ symmetricSubalgebra (Fin N) ℚ := by
      rintro _ ⟨T, rfl⟩
      simp only [powerSumHom]
      have : Algebra.adjoin ℚ (Set.range fun i : Fin N => psum (Fin N) ℚ (i.val + 1)) ≤
          symmetricSubalgebra (Fin N) ℚ := by
        rw [Algebra.adjoin_le_iff]
        rintro _ ⟨i, rfl⟩
        exact psum_isSymmetric (Fin N) ℚ _
      exact this (by rw [Algebra.adjoin_range_eq_range_aeval]; exact ⟨T, rfl⟩)
    exact hsub ⟨S, rfl⟩
  exact this

/- English proof (translation)
Set `e` to `esymmAlgEquiv (Fin N) ℚ (n := N) (by simp)`. Set `π : MvPolynomial (Fin N) ℚ →ₐ[ℚ] symmetricSubalgebra (Fin N) ℚ` to `(powerSumHom N).codRestrict _ (fun S => powerSumHom_isSymmetric N S)`. Set `φ : MvPolynomial (Fin N) ℚ →ₐ[ℚ] MvPolynomial (Fin N) ℚ` to `e.symm.toAlgHom.comp π`. Establish `hsurj : Function.Surjective φ`. Introduce `T`.

Take `⟨S, hS⟩` from `exists_powerSumHom_eq (e T).2`. Use `⟨S, ?_⟩` and prove the remaining obligations. Apply `e.injective` to reduce the goal to its premises. Simplify using `only [φ, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]`. Conclude with `Subtype.ext hS`.

Establish `hinj : Function.Injective φ` using `injective_of_surjective_endo φ.toRingHom hsurj`. Introduce `S T hST`. Apply `hinj` to reduce the goal to its premises. Simplify using `only [φ, AlgHom.comp_apply]`. Use `congr 1`.

Conclude with `Subtype.ext hST`.
-/
theorem powerSumHom_injective (N : ℕ) : Function.Injective (powerSumHom N) := by

  let e := esymmAlgEquiv (Fin N) ℚ (n := N) (by simp)
  let π : MvPolynomial (Fin N) ℚ →ₐ[ℚ] symmetricSubalgebra (Fin N) ℚ :=
    (powerSumHom N).codRestrict _ (fun S => powerSumHom_isSymmetric N S)
  let φ : MvPolynomial (Fin N) ℚ →ₐ[ℚ] MvPolynomial (Fin N) ℚ := e.symm.toAlgHom.comp π
  have hsurj : Function.Surjective φ := by
    intro T
    obtain ⟨S, hS⟩ := exists_powerSumHom_eq (e T).2
    refine ⟨S, ?_⟩
    apply e.injective
    simp only [φ, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
    exact Subtype.ext hS
  have hinj : Function.Injective φ := injective_of_surjective_endo φ.toRingHom hsurj
  intro S T hST
  apply hinj
  simp only [φ, AlgHom.comp_apply]
  congr 1
  exact Subtype.ext hST

/- English proof (translation)
Proceed by induction on `S using MvPolynomial.induction_on with`. Consider the case `C a => simp [powerSumHom]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p i hp`. Simplify using `only [map_mul, powerSumHom, aeval_X, constantCoeff_X, mul_zero]`.

Simplify using `[psum, constantCoeff_X]`.
-/
theorem constantCoeff_powerSumHom (N : ℕ) (S : MvPolynomial (Fin N) ℚ) :
    constantCoeff (powerSumHom N S) = constantCoeff S := by
  induction S using MvPolynomial.induction_on with
  | C a => simp [powerSumHom]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, powerSumHom, aeval_X, constantCoeff_X, mul_zero]
    simp [psum, constantCoeff_X]

end

end Flag

end RestTerms

end GroundTheory.Heights₂.Heights
