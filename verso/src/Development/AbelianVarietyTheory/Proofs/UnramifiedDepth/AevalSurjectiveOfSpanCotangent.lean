import Mathlib
import ReciprocityTheory.DualLattices.SmallLevelClassSet
import ReciprocityTheory.DualLattices.RidConvolutionDerivation
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AevalSurjectiveOfIsNilpotentKer

noncomputable section

open ReciprocityTheory.PGsh

namespace GlobalTheory.HeightOneHopf

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.NilpotentKernelSurjective.aeval_surjective_of_isNilpotent_ker`. Consider the case `exact _root_.GlobalTheory.NilpotentKernelSurjective.aeval_surjective_of_isNilpotent_ker`. Consider the case `(apply _root_.GlobalTheory.NilpotentKernelSurjective.aeval_surjective_of_isNilpotent_ker <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.NilpotentKernelSurjective.aeval_surjective_of_isNilpotent_ker <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.NilpotentKernelSurjective.aeval_surjective_of_isNilpotent_ker <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.NilpotentKernelSurjective.aeval_surjective_of_isNilpotent_ker ..)`.
-/
theorem aeval_surjective_of_span_cotangent {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (ε : A →ₐ[R] R) (hnil : IsNilpotent (RingHom.ker ε)) {d : ℕ} (x : Fin d → A)
    (hx : ∀ i, x i ∈ RingHom.ker ε)
    (hspan : ∀ y ∈ RingHom.ker ε, ∃ l : Fin d → R, y - ∑ i, l i • x i ∈ RingHom.ker ε ^ 2) :
    Function.Surjective (MvPolynomial.aeval (R := R) x) := by
  first
  | exact @_root_.GlobalTheory.NilpotentKernelSurjective.aeval_surjective_of_isNilpotent_ker
  | exact _root_.GlobalTheory.NilpotentKernelSurjective.aeval_surjective_of_isNilpotent_ker
  | (apply _root_.GlobalTheory.NilpotentKernelSurjective.aeval_surjective_of_isNilpotent_ker <;> assumption)
  | (intros; apply _root_.GlobalTheory.NilpotentKernelSurjective.aeval_surjective_of_isNilpotent_ker <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NilpotentKernelSurjective.aeval_surjective_of_isNilpotent_ker <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NilpotentKernelSurjective.aeval_surjective_of_isNilpotent_ker ..)

/- English proof (translation)
Use `set I : Ideal H := RingHom.ker (Bialgebra.counitAlgHom k H) with hI`. Use `set J : Submodule k H := (I ^ 2).restrictScalars k with hJ`. Set `φ : (Fin d → k) →ₗ[k] H ⧸ J` to `J.mkQ ∘ₗ Fintype.linearCombination k x`. Establish `hφ : LinearMap.ker φ = ⊥`. Rewrite using `[LinearMap.ker_eq_bot']`.

Introduce `l hl`. Apply `hind l` to reduce the goal to its premises. Establish `h1 : Fintype.linearCombination k x l ∈ J` using `(Submodule.Quotient.mk_eq_zero J).1 hl`. Rewrite `h1` using `[Fintype.linearCombination_apply]`. Conclude with `h1`.

Take `⟨g, hg⟩` from `φ.exists_leftInverse_of_injective hφ`. Set `π : H →ₗ[k] H` to `LinearMap.id - Algebra.linearMap k H ∘ₗ Coalgebra.counit`. Establish `hπ : ∀ y ∈ I, π y = y`. Introduce `y hy`. Rewrite `hy` using `[hI, RingHom.mem_ker, Bialgebra.counitAlgHom_apply]`.

Simplify using `[π, hy]`. Use `⟨fun i => LinearMap.proj i ∘ₗ g ∘ₗ J.mkQ ∘ₗ π, fun i => ?_, fun i j => ?_⟩` and prove the remaining obligations. Apply `isPtDer_of` to reduce the goal to its premises. Simplify using `[π]`. Introduce `f hf`.

Establish `hfI : f ∈ I` using `Ideal.pow_le_self two_ne_zero hf`. Establish `h0 : J.mkQ f = 0`. Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `hf`. Simplify using `only [LinearMap.comp_apply, hπ f hfI, h0, map_zero]`.

Establish `e : J.mkQ (x j) = φ (Pi.single j 1)`. Simplify using `[φ]`. Establish `e2 : g (φ (Pi.single j 1)) = Pi.single j 1` using `LinearMap.congr_fun hg _`. Simplify using `only [LinearMap.comp_apply, hπ _ (hx j), e, e2, LinearMap.proj_apply, Pi.single_apply]`.
-/
theorem exists_isPtDer_dual {k H : Type*} [Field k] [CommRing H] [Bialgebra k H] {d : ℕ}
    (x : Fin d → H) (hx : ∀ i, x i ∈ RingHom.ker (Bialgebra.counitAlgHom k H))
    (hind : ∀ l : Fin d → k,
      ∑ i, l i • x i ∈ RingHom.ker (Bialgebra.counitAlgHom k H) ^ 2 → l = 0) :
    ∃ δ : Fin d → H →ₗ[k] k, (∀ i, IsPtDer (δ i)) ∧
      ∀ i j, δ i (x j) = if i = j then 1 else 0 := by
  classical
  set I : Ideal H := RingHom.ker (Bialgebra.counitAlgHom k H) with hI
  set J : Submodule k H := (I ^ 2).restrictScalars k with hJ
  let φ : (Fin d → k) →ₗ[k] H ⧸ J := J.mkQ ∘ₗ Fintype.linearCombination k x
  have hφ : LinearMap.ker φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro l hl
    apply hind l
    have h1 : Fintype.linearCombination k x l ∈ J := (Submodule.Quotient.mk_eq_zero J).1 hl
    rw [Fintype.linearCombination_apply] at h1
    exact h1
  obtain ⟨g, hg⟩ := φ.exists_leftInverse_of_injective hφ
  let π : H →ₗ[k] H := LinearMap.id - Algebra.linearMap k H ∘ₗ Coalgebra.counit
  have hπ : ∀ y ∈ I, π y = y := by
    intro y hy
    rw [hI, RingHom.mem_ker, Bialgebra.counitAlgHom_apply] at hy
    simp [π, hy]
  refine ⟨fun i => LinearMap.proj i ∘ₗ g ∘ₗ J.mkQ ∘ₗ π, fun i => ?_, fun i j => ?_⟩
  · apply isPtDer_of
    · simp [π]
    · intro f hf
      have hfI : f ∈ I := Ideal.pow_le_self two_ne_zero hf
      have h0 : J.mkQ f = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hf
      simp only [LinearMap.comp_apply, hπ f hfI, h0, map_zero]
  · have e : J.mkQ (x j) = φ (Pi.single j 1) := by
      simp [φ]
    have e2 : g (φ (Pi.single j 1)) = Pi.single j 1 := LinearMap.congr_fun hg _
    simp only [LinearMap.comp_apply, hπ _ (hx j), e, e2, LinearMap.proj_apply, Pi.single_apply]

/- English proof (translation)
Introduce `p hp k H _ _ _ _ _ d x hpow hx hspan hind`. Establish `: IsNoetherianRing H` using `isNoetherian_of_tower k inferInstance`. Establish `hnil : IsNilpotent (RingHom.ker (Bialgebra.counitAlgHom k H))`. Rewrite using `[Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]`. Introduce `f hf`.

Conclude with `⟨p, hpow f hf⟩`. Establish `hsurj` using `aeval_surjective_of_span_cotangent _ hnil x hx hspan`. Use `⟨hsurj, le_antisymm ?_ ?_⟩` and prove the remaining obligations. Take `⟨δ, hδ, hδx⟩` from `exists_isPtDer_dual x hx hind`. Introduce `P hP`.

Apply `mem_span_pow_of_coeff` to reduce the goal to its premises. Use `coeff_eq_zero_of_stable (Bialgebra.counitAlgHom k H) x hx (fun i => convD (δ i)) (fun i => convD_mul _ (hδ i)) (fun i j => ?_) hsurj (CharP.cast_eq_zero k p) (fun n h0 hn => ?_) {0} ?_ ?_ P hP` and prove the remaining obligations. Rewrite using `[Bialgebra.counitAlgHom_apply, counit_convD, hδx]`. Rewrite using `[isUnit_iff_ne_zero, Ne, CharP.cast_eq_zero_iff k p]`. Conclude with `Nat.not_dvd_of_pos_of_lt h0 hn`.

Introduce and unpack `a rfl`. Simplify using the standard rewrite rules. Introduce and unpack `i a rfl`. Simplify using the standard rewrite rules. Introduce `P hP`.

Conclude with `aeval_eq_zero_of_mem_span x (fun j => hpow _ (hx j)) hP`.
-/
theorem truncated_polynomial : TruncatedPolynomialStatement := by
  intro p hp k H _ _ _ _ _ d x hpow hx hspan hind
  have : IsNoetherianRing H := isNoetherian_of_tower k inferInstance
  have hnil : IsNilpotent (RingHom.ker (Bialgebra.counitAlgHom k H)) := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
    intro f hf
    exact ⟨p, hpow f hf⟩
  have hsurj := aeval_surjective_of_span_cotangent _ hnil x hx hspan
  refine ⟨hsurj, le_antisymm ?_ ?_⟩
  · obtain ⟨δ, hδ, hδx⟩ := exists_isPtDer_dual x hx hind
    intro P hP
    apply mem_span_pow_of_coeff
    refine coeff_eq_zero_of_stable (Bialgebra.counitAlgHom k H) x hx (fun i => convD (δ i))
      (fun i => convD_mul _ (hδ i)) (fun i j => ?_) hsurj (CharP.cast_eq_zero k p)
      (fun n h0 hn => ?_) {0} ?_ ?_ P hP
    · rw [Bialgebra.counitAlgHom_apply, counit_convD, hδx]
    · rw [isUnit_iff_ne_zero, Ne, CharP.cast_eq_zero_iff k p]
      exact Nat.not_dvd_of_pos_of_lt h0 hn
    · rintro a rfl; simp
    · rintro i a rfl; simp
  · intro P hP
    exact aeval_eq_zero_of_mem_span x (fun j => hpow _ (hx j)) hP

end GlobalTheory.HeightOneHopf
