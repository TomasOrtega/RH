import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsAdicCompleteOfPowSmulEqZero

open TensorProduct

namespace GlobalTheory.CompanionTheory.TensorCompleteFinite

open GlobalTheory.CompanionTheory.TensorComplete

/- English proof (translation)
Establish `hM : ∀ (n : ℕ) (x : M), x ∈ (Ideal.span {π} ^ n • ⊤ : Submodule A M) → e x ∈ (Ideal.span {π} ^ n • ⊤ : Submodule A M')`. Introduce `n x hx`. Establish `h1 : (Ideal.span {π} ^ n • ⊤ : Submodule A M).map (e : M →ₗ[A] M') ≤ Ideal.span {π} ^ n • ⊤`. Rewrite using `[Submodule.map_smul'']`. Conclude with `Submodule.smul_mono le_rfl le_top`.

Conclude with `h1 (Submodule.mem_map_of_mem hx)`. Establish `hM' : ∀ (n : ℕ) (x : M'), x ∈ (Ideal.span {π} ^ n • ⊤ : Submodule A M') → e.symm x ∈ (Ideal.span {π} ^ n • ⊤ : Submodule A M)`. Introduce `n x hx`. Establish `h1 : (Ideal.span {π} ^ n • ⊤ : Submodule A M').map (e.symm : M' →ₗ[A] M) ≤ Ideal.span {π} ^ n • ⊤`. Rewrite using `[Submodule.map_smul'']`.

Conclude with `Submodule.smul_mono le_rfl le_top`. Conclude with `h1 (Submodule.mem_map_of_mem hx)`. Use `{ haus' := ?_, prec' := ?_ }` and prove the remaining obligations. Introduce `x hx`. Establish `h0 : e.symm x = 0`.

Use `h.toIsHausdorff.haus' (e.symm x) (fun n => ?_)` and prove the remaining obligations. Rewrite using `[SModEq.sub_mem, sub_zero]`. Establish `hx'` using `(SModEq.sub_mem).mp (hx n)`. Rewrite `hx'` using `[sub_zero]`. Conclude with `hM' n x hx'`.

Simplify using `using congrArg e h0`. Introduce `f hf`. Take `⟨L, hL⟩` from `h.toIsPrecomplete.prec' (fun n => e.symm (f n)) (fun {m n} hmn => by`. Rewrite using `[SModEq.sub_mem, ← map_sub]`. Conclude with `hM' m _ ((SModEq.sub_mem).mp (hf hmn)))`.

Use `⟨e L, fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[SModEq.sub_mem]`. Establish `h2` using `hM n _ ((SModEq.sub_mem).mp (hL n))`. Rewrite `h2` using `[map_sub, LinearEquiv.apply_symm_apply]`. Then use the resulting hypothesis.
-/
theorem isAdicComplete_of_linearEquiv_univ {A : Type} [CommRing A] {π : A} {M : Type} {M' : Type 1}
    [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M'] (e : M ≃ₗ[A] M')
    (h : IsAdicComplete (Ideal.span {π}) M) : IsAdicComplete (Ideal.span {π}) M' := by
  have hM : ∀ (n : ℕ) (x : M), x ∈ (Ideal.span {π} ^ n • ⊤ : Submodule A M) →
      e x ∈ (Ideal.span {π} ^ n • ⊤ : Submodule A M') := by
    intro n x hx
    have h1 : (Ideal.span {π} ^ n • ⊤ : Submodule A M).map (e : M →ₗ[A] M') ≤
        Ideal.span {π} ^ n • ⊤ := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    exact h1 (Submodule.mem_map_of_mem hx)
  have hM' : ∀ (n : ℕ) (x : M'), x ∈ (Ideal.span {π} ^ n • ⊤ : Submodule A M') →
      e.symm x ∈ (Ideal.span {π} ^ n • ⊤ : Submodule A M) := by
    intro n x hx
    have h1 : (Ideal.span {π} ^ n • ⊤ : Submodule A M').map (e.symm : M' →ₗ[A] M) ≤
        Ideal.span {π} ^ n • ⊤ := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    exact h1 (Submodule.mem_map_of_mem hx)
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    have h0 : e.symm x = 0 := by
      refine h.toIsHausdorff.haus' (e.symm x) (fun n => ?_)
      rw [SModEq.sub_mem, sub_zero]
      have hx' := (SModEq.sub_mem).mp (hx n)
      rw [sub_zero] at hx'
      exact hM' n x hx'
    simpa using congrArg e h0
  · intro f hf
    obtain ⟨L, hL⟩ := h.toIsPrecomplete.prec' (fun n => e.symm (f n)) (fun {m n} hmn => by
      rw [SModEq.sub_mem, ← map_sub]
      exact hM' m _ ((SModEq.sub_mem).mp (hf hmn)))
    refine ⟨e L, fun n => ?_⟩
    rw [SModEq.sub_mem]
    have h2 := hM n _ ((SModEq.sub_mem).mp (hL n))
    rwa [map_sub, LinearEquiv.apply_symm_apply] at h2

/- English proof (translation)
Introduce `W _ _ _ l hl A _ _ hA L _ _ _`. Establish `hl0 : l ≠ 0`. Introduce and unpack `rfl`. Conclude with `hl.ne_zero Nat.cast_zero`. Choose the witnesses or unpack the hypotheses as in `⟨p, hpmem, hpu⟩ : ∃ p ∈ l.primeFactorsList, ¬IsUnit (p : W) := by`.

Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Apply `hl.1` to reduce the goal to its premises. Rewrite using `[← Nat.prod_primeFactorsList hl0, Nat.cast_list_prod]`. Use `List.prod_isUnit (fun m hm => ?_)` and prove the remaining obligations.

Take `⟨q, hq, rfl⟩` from `List.mem_map.mp hm`. Conclude with `hcon q hq`. Establish `hp : p.Prime` using `Nat.prime_of_mem_primeFactorsList hpmem`. Take `⟨m, hm⟩` from `Nat.dvd_of_mem_primeFactorsList hpmem`. Establish `hmu : IsUnit (m : W)`.

Establish `h` using `hl.isUnit_or_isUnit (show (l : W) = (p : W) * (m : W) by rw [hm, Nat.cast_mul])`. Conclude with `h.resolve_left hpu`. Establish `hmA : IsUnit (m : A)`. Establish `h` using `hmu.map (algebraMap W A)`. Rewrite `h` using `[map_natCast]`. Then use the resulting hypothesis.

Establish `hI : Ideal.span {(l : A)} = Ideal.span {(p : A)}`. Rewrite using `[hm, Nat.cast_mul, Ideal.span_singleton_mul_right_unit hmA]`. Establish `hp0 : (p : W) ≠ 0`. Introduce `h`. Apply `hl.ne_zero` to reduce the goal to its premises.

Rewrite using `[hm, Nat.cast_mul, h, zero_mul]`. Use `haveI : Fact p.Prime := ⟨hp⟩`. Use `haveI hA' : IsAdicComplete (Ideal.span {(p : A)}) A := by`. Rewrite using `[← hI]`. Conclude with `hA`.

Take `⟨n, f, hf⟩` from `Module.Finite.exists_fin' W L`. Establish `hN` using `isAdicComplete_tensor p W A hp0 hpu ((Fin n → W) ⧸ LinearMap.ker f)`. Rewrite using `[hI]`. Conclude with `isAdicComplete_of_linearEquiv_univ (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A A) (f.quotKerEquivOfSurjective hf)) hN`.
-/
theorem isAdicComplete_tensor_finite : ∀ (W : Type) [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] (l : ℕ), Irreducible (l : W) →
    ∀ (A : Type) [CommRing A] [Algebra W A] [IsAdicComplete (Ideal.span {(l : A)}) A]
      (L : Type 1) [AddCommGroup L] [Module W L] [Module.Finite W L],
      IsAdicComplete (Ideal.span {(l : A)}) (A ⊗[W] L) := by
  intro W _ _ _ l hl A _ _ hA L _ _ _
  have hl0 : l ≠ 0 := by
    rintro rfl
    exact hl.ne_zero Nat.cast_zero
  obtain ⟨p, hpmem, hpu⟩ : ∃ p ∈ l.primeFactorsList, ¬IsUnit (p : W) := by
    by_contra hcon
    push_neg at hcon
    apply hl.1
    rw [← Nat.prod_primeFactorsList hl0, Nat.cast_list_prod]
    refine List.prod_isUnit (fun m hm => ?_)
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
    exact hcon q hq
  have hp : p.Prime := Nat.prime_of_mem_primeFactorsList hpmem
  obtain ⟨m, hm⟩ := Nat.dvd_of_mem_primeFactorsList hpmem
  have hmu : IsUnit (m : W) := by
    have h := hl.isUnit_or_isUnit (show (l : W) = (p : W) * (m : W) by rw [hm, Nat.cast_mul])
    exact h.resolve_left hpu
  have hmA : IsUnit (m : A) := by
    have h := hmu.map (algebraMap W A)
    rwa [map_natCast] at h
  have hI : Ideal.span {(l : A)} = Ideal.span {(p : A)} := by
    rw [hm, Nat.cast_mul, Ideal.span_singleton_mul_right_unit hmA]
  have hp0 : (p : W) ≠ 0 := by
    intro h
    apply hl.ne_zero
    rw [hm, Nat.cast_mul, h, zero_mul]
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hA' : IsAdicComplete (Ideal.span {(p : A)}) A := by
    rw [← hI]
    exact hA
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' W L
  have hN := isAdicComplete_tensor p W A hp0 hpu ((Fin n → W) ⧸ LinearMap.ker f)
  rw [hI]
  exact isAdicComplete_of_linearEquiv_univ
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A A)
      (f.quotKerEquivOfSurjective hf)) hN

end GlobalTheory.CompanionTheory.TensorCompleteFinite
