import Mathlib
open TensorProduct

namespace GlobalTheory

/- English proof (translation)
Use `choose F hF using h`. Use `⟨G.biUnion F, Submodule.span_le.2 fun y hy => ?_⟩` and prove the remaining obligations. Use `Submodule.span_mono (Set.image_mono ?_) (hF y)` and prove the remaining obligations. Introduce `n hn`. Simplify using `only [Finset.coe_biUnion, Set.mem_iUnion]`.

Conclude with `⟨y, hy, hn⟩`.
-/
theorem exists_finset_span_ge_of_forall_mem_span_image {R M N : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (g : N → M) (G : Finset M) (h : ∀ y : M, ∃ S : Finset N, y ∈ Submodule.span R (g '' (S : Set N))) :
    ∃ S : Finset N, Submodule.span R (G : Set M) ≤ Submodule.span R (g '' (S : Set N)) := by
  classical
  choose F hF using h
  refine ⟨G.biUnion F, Submodule.span_le.2 fun y hy => ?_⟩
  refine Submodule.span_mono (Set.image_mono ?_) (hF y)
  intro n hn
  simp only [Finset.coe_biUnion, Set.mem_iUnion]
  exact ⟨y, hy, hn⟩

/- English proof (translation)
Use `set Ahat := AdicCompletion (Ideal.span {f}) A`. Take `⟨G1, hG1⟩` from `hloc.fg_top`. Take `⟨S1, hS1⟩` from `exists_finset_span_ge_of_forall_mem_span_image (R := Localization.Away f) (fun n : N => LocalizedModule.mk n (1 : Submonoid.powers f)) G1 (by`. Introduce `y`. Proceed by induction on `y using LocalizedModule.induction_on with`.

Consider the case `h m s`. Use `⟨{m}, ?_⟩` and prove the remaining obligations. Establish `: LocalizedModule.mk m s = (Localization.mk 1 s : Localization.Away f) • LocalizedModule.mk m (1 : Submonoid.powers f)`. Rewrite using `[LocalizedModule.mk_smul_mk, one_smul, mul_one]`. Rewrite using `[this]`.

Use `Submodule.smul_mem _ _ (Submodule.subset_span ?_)` and prove the remaining obligations. Use the proof step `simp)`. Take `⟨G2, hG2⟩` from `hcomp.fg_top`. Take `⟨S2, hS2⟩` from `exists_finset_span_ge_of_forall_mem_span_image (R := Ahat) (fun n : N => (1 : Ahat) ⊗ₜ[A] n) G2 (by`. Introduce `y`.

Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨∅, Submodule.zero_mem _⟩`. Consider the case `tmul a n`. Use `⟨{n}, ?_⟩` and prove the remaining obligations. Establish `: a ⊗ₜ[A] n = a • ((1 : Ahat) ⊗ₜ[A] n)`.

Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Rewrite using `[this]`. Use `Submodule.smul_mem _ _ (Submodule.subset_span ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules. Consider the case `add x y hx hy`.

Take `⟨Sx, hx⟩` from `hx`. Take `⟨Sy, hy⟩` from `hy`. Use `⟨Sx ∪ Sy, Submodule.add_mem _ ?_ ?_⟩` and prove the remaining obligations. Conclude with `Submodule.span_mono (Set.image_mono (by simp)) hx`. Conclude with `Submodule.span_mono (Set.image_mono (by simp)) hy)`.

Use `set S := S1 ∪ S2`. Use `set N' : Submodule A N := Submodule.span A (S : Set N)`. Establish `hSN' : ∀ n ∈ S, N'.mkQ n = 0` using `fun n hn => by`. Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `Submodule.subset_span hn`.

Establish `htorQ : ∀ q : N ⧸ N', ∃ k : ℕ, f ^ k • q = 0` using `by set Φ := LocalizedModule.map (Submonoid.powers f) N'.mkQ`. Establish `hker : ∀ x, Φ x = 0`. Introduce `x`. Establish `hx : x ∈ Submodule.span (Localization.Away f) (G1 : Set _)` using `by rw [hG1]; trivial`. Establish `hle : Submodule.span (Localization.Away f) ((fun n : N => LocalizedModule.mk n (1 : Submonoid.powers f)) '' (S1 : Set N)) ≤ LinearMap.ker Φ`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨n, hn, rfl⟩`. Simplify using `only [SetLike.mem_coe, LinearMap.mem_ker, Φ, LocalizedModule.map_mk]`. Rewrite using `[hSN' n (Finset.mem_union_left _ hn), LocalizedModule.zero_mk]`. Conclude with `hle (hS1 hx)`.

Introduce `q`. Take `⟨n, rfl⟩` from `N'.mkQ_surjective q`. Establish `h0` using `hker (LocalizedModule.mk n 1)`. Rewrite `h0` using `[LocalizedModule.map_mk, ← LocalizedModule.zero_mk (1 : Submonoid.powers f), LocalizedModule.mk_eq]`. Take `⟨⟨u, k, rfl⟩, hu⟩` from `h0`.

Use `⟨k, ?_⟩` and prove the remaining obligations. Simplify `hu` using `[Submonoid.smul_def]`. Establish `hsub : Subsingleton (TensorProduct A Ahat (N ⧸ N'))` using `by set Ψ := LinearMap.baseChange Ahat N'.mkQ`. Establish `hker : ∀ x, Ψ x = 0`. Introduce `x`.

Establish `hx : x ∈ Submodule.span Ahat (G2 : Set _)` using `by rw [hG2]; trivial`. Establish `hle : Submodule.span Ahat ((fun n : N => (1 : Ahat) ⊗ₜ[A] n) '' (S2 : Set N)) ≤ LinearMap.ker Ψ`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨n, hn, rfl⟩`. Simplify using `only [SetLike.mem_coe, LinearMap.mem_ker, Ψ, LinearMap.baseChange_tmul]`.

Rewrite using `[hSN' n (Finset.mem_union_right _ hn), TensorProduct.tmul_zero]`. Conclude with `hle (hS2 hx)`. Establish `hsurj : Function.Surjective (N'.mkQ.lTensor Ahat)` using `LinearMap.lTensor_surjective Ahat N'.mkQ_surjective`. Use `subsingleton_of_forall_eq 0 fun z => ?_` and prove the remaining obligations. Take `⟨y, rfl⟩` from `hsurj z`.

Conclude with `hker y`. Establish `hQ` using `htor (N ⧸ N') htorQ hsub`. Establish `htop : N' = ⊤`. Conclude with `Submodule.Quotient.subsingleton_iff.1 hQ`. Conclude with `⟨⟨S, htop⟩⟩`.
-/
theorem module_finite_of_localization_of_completion (A : Type) [CommRing A] (f : A)
    (htor : ∀ (Q : Type) [AddCommGroup Q] [Module A Q], (∀ q : Q, ∃ k : ℕ, f ^ k • q = 0) →
      Subsingleton (TensorProduct A (AdicCompletion (Ideal.span {f}) A) Q) → Subsingleton Q)
    (N : Type) [AddCommGroup N] [Module A N]
    (hloc : Module.Finite (Localization.Away f) (LocalizedModule (Submonoid.powers f) N))
    (hcomp : Module.Finite (AdicCompletion (Ideal.span {f}) A)
      (TensorProduct A (AdicCompletion (Ideal.span {f}) A) N)) :
    Module.Finite A N := by
  classical
  set Ahat := AdicCompletion (Ideal.span {f}) A

  obtain ⟨G1, hG1⟩ := hloc.fg_top
  obtain ⟨S1, hS1⟩ := exists_finset_span_ge_of_forall_mem_span_image (R := Localization.Away f)
    (fun n : N => LocalizedModule.mk n (1 : Submonoid.powers f)) G1 (by
      intro y
      induction y using LocalizedModule.induction_on with
      | h m s =>
        refine ⟨{m}, ?_⟩
        have : LocalizedModule.mk m s = (Localization.mk 1 s : Localization.Away f) •
            LocalizedModule.mk m (1 : Submonoid.powers f) := by
          rw [LocalizedModule.mk_smul_mk, one_smul, mul_one]
        rw [this]
        refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
        simp)

  obtain ⟨G2, hG2⟩ := hcomp.fg_top
  obtain ⟨S2, hS2⟩ := exists_finset_span_ge_of_forall_mem_span_image (R := Ahat)
    (fun n : N => (1 : Ahat) ⊗ₜ[A] n) G2 (by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => exact ⟨∅, Submodule.zero_mem _⟩
      | tmul a n =>
        refine ⟨{n}, ?_⟩
        have : a ⊗ₜ[A] n = a • ((1 : Ahat) ⊗ₜ[A] n) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [this]
        refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
        simp
      | add x y hx hy =>
        obtain ⟨Sx, hx⟩ := hx
        obtain ⟨Sy, hy⟩ := hy
        refine ⟨Sx ∪ Sy, Submodule.add_mem _ ?_ ?_⟩
        · exact Submodule.span_mono (Set.image_mono (by simp)) hx
        · exact Submodule.span_mono (Set.image_mono (by simp)) hy)
  set S := S1 ∪ S2
  set N' : Submodule A N := Submodule.span A (S : Set N)
  have hSN' : ∀ n ∈ S, N'.mkQ n = 0 := fun n hn => by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span hn

  have htorQ : ∀ q : N ⧸ N', ∃ k : ℕ, f ^ k • q = 0 := by
    set Φ := LocalizedModule.map (Submonoid.powers f) N'.mkQ
    have hker : ∀ x, Φ x = 0 := by
      intro x
      have hx : x ∈ Submodule.span (Localization.Away f) (G1 : Set _) := by rw [hG1]; trivial
      have hle : Submodule.span (Localization.Away f)
          ((fun n : N => LocalizedModule.mk n (1 : Submonoid.powers f)) '' (S1 : Set N)) ≤
          LinearMap.ker Φ := by
        rw [Submodule.span_le]
        rintro _ ⟨n, hn, rfl⟩
        simp only [SetLike.mem_coe, LinearMap.mem_ker, Φ, LocalizedModule.map_mk]
        rw [hSN' n (Finset.mem_union_left _ hn), LocalizedModule.zero_mk]
      exact hle (hS1 hx)
    intro q
    obtain ⟨n, rfl⟩ := N'.mkQ_surjective q
    have h0 := hker (LocalizedModule.mk n 1)
    rw [LocalizedModule.map_mk, ← LocalizedModule.zero_mk (1 : Submonoid.powers f),
      LocalizedModule.mk_eq] at h0
    obtain ⟨⟨u, k, rfl⟩, hu⟩ := h0
    refine ⟨k, ?_⟩
    simpa [Submonoid.smul_def] using hu

  have hsub : Subsingleton (TensorProduct A Ahat (N ⧸ N')) := by
    set Ψ := LinearMap.baseChange Ahat N'.mkQ
    have hker : ∀ x, Ψ x = 0 := by
      intro x
      have hx : x ∈ Submodule.span Ahat (G2 : Set _) := by rw [hG2]; trivial
      have hle : Submodule.span Ahat
          ((fun n : N => (1 : Ahat) ⊗ₜ[A] n) '' (S2 : Set N)) ≤ LinearMap.ker Ψ := by
        rw [Submodule.span_le]
        rintro _ ⟨n, hn, rfl⟩
        simp only [SetLike.mem_coe, LinearMap.mem_ker, Ψ, LinearMap.baseChange_tmul]
        rw [hSN' n (Finset.mem_union_right _ hn), TensorProduct.tmul_zero]
      exact hle (hS2 hx)
    have hsurj : Function.Surjective (N'.mkQ.lTensor Ahat) :=
      LinearMap.lTensor_surjective Ahat N'.mkQ_surjective
    refine subsingleton_of_forall_eq 0 fun z => ?_
    obtain ⟨y, rfl⟩ := hsurj z
    exact hker y
  have hQ := htor (N ⧸ N') htorQ hsub
  have htop : N' = ⊤ := by
    exact Submodule.Quotient.subsingleton_iff.1 hQ
  exact ⟨⟨S, htop⟩⟩

end GlobalTheory
