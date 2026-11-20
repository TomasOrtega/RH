import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TopNilDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TnIdem

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

/- English proof (translation)
Introduce `R _ _ _ _ κ M _ _ _ T hT`. Take `⟨e, he, hid, hr⟩` from `UpperTheory.V.AlgebraTools.exists_idem_topNil R κ M T hT`. Establish `hee : ∀ x, e (e x) = e x` using `fun x => by`. Establish `h` using `congrArg (fun f : Module.End R M => f x) hid.eq`. Simplify using `using h`.

Establish `hfix : ∀ x ∈ topNil (IsLocalRing.maximalIdeal R) T, e x = x`. Rewrite using `[← hr]`. Introduce and unpack `_ ⟨y, rfl⟩`. Conclude with `hee y`. Establish `hmem : ∀ x, e x ∈ topNil (IsLocalRing.maximalIdeal R) T` using `fun x => by`.

Rewrite using `[← hr]`. Conclude with `⟨x, rfl⟩`. Establish `hcomm : ∀ φ : Module.End R M, (∀ i, Commute φ (T i)) → ∀ x, φ (e x) = e (φ x)`. Introduce `φ hφ x`. Establish `h : Commute φ e`.

Use `Algebra.commute_of_mem_adjoin_of_forall_mem_commute he ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `hφ i`. Establish `h2` using `congrArg (fun f : Module.End R M => f x) h.eq`. Simplify using `using h2`.

Establish `hstab : ∀ φ : Module.End R M, (∀ i, Commute φ (T i)) → ∀ x ∈ topNil (IsLocalRing.maximalIdeal R) T, φ x ∈ topNil (IsLocalRing.maximalIdeal R) T`. Introduce `φ hφ x hx`. Rewrite using `[← hfix x hx, hcomm φ hφ]`. Conclude with `hmem _`. Establish `hI : ∀ I : Ideal R, (I • ⊤ : Submodule R M) ⊓ topNil (IsLocalRing.maximalIdeal R) T = I • topNil (IsLocalRing.maximalIdeal R) T`.

Introduce `I`. Use `le_antisymm ?_ (le_inf (Submodule.smul_mono le_rfl le_top) Submodule.smul_le_right)` and prove the remaining obligations. Introduce and unpack `x ⟨hx1, hx2⟩`. Establish `h1 : e x ∈ Submodule.map e (I • ⊤ : Submodule R M)` using `⟨x, hx1, rfl⟩`. Rewrite `h1` using `[Submodule.map_smul'', Submodule.map_top, hr, hfix x hx2]`.

Conclude with `h1`. Use `⟨⟨LinearMap.ker e, ?_, fun φ hφ => ⟨hstab φ hφ, ?_⟩⟩, hI, ?_, ?_⟩` and prove the remaining obligations. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.disjoint_def]`. Introduce `x hx hk`.

Rewrite using `[← hfix x hx]`. Conclude with `hk`. Rewrite using `[codisjoint_iff, eq_top_iff]`. Introduce `x _`. Use `Submodule.mem_sup.2 ⟨e x, hmem x, x - e x, ?_, by abel⟩` and prove the remaining obligations.

Rewrite using `[LinearMap.mem_ker, map_sub, hee, sub_self]`. Introduce `x hx`. Rewrite `hx`, the goal using `[LinearMap.mem_ker]`. Rewrite using `[← hcomm φ hφ, hx, map_zero]`. Introduce `i`.

Take `⟨S, hS⟩` from `IsNoetherian.noetherian (topNil (IsLocalRing.maximalIdeal R) T)`. Establish `hev : ∀ᶠ r : ℕ in atTop, ∀ x ∈ S, (T i ^ r) x ∈ ((IsLocalRing.maximalIdeal R) ^ 1 • ⊤ : Submodule R M)`. Rewrite using `[Filter.eventually_all_finset]`. Introduce `x hx`. Establish `hx' : x ∈ topNil (IsLocalRing.maximalIdeal R) T` using `hS ▸ Submodule.subset_span hx`.

Conclude with `mem_topNil.1 hx' i 1`. Take `⟨r, hr'⟩` from `hev.exists`. Use `⟨r, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[← hI]`. Use `⟨?_, hstab _ (fun j => (hT i j).pow_left r) x hx⟩` and prove the remaining obligations.

Establish `hle : Submodule.span R (S : Set M) ≤ Submodule.comap (T i ^ r) ((IsLocalRing.maximalIdeal R) • ⊤ : Submodule R M)`. Rewrite using `[Submodule.span_le]`. Introduce `y hy`. Establish `h` using `hr' y hy`. Rewrite `h` using `[pow_one]`.

Conclude with `h`. Rewrite `hle` using `[hS]`. Conclude with `hle hx`. Introduce `hF`. Use `⟨?_, Submodule.finrank_le _⟩` and prove the remaining obligations.

Establish `hP : Module.Projective R (topNil (IsLocalRing.maximalIdeal R) T)` using `Module.Projective.of_split (topNil (IsLocalRing.maximalIdeal R) T).subtype (LinearMap.codRestrict _ e hmem) (by`. Use extensionality with `x`. Simplify using `using hfix x.1 x.2)`. Conclude with `Module.free_of_flat_of_isLocalRing`.
-/
theorem UpperTheory.V.AlgebraTools.topNil_free :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (κ : Type) (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] (T : κ → Module.End R M), (∀ i j, Commute (T i) (T j)) →
      (∃ C : Submodule R M, IsCompl (topNil (IsLocalRing.maximalIdeal R) T) C ∧ ∀ φ : Module.End R M, (∀ i, Commute φ (T i)) →
        (∀ x ∈ topNil (IsLocalRing.maximalIdeal R) T, φ x ∈ topNil (IsLocalRing.maximalIdeal R) T) ∧ ∀ x ∈ C, φ x ∈ C) ∧
      (∀ I : Ideal R, (I • ⊤ : Submodule R M) ⊓ topNil (IsLocalRing.maximalIdeal R) T = I • topNil (IsLocalRing.maximalIdeal R) T) ∧
      (∀ i, ∃ r : ℕ, ∀ x ∈ topNil (IsLocalRing.maximalIdeal R) T, (T i ^ r) x ∈ (IsLocalRing.maximalIdeal R) • topNil (IsLocalRing.maximalIdeal R) T) ∧
      (Module.Free R M → Module.Free R (topNil (IsLocalRing.maximalIdeal R) T) ∧ Module.finrank R (topNil (IsLocalRing.maximalIdeal R) T) ≤ Module.finrank R M) := by
  intro R _ _ _ _ κ M _ _ _ T hT
  obtain ⟨e, he, hid, hr⟩ := UpperTheory.V.AlgebraTools.exists_idem_topNil R κ M T hT
  have hee : ∀ x, e (e x) = e x := fun x => by
    have h := congrArg (fun f : Module.End R M => f x) hid.eq
    simpa using h
  have hfix : ∀ x ∈ topNil (IsLocalRing.maximalIdeal R) T, e x = x := by
    rw [← hr]
    rintro _ ⟨y, rfl⟩
    exact hee y
  have hmem : ∀ x, e x ∈ topNil (IsLocalRing.maximalIdeal R) T := fun x => by
    rw [← hr]; exact ⟨x, rfl⟩
  have hcomm : ∀ φ : Module.End R M, (∀ i, Commute φ (T i)) → ∀ x, φ (e x) = e (φ x) := by
    intro φ hφ x
    have h : Commute φ e := by
      refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute he ?_
      rintro _ ⟨i, rfl⟩
      exact hφ i
    have h2 := congrArg (fun f : Module.End R M => f x) h.eq
    simpa using h2
  have hstab : ∀ φ : Module.End R M, (∀ i, Commute φ (T i)) →
      ∀ x ∈ topNil (IsLocalRing.maximalIdeal R) T, φ x ∈ topNil (IsLocalRing.maximalIdeal R) T := by
    intro φ hφ x hx
    rw [← hfix x hx, hcomm φ hφ]
    exact hmem _
  have hI : ∀ I : Ideal R, (I • ⊤ : Submodule R M) ⊓ topNil (IsLocalRing.maximalIdeal R) T =
      I • topNil (IsLocalRing.maximalIdeal R) T := by
    intro I
    refine le_antisymm ?_ (le_inf (Submodule.smul_mono le_rfl le_top) Submodule.smul_le_right)
    rintro x ⟨hx1, hx2⟩
    have h1 : e x ∈ Submodule.map e (I • ⊤ : Submodule R M) := ⟨x, hx1, rfl⟩
    rw [Submodule.map_smul'', Submodule.map_top, hr, hfix x hx2] at h1
    exact h1
  refine ⟨⟨LinearMap.ker e, ?_, fun φ hφ => ⟨hstab φ hφ, ?_⟩⟩, hI, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · rw [Submodule.disjoint_def]
      intro x hx hk
      rw [← hfix x hx]
      exact hk
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      refine Submodule.mem_sup.2 ⟨e x, hmem x, x - e x, ?_, by abel⟩
      rw [LinearMap.mem_ker, map_sub, hee, sub_self]
  · intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← hcomm φ hφ, hx, map_zero]
  · intro i
    obtain ⟨S, hS⟩ := IsNoetherian.noetherian (topNil (IsLocalRing.maximalIdeal R) T)
    have hev : ∀ᶠ r : ℕ in atTop, ∀ x ∈ S,
        (T i ^ r) x ∈ ((IsLocalRing.maximalIdeal R) ^ 1 • ⊤ : Submodule R M) := by
      rw [Filter.eventually_all_finset]
      intro x hx
      have hx' : x ∈ topNil (IsLocalRing.maximalIdeal R) T := hS ▸ Submodule.subset_span hx
      exact mem_topNil.1 hx' i 1
    obtain ⟨r, hr'⟩ := hev.exists
    refine ⟨r, fun x hx => ?_⟩
    rw [← hI]
    refine ⟨?_, hstab _ (fun j => (hT i j).pow_left r) x hx⟩
    have hle : Submodule.span R (S : Set M) ≤
        Submodule.comap (T i ^ r) ((IsLocalRing.maximalIdeal R) • ⊤ : Submodule R M) := by
      rw [Submodule.span_le]
      intro y hy
      have h := hr' y hy
      rw [pow_one] at h
      exact h
    rw [hS] at hle
    exact hle hx
  · intro hF
    refine ⟨?_, Submodule.finrank_le _⟩
    have hP : Module.Projective R (topNil (IsLocalRing.maximalIdeal R) T) :=
      Module.Projective.of_split (topNil (IsLocalRing.maximalIdeal R) T).subtype
        (LinearMap.codRestrict _ e hmem) (by
          ext x
          simpa using hfix x.1 x.2)
    exact Module.free_of_flat_of_isLocalRing
