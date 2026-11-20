import Mathlib
import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsLocalGenerator
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.ExistsLocalGenerator.exists_local_generator I p`.
-/
private lemma exists_local_generator {B : Type} [CommRing B] [IsDedekindDomain B]
    (I : Ideal B) (p : Ideal B) [hp : p.IsPrime] :
    ∃ π ∈ I, ∃ s, s ∉ p ∧ ∀ x ∈ I, s * x ∈ Ideal.span {π} :=
  _root_.UpperTheory.Reformulated.B.ExistsLocalGenerator.exists_local_generator I p

/- English proof (translation)
Introduce `B _ _ W`. Set `S : Set (PrimeSpectrum B)` to `((W : Set (Spec (CommRingCat.of B)))ᶜ : Set (Spec (CommRingCat.of B)))`. Establish `hS : IsClosed S` using `W.isOpen.isClosed_compl`. Set `I : Ideal B` to `PrimeSpectrum.vanishingIdeal S`. Establish `hWc : PrimeSpectrum.zeroLocus (I : Set B) = S`.

Rewrite using `[PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]`. Conclude with `hS.closure_eq`. Set `D : B → (Spec (CommRingCat.of B)).Opens` to `fun r => PrimeSpectrum.basicOpen (R := CommRingCat.of B) r`. Establish `hbasic : ∀ r : B, IsAffineOpen (D r)`. Introduce `r`.

Establish `h` using `(isAffineOpen_top (Spec (CommRingCat.of B))).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of B)).inv r)`. Rewrite `h` using `[basicOpen_eq_of_affine]`. Then use the resulting hypothesis. Establish `hmain : IsAffineHom W.ι`. Use `isAffineHom_of_forall_exists_isAffineOpen _ fun x => ?_` and prove the remaining obligations. Take `⟨π, hπ, s, hs, hsI⟩` from `@exists_local_generator B _ _ I x.asIdeal x.isPrime`.

Use `⟨D s, hs, hbasic s, ?_⟩` and prove the remaining obligations. Establish `hEq : W ⊓ D s = D (s * π)`. Use extensionality with `q`. Establish `hq : q ∈ W ↔ ¬ (I : Set B) ⊆ q.asIdeal`. Establish `h1 : (I : Set B) ⊆ q.asIdeal ↔ q ∉ W` using `Set.ext_iff.1 hWc q`.

Rewrite using `[h1, not_not]`. Establish `hDm : ∀ r : B, q ∈ D r ↔ r ∉ q.asIdeal` using `fun r => Iff.rfl`. Express the relevant statement in the definitionally equal form `q ∈ W ∧ q ∈ D s ↔ q ∈ D (s * π)`. Rewrite using `[hDm, hDm, hq]`. Establish `hqp : q.asIdeal.IsPrime` using `q.isPrime`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hIq, hsq⟩ hm`. Break down `hqp.mem_or_mem hm with h | h` into its components or cases. Conclude with `hsq h`. Use `hIq fun y hy => ?_` and prove the remaining obligations.

Establish `h2 : s * y ∈ q.asIdeal` using `(Ideal.span_singleton_le_iff_mem q.asIdeal).2 h (hsI y hy)`. Conclude with `(hqp.mem_or_mem h2).resolve_left hsq`. Introduce `hm`. Use `⟨fun hsub => hm (Ideal.mul_mem_left _ _ (hsub hπ)), fun h => hm (Ideal.mul_mem_right _ _ h)⟩` and prove the remaining obligations. Establish `h` using `hbasic (s * π)`.

Rewrite `h` using `[← hEq]`. Establish `h2` using `h.preimage_of_isOpenImmersion W.ι (by simp)`. Establish `e : W.ι ⁻¹ᵁ (W ⊓ D s) = W.ι ⁻¹ᵁ D s`. Use extensionality with `y`. Conclude with `⟨fun hy => hy.2, fun hy => ⟨y.2, hy⟩⟩`.

Rewrite `h2` using `[e]`. Then use the resulting hypothesis. Establish `: IsAffine W.toScheme` using `isAffine_of_isAffineHom W.ι`. Conclude with `this`.
-/
theorem UpperTheory.dedekind_spec_open_isAffine :
    ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (W : (Spec (CommRingCat.of B)).Opens), IsAffineOpen W := by
  intro B _ _ W
  let S : Set (PrimeSpectrum B) := ((W : Set (Spec (CommRingCat.of B)))ᶜ : Set (Spec (CommRingCat.of B)))
  have hS : IsClosed S := W.isOpen.isClosed_compl
  let I : Ideal B := PrimeSpectrum.vanishingIdeal S
  have hWc : PrimeSpectrum.zeroLocus (I : Set B) = S := by
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    exact hS.closure_eq
  let D : B → (Spec (CommRingCat.of B)).Opens := fun r =>
    PrimeSpectrum.basicOpen (R := CommRingCat.of B) r
  have hbasic : ∀ r : B, IsAffineOpen (D r) := by
    intro r
    have h := (isAffineOpen_top (Spec (CommRingCat.of B))).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv r)
    rwa [basicOpen_eq_of_affine] at h
  have hmain : IsAffineHom W.ι := by
    refine isAffineHom_of_forall_exists_isAffineOpen _ fun x => ?_
    obtain ⟨π, hπ, s, hs, hsI⟩ := @exists_local_generator B _ _ I x.asIdeal x.isPrime
    refine ⟨D s, hs, hbasic s, ?_⟩
    have hEq : W ⊓ D s = D (s * π) := by
      ext q
      have hq : q ∈ W ↔ ¬ (I : Set B) ⊆ q.asIdeal := by
        have h1 : (I : Set B) ⊆ q.asIdeal ↔ q ∉ W := Set.ext_iff.1 hWc q
        rw [h1, not_not]
      have hDm : ∀ r : B, q ∈ D r ↔ r ∉ q.asIdeal := fun r => Iff.rfl
      change q ∈ W ∧ q ∈ D s ↔ q ∈ D (s * π)
      rw [hDm, hDm, hq]
      have hqp : q.asIdeal.IsPrime := q.isPrime
      constructor
      · rintro ⟨hIq, hsq⟩ hm
        rcases hqp.mem_or_mem hm with h | h
        · exact hsq h
        · refine hIq fun y hy => ?_
          have h2 : s * y ∈ q.asIdeal :=
            (Ideal.span_singleton_le_iff_mem q.asIdeal).2 h (hsI y hy)
          exact (hqp.mem_or_mem h2).resolve_left hsq
      · intro hm
        refine ⟨fun hsub => hm (Ideal.mul_mem_left _ _ (hsub hπ)),
          fun h => hm (Ideal.mul_mem_right _ _ h)⟩
    have h := hbasic (s * π)
    rw [← hEq] at h
    have h2 := h.preimage_of_isOpenImmersion W.ι (by simp)
    have e : W.ι ⁻¹ᵁ (W ⊓ D s) = W.ι ⁻¹ᵁ D s := by
      ext y
      exact ⟨fun hy => hy.2, fun hy => ⟨y.2, hy⟩⟩
    rwa [e] at h2
  have : IsAffine W.toScheme := isAffine_of_isAffineHom W.ι
  exact this
