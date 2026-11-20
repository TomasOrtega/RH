import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsInvOpenInsideRat
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

/- English proof (translation)
Use `⟨fun U => ?_⟩` and prove the remaining obligations. Establish `hZ : IsNoetherianRing Γ(SpecZ, ⊤)` using `IsLocallyNoetherian.component_noetherian (X := SpecZ) ⟨⊤, isAffineOpen_top _⟩`. Establish `e : (U : X.Opens) ≤ f ⁻¹ᵁ ⊤` using `by simp`. Establish `hφ` using `HasRingHomProperty.appLE @LocallyOfFiniteType f ‹_› ⟨⊤, isAffineOpen_top _⟩ U e`. Set `_` to `(f.appLE ⊤ U.1 e).hom.toAlgebra`.

Establish `: Algebra.FiniteType Γ(SpecZ, ⊤) Γ(X, U)` using `hφ`. Conclude with `Algebra.FiniteType.isNoetherianRing Γ(SpecZ, ⊤) Γ(X, U)`.
-/
theorem isLocallyNoetherian_of_locallyOfFiniteType_specZ {X : Scheme.{0}} (f : X ⟶ SpecZ)
    [LocallyOfFiniteType f] : IsLocallyNoetherian X := by
  refine ⟨fun U => ?_⟩
  have hZ : IsNoetherianRing Γ(SpecZ, ⊤) :=
    IsLocallyNoetherian.component_noetherian (X := SpecZ) ⟨⊤, isAffineOpen_top _⟩
  have e : (U : X.Opens) ≤ f ⁻¹ᵁ ⊤ := by simp
  have hφ := HasRingHomProperty.appLE @LocallyOfFiniteType f ‹_› ⟨⊤, isAffineOpen_top _⟩ U e
  let _ := (f.appLE ⊤ U.1 e).hom.toAlgebra
  have : Algebra.FiniteType Γ(SpecZ, ⊤) Γ(X, U) := hφ
  exact Algebra.FiniteType.isNoetherianRing Γ(SpecZ, ⊤) Γ(X, U)

/- English proof (translation)
Set `y : Spec (CommRingCat.of ℚ)` to `⟨⊥, Ideal.isPrime_bot⟩`. Establish `h : f.base x = (Spec.map (CommRingCat.ofHom (Int.castRingHom ℚ))).base y`. Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Rewrite using `[hx]`. Express the relevant statement in the definitionally equal form `⊥ = Ideal.comap (Int.castRingHom ℚ) ⊥`.

Conclude with `(Ideal.comap_bot_of_injective _ (Int.cast_injective (α := ℚ))).symm`. Take `⟨z, hz, -⟩` from `Scheme.Pullback.exists_preimage_pullback x y h`. Conclude with `⟨z, hz⟩`.
-/
theorem mem_range_baseChangeMap_rat_of_asIdeal_eq_bot {X : Scheme.{0}} (f : X ⟶ SpecZ) (x : X)
    (hx : (f.base x).asIdeal = ⊥) : x ∈ Set.range (baseChangeMap f ℚ) := by
  let y : Spec (CommRingCat.of ℚ) := ⟨⊥, Ideal.isPrime_bot⟩
  have h : f.base x = (Spec.map (CommRingCat.ofHom (Int.castRingHom ℚ))).base y := by
    apply PrimeSpectrum.ext
    rw [hx]
    change ⊥ = Ideal.comap (Int.castRingHom ℚ) ⊥
    exact (Ideal.comap_bot_of_injective _ (Int.cast_injective (α := ℚ))).symm
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x y h
  exact ⟨z, hz⟩

/- English proof (translation)
Introduce `X f _ _ W hW`. Establish `: CompactSpace X` using `QuasiCompact.compactSpace_of_compactSpace f`. Use `isLocallyNoetherian_of_locallyOfFiniteType_specZ f` as an intermediate fact. Establish `: IsNoetherian X` using `{}`. Establish `hgen : ∀ x : X, x ∉ W → (f.base x).asIdeal ≠ ⊥`.

Introduce `x hx h`. Establish `h1` using `hW (mem_range_baseChangeMap_rat_of_asIdeal_eq_bot f x h)`. Rewrite `h1` using `[Scheme.Opens.range_ι]`. Conclude with `hx h1`. Take `⟨S, hSi, hS⟩` from `NoetherianSpace.exists_finset_irreducible (⟨(W : Set X)ᶜ, W.isOpen.isClosed_compl⟩ : Closeds X)`.

Establish `hSZ : ∀ k ∈ S, (k : Set X) ⊆ (W : Set X)ᶜ`. Introduce `k hk`. Establish `h1 : k ≤ S.sup id` using `Finset.le_sup (f := id) hk`. Rewrite `h1` using `[← hS]`. Conclude with `h1`.

Establish `claim : ∀ k ∈ S, ∃ n : ℕ, 0 < n ∧ ∀ x ∈ (k : Set X), (n : ℤ) ∈ (f.base x).asIdeal`. Introduce `k hk`. Establish `hirr : IsIrreducible (k : Set X)` using `hSi ⟨k, hk⟩`. Establish `hg : IsGenericPoint hirr.genericPoint (k : Set X)` using `hirr.isGenericPoint_genericPoint k.isClosed`. Take `⟨n, hn, hn0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot (hgen _ (hSZ k hk hg.mem))`.

Use `⟨n.natAbs, Int.natAbs_pos.mpr hn0, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hle : (f.base hirr.genericPoint).asIdeal ≤ (f.base x).asIdeal` using `(PrimeSpectrum.le_iff_specializes _ _).mpr ((hg.specializes hx).map f.base.hom.continuous)`. Conclude with `Ideal.mem_of_dvd _ (Int.dvd_natAbs.mpr dvd_rfl) (hle hn)`. Use `choose! n hn using claim`. Use `⟨∏ k ∈ S, n k, Finset.prod_pos fun k hk => (hn k hk).1, ?_⟩` and prove the remaining obligations.

Introduce `x hx`. Assume the negation of the conclusion as `hxW`. Establish `hxS : x ∈ ((S.sup id : Closeds X) : Set X)` using `by rw [← hS]; exact hxW`. Rewrite `hxS` using `[Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion, Set.mem_iUnion₂]`. Take `⟨k, hk, hxk⟩` from `hxS`.

Apply `(mem_invOpen f _ x).mp hx` to reduce the goal to its premises. Establish `hdvd : ((n k : ℕ) : ℤ) ∣ ((∏ k ∈ S, n k : ℕ) : ℤ)` using `Int.natCast_dvd_natCast.mpr (Finset.dvd_prod_of_mem n hk)`. Conclude with `Ideal.mem_of_dvd _ hdvd ((hn k hk).2 x hxk)`.
-/
theorem InvOpenInsideRat.proof : InvOpenInsideRat.Statement := by
  intro X f _ _ W hW
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have := isLocallyNoetherian_of_locallyOfFiniteType_specZ f
  have : IsNoetherian X := {}

  have hgen : ∀ x : X, x ∉ W → (f.base x).asIdeal ≠ ⊥ := by
    intro x hx h
    have h1 := hW (mem_range_baseChangeMap_rat_of_asIdeal_eq_bot f x h)
    rw [Scheme.Opens.range_ι] at h1
    exact hx h1
  obtain ⟨S, hSi, hS⟩ := NoetherianSpace.exists_finset_irreducible
    (⟨(W : Set X)ᶜ, W.isOpen.isClosed_compl⟩ : Closeds X)
  have hSZ : ∀ k ∈ S, (k : Set X) ⊆ (W : Set X)ᶜ := by
    intro k hk
    have h1 : k ≤ S.sup id := Finset.le_sup (f := id) hk
    rw [← hS] at h1
    exact h1
  have claim : ∀ k ∈ S, ∃ n : ℕ, 0 < n ∧ ∀ x ∈ (k : Set X), (n : ℤ) ∈ (f.base x).asIdeal := by
    intro k hk
    have hirr : IsIrreducible (k : Set X) := hSi ⟨k, hk⟩
    have hg : IsGenericPoint hirr.genericPoint (k : Set X) :=
      hirr.isGenericPoint_genericPoint k.isClosed
    obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (hgen _ (hSZ k hk hg.mem))
    refine ⟨n.natAbs, Int.natAbs_pos.mpr hn0, fun x hx => ?_⟩
    have hle : (f.base hirr.genericPoint).asIdeal ≤ (f.base x).asIdeal :=
      (PrimeSpectrum.le_iff_specializes _ _).mpr ((hg.specializes hx).map f.base.hom.continuous)
    exact Ideal.mem_of_dvd _ (Int.dvd_natAbs.mpr dvd_rfl) (hle hn)
  choose! n hn using claim
  refine ⟨∏ k ∈ S, n k, Finset.prod_pos fun k hk => (hn k hk).1, ?_⟩
  intro x hx
  by_contra hxW
  have hxS : x ∈ ((S.sup id : Closeds X) : Set X) := by rw [← hS]; exact hxW
  rw [Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion, Set.mem_iUnion₂] at hxS
  obtain ⟨k, hk, hxk⟩ := hxS
  apply (mem_invOpen f _ x).mp hx
  have hdvd : ((n k : ℕ) : ℤ) ∣ ((∏ k ∈ S, n k : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Finset.dvd_prod_of_mem n hk)
  exact Ideal.mem_of_dvd _ hdvd ((hn k hk).2 x hxk)

end

end GroundTheory.Heights₂.Heights.Model
