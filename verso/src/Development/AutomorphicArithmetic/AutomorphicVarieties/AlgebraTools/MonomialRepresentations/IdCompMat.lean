import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.IdComp

open Polynomial Matrix

private noncomputable def UpperTheory.V.AlgebraTools.icmPt {K ι : Type} [Field K] (A : Matrix ι ι K) :
    PrimeSpectrum (MvPolynomial (ι × ι) K) :=
  ⟨RingHom.ker (MvPolynomial.eval (fun p : ι × ι => A p.1 p.2)), RingHom.ker_isPrime _⟩

/- English proof (translation)
Use `⟨(MvPolynomial.aeval fun p : ι × ι => ∑ k, MvPolynomial.C (A p.1 k) * MvPolynomial.X (k, p.2)).toRingHom, fun B => ?_⟩` and prove the remaining obligations. Establish `key : (MvPolynomial.eval fun p : ι × ι => (A * B) p.1 p.2) = (MvPolynomial.eval fun p : ι × ι => B p.1 p.2).comp (MvPolynomial.aeval fun p : ι × ι => ∑ k, MvPolynomial.C (A p.1 k) * MvPolynomial.X (k, p.2)).toRingHom`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`. Simplify using the standard rewrite rules.

Introduce `p`. Simplify using `[Matrix.mul_apply]`. Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Use `show RingHom.ker _ = Ideal.comap _ (RingHom.ker _)`. Rewrite using `[key, RingHom.comap_ker]`.
-/
private theorem UpperTheory.V.AlgebraTools.icmPt_left {K ι : Type} [Field K] [Fintype ι] (A : Matrix ι ι K) :
    ∃ ψ : MvPolynomial (ι × ι) K →+* MvPolynomial (ι × ι) K, ∀ B : Matrix ι ι K,
      UpperTheory.V.AlgebraTools.icmPt (A * B) = PrimeSpectrum.comap ψ (UpperTheory.V.AlgebraTools.icmPt B) := by
  refine ⟨(MvPolynomial.aeval fun p : ι × ι =>
    ∑ k, MvPolynomial.C (A p.1 k) * MvPolynomial.X (k, p.2)).toRingHom, fun B => ?_⟩
  have key : (MvPolynomial.eval fun p : ι × ι => (A * B) p.1 p.2) =
      (MvPolynomial.eval fun p : ι × ι => B p.1 p.2).comp
        (MvPolynomial.aeval fun p : ι × ι =>
          ∑ k, MvPolynomial.C (A p.1 k) * MvPolynomial.X (k, p.2)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro p
      simp [Matrix.mul_apply]
  apply PrimeSpectrum.ext
  show RingHom.ker _ = Ideal.comap _ (RingHom.ker _)
  rw [key, RingHom.comap_ker]

/- English proof (translation)
Use `⟨(MvPolynomial.aeval fun p : ι × ι => ∑ k, MvPolynomial.X (p.1, k) * MvPolynomial.C (A k p.2)).toRingHom, fun B => ?_⟩` and prove the remaining obligations. Establish `key : (MvPolynomial.eval fun p : ι × ι => (B * A) p.1 p.2) = (MvPolynomial.eval fun p : ι × ι => B p.1 p.2).comp (MvPolynomial.aeval fun p : ι × ι => ∑ k, MvPolynomial.X (p.1, k) * MvPolynomial.C (A k p.2)).toRingHom`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`. Simplify using the standard rewrite rules.

Introduce `p`. Simplify using `[Matrix.mul_apply]`. Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Use `show RingHom.ker _ = Ideal.comap _ (RingHom.ker _)`. Rewrite using `[key, RingHom.comap_ker]`.
-/
private theorem UpperTheory.V.AlgebraTools.icmPt_right {K ι : Type} [Field K] [Fintype ι] (A : Matrix ι ι K) :
    ∃ ψ : MvPolynomial (ι × ι) K →+* MvPolynomial (ι × ι) K, ∀ B : Matrix ι ι K,
      UpperTheory.V.AlgebraTools.icmPt (B * A) = PrimeSpectrum.comap ψ (UpperTheory.V.AlgebraTools.icmPt B) := by
  refine ⟨(MvPolynomial.aeval fun p : ι × ι =>
    ∑ k, MvPolynomial.X (p.1, k) * MvPolynomial.C (A k p.2)).toRingHom, fun B => ?_⟩
  have key : (MvPolynomial.eval fun p : ι × ι => (B * A) p.1 p.2) =
      (MvPolynomial.eval fun p : ι × ι => B p.1 p.2).comp
        (MvPolynomial.aeval fun p : ι × ι =>
          ∑ k, MvPolynomial.X (p.1, k) * MvPolynomial.C (A k p.2)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro p
      simp [Matrix.mul_apply]
  apply PrimeSpectrum.ext
  show RingHom.ker _ = Ideal.comap _ (RingHom.ker _)
  rw [key, RingHom.comap_ker]

/- English proof (translation)
Introduce `K G ι _ _ _ _ r`. Set `f : G → PrimeSpectrum (MvPolynomial (ι × ι) K)` to `fun g => UpperTheory.V.AlgebraTools.icmPt (r g)`. Use `letI tG : TopologicalSpace G := TopologicalSpace.induced f inferInstance`. Establish `hind : Topology.IsInducing f` using `⟨rfl⟩`. Use `haveI : TopologicalSpace.NoetherianSpace G := hind.noetherianSpace`.

Establish `hf : Continuous f` using `continuous_induced_dom`. Establish `hL : ∀ g : G, Continuous fun x => g * x`. Introduce `g`. Take `⟨ψ, hψ⟩` from `UpperTheory.V.AlgebraTools.icmPt_left (r g)`. Use `continuous_induced_rng.2 ?_` and prove the remaining obligations.

Establish `: (f ∘ fun x => g * x) = PrimeSpectrum.comap ψ ∘ f`. Use function extensionality and compare the values at `x`. Simplify using `only [Function.comp_apply, f, map_mul]`. Conclude with `hψ (r x)`. Rewrite using `[this]`.

Conclude with `(PrimeSpectrum.continuous_comap ψ).comp hf`. Establish `hR : ∀ g : G, Continuous fun x => x * g`. Introduce `g`. Take `⟨ψ, hψ⟩` from `UpperTheory.V.AlgebraTools.icmPt_right (r g)`. Use `continuous_induced_rng.2 ?_` and prove the remaining obligations.

Establish `: (f ∘ fun x => x * g) = PrimeSpectrum.comap ψ ∘ f`. Use function extensionality and compare the values at `x`. Simplify using `only [Function.comp_apply, f, map_mul]`. Conclude with `hψ (r x)`. Rewrite using `[this]`.

Conclude with `(PrimeSpectrum.continuous_comap ψ).comp hf`. Take `⟨N, hNn, hNf, hNc, hNi, hNd⟩` from `UpperTheory.V.AlgebraTools.idComp G hL hR`. Establish `hmemZ : ∀ (S : Set (MvPolynomial (ι × ι) K)) (g : G), f g ∈ PrimeSpectrum.zeroLocus S ↔ ∀ q ∈ S, MvPolynomial.eval (fun p => r g p.1 p.2) q = 0`. Introduce `S g`. Rewrite using `[PrimeSpectrum.mem_zeroLocus]`.

Prove the components needed by the constructor for the conclusion. Introduce `h q hq`. Conclude with `(RingHom.mem_ker).1 (h hq)`. Introduce `h q hq`. Conclude with `(RingHom.mem_ker).2 (h q hq)`.

Use `⟨N, hNn, hNf, ?_, ?_⟩` and prove the remaining obligations. Take `⟨t, ht, hNt⟩` from `isClosed_induced_iff.1 hNc`. Take `⟨S, rfl⟩` from `(PrimeSpectrum.isClosed_iff_zeroLocus t).1 ht`. Use `⟨S, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[← hmemZ S g]`.

Prove the components needed by the constructor for the conclusion. Introduce `hg`. Establish `h' : g ∈ (N : Set G)` using `hg`. Rewrite `h'` using `[← hNt]`. Conclude with `h'`.

Introduce `hg`. Establish `h' : g ∈ f ⁻¹' PrimeSpectrum.zeroLocus S` using `hg`. Rewrite `h'` using `[hNt]`. Conclude with `h'`. Introduce `U hU σ s hs`.

Set `W : MvPolynomial (ι × ι) K → Set G` to `fun q => {g | MvPolynomial.eval (fun p => r (σ * g) p.1 p.2) q ≠ 0}`. Establish `hWo : ∀ q, IsOpen (W q)`. Introduce `q`. Establish `h1 : IsOpen (f ⁻¹' (PrimeSpectrum.basicOpen q : Set _))` using `(PrimeSpectrum.isOpen_basicOpen).preimage hf`. Establish `h2` using `h1.preimage (hL σ)`.

Use `h2 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `g`. Simplify using `only [W, Set.mem_setOf_eq, Set.mem_preimage, f, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen]`. Use `show _ ↔ q ∉ RingHom.ker _`. Rewrite using `[RingHom.mem_ker]`.

Take `⟨x, hxN, hxO⟩` from `(isIrreducible_iff_sInter.1 hNi) (s.image W) (by`. Introduce `u hu`. Take `⟨q, -, rfl⟩` from `Finset.mem_image.1 hu`. Conclude with `hWo q)`. Use the proof step `(by`.

Introduce `u hu`. Take `⟨q, hq, rfl⟩` from `Finset.mem_image.1 hu`. Take `⟨g, hgN, hg⟩` from `hs q hq`. Conclude with `⟨g, hgN, hg⟩)`. Establish `hOo : IsOpen (⋂₀ (↑(s.image W) : Set (Set G)))`.

Apply `Set.Finite.isOpen_sInter (Finset.finite_toSet _)` to reduce the goal to its premises. Introduce `u hu`. Take `⟨q, -, rfl⟩` from `Finset.mem_image.1 hu`. Conclude with `hWo q`. Take `⟨g, hgO, hgUN⟩` from `mem_closure_iff.1 (hNd U hU hxN) _ hOo hxO`.

Use `⟨g, hgUN, fun q hq => ?_⟩` and prove the remaining obligations. Establish `: g ∈ W q` using `hgO _ (Finset.mem_image_of_mem W hq)`. Conclude with `this`.
-/
theorem UpperTheory.V.AlgebraTools.idCompMat :
    ∀ (K G ι : Type) [Field K] [Group G] [Fintype ι] [DecidableEq ι] (r : G →* Matrix ι ι K),
      ∃ N : Subgroup G, N.Normal ∧ N.FiniteIndex ∧
        (∃ I : Set (MvPolynomial (ι × ι) K), ∀ g, g ∈ N ↔ ∀ f ∈ I, MvPolynomial.eval (fun p => r g p.1 p.2) f = 0) ∧
        ∀ (U : Subgroup G), U.FiniteIndex → ∀ (σ : G) (s : Finset (MvPolynomial (ι × ι) K)),
          (∀ f ∈ s, ∃ g ∈ N, MvPolynomial.eval (fun p => r (σ * g) p.1 p.2) f ≠ 0) →
          ∃ g ∈ U ⊓ N, ∀ f ∈ s, MvPolynomial.eval (fun p => r (σ * g) p.1 p.2) f ≠ 0 := by
  classical
  intro K G ι _ _ _ _ r
  let f : G → PrimeSpectrum (MvPolynomial (ι × ι) K) := fun g => UpperTheory.V.AlgebraTools.icmPt (r g)
  letI tG : TopologicalSpace G := TopologicalSpace.induced f inferInstance
  have hind : Topology.IsInducing f := ⟨rfl⟩
  haveI : TopologicalSpace.NoetherianSpace G := hind.noetherianSpace
  have hf : Continuous f := continuous_induced_dom
  have hL : ∀ g : G, Continuous fun x => g * x := by
    intro g
    obtain ⟨ψ, hψ⟩ := UpperTheory.V.AlgebraTools.icmPt_left (r g)
    refine continuous_induced_rng.2 ?_
    have : (f ∘ fun x => g * x) = PrimeSpectrum.comap ψ ∘ f := by
      funext x
      simp only [Function.comp_apply, f, map_mul]
      exact hψ (r x)
    rw [this]
    exact (PrimeSpectrum.continuous_comap ψ).comp hf
  have hR : ∀ g : G, Continuous fun x => x * g := by
    intro g
    obtain ⟨ψ, hψ⟩ := UpperTheory.V.AlgebraTools.icmPt_right (r g)
    refine continuous_induced_rng.2 ?_
    have : (f ∘ fun x => x * g) = PrimeSpectrum.comap ψ ∘ f := by
      funext x
      simp only [Function.comp_apply, f, map_mul]
      exact hψ (r x)
    rw [this]
    exact (PrimeSpectrum.continuous_comap ψ).comp hf
  obtain ⟨N, hNn, hNf, hNc, hNi, hNd⟩ := UpperTheory.V.AlgebraTools.idComp G hL hR
  have hmemZ : ∀ (S : Set (MvPolynomial (ι × ι) K)) (g : G),
      f g ∈ PrimeSpectrum.zeroLocus S ↔ ∀ q ∈ S, MvPolynomial.eval (fun p => r g p.1 p.2) q = 0 := by
    intro S g
    rw [PrimeSpectrum.mem_zeroLocus]
    constructor
    · intro h q hq
      exact (RingHom.mem_ker).1 (h hq)
    · intro h q hq
      exact (RingHom.mem_ker).2 (h q hq)
  refine ⟨N, hNn, hNf, ?_, ?_⟩
  · obtain ⟨t, ht, hNt⟩ := isClosed_induced_iff.1 hNc
    obtain ⟨S, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus t).1 ht
    refine ⟨S, fun g => ?_⟩
    rw [← hmemZ S g]
    constructor
    · intro hg
      have h' : g ∈ (N : Set G) := hg
      rw [← hNt] at h'
      exact h'
    · intro hg
      have h' : g ∈ f ⁻¹' PrimeSpectrum.zeroLocus S := hg
      rw [hNt] at h'
      exact h'
  · intro U hU σ s hs
    let W : MvPolynomial (ι × ι) K → Set G :=
      fun q => {g | MvPolynomial.eval (fun p => r (σ * g) p.1 p.2) q ≠ 0}
    have hWo : ∀ q, IsOpen (W q) := by
      intro q
      have h1 : IsOpen (f ⁻¹' (PrimeSpectrum.basicOpen q : Set _)) :=
        (PrimeSpectrum.isOpen_basicOpen).preimage hf
      have h2 := h1.preimage (hL σ)
      convert h2 using 1
      ext g
      simp only [W, Set.mem_setOf_eq, Set.mem_preimage, f, SetLike.mem_coe,
        PrimeSpectrum.mem_basicOpen]
      show _ ↔ q ∉ RingHom.ker _
      rw [RingHom.mem_ker]
    obtain ⟨x, hxN, hxO⟩ := (isIrreducible_iff_sInter.1 hNi) (s.image W)
      (by
        intro u hu
        obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hu
        exact hWo q)
      (by
        intro u hu
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hu
        obtain ⟨g, hgN, hg⟩ := hs q hq
        exact ⟨g, hgN, hg⟩)
    have hOo : IsOpen (⋂₀ (↑(s.image W) : Set (Set G))) := by
      apply Set.Finite.isOpen_sInter (Finset.finite_toSet _)
      intro u hu
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hu
      exact hWo q
    obtain ⟨g, hgO, hgUN⟩ := mem_closure_iff.1 (hNd U hU hxN) _ hOo hxO
    refine ⟨g, hgUN, fun q hq => ?_⟩
    have : g ∈ W q := hgO _ (Finset.mem_image_of_mem W hq)
    exact this
