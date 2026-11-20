import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasLinForms
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

namespace GlobalTheory

/- English proof (translation)
Take `⟨hN, -, hC, hZ⟩` from `hR`. Take `⟨hfl, hm, -⟩` from `hφ`. Use `letI : Algebra A R := φ.toAlgebra`. Use `haveI : Module.Flat A R := hfl`. Use `haveI : IsLocalHom (algebraMap A R) := by`.

Use `⟨fun a ha => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hna`. Establish `h1 : φ a ∈ maximalIdeal R` using `hm ▸ Ideal.mem_map_of_mem φ ((mem_maximalIdeal a).2 hna)`. Conclude with `(mem_maximalIdeal _).1 h1 ha`. Use `haveI hff : Module.FaithfullyFlat A R := Module.FaithfullyFlat.of_flat_of_isLocalHom`.

Establish `hinj : Function.Injective φ` using `FaithfulSMul.algebraMap_injective A R`. Establish `hcm : ∀ I : Ideal A, (I.map φ).comap φ = I` using `fun I => Ideal.comap_map_eq_self_of_faithfullyFlat (B := R) I`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible A`. Establish `hmR : maximalIdeal R = Ideal.span {φ ϖ}`. Rewrite using `[← hm, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]`.

Establish `hnf : ¬ IsField R`. Introduce `hF`. Establish `h0 : maximalIdeal R = ⊥` using `(isField_iff_maximalIdeal_eq).1 hF`. Rewrite `h0` using `[hmR, Ideal.span_singleton_eq_bot]`. Conclude with `hϖ.ne_zero (hinj (h0.trans (map_zero φ).symm))`.

Establish `hp : (maximalIdeal R).IsPrincipal` using `⟨⟨φ ϖ, hmR⟩⟩`. Establish `hdvr : IsDiscreteValuationRing R` using `((IsDiscreteValuationRing.TFAE (R := R) hnf).out 0 4).2 hp`. Establish `hdesc : ∀ a b : A, φ a ∣ φ b → a ∣ b`. Introduce `a b h`. Establish `hb : b ∈ ((Ideal.span {a}).map φ).comap φ`.

Rewrite using `[Ideal.mem_comap, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]`. Conclude with `h`. Rewrite `hb` using `[hcm, Ideal.mem_span_singleton]`. Then use the resulting hypothesis. Use `⟨(cDvr_iff R).2 ⟨hdvr, hC, hZ⟩, hinj, fun a b h => ?_⟩` and prove the remaining obligations. Conclude with `associated_of_dvd_dvd (hdesc a b h.dvd) (hdesc b a h.symm.dvd)`.
-/
theorem cDvr_of_isEtaleCompletion (A R : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing R]
    [IsDomain R] [IsLocalRing R] (φ : A →+* R) (hR : IsCN R) (hφ : IsEtaleCompletion φ) :
    CDvr R ∧ Function.Injective φ ∧ ∀ a b : A, Associated (φ a) (φ b) → Associated a b := by
  obtain ⟨hN, -, hC, hZ⟩ := hR
  obtain ⟨hfl, hm, -⟩ := hφ
  letI : Algebra A R := φ.toAlgebra
  haveI : Module.Flat A R := hfl
  haveI : IsLocalHom (algebraMap A R) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have h1 : φ a ∈ maximalIdeal R := hm ▸ Ideal.mem_map_of_mem φ ((mem_maximalIdeal a).2 hna)
    exact (mem_maximalIdeal _).1 h1 ha
  haveI hff : Module.FaithfullyFlat A R := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hinj : Function.Injective φ := FaithfulSMul.algebraMap_injective A R
  have hcm : ∀ I : Ideal A, (I.map φ).comap φ = I := fun I =>
    Ideal.comap_map_eq_self_of_faithfullyFlat (B := R) I
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hmR : maximalIdeal R = Ideal.span {φ ϖ} := by
    rw [← hm, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have hnf : ¬ IsField R := by
    intro hF
    have h0 : maximalIdeal R = ⊥ := (isField_iff_maximalIdeal_eq).1 hF
    rw [hmR, Ideal.span_singleton_eq_bot] at h0
    exact hϖ.ne_zero (hinj (h0.trans (map_zero φ).symm))
  have hp : (maximalIdeal R).IsPrincipal := ⟨⟨φ ϖ, hmR⟩⟩
  have hdvr : IsDiscreteValuationRing R :=
    ((IsDiscreteValuationRing.TFAE (R := R) hnf).out 0 4).2 hp
  have hdesc : ∀ a b : A, φ a ∣ φ b → a ∣ b := by
    intro a b h
    have hb : b ∈ ((Ideal.span {a}).map φ).comap φ := by
      rw [Ideal.mem_comap, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
      exact h
    rwa [hcm, Ideal.mem_span_singleton] at hb
  refine ⟨(cDvr_iff R).2 ⟨hdvr, hC, hZ⟩, hinj, fun a b h => ?_⟩
  exact associated_of_dvd_dvd (hdesc a b h.dvd) (hdesc b a h.symm.dvd)

end GlobalTheory
