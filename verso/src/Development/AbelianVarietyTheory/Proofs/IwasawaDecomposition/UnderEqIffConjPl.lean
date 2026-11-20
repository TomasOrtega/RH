import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.WithZeroEqOfLeExpIff

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Chr

section General

variable {L : Type} [Field L] [NumberField L]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use extensionality with `x`. Establish `h1 : v'.valuation L (algebraMap (𝓞 L) L (RingOfIntegers.mapRingEquiv c x)) = v.valuation L (algebraMap (𝓞 L) L x)` using `h (algebraMap (𝓞 L) L x)`. Rewrite using `[Ideal.mem_comap, ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L), ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L), h1]`.

Introduce `h x`. Conclude with `(GlobalTheory.QNorm.valuation_of_eq_comap c v' v h x).symm`.
-/
theorem conjPl_iff_comap (c : L ≃+* L) (v v' : HeightOneSpectrum (𝓞 L)) :
    ConjPl c v v' ↔ v.asIdeal = v'.asIdeal.comap (RingOfIntegers.mapRingEquiv c) := by
  constructor
  · intro h
    ext x
    have h1 : v'.valuation L (algebraMap (𝓞 L) L (RingOfIntegers.mapRingEquiv c x)) =
        v.valuation L (algebraMap (𝓞 L) L x) := h (algebraMap (𝓞 L) L x)
    rw [Ideal.mem_comap, ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L),
      ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L), h1]
  · intro h x
    exact (GlobalTheory.QNorm.valuation_of_eq_comap c v' v h x).symm

/- English proof (translation)
Rewrite using `[conjPl_iff_comap]`. Prove the components needed by the constructor for the conclusion. Introduce `h x y hxy`. Establish `e : y = RingOfIntegers.mapRingEquiv c x` using `RingOfIntegers.ext hxy`. Rewrite using `[h, Ideal.mem_comap, e]`.

Introduce `h`. Use extensionality with `x`. Conclude with `h x (RingOfIntegers.mapRingEquiv c x) rfl`.
-/
theorem conjPl_iff_mem (c : L ≃+* L) (v v' : HeightOneSpectrum (𝓞 L)) :
    ConjPl c v v' ↔ ∀ x y : 𝓞 L, (y : L) = c (x : L) → (x ∈ v.asIdeal ↔ y ∈ v'.asIdeal) := by
  rw [conjPl_iff_comap]
  constructor
  · intro h x y hxy
    have e : y = RingOfIntegers.mapRingEquiv c x := RingOfIntegers.ext hxy
    rw [h, Ideal.mem_comap, e]
  · intro h
    ext x
    exact h x (RingOfIntegers.mapRingEquiv c x) rfl

/- English proof (translation)
Use `set e : 𝓞 L ≃+* 𝓞 L := RingOfIntegers.mapRingEquiv c with he`. Use `⟨v.comap (e.symm : 𝓞 L →+* 𝓞 L) e.symm.surjective, ?_, ?_⟩` and prove the remaining obligations. Use `show ConjPl c v _`. Rewrite using `[conjPl_iff_comap]`. Use extensionality with `x`.

Express the relevant statement in the definitionally equal form `x ∈ v.asIdeal ↔ e.symm (e x) ∈ v.asIdeal`. Rewrite using `[e.symm_apply_apply]`. Introduce `v' h`. Rewrite `h` using `[conjPl_iff_comap]`. Use extensionality with `x`.

Express the relevant statement in the definitionally equal form `x ∈ v'.asIdeal ↔ e.symm x ∈ v.asIdeal`. Rewrite using `[h, Ideal.mem_comap, e.apply_symm_apply]`.
-/
theorem existsUnique_conjPl (c : L ≃+* L) (v : HeightOneSpectrum (𝓞 L)) : ∃! v', ConjPl c v v' := by
  set e : 𝓞 L ≃+* 𝓞 L := RingOfIntegers.mapRingEquiv c with he
  refine ⟨v.comap (e.symm : 𝓞 L →+* 𝓞 L) e.symm.surjective, ?_, ?_⟩
  · show ConjPl c v _
    rw [conjPl_iff_comap]
    ext x
    change x ∈ v.asIdeal ↔ e.symm (e x) ∈ v.asIdeal
    rw [e.symm_apply_apply]
  · intro v' h
    rw [conjPl_iff_comap] at h
    ext x
    change x ∈ v'.asIdeal ↔ e.symm x ∈ v.asIdeal
    rw [h, Ideal.mem_comap, e.apply_symm_apply]

/- English proof (translation)
Establish `: Algebra.IsQuadraticExtension F L` using `{ finrank_eq_two' := hr }`. Establish `: IsGalois F L` using `inferInstance`. Establish `hall : ∀ σ : L ≃ₐ[F] L, σ = 1 ∨ σ = c`. Introduce `σ`. Establish `hcard : Nat.card (L ≃ₐ[F] L) = 2` using `by rw [IsGalois.card_aut_eq_finrank, hr]`.

Take `⟨y, -, hy⟩` from `(Nat.card_eq_two_iff' (1 : L ≃ₐ[F] L)).1 hcard`. Distinguish the cases in `h : σ = 1`. Conclude with `Or.inl h`. Conclude with `Or.inr ((hy σ h).trans (hy c hc).symm)`. Prove the components needed by the constructor for the conclusion.

Introduce `hu`. Use `w.isPrime` as an intermediate fact. Use `w'.isPrime` as an intermediate fact. Establish `hu' : w'.asIdeal.under (𝓞 F) = w.asIdeal.under (𝓞 F)` using `congrArg HeightOneSpectrum.asIdeal hu`. Take `⟨σ, hσ⟩` from `Ideal.exists_comap_galRestrict_eq (𝓞 F) F L (𝓞 L) (p := w.asIdeal.under (𝓞 F)) (P₁ := w'.asIdeal) (P₂ := w.asIdeal) ⟨inferInstance, ⟨hu'.symm⟩⟩ ⟨inferInstance, ⟨rfl⟩⟩`.

Break down `hall σ with rfl | rfl` into its components or cases. Use `left`. Use extensionality with `x`. Rewrite using `[← hσ, map_one, Ideal.mem_comap]`. Both sides reduce to the same expression.

Use `right`. Rewrite using `[conjPl_iff_mem]`. Introduce `x y hxy`. Establish `e : y = galRestrict (𝓞 F) F L (𝓞 L) σ x`. Apply `RingOfIntegers.ext` to reduce the goal to its premises.

Rewrite using `[hxy]`. Conclude with `(algebraMap_galRestrict_apply (𝓞 F) σ x).symm`. Rewrite using `[← hσ, Ideal.mem_comap, e]`. Introduce and unpack `(rfl | h)`. Both sides reduce to the same expression.

Rewrite `h` using `[conjPl_iff_mem]`. Use extensionality with `a`. Conclude with `(h (algebraMap (𝓞 F) (𝓞 L) a) (algebraMap (𝓞 F) (𝓞 L) a) (c.commutes (a : F)).symm).symm`.
-/
theorem under_eq_iff_conjPl {F : Type} [Field F] [NumberField F] [Algebra F L] (c : L ≃ₐ[F] L)
    (hr : Module.finrank F L = 2) (hc : c ≠ 1) (w w' : HeightOneSpectrum (𝓞 L)) :
    w'.under (𝓞 F) = w.under (𝓞 F) ↔ (w' = w ∨ ConjPl c.toRingEquiv w w') := by
  have : Algebra.IsQuadraticExtension F L := { finrank_eq_two' := hr }
  have : IsGalois F L := inferInstance
  have hall : ∀ σ : L ≃ₐ[F] L, σ = 1 ∨ σ = c := by
    intro σ
    have hcard : Nat.card (L ≃ₐ[F] L) = 2 := by rw [IsGalois.card_aut_eq_finrank, hr]
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : L ≃ₐ[F] L)).1 hcard
    by_cases h : σ = 1
    · exact Or.inl h
    · exact Or.inr ((hy σ h).trans (hy c hc).symm)
  constructor
  · intro hu
    have := w.isPrime
    have := w'.isPrime
    have hu' : w'.asIdeal.under (𝓞 F) = w.asIdeal.under (𝓞 F) := congrArg HeightOneSpectrum.asIdeal hu
    obtain ⟨σ, hσ⟩ := Ideal.exists_comap_galRestrict_eq (𝓞 F) F L (𝓞 L) (p := w.asIdeal.under (𝓞 F))
      (P₁ := w'.asIdeal) (P₂ := w.asIdeal) ⟨inferInstance, ⟨hu'.symm⟩⟩ ⟨inferInstance, ⟨rfl⟩⟩
    rcases hall σ with rfl | rfl
    · left
      ext x
      rw [← hσ, map_one, Ideal.mem_comap]
      rfl
    · right
      rw [conjPl_iff_mem]
      intro x y hxy
      have e : y = galRestrict (𝓞 F) F L (𝓞 L) σ x := by
        apply RingOfIntegers.ext
        rw [hxy]
        exact (algebraMap_galRestrict_apply (𝓞 F) σ x).symm
      rw [← hσ, Ideal.mem_comap, e]
  · rintro (rfl | h)
    · rfl
    · rw [conjPl_iff_mem] at h
      ext a
      exact (h (algebraMap (𝓞 F) (𝓞 L) a) (algebraMap (𝓞 F) (𝓞 L) a) (c.commutes (a : F)).symm).symm

end General

open Classical in

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ _ _ c v => existsUnique_conjPl c v, fun _ H w w' => (conjPl_iff_mem H.conj.toRingEquiv w w').symm, fun _ _ _ _ _ _ _ c hr hc w w' => under_eq_iff_conjPl c hr hc w w'⟩`.
-/
theorem conjPl_main : (∀ (L : Type) [Field L] [NumberField L] (c : L ≃+* L) (v : HeightOneSpectrum (𝓞 L)), ∃! v', ConjPl c v v') ∧ (∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (w w' : HeightOneSpectrum (𝓞 H.E)), IsConjPl H w w' ↔ ConjPl H.conj.toRingEquiv w w') ∧ ∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] (c : L ≃ₐ[F] L), Module.finrank F L = 2 → c ≠ 1 → ∀ (w w' : HeightOneSpectrum (𝓞 L)), w'.under (𝓞 F) = w.under (𝓞 F) ↔ (w' = w ∨ ConjPl c.toRingEquiv w w') :=
  ⟨fun _ _ _ c v => existsUnique_conjPl c v,
    fun _ H w w' => (conjPl_iff_mem H.conj.toRingEquiv w w').symm,
    fun _ _ _ _ _ _ _ c hr hc w w' => under_eq_iff_conjPl c hr hc w w'⟩

end GlobalTheory.Mem.Chr
