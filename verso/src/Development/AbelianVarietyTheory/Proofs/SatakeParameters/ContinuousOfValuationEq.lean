import Mathlib

open IsDedekindDomain Topology

namespace GlobalTheory.ValuationExtensionContinuous

/- English proof (translation)
Use `continuous_of_continuousAt_zero g ?_` and prove the remaining obligations. Rewrite using `[ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero A Γ).tendsto_iff (Valued.hasBasis_nhds_zero B Γ)]`. Introduce `γ _`. Take `⟨k, hk⟩` from `hs (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)`. Establish `hk0 : (Valued.v k : Γ) ≠ 0`.

Rewrite using `[hk]`. Conclude with `(map_ne_zero _).mpr γ.ne_zero`. Establish `hk1 : (Valued.v : Valuation A Γ).restrict k ≠ 0` using `by simpa using hk0`. Use `⟨Units.mk0 _ hk1, trivial, fun x hx => ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hx`.

Simplify using `only [Set.mem_setOf_eq]`. Rewrite using `[Valuation.restrict_lt_iff_lt_embedding, hg, ← hk]`. Conclude with `hx`.
-/
theorem continuous_of_valuation_eq {A B Γ : Type} [Ring A] [Ring B]
    [LinearOrderedCommGroupWithZero Γ] [Valued A Γ] [Valued B Γ]
    (hs : Function.Surjective (Valued.v : A → Γ)) (g : A →+* B)
    (hg : ∀ a, Valued.v (g a) = (Valued.v a : Γ)) : Continuous g := by
  refine continuous_of_continuousAt_zero g ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero A Γ).tendsto_iff
    (Valued.hasBasis_nhds_zero B Γ)]
  intro γ _
  obtain ⟨k, hk⟩ := hs (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)
  have hk0 : (Valued.v k : Γ) ≠ 0 := by
    rw [hk]
    exact (map_ne_zero _).mpr γ.ne_zero
  have hk1 : (Valued.v : Valuation A Γ).restrict k ≠ 0 := by simpa using hk0
  refine ⟨Units.mk0 _ hk1, trivial, fun x hx => ?_⟩
  simp only [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hx
  simp only [Set.mem_setOf_eq]
  rw [Valuation.restrict_lt_iff_lt_embedding, hg, ← hk]
  exact hx

/- English proof (translation)
Set `g : WithVal (w.valuation K) →+* u.adicCompletion L` to `f.comp (WithVal.equiv (w.valuation K)).toRingHom`. Establish `hg : Continuous g`. Use `continuous_of_valuation_eq (fun c => ?_) g (fun a => hf _)` and prove the remaining obligations. Take `⟨k, hk⟩` from `w.valuation_surjective K c`. Conclude with `⟨WithVal.toVal _ k, hk⟩`.

Set `ψ` to `UniformSpace.Completion.extensionHom g hg`. Set `φ : w.adicCompletion K →+* u.adicCompletion L` to `ψ.comp (HeightOneSpectrum.adicCompletion.equiv K w).toRingHom`. Establish `hψ : Continuous ψ` using `UniformSpace.Completion.continuous_extension`. Establish `hφ : Continuous φ` using `hψ.comp (HeightOneSpectrum.adicCompletion.continuous_toCompletion K w)`. Establish `hφa : ∀ a : WithVal (w.valuation K), φ (HeightOneSpectrum.adicCompletion.ofCompletion (a : (w.valuation K).Completion)) = f a.ofVal` using `fun a => UniformSpace.Completion.extensionHom_coe g hg a`.

Use `⟨φ, hφ, fun x => hφa (WithVal.toVal _ x), fun y => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hy : y = 0`. Substitute `hy` using the available equality. Rewrite using `[map_zero, map_zero, map_zero]`. Establish `h1 : (Valued.v y : WithZero (Multiplicative ℤ)) ≠ 0` using `by simpa using hy`.

Establish `h2 : (Valued.v (φ y) : WithZero (Multiplicative ℤ)) ≠ 0` using `by simpa using hy`. Establish `hU` using `Filter.inter_mem (Valued.locally_const h1) (hφ.continuousAt.preimage_mem_nhds (Valued.locally_const h2))`. Establish `hV` using `(HeightOneSpectrum.adicCompletion.continuous_ofCompletion K w).continuousAt (x := y.toCompletion) |>.preimage_mem_nhds hU`. Take `⟨a, ha1, ha2⟩` from `UniformSpace.Completion.denseRange_coe.mem_nhds hV`. Simplify using `only [Set.mem_preimage, Set.mem_setOf_eq] at ha1 ha2`.

Rewrite using `[← ha1, ← ha2, hφa, hf]`. Conclude with `(HeightOneSpectrum.adicCompletion.valued_coe K w a.ofVal).symm`.
-/
theorem exists_extension {K : Type} [Field K] [NumberField K] {R L : Type} [CommRing R]
    [IsDedekindDomain R] [Field L] [Algebra R L] [IsFractionRing R L]
    (w : HeightOneSpectrum (NumberField.RingOfIntegers K)) (u : HeightOneSpectrum R)
    (f : K →+* u.adicCompletion L)
    (hf : ∀ x : K, Valued.v (f x) = w.valuation K x) :
    ∃ φ : w.adicCompletion K →+* u.adicCompletion L, Continuous φ ∧
      (∀ x : K, φ (algebraMap K (w.adicCompletion K) x) = f x) ∧
      ∀ y : w.adicCompletion K, Valued.v (φ y) = Valued.v y := by
  let g : WithVal (w.valuation K) →+* u.adicCompletion L :=
    f.comp (WithVal.equiv (w.valuation K)).toRingHom
  have hg : Continuous g := by
    refine continuous_of_valuation_eq (fun c => ?_) g (fun a => hf _)
    obtain ⟨k, hk⟩ := w.valuation_surjective K c
    exact ⟨WithVal.toVal _ k, hk⟩
  let ψ := UniformSpace.Completion.extensionHom g hg
  let φ : w.adicCompletion K →+* u.adicCompletion L :=
    ψ.comp (HeightOneSpectrum.adicCompletion.equiv K w).toRingHom
  have hψ : Continuous ψ := UniformSpace.Completion.continuous_extension
  have hφ : Continuous φ :=
    hψ.comp (HeightOneSpectrum.adicCompletion.continuous_toCompletion K w)
  have hφa : ∀ a : WithVal (w.valuation K),
      φ (HeightOneSpectrum.adicCompletion.ofCompletion (a : (w.valuation K).Completion))
        = f a.ofVal := fun a => UniformSpace.Completion.extensionHom_coe g hg a
  refine ⟨φ, hφ, fun x => hφa (WithVal.toVal _ x), fun y => ?_⟩
  by_cases hy : y = 0
  · subst hy
    rw [map_zero, map_zero, map_zero]
  have h1 : (Valued.v y : WithZero (Multiplicative ℤ)) ≠ 0 := by simpa using hy
  have h2 : (Valued.v (φ y) : WithZero (Multiplicative ℤ)) ≠ 0 := by simpa using hy
  have hU := Filter.inter_mem (Valued.locally_const h1)
    (hφ.continuousAt.preimage_mem_nhds (Valued.locally_const h2))
  have hV := (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K w).continuousAt
    (x := y.toCompletion) |>.preimage_mem_nhds hU
  obtain ⟨a, ha1, ha2⟩ := UniformSpace.Completion.denseRange_coe.mem_nhds hV
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at ha1 ha2
  rw [← ha1, ← ha2, hφa, hf]
  exact (HeightOneSpectrum.adicCompletion.valued_coe K w a.ofVal).symm

end GlobalTheory.ValuationExtensionContinuous
