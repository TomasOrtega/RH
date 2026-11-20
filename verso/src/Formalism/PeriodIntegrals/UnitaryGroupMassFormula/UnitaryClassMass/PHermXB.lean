import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PHermSk

open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ σ hσ hfix V _ _ p hp t ht X`. Establish `hσσ : ∀ a, σ (σ a) = a` using `fun a => by rw [hσ, hσ, star_star]`. Establish `hinj : Function.Injective (algebraMap (𝓞 E) E)` using `IsFractionRing.injective (𝓞 E) E`. Establish `hcomm : ∀ c : 𝓞 F, algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) c) = algebraMap F E (algebraMap (𝓞 F) F c)`. Introduce `c`.

Use `first`. Consider the case `rfl`. Consider the case `rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]`. Establish `hSw : Sw F E t ≤ hcompl (K` using `E) p := by`. Introduce `s hs`.

Take `⟨c, hc, rfl⟩` from `Submonoid.mem_map.1 hs`. Apply `Submonoid.subset_closure` to reduce the goal to its premises. Rewrite using `[Set.mem_setOf_eq]`. Establish `hcp : algebraMap (𝓞 F) (𝓞 E) c ∉ p`. Introduce `h'`.

Apply `Ideal.mem_primeCompl_iff.1 hc` to reduce the goal to its premises. Rewrite using `[ht, Ideal.mem_comap]`. Conclude with `h'`. Use `⟨hcp, fun t' ht' => ?_⟩` and prove the remaining obligations. Establish `h3 : t' = algebraMap (𝓞 F) (𝓞 E) c`.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[ht', hcomm, ← hσ, AlgHom.commutes]`. Rewrite using `[h3]`. Conclude with `hcp`. Establish `key : ∀ s ∈ hcompl (K` using `E) p, ∃ r : 𝓞 E, r * s ∈ Sw F E t := by`.

Introduce `s hs`. Proceed by induction on `hs using Submonoid.closure_induction with`. Consider the case `mem s hs`. Take `⟨hsp, hconj⟩` from `hs`. Establish `hint : IsIntegral ℤ (σ (algebraMap (𝓞 E) E s))` using `(NumberField.RingOfIntegers.isIntegral_coe s).map σ.toRingHom.toIntAlgHom`.

Set `sb : 𝓞 E` to `⟨σ (algebraMap (𝓞 E) E s), hint⟩`. Establish `hsb : algebraMap (𝓞 E) E sb = star (algebraMap (𝓞 E) E s)`. Rewrite using `[← hσ]`. Both sides reduce to the same expression. Establish `hsbp : sb ∉ p` using `hconj sb hsb`.

Establish `hfixN : σ (algebraMap (𝓞 E) E (sb * s)) = algebraMap (𝓞 E) E (sb * s)`. Rewrite using `[map_mul, map_mul, hsb, ← hσ, hσσ, mul_comm]`. Take `⟨c, hc⟩` from `hfix _ hfixN`. Establish `hcint : IsIntegral ℤ c`. Rewrite using `[← isIntegral_algebraMap_iff (algebraMap F E).injective, hc]`.

Conclude with `NumberField.RingOfIntegers.isIntegral_coe (sb * s)`. Set `c' : 𝓞 F` to `⟨c, hcint⟩`. Establish `hc' : algebraMap (𝓞 F) (𝓞 E) c' = sb * s`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[hcomm, ← hc]`.

Both sides reduce to the same expression. Use `⟨sb, Submonoid.mem_map.2 ⟨c', ?_, hc'⟩⟩` and prove the remaining obligations. Rewrite using `[Ideal.mem_primeCompl_iff, ht, Ideal.mem_comap, hc']`. Conclude with `fun h' => (hp.isPrime.mem_or_mem h').elim hsbp hsp`. Consider the case `one => exact ⟨1, by rw [one_mul]; exact (Sw F E t).one_mem⟩`.

Consider the case `mul x y _ _ hx hy`. Take `⟨r1, h1⟩` from `hx`. Take `⟨r2, h2⟩` from `hy`. Use `⟨r1 * r2, ?_⟩` and prove the remaining obligations. Rewrite using `[show r1 * r2 * (x * y) = r1 * x * (r2 * y) by ring]`.

Conclude with `(Sw F E t).mul_mem h1 h2`. Unfold `loc`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs, hsx⟩`.

Take `⟨r, hr⟩` from `key s hs`. Conclude with `(show ∃ s ∈ Sw F E t, s • x ∈ X from ⟨r * s, hr, by rw [mul_smul]; exact X.smul_mem r hsx⟩)`. Introduce and unpack `⟨s, hs, hsx⟩`. Conclude with `(show ∃ s ∈ hcompl (K := E) p, s • x ∈ X from ⟨s, hSw hs, hsx⟩)`.
-/
theorem local_switching_lattice : LocSw := by
  intro F E _ _ _ _ _ _ σ hσ hfix V _ _ p hp t ht X
  have hσσ : ∀ a, σ (σ a) = a := fun a => by rw [hσ, hσ, star_star]
  have hinj : Function.Injective (algebraMap (𝓞 E) E) := IsFractionRing.injective (𝓞 E) E
  have hcomm : ∀ c : 𝓞 F, algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) c) =
      algebraMap F E (algebraMap (𝓞 F) F c) := by
    intro c
    first
    | rfl
    | rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hSw : Sw F E t ≤ hcompl (K := E) p := by
    intro s hs
    obtain ⟨c, hc, rfl⟩ := Submonoid.mem_map.1 hs
    apply Submonoid.subset_closure
    rw [Set.mem_setOf_eq]
    have hcp : algebraMap (𝓞 F) (𝓞 E) c ∉ p := by
      intro h'
      apply Ideal.mem_primeCompl_iff.1 hc
      rw [ht, Ideal.mem_comap]
      exact h'
    refine ⟨hcp, fun t' ht' => ?_⟩
    have h3 : t' = algebraMap (𝓞 F) (𝓞 E) c := by
      apply hinj
      rw [ht', hcomm, ← hσ, AlgHom.commutes]
    rw [h3]
    exact hcp
  have key : ∀ s ∈ hcompl (K := E) p, ∃ r : 𝓞 E, r * s ∈ Sw F E t := by
    intro s hs
    induction hs using Submonoid.closure_induction with
    | mem s hs =>
      obtain ⟨hsp, hconj⟩ := hs
      have hint : IsIntegral ℤ (σ (algebraMap (𝓞 E) E s)) :=
        (NumberField.RingOfIntegers.isIntegral_coe s).map σ.toRingHom.toIntAlgHom
      let sb : 𝓞 E := ⟨σ (algebraMap (𝓞 E) E s), hint⟩
      have hsb : algebraMap (𝓞 E) E sb = star (algebraMap (𝓞 E) E s) := by
        rw [← hσ]
        rfl
      have hsbp : sb ∉ p := hconj sb hsb
      have hfixN : σ (algebraMap (𝓞 E) E (sb * s)) = algebraMap (𝓞 E) E (sb * s) := by
        rw [map_mul, map_mul, hsb, ← hσ, hσσ, mul_comm]
      obtain ⟨c, hc⟩ := hfix _ hfixN
      have hcint : IsIntegral ℤ c := by
        rw [← isIntegral_algebraMap_iff (algebraMap F E).injective, hc]
        exact NumberField.RingOfIntegers.isIntegral_coe (sb * s)
      let c' : 𝓞 F := ⟨c, hcint⟩
      have hc' : algebraMap (𝓞 F) (𝓞 E) c' = sb * s := by
        apply hinj
        rw [hcomm, ← hc]
        rfl
      refine ⟨sb, Submonoid.mem_map.2 ⟨c', ?_, hc'⟩⟩
      rw [Ideal.mem_primeCompl_iff, ht, Ideal.mem_comap, hc']
      exact fun h' => (hp.isPrime.mem_or_mem h').elim hsbp hsp
    | one => exact ⟨1, by rw [one_mul]; exact (Sw F E t).one_mem⟩
    | mul x y _ _ hx hy =>
      obtain ⟨r1, h1⟩ := hx
      obtain ⟨r2, h2⟩ := hy
      refine ⟨r1 * r2, ?_⟩
      rw [show r1 * r2 * (x * y) = r1 * x * (r2 * y) by ring]
      exact (Sw F E t).mul_mem h1 h2
  unfold loc
  ext x
  constructor
  · rintro ⟨s, hs, hsx⟩
    obtain ⟨r, hr⟩ := key s hs
    exact (show ∃ s ∈ Sw F E t, s • x ∈ X from
      ⟨r * s, hr, by rw [mul_smul]; exact X.smul_mem r hsx⟩)
  · rintro ⟨s, hs, hsx⟩
    exact (show ∃ s ∈ hcompl (K := E) p, s • x ∈ X from ⟨s, hSw hs, hsx⟩)

end PI.UnitaryGroupMassFormula.UJClassMass

end
