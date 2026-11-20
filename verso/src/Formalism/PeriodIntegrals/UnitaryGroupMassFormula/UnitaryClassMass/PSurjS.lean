import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PSurjF

open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

def HermApprox : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ a, σ a = star a) → (∃ θ : E, σ θ ≠ θ) →
    h.IsSymm → h.Nondegenerate → Submodule.IsLattice E L0 →
    ∀ N ∈ genus h L0, ∀ P : Finset (Ideal (𝓞 E)), (∀ p ∈ P, p.IsMaximal) →
      ∃ γ : UJ (σ : E →+* E) (gramOf h b), ∀ p ∈ P,
        loc (K := E) p (gmap (linOf b (γ : GL (Fin M) E)) L0) = loc (K := E) p N

section Over

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `hI : Ideal.span {a} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `ha`. Establish `hfin` using `(Ideal.finite_factors hI).image (fun v : HeightOneSpectrum (𝓞 E) => v.asIdeal)`. Apply `hfin.subset` to reduce the goal to its premises.

Introduce and unpack `p ⟨hp, hap⟩`. Establish `hne : p ≠ ⊥` using `Ring.ne_bot_of_isMaximal_of_not_isField hp (RingOfIntegers.not_isField E)`. Use `⟨⟨p, hp.isPrime, hne⟩, ?_, rfl⟩` and prove the remaining obligations. Use `show p ∣ Ideal.span {a}`. Rewrite using `[Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]`.

Conclude with `hap`.
-/
theorem finMaxElt (a : 𝓞 E) (ha : a ≠ 0) : {p : Ideal (𝓞 E) | p.IsMaximal ∧ a ∈ p}.Finite := by
  have hI : Ideal.span {a} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact ha
  have hfin := (Ideal.finite_factors hI).image (fun v : HeightOneSpectrum (𝓞 E) => v.asIdeal)
  apply hfin.subset
  rintro p ⟨hp, hap⟩
  have hne : p ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hp (RingOfIntegers.not_isField E)
  refine ⟨⟨p, hp.isPrime, hne⟩, ?_, rfl⟩
  show p ∣ Ideal.span {a}
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hap

/- English proof (translation)
Establish `ha : ∀ v : HeightOneSpectrum (𝓞 F), ∃ a : 𝓞 F, a ∈ v.asIdeal ∧ a ≠ 0` using `fun v => Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot`. Use `choose a haM ha0 using ha`. Establish `hne0 : ∀ x : 𝓞 F, x ≠ 0 → algebraMap (𝓞 F) (𝓞 E) x ≠ 0`. Introduce `x hx h0`. Establish `h1 : algebraMap (𝓞 F) E x = 0`.

Rewrite using `[IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E, h0, map_zero]`. Rewrite `h1` using `[IsScalarTower.algebraMap_apply (𝓞 F) F E, map_eq_zero_iff _ (algebraMap F E).injective]`. Conclude with `hx (FaithfulSMul.algebraMap_injective (𝓞 F) F (by rw [h1, map_zero]))`. Apply `(T.finite_toSet.biUnion (fun v _ => finMaxElt (algebraMap (𝓞 F) (𝓞 E) (a v)) (hne0 (a v) (ha0 v)))).subset` to reduce the goal to its premises. Introduce and unpack `p ⟨hp, v, hv, hc⟩`.

Use `Set.mem_biUnion (x := v) hv ⟨hp, ?_⟩` and prove the remaining obligations. Establish `: a v ∈ p.comap (algebraMap (𝓞 F) (𝓞 E))` using `by rw [hc]; exact haM v`. Conclude with `this`.
-/
theorem primesOver_finite (T : Finset (HeightOneSpectrum (𝓞 F))) :
    {p : Ideal (𝓞 E) | p.IsMaximal ∧ ∃ v ∈ T, p.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal}.Finite := by
  classical
  have ha : ∀ v : HeightOneSpectrum (𝓞 F), ∃ a : 𝓞 F, a ∈ v.asIdeal ∧ a ≠ 0 :=
    fun v => Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  choose a haM ha0 using ha
  have hne0 : ∀ x : 𝓞 F, x ≠ 0 → algebraMap (𝓞 F) (𝓞 E) x ≠ 0 := by
    intro x hx h0
    have h1 : algebraMap (𝓞 F) E x = 0 := by
      rw [IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E, h0, map_zero]
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F E, map_eq_zero_iff _ (algebraMap F E).injective] at h1
    exact hx (FaithfulSMul.algebraMap_injective (𝓞 F) F (by rw [h1, map_zero]))
  apply (T.finite_toSet.biUnion (fun v _ => finMaxElt (algebraMap (𝓞 F) (𝓞 E) (a v))
    (hne0 (a v) (ha0 v)))).subset
  rintro p ⟨hp, v, hv, hc⟩
  refine Set.mem_biUnion (x := v) hv ⟨hp, ?_⟩
  have : a v ∈ p.comap (algebraMap (𝓞 F) (𝓞 E)) := by rw [hc]; exact haM v
  exact this

variable [StarRing E] {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

/- English proof (translation)
Introduce and unpack `x ⟨s, hs, hsx⟩`. Set `I : Ideal (𝓞 E)` to `Y.comap (LinearMap.toSpanSingleton (𝓞 E) V x)`. Assume the negation of the conclusion as `hno`. Establish `hle : I.comap (algebraMap (𝓞 F) (𝓞 E)) ≤ v.asIdeal`. Introduce `a ha`.

Assume the negation of the conclusion as `hav`. Conclude with `hno ⟨a, hav, ha⟩`. Take `⟨Q, hIQ, hQp, hQc⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal I hle`. Establish `hQm : Q.IsMaximal` using `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := 𝓞 F) Q (by rw [hQc]; exact v.isMaximal)`. Establish `hsQ : algebraMap (𝓞 F) (𝓞 E) s ∉ Q` using `fun hq => hs (by rw [← hQc]; exact hq)`.

Establish `hs' : algebraMap (𝓞 F) (𝓞 E) s ∈ hcompl (K` using `E) Q := by`. Apply `Submonoid.subset_closure` to reduce the goal to its premises. Use `⟨hsQ, fun t ht => ?_⟩` and prove the remaining obligations. Establish `e1 : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) s) = algebraMap F E (algebraMap (𝓞 F) F s)`. Rewrite using `[← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E]`.

Establish `: t = algebraMap (𝓞 F) (𝓞 E) s`. Apply `FaithfulSMul.algebraMap_injective (𝓞 E) E` to reduce the goal to its premises. Rewrite using `[ht, e1, hst]`. Rewrite using `[this]`. Conclude with `hsQ`.

Establish `hxX : x ∈ loc (K` using `E) Q X := ⟨_, hs', hsx⟩`. Rewrite `hxX` using `[h Q hQm hQc]`. Take `⟨t, ht, htx⟩` from `hxX`. Use `haveI := hQm.isPrime`. Conclude with `(hcompl_le_primeCompl Q ht) (hIQ htx)`.
-/
theorem hermToF (hst : ∀ a : F, star (algebraMap F E a) = algebraMap F E a)
    (v : HeightOneSpectrum (𝓞 F)) (X Y : Submodule (𝓞 E) V)
    (h : ∀ p : Ideal (𝓞 E), p.IsMaximal → p.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal →
      loc (K := E) p X = loc (K := E) p Y) : Floc v X ⊆ Floc v Y := by
  rintro x ⟨s, hs, hsx⟩
  classical
  let I : Ideal (𝓞 E) := Y.comap (LinearMap.toSpanSingleton (𝓞 E) V x)
  by_contra hno
  have hle : I.comap (algebraMap (𝓞 F) (𝓞 E)) ≤ v.asIdeal := by
    intro a ha
    by_contra hav
    exact hno ⟨a, hav, ha⟩
  obtain ⟨Q, hIQ, hQp, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal I hle
  have hQm : Q.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := 𝓞 F) Q (by rw [hQc]; exact v.isMaximal)
  have hsQ : algebraMap (𝓞 F) (𝓞 E) s ∉ Q := fun hq => hs (by rw [← hQc]; exact hq)
  have hs' : algebraMap (𝓞 F) (𝓞 E) s ∈ hcompl (K := E) Q := by
    apply Submonoid.subset_closure
    refine ⟨hsQ, fun t ht => ?_⟩
    have e1 : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) s) = algebraMap F E (algebraMap (𝓞 F) F s) := by
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E]
    have : t = algebraMap (𝓞 F) (𝓞 E) s := by
      apply FaithfulSMul.algebraMap_injective (𝓞 E) E
      rw [ht, e1, hst]
    rw [this]
    exact hsQ
  have hxX : x ∈ loc (K := E) Q X := ⟨_, hs', hsx⟩
  rw [h Q hQm hQc] at hxX
  obtain ⟨t, ht, htx⟩ := hxX
  haveI := hQm.isPrime
  exact (hcompl_le_primeCompl Q ht) (hIQ htx)

end Over

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ hθ hsymm hnd hL N hN T`. Use `set P := (primesOver_finite (E := E) T).toFinset with hP`. Take `⟨γ, hγ⟩` from `hH F E σ V h M b L0 hσ hθ hsymm hnd hL N hN P (fun p hp => ((Set.Finite.mem_toFinset _).1 hp).1)`. Use `⟨γ, fun v hv => ?_⟩` and prove the remaining obligations. Establish `hst : ∀ a : F, star (algebraMap F E a) = algebraMap F E a` using `fun a => by`.

Rewrite using `[← hσ, AlgHom.commutes]`. Establish `hpv : ∀ p : Ideal (𝓞 E), p.IsMaximal → p.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal → loc (K` using `E) p (gmap (linOf b (γ : GL (Fin M) E)) L0) = loc (K := E) p N := fun p hp hc => hγ p ((Set.Finite.mem_toFinset _).2 ⟨hp, v, hv, hc⟩)`. Conclude with `Set.Subset.antisymm (hermToF hst v _ _ hpv) (hermToF hst v _ _ (fun p hp hc => (hpv p hp hc).symm))`.
-/
theorem semiApprox_of (hH : HermApprox) : SemiApprox := by
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ hθ hsymm hnd hL N hN T
  classical
  set P := (primesOver_finite (E := E) T).toFinset with hP
  obtain ⟨γ, hγ⟩ := hH F E σ V h M b L0 hσ hθ hsymm hnd hL N hN P
    (fun p hp => ((Set.Finite.mem_toFinset _).1 hp).1)
  refine ⟨γ, fun v hv => ?_⟩
  have hst : ∀ a : F, star (algebraMap F E a) = algebraMap F E a := fun a => by
    rw [← hσ, AlgHom.commutes]
  have hpv : ∀ p : Ideal (𝓞 E), p.IsMaximal → p.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal →
      loc (K := E) p (gmap (linOf b (γ : GL (Fin M) E)) L0) = loc (K := E) p N :=
    fun p hp hc => hγ p ((Set.Finite.mem_toFinset _).2 ⟨hp, v, hv, hc⟩)
  exact Set.Subset.antisymm (hermToF hst v _ _ hpv) (hermToF hst v _ _ (fun p hp hc => (hpv p hp hc).symm))

/- English proof (translation)
The claim follows from `surjStep_of_F hP (semiApprox_of hH) hO`.
-/
theorem surjStep_of_patchF_herm (hP : PatchF) (hH : HermApprox) (hO : LSOne) : SurjStep :=
  surjStep_of_F hP (semiApprox_of hH) hO

end PI.UnitaryGroupMassFormula.UJClassMass

end
