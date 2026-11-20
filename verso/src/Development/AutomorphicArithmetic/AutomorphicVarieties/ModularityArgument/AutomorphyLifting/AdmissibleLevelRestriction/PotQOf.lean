import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.SplitIrr

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.GalN.V UpperTheory.V.Z.Win

namespace UpperTheory.V.Z.Win.A4

section
variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω]
  {l : ℕ} [Fact l.Prime] {n : ℕ}

/- English proof (translation)
Introduce `x` and use `by rw [IsScalarTower.algebraMap_apply ℚ K Ω] exact h (algebraMap (𝓞 ℚ) (𝓞 K) x)`.
-/
private theorem place_under {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 K)} (h : IsPlaceOver A w) :
    IsPlaceOver A (w.under (𝓞 ℚ)) := fun x => by
  rw [IsScalarTower.algebraMap_apply ℚ K Ω]
  exact h (algebraMap (𝓞 ℚ) (𝓞 K) x)

/- English proof (translation)
Use `haveI := v.isMaximal`. Establish `hker : RingHom.ker (algebraMap (𝓞 ℚ) (𝓞 K)) ≤ v.asIdeal`. Rewrite using `[(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective (𝓞 ℚ) (𝓞 K))]`. Conclude with `bot_le`. Take `⟨M, hM, hc⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) v.asIdeal hker`.

Use `⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField K)⟩, ?_⟩` and prove the remaining obligations. Conclude with `HeightOneSpectrum.ext hc`.
-/
private theorem exists_over (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 ℚ) = v := by
  haveI := v.isMaximal
  have hker : RingHom.ker (algebraMap (𝓞 ℚ) (𝓞 K)) ≤ v.asIdeal := by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective (𝓞 ℚ) (𝓞 K))]
    exact bot_le
  obtain ⟨M, hM, hc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) v.asIdeal hker
  refine ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField K)⟩, ?_⟩
  exact HeightOneSpectrum.ext hc

private def resD (A : ValuationSubring Ω) : ↥(Dec (F := K) A) →* ↥(Dec (F := ℚ) A) where
  toFun u := ⟨(AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω) u, u.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ _ _)

/- English proof (translation)
Set `t : G K Ω` to `{ (s : G ℚ Ω).toRingEquiv with commutes' := h s s.2 }`. Establish `ht : (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω) t = s`. Use extensionality with `x`. Both sides reduce to the same expression. Establish `hm : t ∈ Dec (F` using `K) A := by`.

Use `s.2` as an intermediate fact. Rewrite `this` using `[← ht]`. Conclude with `this`. Conclude with `⟨⟨t, hm⟩, Subtype.ext ht⟩`.
-/
private theorem resD_surj {A : ValuationSubring Ω}
    (h : ∀ g ∈ Dec (F := ℚ) A, ∀ x : K, g (algebraMap K Ω x) = algebraMap K Ω x) (s : ↥(Dec (F := ℚ) A)) :
    ∃ u : ↥(Dec (F := K) A), resD A u = s := by
  let t : G K Ω := { (s : G ℚ Ω).toRingEquiv with commutes' := h s s.2 }
  have ht : (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω) t = s := by
    ext x
    rfl
  have hm : t ∈ Dec (F := K) A := by
    have := s.2
    rw [← ht] at this
    exact this
  exact ⟨⟨t, hm⟩, Subtype.ext ht⟩

/- English proof (translation)
Introduce `A hA`. Establish `hl : A.valuation (l : Ω) < 1`. Simplify using `using (hA ((l : ℕ) : 𝓞 K)).2 hw`. Establish `hv : ((l : ℕ) : 𝓞 ℚ) ∈ (w.under (𝓞 ℚ)).asIdeal` using `Ideal.mem_comap.2 (by simpa using hw)`. Take `⟨κ, ⟨g, hg⟩, hne⟩` from `hU (w.under (𝓞 ℚ)) hv A (place_under hA)`.

Use `⟨fun i => (κ i).comp (resD A), ⟨g, fun u => hg (resD A u)⟩, fun i j e => hne i j ?_⟩` and prove the remaining obligations. Use `MonoidHom.ext fun s => ?_` and prove the remaining obligations. Take `⟨u, rfl⟩` from `resD_surj (hK A hl) s`. Conclude with `DFunLike.congr_fun e u`.
-/
private theorem unl_res (r : G ℚ Ω →* GL (Fin n) (Qbar l))
    (hK : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ g ∈ Dec (F := ℚ) A, ∀ x : K,
      g (algebraMap K Ω x) = algebraMap K Ω x)
    (hU : UnlAll r) (w : HeightOneSpectrum (𝓞 K)) (hw : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal) :
    Unl1 (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) w := by
  intro A hA
  have hl : A.valuation (l : Ω) < 1 := by
    simpa using (hA ((l : ℕ) : 𝓞 K)).2 hw
  have hv : ((l : ℕ) : 𝓞 ℚ) ∈ (w.under (𝓞 ℚ)).asIdeal := Ideal.mem_comap.2 (by simpa using hw)
  obtain ⟨κ, ⟨g, hg⟩, hne⟩ := hU (w.under (𝓞 ℚ)) hv A (place_under hA)
  refine ⟨fun i => (κ i).comp (resD A), ⟨g, fun u => hg (resD A u)⟩, fun i j e => hne i j ?_⟩
  refine MonoidHom.ext fun s => ?_
  obtain ⟨u, rfl⟩ := resD_surj (hK A hl) s
  exact DFunLike.congr_fun e u

end

/- English proof (translation)
Introduce `hF hS Ω _ _ _ l _ ι n r hc hirr haut hU v hv`. Take `⟨K, _, _, _, _, _, hrank, hK, hdec⟩` from `hS Ω l n r hirr`. Establish `hflag : Flagged r` using `fun u hu A hA => (hU u hu A hA).imp fun κ h => h.1`. Take `⟨w, rfl⟩` from `exists_over K v`. Establish `hw : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal` using `by simpa using Ideal.mem_comap.1 hv`.

Establish `hpot` using `(haut hc K hrank hK).2.1 w hw (unl_res r hdec hU w hw)`. Take `⟨-, -, -, hlast⟩` from `hF ℚ Ω l n r`. Conclude with `(((hlast K).2.2 w hw).2 hflag).1 hpot`.
-/
theorem potQ :
    FlagLaws → SplitIrr → PotQ := by
  intro hF hS Ω _ _ _ l _ ι n r hc hirr haut hU v hv
  obtain ⟨K, _, _, _, _, _, hrank, hK, hdec⟩ := hS Ω l n r hirr
  have hflag : Flagged r := fun u hu A hA => (hU u hu A hA).imp fun κ h => h.1
  obtain ⟨w, rfl⟩ := exists_over K v
  have hw : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal := by simpa using Ideal.mem_comap.1 hv
  have hpot := (haut hc K hrank hK).2.1 w hw (unl_res r hdec hU w hw)
  obtain ⟨-, -, -, hlast⟩ := hF ℚ Ω l n r
  exact (((hlast K).2.2 w hw).2 hflag).1 hpot

end UpperTheory.V.Z.Win.A4
