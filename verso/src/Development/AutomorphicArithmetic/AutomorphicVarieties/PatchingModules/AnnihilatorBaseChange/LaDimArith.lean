import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaMvpsCot
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaRegPrime
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplReg
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSurj
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

/- English proof (translation)
A detailed English derivation is pending.
-/
private theorem laDim_co (O : Type) [CommRing O] [IsLocalRing O] (K : Type) [Field K] [Algebra O K]
    (h : Function.Surjective (algebraMap O K)) : IsCO O K where
  toIsLocalRing := inferInstance
  toIsNoetherian := inferInstance
  complete := by
    rw [IsLocalRing.maximalIdeal_eq_bot]
    infer_instance
  isLocalHom := IsLocalHom.of_surjective _ h
  res_surj x := by
    obtain ⟨a, rfl⟩ := h x
    exact ⟨a, by simp⟩

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
private theorem laDim_surj (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] (K : Type) [Field K] [Algebra O K] (σ : Type) [Finite σ] (s : σ)
    (g : MvPowerSeries σ O →ₐ[O] PowerSeries K) (h : Function.Surjective (algebraMap O K))
    (hg : g (MvPowerSeries.X s) = PowerSeries.X) : Function.Surjective g := by
  haveI : IsCO O K := laDim_co O K h
  haveI : IsCO O (MvPowerSeries σ O) := co_mvps O O σ
  haveI : IsCO O (PowerSeries K) := co_mvps O K Unit
  refine co_surj O _ _ g (le_trans ?_ le_sup_left)
  rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.span_le, Set.singleton_subset_iff, ← hg]
  refine Ideal.mem_map_of_mem _ fun hu => ?_
  have := MvPowerSeries.isUnit_constantCoeff _ hu
  simp at this

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
private theorem laDim_arith (x : WithBot ℕ∞) (n : ℕ) (h : x + 1 = ((n + 1 : ℕ) : WithBot ℕ∞)) :
    x = (n : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd h (by rw [WithBot.bot_add]; exact (WithBot.natCast_ne_bot _).symm)
  | coe y =>
    have h' : y + 1 = ((n : ℕ∞) + 1) := by exact_mod_cast h
    have : y = (n : ℕ∞) := WithTop.add_right_cancel ENat.one_ne_top h'
    rw [this]; rfl

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
private theorem laDim_gen (R : Type) [CommRing R] [IsRegularLocalRing R] (S : Type) [CommRing S] [IsDomain S]
    [IsDiscreteValuationRing S] (p : Ideal R) (e : (R ⧸ p) ≃+* S) (n : ℕ)
    (hdim : ringKrullDim R = ((n + 1 : ℕ) : WithBot ℕ∞)) :
    ∃ (La : Type) (_ : CommRing La) (_ : IsLocalRing La) (_ : Algebra R La),
      IsCplAt R p La ∧ IsRegularLocalRing La ∧ ringKrullDim La = (n : WithBot ℕ∞) := by
  haveI : IsDomain (R ⧸ p) := e.toMulEquiv.isDomain _
  haveI hp : p.IsPrime := (Ideal.Quotient.isDomain_iff_prime p).1 inferInstance
  haveI : IsRegularLocalRing (R ⧸ p) := IsRegularLocalRing.of_ringEquiv e.symm
  have hq : ringKrullDim (R ⧸ p) = 1 := by
    rw [ringKrullDim_eq_of_ringEquiv e, IsDiscreteValuationRing.ringKrullDim_eq_one]
  obtain ⟨h1, h2⟩ := regular_localization_of_regular_quotient R p
  have hc := isCplAt_cplAt R p
  obtain ⟨h3, h4⟩ := IsCplAt.regular _ _ _ hc h1
  refine ⟨CplAt R p, inferInstance, inferInstance, inferInstance, hc, h3, ?_⟩
  rw [h4]
  apply laDim_arith
  rw [hq] at h2
  rw [h2, hdim]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Pa.Core.laDim :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (K : Type) [Field K] [Finite K] [Algebra O K] (D : ℕ) (g : abelian₂ O Unit D →ₐ[O] PowerSeries K), Function.Surjective (algebraMap O K) → g (MvPowerSeries.X (.inl ())) = PowerSeries.X → ∃ (La : Type) (_ : CommRing La) (_ : IsLocalRing La) (_ : Algebra (abelian₂ O Unit D) La), IsCplAt (abelian₂ O Unit D) (RingHom.ker g) La ∧ IsRegularLocalRing La ∧ ringKrullDim La = ((1 + D : ℕ) : WithBot ℕ∞) := by
  intro O _ _ _ _ K _ _ _ D g h hg
  have hs : Function.Surjective g := laDim_surj O K _ _ g h hg
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨hreg, hdim, -⟩ := mvPowerSeries_cotInd O ϖ hϖ (Unit ⊕ Fin D)
  haveI : IsRegularLocalRing (abelian₂ O Unit D) := hreg
  refine laDim_gen (abelian₂ O Unit D) (PowerSeries K) (RingHom.ker g)
    (Ideal.quotientKerAlgEquivOfSurjective hs).toRingEquiv (1 + D) ?_
  rw [hdim, Fintype.card_sum, Fintype.card_unit, Fintype.card_fin]
