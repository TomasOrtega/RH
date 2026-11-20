import Formalism.SharpRestriction.GrowthBounds.RootWeights.OperatorsKillInvariantProjection

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

/- English proof (translation)
Establish `hO : CharZero O`. Break down `S with ⟨w, hw, hpm, hp0, -⟩` into its components or cases. Break down `CharP.char_is_prime_or_zero O (ringChar O) with hq | hq` into its components or cases. It suffices to derive a contradiction. Establish `hne : p ≠ ringChar O`.

Introduce and unpack `h`. Apply `hp0` to reduce the goal to its premises. Rewrite using `[h]`. Conclude with `CharP.cast_eq_zero O (ringChar O)`. Establish `hcop : Nat.gcd p (ringChar O) = 1` using `(Nat.coprime_primes hp hq).mpr hne`.

Establish `key : (1 : O) = (p : O) * (Nat.gcdA p (ringChar O) : O)`. Establish `h` using `congrArg (fun z : ℤ => (z : O)) (Nat.gcd_eq_gcd_ab p (ringChar O))`. Simplify using `only [hcop, Nat.cast_one, Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast, CharP.cast_eq_zero, zero_mul, add_zero] at h`. Conclude with `h`. Establish `h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O` using `key ▸ Ideal.mul_mem_right _ _ hpm`.

Conclude with `(IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).mpr h1)`. Use `haveI : CharP O 0 := hq ▸ ringChar.charP O`. Conclude with `CharP.charP_to_charZero O`. Conclude with `charZero_of_injective_algebraMap (IsFractionRing.injective O (KK O))`.
-/
theorem charZero_fraction_field_of_setting {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (S : UniformizedDVR p O) (hp : p.Prime) : CharZero (KK O) := by
  have hO : CharZero O := by
    rcases S with ⟨w, hw, hpm, hp0, -⟩
    rcases CharP.char_is_prime_or_zero O (ringChar O) with hq | hq
    · exfalso
      have hne : p ≠ ringChar O := by
        rintro h
        apply hp0
        rw [h]
        exact CharP.cast_eq_zero O (ringChar O)
      have hcop : Nat.gcd p (ringChar O) = 1 := (Nat.coprime_primes hp hq).mpr hne
      have key : (1 : O) = (p : O) * (Nat.gcdA p (ringChar O) : O) := by
        have h := congrArg (fun z : ℤ => (z : O)) (Nat.gcd_eq_gcd_ab p (ringChar O))
        simp only [hcop, Nat.cast_one, Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast,
          CharP.cast_eq_zero, zero_mul, add_zero] at h
        exact h
      have h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O := key ▸ Ideal.mul_mem_right _ _ hpm
      exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    · haveI : CharP O 0 := hq ▸ ringChar.charP O
      exact CharP.charP_to_charZero O
  exact charZero_of_injective_algebraMap (IsFractionRing.injective O (KK O))

/- English proof (translation)
Unfold `IsSubrepresentation cyclicSubmodule`. Introduce `a b x hx`. Establish `hle : Submodule.span K {x | ∃ u ∈ Umon E, x = u v} ≤ (Submodule.span K {x | ∃ u ∈ Umon E, x = u v}).comap (E a b)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `y ⟨u, hu, rfl⟩`.

Simplify using `only [SetLike.mem_coe, Submodule.mem_comap]`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨E a b * u, ?_, rfl⟩` and prove the remaining obligations. Unfold `Umon at hu ⊢`. Conclude with `Submonoid.mul_mem _ (Submonoid.subset_closure ⟨(a, b), rfl⟩) hu`.

Conclude with `hle hx`.
-/
theorem cyclicSubmodule_isSubrepresentation {n : ℕ} {K V : Type} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V) (v : V) :
    IsSubrepresentation E (cyclicSubmodule E v) := by
  unfold IsSubrepresentation cyclicSubmodule
  intro a b x hx
  have hle : Submodule.span K {x | ∃ u ∈ Umon E, x = u v} ≤
      (Submodule.span K {x | ∃ u ∈ Umon E, x = u v}).comap (E a b) := by
    rw [Submodule.span_le]
    rintro y ⟨u, hu, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap]
    apply Submodule.subset_span
    refine ⟨E a b * u, ?_, rfl⟩
    unfold Umon at hu ⊢
    exact Submonoid.mul_mem _ (Submonoid.subset_closure ⟨(a, b), rfl⟩) hu
  exact hle hx

/- English proof (translation)
Unfold `deF`. Conclude with `Nat.log_mono_right (by omega)`.
-/
theorem log_bound_monotone (p n : ℕ) {k l : ℕ} (h : k ≤ l) : deF p n k ≤ deF p n l := by
  unfold deF
  exact Nat.log_mono_right (by omega)

/- English proof (translation)
Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hab`. Rewrite using `[pow_add, mul_comm, mul_smul]`. Conclude with `M.smul_mem _ h`.
-/
theorem pow_smul_mem_of_le' {O W : Type} [CommRing O] [AddCommGroup W] [Module O W] (M : Submodule O W) (c : O) {a b : ℕ}
    (hab : a ≤ b) {z : W} (h : c ^ a • z ∈ M) : c ^ b • z ∈ M := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [pow_add, mul_comm, mul_smul]
  exact M.smul_mem _ h

/- English proof (translation)
Use `haveI : CharZero (KK O) := charZero_fraction_field_of_setting S hG.prime`. Distinguish the cases in `hv : ∃ v0, IsHWV E lam v0`. Take `⟨v0, hv0⟩` from `hv`. Establish `hL` using `cyclicSubmodule_isSubrepresentation E v0`. Take `⟨d, b, hbM, hbc⟩` from `hB O V M hM.2 hMQ (cyclicSubmodule E v0)`.

Establish `hEH : IsGLRep (homRepresentation (restrictRepresentation E _ hL) E)` using `hHom n (KK O) _ V _ E (hRes n (KK O) V E hE _ hL) hE`. Take `⟨P, hP⟩` from `hInv n (KK O) _ _ hEH`. Take `⟨hl1, hl2⟩` from `hLat O n V E hE M hM hMQ _ hL`. Establish `key : ∀ i, ((p : O) ^ (N0 n * deF p n (ellOf E (MQ M)))) • P ((b.coord i).smulRight x) (b i) ∈ M`. Introduce `i`.

Establish `hf : (b.coord i).smulRight x ∈ homLattice M (cyclicSubmodule E v0)`. Introduce `y hy`. Take `⟨o, ho⟩` from `hbc y hy i`. Rewrite using `[LinearMap.smulRight_apply, ho, algebraMap_smul]`. Conclude with `M.smul_mem _ hx`.

Establish `h1` using `h p n' O S hG n _ _ hEH _ hl1 hl2 P hP _ hf`. Establish `h2` using `h1 (b i) (hbM i)`. Rewrite `h2` using `[LinearMap.smul_apply]`. Use `pow_smul_mem_of_le' M _ ?_ h2` and prove the remaining obligations. Use `Nat.mul_le_mul_left _ (log_bound_monotone p n ?_)` and prove the remaining obligations.

Rewrite using `[hl2, hMQ]`. Conclude with `hEll n (KK O) V E hE _ hL`. Rewrite using `[← hTh n (KK O) V E hE lam e he v0 hv0 hL P hP (Fin d) b x, Nat.cast_smul_eq_nsmul, smul_comm, Finset.smul_sum]`. Conclude with `M.smul_of_tower_mem _ (M.sum_mem fun i _ => key i)`. Establish `h0 : e x = 0`.

Establish `hle : (⨆ mu, isoSub E mu) ≤ LinearMap.ker e`. Use `iSup_le fun mu => ?_` and prove the remaining obligations. Distinguish the cases in `hmu : mu = lam`. Substitute `hmu` using the available equality. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `y ⟨u, _, v, hv', _⟩`. Conclude with `absurd ⟨v, hv'⟩ hv`. Introduce `y hy`. Conclude with `he.2 mu hmu y hy`. Establish `: x ∈ (⨆ mu, isoSub E mu)` using `by rw [hTop n (KK O) V E hE]; trivial`.

Conclude with `hle this`. Rewrite using `[h0, smul_zero]`. Conclude with `M.zero_mem`.
-/
theorem lattice_theorem_single_rep (h : InvariantDenominatorEllPBound) (hTop : IsotypicSubmodulesSpanTop) (hRes : RestrictionIsRepresentation) (hHom : HomSpaceIsRepresentation) (hInv : InvariantProjectionExists)
    (hTh : IsotypicProjectorTraceFormula) (hB : LatticeAdaptedBasisExists) (hLat : HomLatticeDividedPowerStable) (hEll : HomRepEllBoundedByTarget)
    (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (S : UniformizedDVR p O)
    (hG : AdmissibleDVR p n' O) (n : ℕ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
    [IsScalarTower O (KK O) V] [FiniteDimensional (KK O) V] (E : GLOps n (KK O) V) (hE : IsGLRep E)
    (M : Submodule O V) (hM : UZLattice E M) (hMQ : MQ (K := KK O) M = ⊤)
    (lam : Fin n → ℤ) (e : Module.End (KK O) V) (he : IsIsoProj E lam e) (x : V) (hx : x ∈ M) :
    ((p : O) ^ (N0 n * deF p n (ellOf E (MQ M)))) • e x ∈ M := by
  haveI : CharZero (KK O) := charZero_fraction_field_of_setting S hG.prime
  by_cases hv : ∃ v0, IsHWV E lam v0
  · obtain ⟨v0, hv0⟩ := hv
    have hL := cyclicSubmodule_isSubrepresentation E v0
    obtain ⟨d, b, hbM, hbc⟩ := hB O V M hM.2 hMQ (cyclicSubmodule E v0)
    have hEH : IsGLRep (homRepresentation (restrictRepresentation E _ hL) E) :=
      hHom n (KK O) _ V _ E (hRes n (KK O) V E hE _ hL) hE
    obtain ⟨P, hP⟩ := hInv n (KK O) _ _ hEH
    obtain ⟨hl1, hl2⟩ := hLat O n V E hE M hM hMQ _ hL
    have key : ∀ i, ((p : O) ^ (N0 n * deF p n (ellOf E (MQ M)))) • P ((b.coord i).smulRight x) (b i) ∈ M := by
      intro i
      have hf : (b.coord i).smulRight x ∈ homLattice M (cyclicSubmodule E v0) := by
        intro y hy
        obtain ⟨o, ho⟩ := hbc y hy i
        rw [LinearMap.smulRight_apply, ho, algebraMap_smul]
        exact M.smul_mem _ hx
      have h1 := h p n' O S hG n _ _ hEH _ hl1 hl2 P hP _ hf
      have h2 := h1 (b i) (hbM i)
      rw [LinearMap.smul_apply] at h2
      refine pow_smul_mem_of_le' M _ ?_ h2
      refine Nat.mul_le_mul_left _ (log_bound_monotone p n ?_)
      rw [hl2, hMQ]
      exact hEll n (KK O) V E hE _ hL
    rw [← hTh n (KK O) V E hE lam e he v0 hv0 hL P hP (Fin d) b x, Nat.cast_smul_eq_nsmul, smul_comm,
      Finset.smul_sum]
    exact M.smul_of_tower_mem _ (M.sum_mem fun i _ => key i)
  · have h0 : e x = 0 := by
      have hle : (⨆ mu, isoSub E mu) ≤ LinearMap.ker e := by
        refine iSup_le fun mu => ?_
        by_cases hmu : mu = lam
        · subst hmu
          refine Submodule.span_le.2 ?_
          rintro y ⟨u, _, v, hv', _⟩
          exact absurd ⟨v, hv'⟩ hv
        · intro y hy
          exact he.2 mu hmu y hy
      have : x ∈ (⨆ mu, isoSub E mu) := by rw [hTop n (KK O) V E hE]; trivial
      exact hle this
    rw [h0, smul_zero]; exact M.zero_mem

/- English proof (translation)
Unfold `IsotypicProjectorTheoremField`. Introduce `p n' O _ _ _ S hG n _ V _ _ _ _ _ E hE M hM hMQ Sw _ e he x hx`. Rewrite using `[Finset.smul_sum]`. Use `Submodule.sum_mem _ fun lam hlam => ?_` and prove the remaining obligations. Establish `h1` using `lattice_theorem_single_rep h hTop hRes hHom hInv hTh hB hLat hEll p n' O S hG n V E hE M hM hMQ lam (e lam) (he lam hlam) x hx`.

Use `pow_smul_mem_of_le' M (p : O) ?_ h1` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem lattice_theorem_of_interfaces (D : Formalism.BasicNotions.D7) (h : InvariantDenominatorEllPBound) (hTop : IsotypicSubmodulesSpanTop) (hRes : RestrictionIsRepresentation) (hHom : HomSpaceIsRepresentation)
    (hInv : InvariantProjectionExists) (hTh : IsotypicProjectorTraceFormula) (hB : LatticeAdaptedBasisExists) (hLat : HomLatticeDividedPowerStable) (hEll : HomRepEllBoundedByTarget) :
    IsotypicProjectorTheoremField D := by
  unfold IsotypicProjectorTheoremField
  intro p n' O _ _ _ S hG n _ V _ _ _ _ _ E hE M hM hMQ Sw _ e he x hx
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun lam hlam => ?_
  have h1 := lattice_theorem_single_rep h hTop hRes hHom hInv hTh hB hLat hEll p n' O S hG n V E hE M hM hMQ lam (e lam)
    (he lam hlam) x hx
  refine pow_smul_mem_of_le' M (p : O) ?_ h1
  calc N0 n * deF p n (ellOf E (MQ M)) ≤ N0 n * deF p n (ellOf E (MQ M) + ellWt lam) :=
        Nat.mul_le_mul_left _ (log_bound_monotone p n (Nat.le_add_right _ _))
    _ ≤ _ := Finset.le_sup (f := fun lam => N0 n * deF p n (ellOf E (MQ M) + ellWt lam)) hlam

end Formalism.MainNotions.G.GLWeightTheory
