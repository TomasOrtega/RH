import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsFibreCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial IsDedekindDomain

/- English proof (translation)
Introduce `O _ _ F _ _ _ n P W v hP hPO hW hWmax`. Use `hP` as an intermediate fact. Establish `: W.IsPrime` using `hW.1.1`. Use `set mk : MvPolynomial (Fin n) O →+* MvPolynomial (Fin n) O ⧸ P := Ideal.Quotient.mk P with hmk_def`. Establish `hmk : Function.Surjective mk` using `Ideal.Quotient.mk_surjective`.

Establish `hPW : P ≤ W` using `le_sup_left.trans hW.1.2`. Establish `hvW : Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal ≤ W` using `le_sup_right.trans hW.1.2`. Establish `hker : RingHom.ker mk = P` using `Ideal.mk_ker`. Establish `hQprime : (W.map mk).IsPrime` using `Ideal.map_isPrime_of_surjective hmk (by rw [hker]; exact hPW)`. Set `Q : PrimeSpectrum (MvPolynomial (Fin n) O ⧸ P)` to `⟨W.map mk, hQprime⟩`.

Establish `hcomapQ : (W.map mk).comap mk = W`. Rewrite using `[Ideal.comap_map_of_surjective _ hmk, ← RingHom.ker_eq_comap_bot, hker, sup_eq_left.mpr hPW]`. Establish `halg : algebraMap O (MvPolynomial (Fin n) O ⧸ P) = mk.comp C`. Conclude with `RingHom.ext fun _ => rfl`. Establish `hfin` using `Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) O) (P ⊔ Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal)`.

Set `U : Set (PrimeSpectrum (MvPolynomial (Fin n) O ⧸ P))` to `{q | ∀ W' ∈ (P ⊔ Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal).minimalPrimes, W' ≠ W → ¬ W' ≤ q.asIdeal.comap mk}`. Establish `hU : IsOpen U`. Establish `hUc : Uᶜ = ⋃ W' ∈ {W' | W' ∈ (P ⊔ Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal).minimalPrimes ∧ W' ≠ W}, PrimeSpectrum.zeroLocus ((W'.map mk : Ideal (MvPolynomial (Fin n) O ⧸ P)) : Set _)`. Use extensionality with `q`. Simplify using `only [U, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_not, Set.mem_iUnion, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.map_le_iff_le_comap, exists_prop, and_assoc]`.

Rewrite using `[← isClosed_compl_iff, hUc]`. Conclude with `Set.Finite.isClosed_biUnion (hfin.subset fun _ h => h.1) fun _ _ => PrimeSpectrum.isClosed_zeroLocus _`. Establish `hiso : IsOpen (X` using `PrimeSpectrum.comap (algebraMap O (MvPolynomial (Fin n) O ⧸ P)) ⁻¹' {Q.comap (algebraMap O (MvPolynomial (Fin n) O ⧸ P))}) {⟨Q, rfl⟩} := by`. Use `isOpen_induced_iff.mpr ⟨U, hU, ?_⟩` and prove the remaining obligations. Use extensionality with `⟨q, hq⟩`.

Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `hqU`. Establish `hq' : q.asIdeal.comap (algebraMap O _) = Q.asIdeal.comap (algebraMap O _)` using `congrArg PrimeSpectrum.asIdeal hq`. Establish `hle : P ⊔ Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal ≤ q.asIdeal.comap mk`.

Use `sup_le ?_ ?_` and prove the remaining obligations. Introduce `x hx show mk x ∈ q.asIdeal`. Rewrite using `[show mk x = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hx]`. Conclude with `q.asIdeal.zero_mem`. Rewrite using `[Ideal.map_le_iff_le_comap, Ideal.comap_comap, ← halg, hq', halg, ← Ideal.comap_comap] show v.asIdeal ≤ ((W.map mk).comap mk).comap C`.

Rewrite using `[hcomapQ, ← Ideal.map_le_iff_le_comap]`. Conclude with `hvW`. Take `⟨W'', hW'', hW''le⟩` from `Ideal.exists_minimalPrimes_le hle`. Establish `hW''W : W'' = W`. Assume the negation of the conclusion as `hne`.

Conclude with `hqU W'' hW'' hne hW''le`. Rewrite `hW''le` using `[hW''W]`. Establish `heq : W = q.asIdeal.comap mk` using `hWmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hW''le`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `PrimeSpectrum.ext` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `q.asIdeal = W.map mk`. Rewrite using `[heq, Ideal.map_comap_of_surjective _ hmk]`. Introduce `h`. Take `rfl : q = Q` from `congrArg Subtype.val h`. Introduce `W' hW' hne hle`.

Express the relevant statement in the definitionally equal form `W' ≤ (W.map mk).comap mk at hle`. Rewrite `hle` using `[hcomapQ]`. Conclude with `hne (le_antisymm hle (hW.2 hW'.1 hle))`. Establish `: Algebra.QuasiFiniteAt O Q.asIdeal` using `(Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber Q).mpr hiso`. Take `⟨r, hrQ, hr, hm⟩` from `Algebra.zariskisMainProperty_iff.mp (Algebra.ZariskisMainProperty.of_finiteType (R := O) Q.asIdeal)`.

Establish `hr0 : r ≠ 0` using `fun h => hrQ (h ▸ Q.asIdeal.zero_mem)`. Establish `hDalg : ∀ d : MvPolynomial (Fin n) O ⧸ P, IsAlgebraic O d`. Introduce `d`. Take `⟨m, hm⟩` from `hm d`. Conclude with `IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero m hr0)) (hr.pow m).isAlgebraic hm.isAlgebraic`.

Establish `hIprime : (P.map (MvPolynomial.map (algebraMap O F) : MvPolynomial (Fin n) O →+* MvPolynomial (Fin n) F)).IsPrime`. Set `_` to `MvPolynomial.algebraMvPolynomial (σ := Fin n) (R := O) (S := F)`. Establish `hloc : IsLocalization ((nonZeroDivisors O).map (C : O →+* MvPolynomial (Fin n) O)) (MvPolynomial (Fin n) F)` using `MvPolynomial.isLocalization _ _`. Use `IsLocalization.isPrime_of_isPrime_disjoint ((nonZeroDivisors O).map (C : O →+* MvPolynomial (Fin n) O)) (MvPolynomial (Fin n) F) P hP ?_` and prove the remaining obligations. Rewrite using `[Set.disjoint_left]`.

Introduce and unpack `x hx hxP`. Take `⟨c, hc, rfl⟩` from `Submonoid.mem_map.mp hx`. Establish `hcP : c ∈ P.comap (C : O →+* MvPolynomial (Fin n) O)` using `hxP`. Rewrite `hcP` using `[hPO, Ideal.mem_bot]`. Conclude with `nonZeroDivisors.ne_zero hc hcP`.

Set `I` to `P.map (MvPolynomial.map (algebraMap O F) : MvPolynomial (Fin n) O →+* MvPolynomial (Fin n) F)`. Set `φ : (MvPolynomial (Fin n) O ⧸ P) →ₐ[O] (MvPolynomial (Fin n) F ⧸ I)` to `Ideal.quotientMapₐ I (MvPolynomial.mapAlgHom (Algebra.ofId O F)) Ideal.le_comap_map`. Establish `hX : ∀ i, IsIntegral F (Ideal.Quotient.mk I (X i))`. Introduce `i`. Establish `h : Ideal.Quotient.mk I (X i) = φ (Ideal.Quotient.mk P (X i))` using `by show _ = Ideal.Quotient.mk I (MvPolynomial.map (algebraMap O F) (X i))`.

Rewrite using `[MvPolynomial.map_X]`. Rewrite using `[h]`. Conclude with `(((hDalg _).algHom φ).extendScalars (IsFractionRing.injective O F)).isIntegral`. Establish `hint : ∀ x : MvPolynomial (Fin n) F ⧸ I, IsIntegral F x`. Introduce `x`.

Take `⟨p, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a => exact isIntegral_algebraMap`. Consider the case `add p q hp hq => rw [map_add]`. Conclude with `hp.add hq`.

Consider the case `mul_X p i hp => rw [map_mul]`. Conclude with `hp.mul (hX i)`. Establish `: Algebra.IsIntegral F (MvPolynomial (Fin n) F ⧸ I)` using `⟨hint⟩`. Establish `hfield : IsField (MvPolynomial (Fin n) F ⧸ I)` using `(Algebra.IsIntegral.isField_iff_isField (algebraMap F _).injective).mp (Field.toIsField F)`. Conclude with `ringKrullDim_eq_zero_of_isField hfield`.
-/
theorem FibreClosedComponent.proof : FibreClosedComponent.Statement := by
  intro O _ _ F _ _ _ n P W v hP hPO hW hWmax
  classical
  have := hP
  have : W.IsPrime := hW.1.1

  set mk : MvPolynomial (Fin n) O →+* MvPolynomial (Fin n) O ⧸ P := Ideal.Quotient.mk P with hmk_def
  have hmk : Function.Surjective mk := Ideal.Quotient.mk_surjective
  have hPW : P ≤ W := le_sup_left.trans hW.1.2
  have hvW : Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal ≤ W := le_sup_right.trans hW.1.2
  have hker : RingHom.ker mk = P := Ideal.mk_ker
  have hQprime : (W.map mk).IsPrime := Ideal.map_isPrime_of_surjective hmk (by rw [hker]; exact hPW)
  let Q : PrimeSpectrum (MvPolynomial (Fin n) O ⧸ P) := ⟨W.map mk, hQprime⟩
  have hcomapQ : (W.map mk).comap mk = W := by
    rw [Ideal.comap_map_of_surjective _ hmk, ← RingHom.ker_eq_comap_bot, hker, sup_eq_left.mpr hPW]
  have halg : algebraMap O (MvPolynomial (Fin n) O ⧸ P) = mk.comp C := by
    exact RingHom.ext fun _ => rfl

  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) O)
    (P ⊔ Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal)
  let U : Set (PrimeSpectrum (MvPolynomial (Fin n) O ⧸ P)) :=
    {q | ∀ W' ∈ (P ⊔ Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal).minimalPrimes,
      W' ≠ W → ¬ W' ≤ q.asIdeal.comap mk}
  have hU : IsOpen U := by
    have hUc : Uᶜ = ⋃ W' ∈ {W' | W' ∈ (P ⊔ Ideal.map (C : O →+* MvPolynomial (Fin n) O)
        v.asIdeal).minimalPrimes ∧ W' ≠ W},
        PrimeSpectrum.zeroLocus ((W'.map mk : Ideal (MvPolynomial (Fin n) O ⧸ P)) : Set _) := by
      ext q
      simp only [U, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_not, Set.mem_iUnion,
        PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.map_le_iff_le_comap, exists_prop,
        and_assoc]
    rw [← isClosed_compl_iff, hUc]
    exact Set.Finite.isClosed_biUnion (hfin.subset fun _ h => h.1)
      fun _ _ => PrimeSpectrum.isClosed_zeroLocus _
  have hiso : IsOpen (X := PrimeSpectrum.comap (algebraMap O (MvPolynomial (Fin n) O ⧸ P)) ⁻¹'
      {Q.comap (algebraMap O (MvPolynomial (Fin n) O ⧸ P))}) {⟨Q, rfl⟩} := by
    refine isOpen_induced_iff.mpr ⟨U, hU, ?_⟩
    ext ⟨q, hq⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hqU
      have hq' : q.asIdeal.comap (algebraMap O _) = Q.asIdeal.comap (algebraMap O _) :=
        congrArg PrimeSpectrum.asIdeal hq
      have hle : P ⊔ Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal ≤ q.asIdeal.comap mk := by
        refine sup_le ?_ ?_
        · intro x hx
          show mk x ∈ q.asIdeal
          rw [show mk x = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hx]
          exact q.asIdeal.zero_mem
        · rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, ← halg, hq', halg, ← Ideal.comap_comap]
          show v.asIdeal ≤ ((W.map mk).comap mk).comap C
          rw [hcomapQ, ← Ideal.map_le_iff_le_comap]
          exact hvW
      obtain ⟨W'', hW'', hW''le⟩ := Ideal.exists_minimalPrimes_le hle
      have hW''W : W'' = W := by
        by_contra hne
        exact hqU W'' hW'' hne hW''le
      rw [hW''W] at hW''le
      have heq : W = q.asIdeal.comap mk :=
        hWmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hW''le
      apply Subtype.ext
      apply PrimeSpectrum.ext
      change q.asIdeal = W.map mk
      rw [heq, Ideal.map_comap_of_surjective _ hmk]
    · intro h
      obtain rfl : q = Q := congrArg Subtype.val h
      intro W' hW' hne hle
      change W' ≤ (W.map mk).comap mk at hle
      rw [hcomapQ] at hle
      exact hne (le_antisymm hle (hW.2 hW'.1 hle))
  have : Algebra.QuasiFiniteAt O Q.asIdeal :=
    (Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber Q).mpr hiso

  obtain ⟨r, hrQ, hr, hm⟩ :=
    Algebra.zariskisMainProperty_iff.mp (Algebra.ZariskisMainProperty.of_finiteType (R := O) Q.asIdeal)
  have hr0 : r ≠ 0 := fun h => hrQ (h ▸ Q.asIdeal.zero_mem)
  have hDalg : ∀ d : MvPolynomial (Fin n) O ⧸ P, IsAlgebraic O d := by
    intro d
    obtain ⟨m, hm⟩ := hm d
    exact IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero m hr0))
      (hr.pow m).isAlgebraic hm.isAlgebraic

  have hIprime : (P.map (MvPolynomial.map (algebraMap O F) :
      MvPolynomial (Fin n) O →+* MvPolynomial (Fin n) F)).IsPrime := by
    let _ := MvPolynomial.algebraMvPolynomial (σ := Fin n) (R := O) (S := F)
    have hloc : IsLocalization ((nonZeroDivisors O).map (C : O →+* MvPolynomial (Fin n) O))
        (MvPolynomial (Fin n) F) := MvPolynomial.isLocalization _ _
    refine IsLocalization.isPrime_of_isPrime_disjoint
      ((nonZeroDivisors O).map (C : O →+* MvPolynomial (Fin n) O)) (MvPolynomial (Fin n) F) P hP ?_
    rw [Set.disjoint_left]
    rintro x hx hxP
    obtain ⟨c, hc, rfl⟩ := Submonoid.mem_map.mp hx
    have hcP : c ∈ P.comap (C : O →+* MvPolynomial (Fin n) O) := hxP
    rw [hPO, Ideal.mem_bot] at hcP
    exact nonZeroDivisors.ne_zero hc hcP

  let I := P.map (MvPolynomial.map (algebraMap O F) : MvPolynomial (Fin n) O →+* MvPolynomial (Fin n) F)
  let φ : (MvPolynomial (Fin n) O ⧸ P) →ₐ[O] (MvPolynomial (Fin n) F ⧸ I) :=
    Ideal.quotientMapₐ I (MvPolynomial.mapAlgHom (Algebra.ofId O F)) Ideal.le_comap_map
  have hX : ∀ i, IsIntegral F (Ideal.Quotient.mk I (X i)) := by
    intro i
    have h : Ideal.Quotient.mk I (X i) = φ (Ideal.Quotient.mk P (X i)) := by
      show _ = Ideal.Quotient.mk I (MvPolynomial.map (algebraMap O F) (X i))
      rw [MvPolynomial.map_X]
    rw [h]
    exact (((hDalg _).algHom φ).extendScalars (IsFractionRing.injective O F)).isIntegral
  have hint : ∀ x : MvPolynomial (Fin n) F ⧸ I, IsIntegral F x := by
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    induction p using MvPolynomial.induction_on with
    | C a => exact isIntegral_algebraMap
    | add p q hp hq => rw [map_add]; exact hp.add hq
    | mul_X p i hp => rw [map_mul]; exact hp.mul (hX i)
  have : Algebra.IsIntegral F (MvPolynomial (Fin n) F ⧸ I) := ⟨hint⟩
  have hfield : IsField (MvPolynomial (Fin n) F ⧸ I) :=
    (Algebra.IsIntegral.isField_iff_isField (algebraMap F _).injective).mp (Field.toIsField F)
  exact ringKrullDim_eq_zero_of_isField hfield

end GroundTheory.Heights₂.Heights.Vertical
