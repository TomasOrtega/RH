import Mathlib
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
import ReciprocityTheory.AnalyticForms.RegularLocalRings.BaseChangeCB
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial

namespace BaseChangeMin

variable {σ : Type*} [Fintype σ] {F : Type*} [Field F] {F' : Type*} [Field F'] [Algebra F F']

section GD

attribute [local instance] MvPolynomial.algebraMvPolynomial

omit [Fintype σ] in

/- English proof (translation)
The claim follows from `Module.Flat.isBaseChange F (MvPolynomial σ F) F' (MvPolynomial σ F') (Algebra.IsPushout.out (R := F) (S := MvPolynomial σ F) (R' := F') (S' := MvPolynomial σ F'))`.
-/
theorem flat_mvPolynomial_map :
    Module.Flat (MvPolynomial σ F) (MvPolynomial σ F') :=
  Module.Flat.isBaseChange F (MvPolynomial σ F) F' (MvPolynomial σ F')
    (Algebra.IsPushout.out (R := F) (S := MvPolynomial σ F) (R' := F') (S' := MvPolynomial σ F'))

omit [Fintype σ] in

/- English proof (translation)
Use `flat_mvPolynomial_map (σ := σ) (F := F) (F' := F')` as an intermediate fact. Establish `hQp : Q.IsPrime` using `hQ.1.1`. Establish `hle : Ideal.map (algebraMap (MvPolynomial σ F) (MvPolynomial σ F')) 𝔭 ≤ Q` using `hQ.1.2`. Use `set q := Q.comap (algebraMap (MvPolynomial σ F) (MvPolynomial σ F')) with hq`. Establish `: q.IsPrime` using `Ideal.comap_isPrime _ _`.

Establish `: Q.LiesOver q` using `⟨rfl⟩`. Establish `hpq : 𝔭 ≤ q` using `Ideal.map_le_iff_le_comap.mp hle`. Take `⟨P, hPQ, hP, hPl⟩` from `Ideal.exists_ideal_le_liesOver_of_le (p := 𝔭) Q hpq`. Establish `hPext : Ideal.map (MvPolynomial.map (algebraMap F F')) 𝔭 ≤ P`. Rewrite using `[Ideal.map_le_iff_le_comap]`.

Conclude with `hPl.over.le`. Establish `hQP : Q ≤ P` using `hQ.2 ⟨hP, hPext⟩ hPQ`. Establish `hPQe : P = Q` using `le_antisymm hPQ hQP`. Substitute `hPQe` using the available equality. Conclude with `hPl.over.symm`.
-/
theorem comap_of_mem_minimalPrimes_map (𝔭 : Ideal (MvPolynomial σ F)) [𝔭.IsPrime]
    (Q : Ideal (MvPolynomial σ F'))
    (hQ : Q ∈ (Ideal.map (MvPolynomial.map (algebraMap F F')) 𝔭).minimalPrimes) :
    Q.comap (MvPolynomial.map (algebraMap F F')) = 𝔭 := by
  have := flat_mvPolynomial_map (σ := σ) (F := F) (F' := F')
  have hQp : Q.IsPrime := hQ.1.1
  have hle : Ideal.map (algebraMap (MvPolynomial σ F) (MvPolynomial σ F')) 𝔭 ≤ Q := hQ.1.2
  set q := Q.comap (algebraMap (MvPolynomial σ F) (MvPolynomial σ F')) with hq
  have : q.IsPrime := Ideal.comap_isPrime _ _
  have : Q.LiesOver q := ⟨rfl⟩
  have hpq : 𝔭 ≤ q := Ideal.map_le_iff_le_comap.mp hle
  obtain ⟨P, hPQ, hP, hPl⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := 𝔭) Q hpq
  have hPext : Ideal.map (MvPolynomial.map (algebraMap F F')) 𝔭 ≤ P := by
    rw [Ideal.map_le_iff_le_comap]
    exact hPl.over.le
  have hQP : Q ≤ P := hQ.2 ⟨hP, hPext⟩ hPQ
  have hPQe : P = Q := le_antisymm hPQ hQP
  subst hPQe
  exact hPl.over.symm

/- English proof (translation)
Use `flat_mvPolynomial_map (σ := σ) (F := F) (F' := F')` as an intermediate fact. Establish `: Q.IsPrime` using `hQ.1.1`. Establish `hc` using `comap_of_mem_minimalPrimes_map 𝔭 Q hQ`. Establish `: Q.LiesOver 𝔭` using `⟨hc.symm⟩`. Rewrite using `[Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown 𝔭 Q]`.

Establish `h0 : (Q.map (Ideal.Quotient.mk (𝔭.map (algebraMap (MvPolynomial σ F) (MvPolynomial σ F'))))).height = 0`. Establish `hQ' : Q ∈ (𝔭.map (algebraMap (MvPolynomial σ F) (MvPolynomial σ F'))).minimalPrimes` using `hQ`. Rewrite `hQ'` using `[Ideal.minimalPrimes_eq_comap]`. Take `⟨Q', hQ'm, hQ'e⟩` from `hQ'`. Establish `: Q'.IsPrime` using `hQ'm.1.1`.

Rewrite using `[← hQ'e, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]`. Conclude with `Ideal.height_eq_zero_iff.mpr hQ'm`. Rewrite using `[h0, add_zero]`.
-/
theorem height_eq_of_mem_minimalPrimes_map (𝔭 : Ideal (MvPolynomial σ F)) [𝔭.IsPrime]
    (Q : Ideal (MvPolynomial σ F'))
    (hQ : Q ∈ (Ideal.map (MvPolynomial.map (algebraMap F F')) 𝔭).minimalPrimes) :
    Q.height = 𝔭.height := by
  have := flat_mvPolynomial_map (σ := σ) (F := F) (F' := F')
  have : Q.IsPrime := hQ.1.1
  have hc := comap_of_mem_minimalPrimes_map 𝔭 Q hQ
  have : Q.LiesOver 𝔭 := ⟨hc.symm⟩
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown 𝔭 Q]
  have h0 : (Q.map (Ideal.Quotient.mk
      (𝔭.map (algebraMap (MvPolynomial σ F) (MvPolynomial σ F'))))).height = 0 := by
    have hQ' : Q ∈ (𝔭.map (algebraMap (MvPolynomial σ F) (MvPolynomial σ F'))).minimalPrimes := hQ
    rw [Ideal.minimalPrimes_eq_comap] at hQ'
    obtain ⟨Q', hQ'm, hQ'e⟩ := hQ'
    have : Q'.IsPrime := hQ'm.1.1
    rw [← hQ'e, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
    exact Ideal.height_eq_zero_iff.mpr hQ'm
  rw [h0, add_zero]

end GD

/- English proof (translation)
Set `e : MvPolynomial σ k ≃+* MvPolynomial (Fin (Fintype.card σ)) k` to `(MvPolynomial.renameEquiv k (Fintype.equivFin σ)).toRingEquiv`. Establish `: (P.map e).IsPrime` using `Ideal.map_isPrime_of_equiv e`. Establish `h` using `ReciprocityTheory.CA.height_add_ringKrullDim_quotient_mvPolynomial_field k _ (P.map e)`. Rewrite `h` using `[RingEquiv.height_map, ← ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv P (P.map e) e rfl)]`. Conclude with `h`.
-/
theorem height_add_ringKrullDim_quotient (k : Type*) [Field k]
    (P : Ideal (MvPolynomial σ k)) [P.IsPrime] :
    (P.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial σ k ⧸ P) = Fintype.card σ := by
  let e : MvPolynomial σ k ≃+* MvPolynomial (Fin (Fintype.card σ)) k :=
    (MvPolynomial.renameEquiv k (Fintype.equivFin σ)).toRingEquiv
  have : (P.map e).IsPrime := Ideal.map_isPrime_of_equiv e
  have h := ReciprocityTheory.CA.height_add_ringKrullDim_quotient_mvPolynomial_field k _ (P.map e)
  rw [RingEquiv.height_map,
    ← ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv P (P.map e) e rfl)] at h
  exact h

/- English proof (translation)
Establish `: Q.IsPrime` using `hQ.1.1`. Establish `h1` using `height_add_ringKrullDim_quotient F' Q`. Establish `h2` using `height_add_ringKrullDim_quotient F 𝔭`. Rewrite `h1` using `[height_eq_of_mem_minimalPrimes_map 𝔭 Q hQ]`. Conclude with `ReciprocityTheory.AnForm.R.BaseChangeC.withBot_enat_cancel h1 h2`.
-/
theorem ringKrullDim_of_mem_minimalPrimes_map (𝔭 : Ideal (MvPolynomial σ F)) [𝔭.IsPrime]
    (Q : Ideal (MvPolynomial σ F'))
    (hQ : Q ∈ (Ideal.map (MvPolynomial.map (algebraMap F F')) 𝔭).minimalPrimes) :
    ringKrullDim (MvPolynomial σ F' ⧸ Q) = ringKrullDim (MvPolynomial σ F ⧸ 𝔭) := by
  have : Q.IsPrime := hQ.1.1
  have h1 := height_add_ringKrullDim_quotient F' Q
  have h2 := height_add_ringKrullDim_quotient F 𝔭
  rw [height_eq_of_mem_minimalPrimes_map 𝔭 Q hQ] at h1
  exact ReciprocityTheory.AnForm.R.BaseChangeC.withBot_enat_cancel h1 h2

/- English proof (translation)
Rewrite using `[ringKrullDim_quotient, Order.krullDim_eq_iSup_coheight, iSup_le_iff]`. Introduce `a`. Take `⟨Z, hZ, hZa⟩` from `Ideal.exists_minimalPrimes_le ((PrimeSpectrum.mem_zeroLocus _ _).mp a.2)`. Establish `: Z.IsPrime` using `hZ.1.1`. Set `z : PrimeSpectrum.zeroLocus (R` to `R) (I : Set R) := ⟨⟨Z, inferInstance⟩, (PrimeSpectrum.mem_zeroLocus _ _).mpr hZ.1.2⟩`.

Establish `hza : z ≤ a` using `hZa`. Set `e : Set.Ici z ↪o PrimeSpectrum.zeroLocus (R` to `R) (Z : Set R) := OrderEmbedding.ofMapLEIff (fun x => ⟨x.1.1, (PrimeSpectrum.mem_zeroLocus _ _).mpr (show Z ≤ x.1.1.asIdeal from x.2)⟩) fun _ _ => Iff.rfl`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ringKrullDim_quotient_le_of_minimalPrimes {R : Type*} [CommRing R] (I : Ideal R)
    {N : WithBot ℕ∞} (h : ∀ Z ∈ I.minimalPrimes, ringKrullDim (R ⧸ Z) ≤ N) :
    ringKrullDim (R ⧸ I) ≤ N := by
  rw [ringKrullDim_quotient, Order.krullDim_eq_iSup_coheight, iSup_le_iff]
  intro a
  obtain ⟨Z, hZ, hZa⟩ :=
    Ideal.exists_minimalPrimes_le ((PrimeSpectrum.mem_zeroLocus _ _).mp a.2)
  have : Z.IsPrime := hZ.1.1
  let z : PrimeSpectrum.zeroLocus (R := R) (I : Set R) :=
    ⟨⟨Z, inferInstance⟩, (PrimeSpectrum.mem_zeroLocus _ _).mpr hZ.1.2⟩
  have hza : z ≤ a := hZa
  let e : Set.Ici z ↪o PrimeSpectrum.zeroLocus (R := R) (Z : Set R) :=
    OrderEmbedding.ofMapLEIff
      (fun x => ⟨x.1.1, (PrimeSpectrum.mem_zeroLocus _ _).mpr (show Z ≤ x.1.1.asIdeal from x.2)⟩)
      fun _ _ => Iff.rfl
  calc ((Order.coheight a : ℕ∞) : WithBot ℕ∞) ≤ ((Order.coheight z : ℕ∞) : WithBot ℕ∞) :=
        WithBot.coe_le_coe.mpr (Order.coheight_anti hza)
    _ = Order.krullDim (Set.Ici z) := Order.coheight_eq_krullDim_Ici z
    _ ≤ Order.krullDim (PrimeSpectrum.zeroLocus (R := R) (Z : Set R)) :=
        Order.krullDim_le_of_orderEmbedding e
    _ = ringKrullDim (R ⧸ Z) := (ringKrullDim_quotient Z).symm
    _ ≤ N := h Z hZ

end BaseChangeMin

end GroundTheory.Heights₂.Heights.Targets
