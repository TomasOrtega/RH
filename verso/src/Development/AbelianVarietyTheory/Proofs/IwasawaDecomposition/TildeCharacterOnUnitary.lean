import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjQuotientOfRationalUnitaryDeterminantMaStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDeterminantKernelOpenAndFactorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleCharacterTrivialOnLocalUnitsStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical

namespace GlobalTheory.Mem.ChiLaws

/- English proof (translation)
Establish `h : ((infDiag k : Ideles L) : AdeleRing (𝓞 L) L) = (algebraMap L (InfiniteAdeleRing L) k, 1)`. Unfold `infDiag`. Rewrite using `[MonoidHom.finsetProd_apply, Units.coe_prod]`. Set `ι : (∀ w : InfinitePlace L, w.Completion) →* AdeleRing (𝓞 L) L` to `MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)`. Express the relevant statement in the definitionally equal form `∏ w : InfinitePlace L, ι (Pi.mulSingle w (algebraMap L w.Completion k)) = ι (fun w => algebraMap L w.Completion k)`.

Rewrite using `[← map_prod, Finset.univ_prod_mulSingle]`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, h]`. Conclude with `Prod.ext (mul_one _) (one_mul _)`.
-/
theorem infDiag_mul_finPart {L : Type} [Field L] [NumberField L] (k : Lˣ) :
    infDiag k * finPartI L (diagUnits L k) = diagUnits L k := by
  have h : ((infDiag k : Ideles L) : AdeleRing (𝓞 L) L) = (algebraMap L (InfiniteAdeleRing L) k, 1) := by
    unfold infDiag
    rw [MonoidHom.finsetProd_apply, Units.coe_prod]
    let ι : (∀ w : InfinitePlace L, w.Completion) →* AdeleRing (𝓞 L) L :=
      MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)
    change ∏ w : InfinitePlace L, ι (Pi.mulSingle w (algebraMap L w.Completion k)) =
      ι (fun w => algebraMap L w.Completion k)
    rw [← map_prod, Finset.univ_prod_mulSingle]
  apply Units.ext
  rw [Units.val_mul, h]
  exact Prod.ext (mul_one _) (one_mul _)

/- English proof (translation)
Establish `hc : starRingEnd ℂ a ≠ 0` using `by simpa using ha`. Rewrite using `[zpow_ofNat, div_pow, ← Complex.mul_conj', div_eq_iff (mul_ne_zero ha hc)]`. Take the linear combination `(-a) * h`.
-/
theorem phase_sq {a u : ℂ} (ha : a ≠ 0) (h : u * starRingEnd ℂ a = a) :
    (a / ((‖a‖ : ℝ) : ℂ)) ^ (2 : ℤ) = u := by
  have hc : starRingEnd ℂ a ≠ 0 := by simpa using ha
  rw [zpow_ofNat, div_pow, ← Complex.mul_conj', div_eq_iff (mul_ne_zero ha hc)]
  linear_combination (-a) * h

/- English proof (translation)
Establish `hK : KD H ≤ (χ.1.comp (finPartI H.E)).ker` using `(GlobalTheory.T.unitaryDeterminantKernel_open_and_factor R H).2.2.2 χ hχ.triv (fun v => (hχ.unr v).levelLe 1) (fun v _ => hχ.unr v)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Take `⟨a, ha, rfl⟩` from `(mem_UOT H).1 hx`. Rewrite using `[tildeD_mk H hK]`.

Use `GlobalTheory.T.idele_character_trivial_on_local_units H.E χ.1 χ.2.1 _ (finPartI_mem_unitIdl.2 ha) (fun _ => rfl) fun v y hy => ?_` and prove the remaining obligations. Use `hχ.unr v y ?_` and prove the remaining obligations. Unfold `IsUnitAt`. Rewrite using `[hy]`. Conclude with `ha v`.

Use `letI := H.cmStar`. Introduce `z`. Take `⟨h1, h2⟩` from `GlobalTheory.T.exists_conj_quotient_of_rationalUnitaryDeterminantMap R H`. Take `⟨k, hk⟩` from `h2 z`. Rewrite using `[← h1 k z hk, tildeD_mk H hK]`.

Establish `e` using `congrArg χ.1 (infDiag_mul_finPart k)`. Rewrite `e` using `[map_mul, χ.2.2 k, mul_comm, mul_eq_one_iff_eq_inv]`. Establish `hi : ((χ.1 (infDiag k) : ℂˣ) : ℂ) = _` using `hχ.inf k`. Rewrite using `[e, Units.val_inv_eq_inv_val, hi, ← Finset.prod_inv_distrib]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Use `congr 1`. Use `phase_sq ((map_ne_zero _).2 k.ne_zero) ?_` and prove the remaining obligations. Establish `hc : embPsi H τ (H.conj (k : H.E)) = starRingEnd ℂ (embPsi H τ (k : H.E))` using `H.conjE_apply _ _`. Rewrite using `[← hc]`. Conclude with `(map_mul (embPsi H τ) _ _).symm.trans (congrArg _ hk)`.
-/
theorem chi_laws (R : Ranks) (H : Formalism.BasicNotions.Host R) (χ : HChar H.E) (hχ : IsChiPsi H χ) :
    (∀ x ∈ UOT H, tildeD H χ x = 1) ∧
    (letI := H.cmStar; ∀ z : unitary H.E,
      ((tildeD H χ (e1T H z) : ℂˣ) : ℂ) = ∏ τ : R.Psi, (H.emb (τ : R.GG) (z : H.E))⁻¹) := by
  have hK : KD H ≤ (χ.1.comp (finPartI H.E)).ker :=
    (GlobalTheory.T.unitaryDeterminantKernel_open_and_factor R H).2.2.2 χ hχ.triv (fun v => (hχ.unr v).levelLe 1) (fun v _ => hχ.unr v)
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := (mem_UOT H).1 hx
    rw [tildeD_mk H hK]
    refine GlobalTheory.T.idele_character_trivial_on_local_units H.E χ.1 χ.2.1 _ (finPartI_mem_unitIdl.2 ha) (fun _ => rfl) fun v y hy => ?_
    refine hχ.unr v y ?_
    unfold IsUnitAt
    rw [hy]
    exact ha v
  · letI := H.cmStar
    intro z
    obtain ⟨h1, h2⟩ := GlobalTheory.T.exists_conj_quotient_of_rationalUnitaryDeterminantMap R H
    obtain ⟨k, hk⟩ := h2 z
    rw [← h1 k z hk, tildeD_mk H hK]
    have e := congrArg χ.1 (infDiag_mul_finPart k)
    rw [map_mul, χ.2.2 k, mul_comm, mul_eq_one_iff_eq_inv] at e
    have hi : ((χ.1 (infDiag k) : ℂˣ) : ℂ) = _ := hχ.inf k
    rw [e, Units.val_inv_eq_inv_val, hi, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    congr 1
    refine phase_sq ((map_ne_zero _).2 k.ne_zero) ?_
    have hc : embPsi H τ (H.conj (k : H.E)) = starRingEnd ℂ (embPsi H τ (k : H.E)) :=
      H.conjE_apply _ _
    rw [← hc]
    exact (map_mul (embPsi H τ) _ _).symm.trans (congrArg _ hk)

end GlobalTheory.Mem.ChiLaws
