import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.LiftFactorization
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.AvgInt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.OneCoset
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.VolIdx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.SumCoset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularTwistedOrbitLocalFiniteness

noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open scoped Classical ENNReal

namespace UpperTheory.Gal.InertialTypesAlt.L

open PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

/- English proof (translation)
Use `continuous_iff_continuousAt.2 fun x => ?_` and prove the remaining obligations. Establish `hev : F =ᶠ[nhds x] fun _ => F x`. Establish `hop : IsOpen ((fun y => x⁻¹ * y) ⁻¹' (U : Set G))` using `hU.preimage (continuous_const.mul continuous_id)`. Establish `hx : x ∈ (fun y => x⁻¹ * y) ⁻¹' (U : Set G)`. Simplify using `[U.one_mem]`.

Use `filter_upwards [hop.mem_nhds hx] with y hy`. Establish `h1` using `h (x⁻¹ * y) hy x`. Simplify using `using h1`. Conclude with `continuousAt_const.congr hev.symm`.
-/
private theorem continuous_of_rightInv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) (F : G → ℂ) (h : ∀ u ∈ U, ∀ x, F (x * u) = F x) :
    Continuous F := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hev : F =ᶠ[nhds x] fun _ => F x := by
    have hop : IsOpen ((fun y => x⁻¹ * y) ⁻¹' (U : Set G)) :=
      hU.preimage (continuous_const.mul continuous_id)
    have hx : x ∈ (fun y => x⁻¹ * y) ⁻¹' (U : Set G) := by
      simp [U.one_mem]
    filter_upwards [hop.mem_nhds hx] with y hy
    have h1 := h (x⁻¹ * y) hy x
    simpa using h1
  exact continuousAt_const.congr hev.symm

/- English proof (translation)
The claim follows from `(Subgroup.closure_le _).2 fun _ ht => ht.1`.
-/
private theorem cptPart_le {G : Type} [Group G] [TopologicalSpace G] (T : Subgroup G) :
    GlobalTheory.BCT.cptPart T ≤ T :=
  (Subgroup.closure_le _).2 fun _ ht => ht.1

/- English proof (translation)
Unfold `OrbSum`. Introduce `G _ _ _ _ _ _ _ _ μ hμ K hKo hKc hK1 θ hθ δ T hT hcomm hC ν hν U f hU hf hcm`. Substitute `hT` using the available equality. Take `⟨hUo, hUK, hUθ⟩` from `hU`. Take `⟨hfc, hfi⟩` from `hf`.

Use `set F : G → ℂ := fun x => f (x⁻¹ * δ * θ x) with hF`. Establish `hTcl : IsClosed (GlobalTheory.BCT.twCent θ δ : Set G)` using `by show IsClosed {g : G | g * δ = δ * θ g}`. Conclude with `isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul hθ)`. Establish `hFU : ∀ u ∈ U, ∀ x : G, F (x * u) = F x`. Introduce `u hu x`.

Use `show f ((x * u)⁻¹ * δ * θ (x * u)) = f (x⁻¹ * δ * θ x)`. Rewrite using `[_root_.mul_inv_rev, map_mul]`. Establish `h1 : θ u ∈ U` using `hUθ u hu`. Establish `hu' : u⁻¹ ∈ U` using `U.inv_mem hu`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [mul_assoc]`. Use `_ = f (u⁻¹ * (x⁻¹ * δ * θ x)) := (hfi _ h1 _).2`. Use `_ = f (x⁻¹ * δ * θ x) := (hfi _ hu' _).1`. Establish `hFT : ∀ t ∈ GlobalTheory.BCT.twCent θ δ, ∀ x : G, F (t * x) = F x`. Introduce `t ht x`.

Establish `h : t * δ = δ * θ t` using `ht`. Establish `h2 : t⁻¹ * δ * θ t = δ`. Rewrite using `[mul_assoc, ← h, inv_mul_cancel_left]`. Use `show f ((t * x)⁻¹ * δ * θ (t * x)) = f (x⁻¹ * δ * θ x)`. Rewrite using `[_root_.mul_inv_rev, map_mul]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`. Use `_ = f (x⁻¹ * δ * θ x) := by rw [h2]`. Establish `hFc : Continuous F` using `continuous_of_rightInv U hUo F hFU`. Take `⟨_, hsum⟩` from `sumCoset G μ hμ K hKo hKc hK1 _ hTcl hcomm ν hν F hFc hFT hcm`.

Establish `hmapK : ∀ q x : G, x ∈ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj q)) K ↔ q⁻¹ * x * q ∈ K`. Introduce `q x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, hk, rfl⟩`. Simplify `hk` using `[mul_assoc]`.

Introduce `hx`. Conclude with `⟨q⁻¹ * x * q, hx, by simp [mul_assoc]⟩`. Establish `hset : ∀ q : G, {t : GlobalTheory.BCT.twCent θ δ | q⁻¹ * (t : G) * q ∈ K} = {t : GlobalTheory.BCT.twCent θ δ | (t : G) ∈ GlobalTheory.BCT.twCent θ δ ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj q)) K}`. Introduce `q`. Use extensionality with `t`.

Simplify using `only [Set.mem_setOf_eq, Subgroup.mem_inf, hmapK, SetLike.coe_mem, true_and]`. Establish `hopen : ∀ q : G, IsOpen {t : GlobalTheory.BCT.twCent θ δ | (t : G) ∈ GlobalTheory.BCT.twCent θ δ ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj q)) K}`. Introduce `q`. Rewrite using `[← hset q]`. Conclude with `hKo.preimage ((continuous_const.mul continuous_subtype_val).mul continuous_const)`.

Establish `hvol : ∀ q : G, _` using `fun q => volIdx G (GlobalTheory.BCT.twCent θ δ) (GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ)) (GlobalTheory.BCT.twCent θ δ ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj q)) K) hTcl ν hν (cptPart_le _) hC (GlobalTheory.LocFin.inf_le_cptPart _ _ (GlobalTheory.LocFin. …`. Establish `hCfin : ν {t : GlobalTheory.BCT.twCent θ δ | (t : G) ∈ GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ)} ≠ ⊤` using `((hTcl.isClosedEmbedding_subtypeVal).isCompact_preimage hC).measure_lt_top.ne`. Establish `hCne : ν.real {t : GlobalTheory.BCT.twCent θ δ | (t : G) ∈ GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ)} ≠ 0`. Establish `h1` using `(hvol 1).1`. Establish `hsub : {t : GlobalTheory.BCT.twCent θ δ | (t : G) ∈ GlobalTheory.BCT.twCent θ δ ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (1 : G))) K} ⊆ {t : GlobalTheory.BCT.twCent θ δ | (t : G) ∈ GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ)}` using `fun t ht => GlobalTheory.LocFin.inf_le_cptPart _ _ (GlobalTheory.LocFin.isCompact_map_conj K hKc 1) ht`.

Establish `h2` using `measureReal_mono hsub hCfin`. Introduce `h0`. Conclude with `h1 (le_antisymm (h0 ▸ h2) measureReal_nonneg)`. Use `⟨hCne, ?_⟩` and prove the remaining obligations. Rewrite using `[hsum]`.

Unfold `GlobalTheory.BCT.twOrb`. Rewrite using `[mul_finsum]`. Use `finsum_congr fun q => ?_` and prove the remaining obligations. Take `⟨hH0, hCeq⟩` from `hvol (Quotient.out q)`. Establish `hidx : ((GlobalTheory.BCT.twCent θ δ ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (Quotient.out q))) K).relIndex (GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ)) : ℝ) ≠ 0` using `fun h0 => hCne (by rw [hCeq, h0, zero_mul])`.

Rewrite using `[oneCoset G μ hμ K hKo hKc hK1 _ hTcl hcomm ν hν F hFc hFT (Quotient.out q)]`. Rewrite using `[← avgInt G μ hμ K hKo hKc hK1 U hUo F hFU (Quotient.out q)]`. Rewrite using `[hset, hCeq]`. Rewrite using `[show (fun y : K => F (Quotient.out q * ↑y)) = fun k : K => f ((Quotient.out q * ↑k)⁻¹ * δ * θ (Quotient.out q * ↑k)) from rfl]`. Establish `hidxC : ((GlobalTheory.BCT.twCent θ δ ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (Quotient.out q))) K).relIndex (GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ)) : ℂ) ≠ 0` using `by exact_mod_cast hidx`.

Establish `hHC : ((ν.real {t : GlobalTheory.BCT.twCent θ δ | (t : G) ∈ GlobalTheory.BCT.twCent θ δ ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (Quotient.out q))) K} : ℝ) : ℂ) ≠ 0`. Conclude with `hH0` after adjusting the coercions. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem orbSum : OrbSum := by
  unfold OrbSum
  intro G _ _ _ _ _ _ _ _ μ hμ K hKo hKc hK1 θ hθ δ T hT hcomm hC ν hν U f hU hf hcm
  subst hT
  obtain ⟨hUo, hUK, hUθ⟩ := hU
  obtain ⟨hfc, hfi⟩ := hf
  set F : G → ℂ := fun x => f (x⁻¹ * δ * θ x) with hF
  have hTcl : IsClosed (GlobalTheory.BCT.twCent θ δ : Set G) := by
    show IsClosed {g : G | g * δ = δ * θ g}
    exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul hθ)
  have hFU : ∀ u ∈ U, ∀ x : G, F (x * u) = F x := by
    intro u hu x
    show f ((x * u)⁻¹ * δ * θ (x * u)) = f (x⁻¹ * δ * θ x)
    rw [_root_.mul_inv_rev, map_mul]
    have h1 : θ u ∈ U := hUθ u hu
    have hu' : u⁻¹ ∈ U := U.inv_mem hu
    calc f (u⁻¹ * x⁻¹ * δ * (θ x * θ u)) = f (u⁻¹ * (x⁻¹ * δ * θ x) * θ u) := by
          simp only [mul_assoc]
      _ = f (u⁻¹ * (x⁻¹ * δ * θ x)) := (hfi _ h1 _).2
      _ = f (x⁻¹ * δ * θ x) := (hfi _ hu' _).1
  have hFT : ∀ t ∈ GlobalTheory.BCT.twCent θ δ, ∀ x : G, F (t * x) = F x := by
    intro t ht x
    have h : t * δ = δ * θ t := ht
    have h2 : t⁻¹ * δ * θ t = δ := by
      rw [mul_assoc, ← h, inv_mul_cancel_left]
    show f ((t * x)⁻¹ * δ * θ (t * x)) = f (x⁻¹ * δ * θ x)
    rw [_root_.mul_inv_rev, map_mul]
    calc f (x⁻¹ * t⁻¹ * δ * (θ t * θ x)) = f (x⁻¹ * (t⁻¹ * δ * θ t) * θ x) := by
          simp only [mul_assoc]
      _ = f (x⁻¹ * δ * θ x) := by rw [h2]
  have hFc : Continuous F := continuous_of_rightInv U hUo F hFU
  obtain ⟨_, hsum⟩ := sumCoset G μ hμ K hKo hKc hK1 _ hTcl hcomm ν hν F hFc hFT hcm
  have hmapK : ∀ q x : G, x ∈ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj q)) K ↔
      q⁻¹ * x * q ∈ K := by
    intro q x
    constructor
    · rintro ⟨k, hk, rfl⟩
      simpa [mul_assoc] using hk
    · intro hx
      exact ⟨q⁻¹ * x * q, hx, by simp [mul_assoc]⟩
  have hset : ∀ q : G, {t : GlobalTheory.BCT.twCent θ δ | q⁻¹ * (t : G) * q ∈ K} =
      {t : GlobalTheory.BCT.twCent θ δ | (t : G) ∈ GlobalTheory.BCT.twCent θ δ ⊓
        Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj q)) K} := by
    intro q
    ext t
    simp only [Set.mem_setOf_eq, Subgroup.mem_inf, hmapK, SetLike.coe_mem, true_and]
  have hopen : ∀ q : G, IsOpen {t : GlobalTheory.BCT.twCent θ δ | (t : G) ∈ GlobalTheory.BCT.twCent θ δ ⊓
      Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj q)) K} := by
    intro q
    rw [← hset q]
    exact hKo.preimage ((continuous_const.mul continuous_subtype_val).mul continuous_const)
  have hvol : ∀ q : G, _ := fun q => volIdx G (GlobalTheory.BCT.twCent θ δ) (GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ))
    (GlobalTheory.BCT.twCent θ δ ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj q)) K) hTcl ν hν
    (cptPart_le _) hC
    (GlobalTheory.LocFin.inf_le_cptPart _ _ (GlobalTheory.LocFin.isCompact_map_conj K hKc q)) (hopen q)
  have hCfin : ν {t : GlobalTheory.BCT.twCent θ δ | (t : G) ∈ GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ)} ≠ ⊤ :=
    ((hTcl.isClosedEmbedding_subtypeVal).isCompact_preimage hC).measure_lt_top.ne
  have hCne : ν.real {t : GlobalTheory.BCT.twCent θ δ | (t : G) ∈ GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ)} ≠ 0 := by
    have h1 := (hvol 1).1
    have hsub : {t : GlobalTheory.BCT.twCent θ δ | (t : G) ∈ GlobalTheory.BCT.twCent θ δ ⊓
        Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (1 : G))) K} ⊆
        {t : GlobalTheory.BCT.twCent θ δ | (t : G) ∈ GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ)} :=
      fun t ht => GlobalTheory.LocFin.inf_le_cptPart _ _ (GlobalTheory.LocFin.isCompact_map_conj K hKc 1) ht
    have h2 := measureReal_mono hsub hCfin
    intro h0
    exact h1 (le_antisymm (h0 ▸ h2) measureReal_nonneg)
  refine ⟨hCne, ?_⟩
  rw [hsum]
  unfold GlobalTheory.BCT.twOrb
  rw [mul_finsum]
  refine finsum_congr fun q => ?_
  obtain ⟨hH0, hCeq⟩ := hvol (Quotient.out q)
  have hidx : ((GlobalTheory.BCT.twCent θ δ ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (Quotient.out q))) K).relIndex
      (GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ)) : ℝ) ≠ 0 := fun h0 => hCne (by rw [hCeq, h0, zero_mul])
  rw [oneCoset G μ hμ K hKo hKc hK1 _ hTcl hcomm ν hν F hFc hFT (Quotient.out q)]
  rw [← avgInt G μ hμ K hKo hKc hK1 U hUo F hFU (Quotient.out q)]
  rw [hset, hCeq]
  rw [show (fun y : K => F (Quotient.out q * ↑y)) =
    fun k : K => f ((Quotient.out q * ↑k)⁻¹ * δ * θ (Quotient.out q * ↑k)) from rfl]
  have hidxC : ((GlobalTheory.BCT.twCent θ δ ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (Quotient.out q))) K).relIndex
      (GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ)) : ℂ) ≠ 0 := by exact_mod_cast hidx
  have hHC : ((ν.real {t : GlobalTheory.BCT.twCent θ δ | (t : G) ∈ GlobalTheory.BCT.twCent θ δ ⊓
      Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (Quotient.out q))) K} : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hH0
  push_cast
  field_simp

end UpperTheory.Gal.InertialTypesAlt.L
