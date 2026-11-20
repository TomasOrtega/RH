import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.LiftFactorization
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubiniHolds

noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open scoped Classical ENNReal

open PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

/- English proof (translation)
Establish `h` using `DoubleCoset.eq T K (Quotient.out q) g`. Rewrite `h` using `[DoubleCoset.out_eq']`. Conclude with `h.symm.trans eq_comm`.
-/
private lemma UpperTheory.Gal.InertialTypesAlt.L.mem_iff_mk {G : Type} [Group G] (T K : Subgroup G)
    (q : DoubleCoset.Quotient (T : Set G) (K : Set G)) (g : G) :
    (∃ t ∈ T, ∃ y ∈ K, g = t * Quotient.out q * y) ↔ DoubleCoset.mk T K g = q := by
  have h := DoubleCoset.eq T K (Quotient.out q) g
  rw [DoubleCoset.out_eq'] at h
  exact h.symm.trans eq_comm

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ μ hμ K hKo hKc hK1 T hTc hcomm ν hν F hF hFT hFC`. Take `⟨hsf, hinv, hrinv⟩` from `haarComm_holds G T hTc hcomm ν hν`. Take `⟨ρ, hρ, -⟩` from `normEx_holds G ⟨K, hKo, hKc⟩ T hTc ν hν hrinv`. Establish `hInt` using `quotInt_holds G μ hμ T hTc ν hν hinv F hF hFT hFC ρ hρ`. Take `⟨C, hC, hFC'⟩` from `hFC`.

Establish `hFm : Measurable F` using `hF.measurable`. Establish `hmk : ∀ h ∈ T, ∀ g : G, DoubleCoset.mk T K (h * g) = DoubleCoset.mk T K g` using `fun h hh g => ((DoubleCoset.eq T K g (h * g)).2 ⟨h, hh, 1, K.one_mem, by simp⟩).symm`. Use `set Q : Set (DoubleCoset.Quotient (T : Set G) (K : Set G)) := {q | ∃ y ∈ K, F (Quotient.out q * y) ≠ 0} with hQ`. Establish `hkey : ∀ g, F g ≠ 0 → DoubleCoset.mk T K g ∈ Q`. Introduce `g hg`.

Take `⟨t, ht, y, hy, he⟩` from `(UpperTheory.Gal.InertialTypesAlt.L.mem_iff_mk T K (DoubleCoset.mk T K g) g).2 rfl`. Use `⟨y, hy, ?_⟩` and prove the remaining obligations. Establish `e : Quotient.out (DoubleCoset.mk T K g) * y = t⁻¹ * g`. Rewrite using `[eq_inv_mul_iff_mul_eq, ← mul_assoc]`. Conclude with `he.symm`.

Rewrite using `[e, hFT t⁻¹ (T.inv_mem ht) g]`. Conclude with `hg`. Establish `hfin : Q.Finite`. Take `⟨s, hs⟩` from `hC.elim_finite_subcover (fun c : G => {z : G | c⁻¹ * z ∈ K}) (fun c => hKo.preimage (continuous_mul_left c⁻¹)) (fun c _ => Set.mem_iUnion.2 ⟨c, by simp [K.one_mem]⟩)`. Use `(s.finite_toSet.image (DoubleCoset.mk T K)).subset ?_` and prove the remaining obligations.

Introduce and unpack `q ⟨y, hy, hq⟩`. Take `⟨t, ht, c, hc, he⟩` from `hFC' _ hq`. Take `⟨i, hi, hci⟩` from `Set.mem_iUnion₂.1 (hs hc)`. Use `⟨i, hi, ?_⟩` and prove the remaining obligations. Rewrite using `[← DoubleCoset.out_eq' T K q, DoubleCoset.eq]`.

Use `⟨t, ht, i⁻¹ * c * y⁻¹, K.mul_mem hci (K.inv_mem hy), ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `⟨hfin, ?_⟩` and prove the remaining obligations. Establish `hS : ∀ q : DoubleCoset.Quotient (T : Set G) (K : Set G), {g | ∃ t ∈ T, ∃ y ∈ K, g = t * Quotient.out q * y} = {g | DoubleCoset.mk T K g = q}` using `fun q => Set.ext (UpperTheory.Gal.InertialTypesAlt.L.mem_iff_mk T K q)`. Repeatedly rewrite using `[hS]`.

Establish `hSo : ∀ q : DoubleCoset.Quotient (T : Set G) (K : Set G), IsOpen {g | DoubleCoset.mk T K g = q}`. Introduce `q`. Rewrite using `[isOpen_iff_forall_mem_open]`. Introduce `g hg`. Use `⟨{z | g⁻¹ * z ∈ K}, fun z hz => ?_, hKo.preimage (continuous_mul_left g⁻¹), by simp [K.one_mem]⟩` and prove the remaining obligations.

Use `show DoubleCoset.mk T K z = q`. Rewrite using `[← (show DoubleCoset.mk T K g = q from hg), eq_comm, DoubleCoset.eq]`. Conclude with `⟨1, T.one_mem, g⁻¹ * z, hz, by group⟩`. Establish `hSinv : ∀ q : DoubleCoset.Quotient (T : Set G) (K : Set G), ∀ h ∈ T, ∀ g : G, {g | DoubleCoset.mk T K g = q}.indicator F (h * g) = {g | DoubleCoset.mk T K g = q}.indicator F g`. Introduce `q h hh g`.

Simplify using `only [Set.indicator_apply, Set.mem_setOf_eq, hmk h hh g, hFT h hh g]`. Establish `hq_eq : ∀ q : DoubleCoset.Quotient (T : Set G) (K : Set G), quotIntegral μ T ν ({g | DoubleCoset.mk T K g = q}.indicator F) = ∫ g, {g | DoubleCoset.mk T K g = q}.indicator (fun g => F g * ((ρ g).toReal : ℂ)) g ∂μ`. Introduce `q`. Rewrite using `[quotIndep_holds G μ hμ T ν hsf hinv _ (hFm.indicator (hSo q).measurableSet) (hSinv q) ρ hρ]`. Use `congr 1`.

Use function extensionality and compare the values at `g`. Simplify using `only [Set.indicator_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hsupp : (Function.support fun q : DoubleCoset.Quotient (T : Set G) (K : Set G) => quotIntegral μ T ν ({g | DoubleCoset.mk T K g = q}.indicator F)) ⊆ ↑hfin.toFinset`. Introduce `q hq`.

Rewrite using `[Set.Finite.coe_toFinset]`. Assume the negation of the conclusion as `hqQ`. Apply `hq` to reduce the goal to its premises. Establish `h0 : {g | DoubleCoset.mk T K g = q}.indicator F = 0`. Use function extensionality and compare the values at `g`.

Simplify using `only [Set.indicator_apply, Set.mem_setOf_eq, Pi.zero_apply]`. Use `split_ifs with hg`. Assume the negation of the conclusion as `hne`. Conclude with `hqQ (hg ▸ hkey g hne)`. Both sides reduce to the same expression.

Use `show quotIntegral μ T ν ({g | DoubleCoset.mk T K g = q}.indicator F) = 0`. Rewrite using `[h0]`. Simplify using `[quotIntegral]`. Rewrite using `[quotIndep_holds G μ hμ T ν hsf hinv F hFm hFT ρ hρ, finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_congr rfl (fun q _ => hq_eq q), ← integral_finset_sum _ (fun q _ => hInt.indicator (hSo q).measurableSet)]`. Use `congr 1`.

Use function extensionality and compare the values at `g`. Distinguish the cases in `hg : F g = 0`. Simplify using `[Set.indicator_apply, hg]`. Rewrite using `[Finset.sum_eq_single (DoubleCoset.mk T K g)]`. Simplify using `[Set.indicator_apply]`.

Introduce `b _ hb`. Simplify using `only [Set.indicator_apply, Set.mem_setOf_eq]`. Rewrite using `[if_neg (fun h => hb h.symm)]`. Introduce `hn`. Conclude with `absurd (hfin.mem_toFinset.2 (hkey g hg)) hn`.
-/
theorem UpperTheory.Gal.InertialTypesAlt.L.sumCoset :
    UpperTheory.Gal.InertialTypesAlt.L.SumCoset := by
  intro G _ _ _ _ _ _ _ _ μ hμ K hKo hKc hK1 T hTc hcomm ν hν F hF hFT hFC
  obtain ⟨hsf, hinv, hrinv⟩ := haarComm_holds G T hTc hcomm ν hν
  obtain ⟨ρ, hρ, -⟩ := normEx_holds G ⟨K, hKo, hKc⟩ T hTc ν hν hrinv
  have hInt := quotInt_holds G μ hμ T hTc ν hν hinv F hF hFT hFC ρ hρ
  obtain ⟨C, hC, hFC'⟩ := hFC
  have hFm : Measurable F := hF.measurable
  have hmk : ∀ h ∈ T, ∀ g : G, DoubleCoset.mk T K (h * g) = DoubleCoset.mk T K g :=
    fun h hh g => ((DoubleCoset.eq T K g (h * g)).2 ⟨h, hh, 1, K.one_mem, by simp⟩).symm
  set Q : Set (DoubleCoset.Quotient (T : Set G) (K : Set G)) :=
    {q | ∃ y ∈ K, F (Quotient.out q * y) ≠ 0} with hQ
  have hkey : ∀ g, F g ≠ 0 → DoubleCoset.mk T K g ∈ Q := by
    intro g hg
    obtain ⟨t, ht, y, hy, he⟩ :=
      (UpperTheory.Gal.InertialTypesAlt.L.mem_iff_mk T K (DoubleCoset.mk T K g) g).2 rfl
    refine ⟨y, hy, ?_⟩
    have e : Quotient.out (DoubleCoset.mk T K g) * y = t⁻¹ * g := by
      rw [eq_inv_mul_iff_mul_eq, ← mul_assoc]
      exact he.symm
    rw [e, hFT t⁻¹ (T.inv_mem ht) g]
    exact hg
  have hfin : Q.Finite := by
    obtain ⟨s, hs⟩ := hC.elim_finite_subcover (fun c : G => {z : G | c⁻¹ * z ∈ K})
      (fun c => hKo.preimage (continuous_mul_left c⁻¹))
      (fun c _ => Set.mem_iUnion.2 ⟨c, by simp [K.one_mem]⟩)
    refine (s.finite_toSet.image (DoubleCoset.mk T K)).subset ?_
    rintro q ⟨y, hy, hq⟩
    obtain ⟨t, ht, c, hc, he⟩ := hFC' _ hq
    obtain ⟨i, hi, hci⟩ := Set.mem_iUnion₂.1 (hs hc)
    refine ⟨i, hi, ?_⟩
    rw [← DoubleCoset.out_eq' T K q, DoubleCoset.eq]
    refine ⟨t, ht, i⁻¹ * c * y⁻¹, K.mul_mem hci (K.inv_mem hy), ?_⟩
    calc Quotient.out q = Quotient.out q * y * y⁻¹ := by group
      _ = t * c * y⁻¹ := by rw [he]
      _ = t * i * (i⁻¹ * c * y⁻¹) := by group
  refine ⟨hfin, ?_⟩
  have hS : ∀ q : DoubleCoset.Quotient (T : Set G) (K : Set G),
      {g | ∃ t ∈ T, ∃ y ∈ K, g = t * Quotient.out q * y} = {g | DoubleCoset.mk T K g = q} :=
    fun q => Set.ext (UpperTheory.Gal.InertialTypesAlt.L.mem_iff_mk T K q)
  simp_rw [hS]
  have hSo : ∀ q : DoubleCoset.Quotient (T : Set G) (K : Set G),
      IsOpen {g | DoubleCoset.mk T K g = q} := by
    intro q
    rw [isOpen_iff_forall_mem_open]
    intro g hg
    refine ⟨{z | g⁻¹ * z ∈ K}, fun z hz => ?_, hKo.preimage (continuous_mul_left g⁻¹),
      by simp [K.one_mem]⟩
    show DoubleCoset.mk T K z = q
    rw [← (show DoubleCoset.mk T K g = q from hg), eq_comm, DoubleCoset.eq]
    exact ⟨1, T.one_mem, g⁻¹ * z, hz, by group⟩
  have hSinv : ∀ q : DoubleCoset.Quotient (T : Set G) (K : Set G), ∀ h ∈ T, ∀ g : G,
      {g | DoubleCoset.mk T K g = q}.indicator F (h * g) =
        {g | DoubleCoset.mk T K g = q}.indicator F g := by
    intro q h hh g
    simp only [Set.indicator_apply, Set.mem_setOf_eq, hmk h hh g, hFT h hh g]
  have hq_eq : ∀ q : DoubleCoset.Quotient (T : Set G) (K : Set G),
      quotIntegral μ T ν ({g | DoubleCoset.mk T K g = q}.indicator F) =
        ∫ g, {g | DoubleCoset.mk T K g = q}.indicator
          (fun g => F g * ((ρ g).toReal : ℂ)) g ∂μ := by
    intro q
    rw [quotIndep_holds G μ hμ T ν hsf hinv _ (hFm.indicator (hSo q).measurableSet) (hSinv q) ρ hρ]
    congr 1
    funext g
    simp only [Set.indicator_apply]
    split_ifs <;> simp
  have hsupp : (Function.support fun q : DoubleCoset.Quotient (T : Set G) (K : Set G) =>
      quotIntegral μ T ν ({g | DoubleCoset.mk T K g = q}.indicator F)) ⊆
        ↑hfin.toFinset := by
    intro q hq
    rw [Set.Finite.coe_toFinset]
    by_contra hqQ
    apply hq
    have h0 : {g | DoubleCoset.mk T K g = q}.indicator F = 0 := by
      funext g
      simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.zero_apply]
      split_ifs with hg
      · by_contra hne
        exact hqQ (hg ▸ hkey g hne)
      · rfl
    show quotIntegral μ T ν ({g | DoubleCoset.mk T K g = q}.indicator F) = 0
    rw [h0]
    simp [quotIntegral]
  rw [quotIndep_holds G μ hμ T ν hsf hinv F hFm hFT ρ hρ, finsum_eq_sum_of_support_subset _ hsupp,
    Finset.sum_congr rfl (fun q _ => hq_eq q),
    ← integral_finset_sum _ (fun q _ => hInt.indicator (hSo q).measurableSet)]
  congr 1
  funext g
  by_cases hg : F g = 0
  · simp [Set.indicator_apply, hg]
  · rw [Finset.sum_eq_single (DoubleCoset.mk T K g)]
    · simp [Set.indicator_apply]
    · intro b _ hb
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
      rw [if_neg (fun h => hb h.symm)]
    · intro hn
      exact absurd (hfin.mem_toFinset.2 (hkey g hg)) hn
