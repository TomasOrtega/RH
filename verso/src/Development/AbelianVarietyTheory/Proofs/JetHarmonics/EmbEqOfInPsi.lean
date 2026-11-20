import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsInPsiIEEqEmbK
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightExponentsEmbeddingsDegree

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

noncomputable section

namespace GlobalTheory.PtTie

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Proceed by induction. Treat this case separately.

Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem emb_eq_of_inPsi {D : D7} {Q : Par D} (hp : Q.PinHost) {τ σ : D.host.E →+* ℂ} (hτ : InPsi Q.H τ)
    (hσ : InPsi Q.H σ) {x : D.host.E} (hx : x ∈ D.host.K) : τ x = σ x := by
  have hs : τ D.host.sqrtMinusD = σ D.host.sqrtMinusD := by
    rw [← hp.2.1]; exact hτ.trans hσ.symm
  have hx' : x ∈ IntermediateField.adjoin ℚ {D.host.sqrtMinusD} := hx
  induction hx' using IntermediateField.adjoin_induction with
  | mem y hy => rw [Set.mem_singleton_iff.1 hy]; exact hs
  | algebraMap q => simp
  | add a b ha hb iha ihb => rw [map_add, map_add, iha ha, ihb hb]
  | inv a ha iha => rw [map_inv₀, map_inv₀, iha ha]
  | mul a b ha hb iha ihb => rw [map_mul, map_mul, iha ha, ihb hb]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem prod_pow_wtA {D : D7} {Q : Par D} (hQ : Q.Pins) {j : ℕ} (hj : InR D j) (w : WeightFamilies.Wt D j)
    {M : Type} [CommMonoid M] (F : (D.host.E →+* ℂ) → M) :
    ∏ τ : D.host.E →+* ℂ, F τ ^ (∑ i : Fin ((Q.Dw j).mult τ), wtA w (τ, (i : ℕ))) =
      ∏ t : D.what₂.Tau, (F (DV.tauEmb D t) ^ (∑ i, w.aP t i) *
        F (ComplexEmbedding.conjugate (DV.tauEmb D t)) ^ (∑ i, w.aM t i)) := by
  classical
  obtain ⟨hp, hq, -⟩ := hQ.2.2.2 j hj
  have hsw : ∀ τ : D.host.E →+* ℂ, ∑ i : Fin ((Q.Dw j).mult τ), wtA w (τ, (i : ℕ)) =
      ∑ t : D.what₂.Tau, ((if τ = DV.tauEmb D t then ∑ i : Fin ((Q.Dw j).mult τ), ext0 (w.aP t) (i : ℕ) else 0) +
        if τ = ComplexEmbedding.conjugate (DV.tauEmb D t) then
          ∑ i : Fin ((Q.Dw j).mult τ), ext0 (w.aM t) (i : ℕ) else 0) := by
    intro τ
    simp only [GlobalTheory.WeightExponents.wtA_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_add_distrib]
    split_ifs <;> simp
  have hs : ∀ {p m : ℕ} (f : Fin p → ℕ), m = p → ∑ i : Fin m, ext0 f i = ∑ i, f i := by
    rintro p m f rfl
    exact Finset.sum_congr rfl fun i _ => by simp [ext0, i.isLt]
  rw [Finset.prod_congr rfl fun τ _ => by rw [hsw τ, ← Finset.prod_pow_eq_pow_sum], Finset.prod_comm]
  refine Finset.prod_congr rfl fun t _ => ?_
  simp only [pow_add, pow_ite, pow_zero]
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq']
  simp only [Finset.mem_univ, if_true]
  have ht := hQ.1.2.2.2 t
  have hc : ¬ ComplexEmbedding.conjugate (DV.tauEmb D t) (Q.H.rt : D.host.E) = Q.H.rt0 :=
    GlobalTheory.WeightExponents.not_inPsi_conj hQ.1 t
  rw [hs _ (by rw [Datum.mult, if_pos ht, hp]), hs _ (by rw [Datum.mult, if_neg hc, hq])]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem emb_piBarO {D : D7} (EX : ErrX D) (i : Fin 2) (τ : D.host.E →+* ℂ) :
    τ ((piBarO EX i : 𝓞 D.host.E) : D.host.E) = starRingEnd ℂ (τ ((EX.piG i : 𝓞 D.host.E) : D.host.E)) := by
  have h1 : ((piBarO EX i : 𝓞 D.host.E) : D.host.E) = ((barE D (EX.piG i) : 𝓞 D.host.E) : D.host.E) := by
    rw [barE_eq_conj]; rfl
  rw [h1]
  exact IsCMField.complexEmbedding_complexConj D.host.E τ _

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the hypotheses and the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem nrm_eq_prod {D : D7} {Q : Par D} (hQ : Q.Pins) {j : ℕ} (hj : InR D j) (EX : ErrX D) (w : WeightFamilies.Wt D j)
    {τ : D.host.E →+* ℂ} (hτ : InPsi Q.H τ) :
    nrm (Q.Dw j) Q.c (wtA w) (EX.piG 0 * EX.piG 1) =
      ∏ i : Fin 2, embK Q.c τ (EX.piG i) ^ Dplus w * embK Q.c τ (piBarO EX i) ^ Dminus w := by
  have h1 : ∀ t i, embK Q.c (DV.tauEmb D t) (EX.piG i) = embK Q.c τ (EX.piG i) := fun t i =>
    Subtype.ext (emb_eq_of_inPsi hQ.1 (hQ.1.2.2.2 t) hτ (EX.piG_K i))
  have h2 : ∀ t i, embK Q.c (ComplexEmbedding.conjugate (DV.tauEmb D t)) (EX.piG i) = embK Q.c τ (piBarO EX i) :=
    fun t i => Subtype.ext (by
      rw [embK_coe, embK_coe, emb_piBarO, ← emb_eq_of_inPsi hQ.1 (hQ.1.2.2.2 t) hτ (EX.piG_K i)]
      simp)
  unfold nrm Dplus Dminus
  rw [prod_pow_wtA hQ hj w fun σ => embK Q.c σ (EX.piG 0 * EX.piG 1)]
  simp only [map_mul, h1, h2]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, Fin.prod_univ_two,
    mul_pow, mul_pow]
  ring

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.
-/
theorem map_nnW {D : D7} (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) {j : ℕ}
    (w : WeightFamilies.Wt D j) :
    ((nnW B hinj EX w : 𝓞 B.KO) : B.KO) = ∏ i : Fin 2, ((iE D hinj B (EX.piG i) : 𝓞 B.KO) : B.KO) ^ Dplus w *
      ((iE D hinj B (piBarO EX i) : 𝓞 B.KO) : B.KO) ^ Dminus w := by
  unfold nnW
  simp only [RingOfIntegers.coe_eq_algebraMap, map_prod, map_mul, map_pow]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities.
-/
theorem nrm_eq_nnW : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (w : WeightFamilies.Wt D j), nrm (T.Q.Dw j) T.Q.c (wtA w) (EX.piG 0 * EX.piG 1) = ((nnW (recB h.toLawsCore) hinj EX w : 𝓞 T.Q.c.F) : T.Q.c.F) := by
  intro D T h j hj hinj EX w
  obtain ⟨τ, hτ, hE⟩ := exists_inPsi_iE_eq_embK D T h hinj
  rw [nrm_eq_prod h.pins hj EX w hτ]
  refine Eq.trans ?_ (map_nnW (recB h.toLawsCore) hinj EX w).symm
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← hE, ← hE]

end GlobalTheory.PtTie
