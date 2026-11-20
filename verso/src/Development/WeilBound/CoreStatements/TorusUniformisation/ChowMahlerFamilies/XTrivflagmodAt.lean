import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.PluckerCoord
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.TrivFlagKills
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFullFlagRestrictLoc
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialIdealCorresp
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialIdealMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVocabMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVocabMultiHomogIdeal
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XFlagframeBasis
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_trivflagmod_at

section Lin

variable {F : Type*} [Field F] {N : ℕ}

/- English proof (translation)
Establish `hU : IsUnit G.det` using `hG.isUnit`. Use `⟨(Pi.basisFun F (Fin N)).map (G.toLinearEquiv' (G.invertibleOfIsUnitDet hU)), fun i j => ?_⟩` and prove the remaining obligations. Establish `: (G.toLinearEquiv' (G.invertibleOfIsUnitDet hU)) (Pi.single i 1) = G.mulVec (Pi.single i 1)` using `rfl`. Rewrite using `[Module.Basis.map_apply, Pi.basisFun_apply, this]`. Simplify using the standard rewrite rules.
-/
theorem exists_basis_cols (G : Matrix (Fin N) (Fin N) F) (hG : G.det ≠ 0) :
    ∃ u : Module.Basis (Fin N) F (Fin N → F), ∀ i j, u i j = G j i := by
  classical
  have hU : IsUnit G.det := hG.isUnit
  refine ⟨(Pi.basisFun F (Fin N)).map (G.toLinearEquiv' (G.invertibleOfIsUnitDet hU)), fun i j => ?_⟩
  have : (G.toLinearEquiv' (G.invertibleOfIsUnitDet hU)) (Pi.single i 1) = G.mulVec (Pi.single i 1) := rfl
  rw [Module.Basis.map_apply, Pi.basisFun_apply, this]
  simp

/- English proof (translation)
Establish `e : v = ∑ q, a q • u q`. Rewrite using `[← h]`. Use function extensionality and compare the values at `j`. Simplify using `[Finset.sum_apply, hu, Matrix.mulVec, dotProduct, mul_comm]`. Rewrite using `[e, u.repr_sum_self]`.
-/
theorem repr_eq (G : Matrix (Fin N) (Fin N) F) (u : Module.Basis (Fin N) F (Fin N → F))
    (hu : ∀ i j, u i j = G j i) (a v : Fin N → F) (h : G.mulVec a = v) (i : Fin N) :
    u.repr v i = a i := by
  have e : v = ∑ q, a q • u q := by
    rw [← h]
    funext j
    simp [Finset.sum_apply, hu, Matrix.mulVec, dotProduct, mul_comm]
  rw [e, u.repr_sum_self]

/- English proof (translation)
Use `conv_lhs => rw [← u.sum_repr v]`. Simplify using `[Finset.sum_apply, hu, mul_comm]`.
-/
theorem mulVec_repr (G : Matrix (Fin N) (Fin N) F) (u : Module.Basis (Fin N) F (Fin N → F))
    (hu : ∀ i j, u i j = G j i) (v : Fin N → F) (j : Fin N) :
    v j = ∑ q, G j q * u.repr v q := by
  conv_lhs => rw [← u.sum_repr v]
  simp [Finset.sum_apply, hu, mul_comm]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hv i`. Set `G' : Matrix (Fin N) (Fin N) R` to `fun i j => ⟨G i j, hG i j⟩`. Establish `hGG : G = R.val.toRingHom.mapMatrix G'`. Use extensionality with `i j`.

Both sides reduce to the same expression. Establish `hadj : ∀ i j, G.adjugate i j ∈ R`. Introduce `i j`. Rewrite using `[hGG, ← RingHom.map_adjugate]`. Conclude with `(G'.adjugate i j).2`.

Establish `e : G.mulVec (h • G.adjugate.mulVec v) = v`. Rewrite using `[Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul, mul_comm, hdet, one_smul]`. Rewrite using `[repr_eq G u hu _ v e i]`. Express the relevant statement in the definitionally equal form `h * ∑ q, G.adjugate i q * v q ∈ R`. Conclude with `mul_mem hh (sum_mem fun q _ => mul_mem (hadj i q) (hv q))`.

Introduce `hv j`. Rewrite using `[mulVec_repr G u hu v j]`. Conclude with `sum_mem fun q _ => mul_mem (hG j q) (hv q)`.
-/
theorem lat_iff {k : Type*} [CommRing k] [Algebra k F] (R : Subalgebra k F)
    (G : Matrix (Fin N) (Fin N) F) (hG : ∀ i j, G i j ∈ R) {h : F} (hh : h ∈ R)
    (hdet : G.det * h = 1) (u : Module.Basis (Fin N) F (Fin N → F))
    (hu : ∀ i j, u i j = G j i) (v : Fin N → F) :
    (∀ q, v q ∈ R) ↔ ∀ i, u.repr v i ∈ R := by
  classical
  constructor
  · intro hv i
    let G' : Matrix (Fin N) (Fin N) R := fun i j => ⟨G i j, hG i j⟩
    have hGG : G = R.val.toRingHom.mapMatrix G' := by
      ext i j
      rfl
    have hadj : ∀ i j, G.adjugate i j ∈ R := by
      intro i j
      rw [hGG, ← RingHom.map_adjugate]
      exact (G'.adjugate i j).2
    have e : G.mulVec (h • G.adjugate.mulVec v) = v := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
        Matrix.one_mulVec, smul_smul, mul_comm, hdet, one_smul]
    rw [repr_eq G u hu _ v e i]
    change h * ∑ q, G.adjugate i q * v q ∈ R
    exact mul_mem hh (sum_mem fun q _ => mul_mem (hadj i q) (hv q))
  · intro hv j
    rw [mulVec_repr G u hu v j]
    exact sum_mem fun q _ => mul_mem (hG j q) (hv q)

/- English proof (translation)
Use `repr_eq _ w hw (fun j => c⁻¹ * U j i * d j) _ ?_ j` and prove the remaining obligations. Use function extensionality and compare the values at `l`. Rewrite using `[hu]`. Apply `mul_left_cancel₀ hc` to reduce the goal to its premises. Rewrite using `[hGU]`.

Simplify using `only [Matrix.mulVec, dotProduct, Matrix.mul_diagonal, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Use `hd q` as an intermediate fact. Clear the denominators using the available nonvanishing facts.
-/
theorem flag_coords (G G₀ U : Matrix (Fin N) (Fin N) F) (c : F) (hc : c ≠ 0) (d : Fin N → F)
    (hd : ∀ i, d i ≠ 0) (hGU : ∀ i j, c * G i j = ∑ q, G₀ i q * U q j)
    (u w : Module.Basis (Fin N) F (Fin N → F)) (hu : ∀ i j, u i j = G j i)
    (hw : ∀ i j, w i j = (G₀ * Matrix.diagonal fun i => (d i)⁻¹) j i) (i j : Fin N) :
    w.repr (u i) j = c⁻¹ * U j i * d j := by
  refine repr_eq _ w hw (fun j => c⁻¹ * U j i * d j) _ ?_ j
  funext l
  rw [hu]
  apply mul_left_cancel₀ hc
  rw [hGU]
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_diagonal, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  have := hd q
  field_simp

end Lin

section Res

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (kap redIdeal genPt)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagRestrict

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {Ω : Type} [Field Ω] [Algebra O Ω]
variable {x : (Σ k, ι k) → Ω} {Q : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver (kap O) ι)} [Q.IsPrime]

/- English proof (translation)
Set `ρ : locAlg x Q →+* FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver (kap O) ι ⧸ Q)` to `{ toFun := fun a => rs x Q a map_one' := rs_one hPQ map_mul' := fun a b => rs_mul hPQ a.2 b.2 map_zero' := rs_zero hPQ map_add' := fun a b => rs_add hPQ a.2 b.2 }`. Set `g' : Matrix (Fin N) (Fin N) (locAlg x Q)` to `fun i j => ⟨g i j, hg i j⟩`. Establish `h1 : g.det = ((g'.det : locAlg x Q) : Ω)`. Use `(locAlg x Q).val.toRingHom.map_det g'` as an intermediate fact. Conclude with `this.symm`.

Use `⟨h1 ▸ g'.det.2, ?_⟩` and prove the remaining obligations. Rewrite using `[h1]`. Conclude with `ρ.map_det g'`.
-/
theorem rs_det (hPQ : redIdeal O (mcIdeal O x) ≤ Q) {N : ℕ} (g : Matrix (Fin N) (Fin N) Ω)
    (hg : ∀ i j, g i j ∈ locAlg x Q) :
    g.det ∈ locAlg x Q ∧ rs x Q g.det = (g.map (rs x Q)).det := by
  let ρ : locAlg x Q →+* FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver (kap O) ι ⧸ Q) :=
    { toFun := fun a => rs x Q a
      map_one' := rs_one hPQ
      map_mul' := fun a b => rs_mul hPQ a.2 b.2
      map_zero' := rs_zero hPQ
      map_add' := fun a b => rs_add hPQ a.2 b.2 }
  let g' : Matrix (Fin N) (Fin N) (locAlg x Q) := fun i j => ⟨g i j, hg i j⟩
  have h1 : g.det = ((g'.det : locAlg x Q) : Ω) := by
    have := (locAlg x Q).val.toRingHom.map_det g'
    exact this.symm
  refine ⟨h1 ▸ g'.det.2, ?_⟩
  rw [h1]
  exact ρ.map_det g'

/- English proof (translation)
Rewrite using `[rs_mul hPQ (Subalgebra.algebraMap_mem _ _) hr, rs_algebraMap hPQ, (IsLocalRing.residue_eq_zero_iff ϖ).2 hϖ.not_isUnit, map_zero, zero_mul]`.
-/
theorem rs_unif (hPQ : redIdeal O (mcIdeal O x) ≤ Q) {ϖ : O} (hϖ : Irreducible ϖ) {r : Ω}
    (hr : r ∈ locAlg x Q) : rs x Q (algebraMap O Ω ϖ * r) = 0 := by
  rw [rs_mul hPQ (Subalgebra.algebraMap_mem _ _) hr, rs_algebraMap hPQ,
    (IsLocalRing.residue_eq_zero_iff ϖ).2 hϖ.not_isUnit, map_zero, zero_mul]

/- English proof (translation)
Rewrite using `[← aeval_segForm (R := O)]`. Conclude with `aeval_ne_zero hPQ (isMultiHomog_segForm s) (red_segForm_notMem hs)`.
-/
theorem mseg_ne (hPQ : redIdeal O (mcIdeal O x) ≤ Q) {s : ∀ k, ι k}
    (hs : mseg (genPt (kap O) Q) s ≠ 0) : mseg x s ≠ 0 := by
  rw [← aeval_segForm (R := O)]
  exact aeval_ne_zero hPQ (isMultiHomog_segForm s) (red_segForm_notMem hs)

/- English proof (translation)
The claim follows from `Finset.prod_ne_zero_iff.2 fun k hk => zpow_ne_zero _ (Finset.prod_ne_zero_iff.1 hs k hk)`.
-/
theorem mon_ne {F : Type*} [Field F] (y : (Σ k, ι k) → F) {s : ∀ k, ι k} (hs : mseg y s ≠ 0)
    (a : K → ℤ) : chartMon y s a ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun k hk => zpow_ne_zero _ (Finset.prod_ne_zero_iff.1 hs k hk)

/- English proof (translation)
Take `⟨g, hg, hov⟩` from `H`. Establish `hG : ∀ s, mseg (genPt (kap O) Q) s ≠ 0 → (∀ i j, (g s).map (rs x Q) i j ∈ chartRing (kap O) (mseg (genPt (kap O) Q)) s) ∧ ∃ h ∈ chartRing (kap O) (mseg (genPt (kap O) Q)) s, ((g s).map (rs x Q)).det * h = 1`. Introduce `s hs`. Take `⟨h1, h, hh, r, hr, hdet⟩` from `hg s (mseg_ne hPQ hs)`. Use `⟨fun i j => (chartRing_sub hPQ hs (h1 i j)).2, rs x Q h, (chartRing_sub hPQ hs hh).2, ?_⟩` and prove the remaining obligations.

Take `⟨h2, h3⟩` from `rs_det hPQ (g s) fun i j => (chartRing_sub hPQ hs (h1 i j)).1`. Establish `hr'` using `(chartRing_sub hPQ hs hr).1`. Rewrite using `[← h3, ← rs_mul hPQ h2 (chartRing_sub hPQ hs hh).1, hdet, rs_add hPQ (one_mem _) (mul_mem (Subalgebra.algebraMap_mem _ _) hr'), rs_one hPQ, rs_unif hPQ hϖ hr', add_zero]`. Establish `hdet : ∀ s, mseg (genPt (kap O) Q) s ≠ 0 → ((g s).map (rs x Q)).det ≠ 0`. Introduce `s hs`.

Take `⟨-, h, -, hh⟩` from `hG s hs`. Conclude with `left_ne_zero_of_mul_eq_one hh`. Take `⟨w, hw⟩` from `exists_basis_cols ((g s₀).map (rs x Q) * Matrix.diagonal fun i => (chartMon (genPt (kap O) Q) s₀ (b i))⁻¹) (by`. Rewrite using `[Matrix.det_mul, Matrix.det_diagonal]`. Conclude with `mul_ne_zero (hdet s₀ hs₀) (Finset.prod_ne_zero_iff.2 fun i _ => inv_ne_zero (mon_ne _ hs₀ _)))`.

Use `⟨w, (PositivityTheory.Xgn.t_flagframe_basis (kap O) _ K ι (genPt (kap O) Q) N _ (scaledTrivBundle (kap O) (segreVec (genPt (kap O) Q)) N one_ne_zero) w b).2 fun s hs => ?_⟩` and prove the remaining obligations. Take `⟨u, hu⟩` from `exists_basis_cols _ (hdet s hs)`. Take `⟨m, U, Z, hU, hZ, hUt, hUd, -, hE⟩` from `hov s s₀ (mseg_ne hPQ hs) (mseg_ne hPQ hs₀)`. Take `⟨hc1, hc2⟩` from `seg_ratio (x := x) hPQ hs₀ s`. Establish `hc0 : (mseg (genPt (kap O) Q) s / mseg (genPt (kap O) Q) s₀) ^ m ≠ 0` using `pow_ne_zero _ (div_ne_zero hs hs₀)`.

Establish `hgs : ∀ i j, g s i j ∈ locAlg x Q` using `fun i j => (chartRing_sub hPQ hs ((hg s (mseg_ne hPQ hs)).1 i j)).1`. Establish `hg0 : ∀ i j, g s₀ i j ∈ locAlg x Q` using `fun i j => (chartRing_sub hPQ hs₀ ((hg s₀ (mseg_ne hPQ hs₀)).1 i j)).1`. Establish `hU' : ∀ i j, U i j ∈ locAlg x Q` using `fun i j => (chartRing_sub hPQ hs₀ (hU i j)).1`. Establish `hZ' : ∀ i j, Z i j ∈ locAlg x Q` using `fun i j => (chartRing_sub hPQ hs₀ (hZ i j)).1`. Establish `key` using `flag_coords ((g s).map (rs x Q)) ((g s₀).map (rs x Q)) (U.map (rs x Q)) _ hc0 (fun i => chartMon (genPt (kap O) Q) s₀ (b i)) (fun i => mon_ne _ hs₀ _) (by`.

Introduce `i j`. Establish `e : (mseg x s / mseg x s₀) ^ m * g s i j = ∑ q, g s₀ i q * U q j + algebraMap O Ω ϖ * Z i j` using `congrFun (congrFun hE i) j`. Establish `e'` using `congrArg (rs x Q) e`. Rewrite `e'` using `[rs_mul hPQ (pow_mem hc1 m) (hgs i j), rs_pow hPQ hc1, hc2, rs_add hPQ (sum_mem fun q _ => mul_mem (hg0 i q) (hU' q j)) (mul_mem (Subalgebra.algebraMap_mem _ _) (hZ' i j)), rs_unif hPQ hϖ (hZ' i j), add_zero, rs_sum hPQ _ _ fun q _ => mul_mem (hg0 i q) (hU' q j)]`. Simplify using `only [Matrix.map_apply]`.

Rewrite using `[e']`. Conclude with `Finset.sum_congr rfl fun q _ => rs_mul hPQ (hg0 i q) (hU' q j)) u w hu hw`. Use `⟨u, fun i j hij => ?_, fun i => ?_, fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[key, Matrix.map_apply, hUt j i hij, rs_zero hPQ, mul_zero, zero_mul]`. Take `⟨hm1, hm2⟩` from `chartMon_ratio (x := x) hPQ hs hs₀ (b i)`.

Rewrite using `[key, Matrix.map_apply, hUd, rs_mul hPQ (pow_mem hc1 m) hm1, rs_pow hPQ hc1, hc2, hm2, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul, div_mul_cancel₀ _ (mon_ne _ hs₀ _)]`. Take `⟨h1, h, hh, hd⟩` from `hG s hs`. Rewrite using `[← lat_iff _ _ h1 hh hd u hu v]`. Use `(mem_scaledTrivLat (R := kap O)).trans (forall_congr' fun q => ⟨?_, fun hq => ⟨v q, hq, (one_mul _).symm⟩⟩)` and prove the remaining obligations. Introduce and unpack `⟨a, ha, e⟩`.

Rewrite using `[e, one_mul]`. Conclude with `ha`.
-/
theorem exists_frame [DecidableEq K] (hPQ : redIdeal O (mcIdeal O x) ≤ Q) {ϖ : O}
    (hϖ : Irreducible ϖ) {N : ℕ} {b : Fin N → K → ℤ} (H : TrivFlagMod O ϖ x N b)
    {s₀ : ∀ k, ι k} (hs₀ : mseg (genPt (kap O) Q) s₀ ≠ 0) :
    ∃ w : Module.Basis (Fin N) _ (Fin N → _),
      IsFlagFrame (genPt (kap O) Q)
        (scaledTrivBundle (kap O) (segreVec (genPt (kap O) Q)) N one_ne_zero) w b := by
  obtain ⟨g, hg, hov⟩ := H
  have hG : ∀ s, mseg (genPt (kap O) Q) s ≠ 0 →
      (∀ i j, (g s).map (rs x Q) i j ∈ chartRing (kap O) (mseg (genPt (kap O) Q)) s) ∧
      ∃ h ∈ chartRing (kap O) (mseg (genPt (kap O) Q)) s, ((g s).map (rs x Q)).det * h = 1 := by
    intro s hs
    obtain ⟨h1, h, hh, r, hr, hdet⟩ := hg s (mseg_ne hPQ hs)
    refine ⟨fun i j => (chartRing_sub hPQ hs (h1 i j)).2, rs x Q h, (chartRing_sub hPQ hs hh).2, ?_⟩
    obtain ⟨h2, h3⟩ := rs_det hPQ (g s) fun i j => (chartRing_sub hPQ hs (h1 i j)).1
    have hr' := (chartRing_sub hPQ hs hr).1
    rw [← h3, ← rs_mul hPQ h2 (chartRing_sub hPQ hs hh).1, hdet,
      rs_add hPQ (one_mem _) (mul_mem (Subalgebra.algebraMap_mem _ _) hr'), rs_one hPQ,
      rs_unif hPQ hϖ hr', add_zero]
  have hdet : ∀ s, mseg (genPt (kap O) Q) s ≠ 0 → ((g s).map (rs x Q)).det ≠ 0 := by
    intro s hs
    obtain ⟨-, h, -, hh⟩ := hG s hs
    exact left_ne_zero_of_mul_eq_one hh
  obtain ⟨w, hw⟩ := exists_basis_cols ((g s₀).map (rs x Q) *
      Matrix.diagonal fun i => (chartMon (genPt (kap O) Q) s₀ (b i))⁻¹) (by
    rw [Matrix.det_mul, Matrix.det_diagonal]
    exact mul_ne_zero (hdet s₀ hs₀)
      (Finset.prod_ne_zero_iff.2 fun i _ => inv_ne_zero (mon_ne _ hs₀ _)))
  refine ⟨w, (PositivityTheory.Xgn.t_flagframe_basis (kap O) _ K ι (genPt (kap O) Q) N _
    (scaledTrivBundle (kap O) (segreVec (genPt (kap O) Q)) N one_ne_zero) w b).2 fun s hs => ?_⟩
  obtain ⟨u, hu⟩ := exists_basis_cols _ (hdet s hs)
  obtain ⟨m, U, Z, hU, hZ, hUt, hUd, -, hE⟩ := hov s s₀ (mseg_ne hPQ hs) (mseg_ne hPQ hs₀)
  obtain ⟨hc1, hc2⟩ := seg_ratio (x := x) hPQ hs₀ s
  have hc0 : (mseg (genPt (kap O) Q) s / mseg (genPt (kap O) Q) s₀) ^ m ≠ 0 :=
    pow_ne_zero _ (div_ne_zero hs hs₀)
  have hgs : ∀ i j, g s i j ∈ locAlg x Q := fun i j =>
    (chartRing_sub hPQ hs ((hg s (mseg_ne hPQ hs)).1 i j)).1
  have hg0 : ∀ i j, g s₀ i j ∈ locAlg x Q := fun i j =>
    (chartRing_sub hPQ hs₀ ((hg s₀ (mseg_ne hPQ hs₀)).1 i j)).1
  have hU' : ∀ i j, U i j ∈ locAlg x Q := fun i j => (chartRing_sub hPQ hs₀ (hU i j)).1
  have hZ' : ∀ i j, Z i j ∈ locAlg x Q := fun i j => (chartRing_sub hPQ hs₀ (hZ i j)).1
  have key := flag_coords ((g s).map (rs x Q)) ((g s₀).map (rs x Q)) (U.map (rs x Q)) _ hc0
    (fun i => chartMon (genPt (kap O) Q) s₀ (b i)) (fun i => mon_ne _ hs₀ _) (by
      intro i j
      have e : (mseg x s / mseg x s₀) ^ m * g s i j =
          ∑ q, g s₀ i q * U q j + algebraMap O Ω ϖ * Z i j := congrFun (congrFun hE i) j
      have e' := congrArg (rs x Q) e
      rw [rs_mul hPQ (pow_mem hc1 m) (hgs i j), rs_pow hPQ hc1, hc2,
        rs_add hPQ (sum_mem fun q _ => mul_mem (hg0 i q) (hU' q j))
          (mul_mem (Subalgebra.algebraMap_mem _ _) (hZ' i j)), rs_unif hPQ hϖ (hZ' i j), add_zero,
        rs_sum hPQ _ _ fun q _ => mul_mem (hg0 i q) (hU' q j)] at e'
      simp only [Matrix.map_apply]
      rw [e']
      exact Finset.sum_congr rfl fun q _ => rs_mul hPQ (hg0 i q) (hU' q j)) u w hu hw
  refine ⟨u, fun i j hij => ?_, fun i => ?_, fun v => ?_⟩
  · rw [key, Matrix.map_apply, hUt j i hij, rs_zero hPQ, mul_zero, zero_mul]
  · obtain ⟨hm1, hm2⟩ := chartMon_ratio (x := x) hPQ hs hs₀ (b i)
    rw [key, Matrix.map_apply, hUd, rs_mul hPQ (pow_mem hc1 m) hm1, rs_pow hPQ hc1, hc2, hm2,
      ← mul_assoc, inv_mul_cancel₀ hc0, one_mul, div_mul_cancel₀ _ (mon_ne _ hs₀ _)]
  · obtain ⟨h1, h, hh, hd⟩ := hG s hs
    rw [← lat_iff _ _ h1 hh hd u hu v]
    refine (mem_scaledTrivLat (R := kap O)).trans (forall_congr' fun q => ⟨?_, fun hq => ⟨v q, hq, (one_mul _).symm⟩⟩)
    rintro ⟨a, ha, e⟩
    rw [e, one_mul]
    exact ha

end Res

end PositivityTheory.Xgn.A_trivflagmod_at

open PositivityTheory.Xgn.A_trivflagmod_at GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagRestrict in
/- English proof (translation)
Introduce `O _ _ _ Ω _ _ K _ _ ι _ x ϖ hϖ N b H W hW hPW hϖW`. Take `⟨hpr, -, hrel, -⟩` from `SpecialIdealCorresp.proof O ϖ hϖ K ι W W hW.isPrime hϖW`. Establish `hhom` using `(VocabMultiHomogIdeal.proof VocabMultiHomog.proof _ K ι _).2 (SpecialIdealMultiHomog.proof O K ι W hW.multiHomog)`. Use `choose s₀ hs₀ using hrel.1 hW.relevant`. Establish `hPQ : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O (mcIdeal O x) ≤ specialIdeal W` using `Ideal.map_mono hPW`.

Establish `hs : mseg (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.genPt (IsLocalRing.ResidueField O) (specialIdeal W)) s₀ ≠ 0`. Use `Finset.prod_ne_zero_iff.2 fun k _ h => hs₀ k ?_` and prove the remaining obligations. Rewrite using `[← aeval_genPt_eq_zero_iff (specialIdeal W), aeval_X]`. Conclude with `h`. Take `⟨w, hw⟩` from `exists_frame hPQ hϖ H hs`.

Conclude with `⟨_, inferInstance, inferInstance, _, w, mcIdeal_genPt (specialIdeal W) hhom, hw⟩`.
-/
theorem PositivityTheory.Xgn.t_trivflagmod_at : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ (N : ℕ) (b : Fin N → K → ℤ), TrivFlagMod O ϖ x N b → ∀ (W : Ideal (MRing ι O)), IsMultiProjPrime W → (pointIdeal O x) ≤ W → (C ϖ : MRing ι O) ∈ W → TrivFlagAt W b := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x ϖ hϖ N b H W hW hPW hϖW
  obtain ⟨hpr, -, hrel, -⟩ := SpecialIdealCorresp.proof O ϖ hϖ K ι W W hW.isPrime hϖW
  have hhom := (VocabMultiHomogIdeal.proof VocabMultiHomog.proof _ K ι _).2
    (SpecialIdealMultiHomog.proof O K ι W hW.multiHomog)
  choose s₀ hs₀ using hrel.1 hW.relevant
  have hPQ : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O (mcIdeal O x) ≤ specialIdeal W :=
    Ideal.map_mono hPW
  have hs : mseg (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.genPt (IsLocalRing.ResidueField O)
      (specialIdeal W)) s₀ ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun k _ h => hs₀ k ?_
    rw [← aeval_genPt_eq_zero_iff (specialIdeal W), aeval_X]
    exact h
  obtain ⟨w, hw⟩ := exists_frame hPQ hϖ H hs
  exact ⟨_, inferInstance, inferInstance, _, w, mcIdeal_genPt (specialIdeal W) hhom, hw⟩
