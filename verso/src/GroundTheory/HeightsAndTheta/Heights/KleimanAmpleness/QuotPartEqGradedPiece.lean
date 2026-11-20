import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraSide
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideFurther
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PQuotPartGraded
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgCechSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial Filter ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cechHc cechZc cechBc cechCc locPart quotPart Cell cellMon)

noncomputable section

/- English proof (translation)
Establish `hset : {p : MvPolynomial (Σ k, ι k) F | (∀ k, 0 ≤ m k) ∧ IsMultiHomog p (fun k => (m k).toNat)} = (weightedHomogeneousSubmodule F (NumbersDVR.blockWeight ι) (fun k => (m k).toNat) : Set _)`. Use extensionality with `p`. Simplify using `only [Set.mem_ofPred_eq, SetLike.mem_coe, mem_weightedHomogeneousSubmodule, hm, implies_true, true_and]`. Conclude with `(Bridge.isMultiHomog_iff p _).symm`. Rewrite using `[quotPart, hset, NumbersDVR.gradedPiece]`.

Use `conv_rhs => rw [← Submodule.span_eq (weightedHomogeneousSubmodule F _ _), Submodule.map_span]`. Both sides reduce to the same expression.
-/
theorem quotPart_eq_gradedPiece {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] (V : Ideal (MvPolynomial (Σ k, ι k) F)) (m : K → ℤ) (hm : ∀ k, 0 ≤ m k) :
    quotPart F V m = NumbersDVR.gradedPiece V (fun k => (m k).toNat) := by
  have hset : {p : MvPolynomial (Σ k, ι k) F | (∀ k, 0 ≤ m k) ∧ IsMultiHomog p (fun k => (m k).toNat)} =
      (weightedHomogeneousSubmodule F (NumbersDVR.blockWeight ι) (fun k => (m k).toNat) : Set _) := by
    ext p
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe, mem_weightedHomogeneousSubmodule, hm, implies_true, true_and]
    exact (Bridge.isMultiHomog_iff p _).symm
  rw [quotPart, hset, NumbersDVR.gradedPiece]
  conv_rhs => rw [← Submodule.span_eq (weightedHomogeneousSubmodule F _ _), Submodule.map_span]
  rfl

/- English proof (translation)
Introduce `d hd k`. Rewrite `hd` using `[mem_support_iff, coeff_one]`. Use `split_ifs at hd with h`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Conclude with `absurd rfl hd`.
-/
theorem isMultiHomog_one {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] :
    IsMultiHomog (1 : MRingOver S ι) 0 := by
  intro d hd k
  classical
  rw [mem_support_iff, coeff_one] at hd
  split_ifs at hd with h
  · subst h
    simp
  · exact absurd rfl hd

/- English proof (translation)
Introduce `F _ K _ _ ι _ _ V hV`. Establish `hV' : IsMultiHomogIdeal V` using `(Bridge.isMultiHomogIdeal_iff V).mp hV`. Establish `hG : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.IsMGraded F ι (quotPart F V)` using `HilbertSamuel.QuotPartGraded.proof F K ι V hV'`. Take `⟨-, ⟨c₁, h₁⟩, ⟨c₂, h₂⟩, -⟩` from `hS F K ι (MvPolynomial (Σ k, ι k) F ⧸ V) (quotPart F V) inferInstance inferInstance hG`. Take `⟨c₃, h₃⟩` from `hI F K ι (MvPolynomial (Σ k, ι k) F ⧸ V) (quotPart F V) inferInstance inferInstance hG`.

Use `filter_upwards [eventually_ge_atTop (fun _ : K => max (max c₁ c₂) (max c₃ 0))] with m hm`. Establish `hk : ∀ k, max (max c₁ c₂) (max c₃ 0) ≤ m k` using `fun k => hm k`. Use `⟨fun i hi => h₁ m i hi fun k => le_trans (by omega) (hk k), ?_⟩` and prove the remaining obligations. Set `Z` to `cechZc ι (quotPart F V) m 0`. Establish `hmem : ∀ x ∈ quotPart F V m, (fun _ => LocalizedModule.mk x 1 : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.CechC F ι (MvPolynomial (Σ k, ι k) F ⧸ V) 0) ∈ Z`.

Introduce `x hx`. Use `HilbertSamuel.GenTwistGenerated.mem_cechZc_zero (fun J => ?_) (HilbertSamuel.GenTwistGenerated.cechD_const x)` and prove the remaining obligations. Use `Submodule.subset_span ⟨x, 1, 0, isMultiHomog_one, ?_, rfl⟩` and prove the remaining obligations. Use `hx using 2` and compare the differences between its conclusion and the goal. Use extensionality with `k`.

Simplify using the standard rewrite rules. Set `φ : quotPart F V m →ₗ[F] Z` to `{ toFun := fun x => ⟨fun _ => LocalizedModule.mk x.1 1, hmem x.1 x.2⟩ map_add' := fun x y => by`. Use extensionality with `I`. Simplify using the standard rewrite rules. Use the proof step `map_smul' := fun r x => by`.

Use extensionality with `I`. Simplify using `[LocalizedModule.smul'_mk] }`. Establish `hinj : Function.Injective φ`. Introduce `x y hxy`. Establish `hsub : x.1 - y.1 = 0`.

Use `h₃ m (fun k => le_trans (by omega) (hk k)) _ (Submodule.sub_mem _ x.2 y.2) fun I => ?_` and prove the remaining obligations. Establish `h` using `congrFun (congrArg Subtype.val hxy) I`. Express the relevant statement in the definitionally equal form `LocalizedModule.mk x.1 1 = LocalizedModule.mk y.1 1 at h`. Express the relevant statement in the definitionally equal form `LocalizedModule.mkLinearMap (cellMon F I.1) _ (x.1 - y.1) = 0`. Rewrite using `[map_sub]`.

Conclude with `sub_eq_zero.mpr h`. Conclude with `Subtype.ext (sub_eq_zero.mp hsub)`. Establish `hsurj : Function.Surjective φ`. Introduce and unpack `⟨z, hz⟩`. Take `⟨x, hx, hzx⟩` from `h₂ m (fun k => le_trans (by omega) (hk k)) z hz`.

Conclude with `⟨⟨x, hx⟩, Subtype.ext (funext fun I => (hzx I).symm)⟩`. Establish `hbot : (cechBc ι (quotPart F V) m 0).comap (cechZc ι (quotPart F V) m 0).subtype = ⊥`. Rewrite using `[cechBc, Submodule.comap_bot, Submodule.ker_subtype]`. Establish `e2 : cechHc ι (quotPart F V) m 0 ≃ₗ[F] Z` using `Submodule.quotEquivOfEqBot _ hbot`. Establish `hm0 : ∀ k, 0 ≤ m k` using `fun k => le_trans (by omega) (hk k)`.

Rewrite using `[e2.finrank_eq, ← (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).finrank_eq, NumbersDVR.hilbFn, if_pos hm0, quotPart_eq_gradedPiece V m hm0]`.
-/
theorem MultiSerre.proof (hS : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.TheoremSStatement) (hI : SectionMapInj.Statement) :
    MultiSerre.Statement := by
  intro F _ K _ _ ι _ _ V hV
  have hV' : IsMultiHomogIdeal V := (Bridge.isMultiHomogIdeal_iff V).mp hV
  have hG : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.IsMGraded F ι (quotPart F V) :=
    HilbertSamuel.QuotPartGraded.proof F K ι V hV'
  obtain ⟨-, ⟨c₁, h₁⟩, ⟨c₂, h₂⟩, -⟩ :=
    hS F K ι (MvPolynomial (Σ k, ι k) F ⧸ V) (quotPart F V) inferInstance inferInstance hG
  obtain ⟨c₃, h₃⟩ := hI F K ι (MvPolynomial (Σ k, ι k) F ⧸ V) (quotPart F V) inferInstance inferInstance hG
  filter_upwards [eventually_ge_atTop (fun _ : K => max (max c₁ c₂) (max c₃ 0))] with m hm
  have hk : ∀ k, max (max c₁ c₂) (max c₃ 0) ≤ m k := fun k => hm k
  refine ⟨fun i hi => h₁ m i hi fun k => le_trans (by omega) (hk k), ?_⟩

  let Z := cechZc ι (quotPart F V) m 0
  have hmem : ∀ x ∈ quotPart F V m, (fun _ => LocalizedModule.mk x 1 : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.CechC F ι
      (MvPolynomial (Σ k, ι k) F ⧸ V) 0) ∈ Z := by
    intro x hx
    refine HilbertSamuel.GenTwistGenerated.mem_cechZc_zero (fun J => ?_)
      (HilbertSamuel.GenTwistGenerated.cechD_const x)
    refine Submodule.subset_span ⟨x, 1, 0, isMultiHomog_one, ?_, rfl⟩
    convert hx using 2
    ext k
    simp
  let φ : quotPart F V m →ₗ[F] Z :=
    { toFun := fun x => ⟨fun _ => LocalizedModule.mk x.1 1, hmem x.1 x.2⟩
      map_add' := fun x y => by
        ext I
        simp
      map_smul' := fun r x => by
        ext I
        simp [LocalizedModule.smul'_mk] }
  have hinj : Function.Injective φ := by
    intro x y hxy
    have hsub : x.1 - y.1 = 0 := by
      refine h₃ m (fun k => le_trans (by omega) (hk k)) _ (Submodule.sub_mem _ x.2 y.2) fun I => ?_
      have h := congrFun (congrArg Subtype.val hxy) I
      change LocalizedModule.mk x.1 1 = LocalizedModule.mk y.1 1 at h
      change LocalizedModule.mkLinearMap (cellMon F I.1) _ (x.1 - y.1) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr h
    exact Subtype.ext (sub_eq_zero.mp hsub)
  have hsurj : Function.Surjective φ := by
    rintro ⟨z, hz⟩
    obtain ⟨x, hx, hzx⟩ := h₂ m (fun k => le_trans (by omega) (hk k)) z hz
    exact ⟨⟨x, hx⟩, Subtype.ext (funext fun I => (hzx I).symm)⟩
  have hbot : (cechBc ι (quotPart F V) m 0).comap (cechZc ι (quotPart F V) m 0).subtype = ⊥ := by
    rw [cechBc, Submodule.comap_bot, Submodule.ker_subtype]
  have e2 : cechHc ι (quotPart F V) m 0 ≃ₗ[F] Z := Submodule.quotEquivOfEqBot _ hbot
  have hm0 : ∀ k, 0 ≤ m k := fun k => le_trans (by omega) (hk k)
  rw [e2.finrank_eq, ← (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).finrank_eq, NumbersDVR.hilbFn, if_pos hm0,
    quotPart_eq_gradedPiece V m hm0]

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
