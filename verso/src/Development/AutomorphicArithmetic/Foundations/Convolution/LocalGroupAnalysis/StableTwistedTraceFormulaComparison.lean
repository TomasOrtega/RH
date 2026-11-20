import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SelmerRankBoundLaurent
import Development.AutomorphicArithmetic.AdelicQuotients.QuotientHaarMeasurePushforward
import Development.AutomorphicArithmetic.AdelicQuotients.AdelicGLSplitEquiv
import Development.AutomorphicArithmetic.AdelicQuotients.QuotientMeasureSplit
import Development.AutomorphicArithmetic.AdelicQuotients.HaarUnimodularCriterion
import Development.AutomorphicArithmetic.AdelicQuotients.ExistsHaarMeasureAdelicGL
import Development.AutomorphicArithmetic.AdelicQuotients.HaarConstOfHaarExists
import Development.AutomorphicArithmetic.AdelicQuotients.LocalUnimodularOfExistsHaarMeasure
import Development.AutomorphicArithmetic.AdelicQuotients.RestrictedProductCentralizerAdelicGL
import Development.AutomorphicArithmetic.AdelicQuotients.EulerProductSupportFinite
import Development.AutomorphicArithmetic.AdelicQuotients.EulerProductOfQuotientPushforwardSupport
import Development.AutomorphicArithmetic.AdelicQuotients.OrbitalIntegralFubini
import Development.AutomorphicArithmetic.AdelicQuotients.GeometricSideAbsolutelyConvergentOfEulerFubini
import Development.AutomorphicArithmetic.AdelicQuotients.CharpolySeparableUnitSmul
import Development.AutomorphicArithmetic.AdelicQuotients.CentralizerCommutativeOfSeparableCharpoly
import Development.AutomorphicArithmetic.AdelicQuotients.HaarQuotientSubgroup
import Development.AutomorphicArithmetic.AdelicQuotients.RestrictedProductFiniteAdelicGL
import Development.AutomorphicArithmetic.AdelicQuotients.RestrictedProductExtensionOfBaseRegroup
import Development.AutomorphicArithmetic.AdelicQuotients.AdeleGaloisActionBaseChangeCompat
import Development.AutomorphicArithmetic.AdelicQuotients.AdeleGaloisActionContinuous
import Development.AutomorphicArithmetic.AdelicQuotients.AdeleBaseChangeLocalIsClosedEmbedding
import Development.AutomorphicArithmetic.AdelicQuotients.AdicCompletionIntegersBaseChangeIff
import Development.AutomorphicArithmetic.AdelicQuotients.CentralSectionLocalScalar
import Development.AutomorphicArithmetic.AdelicQuotients.CentralSectionBaseChange
import Development.AutomorphicArithmetic.AdelicQuotients.TwistedNormCentralOfBaseChangeCompat
import Development.AutomorphicArithmetic.AdelicQuotients.TwistedNormLocalOfCompat
import Development.AutomorphicArithmetic.AdelicQuotients.SeparableLocalOfSeparableScalar
import Development.AutomorphicArithmetic.AdelicQuotients.TorusCommutativeOfCentralizerCommutative
import Development.AutomorphicArithmetic.AdelicQuotients.BaseChangeTrivialExtension
import Development.AutomorphicArithmetic.AdelicQuotients.AdelicBoundOfCentralizerLocalization
import Development.AutomorphicArithmetic.AdelicQuotients.InfinitePartFiniteOfAdelicBound
import Development.AutomorphicArithmetic.AdelicQuotients.MaximalCompactNormOfUnitCriterion
import Development.AutomorphicArithmetic.AdelicQuotients.SplitCentralizerOfSplitEquiv
import Development.AutomorphicArithmetic.AdelicQuotients.GlobalOrbitalComparisonOfSplit
import Development.AutomorphicArithmetic.AdelicQuotients.OrbitalSideBaseFieldOfAbsoluteConvergence
import Development.AutomorphicArithmetic.AdelicQuotients.OrbitalSideExtensionOfAbsoluteConvergence

open MeasureTheory NumberField IsDedekindDomain Topology Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

/- English proof (translation)
Substitute `hH` using the available equality. Conclude with `h γ hγ ν hν`.
-/
private theorem match_qI {n : ℕ} {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R]
    [MeasurableSpace (GL (Fin n) R)] [MeasurableSpace (GL (Fin n) S)] {ι : R →+* S} {s : S →+* S} {l : ℕ}
    {μS : Measure (GL (Fin n) S)} {μR : Measure (GL (Fin n) R)} {c : ℂ} {φ : GL (Fin n) S → ℂ} {f : GL (Fin n) R → ℂ}
    (h : Match ι s l μS μR c φ f) (γ : GL (Fin n) R) (hγ : γ.val.charpoly.Separable) (H : Subgroup (GL (Fin n) R))
    (hH : H = Subgroup.centralizer {γ}) (ν : Measure H) (hν : ν.IsHaarMeasure) :
    (∀ δ : GL (Fin n) S, twNorm (mapGL n s) l δ = mapGL n ι γ →
      qI μS ((mapGL n ι).comp H.subtype) ν (fun x => φ (x⁻¹ * δ * mapGL n s x)) =
        c * qI μR H.subtype ν (fun x => f (x⁻¹ * γ * x))) ∧
    ((¬ ∃ δ : GL (Fin n) S, twNorm (mapGL n s) l δ = mapGL n ι γ) → qI μR H.subtype ν (fun x => f (x⁻¹ * γ * x)) = 0) := by
  subst hH
  exact h γ hγ ν hν

/- English proof (translation)
Use extensionality with `t`. Rewrite using `[Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, ← mul_assoc, ← hz t, mul_assoc, mul_assoc, mul_right_inj]`.
-/
private theorem cent_mul {G : Type} [Group G] (z g : G) (hz : ∀ x, z * x = x * z) :
    Subgroup.centralizer {g} = Subgroup.centralizer {z * g} := by
  ext t
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, ← mul_assoc, ← hz t, mul_assoc, mul_assoc,
    mul_right_inj]

/- English proof (translation)
Establish `: IsClosed (Subgroup.centralizer {g} : Set G)` using `Set.isClosed_centralizer _`. Conclude with `this.locallyCompactSpace`.
-/
private theorem lc_cent {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] (g : G) :
    LocallyCompactSpace (Subgroup.centralizer {g}) := by
  have : IsClosed (Subgroup.centralizer {g} : Set G) := Set.isClosed_centralizer _
  exact this.locallyCompactSpace

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ σ hσ n hn hp _ _ _ _ _ _ _ _ μE μF μiE μiF mE mF hμE hμF hiE hiF hmE hmF`. Take `⟨μE', μF', uE, uF, hG⟩` from `hGl F E σ hσ n hn μE μF hμE hμF`. Take `⟨aE, haE, hEE⟩` from `hC _ _ _ _ _ _ _ (hRE F E n) μE' μiE mE uE.1 hiE hmE`. Take `⟨aF, haF, hEF⟩` from `hC _ _ _ _ _ _ _ (hRF F n) μF' μiF mF uF.1 hiF hmF`. Use `⟨aE / aF, div_pos (NNReal.coe_pos.2 (pos_iff_ne_zero.2 haE)) (NNReal.coe_pos.2 (pos_iff_ne_zero.2 haF)), ?_⟩` and prove the remaining obligations.

Introduce `S φi fi φ f ci c hφi hφi' hfi hfi' hφ hoff hMi hM γ γ₁ hγ₁ hirr ν hν`. Establish `hsep : IsRegSemisimple γ` using `hirr.separable`. Take `⟨ν', hν', hGF, hGE⟩` from `hG γ γ₁ hγ₁ hsep ν hν`. Take `⟨hs1, hs2, hs3⟩` from `hS F n γ hsep`. Use `haveI : LocallyCompactSpace (TA γ) := lc_cent _`.

Use `haveI : LocallyCompactSpace (TI γ) := lc_cent _`. Use `haveI : ∀ v, LocallyCompactSpace (TF γ v) := fun v => lc_cent _`. Use `haveI : SecondCountableTopology (TA γ) := TopologicalSpace.Subtype.secondCountableTopology _`. Use `haveI : SecondCountableTopology (TI γ) := TopologicalSpace.Subtype.secondCountableTopology _`. Use `haveI : ∀ v, SecondCountableTopology (TF γ v) := fun v => TopologicalSpace.Subtype.secondCountableTopology _`.

Establish `hT` using `fun S' => hX _ _ _ _ _ _ _ (hRC _ _ _ _ _ _ _ (hRF F n) (AdelicGLn.diagonal F n γ)) ν' Measure.haar (fun _ => Measure.haar) hν' inferInstance (fun _ => inferInstance) S'`. Establish `hcF` using `(hKF F n hn γ hsep)`. Rewrite `hcF` using `[eventually_cofinite]`. Establish `hFside` using `fun (S' : Finset (Pl F)) (h1 : S ⊆ S') (h2 : hcF.toFinset ⊆ S') (b : NNReal) (hb : b ≠ 0) (hE : EulT γ ν' Measure.haar (fun _ => Measure.haar) b S') => hSF F n hn μF' μiF mF uF hiF (fun v => (hmF v).1) γ hsep ν' Measure.haar (fun _ => Measure.haar) hν' inferInstance (fun _ => inf …`. Assume the negation of the conclusion as `h`.

Conclude with `hv (h2 (hcF.mem_toFinset.2 h))⟩)`. Establish `hMi'` using `fun s : ℝ => match_qI hMi _ (hs2 s) (TI γ) (cent_mul _ _ (hL F n _).2.1) Measure.haar inferInstance`. Establish `hM'` using `fun v => match_qI (hM v) _ (hs3 v) (TF γ v) rfl Measure.haar inferInstance`. Prove the components needed by the constructor for the conclusion. Introduce `δ hδ`.

Establish `hcE` using `hK F E σ hσ n hn δ γ hsep hδ`. Rewrite `hcE` using `[eventually_cofinite]`. Take `⟨b, hb, hE⟩` from `hT (S ∪ hcF.toFinset ∪ hcE.toFinset)`. Establish `h1 : S ⊆ S ∪ hcF.toFinset ∪ hcE.toFinset` using `Finset.subset_union_left.trans Finset.subset_union_left`. Take `⟨m1, e1⟩` from `hFside _ h1 (Finset.subset_union_right.trans Finset.subset_union_left) b hb hE`.

Take `⟨m2, e2⟩` from `hSE F E σ hσ n hn μE' μiE mE uE hiE (fun v => (hmE v).1) γ hsep δ hδ ν' Measure.haar (fun _ => Measure.haar) hν' inferInstance (fun _ => inferInstance) _ aE b haE hb hE (hEE _) φi φ hφi hφi' (fun v => (hφ v).1) (fun v hv => ⟨(hoff v fun h => hv (h1 h)).1, by`. Assume the negation of the conclusion as `h`. Conclude with `hv (Finset.subset_union_right (hcE.mem_toFinset.2 h))⟩)`. Take `⟨n1, n2⟩` from `hN F E σ hσ n hn δ γ hδ`. Rewrite using `[hGF _ m1, hGE δ hδ _ m2, e1, e2]`.

Establish `i1` using `fun s : ℝ => (hMi' s).1 (pI E n (zA E n s) * pI E n (AdelicGLn.diagonal E n δ)) (by`. Rewrite using `[hZ F E σ hσ n hn, n1, ← map_mul])`. Establish `i2` using `fun v => (hM' v).1 _ (n2 v)`. Simplify using `only [i1, i2]`. Rewrite using `[integral_const_mul, Finset.prod_mul_distrib, ← Finset.prod_subset h1 fun v _ hv => (hoff v hv).2.2]`.

Establish `: ((aF : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast haF`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Introduce `hno`. Distinguish the cases in `hi : ∃ δ, twNorm (mapGL n (galInf σ)) (Module.finrank F E) δ = mapGL n (infMap F E) (pI F n (AdelicGLn.diagonal F n γ))`.

Establish `: ¬ ∀ v : Pl F, ∃ δ, twNorm (mapGL n (galFin σ v)) (Module.finrank F E) δ = mapGL n (incFin E v) (finAt v (AdelicGLn.diagonal F n γ))` using `fun h => hno (hH F E σ hσ n hn hp γ hirr hi h)`. Take `⟨v, hv⟩` from `not_forall.1 this`. Take `⟨b, hb, hE⟩` from `hT (S ∪ hcF.toFinset ∪ {v})`. Take `⟨m1, e1⟩` from `hFside _ (Finset.subset_union_left.trans Finset.subset_union_left) (Finset.subset_union_right.trans Finset.subset_union_left) b hb hE`. Rewrite using `[hGF _ m1, e1, Finset.prod_eq_zero (i := v) (by simp) ((hM' v).2 hv), mul_zero]`.

Take `⟨b, hb, hE⟩` from `hT (S ∪ hcF.toFinset)`. Take `⟨m1, e1⟩` from `hFside _ Finset.subset_union_left Finset.subset_union_right b hb hE`. Establish `i1` using `fun s : ℝ => (hMi' s).2 (by`. Introduce and unpack `⟨δ, hδ⟩`. Use `hi ⟨(pI E n (zA E n s))⁻¹ * δ, ?_⟩` and prove the remaining obligations.

Establish `h` using `hZ F E σ hσ n hn s ((pI E n (zA E n s))⁻¹ * δ)`. Rewrite `h` using `[mul_inv_cancel_left, hδ, map_mul]`. Conclude with `(mul_left_cancel h).symm)`. Rewrite using `[hGF _ m1, e1]`. Simplify using `only [i1, integral_zero, mul_zero, zero_mul]`.
-/
private theorem main (hGl : Glob) (hC : HaarConst) (hX : HaarEx) (hRF : RPF) (hRE : RPE) (hRC : RPCen) (hSF : SideF) (hSE : SideE)
    (hK : K1) (hKF : SelmerRankBoundLaurent) (hH : H1) (hZ : ZNorm) (hN : LocNorm) (hS : SepLoc) (hL : CentLoc) : G4 := by
  classical
  intro F E _ _ _ _ _ _ σ hσ n hn hp _ _ _ _ _ _ _ _ μE μF μiE μiF mE mF hμE hμF hiE hiF hmE hmF
  obtain ⟨μE', μF', uE, uF, hG⟩ := hGl F E σ hσ n hn μE μF hμE hμF
  obtain ⟨aE, haE, hEE⟩ := hC _ _ _ _ _ _ _ (hRE F E n) μE' μiE mE uE.1 hiE hmE
  obtain ⟨aF, haF, hEF⟩ := hC _ _ _ _ _ _ _ (hRF F n) μF' μiF mF uF.1 hiF hmF
  refine ⟨aE / aF, div_pos (NNReal.coe_pos.2 (pos_iff_ne_zero.2 haE)) (NNReal.coe_pos.2 (pos_iff_ne_zero.2 haF)), ?_⟩
  intro S φi fi φ f ci c hφi hφi' hfi hfi' hφ hoff hMi hM γ γ₁ hγ₁ hirr ν hν
  have hsep : IsRegSemisimple γ := hirr.separable
  obtain ⟨ν', hν', hGF, hGE⟩ := hG γ γ₁ hγ₁ hsep ν hν
  obtain ⟨hs1, hs2, hs3⟩ := hS F n γ hsep
  haveI : LocallyCompactSpace (TA γ) := lc_cent _
  haveI : LocallyCompactSpace (TI γ) := lc_cent _
  haveI : ∀ v, LocallyCompactSpace (TF γ v) := fun v => lc_cent _
  haveI : SecondCountableTopology (TA γ) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SecondCountableTopology (TI γ) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : ∀ v, SecondCountableTopology (TF γ v) := fun v => TopologicalSpace.Subtype.secondCountableTopology _
  have hT := fun S' => hX _ _ _ _ _ _ _ (hRC _ _ _ _ _ _ _ (hRF F n) (AdelicGLn.diagonal F n γ)) ν' Measure.haar
    (fun _ => Measure.haar) hν' inferInstance (fun _ => inferInstance) S'
  have hcF := (hKF F n hn γ hsep)
  rw [eventually_cofinite] at hcF
  have hFside := fun (S' : Finset (Pl F)) (h1 : S ⊆ S') (h2 : hcF.toFinset ⊆ S') (b : NNReal) (hb : b ≠ 0)
      (hE : EulT γ ν' Measure.haar (fun _ => Measure.haar) b S') =>
    hSF F n hn μF' μiF mF uF hiF (fun v => (hmF v).1) γ hsep ν' Measure.haar (fun _ => Measure.haar) hν' inferInstance
      (fun _ => inferInstance) S' aF b haF hb hE (hEF S') fi f hfi hfi' (fun v => (hφ v).2.2.1)
      (fun v hv => ⟨(hoff v fun h => hv (h1 h)).2.1, by
        by_contra h
        exact hv (h2 (hcF.mem_toFinset.2 h))⟩)
  have hMi' := fun s : ℝ => match_qI hMi _ (hs2 s) (TI γ) (cent_mul _ _ (hL F n _).2.1) Measure.haar inferInstance
  have hM' := fun v => match_qI (hM v) _ (hs3 v) (TF γ v) rfl Measure.haar inferInstance
  constructor
  · intro δ hδ
    have hcE := hK F E σ hσ n hn δ γ hsep hδ
    rw [eventually_cofinite] at hcE
    obtain ⟨b, hb, hE⟩ := hT (S ∪ hcF.toFinset ∪ hcE.toFinset)
    have h1 : S ⊆ S ∪ hcF.toFinset ∪ hcE.toFinset := Finset.subset_union_left.trans Finset.subset_union_left
    obtain ⟨m1, e1⟩ := hFside _ h1 (Finset.subset_union_right.trans Finset.subset_union_left) b hb hE
    obtain ⟨m2, e2⟩ := hSE F E σ hσ n hn μE' μiE mE uE hiE (fun v => (hmE v).1) γ hsep δ hδ ν' Measure.haar (fun _ => Measure.haar)
      hν' inferInstance (fun _ => inferInstance) _ aE b haE hb hE (hEE _) φi φ hφi hφi' (fun v => (hφ v).1)
      (fun v hv => ⟨(hoff v fun h => hv (h1 h)).1, by
        by_contra h
        exact hv (Finset.subset_union_right (hcE.mem_toFinset.2 h))⟩)
    obtain ⟨n1, n2⟩ := hN F E σ hσ n hn δ γ hδ
    rw [hGF _ m1, hGE δ hδ _ m2, e1, e2]
    have i1 := fun s : ℝ => (hMi' s).1 (pI E n (zA E n s) * pI E n (AdelicGLn.diagonal E n δ)) (by
      rw [hZ F E σ hσ n hn, n1, ← map_mul])
    have i2 := fun v => (hM' v).1 _ (n2 v)
    simp only [i1, i2]
    rw [integral_const_mul, Finset.prod_mul_distrib, ← Finset.prod_subset h1 fun v _ hv => (hoff v hv).2.2]
    have : ((aF : ℝ) : ℂ) ≠ 0 := by exact_mod_cast haF
    push_cast
    field_simp
  · intro hno
    by_cases hi : ∃ δ, twNorm (mapGL n (galInf σ)) (Module.finrank F E) δ =
        mapGL n (infMap F E) (pI F n (AdelicGLn.diagonal F n γ))
    · have : ¬ ∀ v : Pl F, ∃ δ, twNorm (mapGL n (galFin σ v)) (Module.finrank F E) δ =
          mapGL n (incFin E v) (finAt v (AdelicGLn.diagonal F n γ)) := fun h => hno (hH F E σ hσ n hn hp γ hirr hi h)
      obtain ⟨v, hv⟩ := not_forall.1 this
      obtain ⟨b, hb, hE⟩ := hT (S ∪ hcF.toFinset ∪ {v})
      obtain ⟨m1, e1⟩ := hFside _ (Finset.subset_union_left.trans Finset.subset_union_left)
        (Finset.subset_union_right.trans Finset.subset_union_left) b hb hE
      rw [hGF _ m1, e1, Finset.prod_eq_zero (i := v) (by simp) ((hM' v).2 hv), mul_zero]
    · obtain ⟨b, hb, hE⟩ := hT (S ∪ hcF.toFinset)
      obtain ⟨m1, e1⟩ := hFside _ Finset.subset_union_left Finset.subset_union_right b hb hE
      have i1 := fun s : ℝ => (hMi' s).2 (by
        rintro ⟨δ, hδ⟩
        refine hi ⟨(pI E n (zA E n s))⁻¹ * δ, ?_⟩
        have h := hZ F E σ hσ n hn s ((pI E n (zA E n s))⁻¹ * δ)
        rw [mul_inv_cancel_left, hδ, map_mul] at h
        exact (mul_left_cancel h).symm)
      rw [hGF _ m1, e1]
      simp only [i1, integral_zero, mul_zero, zero_mul]

/- English proof (translation)
Introduce `_ _ _ n3 n5 _ p2 k1 h1`. Establish `qpush : QPush` using `UpperTheory.quotient_haar_measure_pushforward`. Establish `splitEq : SplitEquiv` using `UpperTheory.adelicGL_split_equiv`. Establish `splitQ : SplitQ` using `UpperTheory.quotient_measure_split`. Establish `uniOf : UniOf` using `UpperTheory.haar_unimodular_criterion`.

Establish `haarEx : HaarEx` using `UpperTheory.exists_haarMeasure_adelicGL`. Establish `haarConst : HaarConst` using `UpperTheory.haar_const_of_haar_exists haarEx`. Establish `uniLoc : UniLoc` using `UpperTheory.local_unimodular_of_exists_haar_measure haarEx`. Establish `rpCen : RPCen` using `UpperTheory.restrictedProduct_centralizer_adelicGL`. Establish `euler : Euler` using `UpperTheory.eulerProduct_of_quotient_pushforward_support qpush UpperTheory.euler_product_support_finite`.

Establish `sideAbs : SideAbs` using `UpperTheory.geometric_side_absolutely_convergent_of_euler_fubini euler UpperTheory.orbital_integral_fubini`. Establish `qsub : QSub` using `UpperTheory.haar_quotient_subgroup`. Establish `rpf : RPF` using `UpperTheory.restrictedProduct_finite_adelicGL`. Establish `rpe : RPE` using `UpperTheory.restrictedProduct_extension_of_base_regroup rpf`. Establish `compat : Compat` using `UpperTheory.adele_galois_action_baseChange_compat`.

Establish `galCont : GalCont` using `UpperTheory.adele_galois_action_continuous compat rpe`. Establish `locEmb : LocEmb` using `UpperTheory.adele_baseChange_local_isClosedEmbedding`. Establish `unitIff : UnitIff` using `UpperTheory.adicCompletion_integers_baseChange_iff`. Establish `centLoc : CentLoc` using `UpperTheory.centralSection_local_scalar`. Establish `centBC : CentBC` using `UpperTheory.centralSection_baseChange`.

Establish `zNorm : ZNorm` using `UpperTheory.twistedNorm_central_of_baseChange_compat compat centLoc centBC`. Establish `locNorm : LocNorm` using `UpperTheory.twistedNorm_local_of_compat compat`. Establish `sepLoc : SepLoc` using `UpperTheory.separableLocal_of_separableScalar UpperTheory.charpoly_separable_unit_smul centLoc`. Establish `tComm : TComm` using `UpperTheory.torusCommutative_of_centralizerCommutative UpperTheory.centralizer_commutative_of_separable_charpoly`. Establish `triv : Triv` using `UpperTheory.baseChange_trivial_extension`.

Establish `boundE : BoundE` using `UpperTheory.adelicBound_of_centralizer_localization n5 compat centLoc rpe`. Establish `infF : InfF` using `UpperTheory.infinitePart_finite_of_adelicBound p2 triv boundE`. Establish `k1F : SelmerRankBoundLaurent` using `UpperTheory.maximalCompactNorm_of_unit_criterion k1 triv unitIff compat`. Establish `spl : Spl` using `UpperTheory.splitCentralizer_of_splitEquiv splitEq n5 centBC`. Establish `glob : Glob` using `UpperTheory.globalOrbitalComparison_of_split qsub splitQ uniOf tComm spl n3 n5 centBC`.

Establish `sideF : SideF` using `UpperTheory.orbitalSideBaseField_of_absoluteConvergence sideAbs rpf rpCen uniLoc uniOf tComm sepLoc centLoc infF`. Establish `sideE : SideE` using `UpperTheory.orbitalSideExtension_of_absoluteConvergence sideAbs rpf rpe rpCen uniLoc uniOf tComm sepLoc centLoc compat galCont locEmb unitIff locNorm boundE n3 n5 p2`. Conclude with `main glob haarConst haarEx rpf rpe rpCen sideF sideE k1 k1F h1 zNorm locNorm sepLoc centLoc`.
-/
theorem UpperTheory.ConvolutionTheory.G.stable_twisted_trace_formula_comparison :
    Q1 → Q2 → Q3 → N3 → N5 → P1 → P2 → K1 → H1 → G4 := by
  intro _ _ _ n3 n5 _ p2 k1 h1
  have qpush : QPush := UpperTheory.quotient_haar_measure_pushforward
  have splitEq : SplitEquiv := UpperTheory.adelicGL_split_equiv
  have splitQ : SplitQ := UpperTheory.quotient_measure_split
  have uniOf : UniOf := UpperTheory.haar_unimodular_criterion
  have haarEx : HaarEx := UpperTheory.exists_haarMeasure_adelicGL
  have haarConst : HaarConst := UpperTheory.haar_const_of_haar_exists haarEx
  have uniLoc : UniLoc := UpperTheory.local_unimodular_of_exists_haar_measure haarEx
  have rpCen : RPCen := UpperTheory.restrictedProduct_centralizer_adelicGL
  have euler : Euler := UpperTheory.eulerProduct_of_quotient_pushforward_support qpush UpperTheory.euler_product_support_finite
  have sideAbs : SideAbs := UpperTheory.geometric_side_absolutely_convergent_of_euler_fubini euler UpperTheory.orbital_integral_fubini
  have qsub : QSub := UpperTheory.haar_quotient_subgroup
  have rpf : RPF := UpperTheory.restrictedProduct_finite_adelicGL
  have rpe : RPE := UpperTheory.restrictedProduct_extension_of_base_regroup rpf
  have compat : Compat := UpperTheory.adele_galois_action_baseChange_compat
  have galCont : GalCont := UpperTheory.adele_galois_action_continuous compat rpe
  have locEmb : LocEmb := UpperTheory.adele_baseChange_local_isClosedEmbedding
  have unitIff : UnitIff := UpperTheory.adicCompletion_integers_baseChange_iff
  have centLoc : CentLoc := UpperTheory.centralSection_local_scalar
  have centBC : CentBC := UpperTheory.centralSection_baseChange
  have zNorm : ZNorm := UpperTheory.twistedNorm_central_of_baseChange_compat compat centLoc centBC
  have locNorm : LocNorm := UpperTheory.twistedNorm_local_of_compat compat
  have sepLoc : SepLoc := UpperTheory.separableLocal_of_separableScalar UpperTheory.charpoly_separable_unit_smul centLoc
  have tComm : TComm := UpperTheory.torusCommutative_of_centralizerCommutative UpperTheory.centralizer_commutative_of_separable_charpoly
  have triv : Triv := UpperTheory.baseChange_trivial_extension
  have boundE : BoundE := UpperTheory.adelicBound_of_centralizer_localization n5 compat centLoc rpe
  have infF : InfF := UpperTheory.infinitePart_finite_of_adelicBound p2 triv boundE
  have k1F : SelmerRankBoundLaurent := UpperTheory.maximalCompactNorm_of_unit_criterion k1 triv unitIff compat
  have spl : Spl := UpperTheory.splitCentralizer_of_splitEquiv splitEq n5 centBC
  have glob : Glob := UpperTheory.globalOrbitalComparison_of_split qsub splitQ uniOf tComm spl n3 n5 centBC
  have sideF : SideF := UpperTheory.orbitalSideBaseField_of_absoluteConvergence sideAbs rpf rpCen uniLoc uniOf tComm sepLoc centLoc infF
  have sideE : SideE := UpperTheory.orbitalSideExtension_of_absoluteConvergence sideAbs rpf rpe rpCen uniLoc uniOf tComm sepLoc centLoc compat galCont locEmb unitIff locNorm boundE n3 n5 p2
  exact main glob haarConst haarEx rpf rpe rpCen sideF sideE k1 k1F h1 zNorm locNorm sepLoc centLoc
