import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensApply
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.AvgTens
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsLCProd

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

open scoped RestrictedProduct

namespace UpperTheory.ConvolutionTheory.GM.CompactClopenAverage

section Gen

/- English proof (translation)
Establish `hle : (Filter.cofinite : Filter ι) ≤ Filter.principal Tᶜ`. Rewrite using `[Filter.le_principal_iff, Filter.mem_cofinite, compl_compl]`. Conclude with `hT`. Establish `Y : IsCompact ((↑) ⁻¹' (Set.univ.pi D) : Set (Πʳ i, [R i, A i]_[Filter.principal Tᶜ]))`. Use `RestrictedProduct.isEmbedding_coe_of_principal.isCompact_preimage_iff ?_ |>.mpr (isCompact_univ_pi hD)` and prove the remaining obligations.

Rewrite using `[RestrictedProduct.range_coe_principal]`. Introduce `f hf i hi`. Conclude with `hDA i hi (hf i trivial)`. Use `Y.image (RestrictedProduct.continuous_inclusion hle) using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `⟨⟨x, Filter.eventually_principal.2 fun i hi => hDA i hi (hx i)⟩, fun i _ => hx i, rfl⟩` and prove the remaining obligations. Introduce and unpack `⟨y, hy, rfl⟩ i`. Conclude with `hy i trivial`.
-/
private theorem rp_compact {ι : Type*} {R : ι → Type*} [∀ i, TopologicalSpace (R i)] {A : ∀ i, Set (R i)}
    (D : ∀ i, Set (R i)) (hD : ∀ i, IsCompact (D i)) (T : Set ι) (hT : T.Finite)
    (hDA : ∀ i, i ∉ T → D i ⊆ A i) : IsCompact {x : Πʳ i, [R i, A i] | ∀ i, x i ∈ D i} := by
  have hle : (Filter.cofinite : Filter ι) ≤ Filter.principal Tᶜ := by
    rw [Filter.le_principal_iff, Filter.mem_cofinite, compl_compl]
    exact hT
  have Y : IsCompact ((↑) ⁻¹' (Set.univ.pi D) : Set (Πʳ i, [R i, A i]_[Filter.principal Tᶜ])) := by
    refine RestrictedProduct.isEmbedding_coe_of_principal.isCompact_preimage_iff ?_ |>.mpr
      (isCompact_univ_pi hD)
    rw [RestrictedProduct.range_coe_principal]
    intro f hf i hi
    exact hDA i hi (hf i trivial)
  convert Y.image (RestrictedProduct.continuous_inclusion hle) using 1
  ext x
  constructor
  · intro hx
    refine ⟨⟨x, Filter.eventually_principal.2 fun i hi => hDA i hi (hx i)⟩, fun i _ => hx i, rfl⟩
  · rintro ⟨y, hy, rfl⟩ i
    exact hy i trivial

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qf48.isLC_prod T f h`.
-/
private theorem isLC_prod {X ι : Type*} [TopologicalSpace X] (T : Finset ι) (f : ι → X → ℂ)
    (h : ∀ i ∈ T, IsLocallyConstant (f i)) : IsLocallyConstant fun x => ∏ i ∈ T, f i x :=
  _root_.UpperTheory.Reformulated.B.Qf48.isLC_prod T f h

/- English proof (translation)
The claim follows from `Continuous.units_map _ (Continuous.matrix_map continuous_id hf)`.
-/
private theorem continuous_mapGL' {m : ℕ} {R S : Type*} [CommRing R] [CommRing S] [TopologicalSpace R]
    [TopologicalSpace S] (f : R →+* S) (hf : Continuous f) : Continuous (mapGL m f) :=
  Continuous.units_map _ (Continuous.matrix_map continuous_id hf)

end Gen

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

/- English proof (translation)
Assemble the required witnesses or components as `⟨rfl⟩`.
-/
private theorem liesOver_under (w : Pl E) : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩

/- English proof (translation)
The claim follows from `HeightOneSpectrum.ext w.2.over.symm`.
-/
private theorem under_eq {v : Pl F} (w : PlacesOver E v) : w.1.under (𝓞 F) = v :=
  HeightOneSpectrum.ext w.2.over.symm

/- English proof (translation)
Use `(hS.biUnion fun v _ => Set.finite_range (Subtype.val : PlacesOver E v → Pl E)).subset ?_` and prove the remaining obligations. Introduce `w hw`. Conclude with `Set.mem_biUnion hw ⟨⟨w, liesOver_under w⟩, rfl⟩`.
-/
private theorem finite_under (S : Set (Pl F)) (hS : S.Finite) :
    {w : Pl E | w.under (𝓞 F) ∈ S}.Finite := by
  refine (hS.biUnion fun v _ => Set.finite_range (Subtype.val : PlacesOver E v → Pl E)).subset ?_
  intro w hw
  exact Set.mem_biUnion hw ⟨⟨w, liesOver_under w⟩, rfl⟩

private noncomputable def pv (v : Pl F) (x : AdelicGLn.FiniteAdelicGL E n) : GL (Fin n) (CompletionsOver E v) :=
  mapGL n (atFin v) (finEmb E n x)

/- English proof (translation)
Establish `h` using `AdelicGLn.prodEquiv_apply_snd E n (finEmb E n x) a b`. Rewrite `h` using `[prodEquiv_finEmb]`. Conclude with `h.symm`.
-/
private theorem finEmb_entry (x : AdelicGLn.FiniteAdelicGL E n) (a b : Fin n) :
    ((finEmb E n x : AdelicGLn.AdelicGL E n) a b).2 = x a b := by
  have h := AdelicGLn.prodEquiv_apply_snd E n (finEmb E n x) a b
  rw [prodEquiv_finEmb] at h
  exact h.symm

/- English proof (translation)
Use `Units.ext (Matrix.ext fun a b => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((finEmb E n x : AdelicGLn.AdelicGL E n) a b).2 w.1 = _`. Rewrite using `[finEmb_entry]`. Both sides reduce to the same expression.
-/
private theorem cmp_pv {v : Pl F} (w : PlacesOver E v) (x : AdelicGLn.FiniteAdelicGL E n) :
    cmp w (pv v x) = AdelicGLn.finiteRestrictedEquiv E n x w.1 := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  change ((finEmb E n x : AdelicGLn.AdelicGL E n) a b).2 w.1 = _
  rw [finEmb_entry]
  rfl

/- English proof (translation)
The claim follows from `continuous_pi fun w => (RestrictedProduct.continuous_eval w.1).comp continuous_snd`.
-/
private theorem continuous_atFin (v : Pl F) : Continuous (atFin (E := E) v) :=
  continuous_pi fun w => (RestrictedProduct.continuous_eval w.1).comp continuous_snd

/- English proof (translation)
The claim follows from `(continuous_mapGL' _ (continuous_atFin v)).comp continuous_finEmb`.
-/
private theorem continuous_pv (v : Pl F) : Continuous (pv (E := E) (n := n) v) :=
  (continuous_mapGL' _ (continuous_atFin v)).comp continuous_finEmb

/- English proof (translation)
The claim follows from `continuous_mapGL' _ (continuous_apply w)`.
-/
private theorem continuous_cmp {v : Pl F} (w : PlacesOver E v) : Continuous (cmp (n := n) w) :=
  continuous_mapGL' _ (continuous_apply w)

private def U (S : Finset (Pl F)) : Set (AdelicGLn.FiniteAdelicGL E n) :=
  {x | ∀ w : Pl E, w.under (𝓞 F) ∉ S →
    AdelicGLn.finiteRestrictedEquiv E n x w ∈ GLnLocal.integralGL (w.adicCompletion E) n}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Simplify using `only [U, Set.setOf_forall]`. Use `isClosed_iInter fun w => isClosed_iInter fun _ => ?_` and prove the remaining obligations. Conclude with `(GLnLocal.isCompact_integralGL (w.adicCompletion E) n).isClosed.preimage ((RestrictedProduct.continuous_eval w).comp (AdelicGLn.finiteRestrictedEquiv E n).continuous)`. Establish `h` using `RestrictedProduct.isOpen_forall_imp_mem (R := fun w : Pl E => GL (Fin n) (w.adicCompletion E)) (A := fun w => (GLnLocal.integralGL (w.adicCompletion E) n : Set _)) (fun w => GLnLocal.isOpen_integralGL (w.adicCompletion E) n) (p := fun w => w.under (𝓞 F) ∉ S)`.

Conclude with `h.preimage (AdelicGLn.finiteRestrictedEquiv E n).continuous`.
-/
private theorem isClopen_U (S : Finset (Pl F)) : IsClopen (U (E := E) (n := n) S) := by
  constructor
  · simp only [U, Set.setOf_forall]
    refine isClosed_iInter fun w => isClosed_iInter fun _ => ?_
    exact (GLnLocal.isCompact_integralGL (w.adicCompletion E) n).isClosed.preimage
      ((RestrictedProduct.continuous_eval w).comp (AdelicGLn.finiteRestrictedEquiv E n).continuous)
  · have h := RestrictedProduct.isOpen_forall_imp_mem
      (R := fun w : Pl E => GL (Fin n) (w.adicCompletion E))
      (A := fun w => (GLnLocal.integralGL (w.adicCompletion E) n : Set _))
      (fun w => GLnLocal.isOpen_integralGL (w.adicCompletion E) n) (p := fun w => w.under (𝓞 F) ∉ S)
    exact h.preimage (AdelicGLn.finiteRestrictedEquiv E n).continuous

/- English proof (translation)
Distinguish the cases in `hx : x ∈ U (E := E) (n := n) S`. Rewrite using `[Set.indicator_of_mem hx, Pi.one_apply, mul_one]`. Use `finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hvS`. Use `hv ?_` and prove the remaining obligations.

Establish `hvS' : v ∉ S` using `hvS`. Express the relevant statement in the definitionally equal form `φ v (pv v x) = 1`. Rewrite using `[hφ v hvS', Set.indicator_of_mem, Pi.one_apply]`. Introduce `w`. Use `hx w.1 (by rw [under_eq]; exact hvS')` as an intermediate fact.

Rewrite `this` using `[← cmp_pv]`. Conclude with `this`. Rewrite using `[Set.indicator_of_notMem hx, mul_zero]`. Simplify using `only [U, Set.mem_setOf_eq, not_forall] at hx`. Take `⟨w, hwS, hw⟩` from `hx`.

Establish `hB : {w : Pl E | AdelicGLn.finiteRestrictedEquiv E n x w ∉ GLnLocal.integralGL (w.adicCompletion E) n}.Finite` using `Filter.eventually_cofinite.1 (AdelicGLn.finiteRestrictedEquiv E n x).2`. Use `finprod_eq_zero _ (w.under (𝓞 F)) ?_ ?_` and prove the remaining obligations. Rewrite using `[hφ _ hwS, Set.indicator_of_notMem]`. Introduce `h`. Use `hw ?_` and prove the remaining obligations.

Establish `h1 : cmp (⟨w, liesOver_under w⟩ : PlacesOver E (w.under (𝓞 F))) (pv _ x) ∈ GLnLocal.integralGL (w.adicCompletion E) n` using `h ⟨w, liesOver_under w⟩`. Rewrite `h1` using `[cmp_pv]`. Conclude with `h1`. Use `(S.finite_toSet.union (hB.image fun w : Pl E => w.under (𝓞 F))).subset fun v hv => ?_` and prove the remaining obligations. Distinguish the cases in `hvS : v ∈ S`.

Conclude with `Or.inl hvS`. Use `right`. Establish `hnot : pv v x ∉ unitSet E n v`. Introduce `h`. Use `hv ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `φ v (pv v x) = 1`. Rewrite using `[hφ v hvS, Set.indicator_of_mem h, Pi.one_apply]`. Simplify using `only [unitSet, Set.mem_setOf_eq, not_forall] at hnot`. Take `⟨w', hw'⟩` from `hnot`. Use `⟨w'.1, ?_, under_eq w'⟩` and prove the remaining obligations.

Introduce `h`. Use `hw' ?_` and prove the remaining obligations. Establish `: cmp w' (pv v x) ∈ GLnLocal.integralGL (w'.1.adicCompletion E) n`. Rewrite using `[cmp_pv]`. Conclude with `h`.

Conclude with `this`.
-/
private theorem e_formula (S : Finset (Pl F)) (φ : ∀ v : Pl F, GL (Fin n) (CompletionsOver E v) → ℂ)
    (hφ : ∀ v ∉ S, φ v = (unitSet E n v).indicator 1) (x : AdelicGLn.FiniteAdelicGL E n) :
    ∏ᶠ v, φ v (pv v x) = (∏ v ∈ S, φ v (pv v x)) * (U S).indicator 1 x := by
  classical
  by_cases hx : x ∈ U (E := E) (n := n) S
  · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    by_contra hvS
    refine hv ?_
    have hvS' : v ∉ S := hvS
    change φ v (pv v x) = 1
    rw [hφ v hvS', Set.indicator_of_mem, Pi.one_apply]
    intro w
    have := hx w.1 (by rw [under_eq]; exact hvS')
    rw [← cmp_pv] at this
    exact this
  · rw [Set.indicator_of_notMem hx, mul_zero]
    simp only [U, Set.mem_setOf_eq, not_forall] at hx
    obtain ⟨w, hwS, hw⟩ := hx
    have hB : {w : Pl E | AdelicGLn.finiteRestrictedEquiv E n x w ∉
        GLnLocal.integralGL (w.adicCompletion E) n}.Finite :=
      Filter.eventually_cofinite.1 (AdelicGLn.finiteRestrictedEquiv E n x).2
    refine finprod_eq_zero _ (w.under (𝓞 F)) ?_ ?_
    · rw [hφ _ hwS, Set.indicator_of_notMem]
      intro h
      refine hw ?_
      have h1 : cmp (⟨w, liesOver_under w⟩ : PlacesOver E (w.under (𝓞 F))) (pv _ x) ∈
          GLnLocal.integralGL (w.adicCompletion E) n := h ⟨w, liesOver_under w⟩
      rw [cmp_pv] at h1
      exact h1
    · refine (S.finite_toSet.union (hB.image fun w : Pl E => w.under (𝓞 F))).subset fun v hv => ?_
      by_cases hvS : v ∈ S
      · exact Or.inl hvS
      · right
        have hnot : pv v x ∉ unitSet E n v := by
          intro h
          refine hv ?_
          change φ v (pv v x) = 1
          rw [hφ v hvS, Set.indicator_of_mem h, Pi.one_apply]
        simp only [unitSet, Set.mem_setOf_eq, not_forall] at hnot
        obtain ⟨w', hw'⟩ := hnot
        refine ⟨w'.1, ?_, under_eq w'⟩
        intro h
        refine hw' ?_
        have : cmp w' (pv v x) ∈ GLnLocal.integralGL (w'.1.adicCompletion E) n := by
          rw [cmp_pv]
          exact h
        exact this

/- English proof (translation)
Set `D : ∀ w : Pl E, Set (GL (Fin n) (w.adicCompletion E))` to `fun w => if w.under (𝓞 F) ∈ S then cmp (⟨w, liesOver_under w⟩ : PlacesOver E (w.under (𝓞 F))) '' tsupport (φ (w.under (𝓞 F))) else (GLnLocal.integralGL (w.adicCompletion E) n : Set _)`. Establish `hD : ∀ w, IsCompact (D w)` using `fun w => by`. Distinguish the cases in `h : w.under (𝓞 F) ∈ S`. Simplify using `only [D, if_pos h]`. Conclude with `(hS _ h).isCompact.image (continuous_cmp _)`.

Simplify using `only [D, if_neg h]`. Conclude with `GLnLocal.isCompact_integralGL _ n`. Establish `hK` using `rp_compact (A := fun w : Pl E => (GLnLocal.integralGL (w.adicCompletion E) n : Set _)) D hD {w : Pl E | w.under (𝓞 F) ∈ S} (finite_under _ S.finite_toSet) (fun w hw => by`. Establish `h : w.under (𝓞 F) ∉ S` using `hw`. Simplify using `only [D, if_neg h]`.

Conclude with `subset_rfl)`. Use `⟨_, (AdelicGLn.finiteRestrictedEquiv E n).toHomeomorph.isCompact_preimage.2 hK, ?_⟩` and prove the remaining obligations. Introduce `x hx hne w`. Distinguish the cases in `h : w.under (𝓞 F) ∈ S`. Express the relevant statement in the definitionally equal form `_ ∈ D w`.

Simplify using `only [D, if_pos h]`. Conclude with `⟨pv _ x, subset_tsupport _ (hne _ h), cmp_pv _ x⟩`. Express the relevant statement in the definitionally equal form `_ ∈ D w`. Simplify using `only [D, if_neg h]`. Conclude with `hx w h`.
-/
private theorem e_compact (S : Finset (Pl F)) (φ : ∀ v : Pl F, GL (Fin n) (CompletionsOver E v) → ℂ)
    (hS : ∀ v ∈ S, HasCompactSupport (φ v)) :
    ∃ C : Set (AdelicGLn.FiniteAdelicGL E n), IsCompact C ∧
      ∀ x ∈ U S, (∀ v ∈ S, φ v (pv v x) ≠ 0) → x ∈ C := by
  classical
  let D : ∀ w : Pl E, Set (GL (Fin n) (w.adicCompletion E)) := fun w =>
    if w.under (𝓞 F) ∈ S then
      cmp (⟨w, liesOver_under w⟩ : PlacesOver E (w.under (𝓞 F))) '' tsupport (φ (w.under (𝓞 F)))
    else (GLnLocal.integralGL (w.adicCompletion E) n : Set _)
  have hD : ∀ w, IsCompact (D w) := fun w => by
    by_cases h : w.under (𝓞 F) ∈ S
    · simp only [D, if_pos h]
      exact (hS _ h).isCompact.image (continuous_cmp _)
    · simp only [D, if_neg h]
      exact GLnLocal.isCompact_integralGL _ n
  have hK := rp_compact (A := fun w : Pl E => (GLnLocal.integralGL (w.adicCompletion E) n : Set _)) D hD
    {w : Pl E | w.under (𝓞 F) ∈ S} (finite_under _ S.finite_toSet) (fun w hw => by
      have h : w.under (𝓞 F) ∉ S := hw
      simp only [D, if_neg h]
      exact subset_rfl)
  refine ⟨_, (AdelicGLn.finiteRestrictedEquiv E n).toHomeomorph.isCompact_preimage.2 hK, ?_⟩
  intro x hx hne w
  by_cases h : w.under (𝓞 F) ∈ S
  · change _ ∈ D w
    simp only [D, if_pos h]
    exact ⟨pv _ x, subset_tsupport _ (hne _ h), cmp_pv _ x⟩
  · change _ ∈ D w
    simp only [D, if_neg h]
    exact hx w h

/- English proof (translation)
Use `Units.ext (Matrix.ext fun a b => ?_)` and prove the remaining obligations. Use function extensionality and compare the values at `w`. Express the relevant statement in the definitionally equal form `((finEmb E n (CuspidalSpectrum.finPart E n g) : AdelicGLn.AdelicGL E n) a b).2 w.1 = (g a b).2 w.1`. Rewrite using `[finEmb_entry]`. Both sides reduce to the same expression.
-/
private theorem pv_finPart (v : Pl F) (g : AdelicGLn.AdelicGL E n) :
    pv v (CuspidalSpectrum.finPart E n g) = mapGL n (atFin v) g := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  funext w
  change ((finEmb E n (CuspidalSpectrum.finPart E n g) : AdelicGLn.AdelicGL E n) a b).2 w.1 = (g a b).2 w.1
  rw [finEmb_entry]
  rfl

end Main

end UpperTheory.ConvolutionTheory.GM.CompactClopenAverage

open UpperTheory.ConvolutionTheory.GM.CompactClopenAverage in
/- English proof (translation)
Introduce `F E _ _ _ _ _ n hn S β φ hS hoff`. Set `e₀ : AdelicGLn.FiniteAdelicGL E n → ℂ` to `fun x => ∏ᶠ v, φ v (pv v x)`. Establish `hform : ∀ x, e₀ x = (∏ v ∈ S, φ v (pv v x)) * (U S).indicator 1 x` using `fun x => e_formula S φ hoff x`. Establish `hlc : IsLocallyConstant e₀`. Establish `h1 : IsLocallyConstant fun x : AdelicGLn.FiniteAdelicGL E n => ∏ v ∈ S, φ v (pv v x)` using `isLC_prod S (fun v x => φ v (pv v x)) fun v hv => (hS v hv).1.comp_continuous (continuous_pv v)`.

Establish `h2 : IsLocallyConstant ((U (E` using `E) (n := n) S).indicator (1 : AdelicGLn.FiniteAdelicGL E n → ℂ)) := by`. Rewrite using `[← LocallyConstant.coe_charFn ℂ (isClopen_U S)]`. Conclude with `LocallyConstant.isLocallyConstant _`. Establish `h3` using `h1.mul h2`. Establish `: e₀ = _` using `funext hform`.

Rewrite using `[this]`. Conclude with `h3`. Establish `hcs : HasCompactSupport e₀`. Take `⟨C, hC, hsub⟩` from `e_compact S φ fun v hv => (hS v hv).2`. Use `HasCompactSupport.of_support_subset_isCompact hC fun x hx => ?_` and prove the remaining obligations.

Establish `hx' : e₀ x ≠ 0` using `hx`. Rewrite `hx'` using `[hform]`. Establish `hU : x ∈ U (E` using `E) (n := n) S := by`. Assume the negation of the conclusion as `h`. Conclude with `hx' (by rw [Set.indicator_of_notMem h, mul_zero])`.

Use `hsub x hU fun v hv h0 => hx' ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_eq_zero hv h0, zero_mul]`. Set `e : TF E n` to `⟨⟨e₀, hlc.continuous⟩, hcs⟩`. Use `⟨e, hlc, fun x => rfl, fun x => ?_⟩` and prove the remaining obligations. Establish `hinf` using `(UpperTheory.ConvolutionTheory.Tf.avgTens E n hn β e _ fun _ => rfl).2`.

Establish `hΦ : ∀ g, tensE (onInf β) φ g = β (infPart E n g) * e (CuspidalSpectrum.finPart E n g)`. Introduce `g`. Express the relevant statement in the definitionally equal form `onInf β _ * _ = β _ * ∏ᶠ v, φ v (pv v _)`. Simplify using `only [pv_finPart]`. Use `congr 1`.

Conclude with `((UpperTheory.ConvolutionTheory.Tf.avgTens E n hn β e _ hΦ).1 x).symm`.
-/
theorem UpperTheory.ConvolutionTheory.GM.avgE :
    AvgE := by
  intro F E _ _ _ _ _ n hn S β φ hS hoff
  classical
  let e₀ : AdelicGLn.FiniteAdelicGL E n → ℂ := fun x => ∏ᶠ v, φ v (pv v x)
  have hform : ∀ x, e₀ x = (∏ v ∈ S, φ v (pv v x)) * (U S).indicator 1 x :=
    fun x => e_formula S φ hoff x
  have hlc : IsLocallyConstant e₀ := by
    have h1 : IsLocallyConstant fun x : AdelicGLn.FiniteAdelicGL E n => ∏ v ∈ S, φ v (pv v x) :=
      isLC_prod S (fun v x => φ v (pv v x)) fun v hv => (hS v hv).1.comp_continuous (continuous_pv v)
    have h2 : IsLocallyConstant ((U (E := E) (n := n) S).indicator (1 : AdelicGLn.FiniteAdelicGL E n → ℂ)) := by
      rw [← LocallyConstant.coe_charFn ℂ (isClopen_U S)]
      exact LocallyConstant.isLocallyConstant _
    have h3 := h1.mul h2
    have : e₀ = _ := funext hform
    rw [this]
    exact h3
  have hcs : HasCompactSupport e₀ := by
    obtain ⟨C, hC, hsub⟩ := e_compact S φ fun v hv => (hS v hv).2
    refine HasCompactSupport.of_support_subset_isCompact hC fun x hx => ?_
    have hx' : e₀ x ≠ 0 := hx
    rw [hform] at hx'
    have hU : x ∈ U (E := E) (n := n) S := by
      by_contra h
      exact hx' (by rw [Set.indicator_of_notMem h, mul_zero])
    refine hsub x hU fun v hv h0 => hx' ?_
    rw [Finset.prod_eq_zero hv h0, zero_mul]
  let e : TF E n := ⟨⟨e₀, hlc.continuous⟩, hcs⟩
  refine ⟨e, hlc, fun x => rfl, fun x => ?_⟩
  have hinf := (UpperTheory.ConvolutionTheory.Tf.avgTens E n hn β e _ fun _ => rfl).2
  have hΦ : ∀ g, tensE (onInf β) φ g = β (infPart E n g) * e (CuspidalSpectrum.finPart E n g) := by
    intro g
    change onInf β _ * _ = β _ * ∏ᶠ v, φ v (pv v _)
    simp only [pv_finPart]
    congr 1
  exact ((UpperTheory.ConvolutionTheory.Tf.avgTens E n hn β e _ hΦ).1 x).symm
