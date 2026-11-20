import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.PerCont
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries
import GroundTheory.GlobalFields.IdeleGroups.Rational
import GroundTheory.AutomorphicForms.GL2Classical.EigenformTranslates

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical
open scoped ENNReal

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.Cp
open scoped NumberField.AdeleRing

open GroundTheory.Global.RationalIdeles GroundTheory.Automorphic.Reduction in
/- English proof (translation)
Rewrite using `[coe_realPart, posIdeleHom_apply, GroundTheory.Automorphic.GL2Classical.posIdele_fst_rat, RingEquiv.apply_symm_apply]`.
-/
private theorem pos_real (s : {r : ℝ // 0 < r}) : (realPart (posIdeleHom ℚ s) : ℝ) = s.1 := by
  rw [coe_realPart, posIdeleHom_apply, GroundTheory.Automorphic.GL2Classical.posIdele_fst_rat, RingEquiv.apply_symm_apply]

open GroundTheory.Global.RationalIdeles GroundTheory.Automorphic.Reduction in
/- English proof (translation)
Use `mem_positiveSubgroup.2 ⟨(IdeleGroup.mem_standardOpenSubgroup ℚ).2 fun v => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_inv, posIdeleHom_apply, posIdeleHom_apply, posIdele_finite, posIdele_finite]`. Conclude with `⟨one_mem _, one_mem _⟩`. Rewrite using `[pos_real]`. Conclude with `s.2`.
-/
private theorem pos_mem (s : {r : ℝ // 0 < r}) : posIdeleHom ℚ s ∈ positiveSubgroup := by
  refine mem_positiveSubgroup.2 ⟨(IdeleGroup.mem_standardOpenSubgroup ℚ).2 fun v => ?_, ?_⟩
  · rw [← map_inv, posIdeleHom_apply, posIdeleHom_apply, posIdele_finite, posIdele_finite]
    exact ⟨one_mem _, one_mem _⟩
  · rw [pos_real]; exact s.2

/- English proof (translation)
Rewrite using `[← map_mul]`. Establish `h : ((t⁻¹ : IdeleGroup ℚ) : 𝔸[ℚ]).2 v * (t : 𝔸[ℚ]).2 v = 1` using `congrArg (fun x : 𝔸[ℚ] => x.2 v) (Units.inv_mul t)`. Rewrite using `[h, map_one]`.
-/
private theorem val_inv (t : IdeleGroup ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v (((t⁻¹ : IdeleGroup ℚ) : 𝔸[ℚ]).2 v) * Valued.v ((t : 𝔸[ℚ]).2 v) = 1 := by
  rw [← map_mul]
  have h : ((t⁻¹ : IdeleGroup ℚ) : 𝔸[ℚ]).2 v * (t : 𝔸[ℚ]).2 v = 1 :=
    congrArg (fun x : 𝔸[ℚ] => x.2 v) (Units.inv_mul t)
  rw [h, map_one]

open GroundTheory.Global.RationalIdeles in
/- English proof (translation)
Establish `h1 : (realPart t : ℝ) = 1`. Rewrite using `[coe_realPart, show (t : 𝔸[ℚ]).1 = 1 from ht.1, map_one]`. Use `⟨mem_positiveSubgroup.2 ⟨(IdeleGroup.mem_standardOpenSubgroup ℚ).2 fun v => ?_, by rw [h1]; exact one_pos⟩, h1⟩` and prove the remaining obligations. Establish `hv : Valued.v ((t : 𝔸[ℚ]).2 v) = 1` using `ht.2 v`. Establish `hi` using `val_inv t v`.

Rewrite `hi` using `[hv, mul_one]`. Conclude with `⟨(HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 hv.le, (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 hi.le⟩`.
-/
private theorem uu_mem {t : IdeleGroup ℚ} (ht : t ∈ UU) : t ∈ positiveSubgroup ∧ (realPart t : ℝ) = 1 := by
  have h1 : (realPart t : ℝ) = 1 := by
    rw [coe_realPart, show (t : 𝔸[ℚ]).1 = 1 from ht.1, map_one]
  refine ⟨mem_positiveSubgroup.2 ⟨(IdeleGroup.mem_standardOpenSubgroup ℚ).2 fun v => ?_, by rw [h1]; exact one_pos⟩, h1⟩
  have hv : Valued.v ((t : 𝔸[ℚ]).2 v) = 1 := ht.2 v
  have hi := val_inv t v
  rw [hv, mul_one] at hi
  exact ⟨(HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 hv.le,
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 hi.le⟩

open GroundTheory.Global.RationalIdeles in
/- English proof (translation)
Use `⟨realEquiv.injective ?_, fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[map_one, ← coe_realPart, h1]`. Take `⟨ha, hb⟩` from `(IdeleGroup.mem_standardOpenSubgroup ℚ).1 (mem_positiveSubgroup.1 hp).1 v`. Establish `ha'` using `(HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 ha`. Establish `hb'` using `(HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 hb`.

Establish `hi` using `val_inv t v`. Use `le_antisymm ha' ?_` and prove the remaining obligations. Use `mul_le_mul' hb' (le_refl (Valued.v ((t : 𝔸[ℚ]).2 v)))` as an intermediate fact. Rewrite `this` using `[hi, one_mul]`. Then use the resulting hypothesis.
-/
private theorem mem_uu {t : IdeleGroup ℚ} (hp : t ∈ positiveSubgroup) (h1 : (realPart t : ℝ) = 1) : t ∈ UU := by
  refine ⟨realEquiv.injective ?_, fun v => ?_⟩
  · rw [map_one, ← coe_realPart, h1]
  · obtain ⟨ha, hb⟩ := (IdeleGroup.mem_standardOpenSubgroup ℚ).1 (mem_positiveSubgroup.1 hp).1 v
    have ha' := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 ha
    have hb' := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 hb
    have hi := val_inv t v
    refine le_antisymm ha' ?_
    have := mul_le_mul' hb' (le_refl (Valued.v ((t : 𝔸[ℚ]).2 v)))
    rwa [hi, one_mul] at this

open GroundTheory.Global.RationalIdeles GroundTheory.Automorphic.Reduction in
/- English proof (translation)
Set `e` to `MulEquiv.ofBijective mulMap mulMap_bijective`. Set `qd : IdeleGroup ℚ → ℚˣ` to `fun d => (e.symm d).1`. Set `pd : IdeleGroup ℚ → positiveSubgroup` to `fun d => (e.symm d).2`. Establish `hd : ∀ d, d = IdeleGroup.diagonal ℚ (qd d) * (pd d : IdeleGroup ℚ)` using `fun d => (e.apply_symm_apply d).symm`. Establish `hu : ∀ (a : ℚˣ) (p : positiveSubgroup), qd (IdeleGroup.diagonal ℚ a * (p : IdeleGroup ℚ)) = a ∧ pd (IdeleGroup.diagonal ℚ a * (p : IdeleGroup ℚ)) = p`.

Introduce `a p`. Establish `: e.symm (IdeleGroup.diagonal ℚ a * (p : IdeleGroup ℚ)) = (a, p)` using `e.symm_apply_apply (a, p)`. Conclude with `⟨congrArg Prod.fst this, congrArg Prod.snd this⟩`. Establish `hpe : ∀ d, (pd d : IdeleGroup ℚ) = (IdeleGroup.diagonal ℚ (qd d))⁻¹ * d` using `fun d => eq_inv_mul_of_mul_eq (hd d).symm`. Establish `hQ : IsLocallyConstant qd`.

Use `(IsLocallyConstant.iff_exists_open qd).2 fun d => ?_` and prove the remaining obligations. Use `⟨(fun x => (IdeleGroup.diagonal ℚ (qd d))⁻¹ * x) ⁻¹' (positiveSubgroup : Set (IdeleGroup ℚ)), isOpen_positiveSubgroup.preimage (continuous_const.mul continuous_id), ?_, fun x hx => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(IdeleGroup.diagonal ℚ (qd d))⁻¹ * d ∈ positiveSubgroup`. Conclude with `hpe d ▸ (pd d).2`. Establish `hx' : (IdeleGroup.diagonal ℚ (qd d))⁻¹ * x ∈ positiveSubgroup` using `hx`.

Use `(hu (qd d) ⟨_, hx'⟩).1` as an intermediate fact. Simplify using `using this`. Establish `hP : Continuous fun d => (pd d : IdeleGroup ℚ)`. Establish `h1 : Continuous fun d => (IdeleGroup.diagonal ℚ (qd d))⁻¹` using `(hQ.comp fun a => (IdeleGroup.diagonal ℚ a)⁻¹).continuous`. Conclude with `(h1.mul continuous_id).congr fun d => (hpe d).symm`.

Establish `hpos : ∀ d, 0 < (realPart (pd d : IdeleGroup ℚ) : ℝ)` using `fun d => (mem_positiveSubgroup.1 (pd d).2).2`. Set `S : IdeleGroup ℚ → {r : ℝ // 0 < r}` to `fun d => ⟨realPart (pd d : IdeleGroup ℚ), hpos d⟩`. Establish `hS : Continuous S` using `(Units.continuous_val.comp (continuous_realPart.comp hP)).subtype_mk _`. Use `⟨qd, S, fun d => (posIdeleHom ℚ (S d))⁻¹ * (pd d : IdeleGroup ℚ), hQ, hS, (continuous_posIdeleHom.comp hS).inv.mul hP, fun d => ?_, fun d => ?_, fun a s t ht => ?_⟩` and prove the remaining obligations. Use `mem_uu (positiveSubgroup.mul_mem (positiveSubgroup.inv_mem (pos_mem _)) (pd d).2) ?_` and prove the remaining obligations.

Rewrite using `[map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, pos_real]`. Conclude with `inv_mul_cancel₀ (hpos d).ne'`. Use `conv_lhs => rw [hd d] group`. Establish `hp : posIdeleHom ℚ s * t ∈ positiveSubgroup` using `positiveSubgroup.mul_mem (pos_mem s) (uu_mem ht).1`. Establish `h` using `hu a ⟨_, hp⟩`.

Establish `e1 : IdeleGroup.diagonal ℚ a * posIdeleHom ℚ s * t = IdeleGroup.diagonal ℚ a * ((⟨_, hp⟩ : positiveSubgroup) : IdeleGroup ℚ)` using `mul_assoc _ _ _`. Establish `hs : S (IdeleGroup.diagonal ℚ a * posIdeleHom ℚ s * t) = s`. Use `Subtype.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(realPart (pd _ : IdeleGroup ℚ) : ℝ) = _`. Rewrite using `[e1, h.2]`.

Express the relevant statement in the definitionally equal form `(realPart (posIdeleHom ℚ s * t) : ℝ) = _`. Rewrite using `[map_mul, Units.val_mul, pos_real, (uu_mem ht).2, mul_one]`. Use `⟨by rw [e1]; exact h.1, hs, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(posIdeleHom ℚ (S _))⁻¹ * (pd _ : IdeleGroup ℚ) = t`. Rewrite using `[hs, e1, h.2]`.

Simplify using the standard rewrite rules.
-/
private theorem dec : ∃ (Q : IdeleGroup ℚ → ℚˣ) (S : IdeleGroup ℚ → {r : ℝ // 0 < r}) (T : IdeleGroup ℚ → IdeleGroup ℚ),
    IsLocallyConstant Q ∧ Continuous S ∧ Continuous T ∧ (∀ d, T d ∈ UU) ∧
    (∀ d, d = IdeleGroup.diagonal ℚ (Q d) * posIdeleHom ℚ (S d) * T d) ∧
    ∀ a s t, t ∈ UU → Q (IdeleGroup.diagonal ℚ a * posIdeleHom ℚ s * t) = a ∧
      S (IdeleGroup.diagonal ℚ a * posIdeleHom ℚ s * t) = s ∧ T (IdeleGroup.diagonal ℚ a * posIdeleHom ℚ s * t) = t := by
  let e := MulEquiv.ofBijective mulMap mulMap_bijective
  let qd : IdeleGroup ℚ → ℚˣ := fun d => (e.symm d).1
  let pd : IdeleGroup ℚ → positiveSubgroup := fun d => (e.symm d).2
  have hd : ∀ d, d = IdeleGroup.diagonal ℚ (qd d) * (pd d : IdeleGroup ℚ) := fun d =>
    (e.apply_symm_apply d).symm
  have hu : ∀ (a : ℚˣ) (p : positiveSubgroup), qd (IdeleGroup.diagonal ℚ a * (p : IdeleGroup ℚ)) = a ∧
      pd (IdeleGroup.diagonal ℚ a * (p : IdeleGroup ℚ)) = p := by
    intro a p
    have : e.symm (IdeleGroup.diagonal ℚ a * (p : IdeleGroup ℚ)) = (a, p) := e.symm_apply_apply (a, p)
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  have hpe : ∀ d, (pd d : IdeleGroup ℚ) = (IdeleGroup.diagonal ℚ (qd d))⁻¹ * d := fun d =>
    eq_inv_mul_of_mul_eq (hd d).symm
  have hQ : IsLocallyConstant qd := by
    refine (IsLocallyConstant.iff_exists_open qd).2 fun d => ?_
    refine ⟨(fun x => (IdeleGroup.diagonal ℚ (qd d))⁻¹ * x) ⁻¹' (positiveSubgroup : Set (IdeleGroup ℚ)),
      isOpen_positiveSubgroup.preimage (continuous_const.mul continuous_id), ?_, fun x hx => ?_⟩
    · change (IdeleGroup.diagonal ℚ (qd d))⁻¹ * d ∈ positiveSubgroup
      exact hpe d ▸ (pd d).2
    · have hx' : (IdeleGroup.diagonal ℚ (qd d))⁻¹ * x ∈ positiveSubgroup := hx
      have := (hu (qd d) ⟨_, hx'⟩).1
      simpa using this
  have hP : Continuous fun d => (pd d : IdeleGroup ℚ) := by
    have h1 : Continuous fun d => (IdeleGroup.diagonal ℚ (qd d))⁻¹ :=
      (hQ.comp fun a => (IdeleGroup.diagonal ℚ a)⁻¹).continuous
    exact (h1.mul continuous_id).congr fun d => (hpe d).symm
  have hpos : ∀ d, 0 < (realPart (pd d : IdeleGroup ℚ) : ℝ) := fun d => (mem_positiveSubgroup.1 (pd d).2).2
  let S : IdeleGroup ℚ → {r : ℝ // 0 < r} := fun d => ⟨realPart (pd d : IdeleGroup ℚ), hpos d⟩
  have hS : Continuous S :=
    (Units.continuous_val.comp (continuous_realPart.comp hP)).subtype_mk _
  refine ⟨qd, S, fun d => (posIdeleHom ℚ (S d))⁻¹ * (pd d : IdeleGroup ℚ), hQ, hS,
    (continuous_posIdeleHom.comp hS).inv.mul hP, fun d => ?_, fun d => ?_, fun a s t ht => ?_⟩
  · refine mem_uu (positiveSubgroup.mul_mem (positiveSubgroup.inv_mem (pos_mem _)) (pd d).2) ?_
    rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, pos_real]
    exact inv_mul_cancel₀ (hpos d).ne'
  · conv_lhs => rw [hd d]
    group
  · have hp : posIdeleHom ℚ s * t ∈ positiveSubgroup := positiveSubgroup.mul_mem (pos_mem s) (uu_mem ht).1
    have h := hu a ⟨_, hp⟩
    have e1 : IdeleGroup.diagonal ℚ a * posIdeleHom ℚ s * t = IdeleGroup.diagonal ℚ a * ((⟨_, hp⟩ : positiveSubgroup) : IdeleGroup ℚ) := mul_assoc _ _ _
    have hs : S (IdeleGroup.diagonal ℚ a * posIdeleHom ℚ s * t) = s := by
      refine Subtype.ext ?_
      change (realPart (pd _ : IdeleGroup ℚ) : ℝ) = _
      rw [e1, h.2]
      change (realPart (posIdeleHom ℚ s * t) : ℝ) = _
      rw [map_mul, Units.val_mul, pos_real, (uu_mem ht).2, mul_one]
    refine ⟨by rw [e1]; exact h.1, hs, ?_⟩
    change (posIdeleHom ℚ (S _))⁻¹ * (pd _ : IdeleGroup ℚ) = t
    rw [hs, e1, h.2]
    simp

/- English proof (translation)
Establish `ha : ∀ x : 𝔸[ℚ], IdeleGroup.diagonal ℚ q • x = algebraMap ℚ 𝔸[ℚ] q * x` using `fun x => by`. Rewrite using `[Units.smul_def, smul_eq_mul, IdeleGroup.coe_diagonal]`. Establish `mp : MeasurePreserving (fun x : 𝔸[ℚ] => IdeleGroup.diagonal ℚ q • x) (adeleMeasure ℚ) (adeleMeasure ℚ)`. Use `⟨(continuous_const_smul _).measurable, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul_adeleMeasure, IdeleGroup.ideleModule_diagonal]`.

Simplify using the standard rewrite rules. Establish `hq : algebraMap ℚ 𝔸[ℚ] (q : ℚ) * algebraMap ℚ 𝔸[ℚ] ((q⁻¹ : ℚˣ) : ℚ) = 1`. Rewrite using `[← map_mul, Units.mul_inv, map_one]`. Establish `hT : IsAddFundamentalDomain (↥(AdeleRing.principalSubgroup (𝓞 ℚ) ℚ)) ((fun x : 𝔸[ℚ] => IdeleGroup.diagonal ℚ q • x) ⁻¹' fundamentalSet ℚ) (adeleMeasure ℚ)`. Use `IsAddFundamentalDomain.mk' (mp.measurable (measurableSet_fundamentalSet ℚ)).nullMeasurableSet fun x => ?_` and prove the remaining obligations.

Take `⟨k, hk, hu⟩` from `existsUnique_sub_mem_fundamentalSet ℚ (IdeleGroup.diagonal ℚ q • x)`. Use `⟨⟨algebraMap ℚ 𝔸[ℚ] (-(((q⁻¹ : ℚˣ) : ℚ) * k)), ⟨_, rfl⟩⟩, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `IdeleGroup.diagonal ℚ q • (algebraMap ℚ 𝔸[ℚ] (-(((q⁻¹ : ℚˣ) : ℚ) * k)) + x) ∈ fundamentalSet ℚ`. Use `hk using 1` and compare the differences between its conclusion and the goal. Rewrite using `[ha, ha, mul_add, map_neg, map_mul, mul_neg, ← mul_assoc, hq, one_mul]`.

Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `⟨_, c, rfl⟩ hc`. Express the relevant statement in the definitionally equal form `IdeleGroup.diagonal ℚ q • (algebraMap ℚ 𝔸[ℚ] c + x) ∈ fundamentalSet ℚ at hc`. Establish `h` using `hu (-((q : ℚ) * c)) (by`. Use `hc using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[ha, ha, mul_add, map_neg, map_mul]`. Use the proof step `ring)`. Use `Subtype.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `algebraMap ℚ 𝔸[ℚ] c = algebraMap ℚ 𝔸[ℚ] (-(((q⁻¹ : ℚˣ) : ℚ) * k))`. Rewrite using `[← h]`.

Use `congr 1`. Simplify using the standard rewrite rules. Establish `h1` using `(isAddFundamentalDomain_fundamentalSet ℚ).setIntegral_eq hT (f := fun b => g (IdeleGroup.diagonal ℚ q • b)) (fun γ x => by`. Take `⟨γ, c, rfl⟩` from `γ`. Express the relevant statement in the definitionally equal form `g (IdeleGroup.diagonal ℚ q • (algebraMap ℚ 𝔸[ℚ] c + x)) = _`.

Rewrite using `[ha, ha, mul_add, ← map_mul, hg])`. Rewrite using `[h1]`. Conclude with `mp.setIntegral_preimage_emb (Homeomorph.smul (IdeleGroup.diagonal ℚ q)).measurableEmbedding g _`.
-/
private theorem scale_int (q : ℚˣ) (g : 𝔸[ℚ] → ℂ) (hg : ∀ (c : ℚ) b, g (algebraMap ℚ 𝔸[ℚ] c + b) = g b) :
    ∫ b in fundamentalSet ℚ, g (IdeleGroup.diagonal ℚ q • b) ∂adeleMeasure ℚ =
      ∫ b in fundamentalSet ℚ, g b ∂adeleMeasure ℚ := by
  have ha : ∀ x : 𝔸[ℚ], IdeleGroup.diagonal ℚ q • x = algebraMap ℚ 𝔸[ℚ] q * x := fun x => by
    rw [Units.smul_def, smul_eq_mul, IdeleGroup.coe_diagonal]
  have mp : MeasurePreserving (fun x : 𝔸[ℚ] => IdeleGroup.diagonal ℚ q • x) (adeleMeasure ℚ) (adeleMeasure ℚ) := by
    refine ⟨(continuous_const_smul _).measurable, ?_⟩
    rw [map_smul_adeleMeasure, IdeleGroup.ideleModule_diagonal]
    simp
  have hq : algebraMap ℚ 𝔸[ℚ] (q : ℚ) * algebraMap ℚ 𝔸[ℚ] ((q⁻¹ : ℚˣ) : ℚ) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hT : IsAddFundamentalDomain (↥(AdeleRing.principalSubgroup (𝓞 ℚ) ℚ))
      ((fun x : 𝔸[ℚ] => IdeleGroup.diagonal ℚ q • x) ⁻¹' fundamentalSet ℚ) (adeleMeasure ℚ) := by
    refine IsAddFundamentalDomain.mk' (mp.measurable (measurableSet_fundamentalSet ℚ)).nullMeasurableSet fun x => ?_
    obtain ⟨k, hk, hu⟩ := existsUnique_sub_mem_fundamentalSet ℚ (IdeleGroup.diagonal ℚ q • x)
    refine ⟨⟨algebraMap ℚ 𝔸[ℚ] (-(((q⁻¹ : ℚˣ) : ℚ) * k)), ⟨_, rfl⟩⟩, ?_, ?_⟩
    · change IdeleGroup.diagonal ℚ q • (algebraMap ℚ 𝔸[ℚ] (-(((q⁻¹ : ℚˣ) : ℚ) * k)) + x) ∈ fundamentalSet ℚ
      convert hk using 1
      rw [ha, ha, mul_add, map_neg, map_mul, mul_neg, ← mul_assoc, hq, one_mul]
      ring
    · rintro ⟨_, c, rfl⟩ hc
      change IdeleGroup.diagonal ℚ q • (algebraMap ℚ 𝔸[ℚ] c + x) ∈ fundamentalSet ℚ at hc
      have h := hu (-((q : ℚ) * c)) (by
        convert hc using 1
        rw [ha, ha, mul_add, map_neg, map_mul]
        ring)
      refine Subtype.ext ?_
      change algebraMap ℚ 𝔸[ℚ] c = algebraMap ℚ 𝔸[ℚ] (-(((q⁻¹ : ℚˣ) : ℚ) * k))
      rw [← h]
      congr 1
      simp
  have h1 := (isAddFundamentalDomain_fundamentalSet ℚ).setIntegral_eq hT
    (f := fun b => g (IdeleGroup.diagonal ℚ q • b)) (fun γ x => by
      obtain ⟨γ, c, rfl⟩ := γ
      change g (IdeleGroup.diagonal ℚ q • (algebraMap ℚ 𝔸[ℚ] c + x)) = _
      rw [ha, ha, mul_add, ← map_mul, hg])
  rw [h1]
  exact mp.setIntegral_preimage_emb (Homeomorph.smul (IdeleGroup.diagonal ℚ q)).measurableEmbedding g _

local notation "Dt" => Matrix.GeneralLinearGroup.det

private def dq (q : ℚˣ) : GL (Fin 2) ℚ :=
  ⟨!![(q : ℚ), 0; 0, 1], !![((q⁻¹ : ℚˣ) : ℚ), 0; 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp, by ext i j; fin_cases i <;> fin_cases j <;> simp⟩

/- English proof (translation)
The claim follows from `Units.ext (by simp [dq, Matrix.det_fin_two])`.
-/
private theorem det_dq (q : ℚˣ) : Dt (dq q) = q := Units.ext (by simp [dq, Matrix.det_fin_two])

/- English proof (translation)
The claim follows from `Units.ext (by ext i j; fin_cases i <;> fin_cases j <;> simp [dq])`.
-/
private theorem dq_one : dq 1 = 1 := Units.ext (by ext i j; fin_cases i <;> fin_cases j <;> simp [dq])

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[IdeleGroup.coe_diagonal]`. Conclude with `(RingHom.map_det (algebraMap ℚ (A ℚ)) γ.val).symm`.
-/
private theorem det_rat (γ : GL (Fin 2) ℚ) : Dt (ratGL ℚ 2 γ) = IdeleGroup.diagonal ℚ (Dt γ) := by
  refine Units.ext ?_
  rw [IdeleGroup.coe_diagonal]
  exact (RingHom.map_det (algebraMap ℚ (A ℚ)) γ.val).symm

/- English proof (translation)
The claim follows from `Units.ext (by simp [dM, Matrix.det_fin_two])`.
-/
private theorem det_dM (t : (A ℚ)ˣ) : Dt (dM t) = t := Units.ext (by simp [dM, Matrix.det_fin_two])

/- English proof (translation)
The claim follows from `Units.ext g.det_coe`.
-/
private theorem det_gl (g : G1 ℚ) : Dt (gl g) = 1 := Units.ext g.det_coe

open GroundTheory.Automorphic.Reduction in
/- English proof (translation)
Use `set t := rpowHom ((2 * Module.finrank ℚ ℚ : ℝ))⁻¹ s with ht`. Establish `hc : centralSection ℚ 2 s = diagUnits 2 (fun _ => posIdeleHom ℚ t)` using `rfl`. Establish `hts : t * t = s`. Use `Subtype.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `t.1 * t.1 = s.1`.

Establish `: t.1 = s.1 ^ ((2 * Module.finrank ℚ ℚ : ℝ))⁻¹` using `rfl`. Rewrite using `[this, ← Real.rpow_add s.2, Module.finrank_self]`. Evaluate the numerical expressions. Rewrite using `[hc, ← hts, map_mul]`. Use `(det_diagUnits (K := ℚ) (n := 2) (fun _ => posIdeleHom ℚ t)).trans ?_` and prove the remaining obligations.

Simplify using `[Fin.prod_univ_two, pow_two]`.
-/
private theorem det_centralSection (s : {r : ℝ // 0 < r}) : Dt (centralSection ℚ 2 s) = posIdeleHom ℚ s := by
  set t := rpowHom ((2 * Module.finrank ℚ ℚ : ℝ))⁻¹ s with ht
  have hc : centralSection ℚ 2 s = diagUnits 2 (fun _ => posIdeleHom ℚ t) := rfl
  have hts : t * t = s := by
    refine Subtype.ext ?_
    change t.1 * t.1 = s.1
    have : t.1 = s.1 ^ ((2 * Module.finrank ℚ ℚ : ℝ))⁻¹ := rfl
    rw [this, ← Real.rpow_add s.2, Module.finrank_self]
    norm_num
  rw [hc, ← hts, map_mul]
  refine (det_diagUnits (K := ℚ) (n := 2) (fun _ => posIdeleHom ℚ t)).trans ?_
  simp [Fin.prod_univ_two, pow_two]

private def toS (y : GL (Fin 2) (A ℚ)) (h : Dt y = 1) : G1 ℚ := ⟨y.val, congrArg Units.val h⟩

/- English proof (translation)
The claim follows from `Units.ext rfl`.
-/
private theorem gl_toS (y : GL (Fin 2) (A ℚ)) (h : Dt y = 1) : gl (toS y h) = y := Units.ext rfl

/- English proof (translation)
The claim follows from `Subtype.ext (congrArg Units.val e)`.
-/
private theorem toS_eq {y y' : GL (Fin 2) (A ℚ)} {h : Dt y = 1} {h' : Dt y' = 1} (g : G1 ℚ) (e : y = gl g * y') :
    toS y h = g * toS y' h' := Subtype.ext (congrArg Units.val e)

open GroundTheory.Automorphic.Reduction in

private def Mx (Q : IdeleGroup ℚ → ℚˣ) (S : IdeleGroup ℚ → {r : ℝ // 0 < r}) (T : IdeleGroup ℚ → IdeleGroup ℚ)
    (x : GL (Fin 2) (A ℚ)) : GL (Fin 2) (A ℚ) :=
  ratGL ℚ 2 (dq (Q (Dt x)))⁻¹ * (centralSection ℚ 2 (S (Dt x)))⁻¹ * x * (dM (T (Dt x)))⁻¹

/- English proof (translation)
Establish `h : (ratGL ℚ 2 (dq a)⁻¹).val = (!![((a⁻¹ : ℚˣ) : ℚ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ (A ℚ))` using `rfl`. Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[Units.val_mul, Units.val_mul, h]`. Establish `h2 : ∀ c : A ℚ, (gl (nU c)).val = !![1, c; 0, 1]` using `fun _ => rfl`. Rewrite using `[h2, h2, Units.smul_def, smul_eq_mul, IdeleGroup.coe_diagonal]`.

Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]`.
-/
private theorem nU_conj (a : ℚˣ) (b : A ℚ) :
    ratGL ℚ 2 (dq a)⁻¹ * gl (nU b) = gl (nU (IdeleGroup.diagonal ℚ a⁻¹ • b)) * ratGL ℚ 2 (dq a)⁻¹ := by
  have h : (ratGL ℚ 2 (dq a)⁻¹).val = (!![((a⁻¹ : ℚˣ) : ℚ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ (A ℚ)) := rfl
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, h]
  have h2 : ∀ c : A ℚ, (gl (nU c)).val = !![1, c; 0, 1] := fun _ => rfl
  rw [h2, h2, Units.smul_def, smul_eq_mul, IdeleGroup.coe_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/- English proof (translation)
Use `⟨⟨!![1, c; 0, 1], by simp [Matrix.det_fin_two]⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `!![1, algebraMap ℚ (A ℚ) c; 0, 1] = (!![1, c; 0, 1] : Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ (A ℚ))`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp`.
-/
private theorem nU_rat (c : ℚ) : ∃ γ, nU (algebraMap ℚ (A ℚ) c) = ratS ℚ γ := by
  refine ⟨⟨!![1, c; 0, 1], by simp [Matrix.det_fin_two]⟩, Subtype.ext ?_⟩
  change !![1, algebraMap ℚ (A ℚ) c; 0, 1] = (!![1, c; 0, 1] : Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ (A ℚ))
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/- English proof (translation)
Use `Subtype.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `!![1, b + c; 0, 1] = !![1, b; 0, 1] * !![1, c; 0, 1]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]`.
-/
private theorem nU_plus (b c : A ℚ) : nU (b + c) = nU b * nU c := by
  refine Subtype.ext ?_
  change !![1, b + c; 0, 1] = !![1, b; 0, 1] * !![1, c; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨γ.val, congrArg Units.val h⟩, Units.ext rfl⟩`.
-/
private theorem rat_sl (γ : GL (Fin 2) ℚ) (h : Dt γ = 1) : ∃ g, ratGL ℚ 2 γ = gl (ratS ℚ g) :=
  ⟨⟨γ.val, congrArg Units.val h⟩, Units.ext rfl⟩

open GroundTheory.Automorphic.Reduction in
/- English proof (translation)
Introduce `u hu`. Take `⟨Q, S, T, hQ, hS, hT, hTU, hdec, huniq⟩` from `dec`. Establish `hM1 : ∀ x, Dt (Mx Q S T x) = 1`. Introduce `x`. Establish `hg : ∀ a p d t : IdeleGroup ℚ, d = a * p * t → a⁻¹ * p⁻¹ * d * t⁻¹ = 1`.

Introduce `a p d t h`. Rewrite using `[h, show a⁻¹ * p⁻¹ * (a * p * t) * t⁻¹ = (a⁻¹ * a) * (p⁻¹ * p) * (t * t⁻¹) by ac_rfl]`. Simplify using the standard rewrite rules. Use `hg _ _ _ _ (hdec (Dt x))` as an intermediate fact. Simplify `this` using `only [Mx, map_mul, map_inv, det_rat, det_dq, det_centralSection, det_dM]`.

Establish `hMe : ∀ x a s t, t ∈ UU → Dt x = IdeleGroup.diagonal ℚ a * posIdeleHom ℚ s * t → Mx Q S T x = ratGL ℚ 2 (dq a)⁻¹ * (centralSection ℚ 2 s)⁻¹ * x * (dM t)⁻¹`. Introduce `x a s t ht hx`. Take `⟨h1, h2, h3⟩` from `huniq a s t ht`. Rewrite using `[Mx, hx, h1, h2, h3]`. Establish `hex : ∀ x : GL (Fin 2) (A ℚ), ∃ a s t, t ∈ UU ∧ Dt x = IdeleGroup.diagonal ℚ a * posIdeleHom ℚ s * t` using `fun x => ⟨_, _, _, hTU _, hdec _⟩`.

Establish `hz : ∀ s (g : GL (Fin 2) (A ℚ)), (centralSection ℚ 2 s)⁻¹ * g = g * (centralSection ℚ 2 s)⁻¹` using `fun s g => ((show Commute (centralSection ℚ 2 s) g from centralSection_mul_comm s g).inv_left).eq`. Set `sl : GL (Fin 2) (A ℚ) → G1 ℚ` to `fun x => toS (Mx Q S T x) (hM1 x)`. Establish `hdc : Continuous fun x : GL (Fin 2) (A ℚ) => Dt x` using `Matrix.GeneralLinearGroup.continuous_det`. Establish `hMc : Continuous (Mx Q S T)`. Establish `h1 : Continuous fun x : GL (Fin 2) (A ℚ) => ratGL ℚ 2 (dq (Q (Dt x)))⁻¹` using `((hQ.comp fun a => ratGL ℚ 2 (dq a)⁻¹).comp_continuous hdc).continuous`.

Establish `h2 : Continuous fun x : GL (Fin 2) (A ℚ) => (centralSection ℚ 2 (S (Dt x)))⁻¹` using `(continuous_centralSection.comp (hS.comp hdc)).inv`. Establish `h3 : Continuous fun x : GL (Fin 2) (A ℚ) => (dM (T (Dt x)))⁻¹` using `(continuous_dM.comp (hT.comp hdc)).inv`. Conclude with `((h1.mul h2).mul continuous_id).mul h3`. Establish `hsl : Continuous sl` using `(Units.continuous_val.comp hMc).subtype_mk _`. Use `⟨fun x => u (sl x), ⟨hu.cont.comp hsl, ?_, ?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations.

Introduce `γ x`. Take `⟨a, s, t, ht, hx⟩` from `hex x`. Establish `e1` using `hMe x a s t ht hx`. Establish `e2` using `hMe (ratGL ℚ 2 γ * x) (Dt γ * a) s t ht (by`. Rewrite using `[map_mul, det_rat, hx, map_mul]`.

Simplify using `only [mul_assoc])`. Take `⟨g, hg⟩` from `rat_sl ((dq (Dt γ * a))⁻¹ * γ * dq a) (by`. Simplify using `only [map_mul, map_inv, det_dq]`. Simplify using `[mul_comm, mul_assoc, mul_left_comm])`. Establish `h : sl (ratGL ℚ 2 γ * x) = ratS ℚ g * sl x` using `toS_eq _ (by`.

Rewrite using `[e1, e2, ← hg]`. Simplify using `only [map_mul, map_inv, mul_assoc, mul_inv_cancel_left]`. Rewrite using `[← mul_assoc (centralSection ℚ 2 s)⁻¹, hz]`. Simplify using `only [mul_assoc])`. Express the relevant statement in the definitionally equal form `u (sl _) = u (sl x)`.

Rewrite using `[h]`. Conclude with `hu.left g _`. Take `⟨B, hB⟩` from `hu.bdd`. Conclude with `⟨B, fun x => hB _⟩`. Introduce `s₀ x`.

Take `⟨a, s, t, ht, hx⟩` from `hex x`. Establish `e1` using `hMe x a s t ht hx`. Establish `e2` using `hMe (centralSection ℚ 2 s₀ * x) a (s₀ * s) t ht (by`. Rewrite using `[map_mul, det_centralSection, hx, map_mul]`. Simplify using `only [mul_assoc, mul_left_comm])`.

Establish `h : sl (centralSection ℚ 2 s₀ * x) = 1 * sl x` using `toS_eq _ (by`. Rewrite using `[e1, e2]`. Simplify using `only [map_mul, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left, map_one, one_mul])`. Express the relevant statement in the definitionally equal form `u (sl _) = u (sl x)`. Rewrite using `[h, one_mul]`.

Introduce `g t ht`. Establish `e` using `hMe (gl g * dM t) 1 1 t ht (by`. Rewrite using `[map_mul, det_gl, det_dM]`. Use the proof step `simp)`. Establish `e' : Mx Q S T (gl g * dM t) = gl g` using `e.trans (by simp [dq_one])`.

Establish `h : sl (gl g * dM t) = g` using `Subtype.ext (congrArg Units.val e')`. Express the relevant statement in the definitionally equal form `u (sl _) = u g`. Rewrite using `[h]`. Introduce `x`. Take `⟨a, s, t, ht, hx⟩` from `hex x`.

Establish `e1` using `hMe x a s t ht hx`. Establish `key : ∀ b, sl (gl (nU b) * x) = nU (IdeleGroup.diagonal ℚ a⁻¹ • b) * sl x` using `fun b => toS_eq _ (by`. Rewrite using `[hMe (gl (nU b) * x) a s t ht (by rw [map_mul, det_gl, one_mul, hx]), e1]`. Simplify using `only [mul_assoc]`. Rewrite using `[← mul_assoc (centralSection ℚ 2 s)⁻¹, hz, mul_assoc, ← mul_assoc (ratGL ℚ 2 (dq a)⁻¹), nU_conj]`.

Simplify using `only [mul_assoc])`. Express the relevant statement in the definitionally equal form `∫ b in fundamentalSet ℚ, u (sl (gl (nU b) * x)) ∂(adeleMeasure ℚ) = 0`. Repeatedly rewrite using `[key]`. Rewrite using `[scale_int a⁻¹ (fun b => u (nU b * sl x)) (fun c b => ?_)]`. Conclude with `hu.cusp _`.

Take `⟨γ, hγ⟩` from `nU_rat c`. Express the relevant statement in the definitionally equal form `u (nU (algebraMap ℚ (A ℚ) c + b) * sl x) = u (nU b * sl x)`. Rewrite using `[nU_plus, hγ, mul_assoc]`. Conclude with `hu.left γ _`.
-/
theorem ext : Ext := by
  intro u hu
  obtain ⟨Q, S, T, hQ, hS, hT, hTU, hdec, huniq⟩ := dec
  have hM1 : ∀ x, Dt (Mx Q S T x) = 1 := by
    intro x
    have hg : ∀ a p d t : IdeleGroup ℚ, d = a * p * t → a⁻¹ * p⁻¹ * d * t⁻¹ = 1 := by
      intro a p d t h
      rw [h, show a⁻¹ * p⁻¹ * (a * p * t) * t⁻¹ = (a⁻¹ * a) * (p⁻¹ * p) * (t * t⁻¹) by ac_rfl]
      simp
    have := hg _ _ _ _ (hdec (Dt x))
    simpa only [Mx, map_mul, map_inv, det_rat, det_dq, det_centralSection, det_dM] using this
  have hMe : ∀ x a s t, t ∈ UU → Dt x = IdeleGroup.diagonal ℚ a * posIdeleHom ℚ s * t →
      Mx Q S T x = ratGL ℚ 2 (dq a)⁻¹ * (centralSection ℚ 2 s)⁻¹ * x * (dM t)⁻¹ := by
    intro x a s t ht hx
    obtain ⟨h1, h2, h3⟩ := huniq a s t ht
    rw [Mx, hx, h1, h2, h3]
  have hex : ∀ x : GL (Fin 2) (A ℚ), ∃ a s t, t ∈ UU ∧ Dt x = IdeleGroup.diagonal ℚ a * posIdeleHom ℚ s * t :=
    fun x => ⟨_, _, _, hTU _, hdec _⟩
  have hz : ∀ s (g : GL (Fin 2) (A ℚ)), (centralSection ℚ 2 s)⁻¹ * g = g * (centralSection ℚ 2 s)⁻¹ := fun s g =>
    ((show Commute (centralSection ℚ 2 s) g from centralSection_mul_comm s g).inv_left).eq
  let sl : GL (Fin 2) (A ℚ) → G1 ℚ := fun x => toS (Mx Q S T x) (hM1 x)
  have hdc : Continuous fun x : GL (Fin 2) (A ℚ) => Dt x := Matrix.GeneralLinearGroup.continuous_det
  have hMc : Continuous (Mx Q S T) := by
    have h1 : Continuous fun x : GL (Fin 2) (A ℚ) => ratGL ℚ 2 (dq (Q (Dt x)))⁻¹ :=
      ((hQ.comp fun a => ratGL ℚ 2 (dq a)⁻¹).comp_continuous hdc).continuous
    have h2 : Continuous fun x : GL (Fin 2) (A ℚ) => (centralSection ℚ 2 (S (Dt x)))⁻¹ :=
      (continuous_centralSection.comp (hS.comp hdc)).inv
    have h3 : Continuous fun x : GL (Fin 2) (A ℚ) => (dM (T (Dt x)))⁻¹ :=
      (continuous_dM.comp (hT.comp hdc)).inv
    exact ((h1.mul h2).mul continuous_id).mul h3
  have hsl : Continuous sl := (Units.continuous_val.comp hMc).subtype_mk _
  refine ⟨fun x => u (sl x), ⟨hu.cont.comp hsl, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro γ x
    obtain ⟨a, s, t, ht, hx⟩ := hex x
    have e1 := hMe x a s t ht hx
    have e2 := hMe (ratGL ℚ 2 γ * x) (Dt γ * a) s t ht (by
      rw [map_mul, det_rat, hx, map_mul]
      simp only [mul_assoc])
    obtain ⟨g, hg⟩ := rat_sl ((dq (Dt γ * a))⁻¹ * γ * dq a) (by
      simp only [map_mul, map_inv, det_dq]
      simp [mul_comm, mul_assoc, mul_left_comm])
    have h : sl (ratGL ℚ 2 γ * x) = ratS ℚ g * sl x := toS_eq _ (by
      rw [e1, e2, ← hg]
      simp only [map_mul, map_inv, mul_assoc, mul_inv_cancel_left]
      rw [← mul_assoc (centralSection ℚ 2 s)⁻¹, hz]
      simp only [mul_assoc])
    change u (sl _) = u (sl x)
    rw [h]
    exact hu.left g _
  · obtain ⟨B, hB⟩ := hu.bdd
    exact ⟨B, fun x => hB _⟩
  · intro s₀ x
    obtain ⟨a, s, t, ht, hx⟩ := hex x
    have e1 := hMe x a s t ht hx
    have e2 := hMe (centralSection ℚ 2 s₀ * x) a (s₀ * s) t ht (by
      rw [map_mul, det_centralSection, hx, map_mul]
      simp only [mul_assoc, mul_left_comm])
    have h : sl (centralSection ℚ 2 s₀ * x) = 1 * sl x := toS_eq _ (by
      rw [e1, e2]
      simp only [map_mul, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left, map_one, one_mul])
    change u (sl _) = u (sl x)
    rw [h, one_mul]
  · intro g t ht
    have e := hMe (gl g * dM t) 1 1 t ht (by
      rw [map_mul, det_gl, det_dM]
      simp)
    have e' : Mx Q S T (gl g * dM t) = gl g := e.trans (by simp [dq_one])
    have h : sl (gl g * dM t) = g := Subtype.ext (congrArg Units.val e')
    change u (sl _) = u g
    rw [h]
  · intro x
    obtain ⟨a, s, t, ht, hx⟩ := hex x
    have e1 := hMe x a s t ht hx
    have key : ∀ b, sl (gl (nU b) * x) = nU (IdeleGroup.diagonal ℚ a⁻¹ • b) * sl x := fun b => toS_eq _ (by
      rw [hMe (gl (nU b) * x) a s t ht (by rw [map_mul, det_gl, one_mul, hx]), e1]
      simp only [mul_assoc]
      rw [← mul_assoc (centralSection ℚ 2 s)⁻¹, hz, mul_assoc, ← mul_assoc (ratGL ℚ 2 (dq a)⁻¹), nU_conj]
      simp only [mul_assoc])
    change ∫ b in fundamentalSet ℚ, u (sl (gl (nU b) * x)) ∂(adeleMeasure ℚ) = 0
    simp_rw [key]
    rw [scale_int a⁻¹ (fun b => u (nU b * sl x)) (fun c b => ?_)]
    · exact hu.cusp _
    · obtain ⟨γ, hγ⟩ := nU_rat c
      change u (nU (algebraMap ℚ (A ℚ) c + b) * sl x) = u (nU b * sl x)
      rw [nU_plus, hγ, mul_assoc]
      exact hu.left γ _

end UpperTheory.ConvolutionTheory.RankTwoDescent.Cp
