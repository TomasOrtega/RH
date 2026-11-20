import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.HeckeInj
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.FinSplit
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.PositionOf
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.GlueBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.GalAdEq
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.AdBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import Development.AutomorphicArithmetic.AdelicQuotients.AdeleGaloisActionBaseChangeCompat
import Development.AutomorphicArithmetic.AdelicQuotients.CentralSectionBaseChange

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

/- English proof (translation)
Use `Units.ext (Matrix.ext fun a b => Prod.ext ?_ (FiniteAdeleRing.ext E fun w => ?_))` and prove the remaining obligations. Conclude with `congrArg (fun x : GL (Fin n) (InfiniteAdeleRing E) => x.val a b) h1`. Conclude with `congrArg (fun x : GL (Fin n) (CompletionsOver E (AdeleBaseChange.below F w)) => x.val a b ⟨w, AdeleBaseChange.liesOver_below w⟩) (h2 _)`.
-/
private theorem ad_ext (F : Type) [Field F] [NumberField F] [Algebra F E] {g g' : AdelicGLn.AdelicGL E n}
    (h1 : T4.pI E n g = T4.pI E n g') (h2 : ∀ v : Pl F, T4.pE E n v g = T4.pE E n v g') : g = g' := by
  refine Units.ext (Matrix.ext fun a b => Prod.ext ?_ (FiniteAdeleRing.ext E fun w => ?_))
  · exact congrArg (fun x : GL (Fin n) (InfiniteAdeleRing E) => x.val a b) h1
  · exact congrArg (fun x : GL (Fin n) (CompletionsOver E (AdeleBaseChange.below F w)) =>
      x.val a b ⟨w, AdeleBaseChange.liesOver_below w⟩) (h2 _)

/- English proof (translation)
The claim follows from `Units.ext (Matrix.ext fun a b => (AdelicGLn.prodEquiv_apply_fst E n g a b).symm)`.
-/
private theorem pI_eq (g : AdelicGLn.AdelicGL E n) : T4.pI E n g = (AdelicGLn.prodEquiv E n g).1 :=
  Units.ext (Matrix.ext fun a b => (AdelicGLn.prodEquiv_apply_fst E n g a b).symm)

/- English proof (translation)
Use `Units.ext (Matrix.ext fun a b => funext fun w => ?_)` and prove the remaining obligations. Establish `h1 : (g.val a b).2 w.1 = (1 : GL (Fin n) (w.1.adicCompletion E)).val a b`. Rewrite using `[← h w, finAt_apply]`. Use `h1.trans ?_` and prove the remaining obligations. Simplify using `only [Units.val_one, Matrix.one_apply]`.

Apply the tactic sequence `split_ifs <;> rfl`.
-/
private theorem pE_ext {v : Pl F} {g : AdelicGLn.AdelicGL E n} (h : ∀ w : PlacesOver E v, finAt w.1 g = 1) :
    T4.pE E n v g = 1 := by
  refine Units.ext (Matrix.ext fun a b => funext fun w => ?_)
  have h1 : (g.val a b).2 w.1 = (1 : GL (Fin n) (w.1.adicCompletion E)).val a b := by
    rw [← h w, finAt_apply]
  refine h1.trans ?_
  simp only [Units.val_one, Matrix.one_apply]
  split_ifs <;> rfl

/- English proof (translation)
Establish `hl : Module.finrank F E ≠ 0` using `Module.finrank_pos.ne'`. Establish `e : (⟨(s : ℝ) ^ ((Module.finrank F E : ℝ))⁻¹, Real.rpow_pos_of_pos s.2 _⟩ : {r : ℝ // 0 < r}) ^ Module.finrank F E = s`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Positive.val_pow]`. Conclude with `Real.rpow_inv_natCast_pow s.2.le hl`.

Rewrite using `[← e, ← UpperTheory.centralSection_baseChange F E n]`. Conclude with `(UpperTheory.adele_galois_action_baseChange_compat F E σ n).2.2.2.2.1 _`.
-/
private theorem gal_cent (σ : E ≃ₐ[F] E) (s : {r : ℝ // 0 < r}) :
    mapGL n (galAd σ) (centralSection E n s) = centralSection E n s := by
  have hl : Module.finrank F E ≠ 0 := Module.finrank_pos.ne'
  have e : (⟨(s : ℝ) ^ ((Module.finrank F E : ℝ))⁻¹, Real.rpow_pos_of_pos s.2 _⟩ : {r : ℝ // 0 < r}) ^
      Module.finrank F E = s := by
    apply Subtype.ext
    rw [Positive.val_pow]
    exact Real.rpow_inv_natCast_pow s.2.le hl
  rw [← e, ← UpperTheory.centralSection_baseChange F E n]
  exact (UpperTheory.adele_galois_action_baseChange_compat F E σ n).2.2.2.2.1 _

/- English proof (translation)
Establish `h1 : ((θ.e (retractOne x) : G1 E n) : AdelicGLn.AdelicGL E n) * centralSection E n (detModule E n x) = mapGL n (galAd σ) x`. Rewrite using `[hθ, coe_retractOne, map_mul, map_inv, gal_cent, inv_mul_cancel_right]`. Rewrite using `[← h1, retractOne_mul, retractOne_coe, retractOne_centralSection, mul_one]`.
-/
private theorem gal_retract (σ : E ≃ₐ[F] E) (hn : 0 < n) {μ : Measure (G1 E n)} [μ.IsHaarMeasure] {θ : Twist μ}
    (hθ : IsGalTwist σ θ) (x : AdelicGLn.AdelicGL E n) :
    θ.e (retractOne x) = retractOne (mapGL n (galAd σ) x) := by
  have h1 : ((θ.e (retractOne x) : G1 E n) : AdelicGLn.AdelicGL E n) * centralSection E n (detModule E n x) =
      mapGL n (galAd σ) x := by
    rw [hθ, coe_retractOne, map_mul, map_inv, gal_cent, inv_mul_cancel_right]
  rw [← h1, retractOne_mul, retractOne_coe, retractOne_centralSection, mul_one]

/- English proof (translation)
Take `⟨c1, c2, -⟩` from `UpperTheory.adele_galois_action_baseChange_compat F E σ n`. Use `ad_ext F ?_ fun v => ?_` and prove the remaining obligations. Rewrite using `[c1, pI_eq, pI_eq, prodEquiv_infEmb, prodEquiv_infEmb, ContinuousMulEquiv.symm_apply_apply]`. Rewrite using `[c2, pE_ext fun w => finAt_infEmb w.1 _, pE_ext fun w => finAt_infEmb w.1 _, map_one]`.
-/
private theorem gal_infEmb (σ : E ≃ₐ[F] E) (a : archGroup E n) :
    mapGL n (galAd σ) (infEmb E n a) =
      infEmb E n (archEquiv E n (mapGL n (galInf σ) ((archEquiv E n).symm a))) := by
  obtain ⟨c1, c2, -⟩ := UpperTheory.adele_galois_action_baseChange_compat F E σ n
  refine ad_ext F ?_ fun v => ?_
  · rw [c1, pI_eq, pI_eq, prodEquiv_infEmb, prodEquiv_infEmb, ContinuousMulEquiv.symm_apply_apply]
  · rw [c2, pE_ext fun w => finAt_infEmb w.1 _, pE_ext fun w => finAt_infEmb w.1 _, map_one]

/- English proof (translation)
Use `⟨_, fun i => ?_, gal_infEmb σ k⟩` and prove the remaining obligations. Establish `hsh` using `(UpperTheory.ConvolutionTheory.L1.glueBasic _ _ _ _ m D n).2.2.2.2.2.2.1`. Establish `h : ∀ i x, compA D n i x = archEquiv F n (D.comp n i ((archEquiv E n).symm x))` using `fun _ _ => rfl`. Rewrite using `[h, h, ContinuousMulEquiv.symm_apply_apply, hsh]`.
-/
private theorem arch_shift {σ : E ≃ₐ[F] E} {m : ℕ} (D : InfD σ m) (k : archGroup E n) :
    ∃ k' : archGroup E n, (∀ i, compA D n i k' = compA D n (i + 1) k) ∧
      mapGL n (galAd σ) (infEmb E n k) = infEmb E n k' := by
  refine ⟨_, fun i => ?_, gal_infEmb σ k⟩
  have hsh := (UpperTheory.ConvolutionTheory.L1.glueBasic _ _ _ _ m D n).2.2.2.2.2.2.1
  have h : ∀ i x, compA D n i x = archEquiv F n (D.comp n i ((archEquiv E n).symm x)) := fun _ _ => rfl
  rw [h, h, ContinuousMulEquiv.symm_apply_apply, hsh]

/- English proof (translation)
Use `Units.ext (Matrix.ext fun a b => (completionMap v (w j).1).injective ?_)` and prove the remaining obligations. Use `(hD _ j).trans ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(finAt (w j).1 (finEmb E n (AdelicGLn.localEmbedding (w i).1 (mapGL n (completionMap v (w i).1) g)))).val a b = _`. Use `split_ifs with h`. Substitute `h` using the available equality.

Rewrite using `[(UpperTheory.ConvolutionTheory.Tf.locEmb E n (w j).1).2.1]`. Both sides reduce to the same expression. Rewrite using `[(UpperTheory.ConvolutionTheory.Tf.locEmb E n (w i).1).2.2.1 (w j).1 (fun h' => h (w.injective (Subtype.ext h')))]`. Simplify using `only [Units.val_one, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem comp_loc {σ : E ≃ₐ[F] E} {v : Pl F} (D : Split (incFin E v) (galFin σ v) 1)
    (w : Fin 2 ≃ PlacesOver E v)
    (hD : ∀ (b : CompletionsOver E v) i, completionMap v (w i).1 (D.e b i) = b (w i))
    (i j : Fin 2) (g : Gw n v) :
    D.comp n j (T4.pE E n v (finEmb E n (AdelicGLn.localEmbedding (w i).1 (mapGL n (completionMap v (w i).1) g)))) =
      if j = i then g else 1 := by
  refine Units.ext (Matrix.ext fun a b => (completionMap v (w j).1).injective ?_)
  refine (hD _ j).trans ?_
  change (finAt (w j).1 (finEmb E n (AdelicGLn.localEmbedding (w i).1 (mapGL n (completionMap v (w i).1) g)))).val a b = _
  split_ifs with h
  · subst h
    rw [(UpperTheory.ConvolutionTheory.Tf.locEmb E n (w j).1).2.1]
    rfl
  · rw [(UpperTheory.ConvolutionTheory.Tf.locEmb E n (w i).1).2.2.1 (w j).1 (fun h' => h (w.injective (Subtype.ext h')))]
    simp only [Units.val_one, Matrix.one_apply]
    split_ifs <;> simp

/- English proof (translation)
Use `pE_ext fun u => (UpperTheory.ConvolutionTheory.Tf.locEmb E n w.1).2.2.1 u.1 (fun h' => h ?_) x` and prove the remaining obligations. Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Rewrite using `[u.2.over, w.2.over, h']`.
-/
private theorem pE_loc {v v' : Pl F} (h : v' ≠ v) (w : PlacesOver E v) (x : Gw n w.1) :
    T4.pE E n v' (finEmb E n (AdelicGLn.localEmbedding w.1 x)) = 1 := by
  refine pE_ext fun u => (UpperTheory.ConvolutionTheory.Tf.locEmb E n w.1).2.2.1 u.1 (fun h' => h ?_) x
  apply HeightOneSpectrum.ext
  rw [u.2.over, w.2.over, h']

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ _ σ h2 hσ n hn μ _ θ`. Use `⟨?_, fun hθ => ⟨fun g => ?_, fun D eF e he k => ?_, fun v hv => ?_⟩⟩` and prove the remaining obligations. Unfold `IsGalTwist UpperTheory.ConvolutionTheory.K.IsGal`. Rewrite using `[UpperTheory.ConvolutionTheory.K.galAdEq]`. Establish `hs : σ.toRingEquiv.trans σ.toRingEquiv = RingEquiv.refl E`.

Establish `h : σ ^ 2 = 1`. Rewrite using `[← h2, ← IsGalois.card_aut_eq_finrank F E]`. Conclude with `pow_card_eq_one'`. Use extensionality with `x`. Conclude with `congrArg (fun τ : E ≃ₐ[F] E => τ x) ((sq σ).symm.trans h)`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hθ, hθ, UpperTheory.ConvolutionTheory.K.galAdEq]`. Use `Units.ext (Matrix.ext fun a b => ?_)` and prove the remaining obligations. Take `⟨-, b1, b2⟩` from `UpperTheory.ConvolutionTheory.K.adBasic E`. Use `(b2 _ _ _).symm.trans ?_` and prove the remaining obligations.

Rewrite using `[hs, b1]`. Establish `hc` using `(UpperTheory.ConvolutionTheory.L1.positionOf F E σ 1 D).2 n`. Establish `hk` using `(hc k).1 k.2`. Take `⟨k', key, hk'⟩` from `arch_shift D (k : archGroup E n)`. Establish `hm : k' ∈ archCompact E n` using `(hc k').2 fun i => by rw [key i]; exact hk (i + 1)`.

Use `⟨⟨k', hm⟩, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `θ.e (archP E n k) = archP E n k'`. Rewrite using `[← retract_infEmb, ← retract_infEmb, gal_retract σ hn hθ, hk']`. Rewrite using `[he k (fun i => ⟨_, hk i⟩) fun _ => rfl, he ⟨k', hm⟩ (fun i => ⟨_, hk (i + 1)⟩) fun i => (key i).symm, Fin.prod_univ_two, Fin.prod_univ_two, mul_comm]`. Both sides reduce to the same expression.

Choose the witnesses or unpack the hypotheses as in `⟨w₀⟩ : Nonempty (PlacesOver E v) := by`. Take `⟨⟨P, hP, hl⟩⟩ : Nonempty (v.asIdeal.primesOver (𝓞 E))` from `inferInstance`. Conclude with `⟨⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩, hl⟩⟩`. Take `⟨D, w, -, hD⟩` from `UpperTheory.ConvolutionTheory.L1.finSplit F E σ hσ 1 h2 v w₀ hv`. Use `⟨w, fun i g => ?_⟩` and prove the remaining obligations.

Take `⟨c1, c2, -⟩` from `UpperTheory.adele_galois_action_baseChange_compat F E σ n`. Take `⟨-, g2, -, -, -, -, hsh, -⟩` from `UpperTheory.ConvolutionTheory.L1.glueBasic _ _ _ _ 1 D n`. Express the relevant statement in the definitionally equal form `θ.e (retractOne (finEmb E n _)) = retractOne (finEmb E n _)`. Rewrite using `[gal_retract σ hn hθ]`. Use `congr 1`.

Use `ad_ext F ?_ fun v' => ?_` and prove the remaining obligations. Rewrite using `[c1, pI_eq, pI_eq, prodEquiv_finEmb, prodEquiv_finEmb, map_one]`. Rewrite using `[c2]`. Distinguish the cases in `h : v' = v`. Substitute `h` using the available equality.

Rewrite using `[← g2 (mapGL n (galFin σ v') _), ← g2 (T4.pE E n v' (finEmb E n (AdelicGLn.localEmbedding (w (i + 1)).1 _)))]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Rewrite using `[hsh, comp_loc D w hD, comp_loc D w hD]`. Establish `: j + 1 = i ↔ j = i + 1` using `by revert i j; decide`.

Simplify using `only [this]`. Rewrite using `[pE_loc h, pE_loc h, map_one]`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.galLoc :
    GalLoc := by
  intro F E _ _ _ _ _ _ _ _ σ h2 hσ n hn μ _ θ
  refine ⟨?_, fun hθ => ⟨fun g => ?_, fun D eF e he k => ?_, fun v hv => ?_⟩⟩
  · unfold IsGalTwist UpperTheory.ConvolutionTheory.K.IsGal
    rw [UpperTheory.ConvolutionTheory.K.galAdEq]
  · have hs : σ.toRingEquiv.trans σ.toRingEquiv = RingEquiv.refl E := by
      have h : σ ^ 2 = 1 := by
        rw [← h2, ← IsGalois.card_aut_eq_finrank F E]
        exact pow_card_eq_one'
      ext x
      exact congrArg (fun τ : E ≃ₐ[F] E => τ x) ((sq σ).symm.trans h)
    apply Subtype.ext
    rw [hθ, hθ, UpperTheory.ConvolutionTheory.K.galAdEq]
    refine Units.ext (Matrix.ext fun a b => ?_)
    obtain ⟨-, b1, b2⟩ := UpperTheory.ConvolutionTheory.K.adBasic E
    refine (b2 _ _ _).symm.trans ?_
    rw [hs, b1]
  · have hc := (UpperTheory.ConvolutionTheory.L1.positionOf F E σ 1 D).2 n
    have hk := (hc k).1 k.2
    obtain ⟨k', key, hk'⟩ := arch_shift D (k : archGroup E n)
    have hm : k' ∈ archCompact E n := (hc k').2 fun i => by rw [key i]; exact hk (i + 1)
    refine ⟨⟨k', hm⟩, ?_, ?_⟩
    · change θ.e (archP E n k) = archP E n k'
      rw [← retract_infEmb, ← retract_infEmb, gal_retract σ hn hθ, hk']
    · rw [he k (fun i => ⟨_, hk i⟩) fun _ => rfl, he ⟨k', hm⟩ (fun i => ⟨_, hk (i + 1)⟩) fun i => (key i).symm,
        Fin.prod_univ_two, Fin.prod_univ_two, mul_comm]
      rfl
  · obtain ⟨w₀⟩ : Nonempty (PlacesOver E v) := by
      obtain ⟨⟨P, hP, hl⟩⟩ : Nonempty (v.asIdeal.primesOver (𝓞 E)) := inferInstance
      exact ⟨⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩, hl⟩⟩
    obtain ⟨D, w, -, hD⟩ := UpperTheory.ConvolutionTheory.L1.finSplit F E σ hσ 1 h2 v w₀ hv
    refine ⟨w, fun i g => ?_⟩
    obtain ⟨c1, c2, -⟩ := UpperTheory.adele_galois_action_baseChange_compat F E σ n
    obtain ⟨-, g2, -, -, -, -, hsh, -⟩ := UpperTheory.ConvolutionTheory.L1.glueBasic _ _ _ _ 1 D n
    change θ.e (retractOne (finEmb E n _)) = retractOne (finEmb E n _)
    rw [gal_retract σ hn hθ]
    congr 1
    refine ad_ext F ?_ fun v' => ?_
    · rw [c1, pI_eq, pI_eq, prodEquiv_finEmb, prodEquiv_finEmb, map_one]
    · rw [c2]
      by_cases h : v' = v
      · subst h
        rw [← g2 (mapGL n (galFin σ v') _), ← g2 (T4.pE E n v' (finEmb E n (AdelicGLn.localEmbedding (w (i + 1)).1 _)))]
        congr 1
        funext j
        rw [hsh, comp_loc D w hD, comp_loc D w hD]
        have : j + 1 = i ↔ j = i + 1 := by revert i j; decide
        simp only [this]
      · rw [pE_loc h, pE_loc h, map_one]
