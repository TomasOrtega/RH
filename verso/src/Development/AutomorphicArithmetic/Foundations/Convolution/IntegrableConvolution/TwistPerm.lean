import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensFactor
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ArchBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.GlueBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.EigBasic
import Development.AutomorphicArithmetic.AdelicQuotients.AdeleGaloisActionBaseChangeCompat
import Development.AutomorphicArithmetic.AdelicQuotients.CentralSectionBaseChange
import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.CharacterColumnKernelsOfBlockChiCOfBlockChiOne
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.TwUnitary
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GroundTheory.Global GroundTheory.Global.SemiLocal PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

namespace UpperTheory.ConvolutionTheory.L1

section TwB
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `hd : 0 < Module.finrank F E` using `Module.finrank_pos`. Set `s : {r : ℝ // 0 < r}` to `⟨t.1 ^ (((Module.finrank F E : ℕ) : ℝ)⁻¹), Real.rpow_pos_of_pos t.2 _⟩`. Establish `hs : s ^ Module.finrank F E = t`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(t.1 ^ (((Module.finrank F E : ℕ) : ℝ)⁻¹)) ^ Module.finrank F E = t.1`.

Conclude with `Real.rpow_inv_natCast_pow t.2.le hd.ne'`. Rewrite using `[← hs, ← UpperTheory.centralSection_baseChange F E n s]`. Conclude with `(UpperTheory.adele_galois_action_baseChange_compat F E σ n).2.2.2.2.1 _`.
-/
private theorem gal_central (σ : E ≃ₐ[F] E) (n : ℕ) (t : {r : ℝ // 0 < r}) :
    mapGL n (galAd σ) (centralSection E n t) = centralSection E n t := by
  have hd : 0 < Module.finrank F E := Module.finrank_pos
  let s : {r : ℝ // 0 < r} := ⟨t.1 ^ (((Module.finrank F E : ℕ) : ℝ)⁻¹), Real.rpow_pos_of_pos t.2 _⟩
  have hs : s ^ Module.finrank F E = t := by
    apply Subtype.ext
    change (t.1 ^ (((Module.finrank F E : ℕ) : ℝ)⁻¹)) ^ Module.finrank F E = t.1
    exact Real.rpow_inv_natCast_pow t.2.le hd.ne'
  rw [← hs, ← UpperTheory.centralSection_baseChange F E n s]
  exact (UpperTheory.adele_galois_action_baseChange_compat F E σ n).2.2.2.2.1 _

/- English proof (translation)
Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Establish `: Subsingleton (AdelicGLn.AdelicGL E 0)` using `⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩`. Rewrite using `[Subsingleton.elim (mapGL 0 (galAd σ) g) g]`. Conclude with `(UpperTheory.ConvolutionTheory.G.character_column_kernels_of_block_chi_c_of_block_chi_one F E σ hσ n hn).2.2 g`.
-/
private theorem gal_module [IsGalois F E] (σ : E ≃ₐ[F] E) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) (n : ℕ)
    (g : AdelicGLn.AdelicGL E n) : detModule E n (mapGL n (galAd σ) g) = detModule E n g := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Subsingleton (AdelicGLn.AdelicGL E 0) :=
      ⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩
    rw [Subsingleton.elim (mapGL 0 (galAd σ) g) g]
  · exact (UpperTheory.ConvolutionTheory.G.character_column_kernels_of_block_chi_c_of_block_chi_one F E σ hσ n hn).2.2 g

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hθ, hx, hy, map_mul, map_inv, gal_central, hg, ← hg, gal_module σ hσ]`.
-/
private theorem e_proj [IsGalois F E] {σ : E ≃ₐ[F] E} (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) {n : ℕ}
    {μ : Measure (normOneGL E n)} [μ.IsHaarMeasure] {θ : Twist μ} (hθ : IsGalTwist σ θ)
    {g g' : AdelicGLn.AdelicGL E n} (hg : mapGL n (galAd σ) g = g') {x y : normOneGL E n}
    (hx : (x : AdelicGLn.AdelicGL E n) = g * (centralSection E n (detModule E n g))⁻¹)
    (hy : (y : AdelicGLn.AdelicGL E n) = g' * (centralSection E n (detModule E n g'))⁻¹) :
    θ.e x = y := by
  apply Subtype.ext
  rw [hθ, hx, hy, map_mul, map_inv, gal_central, hg, ← hg, gal_module σ hσ]

/- English proof (translation)
The claim follows from `e_proj hσ hθ h rfl rfl`.
-/
private theorem e_archP [IsGalois F E] {σ : E ≃ₐ[F] E} (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) {n : ℕ}
    {μ : Measure (normOneGL E n)} [μ.IsHaarMeasure] {θ : Twist μ} (hθ : IsGalTwist σ θ)
    {a a' : archGroup E n} (h : mapGL n (galAd σ) (infEmb E n a) = infEmb E n a') :
    θ.e (archP E n a) = archP E n a' :=
  e_proj hσ hθ h rfl rfl

/- English proof (translation)
The claim follows from `e_proj hσ hθ h rfl rfl`.
-/
private theorem e_finProj [IsGalois F E] {σ : E ≃ₐ[F] E} (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) {n : ℕ}
    {μ : Measure (normOneGL E n)} [μ.IsHaarMeasure] {θ : Twist μ} (hθ : IsGalTwist σ θ)
    {u u' : AdelicGLn.FiniteAdelicGL E n} (h : mapGL n (galAd σ) (finEmb E n u) = finEmb E n u') :
    θ.e (MultiplicityOne.finProj E n u) = MultiplicityOne.finProj E n u' :=
  e_proj hσ hθ h rfl rfl

/- English proof (translation)
Use `Units.ext (Matrix.ext fun a b => Prod.ext ?_ ?_)` and prove the remaining obligations. Conclude with `congrFun (congrFun (congrArg (fun x : GL (Fin n) (InfiniteAdeleRing E) => x.val) hi) a) b`. Use `FiniteAdeleRing.ext E fun w => ?_` and prove the remaining obligations. Establish `h1` using `congrFun (congrFun (congrArg (fun x : GL (Fin n) (CompletionsOver E (w.under (𝓞 F))) => x.val) (hf (w.under (𝓞 F)))) a) b`. Conclude with `congrFun h1 ⟨w, inferInstance⟩`.
-/
private theorem ad_ext {n : ℕ} {g h : AdelicGLn.AdelicGL E n}
    (hi : UpperTheory.ConvolutionTheory.T4.pI E n g = UpperTheory.ConvolutionTheory.T4.pI E n h)
    (hf : ∀ v : Pl F, UpperTheory.ConvolutionTheory.T4.pE E n v g = UpperTheory.ConvolutionTheory.T4.pE E n v h) : g = h := by
  refine Units.ext (Matrix.ext fun a b => Prod.ext ?_ ?_)
  · exact congrFun (congrFun (congrArg (fun x : GL (Fin n) (InfiniteAdeleRing E) => x.val) hi) a) b
  · refine FiniteAdeleRing.ext E fun w => ?_
    have h1 := congrFun (congrFun (congrArg (fun x : GL (Fin n) (CompletionsOver E (w.under (𝓞 F))) => x.val)
      (hf (w.under (𝓞 F)))) a) b
    exact congrFun h1 ⟨w, inferInstance⟩

/- English proof (translation)
The claim follows from `congrArg Prod.fst (prodEquiv_infEmb a)`.
-/
private theorem pI_infEmb {n : ℕ} (a : archGroup E n) :
    UpperTheory.ConvolutionTheory.T4.pI E n (infEmb E n a) = (archEquiv E n).symm a :=
  congrArg Prod.fst (prodEquiv_infEmb a)

/- English proof (translation)
Use `Units.ext (Matrix.ext fun a b => funext fun w => ?_)` and prove the remaining obligations. Establish `h1` using `congrFun (congrFun (congrArg (fun x : AdelicGLn.FiniteAdelicGL E n => x.val) h) a) b`. Establish `h2` using `congrArg (fun y : FiniteAdeleRing (𝓞 E) E => y w.1) h1`. Use `h2.trans ?_` and prove the remaining obligations. Distinguish the cases in `hab : a = b`.

Substitute `hab` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply_ne hab]`.
-/
private theorem pE_of_snd {n : ℕ} {g : AdelicGLn.AdelicGL E n} (h : (AdelicGLn.prodEquiv E n g).2 = 1) (v : Pl F) :
    UpperTheory.ConvolutionTheory.T4.pE E n v g = 1 := by
  refine Units.ext (Matrix.ext fun a b => funext fun w => ?_)
  have h1 := congrFun (congrFun (congrArg (fun x : AdelicGLn.FiniteAdelicGL E n => x.val) h) a) b
  have h2 := congrArg (fun y : FiniteAdeleRing (𝓞 E) E => y w.1) h1
  refine h2.trans ?_
  by_cases hab : a = b
  · subst hab; simp
  · simp [Matrix.one_apply_ne hab]

/- English proof (translation)
The claim follows from `pE_of_snd (congrArg Prod.snd (prodEquiv_infEmb a)) v`.
-/
private theorem pE_infEmb {n : ℕ} (a : archGroup E n) (v : Pl F) : UpperTheory.ConvolutionTheory.T4.pE E n v (infEmb E n a) = 1 :=
  pE_of_snd (congrArg Prod.snd (prodEquiv_infEmb a)) v

/- English proof (translation)
The claim follows from `congrArg Prod.fst (prodEquiv_finEmb u)`.
-/
private theorem pI_finEmb {n : ℕ} (u : AdelicGLn.FiniteAdelicGL E n) : UpperTheory.ConvolutionTheory.T4.pI E n (finEmb E n u) = 1 :=
  congrArg Prod.fst (prodEquiv_finEmb u)

/- English proof (translation)
Take `⟨c1, c2, -, -, -, -, c7, -⟩` from `UpperTheory.ConvolutionTheory.L1.glueBasic R S ι s m D n`. Rewrite using `[← c2 (mapGL n s (D.glue n h))]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Rewrite using `[c7, c1]`.
-/
private theorem glue_shift {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S] {ι : R →+* S} {s : S →+* S} {m : ℕ} (D : Split ι s m) (n : ℕ)
    (h : Fin (m + 1) → GL (Fin n) R) : mapGL n s (D.glue n h) = D.glue n fun j => h (j + 1) := by
  obtain ⟨c1, c2, -, -, -, -, c7, -⟩ := UpperTheory.ConvolutionTheory.L1.glueBasic R S ι s m D n
  rw [← c2 (mapGL n s (D.glue n h))]
  congr 1
  funext j
  rw [c7, c1]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Pi.mulSingle_eq_of_ne h, Pi.mulSingle_eq_of_ne (fun e => h (add_right_cancel e))]`.
-/
private theorem mulSingle_shift {m : ℕ} {G : Type*} [One G] (i : Fin (m + 1)) (g : G) :
    (fun j => (Pi.mulSingle (i + 1) g : Fin (m + 1) → G) (j + 1)) = Pi.mulSingle i g := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · rw [Pi.mulSingle_eq_of_ne h, Pi.mulSingle_eq_of_ne (fun e => h (add_right_cancel e))]

/- English proof (translation)
Establish `hc` using `UpperTheory.adele_galois_action_baseChange_compat F E σ n`. Use `ad_ext (F := F) ?_ fun v => ?_` and prove the remaining obligations. Rewrite using `[hc.1, pI_infEmb, pI_infEmb, hs, hs]`. Simplify using `only [glueA, ContinuousMulEquiv.symm_apply_apply]`. Rewrite using `[glue_shift, ← mulSingle_shift i g]`.

Rewrite using `[hc.2.1, pE_infEmb, pE_infEmb, map_one]`.
-/
private theorem gal_position {σ : E ≃ₐ[F] E} {m n : ℕ} (D : InfD σ m) {s : Fin (m + 1) → archGroup F n →* archGroup E n}
    (hs : IsBlockElement D n s) (i : Fin (m + 1)) (g : archGroup F n) :
    mapGL n (galAd σ) (infEmb E n (s (i + 1) g)) = infEmb E n (s i g) := by
  have hc := UpperTheory.adele_galois_action_baseChange_compat F E σ n
  refine ad_ext (F := F) ?_ fun v => ?_
  · rw [hc.1, pI_infEmb, pI_infEmb, hs, hs]
    simp only [glueA, ContinuousMulEquiv.symm_apply_apply]
    rw [glue_shift, ← mulSingle_shift i g]
  · rw [hc.2.1, pE_infEmb, pE_infEmb, map_one]

/- English proof (translation)
Rewrite using `[(UpperTheory.ConvolutionTheory.Dp.twUnitary E n μ θ).2.2, e_archP hσ hθ (gal_position D hs i g)]`.
-/
private theorem clause1 [IsGalois F E] {σ : E ≃ₐ[F] E} (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) {m n : ℕ}
    {μ : Measure (normOneGL E n)} [μ.IsHaarMeasure] {θ : Twist μ} (hθ : IsGalTwist σ θ) (D : InfD σ m)
    {s : Fin (m + 1) → archGroup F n →* archGroup E n} (hs : IsBlockElement D n s) (i : Fin (m + 1)) (g : archGroup F n)
    (v : LL μ) : θ.U (rightRegularRep (rationalGLOne E n) μ (archP E n (s (i + 1) g)) v) =
      rightRegularRep (rationalGLOne E n) μ (archP E n (s i g)) (θ.U v) := by
  rw [(UpperTheory.ConvolutionTheory.Dp.twUnitary E n μ θ).2.2, e_archP hσ hθ (gal_position D hs i g)]

/- English proof (translation)
The claim follows from `Units.ext (Matrix.ext fun _ _ => rfl)`.
-/
private theorem cmp_pE {n : ℕ} (p : Pl F) (u : PlacesOver E p) (g : AdelicGLn.AdelicGL E n) :
    GM.cmp u (UpperTheory.ConvolutionTheory.T4.pE E n p g) = finAt u.1 g :=
  Units.ext (Matrix.ext fun _ _ => rfl)

/- English proof (translation)
The claim follows from `Units.ext (Matrix.ext fun a b => funext fun u => congrFun (congrFun (congrArg (fun z : GL (Fin n) (u.1.adicCompletion E) => z.val) (h u)) a) b)`.
-/
private theorem gl_ext {n : ℕ} {p : Pl F} {x y : GL (Fin n) (CompletionsOver E p)} (h : ∀ u, GM.cmp u x = GM.cmp u y) : x = y :=
  Units.ext (Matrix.ext fun a b => funext fun u =>
    congrFun (congrFun (congrArg (fun z : GL (Fin n) (u.1.adicCompletion E) => z.val) (h u)) a) b)

/- English proof (translation)
Introduce `x y h` and use `Units.ext (Matrix.ext fun a b => f.injective (congrFun (congrFun (congrArg (fun z : GL (Fin n) S => z.val) h) a) b))`.
-/
private theorem mapGL_inj {K S : Type*} [Field K] [CommRing S] [Nontrivial S] {n : ℕ} (f : K →+* S) :
    Function.Injective (mapGL n f) := fun x y h =>
  Units.ext (Matrix.ext fun a b => f.injective
    (congrFun (congrFun (congrArg (fun z : GL (Fin n) S => z.val) h) a) b))

/- English proof (translation)
Establish `h1 : v.asIdeal = u.1.asIdeal.under (𝓞 F)` using `u.2.over`. Establish `h2 : p.asIdeal = u'.1.asIdeal.under (𝓞 F)` using `u'.2.over`. Conclude with `HeightOneSpectrum.ext (by rw [h1, h2, h])`.
-/
private theorem over_unique {v p : Pl F} (u : PlacesOver E v) (u' : PlacesOver E p) (h : u.1 = u'.1) : v = p := by
  have h1 : v.asIdeal = u.1.asIdeal.under (𝓞 F) := u.2.over
  have h2 : p.asIdeal = u'.1.asIdeal.under (𝓞 F) := u'.2.over
  exact HeightOneSpectrum.ext (by rw [h1, h2, h])

/- English proof (translation)
The claim follows from `(UpperTheory.ConvolutionTheory.Tf.locEmb E n w).2.1 x`.
-/
private theorem fin_local {n : ℕ} (w : Pl E) (x : GL (Fin n) (w.adicCompletion E)) :
    finAt w (finEmb E n (AdelicGLn.localEmbedding w x)) = x :=
  (UpperTheory.ConvolutionTheory.Tf.locEmb E n w).2.1 x

/- English proof (translation)
The claim follows from `(UpperTheory.ConvolutionTheory.Tf.locEmb E n w).2.2.1 u h x`.
-/
private theorem fin_local_ne {n : ℕ} {w u : Pl E} (h : u ≠ w) (x : GL (Fin n) (w.adicCompletion E)) :
    finAt u (finEmb E n (AdelicGLn.localEmbedding w x)) = 1 :=
  (UpperTheory.ConvolutionTheory.Tf.locEmb E n w).2.2.1 u h x

/- English proof (translation)
Use `gl_ext fun u => ?_` and prove the remaining obligations. Rewrite using `[cmp_pE, map_one, fin_local_ne (fun e => hv (over_unique u w e))]`.
-/
private theorem pE_local_ne {n : ℕ} {v p : Pl F} (hv : v ≠ p) (w : PlacesOver E p) (x : GL (Fin n) (w.1.adicCompletion E)) :
    UpperTheory.ConvolutionTheory.T4.pE E n v (finEmb E n (AdelicGLn.localEmbedding w.1 x)) = 1 := by
  refine gl_ext fun u => ?_
  rw [cmp_pE, map_one, fin_local_ne (fun e => hv (over_unique u w e))]

/- English proof (translation)
Establish `hc` using `UpperTheory.adele_galois_action_baseChange_compat F E σ n`. Use `ad_ext (F := F) ?_ fun v => ?_` and prove the remaining obligations. Rewrite using `[hc.1, pI_finEmb, pI_finEmb, map_one]`. Rewrite using `[hc.2.1 v]`. Distinguish the cases in `hv : v = p`.

Substitute `hv` using the available equality. Establish `hcmp : ∀ (b : GL (Fin n) (CompletionsOver E v)) j, GM.cmp (w j) b = mapGL n (completionMap v (w j).1) (D.comp n j b)` using `fun b j => Units.ext (Matrix.ext fun a c => (hw ((b : Matrix (Fin n) (Fin n) (CompletionsOver E v)) a c) j).symm)`. Take `⟨-, -, -, -, -, -, c7, -⟩` from `UpperTheory.ConvolutionTheory.L1.glueBasic _ _ (incFin E v) (galFin σ v) m D n`. Use `gl_ext fun u => ?_` and prove the remaining obligations. Take `⟨j, rfl⟩` from `w.surjective u`.

Rewrite using `[hcmp, c7, cmp_pE]`. Use `set b := UpperTheory.ConvolutionTheory.T4.pE E n v (finEmb E n (AdelicGLn.localEmbedding (w (i + 1)).1 (mapGL n (completionMap v (w (i + 1)).1) g))) with hb`. Establish `h1` using `hcmp b (j + 1)`. Rewrite `h1` using `[hb, cmp_pE, ← hb]`. Distinguish the cases in `hji : j = i`.

Substitute `hji` using the available equality. Rewrite `h1`, the goal using `[fin_local]`. Rewrite using `[mapGL_inj _ h1]`. Establish `hne : (w (j + 1)).1 ≠ (w (i + 1)).1` using `fun e => hji (add_right_cancel (w.injective (Subtype.ext e)))`. Establish `hne' : (w j).1 ≠ (w i).1` using `fun e => hji (w.injective (Subtype.ext e))`.

Rewrite `h1` using `[fin_local_ne hne, ← map_one (mapGL n (completionMap v (w (j + 1)).1))]`. Rewrite using `[fin_local_ne hne', ← mapGL_inj _ h1, map_one]`. Rewrite using `[pE_local_ne hv, pE_local_ne hv, map_one]`.
-/
private theorem gal_place {σ : E ≃ₐ[F] E} {m n : ℕ} (p : Pl F) (D : Split (incFin E p) (galFin σ p) m)
    (w : Fin (m + 1) ≃ PlacesOver E p)
    (hw : ∀ (b : CompletionsOver E p) i, completionMap p (w i).1 (D.e b i) = b (w i)) (i : Fin (m + 1))
    (g : GL (Fin n) (p.adicCompletion F)) :
    mapGL n (galAd σ) (finEmb E n (AdelicGLn.localEmbedding (w (i + 1)).1 (mapGL n (completionMap p (w (i + 1)).1) g))) =
      finEmb E n (AdelicGLn.localEmbedding (w i).1 (mapGL n (completionMap p (w i).1) g)) := by
  have hc := UpperTheory.adele_galois_action_baseChange_compat F E σ n
  refine ad_ext (F := F) ?_ fun v => ?_
  · rw [hc.1, pI_finEmb, pI_finEmb, map_one]
  · rw [hc.2.1 v]
    by_cases hv : v = p
    · subst hv
      have hcmp : ∀ (b : GL (Fin n) (CompletionsOver E v)) j,
          GM.cmp (w j) b = mapGL n (completionMap v (w j).1) (D.comp n j b) := fun b j =>
        Units.ext (Matrix.ext fun a c => (hw ((b : Matrix (Fin n) (Fin n) (CompletionsOver E v)) a c) j).symm)
      obtain ⟨-, -, -, -, -, -, c7, -⟩ := UpperTheory.ConvolutionTheory.L1.glueBasic _ _ (incFin E v) (galFin σ v) m D n
      refine gl_ext fun u => ?_
      obtain ⟨j, rfl⟩ := w.surjective u
      rw [hcmp, c7, cmp_pE]
      set b := UpperTheory.ConvolutionTheory.T4.pE E n v
        (finEmb E n (AdelicGLn.localEmbedding (w (i + 1)).1 (mapGL n (completionMap v (w (i + 1)).1) g))) with hb
      have h1 := hcmp b (j + 1)
      rw [hb, cmp_pE, ← hb] at h1
      by_cases hji : j = i
      · subst hji
        rw [fin_local] at h1 ⊢
        rw [mapGL_inj _ h1]
      · have hne : (w (j + 1)).1 ≠ (w (i + 1)).1 := fun e =>
          hji (add_right_cancel (w.injective (Subtype.ext e)))
        have hne' : (w j).1 ≠ (w i).1 := fun e => hji (w.injective (Subtype.ext e))
        rw [fin_local_ne hne, ← map_one (mapGL n (completionMap v (w (j + 1)).1))] at h1
        rw [fin_local_ne hne', ← mapGL_inj _ h1, map_one]
    · rw [pE_local_ne hv, pE_local_ne hv, map_one]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `θ.U (rightRegularRep (rationalGLOne E n) μ (MultiplicityOne.finProj E n _) v) = rightRegularRep (rationalGLOne E n) μ (MultiplicityOne.finProj E n _) (θ.U v)`. Rewrite using `[(UpperTheory.ConvolutionTheory.Dp.twUnitary E n μ θ).2.2, e_finProj hσ hθ (gal_place p D w hw i g)]`.
-/
private theorem clause2 [IsGalois F E] {σ : E ≃ₐ[F] E} (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) {m n : ℕ}
    {μ : Measure (normOneGL E n)} [μ.IsHaarMeasure] {θ : Twist μ} (hθ : IsGalTwist σ θ) (p : Pl F)
    (D : Split (incFin E p) (galFin σ p) m) (w : Fin (m + 1) ≃ PlacesOver E p)
    (hw : ∀ (b : CompletionsOver E p) i, completionMap p (w i).1 (D.e b i) = b (w i)) (i : Fin (m + 1))
    (g : GL (Fin n) (p.adicCompletion F)) (v : LL μ) :
    θ.U (rhoL μ (w (i + 1)).1 (mapGL n (completionMap p (w (i + 1)).1) g) v) =
      rhoL μ (w i).1 (mapGL n (completionMap p (w i).1) g) (θ.U v) := by
  change θ.U (rightRegularRep (rationalGLOne E n) μ (MultiplicityOne.finProj E n _) v) =
    rightRegularRep (rationalGLOne E n) μ (MultiplicityOne.finProj E n _) (θ.U v)
  rw [(UpperTheory.ConvolutionTheory.Dp.twUnitary E n μ θ).2.2, e_finProj hσ hθ (gal_place p D w hw i g)]

open scoped TensorProduct in
/- English proof (translation)
Establish `h : ∀ x : E ⊗[F] A, Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F A) (Algebra.TensorProduct.map (τ : E →ₐ[F] E) (AlgHom.id F A) x) = Algebra.TensorProduct.map ((σ * τ : E ≃ₐ[F] E) : E →ₐ[F] E) (AlgHom.id F A) x`. Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a c => simp`.

Consider the case `add a c ha hc => simp only [map_add, ha, hc]`. Simplify using `[galOf, h]`.
-/
private theorem galOf_mul {A B : Type*} [CommRing A] [Algebra F A] [CommRing B] [Algebra E B] (e : E ⊗[F] A ≃ₐ[E] B)
    (σ τ : E ≃ₐ[F] E) (b : B) : galOf e σ (galOf e τ b) = galOf e (σ * τ) b := by
  have h : ∀ x : E ⊗[F] A, Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F A)
      (Algebra.TensorProduct.map (τ : E →ₐ[F] E) (AlgHom.id F A) x) =
      Algebra.TensorProduct.map ((σ * τ : E ≃ₐ[F] E) : E →ₐ[F] E) (AlgHom.id F A) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a c => simp
    | add a c ha hc => simp only [map_add, ha, hc]
  simp [galOf, h]

open scoped TensorProduct in
/- English proof (translation)
Establish `h : ∀ x : E ⊗[F] A, Algebra.TensorProduct.map ((1 : E ≃ₐ[F] E) : E →ₐ[F] E) (AlgHom.id F A) x = x`. Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a c => simp`.

Consider the case `add a c ha hc => simp only [map_add, ha, hc]`. Simplify using `[galOf, h]`.
-/
private theorem galOf_one {A B : Type*} [CommRing A] [Algebra F A] [CommRing B] [Algebra E B] (e : E ⊗[F] A ≃ₐ[E] B)
    (b : B) : galOf e (1 : E ≃ₐ[F] E) b = b := by
  have h : ∀ x : E ⊗[F] A, Algebra.TensorProduct.map ((1 : E ≃ₐ[F] E) : E →ₐ[F] E) (AlgHom.id F A) x = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a c => simp
    | add a c ha hc => simp only [map_add, ha, hc]
  simp [galOf, h]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Use `Units.ext (Matrix.ext fun a b => ?_)` and prove the remaining obligations. Conclude with `(galOf_one (tensorEquiv' E v) _).symm`. Consider the case `succ k ih`.

Rewrite using `[Function.iterate_succ_apply', ih]`. Use `Units.ext (Matrix.ext fun a b => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `galFin σ v (galFin (σ ^ k) v _) = galFin (σ ^ (k + 1)) v _`. Rewrite using `[pow_succ']`. Conclude with `galOf_mul (tensorEquiv' E v) _ _ _`.
-/
private theorem mapGL_iter (σ : E ≃ₐ[F] E) (v : Pl F) {n : ℕ} (k : ℕ) (Y : GL (Fin n) (CompletionsOver E v)) :
    (mapGL n (galFin σ v))^[k] Y = mapGL n (galFin (σ ^ k) v) Y := by
  induction k with
  | zero =>
    refine Units.ext (Matrix.ext fun a b => ?_)
    exact (galOf_one (tensorEquiv' E v) _).symm
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    refine Units.ext (Matrix.ext fun a b => ?_)
    change galFin σ v (galFin (σ ^ k) v _) = galFin (σ ^ (k + 1)) v _
    rw [pow_succ']
    exact galOf_mul (tensorEquiv' E v) _ _ _

private def lp {n : ℕ} {v : Pl F} (Z : GL (Fin n) (CompletionsOver E v)) (l : List (PlacesOver E v)) :
    AdelicGLn.FiniteAdelicGL E n :=
  (l.map fun u => AdelicGLn.localEmbedding u.1 (GM.cmp u Z)).prod

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem lp_nil {n : ℕ} {v : Pl F} (Z : GL (Fin n) (CompletionsOver E v)) : lp Z [] = 1 := rfl

/- English proof (translation)
Simplify using `[lp]`.
-/
private theorem lp_cons {n : ℕ} {v : Pl F} (Z : GL (Fin n) (CompletionsOver E v)) (a : PlacesOver E v)
    (l : List (PlacesOver E v)) : lp Z (a :: l) = AdelicGLn.localEmbedding a.1 (GM.cmp a Z) * lp Z l := by
  simp [lp]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => rw [lp_nil, map_one, finAt_one]`. Consider the case `cons a l ih`. Rewrite using `[lp_cons, map_mul, finAt_mul, ih fun u hu => h u (List.mem_cons_of_mem _ hu), fin_local_ne (h a List.mem_cons_self).symm, one_mul]`.
-/
private theorem lp_fin_ne {n : ℕ} {v : Pl F} (Z : GL (Fin n) (CompletionsOver E v)) (w : Pl E)
    (l : List (PlacesOver E v)) (h : ∀ u ∈ l, u.1 ≠ w) : finAt w (finEmb E n (lp Z l)) = 1 := by
  induction l with
  | nil => rw [lp_nil, map_one, finAt_one]
  | cons a l ih =>
    rw [lp_cons, map_mul, finAt_mul, ih fun u hu => h u (List.mem_cons_of_mem _ hu),
      fin_local_ne (h a List.mem_cons_self).symm, one_mul]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp at hu`. Consider the case `cons a l ih`. Rewrite `hl` using `[List.nodup_cons]`. Rewrite using `[lp_cons, map_mul, finAt_mul]`.

Distinguish the cases in `hau : u = a`. Substitute `hau` using the available equality. Rewrite using `[fin_local, lp_fin_ne Z _ l (fun x hx e => hl.1 (by rwa [← (Subtype.ext e : x = u)])), mul_one]`. Rewrite using `[fin_local_ne (fun e => hau (Subtype.ext e)), one_mul, ih hl.2 ((List.mem_cons.1 hu).resolve_left hau)]`.
-/
private theorem lp_fin_mem {n : ℕ} {v : Pl F} (Z : GL (Fin n) (CompletionsOver E v)) (l : List (PlacesOver E v))
    (hl : l.Nodup) (u : PlacesOver E v) (hu : u ∈ l) : finAt u.1 (finEmb E n (lp Z l)) = GM.cmp u Z := by
  induction l with
  | nil => simp at hu
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    rw [lp_cons, map_mul, finAt_mul]
    by_cases hau : u = a
    · subst hau
      rw [fin_local, lp_fin_ne Z _ l (fun x hx e => hl.1 (by rwa [← (Subtype.ext e : x = u)])), mul_one]
    · rw [fin_local_ne (fun e => hau (Subtype.ext e)), one_mul, ih hl.2 ((List.mem_cons.1 hu).resolve_left hau)]

private def pt {n : ℕ} {v : Pl F} (Z : GL (Fin n) (CompletionsOver E v)) : AdelicGLn.FiniteAdelicGL E n :=
  lp Z Finset.univ.toList

/- English proof (translation)
The claim follows from `gl_ext fun u => by rw [cmp_pE] exact lp_fin_mem Z _ (Finset.nodup_toList _) u (Finset.mem_toList.2 (Finset.mem_univ u))`.
-/
private theorem pE_pt {n : ℕ} {v : Pl F} (Z : GL (Fin n) (CompletionsOver E v)) :
    UpperTheory.ConvolutionTheory.T4.pE E n v (finEmb E n (pt Z)) = Z :=
  gl_ext fun u => by
    rw [cmp_pE]
    exact lp_fin_mem Z _ (Finset.nodup_toList _) u (Finset.mem_toList.2 (Finset.mem_univ u))

/- English proof (translation)
The claim follows from `gl_ext fun u => by rw [cmp_pE, map_one] exact lp_fin_ne Z _ _ fun x _ e => hv (over_unique u x e.symm)`.
-/
private theorem pE_pt_ne {n : ℕ} {v v' : Pl F} (hv : v' ≠ v) (Z : GL (Fin n) (CompletionsOver E v)) :
    UpperTheory.ConvolutionTheory.T4.pE E n v' (finEmb E n (pt Z)) = 1 :=
  gl_ext fun u => by
    rw [cmp_pE, map_one]
    exact lp_fin_ne Z _ _ fun x _ e => hv (over_unique u x e.symm)

/- English proof (translation)
Establish `hc` using `UpperTheory.adele_galois_action_baseChange_compat F E σ n`. Use `ad_ext (F := F) ?_ fun v' => ?_` and prove the remaining obligations. Rewrite using `[hc.1, pI_finEmb, pI_finEmb, map_one]`. Rewrite using `[hc.2.1 v']`. Distinguish the cases in `hv : v' = v`.

Substitute `hv` using the available equality. Rewrite using `[pE_pt, pE_pt]`. Rewrite using `[pE_pt_ne hv, pE_pt_ne hv, map_one]`.
-/
private theorem gal_pt (σ : E ≃ₐ[F] E) {n : ℕ} {v : Pl F} (Z : GL (Fin n) (CompletionsOver E v)) :
    mapGL n (galAd σ) (finEmb E n (pt Z)) = finEmb E n (pt (mapGL n (galFin σ v) Z)) := by
  have hc := UpperTheory.adele_galois_action_baseChange_compat F E σ n
  refine ad_ext (F := F) ?_ fun v' => ?_
  · rw [hc.1, pI_finEmb, pI_finEmb, map_one]
  · rw [hc.2.1 v']
    by_cases hv : v' = v
    · subst hv
      rw [pE_pt, pE_pt]
    · rw [pE_pt_ne hv, pE_pt_ne hv, map_one]

/- English proof (translation)
Use `finEmb_injective (ad_ext (F := F) ?_ fun v' => ?_)` and prove the remaining obligations. Rewrite using `[pI_finEmb, pI_finEmb]`. Distinguish the cases in `hv : v' = v`. Substitute `hv` using the available equality. Rewrite using `[pE_pt]`.

Rewrite using `[pE_pt_ne hv, pE_local_ne hv]`.
-/
private theorem pt_local {n : ℕ} {v : Pl F} (u : PlacesOver E v) (y : GL (Fin n) (u.1.adicCompletion E)) :
    pt (UpperTheory.ConvolutionTheory.T4.pE E n v (finEmb E n (AdelicGLn.localEmbedding u.1 y))) = AdelicGLn.localEmbedding u.1 y := by
  refine finEmb_injective (ad_ext (F := F) ?_ fun v' => ?_)
  · rw [pI_finEmb, pI_finEmb]
  · by_cases hv : v' = v
    · subst hv
      rw [pE_pt]
    · rw [pE_pt_ne hv, pE_local_ne hv]

section Types
variable {σ : E ≃ₐ[F] E} {n : ℕ} {q : Pl F} {w₀ : PlacesOver E q}
variable (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure]

/- English proof (translation)
Simplify using `only [rhoF, map_mul, UnitaryRep.map_mul_apply]`.
-/
private theorem rhoF_mul (h h' : AdelicGLn.FiniteAdelicGL E n) (f : LL μ) :
    rhoF μ (h * h') f = rhoF μ h (rhoF μ h' f) := by
  simp only [rhoF, map_mul, UnitaryRep.map_mul_apply]

/- English proof (translation)
Simplify using `only [rhoF, map_one, UnitaryRep.map_one]`. Both sides reduce to the same expression.
-/
private theorem rhoF_one (f : LL μ) : rhoF μ (1 : AdelicGLn.FiniteAdelicGL E n) f = f := by
  simp only [rhoF, map_one, UnitaryRep.map_one]
  rfl

/- English proof (translation)
Simplify using `only [eigL, Submodule.mem_iInf, LinearMap.mem_eqLocus, ContinuousLinearMap.coe_coe, LinearMap.smul_apply, LinearMap.id_apply]`.
-/
private theorem mem_eigL {w : Pl E} {J : Subgroup (Gw n w)} {χ : Gw n w → ℂ} {f : LL μ} :
    f ∈ eigL μ w J χ ↔ ∀ x ∈ J, rhoL μ w x f = χ x • f := by
  simp only [eigL, Submodule.mem_iInf, LinearMap.mem_eqLocus, ContinuousLinearMap.coe_coe,
    LinearMap.smul_apply, LinearMap.id_apply]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp [lp_nil, rhoF_one]`. Consider the case `cons a l ih`. Rewrite using `[lp_cons, rhoF_mul, ih (fun u hu => hJ u (List.mem_cons_of_mem _ hu)) (fun u hu => hf u (List.mem_cons_of_mem _ hu)), map_smul]`. Establish `h1` using `(mem_eigL μ).1 (hf a List.mem_cons_self) _ (hJ a List.mem_cons_self)`.

Express the relevant statement in the definitionally equal form `_ • rhoL μ a.1 _ f = _`. Rewrite using `[h1, smul_smul, List.map_cons, List.prod_cons, mul_comm]`.
-/
private theorem rho_lp (J : ∀ w : Pl E, Subgroup (Gw n w)) (χ : ∀ w : Pl E, Gw n w → ℂ) {v : Pl F}
    (Z : GL (Fin n) (CompletionsOver E v)) (l : List (PlacesOver E v)) (f : LL μ)
    (hJ : ∀ u ∈ l, GM.cmp u Z ∈ J u.1) (hf : ∀ u ∈ l, f ∈ eigL μ u.1 (J u.1) (χ u.1)) :
    rhoF μ (lp Z l) f = (l.map fun u => χ u.1 (GM.cmp u Z)).prod • f := by
  induction l with
  | nil => simp [lp_nil, rhoF_one]
  | cons a l ih =>
    rw [lp_cons, rhoF_mul, ih (fun u hu => hJ u (List.mem_cons_of_mem _ hu))
      (fun u hu => hf u (List.mem_cons_of_mem _ hu)), map_smul]
    have h1 := (mem_eigL μ).1 (hf a List.mem_cons_self) _ (hJ a List.mem_cons_self)
    change _ • rhoL μ a.1 _ f = _
    rw [h1, smul_smul, List.map_cons, List.prod_cons, mul_comm]

private def chiT (T : Ty σ n q w₀) (v : Pl F) (Z : GL (Fin n) (CompletionsOver E v)) : ℂ :=
  ∏ᶠ u : PlacesOver E v, T.χ u.1 (GM.cmp u Z)

/- English proof (translation)
Rewrite using `[pt, rho_lp μ T.J T.χ Z _ f (fun u _ => hZ u) (fun u _ => hf u), chiT, finprod_eq_prod_of_fintype, Finset.prod_map_toList]`.
-/
private theorem pt_eig (T : Ty σ n q w₀) {v : Pl F} (Z : GL (Fin n) (CompletionsOver E v)) (f : LL μ)
    (hZ : ∀ u : PlacesOver E v, GM.cmp u Z ∈ T.J u.1) (hf : ∀ u : PlacesOver E v, f ∈ eigL μ u.1 (T.J u.1) (T.χ u.1)) :
    rhoF μ (pt Z) f = chiT T v Z • f := by
  rw [pt, rho_lp μ T.J T.χ Z _ f (fun u _ => hZ u) (fun u _ => hf u), chiT,
    finprod_eq_prod_of_fintype, Finset.prod_map_toList]

/- English proof (translation)
Take `⟨-, h1, h2⟩` from `T.chr w`. Establish `h3` using `h2 1 (one_mem _) 1 (one_mem _)`. Rewrite `h3` using `[mul_one]`. Establish `h4 : T.χ w 1 ≠ 0` using `fun e => by`. Use `h1 1 (one_mem _)` as an intermediate fact.

Rewrite `this` using `[e, norm_zero]`. Conclude with `zero_ne_one this`. Conclude with `(mul_left_cancel₀ h4 (by rw [mul_one]; exact h3)).symm`.
-/
private theorem chi_one (T : Ty σ n q w₀) (w : Pl E) : T.χ w 1 = 1 := by
  obtain ⟨-, h1, h2⟩ := T.chr w
  have h3 := h2 1 (one_mem _) 1 (one_mem _)
  rw [mul_one] at h3
  have h4 : T.χ w 1 ≠ 0 := fun e => by
    have := h1 1 (one_mem _)
    rw [e, norm_zero] at this
    exact zero_ne_one this
  exact (mul_left_cancel₀ h4 (by rw [mul_one]; exact h3)).symm

/- English proof (translation)
Rewrite using `[chiT, finprod_eq_single _ u₀ fun u hu => ?_]`. Rewrite using `[cmp_pE, fin_local]`. Rewrite using `[cmp_pE, fin_local_ne (fun e => hu (Subtype.ext e)), chi_one]`.
-/
private theorem chi_single (T : Ty σ n q w₀) {v : Pl F} (u₀ : PlacesOver E v) (y : Gw n u₀.1) :
    chiT T v (UpperTheory.ConvolutionTheory.T4.pE E n v (finEmb E n (AdelicGLn.localEmbedding u₀.1 y))) = T.χ u₀.1 y := by
  rw [chiT, finprod_eq_single _ u₀ fun u hu => ?_]
  · rw [cmp_pE, fin_local]
  · rw [cmp_pE, fin_local_ne (fun e => hu (Subtype.ext e)), chi_one]

/- English proof (translation)
Distinguish the cases in `hu : u = u₀`. Substitute `hu` using the available equality. Rewrite using `[cmp_pE, fin_local]`. Conclude with `hy`. Rewrite using `[cmp_pE, fin_local_ne (fun e => hu (Subtype.ext e))]`.

Conclude with `one_mem _`.
-/
private theorem single_mem (T : Ty σ n q w₀) {v : Pl F} (u₀ : PlacesOver E v) {y : Gw n u₀.1} (hy : y ∈ T.J u₀.1)
    (u : PlacesOver E v) :
    GM.cmp u (UpperTheory.ConvolutionTheory.T4.pE E n v (finEmb E n (AdelicGLn.localEmbedding u₀.1 y))) ∈ T.J u.1 := by
  by_cases hu : u = u₀
  · subst hu
    rw [cmp_pE, fin_local]
    exact hy
  · rw [cmp_pE, fin_local_ne (fun e => hu (Subtype.ext e))]
    exact one_mem _

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => exact ⟨hY, rfl⟩`. Consider the case `succ k ih`. Rewrite using `[Function.iterate_succ_apply']`. Take `⟨h1, h2⟩` from `T.stable v _ ih.1`.

Conclude with `⟨h1, h2.trans ih.2⟩`.
-/
private theorem stable_iter (T : Ty σ n q w₀) {v : Pl F} (Y : GL (Fin n) (CompletionsOver E v))
    (hY : ∀ u : PlacesOver E v, GM.cmp u Y ∈ T.J u.1) (k : ℕ) :
    (∀ u : PlacesOver E v, GM.cmp u ((mapGL n (galFin σ v))^[k] Y) ∈ T.J u.1) ∧
      chiT T v ((mapGL n (galFin σ v))^[k] Y) = chiT T v Y := by
  induction k with
  | zero => exact ⟨hY, rfl⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨h1, h2⟩ := T.stable v _ ih.1
    exact ⟨h1, h2.trans ih.2⟩

/- English proof (translation)
Take `⟨k, hk⟩` from `Nat.exists_eq_succ_of_ne_zero (orderOf_pos σ).ne'`. Take `⟨h1, h2⟩` from `stable_iter T Y hY k`. Use `⟨_, h1, ?_, h2⟩` and prove the remaining obligations. Rewrite using `[← Function.iterate_succ_apply' (mapGL n (galFin σ v)), mapGL_iter, ← hk, pow_orderOf_eq_one]`. Use `Units.ext (Matrix.ext fun a b => ?_)` and prove the remaining obligations.

Conclude with `galOf_one (tensorEquiv' E v) _`.
-/
private theorem exists_pre [FiniteDimensional F E] (T : Ty σ n q w₀) {v : Pl F} (Y : GL (Fin n) (CompletionsOver E v))
    (hY : ∀ u : PlacesOver E v, GM.cmp u Y ∈ T.J u.1) :
    ∃ Z : GL (Fin n) (CompletionsOver E v), (∀ u : PlacesOver E v, GM.cmp u Z ∈ T.J u.1) ∧
      mapGL n (galFin σ v) Z = Y ∧ chiT T v Z = chiT T v Y := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (orderOf_pos σ).ne'
  obtain ⟨h1, h2⟩ := stable_iter T Y hY k
  refine ⟨_, h1, ?_, h2⟩
  rw [← Function.iterate_succ_apply' (mapGL n (galFin σ v)), mapGL_iter, ← hk,
    pow_orderOf_eq_one]
  refine Units.ext (Matrix.ext fun a b => ?_)
  exact galOf_one (tensorEquiv' E v) _

/- English proof (translation)
The claim follows from `HeightOneSpectrum.ext u.2.over.symm`.
-/
private theorem under_eq {v : Pl F} (u : PlacesOver E v) : u.1.under (𝓞 F) = v :=
  HeightOneSpectrum.ext u.2.over.symm

end Types

section Commute
variable {σ : E ≃ₐ[F] E} {n : ℕ} {q : Pl F} {w₀ : PlacesOver E q}

/- English proof (translation)
Establish `hc : V.topologicalClosure = V` using `hV.submodule_topologicalClosure_eq`. Establish `hm : ∀ v, v ∈ V.topologicalClosure ↔ v ∈ V` using `fun v => by rw [hc]`. Establish `a1 : ∀ v, prj V v ∈ V` using `fun v => (hm _).1 (Submodule.starProjection_apply_mem _ v)`. Establish `a3 : ∀ v, ∀ w ∈ V, inner ℂ (v - prj V v) w = 0` using `fun v w hw => Submodule.starProjection_inner_eq_zero v w ((hm _).2 hw)`. Use `ContinuousLinearMap.ext fun v => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `U (prj V v) = prj V (U v)`. Use `symm`. Use `Submodule.eq_starProjection_of_mem_of_inner_eq_zero ((hm _).2 (h1 _ (a1 v))) fun w hw => ?_` and prove the remaining obligations. Establish `e : U v - U (prj V v) = U (v - prj V v)` using `(map_sub U _ _).symm`. Rewrite using `[e, ← U.apply_symm_apply w, U.inner_map_map]`.

Conclude with `a3 v _ (h2 w ((hm _).1 hw))`.
-/
private theorem commute_of_stable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : Submodule ℂ H) (hV : IsClosed (V : Set H)) (U : H ≃ₗᵢ[ℂ] H) (h1 : ∀ v ∈ V, U v ∈ V)
    (h2 : ∀ v ∈ V, U.symm v ∈ V) : Commute (U : H →L[ℂ] H) (prj V) := by
  have hc : V.topologicalClosure = V := hV.submodule_topologicalClosure_eq
  have hm : ∀ v, v ∈ V.topologicalClosure ↔ v ∈ V := fun v => by rw [hc]
  have a1 : ∀ v, prj V v ∈ V := fun v => (hm _).1 (Submodule.starProjection_apply_mem _ v)
  have a3 : ∀ v, ∀ w ∈ V, inner ℂ (v - prj V v) w = 0 := fun v w hw =>
    Submodule.starProjection_inner_eq_zero v w ((hm _).2 hw)
  refine ContinuousLinearMap.ext fun v => ?_
  change U (prj V v) = prj V (U v)
  symm
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ((hm _).2 (h1 _ (a1 v))) fun w hw => ?_
  have e : U v - U (prj V v) = U (v - prj V v) := (map_sub U _ _).symm
  rw [e, ← U.apply_symm_apply w, U.inner_map_map]
  exact a3 v _ (h2 w ((hm _).1 hw))

/- English proof (translation)
Take `⟨U, hU, -, -⟩` from `UpperTheory.ConvolutionTheory.C.twistUnitary E n μ θ`. Establish `hUa : ∀ v, θ.U v = U v` using `fun v => by rw [← hU]; rfl`. Establish `hmem : ∀ f, f ∈ (⨅ (w : Pl E) (_ : w.under (𝓞 F) ∉ P), eigL μ w (T.J w) (T.χ w)) ↔ ∀ w : Pl E, w.under (𝓞 F) ∉ P → f ∈ eigL μ w (T.J w) (T.χ w)` using `fun f => by`. Simplify using `only [Submodule.mem_iInf]`. Establish `hcl : IsClosed ((⨅ (w : Pl E) (_ : w.under (𝓞 F) ∉ P), eigL μ w (T.J w) (T.χ w) : Submodule ℂ (LL μ)) : Set (LL μ))`.

Establish `e : ((⨅ (w : Pl E) (_ : w.under (𝓞 F) ∉ P), eigL μ w (T.J w) (T.χ w) : Submodule ℂ (LL μ)) : Set (LL μ)) = ⋂ (w : Pl E) (_ : w.under (𝓞 F) ∉ P), (eigL μ w (T.J w) (T.χ w) : Set (LL μ))`. Use extensionality with `f`. Simplify using `only [SetLike.mem_coe, hmem, Set.mem_iInter]`. Rewrite using `[e]`. Conclude with `isClosed_iInter fun w => isClosed_iInter fun _ => (UpperTheory.ConvolutionTheory.L1.eigBasic E n μ w (T.J w) (T.χ w) (T.co w) (T.chr w)).1`.

Establish `hint : ∀ x x' : AdelicGLn.FiniteAdelicGL E n, mapGL n (galAd σ) (finEmb E n x) = finEmb E n x' → ∀ f, θ.U (rhoF μ x f) = rhoF μ x' (θ.U f)` using `fun x x' h f => by`. Express the relevant statement in the definitionally equal form `θ.U (rightRegularRep (rationalGLOne E n) μ (MultiplicityOne.finProj E n x) f) = rightRegularRep (rationalGLOne E n) μ (MultiplicityOne.finProj E n x') (θ.U f)`. Rewrite using `[(UpperTheory.ConvolutionTheory.Dp.twUnitary E n μ θ).2.2, e_finProj hσ hθ h]`. Establish `hfw : ∀ f ∈ (⨅ (w : Pl E) (_ : w.under (𝓞 F) ∉ P), eigL μ w (T.J w) (T.χ w)), U f ∈ (⨅ (w : Pl E) (_ : w.under (𝓞 F) ∉ P), eigL μ w (T.J w) (T.χ w))`. Introduce `f hf`.

Rewrite using `[hmem]`. Introduce `w hw`. Rewrite using `[mem_eigL]`. Introduce `y hy`. Set `u₀ : PlacesOver E (w.under (𝓞 F))` to `⟨w, inferInstance⟩`.

Establish `hfv : ∀ u : PlacesOver E (w.under (𝓞 F)), f ∈ eigL μ u.1 (T.J u.1) (T.χ u.1)` using `fun u => (hmem f).1 hf u.1 (by rw [under_eq]; exact hw)`. Take `⟨Z, hZ, hZY, hχ⟩` from `exists_pre T _ (single_mem T u₀ hy)`. Establish `e1 : rhoL μ w y (U f) = rhoF μ (pt (UpperTheory.ConvolutionTheory.T4.pE E n (w.under (𝓞 F)) (finEmb E n (AdelicGLn.localEmbedding w y)))) (U f)`. Rewrite using `[pt_local u₀ y]`. Both sides reduce to the same expression.

Rewrite using `[e1, ← hZY, ← hUa, ← hint _ _ (gal_pt σ Z), pt_eig μ T Z f hZ hfv, map_smul, hχ]`. Conclude with `congrArg (· • θ.U f) (chi_single T u₀ y)`. Establish `hbw : ∀ f ∈ (⨅ (w : Pl E) (_ : w.under (𝓞 F) ∉ P), eigL μ w (T.J w) (T.χ w)), U.symm f ∈ (⨅ (w : Pl E) (_ : w.under (𝓞 F) ∉ P), eigL μ w (T.J w) (T.χ w))`. Introduce `f hf`. Establish `hg : θ.U (U.symm f) = f` using `by rw [hUa, U.apply_symm_apply]`.

Rewrite using `[hmem]`. Introduce `w hw`. Rewrite using `[mem_eigL]`. Introduce `y hy`. Set `u₀ : PlacesOver E (w.under (𝓞 F))` to `⟨w, inferInstance⟩`.

Establish `hfv : ∀ u : PlacesOver E (w.under (𝓞 F)), f ∈ eigL μ u.1 (T.J u.1) (T.χ u.1)` using `fun u => (hmem f).1 hf u.1 (by rw [under_eq]; exact hw)`. Take `⟨h1, h2⟩` from `T.stable _ _ (single_mem T u₀ hy)`. Establish `e1 : rhoL μ w y (U.symm f) = rhoF μ (pt (UpperTheory.ConvolutionTheory.T4.pE E n (w.under (𝓞 F)) (finEmb E n (AdelicGLn.localEmbedding w y)))) (U.symm f)`. Rewrite using `[pt_local u₀ y]`. Both sides reduce to the same expression.

Establish `e2 : θ.U (rhoL μ w y (U.symm f)) = θ.U (T.χ w y • U.symm f)`. Rewrite using `[e1, hint _ _ (gal_pt σ _), hg, pt_eig μ T _ f h1 hfv, map_smul, hg]`. Conclude with `congrArg (· • f) (h2.trans (chi_single T u₀ y))`. Rewrite `e2` using `[hUa, hUa]`. Conclude with `U.injective e2`.

Establish `h` using `commute_of_stable _ hcl U hfw hbw`. Rewrite `h` using `[hU]`. Then use the resulting hypothesis.
-/
private theorem clause3 [IsGalois F E] (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure]
    (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) {θ : Twist μ} (hθ : IsGalTwist σ θ) (T : Ty σ n q w₀) (P : Set (Pl F)) :
    Commute θ.U (prj (⨅ (w : Pl E) (_ : w.under (𝓞 F) ∉ P), eigL μ w (T.J w) (T.χ w))) := by
  obtain ⟨U, hU, -, -⟩ := UpperTheory.ConvolutionTheory.C.twistUnitary E n μ θ
  have hUa : ∀ v, θ.U v = U v := fun v => by rw [← hU]; rfl
  have hmem : ∀ f, f ∈ (⨅ (w : Pl E) (_ : w.under (𝓞 F) ∉ P), eigL μ w (T.J w) (T.χ w)) ↔
      ∀ w : Pl E, w.under (𝓞 F) ∉ P → f ∈ eigL μ w (T.J w) (T.χ w) := fun f => by
    simp only [Submodule.mem_iInf]
  have hcl : IsClosed ((⨅ (w : Pl E) (_ : w.under (𝓞 F) ∉ P), eigL μ w (T.J w) (T.χ w) : Submodule ℂ (LL μ)) :
      Set (LL μ)) := by
    have e : ((⨅ (w : Pl E) (_ : w.under (𝓞 F) ∉ P), eigL μ w (T.J w) (T.χ w) : Submodule ℂ (LL μ)) : Set (LL μ)) =
        ⋂ (w : Pl E) (_ : w.under (𝓞 F) ∉ P), (eigL μ w (T.J w) (T.χ w) : Set (LL μ)) := by
      ext f
      simp only [SetLike.mem_coe, hmem, Set.mem_iInter]
    rw [e]
    exact isClosed_iInter fun w => isClosed_iInter fun _ =>
      (UpperTheory.ConvolutionTheory.L1.eigBasic E n μ w (T.J w) (T.χ w) (T.co w) (T.chr w)).1
  have hint : ∀ x x' : AdelicGLn.FiniteAdelicGL E n, mapGL n (galAd σ) (finEmb E n x) = finEmb E n x' →
      ∀ f, θ.U (rhoF μ x f) = rhoF μ x' (θ.U f) := fun x x' h f => by
    change θ.U (rightRegularRep (rationalGLOne E n) μ (MultiplicityOne.finProj E n x) f) =
      rightRegularRep (rationalGLOne E n) μ (MultiplicityOne.finProj E n x') (θ.U f)
    rw [(UpperTheory.ConvolutionTheory.Dp.twUnitary E n μ θ).2.2, e_finProj hσ hθ h]
  have hfw : ∀ f ∈ (⨅ (w : Pl E) (_ : w.under (𝓞 F) ∉ P), eigL μ w (T.J w) (T.χ w)), U f ∈
      (⨅ (w : Pl E) (_ : w.under (𝓞 F) ∉ P), eigL μ w (T.J w) (T.χ w)) := by
    intro f hf
    rw [hmem]
    intro w hw
    rw [mem_eigL]
    intro y hy
    let u₀ : PlacesOver E (w.under (𝓞 F)) := ⟨w, inferInstance⟩
    have hfv : ∀ u : PlacesOver E (w.under (𝓞 F)), f ∈ eigL μ u.1 (T.J u.1) (T.χ u.1) := fun u =>
      (hmem f).1 hf u.1 (by rw [under_eq]; exact hw)
    obtain ⟨Z, hZ, hZY, hχ⟩ := exists_pre T _ (single_mem T u₀ hy)
    have e1 : rhoL μ w y (U f) = rhoF μ (pt (UpperTheory.ConvolutionTheory.T4.pE E n (w.under (𝓞 F))
        (finEmb E n (AdelicGLn.localEmbedding w y)))) (U f) := by
      rw [pt_local u₀ y]
      rfl
    rw [e1, ← hZY, ← hUa, ← hint _ _ (gal_pt σ Z), pt_eig μ T Z f hZ hfv, map_smul, hχ]
    exact congrArg (· • θ.U f) (chi_single T u₀ y)
  have hbw : ∀ f ∈ (⨅ (w : Pl E) (_ : w.under (𝓞 F) ∉ P), eigL μ w (T.J w) (T.χ w)), U.symm f ∈
      (⨅ (w : Pl E) (_ : w.under (𝓞 F) ∉ P), eigL μ w (T.J w) (T.χ w)) := by
    intro f hf
    have hg : θ.U (U.symm f) = f := by rw [hUa, U.apply_symm_apply]
    rw [hmem]
    intro w hw
    rw [mem_eigL]
    intro y hy
    let u₀ : PlacesOver E (w.under (𝓞 F)) := ⟨w, inferInstance⟩
    have hfv : ∀ u : PlacesOver E (w.under (𝓞 F)), f ∈ eigL μ u.1 (T.J u.1) (T.χ u.1) := fun u =>
      (hmem f).1 hf u.1 (by rw [under_eq]; exact hw)
    obtain ⟨h1, h2⟩ := T.stable _ _ (single_mem T u₀ hy)
    have e1 : rhoL μ w y (U.symm f) = rhoF μ (pt (UpperTheory.ConvolutionTheory.T4.pE E n (w.under (𝓞 F))
        (finEmb E n (AdelicGLn.localEmbedding w y)))) (U.symm f) := by
      rw [pt_local u₀ y]
      rfl
    have e2 : θ.U (rhoL μ w y (U.symm f)) = θ.U (T.χ w y • U.symm f) := by
      rw [e1, hint _ _ (gal_pt σ _), hg, pt_eig μ T _ f h1 hfv, map_smul, hg]
      exact congrArg (· • f) (h2.trans (chi_single T u₀ y))
    rw [hUa, hUa] at e2
    exact U.injective e2
  have h := commute_of_stable _ hcl U hfw hbw
  rwa [hU] at h

end Commute

end TwB
end UpperTheory.ConvolutionTheory.L1

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ σ hσ m n μ _ θ hθ`. Conclude with `⟨fun D s hs i g v => UpperTheory.ConvolutionTheory.L1.clause1 hσ hθ D hs i g v, fun p D w hw i g v => UpperTheory.ConvolutionTheory.L1.clause2 hσ hθ p D w hw i g v, fun q w₀ T P => UpperTheory.ConvolutionTheory.L1.clause3 μ hσ hθ T P⟩`.
-/
theorem UpperTheory.ConvolutionTheory.L1.twistPerm :
    UpperTheory.ConvolutionTheory.L1.TwistPerm := by
  intro F E _ _ _ _ _ _ σ hσ m n μ _ θ hθ
  exact ⟨fun D s hs i g v => UpperTheory.ConvolutionTheory.L1.clause1 hσ hθ D hs i g v,
    fun p D w hw i g v => UpperTheory.ConvolutionTheory.L1.clause2 hσ hθ p D w hw i g v,
    fun q w₀ T P => UpperTheory.ConvolutionTheory.L1.clause3 μ hσ hθ T P⟩
