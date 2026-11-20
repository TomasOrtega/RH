import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SelmerRankBoundLaurent
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction PositivityTheory.Rg.Tf.Core Topology GroundTheory.Global.AdeleBaseChange

/- English proof (translation)
Rewrite using `[Subgroup.mem_centralizer_singleton_iff, ← h]`. Conclude with `congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 t.2)`.
-/
private theorem mem_TA {K : Type} [Field K] [NumberField K] {n : ℕ} {γ : GL (Fin n) K} {γ₁ : G1 K n}
    (h : (γ₁ : GA K n) = AdelicGLn.diagonal K n γ) (t : Subgroup.centralizer {γ₁}) :
    ((t : G1 K n) : GA K n) ∈ TA γ := by
  rw [Subgroup.mem_centralizer_singleton_iff, ← h]
  exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 t.2)

private noncomputable def cenIn {K : Type} [Field K] [NumberField K] {n : ℕ} {γ : GL (Fin n) K} {γ₁ : G1 K n}
    (h : (γ₁ : GA K n) = AdelicGLn.diagonal K n γ) : Subgroup.centralizer {γ₁} →* TA γ where
  toFun t := ⟨((t : G1 K n) : GA K n), mem_TA h t⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/- English proof (translation)
Rewrite using `[Subgroup.mem_centralizer_singleton_iff]`. Conclude with `centralSection_mul_comm s _`.
-/
private theorem cs_mem_TA {K : Type} [Field K] [NumberField K] {n : ℕ} (γ : GL (Fin n) K)
    (s : {r : ℝ // 0 < r}) : centralSection K n s ∈ TA γ := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact centralSection_mul_comm s _

/- English proof (translation)
Establish `: (Subgroup.centralizer {γ₁} : Set (G1 K n)) = {x | x * γ₁ = γ₁ * x}`. Use extensionality with `x`. Conclude with `Subgroup.mem_centralizer_singleton_iff`. Rewrite using `[this]`. Conclude with `isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)`.
-/
private theorem isClosed_cen {K : Type} [Field K] [NumberField K] {n : ℕ} (γ₁ : G1 K n) :
    IsClosed (Subgroup.centralizer {γ₁} : Set (G1 K n)) := by
  have : (Subgroup.centralizer {γ₁} : Set (G1 K n)) = {x | x * γ₁ = γ₁ * x} := by
    ext x
    exact Subgroup.mem_centralizer_singleton_iff
  rw [this]
  exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)

/- English proof (translation)
Introduce `hS hN hC F E _ _ _ _ _ _ σ hσ n hn`. Take `⟨hcl, hmod, -⟩` from `hN F E σ hσ n hn`. Establish `hl : 0 < Module.finrank F E` using `Module.finrank_pos`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Take `⟨e, he⟩` from `hS (G1 E n) {r : ℝ // 0 < r} (GA E n) (normOneGL E n).subtype ((rpowHom ((Module.finrank F E : ℝ))⁻¹).comp (detModule E n)) ((mapGL n (adeleMap F E)).comp (centralSection F n)) IsEmbedding.subtypeVal ((continuous_rpowHom _).comp continuous_detModule) (hcl.continuous.comp continuo …`.

Use `Subtype.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((detModule E n (mapGL n (adeleMap F E) (centralSection F n s)) : ℝ)) ^ ((Module.finrank F E : ℝ))⁻¹ = s.1`. Rewrite using `[hmod, detModule_centralSection hn]`. Conclude with `Real.pow_rpow_inv_natCast s.2.le hl.ne')`. Use the proof step `(fun s g => by`.

Express the relevant statement in the definitionally equal form `mapGL n (adeleMap F E) (centralSection F n s) * g = g * mapGL n (adeleMap F E) (centralSection F n s)`. Rewrite using `[hC F E n s]`. Conclude with `centralSection_mul_comm _ g)`. Use the proof step `(fun g => by`. Prove the components needed by the constructor for the conclusion.

Introduce `hg`. Establish `h1 : ((detModule E n g : ℝ)) ^ ((Module.finrank F E : ℝ))⁻¹ = 1` using `congrArg Subtype.val hg`. Establish `h2 : (detModule E n g : ℝ) = 1`. Establish `h3` using `Real.rpow_inv_natCast_pow (detModule E n g).2.le hl.ne'`. Rewrite `h3` using `[h1, one_pow]`.

Conclude with `h3.symm`. Conclude with `⟨⟨g, mem_normOneGL_iff_detModule.2 (Subtype.ext h2)⟩, rfl⟩`. Introduce and unpack `⟨x, rfl⟩`. Establish `h1 : detModule E n (x : GA E n) = 1` using `mem_normOneGL_iff_detModule.1 x.2`. Express the relevant statement in the definitionally equal form `rpowHom _ (detModule E n (x : GA E n)) = 1`.

Rewrite using `[h1, map_one])`. Conclude with `⟨e, he⟩`. Introduce `γ γ₁ h`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Take `⟨e, he⟩` from `hS (Subgroup.centralizer {γ₁}) {r : ℝ // 0 < r} (TA γ) (cenIn h) ((detModule F n).comp (TA γ).subtype) ((centralSection F n).codRestrict (TA γ) (cs_mem_TA γ)) ((IsEmbedding.of_comp_iff (IsEmbedding.subtypeVal : IsEmbedding (Subtype.val : TA γ → GA F n))).1 (show IsEmbedding ((Sub …`.

Prove the components needed by the constructor for the conclusion. Introduce `hg`. Establish `h1 : (g : GA F n) ∈ normOneGL F n` using `mem_normOneGL_iff_detModule.2 hg`. Use `⟨⟨⟨g, h1⟩, ?_⟩, rfl⟩` and prove the remaining obligations. Rewrite using `[Subgroup.mem_centralizer_singleton_iff]`.

Use `Subtype.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(g : GA F n) * (γ₁ : GA F n) = (γ₁ : GA F n) * g`. Rewrite using `[h]`. Conclude with `Subgroup.mem_centralizer_singleton_iff.1 g.2`. Introduce and unpack `⟨x, rfl⟩`.

Conclude with `mem_normOneGL_iff_detModule.1 x.1.2)`. Conclude with `⟨e, fun x => congrArg Subtype.val (he x)⟩`. Establish `hmem : ∀ t : Subgroup.centralizer {γ₁}, mapGL n (adeleMap F E) ((t : G1 F n) : GA F n) ∈ normOneGL E n` using `fun t => by`. Use `mem_normOneGL_iff_detModule.2 (Subtype.ext ?_)` and prove the remaining obligations. Rewrite using `[hmod, mem_normOneGL_iff_detModule.1 (t : G1 F n).2]`.

Simplify using the standard rewrite rules. Set `j : Subgroup.centralizer {γ₁} →* G1 E n` to `{ toFun := fun t => ⟨mapGL n (adeleMap F E) ((t : G1 F n) : GA F n), hmem t⟩ map_one' := Subtype.ext (map_one _) map_mul' := fun a b => Subtype.ext (map_mul _ _ _) }`. Use `⟨j, ?_, fun t => rfl⟩` and prove the remaining obligations. Establish `hE : IsClosedEmbedding (Subtype.val : G1 E n → GA E n)` using `isClosed_normOneGL.isClosedEmbedding_subtypeVal`. Establish `hF : IsClosedEmbedding (Subtype.val : G1 F n → GA F n)` using `isClosed_normOneGL.isClosedEmbedding_subtypeVal`.

Establish `hT : IsClosedEmbedding (Subtype.val : Subgroup.centralizer {γ₁} → G1 F n)` using `(isClosed_cen γ₁).isClosedEmbedding_subtypeVal`. Conclude with `(IsClosedEmbedding.of_comp_iff hE).1 (hcl.comp (hF.comp hT))`.
-/
theorem UpperTheory.splitCentralizer_of_splitEquiv :
    SplitEquiv → N5 → CentBC → Spl := by
  intro hS hN hC F E _ _ _ _ _ _ σ hσ n hn
  obtain ⟨hcl, hmod, -⟩ := hN F E σ hσ n hn
  have hl : 0 < Module.finrank F E := Module.finrank_pos
  refine ⟨?_, ?_⟩
  · obtain ⟨e, he⟩ := hS (G1 E n) {r : ℝ // 0 < r} (GA E n) (normOneGL E n).subtype
      ((rpowHom ((Module.finrank F E : ℝ))⁻¹).comp (detModule E n))
      ((mapGL n (adeleMap F E)).comp (centralSection F n))
      IsEmbedding.subtypeVal
      ((continuous_rpowHom _).comp continuous_detModule)
      (hcl.continuous.comp continuous_centralSection)
      (fun s => by
        refine Subtype.ext ?_
        change ((detModule E n (mapGL n (adeleMap F E) (centralSection F n s)) : ℝ)) ^
          ((Module.finrank F E : ℝ))⁻¹ = s.1
        rw [hmod, detModule_centralSection hn]
        exact Real.pow_rpow_inv_natCast s.2.le hl.ne')
      (fun s g => by
        change mapGL n (adeleMap F E) (centralSection F n s) * g = g * mapGL n (adeleMap F E) (centralSection F n s)
        rw [hC F E n s]
        exact centralSection_mul_comm _ g)
      (fun g => by
        constructor
        · intro hg
          have h1 : ((detModule E n g : ℝ)) ^ ((Module.finrank F E : ℝ))⁻¹ = 1 := congrArg Subtype.val hg
          have h2 : (detModule E n g : ℝ) = 1 := by
            have h3 := Real.rpow_inv_natCast_pow (detModule E n g).2.le hl.ne'
            rw [h1, one_pow] at h3
            exact h3.symm
          exact ⟨⟨g, mem_normOneGL_iff_detModule.2 (Subtype.ext h2)⟩, rfl⟩
        · rintro ⟨x, rfl⟩
          have h1 : detModule E n (x : GA E n) = 1 := mem_normOneGL_iff_detModule.1 x.2
          change rpowHom _ (detModule E n (x : GA E n)) = 1
          rw [h1, map_one])
    exact ⟨e, he⟩
  · intro γ γ₁ h
    refine ⟨?_, ?_⟩
    · obtain ⟨e, he⟩ := hS (Subgroup.centralizer {γ₁}) {r : ℝ // 0 < r} (TA γ) (cenIn h)
        ((detModule F n).comp (TA γ).subtype)
        ((centralSection F n).codRestrict (TA γ) (cs_mem_TA γ))
        ((IsEmbedding.of_comp_iff (IsEmbedding.subtypeVal : IsEmbedding (Subtype.val : TA γ → GA F n))).1
          (show IsEmbedding ((Subtype.val : G1 F n → GA F n) ∘ (Subtype.val : Subgroup.centralizer {γ₁} → G1 F n)) from
            IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal))
        (continuous_detModule.comp continuous_subtype_val)
        (continuous_centralSection.subtype_mk _)
        (fun s => detModule_centralSection hn s)
        (fun s g => Subtype.ext (centralSection_mul_comm s _))
        (fun g => by
          constructor
          · intro hg
            have h1 : (g : GA F n) ∈ normOneGL F n := mem_normOneGL_iff_detModule.2 hg
            refine ⟨⟨⟨g, h1⟩, ?_⟩, rfl⟩
            rw [Subgroup.mem_centralizer_singleton_iff]
            refine Subtype.ext ?_
            change (g : GA F n) * (γ₁ : GA F n) = (γ₁ : GA F n) * g
            rw [h]
            exact Subgroup.mem_centralizer_singleton_iff.1 g.2
          · rintro ⟨x, rfl⟩
            exact mem_normOneGL_iff_detModule.1 x.1.2)
      exact ⟨e, fun x => congrArg Subtype.val (he x)⟩
    · have hmem : ∀ t : Subgroup.centralizer {γ₁},
          mapGL n (adeleMap F E) ((t : G1 F n) : GA F n) ∈ normOneGL E n := fun t => by
        refine mem_normOneGL_iff_detModule.2 (Subtype.ext ?_)
        rw [hmod, mem_normOneGL_iff_detModule.1 (t : G1 F n).2]
        simp
      let j : Subgroup.centralizer {γ₁} →* G1 E n :=
        { toFun := fun t => ⟨mapGL n (adeleMap F E) ((t : G1 F n) : GA F n), hmem t⟩
          map_one' := Subtype.ext (map_one _)
          map_mul' := fun a b => Subtype.ext (map_mul _ _ _) }
      refine ⟨j, ?_, fun t => rfl⟩
      have hE : IsClosedEmbedding (Subtype.val : G1 E n → GA E n) :=
        isClosed_normOneGL.isClosedEmbedding_subtypeVal
      have hF : IsClosedEmbedding (Subtype.val : G1 F n → GA F n) :=
        isClosed_normOneGL.isClosedEmbedding_subtypeVal
      have hT : IsClosedEmbedding (Subtype.val : Subgroup.centralizer {γ₁} → G1 F n) :=
        (isClosed_cen γ₁).isClosedEmbedding_subtypeVal
      exact (IsClosedEmbedding.of_comp_iff hE).1 (hcl.comp (hF.comp hT))
