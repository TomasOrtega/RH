import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.RightOnto
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdel

noncomputable section

namespace PositivityTheory.KCo

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.EmbChart

/- English proof (translation)
Use `set S : Set (κ → Fv F v) := {x | ∀ i, x i ∈ v.adicCompletionIntegers F} with hSdef`. Establish `hOv : IsOpen ((v.adicCompletionIntegers F : Set (Fv F v)))` using `Valued.isOpen_integer _`. Establish `hCv : IsCompact ((v.adicCompletionIntegers F : Set (Fv F v)))` using `by haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v`. Conclude with `isCompact_iff_compactSpace.mpr inferInstance`. Establish `hSeq : S = Set.pi Set.univ (fun _ : κ => (v.adicCompletionIntegers F : Set (Fv F v)))`.

Use extensionality with `x`. Simplify using `[hSdef]`. Establish `hO : IsOpen S`. Rewrite using `[hSeq]`. Conclude with `isOpen_set_pi Set.finite_univ (fun _ _ => hOv)`.

Establish `hC : IsCompact S`. Rewrite using `[hSeq]`. Conclude with `isCompact_univ_pi (fun _ => hCv)`. Establish `hCl : IsClosed S` using `hC.isClosed`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`. Distinguish the cases in `hx : x ∈ S`. Use `filter_upwards [hO.mem_nhds hx] with y hy`. Rewrite using `[Set.indicator_of_mem hy, Set.indicator_of_mem hx]`.

Both sides reduce to the same expression. Use `filter_upwards [hCl.isOpen_compl.mem_nhds hx] with y hy`. Rewrite using `[Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]`. Conclude with `HasCompactSupport.intro hC (fun x hx => Set.indicator_of_notMem hx _)`.
-/
theorem std_mem_SB {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl F) :
    Set.indicator {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} (1 : (κ → Fv F v) → ℂ) ∈ SB (κ → Fv F v) := by
  set S : Set (κ → Fv F v) := {x | ∀ i, x i ∈ v.adicCompletionIntegers F} with hSdef
  have hOv : IsOpen ((v.adicCompletionIntegers F : Set (Fv F v))) := Valued.isOpen_integer _
  have hCv : IsCompact ((v.adicCompletionIntegers F : Set (Fv F v))) := by
    haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
    exact isCompact_iff_compactSpace.mpr inferInstance
  have hSeq : S = Set.pi Set.univ (fun _ : κ => (v.adicCompletionIntegers F : Set (Fv F v))) := by
    ext x
    simp [hSdef]
  have hO : IsOpen S := by
    rw [hSeq]
    exact isOpen_set_pi Set.finite_univ (fun _ _ => hOv)
  have hC : IsCompact S := by
    rw [hSeq]
    exact isCompact_univ_pi (fun _ => hCv)
  have hCl : IsClosed S := hC.isClosed
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ S
    · filter_upwards [hO.mem_nhds hx] with y hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
      rfl
    · filter_upwards [hCl.isOpen_compl.mem_nhds hx] with y hy
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
  · exact HasCompactSupport.intro hC (fun x hx => Set.indicator_of_notMem hx _)

/- English proof (translation)
Set `b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F)` to `⟨1, 2, one_pos, one_lt_two⟩`. Establish `h1 : HasCompactSupport fun x => ((b x : ℝ) : ℂ)` using `b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)`. Establish `h2 : ContDiff ℝ (⊤ : ℕ∞) fun x => ((b x : ℝ) : ℂ)` using `Complex.ofRealCLM.contDiff.comp b.contDiff`. Use `⟨h1.toSchwartzMap h2, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((b 0 : ℝ) : ℂ) = 1`.

Rewrite using `[b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]`. Simplify using the standard rewrite rules.
-/
theorem exists_sinf (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] : ∃ f : SInf F κ, f 0 = 1 := by
  classical
  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport fun x => ((b x : ℝ) : ℂ) := b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have h2 : ContDiff ℝ (⊤ : ℕ∞) fun x => ((b x : ℝ) : ℂ) := Complex.ofRealCLM.contDiff.comp b.contDiff
  refine ⟨h1.toSchwartzMap h2, ?_⟩
  change ((b 0 : ℝ) : ℂ) = 1
  rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]
  simp

/- English proof (translation)
The claim follows from `have hg : (fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => evalV F v (y i)) ∈ SB _ := ⟨isLocallyConstant_finprod_evalV φ hSB hstd, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hSB hstd⟩ Submodule.subset_span ⟨f, _, hg, rfl⟩`.
-/
theorem pure_mem_schA {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : SInf F κ)
    (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (hSB : ∀ v, φ v ∈ SB _)
    (hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ schA F κ :=
  have hg : (fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => evalV F v (y i)) ∈ SB _ :=
    ⟨isLocallyConstant_finprod_evalV φ hSB hstd, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hSB hstd⟩
  Submodule.subset_span ⟨f, _, hg, rfl⟩

/- English proof (translation)
Unfold `ActsUniq`. Introduce `F _ _ κ _ v T φ hφ φ₁ φ₂ h₁ h₂`. Use `set std : ∀ w : Pl F, (κ → Fv F w) → ℂ := fun w => Set.indicator {x : κ → Fv F w | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 with hstd_def`. Take `⟨f, hf⟩` from `exists_sinf F κ`. Use `set ψ : ∀ w : Pl F, (κ → Fv F w) → ℂ := Function.update std v (fun _ => 1) with hψ`.

Use `set r : (κ → AF F) → ℂ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f ψ with hr`. Establish `hstd_ev : ∀ᶠ w in Filter.cofinite, std w = Set.indicator {x : κ → Fv F w | ∀ i, x i ∈ w.adicCompletionIntegers F} 1` using `Filter.Eventually.of_forall (fun w => rfl)`. Establish `htens : tens (evFin F v) φ r = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update std v φ)`. Use function extensionality and compare the values at `x`. Simplify using `only [tens, hr, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, hψ]`.

Rewrite using `[GlobalTheory.PureFactor.finprod_update std v φ hstd_ev x]`. Expand and normalize the polynomial expressions, which then agree. Establish `hRest : Rest (evFin F v) φ r`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `x z hz`.

Set `e : FiniteAdeleRing (𝓞 F) F` to `RestrictedProduct.mk (Function.update (fun w : Pl F => (1 : Fv F w)) v 0) (by filter_upwards [Filter.eventually_cofinite_ne v] with w hw`. Rewrite using `[Function.update_of_ne hw]`. Conclude with `(HeightOneSpectrum.adicCompletionIntegers F w).one_mem)`. Set `u : AF F` to `((1 : InfiniteAdeleRing F), e)`. Establish `hu : evFin F v u = 0` using `by show Function.update (fun w : Pl F => (1 : Fv F w)) v 0 v = 0`.

Rewrite using `[Function.update_self]`. Establish `huz` using `hz u hu`. Establish `hz_inf : ∀ i, (z i).1 = 0`. Introduce `i`. Establish `h` using `congrFun huz i`.

Rewrite `h` using `[Pi.smul_apply, smul_eq_mul, Pi.zero_apply]`. Establish `h'` using `congrArg Prod.fst h`. Express the relevant statement in the definitionally equal form `(1 : InfiniteAdeleRing F) * (z i).1 = 0 at h'`. Rewrite `h'` using `[one_mul]`. Then use the resulting hypothesis. Establish `hz_fin : ∀ w, w ≠ v → ∀ i, evFin F w (z i) = 0`.

Introduce `w hw i`. Establish `h` using `congrArg (evFin F w) (congrFun huz i)`. Establish `hew : evFin F w u = 1` using `by show Function.update (fun w : Pl F => (1 : Fv F w)) v 0 w = 1`. Rewrite using `[Function.update_of_ne hw]`. Rewrite `h` using `[Pi.smul_apply, smul_eq_mul, map_mul, hew, one_mul, Pi.zero_apply, map_zero]`.

Conclude with `h`. Establish `hI : ∀ i, evI F ((x + z) i) = evI F (x i)`. Introduce `i`. Express the relevant statement in the definitionally equal form `InfiniteAdeleRing.ringEquiv_mixedSpace F ((x i).1 + (z i).1) = InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1`. Rewrite using `[hz_inf i, add_zero]`.

Establish `hP : ∀ w, ψ w (fun i => evFin F w ((x + z) i)) = ψ w (fun i => evFin F w (x i))`. Introduce `w`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Simplify using `[hψ]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[Pi.add_apply, map_add, hz_fin w hw i, add_zero]`. Use `show f (fun i => evI F ((x + z) i)) * ∏ᶠ w, ψ w (fun i => evFin F w ((x + z) i)) = f (fun i => evI F (x i)) * ∏ᶠ w, ψ w (fun i => evFin F w (x i))`. Rewrite using `[finprod_congr hP]`.

Use `congr 2`. Use function extensionality and compare the values at `i`. Conclude with `hI i`. Rewrite using `[htens]`. Apply `pure_mem_schA f` to reduce the goal to its premises.

Introduce `w`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Simplify using `using hφ`. Rewrite using `[Function.update_of_ne hw]`.

Conclude with `std_mem_SB w`. Use `filter_upwards [Filter.eventually_cofinite_ne v] with w hw`. Rewrite using `[Function.update_of_ne hw]`. Establish `heq : tens (evFin F v) φ₁ r = tens (evFin F v) φ₂ r` using `(h₁ r hRest).symm.trans (h₂ r hRest)`. Use function extensionality and compare the values at `y`.

Set `s : κ → AF F` to `fun i => ((0 : InfiniteAdeleRing F), RestrictedProduct.mk (Function.update (fun w : Pl F => (0 : Fv F w)) v (y i)) (by filter_upwards [Filter.eventually_cofinite_ne v] with w hw`. Rewrite using `[Function.update_of_ne hw]`. Conclude with `(HeightOneSpectrum.adicCompletionIntegers F w).zero_mem))`. Establish `hs : (fun i => evFin F v (s i)) = y`. Use function extensionality and compare the values at `i`.

Use `show Function.update (fun w : Pl F => (0 : Fv F w)) v (y i) v = y i`. Rewrite using `[Function.update_self]`. Establish `hrs : r s = 1` using `by show f (fun i => evI F (s i)) * ∏ᶠ w, ψ w (fun i => evFin F w (s i)) = 1`. Establish `h0 : (fun i => evI F (s i)) = 0`. Use function extensionality and compare the values at `i`.

Use `show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0`. Conclude with `map_zero _`. Establish `h1 : ∀ w, ψ w (fun i => evFin F w (s i)) = 1`. Introduce `w`. Distinguish the cases in `hw : w = v`.

Substitute `hw` using the available equality. Simplify using `[hψ]`. Rewrite using `[hψ, Function.update_of_ne hw]`. Establish `h00 : (fun i => evFin F w (s i)) = 0`. Use function extensionality and compare the values at `i`.

Use `show Function.update (fun w : Pl F => (0 : Fv F w)) v (y i) w = 0`. Rewrite using `[Function.update_of_ne hw]`. Rewrite using `[h00, hstd_def]`. Simplify using the standard rewrite rules. Rewrite using `[h0, hf, finprod_congr h1, finprod_one, one_mul]`.

Establish `key` using `congrFun heq s`. Express the relevant statement in the definitionally equal form `φ₁ (fun i => evFin F v (s i)) * r s = φ₂ (fun i => evFin F v (s i)) * r s at key`. Rewrite `key` using `[hs, hrs, mul_one, mul_one]`. Conclude with `key`.
-/
theorem action_uniqueness : ActsUniq := by
  classical
  unfold ActsUniq
  intro F _ _ κ _ v T φ hφ φ₁ φ₂ h₁ h₂
  set std : ∀ w : Pl F, (κ → Fv F w) → ℂ :=
    fun w => Set.indicator {x : κ → Fv F w | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 with hstd_def
  obtain ⟨f, hf⟩ := exists_sinf F κ
  set ψ : ∀ w : Pl F, (κ → Fv F w) → ℂ := Function.update std v (fun _ => 1) with hψ
  set r : (κ → AF F) → ℂ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f ψ with hr
  have hstd_ev : ∀ᶠ w in Filter.cofinite,
      std w = Set.indicator {x : κ → Fv F w | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 :=
    Filter.Eventually.of_forall (fun w => rfl)
  have htens : tens (evFin F v) φ r = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update std v φ) := by
    funext x
    simp only [tens, hr, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, hψ]
    rw [GlobalTheory.PureFactor.finprod_update std v φ hstd_ev x]
    ring
  have hRest : Rest (evFin F v) φ r := by
    refine ⟨?_, ?_⟩
    · intro x z hz
      let e : FiniteAdeleRing (𝓞 F) F :=
        RestrictedProduct.mk (Function.update (fun w : Pl F => (1 : Fv F w)) v 0) (by
          filter_upwards [Filter.eventually_cofinite_ne v] with w hw
          rw [Function.update_of_ne hw]
          exact (HeightOneSpectrum.adicCompletionIntegers F w).one_mem)
      let u : AF F := ((1 : InfiniteAdeleRing F), e)
      have hu : evFin F v u = 0 := by
        show Function.update (fun w : Pl F => (1 : Fv F w)) v 0 v = 0
        rw [Function.update_self]
      have huz := hz u hu
      have hz_inf : ∀ i, (z i).1 = 0 := by
        intro i
        have h := congrFun huz i
        rw [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
        have h' := congrArg Prod.fst h
        change (1 : InfiniteAdeleRing F) * (z i).1 = 0 at h'
        rwa [one_mul] at h'
      have hz_fin : ∀ w, w ≠ v → ∀ i, evFin F w (z i) = 0 := by
        intro w hw i
        have h := congrArg (evFin F w) (congrFun huz i)
        have hew : evFin F w u = 1 := by
          show Function.update (fun w : Pl F => (1 : Fv F w)) v 0 w = 1
          rw [Function.update_of_ne hw]
        rw [Pi.smul_apply, smul_eq_mul, map_mul, hew, one_mul, Pi.zero_apply, map_zero] at h
        exact h
      have hI : ∀ i, evI F ((x + z) i) = evI F (x i) := by
        intro i
        change InfiniteAdeleRing.ringEquiv_mixedSpace F ((x i).1 + (z i).1) =
          InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1
        rw [hz_inf i, add_zero]
      have hP : ∀ w, ψ w (fun i => evFin F w ((x + z) i)) = ψ w (fun i => evFin F w (x i)) := by
        intro w
        by_cases hw : w = v
        · subst hw
          simp [hψ]
        · congr 1
          funext i
          rw [Pi.add_apply, map_add, hz_fin w hw i, add_zero]
      show f (fun i => evI F ((x + z) i)) * ∏ᶠ w, ψ w (fun i => evFin F w ((x + z) i)) =
        f (fun i => evI F (x i)) * ∏ᶠ w, ψ w (fun i => evFin F w (x i))
      rw [finprod_congr hP]
      congr 2
      funext i
      exact hI i
    · rw [htens]
      apply pure_mem_schA f
      · intro w
        by_cases hw : w = v
        · subst hw
          simpa using hφ
        · rw [Function.update_of_ne hw]
          exact std_mem_SB w
      · filter_upwards [Filter.eventually_cofinite_ne v] with w hw
        rw [Function.update_of_ne hw]
  have heq : tens (evFin F v) φ₁ r = tens (evFin F v) φ₂ r := (h₁ r hRest).symm.trans (h₂ r hRest)
  funext y
  let s : κ → AF F := fun i => ((0 : InfiniteAdeleRing F),
    RestrictedProduct.mk (Function.update (fun w : Pl F => (0 : Fv F w)) v (y i)) (by
      filter_upwards [Filter.eventually_cofinite_ne v] with w hw
      rw [Function.update_of_ne hw]
      exact (HeightOneSpectrum.adicCompletionIntegers F w).zero_mem))
  have hs : (fun i => evFin F v (s i)) = y := by
    funext i
    show Function.update (fun w : Pl F => (0 : Fv F w)) v (y i) v = y i
    rw [Function.update_self]
  have hrs : r s = 1 := by
    show f (fun i => evI F (s i)) * ∏ᶠ w, ψ w (fun i => evFin F w (s i)) = 1
    have h0 : (fun i => evI F (s i)) = 0 := by
      funext i
      show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
      exact map_zero _
    have h1 : ∀ w, ψ w (fun i => evFin F w (s i)) = 1 := by
      intro w
      by_cases hw : w = v
      · subst hw
        simp [hψ]
      · rw [hψ, Function.update_of_ne hw]
        have h00 : (fun i => evFin F w (s i)) = 0 := by
          funext i
          show Function.update (fun w : Pl F => (0 : Fv F w)) v (y i) w = 0
          rw [Function.update_of_ne hw]
        rw [h00, hstd_def]
        simp
    rw [h0, hf, finprod_congr h1, finprod_one, one_mul]
  have key := congrFun heq s
  change φ₁ (fun i => evFin F v (s i)) * r s = φ₂ (fun i => evFin F v (s i)) * r s at key
  rw [hs, hrs, mul_one, mul_one] at key
  exact key

end PositivityTheory.KCo
