import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianLatticeOpenCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharHalfTraceTensorLatticeHeisenbergCocycle

noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThK.Adapt

/- English proof (translation)
Apply the tactic sequence `let S : ((κ → R) × (κ → R)) →ₗ[R] (κ → R) × (κ → R) := { toFun := fun w => (fun k => w.1 ⬝ᵥ (T (0, Pi.single k 1)).2 - (T (0, Pi.single k 1)).1 ⬝ᵥ w.2, fun k => (T (Pi.single k 1, 0)).1 ⬝ᵥ w.2 - w.1 ⬝ᵥ (T (Pi.single k 1, 0)).2) map_add' := fun a b => by ext k <;> simp <;> ring ma …`. Establish `hS : Function.LeftInverse S T` using `fun u => by`. Use extensionality with `k`. Simplify `h u (0, Pi.single k 1)` using `[S]`. Simplify `h (Pi.single k 1, 0) u` using `[S]`.

Establish `hi : Function.Injective S` using `OrzechProperty.injective_of_surjective_endomorphism S hS.surjective`. Conclude with `⟨hS.injective, fun w => ⟨S w, hi (hS _)⟩⟩`.
-/
theorem bijective_of_symp {R κ : Type} [CommRing R] [Fintype κ] (T : ((κ → R) × (κ → R)) →ₗ[R] (κ → R) × (κ → R))
    (h : ∀ u w, (T u).1 ⬝ᵥ (T w).2 - (T w).1 ⬝ᵥ (T u).2 = u.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ u.2) : Function.Bijective T := by
  classical
  let S : ((κ → R) × (κ → R)) →ₗ[R] (κ → R) × (κ → R) :=
    { toFun := fun w => (fun k => w.1 ⬝ᵥ (T (0, Pi.single k 1)).2 - (T (0, Pi.single k 1)).1 ⬝ᵥ w.2,
        fun k => (T (Pi.single k 1, 0)).1 ⬝ᵥ w.2 - w.1 ⬝ᵥ (T (Pi.single k 1, 0)).2)
      map_add' := fun a b => by ext k <;> simp <;> ring
      map_smul' := fun c a => by ext k <;> simp <;> ring }
  have hS : Function.LeftInverse S T := fun u => by
    ext k
    · simpa [S] using h u (0, Pi.single k 1)
    · simpa [S] using h (Pi.single k 1, 0) u
  have hi : Function.Injective S := OrzechProperty.injective_of_surjective_endomorphism S hS.surjective
  exact ⟨hS.injective, fun w => ⟨S w, hi (hS _)⟩⟩

section Glue

variable {κ κ₀ κ₁ : Type} (ε : κ ≃ κ₀ ⊕ κ₁)

def glue {R : Type} (a : κ₀ → R) (b : κ₁ → R) : κ → R := fun k => Sum.elim a b (ε k)

/- English proof (translation)
Simplify using `[glue]`.
-/
@[simp] theorem glue_inl {R : Type} (a : κ₀ → R) (b : κ₁ → R) (k : κ₀) : glue ε a b (ε.symm (.inl k)) = a k := by
  simp [glue]

/- English proof (translation)
Simplify using `[glue]`.
-/
@[simp] theorem glue_inr {R : Type} (a : κ₀ → R) (b : κ₁ → R) (k : κ₁) : glue ε a b (ε.symm (.inr k)) = b k := by
  simp [glue]

/- English proof (translation)
Apply the tactic sequence `funext k; unfold glue; cases ε k <;> rfl`.
-/
theorem glue_map {R S : Type} (f : R → S) (a : κ₀ → R) (b : κ₁ → R) :
    (fun k => f (glue ε a b k)) = glue ε (fun k => f (a k)) fun k => f (b k) := by
  funext k; unfold glue; cases ε k <;> rfl

/- English proof (translation)
Apply the tactic sequence `funext k; simp only [glue, Pi.add_apply]; cases ε k <;> rfl`.
-/
theorem glue_add {R : Type} [Add R] (a a' : κ₀ → R) (b b' : κ₁ → R) :
    glue ε a b + glue ε a' b' = glue ε (a + a') (b + b') := by
  funext k; simp only [glue, Pi.add_apply]; cases ε k <;> rfl

/- English proof (translation)
Apply the tactic sequence `funext k; simp only [glue, Pi.smul_apply]; cases ε k <;> rfl`.
-/
theorem glue_smul {R S : Type} [SMul S R] (c : S) (a : κ₀ → R) (b : κ₁ → R) :
    c • glue ε a b = glue ε (c • a) (c • b) := by
  funext k; simp only [glue, Pi.smul_apply]; cases ε k <;> rfl

/- English proof (translation)
Apply the tactic sequence `funext k; simp only [glue]; cases ε k <;> rfl`.
-/
theorem glue_zero {R : Type} [Zero R] : glue ε (0 : κ₀ → R) 0 = 0 := by
  funext k; simp only [glue]; cases ε k <;> rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun k => x (ε.symm (.inl k)), fun k => x (ε.symm (.inr k)), funext fun k => by obtain ⟨k, rfl⟩ := ε.symm.surjective k cases k <;> simp⟩`.
-/
theorem exists_glue {R : Type} (x : κ → R) : ∃ a b, x = glue ε a b :=
  ⟨fun k => x (ε.symm (.inl k)), fun k => x (ε.symm (.inr k)), funext fun k => by
    obtain ⟨k, rfl⟩ := ε.symm.surjective k
    cases k <;> simp⟩

/- English proof (translation)
Rewrite using `[← sumElim_dotProduct_sumElim]`. Conclude with `Equiv.sum_comp ε fun k => Sum.elim a b k * Sum.elim a' b' k`.
-/
theorem glue_dot {R : Type} [CommRing R] [Fintype κ] [Fintype κ₀] [Fintype κ₁] (a a' : κ₀ → R) (b b' : κ₁ → R) :
    glue ε a b ⬝ᵥ glue ε a' b' = a ⬝ᵥ a' + b ⬝ᵥ b' := by
  rw [← sumElim_dotProduct_sumElim]
  exact Equiv.sum_comp ε fun k => Sum.elim a b k * Sum.elim a' b' k

/- English proof (translation)
Use `continuous_pi fun k => ?_` and prove the remaining obligations. Unfold `glue`. Consider the cases of `ε k`. Conclude with `(continuous_apply _).comp ha`. Conclude with `(continuous_apply _).comp hb`.
-/
theorem continuous_glue {R X : Type} [TopologicalSpace R] [TopologicalSpace X] {a : X → κ₀ → R} {b : X → κ₁ → R}
    (ha : Continuous a) (hb : Continuous b) : Continuous fun x => glue ε (a x) (b x) := by
  refine continuous_pi fun k => ?_
  unfold glue
  cases ε k
  · exact (continuous_apply _).comp ha
  · exact (continuous_apply _).comp hb

/- English proof (translation)
Establish `hs : Continuous fun b => glue ε a b` using `continuous_glue ε continuous_const continuous_id`. Establish `hinv : Function.LeftInverse (fun (x : κ → R) k => x (ε.symm (.inr k))) fun b => glue ε a b` using `fun b => funext fun k => glue_inr ε a b k`. Conclude with `⟨hg.1.comp_continuous hs, hg.2.comp_isClosedEmbedding (hinv.isClosedEmbedding (by fun_prop) hs)⟩`.
-/
theorem slice_mem_SB {R : Type} [TopologicalSpace R] [T2Space R] (a : κ₀ → R) {g : (κ → R) → ℂ} (hg : g ∈ SB (κ → R)) :
    (fun b => g (glue ε a b)) ∈ SB (κ₁ → R) := by
  have hs : Continuous fun b => glue ε a b := continuous_glue ε continuous_const continuous_id
  have hinv : Function.LeftInverse (fun (x : κ → R) k => x (ε.symm (.inr k))) fun b => glue ε a b :=
    fun b => funext fun k => glue_inr ε a b k
  exact ⟨hg.1.comp_continuous hs, hg.2.comp_isClosedEmbedding (hinv.isClosedEmbedding (by fun_prop) hs)⟩

def box {R : Type} (Λ : Set (κ₀ → R)) (φ : (κ₁ → R) → ℂ) : (κ → R) → ℂ :=
  fun x => Λ.indicator 1 (fun k => x (ε.symm (.inl k))) * φ fun k => x (ε.symm (.inr k))

/- English proof (translation)
Simplify using `[box]`.
-/
theorem box_glue {R : Type} (Λ : Set (κ₀ → R)) (φ : (κ₁ → R) → ℂ) (a : κ₀ → R) (b : κ₁ → R) :
    box ε Λ φ (glue ε a b) = Λ.indicator 1 a * φ b := by
  simp [box]

/- English proof (translation)
Establish `h1 : IsLocallyConstant (Λ.indicator (1 : (κ₀ → R) → ℂ))` using `(LocallyConstant.indicator (1 : LocallyConstant _ ℂ) (⟨hc.isClosed, ho⟩ : IsClopen Λ)).isLocallyConstant`. Use `⟨(h1.comp_continuous (f := fun (x : κ → R) k => x (ε.symm (.inl k))) (by fun_prop)).mul (hφ.1.comp_continuous (f := fun (x : κ → R) k => x (ε.symm (.inr k))) (by fun_prop)), ?_⟩` and prove the remaining obligations. Use `HasCompactSupport.intro ((hc.prod hφ.2.isCompact).image (continuous_glue ε continuous_fst continuous_snd)) fun x hx => ?_` and prove the remaining obligations. Take `⟨a, b, rfl⟩` from `exists_glue ε x`. Rewrite using `[box_glue]`.

Distinguish the cases in `ha : a ∈ Λ`. Rewrite using `[image_eq_zero_of_notMem_tsupport (f := φ) fun hb => hx ⟨(a, b), ⟨ha, hb⟩, rfl⟩, mul_zero]`. Rewrite using `[Set.indicator_of_notMem ha, zero_mul]`.
-/
theorem box_mem_SB {R : Type} [TopologicalSpace R] [T2Space R] {Λ : Set (κ₀ → R)} (ho : IsOpen Λ) (hc : IsCompact Λ)
    {φ : (κ₁ → R) → ℂ} (hφ : φ ∈ SB (κ₁ → R)) : box ε Λ φ ∈ SB (κ → R) := by
  have h1 : IsLocallyConstant (Λ.indicator (1 : (κ₀ → R) → ℂ)) :=
    (LocallyConstant.indicator (1 : LocallyConstant _ ℂ) (⟨hc.isClosed, ho⟩ : IsClopen Λ)).isLocallyConstant
  refine ⟨(h1.comp_continuous (f := fun (x : κ → R) k => x (ε.symm (.inl k))) (by fun_prop)).mul
    (hφ.1.comp_continuous (f := fun (x : κ → R) k => x (ε.symm (.inr k))) (by fun_prop)), ?_⟩
  refine HasCompactSupport.intro ((hc.prod hφ.2.isCompact).image
    (continuous_glue ε continuous_fst continuous_snd)) fun x hx => ?_
  obtain ⟨a, b, rfl⟩ := exists_glue ε x
  rw [box_glue]
  by_cases ha : a ∈ Λ
  · rw [image_eq_zero_of_notMem_tsupport (f := φ) fun hb => hx ⟨(a, b), ⟨ha, hb⟩, rfl⟩, mul_zero]
  · rw [Set.indicator_of_notMem ha, zero_mul]

variable [Fintype κ] [Fintype κ₁]

/- English proof (translation)
Set `L : (κ₁ → V) →L[ℝ] (κ → V)` to `{ toFun := fun b => glue ε 0 b map_add' := fun b b' => by rw [glue_add, add_zero] map_smul' := fun c b => by rw [glue_smul, smul_zero]; rfl cont := continuous_glue ε continuous_const continuous_id }`. Establish `e : (fun b => glue ε a b) = fun b => glue ε a 0 + L b` using `funext fun b => by show _ = _ + glue ε 0 b`. Rewrite using `[glue_add, add_zero, zero_add]`. Establish `ht : Function.HasTemperateGrowth fun b => glue ε a b`. Rewrite using `[e]`.

Conclude with `(Function.HasTemperateGrowth.const _).add L.hasTemperateGrowth`. Establish `hl : AntilipschitzWith 1 fun b => glue ε a b` using `AntilipschitzWith.of_le_mul_dist fun b b' => by`. Rewrite using `[NNReal.coe_one, one_mul, dist_pi_le_iff dist_nonneg]`. Introduce `k`. Simplify using `using dist_le_pi_dist (glue ε a b) (glue ε a b') (ε.symm (.inr k))`.

Conclude with `⟨SchwartzMap.compCLMOfAntilipschitz ℂ ht hl, fun f b => rfl⟩`.
-/
theorem exists_slice {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (a : κ₀ → V) :
    ∃ T : SchwartzMap (κ → V) ℂ →L[ℂ] SchwartzMap (κ₁ → V) ℂ, ∀ f b, T f b = f (glue ε a b) := by
  let L : (κ₁ → V) →L[ℝ] (κ → V) :=
    { toFun := fun b => glue ε 0 b
      map_add' := fun b b' => by rw [glue_add, add_zero]
      map_smul' := fun c b => by rw [glue_smul, smul_zero]; rfl
      cont := continuous_glue ε continuous_const continuous_id }
  have e : (fun b => glue ε a b) = fun b => glue ε a 0 + L b := funext fun b => by
    show _ = _ + glue ε 0 b
    rw [glue_add, add_zero, zero_add]
  have ht : Function.HasTemperateGrowth fun b => glue ε a b := by
    rw [e]; exact (Function.HasTemperateGrowth.const _).add L.hasTemperateGrowth
  have hl : AntilipschitzWith 1 fun b => glue ε a b := AntilipschitzWith.of_le_mul_dist fun b b' => by
    rw [NNReal.coe_one, one_mul, dist_pi_le_iff dist_nonneg]
    intro k
    simpa using dist_le_pi_dist (glue ε a b) (glue ε a b') (ε.symm (.inr k))
  exact ⟨SchwartzMap.compCLMOfAntilipschitz ℂ ht hl, fun f b => rfl⟩

/- English proof (translation)
Set `c : ContDiffBump (0 : V)` to `default`. Use `⟨(c.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)).toSchwartzMap (Complex.ofRealCLM.contDiff.comp c.contDiff), ?_⟩` and prove the remaining obligations. Use `show ((c 0 : ℝ) : ℂ) ≠ 0`. Rewrite using `[c.one_of_mem_closedBall (Metric.mem_closedBall_self c.rIn_pos.le)]`. Simplify using the standard rewrite rules.
-/
theorem exists_schwartz_ne (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    ∃ f : SchwartzMap V ℂ, f 0 ≠ 0 := by
  let c : ContDiffBump (0 : V) := default
  refine ⟨(c.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp c.contDiff), ?_⟩
  show ((c 0 : ℝ) : ℂ) ≠ 0
  rw [c.one_of_mem_closedBall (Metric.mem_closedBall_self c.rIn_pos.le)]
  simp

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Use `haveI : T2Space (Af F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F`. Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem Φ hΦ`. Take `⟨f, g, hg, rfl⟩` from `hΦ`. Take `⟨T, hT⟩` from `exists_slice ε fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (a k).1`.

Use `Submodule.subset_span ⟨T f, _, slice_mem_SB ε (fun k => (a k).2) hg, funext fun b => ?_⟩` and prove the remaining obligations. Simplify using `only [pureA, hT]`. Rewrite using `[glue_map ε (fun z : AF F => InfiniteAdeleRing.ringEquiv_mixedSpace F z.1), glue_map ε (fun z : AF F => z.2)]`. Consider the case `zero => exact Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => exact Submodule.add_mem _ hx hy`.

Consider the case `smul c x _ hx => exact Submodule.smul_mem _ c hx`.
-/
theorem slice_mem_schA (a : κ₀ → AF F) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    (fun b => Φ (glue ε a b)) ∈ schA F κ₁ := by
  classical
  haveI : T2Space (Af F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  induction hΦ using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    obtain ⟨T, hT⟩ := exists_slice ε fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (a k).1
    refine Submodule.subset_span ⟨T f, _, slice_mem_SB ε (fun k => (a k).2) hg, funext fun b => ?_⟩
    simp only [pureA, hT]
    rw [glue_map ε (fun z : AF F => InfiniteAdeleRing.ringEquiv_mixedSpace F z.1), glue_map ε (fun z : AF F => z.2)]
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

end Glue

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {κ₀ : Type} [Fintype κ₀]
  (ε : Fin n × Fin d ≃ κ₀ ⊕ Fin n₁ × Fin d₁)

/- English proof (translation)
Use `⟨LinearMap.funLeft ℂ ℂ fun b => glue ε 0 b, fun Φ hΦ => slice_mem_schA ε 0 hΦ, fun z Φ _ => ?_, fun u hu Φ _ => ?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `b`. Simplify using `only [LinearMap.funLeft_apply, Darboux.rho, schr, hco, (hj z).1, (hj z).2, glue_dot, glue_add, zero_dotProduct, zero_add]`. Use function extensionality and compare the values at `b`. Simplify using `only [LinearMap.funLeft_apply, Darboux.rho, schr, hco, (hI u hu).1, (hI u hu).2, glue_dot, glue_add, zero_dotProduct, map_zero, Prod.fst_zero, Prod.snd_zero, add_zero, dotProduct_zero, mul_zero, AddChar.map_zero_eq_one, one_mul]`.

Take `⟨T, hT⟩` from `exists_slice ε (0 : κ₀ → mixedEmbedding.mixedSpace F)`. Use `⟨T, fun v => LinearMap.funLeft ℂ ℂ fun b => glue ε 0 b, fun h => ?_, fun v => ⟨funext (hvac v), ?_⟩, fun f φ _ _ => ?_⟩` and prove the remaining obligations. Take `⟨f, hf⟩` from `exists_schwartz_ne (Fin n × Fin d → mixedEmbedding.mixedSpace F)`. Use `hT f 0` as an intermediate fact. Rewrite `this` using `[h, glue_zero]`.

Conclude with `hf this.symm`. Use `le_antisymm ?_ fun φ hφ => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨g, hg, rfl⟩`. Conclude with `slice_mem_SB ε 0 hg`. Establish `h1 : IsOpen (Set.univ.pi fun _ : κ₀ => (v.adicCompletionIntegers F : Set (Fv F v)))` using `isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_valuationSubring _`.

Establish `h2 : IsCompact (Set.univ.pi fun _ : κ₀ => (v.adicCompletionIntegers F : Set (Fv F v)))` using `isCompact_univ_pi fun _ => PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v`. Use `⟨_, box_mem_SB ε h1 h2 hφ, funext fun b => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.funLeft_apply, box_glue, Set.indicator_of_mem (by exact fun _ _ => zero_mem _), Pi.one_apply, one_mul]`. Use function extensionality and compare the values at `b`. Simplify using `only [LinearMap.funLeft_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, hT]`.

Rewrite using `[glue_map ε (evI F)]`. Use `congr 1`. Use `congr 2`. Use function extensionality and compare the values at `k`. Conclude with `map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)`.

Use `finprod_congr fun v => ?_` and prove the remaining obligations. Rewrite using `[glue_map ε (evFin F v)]`. Simplify using `only [Pi.zero_apply, map_zero]`. Both sides reduce to the same expression.
-/
theorem exists_isEv (B : Base F E) (Ma : Model σ X W) (M₁ : Model σ X₁ W₁)
    (p q : Matrix (Fin n) (Fin d) (AE F E) → κ₀ → AF F) (π : Matrix (Fin n) (Fin d) (AE F E) → Matrix (Fin n₁) (Fin d₁) (AE F E))
    (hco : ∀ z, Ma.co.e z = (glue ε (p z) (M₁.co.e (π z)).1, glue ε (q z) (M₁.co.e (π z)).2))
    (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (AE F E)))
    (hj : ∀ z, p (incM F ι * z * (incM F ι')ᵀ) = 0 ∧ π (incM F ι * z * (incM F ι')ᵀ) = z)
    (hI : ∀ u ∈ I, p u = 0 ∧ π u = 0) (hvac : ∀ v b, Ma.vac v (glue ε 0 b) = M₁.vac v b) :
    ∃ e, IsEv B Ma M₁ ι ι' I e := by
  classical
  refine ⟨LinearMap.funLeft ℂ ℂ fun b => glue ε 0 b, fun Φ hΦ => slice_mem_schA ε 0 hΦ, fun z Φ _ => ?_, fun u hu Φ _ => ?_, ?_⟩
  · funext b
    simp only [LinearMap.funLeft_apply, Darboux.rho, schr, hco, (hj z).1, (hj z).2, glue_dot, glue_add, zero_dotProduct,
      zero_add]
  · funext b
    simp only [LinearMap.funLeft_apply, Darboux.rho, schr, hco, (hI u hu).1, (hI u hu).2, glue_dot, glue_add,
      zero_dotProduct, map_zero, Prod.fst_zero, Prod.snd_zero, add_zero, dotProduct_zero, mul_zero,
      AddChar.map_zero_eq_one, one_mul]
  · obtain ⟨T, hT⟩ := exists_slice ε (0 : κ₀ → mixedEmbedding.mixedSpace F)
    refine ⟨T, fun v => LinearMap.funLeft ℂ ℂ fun b => glue ε 0 b, fun h => ?_, fun v => ⟨funext (hvac v), ?_⟩,
      fun f φ _ _ => ?_⟩
    · obtain ⟨f, hf⟩ := exists_schwartz_ne (Fin n × Fin d → mixedEmbedding.mixedSpace F)
      have := hT f 0
      rw [h, glue_zero] at this
      exact hf this.symm
    · refine le_antisymm ?_ fun φ hφ => ?_
      · rintro _ ⟨g, hg, rfl⟩
        exact slice_mem_SB ε 0 hg
      · have h1 : IsOpen (Set.univ.pi fun _ : κ₀ => (v.adicCompletionIntegers F : Set (Fv F v))) :=
          isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_valuationSubring _
        have h2 : IsCompact (Set.univ.pi fun _ : κ₀ => (v.adicCompletionIntegers F : Set (Fv F v))) :=
          isCompact_univ_pi fun _ => PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v
        refine ⟨_, box_mem_SB ε h1 h2 hφ, funext fun b => ?_⟩
        rw [LinearMap.funLeft_apply, box_glue, Set.indicator_of_mem (by exact fun _ _ => zero_mem _), Pi.one_apply, one_mul]
    · funext b
      simp only [LinearMap.funLeft_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, hT]
      rw [glue_map ε (evI F)]
      congr 1
      · congr 2
        funext k
        exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
      · refine finprod_congr fun v => ?_
        rw [glue_map ε (evFin F v)]
        simp only [Pi.zero_apply, map_zero]
        rfl

/- English proof (translation)
Take `⟨hKo, hKc⟩` from `GlobalTheory.LatOpenCpt.main σ B X W r s r' s' hX hW Ma hrat v`. Use `set K := (latAtV X W v).map (GlobalTheory.LatVac.locCo Ma.co v) with hK`. Set `pr : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) →+ (κ₀ → Fv F v)` to `{ toFun := fun w k => w.1 (ε.symm (.inl k)), map_zero' := rfl, map_add' := fun _ _ => rfl }`. Establish `hΛc : IsCompact (K.map pr : Set (κ₀ → Fv F v))` using `hKc.image (show Continuous fun (w : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) k => w.1 (ε.symm (.inl k)) by fun_prop)`. Establish `hΛo : IsOpen (K.map pr : Set (κ₀ → Fv F v))`.

Apply `AddSubgroup.isOpen_of_mem_nhds (g := 0)` to reduce the goal to its premises. Establish `hc : Continuous fun a : κ₀ → Fv F v => ((glue ε a 0, 0) : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v))` using `(continuous_glue ε continuous_id continuous_const).prodMk continuous_const`. Use `Filter.mem_of_superset ((hKo.preimage hc).mem_nhds ?_) fun a ha => ⟨_, ha, funext fun k => glue_inl ε a 0 k⟩` and prove the remaining obligations. Use `show (glue ε 0 0, 0) ∈ K`. Rewrite using `[glue_zero]`.

Conclude with `K.zero_mem`. Establish `hmem : ∀ a, a ∈ K.map pr ↔ ∃ γ ∈ latAtV X W v, (fun k => evFin F v (p γ k)) = a` using `fun a => by`. Establish `: ∀ γ, pr (GlobalTheory.LatVac.locCo Ma.co v γ) = fun k => evFin F v (p γ k)` using `fun γ => funext fun k => by show evFin F v ((Ma.co.e γ).1 _) = _`. Simplify using `only [hco, glue_inl]`. Simplify using `only [hK, AddSubgroup.map_map, AddSubgroup.mem_map, AddMonoidHom.comp_apply, this]`.

Use `set Λ := K.map pr`. Establish `h0 : ∀ b, box ε (Λ : Set _) φ (glue ε 0 b) = φ b` using `fun b => by`. Rewrite using `[box_glue, Set.indicator_of_mem Λ.zero_mem, Pi.one_apply, one_mul]`. Take `⟨hSB, hne, θ, hθ1, hA⟩` from `hφ`. Use `⟨box ε Λ φ, ⟨box_mem_SB ε hΛo hΛc hSB, fun h => hne (funext fun b => by rw [← h0, h]; rfl), θ, hθ1, fun γ hγ R hR => ?_⟩, h0⟩` and prove the remaining obligations.

Establish `hat : ∀ u, evFin F v u = 0 → u • p γ = 0 ∧ u • q γ = 0` using `fun u hu => by`. Establish `h1` using `congrArg Ma.co.e ((GlobalTheory.LatVac.latAtV_at_stable X W v).1 γ hγ u hu)`. Rewrite `h1` using `[map_smul, map_zero, hco]`. Conclude with `⟨funext fun k => by simpa using congrFun (congrArg Prod.fst h1) (ε.symm (.inl k)),`. Use function extensionality and compare the values at `fun k => by simpa using congrFun (congrArg Prod.snd h1) (ε.symm (.inl k))⟩`.

Use function extensionality and compare the values at `x`. Take `⟨a, b, rfl⟩` from `exists_glue ε x`. Establish `hp : (fun k => evFin F v (p γ k)) ∈ Λ` using `(hmem _).2 ⟨γ, hγ, rfl⟩`. Simplify using `only [Darboux.rho, schr, tens, hco, glue_dot, glue_add, glue_map ε (evFin F v), Pi.smul_apply, box_glue]`. Distinguish the cases in `ha : (fun k => evFin F v (a k)) ∈ Λ`.

Establish `ha' : (fun k => evFin F v ((a + p γ) k)) ∈ Λ`. Simplify using `only [Pi.add_apply, map_add]`. Conclude with `Λ.add_mem ha hp`. Establish `hR₁ : Rest (evFin F v) φ fun b => R (glue ε a b)`. Use `⟨fun x z hz => ?_, ?_⟩` and prove the remaining obligations.

Use `hR.1 (glue ε a x) (glue ε 0 z) fun u hu => by rw [glue_smul, hz u hu, smul_zero, glue_zero]` as an intermediate fact. Rewrite `this` using `[glue_add, add_zero]`. Then use the resulting hypothesis. Use `slice_mem_schA ε a hR.2` as an intermediate fact. Simplify using `only [tens, glue_map ε (evFin F v), box_glue, Set.indicator_of_mem ha, Pi.one_apply, one_mul] at this`. Conclude with `this`.

Establish `key` using `congrFun (hA (π γ) (hlat γ hγ) _ hR₁) b`. Simplify using `only [Darboux.rho, schr, tens, Pi.smul_apply] at key`. Establish `hs : ∀ c, R (glue ε (a + p γ) c) = R (glue ε a c)` using `fun c => by`. Use `hR.1 (glue ε a c) (glue ε (p γ) 0) fun u hu => by rw [glue_smul, (hat u hu).1, smul_zero, glue_zero]` as an intermediate fact. Rewrite `this` using `[glue_add, add_zero]`. Then use the resulting hypothesis.

Establish `h1 : B.ψ (a ⬝ᵥ q γ) = 1`. Take `⟨γ', hγ', e⟩` from `(hmem _).1 ha`. Rewrite using `[← hpq γ hγ γ' hγ']`. Use `congr 1`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Use `congrFun (hat (a k - p γ' k) (by rw [map_sub, sub_eq_zero]; exact (congrFun e k).symm)).2 k` as an intermediate fact. Simplify using `only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this`. Take the linear combination `this`. Rewrite using `[Set.indicator_of_mem ha, Set.indicator_of_mem ha', hs, hθ θ hθ1 γ hγ, mul_add, add_add_add_comm, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul B.ψ (a ⬝ᵥ q γ), h1]`. Simplify using `only [Pi.one_apply, one_mul, smul_eq_mul] at key ⊢`.

Rewrite using `[mul_assoc, key]`. Expand and normalize the polynomial expressions, which then agree. Establish `ha' : (fun k => evFin F v ((a + p γ) k)) ∉ Λ` using `fun h => ha (by`. Use `Λ.sub_mem h hp` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `k`. Use the proof step `simp)`. Rewrite using `[Set.indicator_of_notMem ha, Set.indicator_of_notMem ha']`. Simplify using the standard rewrite rules.
-/
theorem exists_isVac {B : Base F E} {r s r' s' : ℕ} (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s')
    (Ma : Model σ X W) (M₁ : Model σ X₁ W₁)
    (hrat : ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      Ma.co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)))
    (p q : Matrix (Fin n) (Fin d) (AE F E) → κ₀ → AF F) (π : Matrix (Fin n) (Fin d) (AE F E) → Matrix (Fin n₁) (Fin d₁) (AE F E))
    (hco : ∀ z, Ma.co.e z = (glue ε (p z) (M₁.co.e (π z)).1, glue ε (q z) (M₁.co.e (π z)).2)) (v : Pl F)
    (hlat : ∀ γ ∈ latAtV X W v, π γ ∈ latAtV X₁ W₁ v)
    (hpq : ∀ γ ∈ latAtV X W v, ∀ γ' ∈ latAtV X W v, B.ψ (p γ' ⬝ᵥ q γ) = 1)
    (hθ : ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 → ∀ γ ∈ latAtV X W v,
      B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ) =
        B.ψ (⅟(2 : AF F) * (p γ ⬝ᵥ q γ)) *
          B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X₁.J) (incM F W₁.J) (π γ) (π γ)))
    {φ : (Fin n₁ × Fin d₁ → Fv F v) → ℂ} (hφ : M₁.IsVac B.ψ v φ) :
    ∃ φa, Ma.IsVac B.ψ v φa ∧ ∀ b, φa (glue ε 0 b) = φ b := by
  obtain ⟨hKo, hKc⟩ := GlobalTheory.LatOpenCpt.main σ B X W r s r' s' hX hW Ma hrat v
  set K := (latAtV X W v).map (GlobalTheory.LatVac.locCo Ma.co v) with hK
  let pr : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) →+ (κ₀ → Fv F v) :=
    { toFun := fun w k => w.1 (ε.symm (.inl k)), map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hΛc : IsCompact (K.map pr : Set (κ₀ → Fv F v)) :=
    hKc.image (show Continuous fun (w : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) k => w.1 (ε.symm (.inl k)) by
      fun_prop)
  have hΛo : IsOpen (K.map pr : Set (κ₀ → Fv F v)) := by
    apply AddSubgroup.isOpen_of_mem_nhds (g := 0)
    have hc : Continuous fun a : κ₀ → Fv F v => ((glue ε a 0, 0) : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) :=
      (continuous_glue ε continuous_id continuous_const).prodMk continuous_const
    refine Filter.mem_of_superset ((hKo.preimage hc).mem_nhds ?_) fun a ha => ⟨_, ha, funext fun k => glue_inl ε a 0 k⟩
    show (glue ε 0 0, 0) ∈ K
    rw [glue_zero]
    exact K.zero_mem
  have hmem : ∀ a, a ∈ K.map pr ↔ ∃ γ ∈ latAtV X W v, (fun k => evFin F v (p γ k)) = a := fun a => by
    have : ∀ γ, pr (GlobalTheory.LatVac.locCo Ma.co v γ) = fun k => evFin F v (p γ k) := fun γ => funext fun k => by
      show evFin F v ((Ma.co.e γ).1 _) = _
      simp only [hco, glue_inl]
    simp only [hK, AddSubgroup.map_map, AddSubgroup.mem_map, AddMonoidHom.comp_apply, this]
  set Λ := K.map pr
  have h0 : ∀ b, box ε (Λ : Set _) φ (glue ε 0 b) = φ b := fun b => by
    rw [box_glue, Set.indicator_of_mem Λ.zero_mem, Pi.one_apply, one_mul]
  obtain ⟨hSB, hne, θ, hθ1, hA⟩ := hφ
  refine ⟨box ε Λ φ, ⟨box_mem_SB ε hΛo hΛc hSB, fun h => hne (funext fun b => by rw [← h0, h]; rfl), θ, hθ1,
    fun γ hγ R hR => ?_⟩, h0⟩
  have hat : ∀ u, evFin F v u = 0 → u • p γ = 0 ∧ u • q γ = 0 := fun u hu => by
    have h1 := congrArg Ma.co.e ((GlobalTheory.LatVac.latAtV_at_stable X W v).1 γ hγ u hu)
    rw [map_smul, map_zero, hco] at h1
    exact ⟨funext fun k => by simpa using congrFun (congrArg Prod.fst h1) (ε.symm (.inl k)),
      funext fun k => by simpa using congrFun (congrArg Prod.snd h1) (ε.symm (.inl k))⟩
  funext x
  obtain ⟨a, b, rfl⟩ := exists_glue ε x
  have hp : (fun k => evFin F v (p γ k)) ∈ Λ := (hmem _).2 ⟨γ, hγ, rfl⟩
  simp only [Darboux.rho, schr, tens, hco, glue_dot, glue_add, glue_map ε (evFin F v), Pi.smul_apply, box_glue]
  by_cases ha : (fun k => evFin F v (a k)) ∈ Λ
  · have ha' : (fun k => evFin F v ((a + p γ) k)) ∈ Λ := by
      simp only [Pi.add_apply, map_add]
      exact Λ.add_mem ha hp
    have hR₁ : Rest (evFin F v) φ fun b => R (glue ε a b) := by
      refine ⟨fun x z hz => ?_, ?_⟩
      · have := hR.1 (glue ε a x) (glue ε 0 z) fun u hu => by rw [glue_smul, hz u hu, smul_zero, glue_zero]
        rwa [glue_add, add_zero] at this
      · have := slice_mem_schA ε a hR.2
        simp only [tens, glue_map ε (evFin F v), box_glue, Set.indicator_of_mem ha, Pi.one_apply, one_mul] at this
        exact this
    have key := congrFun (hA (π γ) (hlat γ hγ) _ hR₁) b
    simp only [Darboux.rho, schr, tens, Pi.smul_apply] at key
    have hs : ∀ c, R (glue ε (a + p γ) c) = R (glue ε a c) := fun c => by
      have := hR.1 (glue ε a c) (glue ε (p γ) 0) fun u hu => by rw [glue_smul, (hat u hu).1, smul_zero, glue_zero]
      rwa [glue_add, add_zero] at this
    have h1 : B.ψ (a ⬝ᵥ q γ) = 1 := by
      obtain ⟨γ', hγ', e⟩ := (hmem _).1 ha
      rw [← hpq γ hγ γ' hγ']
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      have := congrFun (hat (a k - p γ' k) (by rw [map_sub, sub_eq_zero]; exact (congrFun e k).symm)).2 k
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      linear_combination this
    rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha', hs, hθ θ hθ1 γ hγ, mul_add, add_add_add_comm,
      AddChar.map_add_eq_mul, AddChar.map_add_eq_mul B.ψ (a ⬝ᵥ q γ), h1]
    simp only [Pi.one_apply, one_mul, smul_eq_mul] at key ⊢
    rw [mul_assoc, key]
    ring
  · have ha' : (fun k => evFin F v ((a + p γ) k)) ∉ Λ := fun h => ha (by
      have := Λ.sub_mem h hp
      convert this using 1
      funext k
      simp)
    rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha']
    simp

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Conclude with `τ.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])`.
-/
theorem conj_conj {B : Base F E} (hB : B.IsGood σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact τ.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e => simp [cA, conj_conj hB]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.
-/
theorem cA_cA {B : Base F E} (hB : B.IsGood σ) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [cA, conj_conj hB]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/- English proof (translation)
Set `ε : Fin n × Fin d ≃ (κ × Fin 2) ⊕ Fin n₁ × Fin d₁` to `Fintype.equivOfCardEq (by simp [hcard])`. Set `β` to `Module.finBasisOfFinrankEq F E hB.cm.2.2.1`. Set `βA` to `Algebra.TensorProduct.basis (AF F) β`. Set `Tr` to `Algebra.trace (AF F) (AE F E)`. Set `p : Matrix (Fin n) (Fin d) (AE F E) → κ × Fin 2 → AF F` to `fun z k => βA.repr (b z k.1) k.2`.

Set `q : Matrix (Fin n) (Fin d) (AE F E) → κ × Fin 2 → AF F` to `fun z k => -Tr (βA k.2 * D z k.1)`. Establish `hpq : ∀ z z', p z ⬝ᵥ q z' = -Tr (b z ⬝ᵥ D z')` using `fun z z' => by`. Simplify using `only [dotProduct, Fintype.sum_prod_type, map_sum, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `conv_rhs => rw [← βA.sum_repr (b z k), Finset.sum_mul, map_sum, ← Finset.sum_neg_distrib]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_mul_assoc, map_smul, smul_eq_mul, ← mul_neg]`. Establish `hTr : ∀ z, Tr (cA σ z) = Tr z` using `GlobalTheory.VacCocycle.trace_conj (cA σ) (cA_cA hB)`. Set `Φ : Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)` to `{ toFun := fun z => (glue ε (p z) (M₁.co.e (π z)).1, glue ε (q z) (M₁.co.e (π z)).2) map_add' := fun z z' => by`. Rewrite using `[Prod.mk_add_mk, glue_add, glue_add, hπ.map_add, map_add]`.

Apply the tactic sequence `congr 2 <;> funext k <;> simp [p, q, hb.map_add, hD.map_add, mul_add, add_comm]`. Use the proof step `map_smul' := fun c z => by`. Rewrite using `[Prod.smul_mk, glue_smul, glue_smul, hπ.map_smul, map_smul]`. Apply the tactic sequence `congr 2 <;> funext k <;> simp [p, q, hb.map_smul, hD.map_smul] }`. Establish `hΦ : ∀ z z', symp (R` using `AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) z z' = (Φ z).1 ⬝ᵥ (Φ z').2 - (Φ z').1 ⬝ᵥ (Φ z).2 := fun z z' => by`.

Establish `h1` using `M₁.co.form (π z) (π z')`. Use `show Tr _ = glue ε _ _ ⬝ᵥ glue ε _ _ - glue ε _ _ ⬝ᵥ glue ε _ _`. Express the relevant statement in the definitionally equal form `Tr _ = _ at h1`. Rewrite using `[glue_dot, glue_dot, hpq, hpq, hH, mul_add, map_add, h1, neg_one_mul, map_neg, map_sub, hTr]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hbij : Function.Bijective Φ`. Use `(bijective_of_symp (Φ ∘ₗ M.co.e.symm.toLinearMap) fun u w => by` as an intermediate fact. Establish `h1` using `M.co.form (M.co.e.symm u) (M.co.e.symm w)`. Rewrite `h1` using `[hΦ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]`. Conclude with `h1).comp M.co.e.bijective`.

Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `z`. Simplify using the standard rewrite rules. Set `co : Darboux (symp (R` to `AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d) := ⟨LinearEquiv.ofBijective Φ hbij, hΦ⟩`. Establish `hco : ∀ z, co.e z = (glue ε (p z) (M₁.co.e (π z)).1, glue ε (q z) (M₁.co.e (π z)).2)` using `fun z => rfl`.

Establish `hr : ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F, co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))` using `fun x => by`. Take `⟨⟨y, hy⟩, ⟨y', hy'⟩, x₁, hx₁⟩` from `hrat x`. Take `⟨u, w, huw⟩` from `hM₁.rat x₁`. Use `⟨glue ε (fun k => β.repr (y k.1) k.2) u, glue ε (fun k => -Algebra.trace F E (β k.2 * y' k.1)) w, ?_⟩` and prove the remaining obligations. Rewrite using `[hco, hx₁, huw, glue_map ε (algebraMap F (AF F)), glue_map ε (algebraMap F (AF F))]`.

Apply the tactic sequence `congr 2 <;> funext k`. Simplify using `only [p, hy] show βA.repr ((1 : AF F) ⊗ₜ[F] y k.1) k.2 = _`. Simplify using `[βA, Algebra.TensorProduct.basis_repr_tmul]`. Simplify using `only [q, hy']`. Rewrite using `[map_neg, ← GlobalTheory.VacIndic.trace_inclR, map_mul (inclR (F := F) (AF F)), Algebra.TensorProduct.basis_apply]`.

Both sides reduce to the same expression. Establish `hδ : ∀ v, ∀ γ ∈ latAtV X W v, ∀ γ' ∈ latAtV X W v, ∀ θ : 𝓞 E, B.ψ (Tr (inclR (F` using `F) (AF F) (θ : E) * (b γ' ⬝ᵥ D γ))) = 1 := fun v γ hγ γ' hγ' θ => by`. Take `⟨-, δ, h0, h1, h2, h3⟩` from `hlat v γ hγ`. Use `GlobalTheory.LatVacArith.psi_symp_latAtV σ B X W r s r' s' hB hX hW v θ 1 (by rw [map_one]; exact one_mem _) γ' hγ' δ h0` as an intermediate fact. Rewrite `this` using `[one_mul, symp, hH, h1, h2, h3]`.

Simplify `this` using `[hTens]`. Establish `hv : ∀ v, ∃ φa, Model.IsVac (⟨co, fun _ => 0, 0, ∅⟩ : Model σ X W) B.ψ v φa ∧ ∀ c, φa (glue ε 0 c) = M₁.vac v c`. Introduce `v`. Use `exists_isVac ε hX hW _ M₁ hr p q π hco v (fun γ hγ => (hlat v γ hγ).1) (fun γ hγ γ' hγ' => ?_) (fun θ hθ γ hγ => ?_) (hM₁.vac v)` and prove the remaining obligations. Use `hδ v γ hγ γ' hγ' (-1)` as an intermediate fact.

Rewrite `this` using `[show ((-1 : 𝓞 E) : E) = -1 by simp, map_neg, map_one, neg_one_mul, map_neg]`. Rewrite using `[hpq, this]`. Rewrite using `[← one_mul (B.ψ _ * B.ψ _), ← hδ v γ hγ γ hγ θ]`. Simplify using `only [← AddChar.map_add_eq_mul]`. Use `congr 1`.

Establish `h1 : inclR (F` using `F) (AF F) (θ : E) + cA σ (inclR (F := F) (AF F) (θ : E)) = 1 := by`. Rewrite using `[GlobalTheory.VacIndic.cA_inclR, ← map_add, hθ, map_one]`. Establish `h2 : Tr (inclR (F` using `F) (AF F) (θ : E) * cA σ (b γ ⬝ᵥ D γ)) = Tr (b γ ⬝ᵥ D γ) - Tr (inclR (F := F) (AF F) (θ : E) * (b γ ⬝ᵥ D γ)) := by`. Rewrite using `[← hTr, map_mul, cA_cA hB, ← map_sub, eq_sub_of_add_eq' h1, sub_mul, one_mul]`. Establish `h3 : (⅟(2 : AF F)) * 2 = 1` using `invOf_mul_self _`.

Use `show _ * Tr _ = _ + (_ + _ * Tr _)`. Rewrite using `[hpq, hH, mul_add (inclR (F := F) (AF F) (θ : E)), mul_sub, map_add, map_sub, h2]`. Generalize the expression as in `(⅟(2 : AF F)) = t at h3 ⊢`. Take the linear combination `(Tr (inclR (F := F) (AF F) (θ : E) * (b γ ⬝ᵥ D γ))) * h3`. Use `choose φa hφa hφb using hv`.

Set `S : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ` to `fun v => Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1`. Set `G : Pl F → Prop` to `fun v => Model.IsVac (⟨co, fun _ => 0, 0, ∅⟩ : Model σ X W) B.ψ v (S v) ∧ M₁.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1`. Set `Ma : Model σ X W` to `⟨co, fun v => if G v then S v else φa v, M.μ, M.dom⟩`. Take `⟨e, he⟩` from `exists_isEv ε B Ma M₁ p q π hco ι ι' I (fun z => ⟨funext fun k => by simp [p, (hj z).1], (hj z).2⟩) (fun u hu => ⟨funext fun k => by simp [p, (hI u hu).1], (hI u hu).2⟩) fun v c => by`. Distinguish the cases in `h : G v`.

Use `show (if G v then S v else φa v) _ = _`. Rewrite using `[if_pos h, h.2]`. Use `Set.indicator_eq_indicator ⟨fun hx i => ?_, fun hx i => ?_⟩ rfl` and prove the remaining obligations. Simplify using `using hx (ε.symm (.inr i))`. Take `⟨i, rfl⟩` from `ε.symm.surjective i`.

Break down `i with i | i` into its components or cases. Rewrite using `[glue_inl]`. Conclude with `zero_mem _`. Rewrite using `[glue_inr]`. Conclude with `hx i`.

Use `show (if G v then S v else φa v) _ = _`. Rewrite using `[if_neg h, hφb]`. Use `⟨Ma, e, ⟨hr, fun v => ?_, ?_, hM.haar, hM.dom⟩, he⟩` and prove the remaining obligations. Use `show Model.IsVac _ _ _ (if G v then S v else φa v) split_ifs with h`. Conclude with `h.1`.

Conclude with `hφa v`. Use `filter_upwards [GlobalTheory.VacIndic.eventually_isVac_indicator B hB X W r s r' s' hX hW co hr, hM₁.std] with v h1 h2`. Conclude with `if_pos ⟨h1, h2⟩`.
-/
theorem exists_model {B : Base F E} {r s r' s' : ℕ} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s')
    {M : Model σ X W} (hM : M.IsGood B.ψ) {M₁ : Model σ X₁ W₁} (hM₁ : M₁.IsGood B.ψ) {κ : Type} [Fintype κ]
    (hcard : n * d = Fintype.card κ * 2 + n₁ * d₁) (b D : Matrix (Fin n) (Fin d) (AE F E) → κ → AE F E)
    (π : Matrix (Fin n) (Fin d) (AE F E) → Matrix (Fin n₁) (Fin d₁) (AE F E)) (hb : IsLinearMap (AF F) b)
    (hD : IsLinearMap (AF F) D) (hπ : IsLinearMap (AF F) π)
    (hH : ∀ z z', hTens (cA σ) (incM F X.J) (incM F W.J) z z' =
      b z ⬝ᵥ D z' - cA σ (b z' ⬝ᵥ D z) + hTens (cA σ) (incM F X₁.J) (incM F W₁.J) (π z) (π z'))
    (hrat : ∀ x, (∃ y : κ → E, b (incM F x) = fun k => inclR (F := F) (AF F) (y k)) ∧
      (∃ y : κ → E, D (incM F x) = fun k => inclR (F := F) (AF F) (y k)) ∧ ∃ x₁, π (incM F x) = incM F x₁)
    (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (AE F E)))
    (hj : ∀ z, b (incM F ι * z * (incM F ι')ᵀ) = 0 ∧ π (incM F ι * z * (incM F ι')ᵀ) = z)
    (hI : ∀ u ∈ I, b u = 0 ∧ π u = 0)
    (hlat : ∀ v, ∀ γ ∈ latAtV X W v, π γ ∈ latAtV X₁ W₁ v ∧ ∃ δ ∈ latAtV X W v, b δ = 0 ∧ π δ = 0 ∧ D δ = D γ) :
    ∃ (Ma : Model σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁), Ma.IsGood B.ψ ∧ IsEv B Ma M₁ ι ι' I e := by
  classical
  let ε : Fin n × Fin d ≃ (κ × Fin 2) ⊕ Fin n₁ × Fin d₁ := Fintype.equivOfCardEq (by simp [hcard])
  let β := Module.finBasisOfFinrankEq F E hB.cm.2.2.1
  let βA := Algebra.TensorProduct.basis (AF F) β
  let Tr := Algebra.trace (AF F) (AE F E)
  let p : Matrix (Fin n) (Fin d) (AE F E) → κ × Fin 2 → AF F := fun z k => βA.repr (b z k.1) k.2
  let q : Matrix (Fin n) (Fin d) (AE F E) → κ × Fin 2 → AF F := fun z k => -Tr (βA k.2 * D z k.1)
  have hpq : ∀ z z', p z ⬝ᵥ q z' = -Tr (b z ⬝ᵥ D z') := fun z z' => by
    simp only [dotProduct, Fintype.sum_prod_type, map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    conv_rhs => rw [← βA.sum_repr (b z k), Finset.sum_mul, map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, map_smul, smul_eq_mul, ← mul_neg]
  have hTr : ∀ z, Tr (cA σ z) = Tr z := GlobalTheory.VacCocycle.trace_conj (cA σ) (cA_cA hB)
  let Φ : Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
    { toFun := fun z => (glue ε (p z) (M₁.co.e (π z)).1, glue ε (q z) (M₁.co.e (π z)).2)
      map_add' := fun z z' => by
        rw [Prod.mk_add_mk, glue_add, glue_add, hπ.map_add, map_add]
        congr 2 <;> funext k <;> simp [p, q, hb.map_add, hD.map_add, mul_add, add_comm]
      map_smul' := fun c z => by
        rw [Prod.smul_mk, glue_smul, glue_smul, hπ.map_smul, map_smul]
        congr 2 <;> funext k <;> simp [p, q, hb.map_smul, hD.map_smul] }
  have hΦ : ∀ z z', symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) z z' =
      (Φ z).1 ⬝ᵥ (Φ z').2 - (Φ z').1 ⬝ᵥ (Φ z).2 := fun z z' => by
    have h1 := M₁.co.form (π z) (π z')
    show Tr _ = glue ε _ _ ⬝ᵥ glue ε _ _ - glue ε _ _ ⬝ᵥ glue ε _ _
    change Tr _ = _ at h1
    rw [glue_dot, glue_dot, hpq, hpq, hH, mul_add, map_add, h1, neg_one_mul, map_neg, map_sub, hTr]
    ring
  have hbij : Function.Bijective Φ := by
    have := (bijective_of_symp (Φ ∘ₗ M.co.e.symm.toLinearMap) fun u w => by
      have h1 := M.co.form (M.co.e.symm u) (M.co.e.symm w)
      rw [hΦ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h1
      exact h1).comp M.co.e.bijective
    convert this using 1
    funext z
    simp
  let co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d) :=
    ⟨LinearEquiv.ofBijective Φ hbij, hΦ⟩
  have hco : ∀ z, co.e z = (glue ε (p z) (M₁.co.e (π z)).1, glue ε (q z) (M₁.co.e (π z)).2) := fun z => rfl
  have hr : ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := fun x => by
    obtain ⟨⟨y, hy⟩, ⟨y', hy'⟩, x₁, hx₁⟩ := hrat x
    obtain ⟨u, w, huw⟩ := hM₁.rat x₁
    refine ⟨glue ε (fun k => β.repr (y k.1) k.2) u, glue ε (fun k => -Algebra.trace F E (β k.2 * y' k.1)) w, ?_⟩
    rw [hco, hx₁, huw, glue_map ε (algebraMap F (AF F)), glue_map ε (algebraMap F (AF F))]
    congr 2 <;> funext k
    · simp only [p, hy]
      show βA.repr ((1 : AF F) ⊗ₜ[F] y k.1) k.2 = _
      simp [βA, Algebra.TensorProduct.basis_repr_tmul]
    · simp only [q, hy']
      rw [map_neg, ← GlobalTheory.VacIndic.trace_inclR, map_mul (inclR (F := F) (AF F)), Algebra.TensorProduct.basis_apply]
      rfl
  have hδ : ∀ v, ∀ γ ∈ latAtV X W v, ∀ γ' ∈ latAtV X W v, ∀ θ : 𝓞 E,
      B.ψ (Tr (inclR (F := F) (AF F) (θ : E) * (b γ' ⬝ᵥ D γ))) = 1 := fun v γ hγ γ' hγ' θ => by
    obtain ⟨-, δ, h0, h1, h2, h3⟩ := hlat v γ hγ
    have := GlobalTheory.LatVacArith.psi_symp_latAtV σ B X W r s r' s' hB hX hW v θ 1 (by rw [map_one]; exact one_mem _) γ' hγ' δ h0
    rw [one_mul, symp, hH, h1, h2, h3] at this
    simpa [hTens] using this
  have hv : ∀ v, ∃ φa, Model.IsVac (⟨co, fun _ => 0, 0, ∅⟩ : Model σ X W) B.ψ v φa ∧ ∀ c, φa (glue ε 0 c) = M₁.vac v c := by
    intro v
    refine exists_isVac ε hX hW _ M₁ hr p q π hco v (fun γ hγ => (hlat v γ hγ).1) (fun γ hγ γ' hγ' => ?_)
      (fun θ hθ γ hγ => ?_) (hM₁.vac v)
    · have := hδ v γ hγ γ' hγ' (-1)
      rw [show ((-1 : 𝓞 E) : E) = -1 by simp, map_neg, map_one, neg_one_mul, map_neg] at this
      rw [hpq, this]
    · rw [← one_mul (B.ψ _ * B.ψ _), ← hδ v γ hγ γ hγ θ]
      simp only [← AddChar.map_add_eq_mul]
      congr 1
      have h1 : inclR (F := F) (AF F) (θ : E) + cA σ (inclR (F := F) (AF F) (θ : E)) = 1 := by
        rw [GlobalTheory.VacIndic.cA_inclR, ← map_add, hθ, map_one]
      have h2 : Tr (inclR (F := F) (AF F) (θ : E) * cA σ (b γ ⬝ᵥ D γ)) =
          Tr (b γ ⬝ᵥ D γ) - Tr (inclR (F := F) (AF F) (θ : E) * (b γ ⬝ᵥ D γ)) := by
        rw [← hTr, map_mul, cA_cA hB, ← map_sub, eq_sub_of_add_eq' h1, sub_mul, one_mul]
      have h3 : (⅟(2 : AF F)) * 2 = 1 := invOf_mul_self _
      show _ * Tr _ = _ + (_ + _ * Tr _)
      rw [hpq, hH, mul_add (inclR (F := F) (AF F) (θ : E)), mul_sub, map_add, map_sub, h2]
      generalize (⅟(2 : AF F)) = t at h3 ⊢
      linear_combination (Tr (inclR (F := F) (AF F) (θ : E) * (b γ ⬝ᵥ D γ))) * h3
  choose φa hφa hφb using hv
  let S : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ := fun v => Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
  let G : Pl F → Prop := fun v => Model.IsVac (⟨co, fun _ => 0, 0, ∅⟩ : Model σ X W) B.ψ v (S v) ∧
    M₁.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
  let Ma : Model σ X W := ⟨co, fun v => if G v then S v else φa v, M.μ, M.dom⟩
  obtain ⟨e, he⟩ := exists_isEv ε B Ma M₁ p q π hco ι ι' I
    (fun z => ⟨funext fun k => by simp [p, (hj z).1], (hj z).2⟩)
    (fun u hu => ⟨funext fun k => by simp [p, (hI u hu).1], (hI u hu).2⟩) fun v c => by
      by_cases h : G v
      · show (if G v then S v else φa v) _ = _
        rw [if_pos h, h.2]
        refine Set.indicator_eq_indicator ⟨fun hx i => ?_, fun hx i => ?_⟩ rfl
        · simpa using hx (ε.symm (.inr i))
        · obtain ⟨i, rfl⟩ := ε.symm.surjective i
          rcases i with i | i
          · rw [glue_inl]; exact zero_mem _
          · rw [glue_inr]; exact hx i
      · show (if G v then S v else φa v) _ = _
        rw [if_neg h, hφb]
  refine ⟨Ma, e, ⟨hr, fun v => ?_, ?_, hM.haar, hM.dom⟩, he⟩
  · show Model.IsVac _ _ _ (if G v then S v else φa v)
    split_ifs with h
    · exact h.1
    · exact hφa v
  · filter_upwards [GlobalTheory.VacIndic.eventually_isVac_indicator B hB X W r s r' s' hX hW co hr, hM₁.std] with v h1 h2
    exact if_pos ⟨h1, h2⟩

section Alg

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S) {α β α' β' : Type} [Fintype α] [Fintype β]
  [Fintype α'] [Fintype β']

/- English proof (translation)
Simplify using `only [hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `Eq.trans ?_ Finset.sum_comm` and prove the remaining obligations.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => by ring`.
-/
theorem hTens_eq_trace (J : Matrix α α S) (J' : Matrix β β S) (z z' : Matrix α β S) :
    hTens c J J' z z' = (zᵀ * J * z'.map c * J'ᵀ).trace := by
  simp only [hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Eq.trans ?_ Finset.sum_comm
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => by ring

/- English proof (translation)
Establish `hm : (P * z' * P'ᵀ).map c = P.map c * z'.map c * (P'.map c)ᵀ`. Rewrite using `[show (P * z' * P'ᵀ).map c = (P * z').map c * P'ᵀ.map c from Matrix.map_mul (f := c.toRingHom), show (P * z').map c = P.map c * z'.map c from Matrix.map_mul (f := c.toRingHom)]`. Both sides reduce to the same expression. Rewrite using `[hTens_eq_trace, hTens_eq_trace, hm]`. Simplify using `only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]`.

Rewrite using `[Matrix.trace_mul_comm]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem hTens_mul (J : Matrix α α S) (J' : Matrix β β S) (P : Matrix α α' S) (P' : Matrix β β' S) (z z' : Matrix α' β' S) :
    hTens c J J' (P * z * P'ᵀ) (P * z' * P'ᵀ) = hTens c (Pᵀ * J * P.map c) (P'ᵀ * J' * P'.map c) z z' := by
  have hm : (P * z' * P'ᵀ).map c = P.map c * z'.map c * (P'.map c)ᵀ := by
    rw [show (P * z' * P'ᵀ).map c = (P * z').map c * P'ᵀ.map c from Matrix.map_mul (f := c.toRingHom),
      show (P * z').map c = P.map c * z'.map c from Matrix.map_mul (f := c.toRingHom)]
    rfl
  rw [hTens_eq_trace, hTens_eq_trace, hm]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Simplify using `[hTens, Fintype.sum_sum_type, Fin.sum_univ_two, Finset.mul_sum]`. Simplify using `only [mul_assoc, mul_left_comm η]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hTens_plane_left (J : Matrix α α S) (η : S) (J' : Matrix β β S) (z z' : Matrix (α ⊕ Fin 2) β S) :
    hTens c (Matrix.fromBlocks J 0 0 !![0, 1; η, 0]) J' z z' =
      η * ∑ j, ∑ l, z (.inr 1) j * J' j l * c (z' (.inr 0) l) + ∑ j, ∑ l, z (.inr 0) j * J' j l * c (z' (.inr 1) l) +
        hTens c J J' (z.submatrix .inl id) (z'.submatrix .inl id) := by
  simp [hTens, Fintype.sum_sum_type, Fin.sum_univ_two, Finset.mul_sum]
  simp only [mul_assoc, mul_left_comm η]
  ring

/- English proof (translation)
Simplify using `[hTens, Fintype.sum_sum_type, Fin.sum_univ_two, Finset.mul_sum, Finset.sum_add_distrib]`. Simplify using `only [mul_assoc, mul_left_comm η]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hTens_plane_right (J : Matrix α α S) (η : S) (J' : Matrix β β S) (z z' : Matrix α (β ⊕ Fin 2) S) :
    hTens c J (Matrix.fromBlocks J' 0 0 !![0, 1; η, 0]) z z' =
      η * ∑ i, ∑ k, z i (.inr 1) * J i k * c (z' k (.inr 0)) + ∑ i, ∑ k, z i (.inr 0) * J i k * c (z' k (.inr 1)) +
        hTens c J J' (z.submatrix id .inl) (z'.submatrix id .inl) := by
  simp [hTens, Fintype.sum_sum_type, Fin.sum_univ_two, Finset.mul_sum, Finset.sum_add_distrib]
  simp only [mul_assoc, mul_left_comm η]
  ring

/- English proof (translation)
Simplify using `only [map_sum, map_mul, hc, hJ, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring`.
-/
theorem conj_pair (hc : ∀ z, c (c z) = z) {J : Matrix α α S} {η : S} (hJ : ∀ i j, c (J j i) = η * J i j) (u w : α → S) :
    c (∑ i, ∑ k, u i * J i k * c (w k)) = η * ∑ i, ∑ k, w i * J i k * c (u k) := by
  simp only [map_sum, map_mul, hc, hJ, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

end Alg

section Plane

variable {m m₁ i₀ i₁ : ℕ} {Y : Spc F E m} {Y₁ : Spc F E m₁} {B : Base F E} {H : Plane E m m₁}

def frame (H : Plane E m m₁) : Matrix (Fin m) (Fin m₁ ⊕ Fin 2) E := Matrix.fromCols H.ι (Matrix.of fun i => ![H.x i, H.y i])

omit [NumberField F] [Algebra F E] in
/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[frame, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem frame_mulVec (H : Plane E m m₁) (w : Fin m₁ ⊕ Fin 2 → E) :
    frame H *ᵥ w = w (.inr 0) • H.x + H.ι *ᵥ (fun i => w (.inl i)) + w (.inr 1) • H.y := by
  funext i
  simp [frame, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

/- English proof (translation)
Establish `h1 : ∀ z ∈ Y.L, ∃ w, frame H *ᵥ w = z ∧ (fun i => w (.inl i)) ∈ Y₁.L ∧ w (.inr 0) • H.x ∈ Y.L ∧ w (.inr 1) • H.y ∈ Y.L` using `fun z hz => by`. Take `⟨s, t, u, hs, ht, hu, rfl⟩` from `hH.split z hz`. Conclude with `⟨Sum.elim u ![s, t], frame_mulVec H _, hu, hs, ht⟩`. Establish `h2 : LinearMap.range (frame H).mulVecLin = ⊤`. Rewrite using `[eq_top_iff, ← hL.span_eq_top, Submodule.span_le]`.

Introduce `z hz`. Take `⟨w, hw, -⟩` from `h1 z hz`. Conclude with `⟨w, hw⟩`. Use `choose f hf using fun j : Fin m => LinearMap.range_eq_top.1 h2 (Pi.single j 1)`. Establish `h3 : frame H * (Matrix.of f)ᵀ = 1`.

Use extensionality with `i j`. Rewrite using `[Matrix.one_apply, ← Pi.single_apply j (1 : E) i, ← hf j]`. Both sides reduce to the same expression. Establish `h4` using `(Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [hH.rank])).1 h3`. Use `⟨_, h3, h4, fun u hu => ?_⟩` and prove the remaining obligations.

Take `⟨w, rfl, hw⟩` from `h1 u hu`. Rewrite using `[Matrix.mulVec_mulVec, h4, Matrix.one_mulVec]` and apply the resulting hypothesis.
-/
theorem exists_frame_inv (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) (hL : Y.L.IsLattice E) :
    ∃ Q : Matrix (Fin m₁ ⊕ Fin 2) (Fin m) E, frame H * Q = 1 ∧ Q * frame H = 1 ∧ ∀ u ∈ Y.L,
      (fun i => (Q *ᵥ u) (.inl i)) ∈ Y₁.L ∧ (Q *ᵥ u) (.inr 0) • H.x ∈ Y.L ∧ (Q *ᵥ u) (.inr 1) • H.y ∈ Y.L := by
  have h1 : ∀ z ∈ Y.L, ∃ w, frame H *ᵥ w = z ∧ (fun i => w (.inl i)) ∈ Y₁.L ∧ w (.inr 0) • H.x ∈ Y.L ∧
      w (.inr 1) • H.y ∈ Y.L := fun z hz => by
    obtain ⟨s, t, u, hs, ht, hu, rfl⟩ := hH.split z hz
    exact ⟨Sum.elim u ![s, t], frame_mulVec H _, hu, hs, ht⟩
  have h2 : LinearMap.range (frame H).mulVecLin = ⊤ := by
    rw [eq_top_iff, ← hL.span_eq_top, Submodule.span_le]
    intro z hz
    obtain ⟨w, hw, -⟩ := h1 z hz
    exact ⟨w, hw⟩
  choose f hf using fun j : Fin m => LinearMap.range_eq_top.1 h2 (Pi.single j 1)
  have h3 : frame H * (Matrix.of f)ᵀ = 1 := by
    ext i j
    rw [Matrix.one_apply, ← Pi.single_apply j (1 : E) i, ← hf j]
    rfl
  have h4 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [hH.rank])).1 h3
  refine ⟨_, h3, h4, fun u hu => ?_⟩
  obtain ⟨w, rfl, hw⟩ := h1 u hu
  rwa [Matrix.mulVec_mulVec, h4, Matrix.one_mulVec]

/- English proof (translation)
Establish `hf : ∀ u w, form σ Y.J u w = ∑ i, ∑ k, u i * Y.J i k * σ (w k)` using `fun u w => by`. Simplify using `[form, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]`. Establish `hs : ∀ u w, form σ Y.J w u = η * σ (form σ Y.J u w)` using `fun u w => by`. Rewrite using `[hf u w, conj_pair σ (conj_conj hB) hJ, ← mul_assoc, hη, one_mul, hf]`. Establish `he : ∀ a b, ((frame H)ᵀ * Y.J * (frame H).map σ) a b = form σ Y.J (fun i => frame H i a) fun i => frame H i b` using `fun a b => by`.

Simplify using `only [hf, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Conclude with `Finset.sum_comm`. Establish `hi : ∀ j, (fun i => frame H i (.inl j)) = H.ι *ᵥ Pi.single j 1` using `fun j => by`. Use function extensionality and compare the values at `i`. Simplify using `[frame]`.

Establish `hx : (fun i => frame H i (.inr 0)) = H.x` using `rfl`. Establish `hy : (fun i => frame H i (.inr 1)) = H.y` using `rfl`. Use extensionality with `(a | a) (b | b)`. Rewrite using `[Matrix.fromBlocks_apply₁₁, ← hH.gram]`. Both sides reduce to the same expression.

Rewrite using `[he, hi] fin_cases b`. Conclude with `(hH.orth _).1`. Conclude with `(hH.orth _).2`. Rewrite using `[he, hi, hs] fin_cases a`. Conclude with `(congrArg (fun t => η * σ t) (hH.orth _).1).trans (by simp)`.

Conclude with `(congrArg (fun t => η * σ t) (hH.orth _).2).trans (by simp)`. Apply the tactic sequence `rw [he] fin_cases a <;> fin_cases b`. Conclude with `hH.xx`. Conclude with `hH.xy`. Conclude with `(hs H.x H.y).trans (by simp [hH.xy])`.

Conclude with `hH.yy`.
-/
theorem frame_gram (hB : B.IsGood σ) (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) {η : E} (hη : η * η = 1)
    (hJ : ∀ i j, σ (Y.J j i) = η * Y.J i j) :
    (frame H)ᵀ * Y.J * (frame H).map σ = Matrix.fromBlocks Y₁.J 0 0 !![0, 1; η, 0] := by
  have hf : ∀ u w, form σ Y.J u w = ∑ i, ∑ k, u i * Y.J i k * σ (w k) := fun u w => by
    simp [form, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hs : ∀ u w, form σ Y.J w u = η * σ (form σ Y.J u w) := fun u w => by
    rw [hf u w, conj_pair σ (conj_conj hB) hJ, ← mul_assoc, hη, one_mul, hf]
  have he : ∀ a b, ((frame H)ᵀ * Y.J * (frame H).map σ) a b = form σ Y.J (fun i => frame H i a) fun i => frame H i b :=
    fun a b => by
      simp only [hf, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
      exact Finset.sum_comm
  have hi : ∀ j, (fun i => frame H i (.inl j)) = H.ι *ᵥ Pi.single j 1 := fun j => by
    funext i; simp [frame]
  have hx : (fun i => frame H i (.inr 0)) = H.x := rfl
  have hy : (fun i => frame H i (.inr 1)) = H.y := rfl
  ext (a | a) (b | b)
  · rw [Matrix.fromBlocks_apply₁₁, ← hH.gram]; rfl
  · rw [he, hi]
    fin_cases b
    · exact (hH.orth _).1
    · exact (hH.orth _).2
  · rw [he, hi, hs]
    fin_cases a
    · exact (congrArg (fun t => η * σ t) (hH.orth _).1).trans (by simp)
    · exact (congrArg (fun t => η * σ t) (hH.orth _).2).trans (by simp)
  · rw [he]
    fin_cases a <;> fin_cases b
    · exact hH.xx
    · exact hH.xy
    · exact (hs H.x H.y).trans (by simp [hH.xy])
    · exact hH.yy

def mask (S : Type) [CommRing S] (m₁ : ℕ) (c s t : ℤ) : Matrix (Fin m₁ ⊕ Fin 2) (Fin m₁ ⊕ Fin 2) S :=
  Matrix.diagonal (Sum.elim (fun _ => (c : S)) ![(s : S), (t : S)])

/- English proof (translation)
Introduce `u hu` and use `by obtain ⟨h1, h2, h3⟩ := hQ u hu rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, frame_mulVec] refine add_mem (add_mem ?_ ((hH.low _).1 ?_)) ?_ · convert zsmul_mem h2 s using 1 simp [mask, Matrix.mulVec_diagonal, mul_smul, Int.cast_smul_eq_zsmul] · convert zsmul_mem h1 c usi …`.
-/
theorem mask_mem (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) {Q : Matrix (Fin m₁ ⊕ Fin 2) (Fin m) E} (hQ : ∀ u ∈ Y.L,
    (fun i => (Q *ᵥ u) (.inl i)) ∈ Y₁.L ∧ (Q *ᵥ u) (.inr 0) • H.x ∈ Y.L ∧ (Q *ᵥ u) (.inr 1) • H.y ∈ Y.L) (c s t : ℤ) :
    ∀ u ∈ Y.L, (frame H * mask E m₁ c s t * Q) *ᵥ u ∈ Y.L := fun u hu => by
  obtain ⟨h1, h2, h3⟩ := hQ u hu
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, frame_mulVec]
  refine add_mem (add_mem ?_ ((hH.low _).1 ?_)) ?_
  · convert zsmul_mem h2 s using 1
    simp [mask, Matrix.mulVec_diagonal, mul_smul, Int.cast_smul_eq_zsmul]
  · convert zsmul_mem h1 c using 1
    funext i
    simp [mask, Matrix.mulVec_diagonal]
  · convert zsmul_mem h3 t using 1
    simp [mask, Matrix.mulVec_diagonal, mul_smul, Int.cast_smul_eq_zsmul]

end Plane

/- English proof (translation)
The claim follows from `Matrix.map_mul`.
-/
theorem incM_mul {α β γ : Type} [Fintype β] (A : Matrix α β E) (C : Matrix β γ E) : incM F (A * C) = incM F A * incM F C :=
  Matrix.map_mul

/- English proof (translation)
Rewrite using `[incM, mask, Matrix.diagonal_map (map_zero _)]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Break down `a with a | a` into its components or cases. Simplify using the standard rewrite rules.

Apply the tactic sequence `fin_cases a <;> simp`.
-/
theorem incM_mask (m₁ : ℕ) (c s t : ℤ) : incM F (mask E m₁ c s t) = mask (AE F E) m₁ c s t := by
  rw [incM, mask, Matrix.diagonal_map (map_zero _)]
  congr 1
  funext a
  rcases a with a | a
  · simp
  · fin_cases a <;> simp

/- English proof (translation)
Proceed by induction on `hγ using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, hav, x, hx, y, hy, rfl⟩` from `hz`. Use `AddSubgroup.subset_closure ⟨a, ha, hav, _, hA x hx, _, hA' y hy, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul, ← incM_mul, show (incM F A')ᵀ = incM F A'ᵀ from rfl, ← incM_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]`.

Consider the case `zero => rw [Matrix.mul_zero, Matrix.zero_mul]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.add_mul]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [Matrix.mul_neg, Matrix.neg_mul]`.

Conclude with `neg_mem hx`.
-/
theorem lat_map {A : Matrix (Fin n₁) (Fin n) E} {A' : Matrix (Fin d₁) (Fin d) E} (hA : ∀ u ∈ X.L, A *ᵥ u ∈ X₁.L)
    (hA' : ∀ u ∈ W.L, A' *ᵥ u ∈ W₁.L) {v : Pl F} {γ : Matrix (Fin n) (Fin d) (AE F E)} (hγ : γ ∈ latAtV X W v) :
    incM F A * γ * (incM F A')ᵀ ∈ latAtV X₁ W₁ v := by
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hav, x, hx, y, hy, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, ha, hav, _, hA x hx, _, hA' y hy, ?_⟩
    rw [Matrix.mul_smul, Matrix.smul_mul, ← incM_mul, show (incM F A')ᵀ = incM F A'ᵀ from rfl, ← incM_mul,
      Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
  | zero => rw [Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mul_neg, Matrix.neg_mul]; exact neg_mem hx

end GlobalTheory.ThK.Adapt

end
