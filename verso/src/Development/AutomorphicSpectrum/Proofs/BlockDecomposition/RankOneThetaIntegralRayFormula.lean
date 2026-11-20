import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaTestFunctionRayAsymptoticStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RayNormAndModuleFormulaStatement

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.UnitBd

def cnt {F : Type} [Field F] [NumberField F] (θ : ℝ →+* Ainf F) (ι : Type) (K : Set (ι → Ainf F)) (ε : ℝ) : ℝ≥0∞ :=
  ∑' _y : {y : ι → F // (∀ v : HeightOneSpectrum (𝓞 F), ∀ i, algebraMap F (Fv F v) (y i) ∈ v.adicCompletionIntegers F) ∧
    (fun i => θ ε * algebraMap F (Ainf F) (y i)) ∈ K}, (1 : ℝ≥0∞)

/- English proof (translation)
Introduce `hEq F _ _ hF θ hθ li lam hli hlam ι _ K hK`. Take `⟨_, _, _, _, -⟩` from `GlobalTheory.T.infinite_adeles_local_ring_totally_real F hF`. Establish `: BorelSpace (Ainf F)` using `⟨rfl⟩`. Use `haveI := hli.1`. Take `⟨f, hf1, -, hfc, hf01⟩` from `exists_continuous_one_zero_of_isCompact (hK.union (isCompact_singleton (x := (0 : ι → Ainf F)))) isClosed_empty (Set.disjoint_empty _)`.

Establish `hL` using `hEq F hF θ hθ li lam hli hlam ι ∅ (f : (ι → Ainf F) → ℝ) (fun _ _ => 0) f.continuous hfc (by simp)`. Simplify using `only [Finset.prod_empty, mul_one] at hL`. Use `set L := ∫ y, f y ∂(Measure.pi fun _ : ι => li) with hLdef`. Establish `hLpos : 0 < L`. Use `Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero f.continuous hfc (fun x => (hf01 x).1) (x := 0) ?_` and prove the remaining obligations.

Rewrite using `[hf1 (Or.inr rfl)]`. Conclude with `one_ne_zero`. Use `⟨Real.toNNReal (L + 1), ?_⟩` and prove the remaining obligations. Use `filter_upwards [hL.eventually (lt_mem_nhds (half_lt_self hLpos)), hL.eventually (gt_mem_nhds (lt_add_one L)), self_mem_nhdsWithin] with ε h1 h2 h3`. Use `set u : {x : ι → F // ∀ v, v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 F))) → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F} → ℝ := fun x => f fun i => θ ε * algebraMap F (Ainf F) (x.1 i) with hu`.

Establish `hu0 : ∀ x, 0 ≤ u x` using `fun x => (hf01 _).1`. Establish `hsum : Summable u`. Assume the negation of the conclusion as `hns`. Establish `e0 : ∑' x, u x = 0` using `tsum_eq_zero_of_not_summable hns`. Simplify using `only [hu] at e0`.

Rewrite `h1` using `[e0, mul_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hle : cnt θ ι K ε ≤ ∑' x, ENNReal.ofReal (u x)`. Establish `hinj : Function.Injective fun y : {y : ι → F // (∀ v : HeightOneSpectrum (𝓞 F), ∀ i, algebraMap F (Fv F v) (y i) ∈ v.adicCompletionIntegers F) ∧ (fun i => θ ε * algebraMap F (Ainf F) (y i)) ∈ K} => (⟨y.1, fun v _ i => y.2.1 v i⟩ : {x : ι → F // ∀ v, v ∉ (∅ : Finset (HeightOneSpec …` using `fun y y' e => Subtype.ext (Subtype.mk.inj e)`. Use `le_trans (le_of_eq (tsum_congr fun y => ?_)) (ENNReal.tsum_comp_le_tsum_of_injective hinj fun x => ENNReal.ofReal (u x))` and prove the remaining obligations.

Simplify using `only [hu]`. Rewrite using `[hf1 (Or.inl y.2.2)]`. Simplify using the standard rewrite rules. Rewrite `hle` using `[← ENNReal.ofReal_tsum_of_nonneg hu0 hsum]`. Establish `hpos : 0 ≤ ε ^ (Module.finrank ℚ F * Fintype.card ι)` using `pow_nonneg (le_of_lt h3) _`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem count : PositivityTheory.Rg.Mass.Equi → ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ →
    ∀ (li : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf li → (∀ v, IsStdV v (lam v)) →
    ∀ (ι : Type) [Fintype ι] (K : Set (ι → Ainf F)), IsCompact K → ∃ B : ℝ≥0, ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ENNReal.ofReal (ε ^ (Module.finrank ℚ F * Fintype.card ι)) * cnt θ ι K ε ≤ B := by
  intro hEq F _ _ hF θ hθ li lam hli hlam ι _ K hK
  obtain ⟨_, _, _, _, -⟩ := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hF
  have : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI := hli.1
  obtain ⟨f, hf1, -, hfc, hf01⟩ := exists_continuous_one_zero_of_isCompact
    (hK.union (isCompact_singleton (x := (0 : ι → Ainf F)))) isClosed_empty (Set.disjoint_empty _)
  have hL := hEq F hF θ hθ li lam hli hlam ι ∅ (f : (ι → Ainf F) → ℝ) (fun _ _ => 0) f.continuous hfc (by simp)
  simp only [Finset.prod_empty, mul_one] at hL
  set L := ∫ y, f y ∂(Measure.pi fun _ : ι => li) with hLdef
  have hLpos : 0 < L := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero f.continuous hfc (fun x => (hf01 x).1)
      (x := 0) ?_
    rw [hf1 (Or.inr rfl)]
    exact one_ne_zero
  refine ⟨Real.toNNReal (L + 1), ?_⟩
  filter_upwards [hL.eventually (lt_mem_nhds (half_lt_self hLpos)), hL.eventually (gt_mem_nhds (lt_add_one L)),
    self_mem_nhdsWithin] with ε h1 h2 h3
  set u : {x : ι → F // ∀ v, v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 F))) → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F} → ℝ :=
    fun x => f fun i => θ ε * algebraMap F (Ainf F) (x.1 i) with hu
  have hu0 : ∀ x, 0 ≤ u x := fun x => (hf01 _).1
  have hsum : Summable u := by
    by_contra hns
    have e0 : ∑' x, u x = 0 := tsum_eq_zero_of_not_summable hns
    simp only [hu] at e0
    rw [e0, mul_zero] at h1
    linarith
  have hle : cnt θ ι K ε ≤ ∑' x, ENNReal.ofReal (u x) := by
    have hinj : Function.Injective fun y : {y : ι → F // (∀ v : HeightOneSpectrum (𝓞 F), ∀ i, algebraMap F (Fv F v) (y i) ∈ v.adicCompletionIntegers F) ∧
      (fun i => θ ε * algebraMap F (Ainf F) (y i)) ∈ K} =>
        (⟨y.1, fun v _ i => y.2.1 v i⟩ : {x : ι → F // ∀ v, v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 F))) → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F}) :=
      fun y y' e => Subtype.ext (Subtype.mk.inj e)
    refine le_trans (le_of_eq (tsum_congr fun y => ?_)) (ENNReal.tsum_comp_le_tsum_of_injective hinj fun x => ENNReal.ofReal (u x))
    simp only [hu]
    rw [hf1 (Or.inl y.2.2)]
    simp
  rw [← ENNReal.ofReal_tsum_of_nonneg hu0 hsum] at hle
  have hpos : 0 ≤ ε ^ (Module.finrank ℚ F * Fintype.card ι) := pow_nonneg (le_of_lt h3) _
  calc _ ≤ ENNReal.ofReal (ε ^ (Module.finrank ℚ F * Fintype.card ι)) * ENNReal.ofReal (∑' x, u x) := mul_le_mul' le_rfl hle
    _ = ENNReal.ofReal (ε ^ (Module.finrank ℚ F * Fintype.card ι) * ∑' x, u x) := (ENNReal.ofReal_mul hpos).symm
    _ ≤ ENNReal.ofReal (L + 1) := ENNReal.ofReal_le_ofReal (le_of_lt h2)
    _ = _ := rfl

def box (F : Type) [Field F] [NumberField F] (ι : Type) (ρ : ℝ) : Set (ι → Ainf F) :=
  {x | ∀ i w, ‖x i w‖ ≤ ρ}

/- English proof (translation)
Establish `hn` using `(GlobalTheory.T.ray_norm_and_module_formula F hF θ hθ r hr).1`. Establish `hm : ∀ y : ι → F, (fun i => θ ε * algebraMap F (Ainf F) (y i)) ∈ box F ι ρ → (fun i => θ δ * algebraMap F (Ainf F) (y i)) ∈ box F ι ρ` using `fun y h i w => by`. Establish `e : ∀ t : ℝ, ‖(θ t * algebraMap F (Ainf F) (y i)) w‖ = |t| * ‖algebraMap F (Ainf F) (y i) w‖` using `fun t => by`. Express the relevant statement in the definitionally equal form `‖θ t w * algebraMap F (Ainf F) (y i) w‖ = _`. Rewrite using `[norm_mul, hn]`.

Establish `h1 : ‖(θ ε * algebraMap F (Ainf F) (y i)) w‖ ≤ ρ` using `h i w`. Express the relevant statement in the definitionally equal form `‖(θ δ * algebraMap F (Ainf F) (y i)) w‖ ≤ ρ`. Rewrite `h1`, the goal using `[e]`. Rewrite using `[abs_of_pos hδ]`. Rewrite `h1` using `[abs_of_pos (hδ.trans_le hδε)]`.

Conclude with `(mul_le_mul_of_nonneg_right hδε (norm_nonneg _)).trans h1`. Establish `hinj : Function.Injective fun y : {y : ι → F // (∀ v : HeightOneSpectrum (𝓞 F), ∀ i, algebraMap F (Fv F v) (y i) ∈ v.adicCompletionIntegers F) ∧ (fun i => θ ε * algebraMap F (Ainf F) (y i)) ∈ box F ι ρ} => (⟨y.1, y.2.1, hm y.1 y.2.2⟩ : {y : ι → F // (∀ v : HeightOneSpectrum (𝓞 F) …` using `fun y y' e => Subtype.ext (Subtype.mk.inj e)`. Conclude with `ENNReal.tsum_comp_le_tsum_of_injective hinj fun _ => (1 : ℝ≥0∞)`.
-/
theorem cnt_anti {F : Type} [Field F] [NumberField F] (hF : IsTotallyReal F) (θ : ℝ →+* Ainf F) (hθ : Continuous θ)
    (r : ℝ → (AF F)ˣ) (hr : IsRay θ r) (ι : Type) (ρ : ℝ) {δ ε : ℝ} (hδ : 0 < δ) (hδε : δ ≤ ε) :
    cnt θ ι (box F ι ρ) ε ≤ cnt θ ι (box F ι ρ) δ := by
  have hn := (GlobalTheory.T.ray_norm_and_module_formula F hF θ hθ r hr).1
  have hm : ∀ y : ι → F, (fun i => θ ε * algebraMap F (Ainf F) (y i)) ∈ box F ι ρ →
      (fun i => θ δ * algebraMap F (Ainf F) (y i)) ∈ box F ι ρ := fun y h i w => by
    have e : ∀ t : ℝ, ‖(θ t * algebraMap F (Ainf F) (y i)) w‖ = |t| * ‖algebraMap F (Ainf F) (y i) w‖ := fun t => by
      change ‖θ t w * algebraMap F (Ainf F) (y i) w‖ = _
      rw [norm_mul, hn]
    have h1 : ‖(θ ε * algebraMap F (Ainf F) (y i)) w‖ ≤ ρ := h i w
    change ‖(θ δ * algebraMap F (Ainf F) (y i)) w‖ ≤ ρ
    rw [e] at h1 ⊢
    rw [abs_of_pos hδ]
    rw [abs_of_pos (hδ.trans_le hδε)] at h1
    exact (mul_le_mul_of_nonneg_right hδε (norm_nonneg _)).trans h1
  have hinj : Function.Injective fun y : {y : ι → F // (∀ v : HeightOneSpectrum (𝓞 F), ∀ i, algebraMap F (Fv F v) (y i) ∈ v.adicCompletionIntegers F) ∧
      (fun i => θ ε * algebraMap F (Ainf F) (y i)) ∈ box F ι ρ} =>
      (⟨y.1, y.2.1, hm y.1 y.2.2⟩ : {y : ι → F // (∀ v : HeightOneSpectrum (𝓞 F), ∀ i, algebraMap F (Fv F v) (y i) ∈ v.adicCompletionIntegers F) ∧
      (fun i => θ δ * algebraMap F (Ainf F) (y i)) ∈ box F ι ρ}) :=
    fun y y' e => Subtype.ext (Subtype.mk.inj e)
  exact ENNReal.tsum_comp_le_tsum_of_injective hinj fun _ => (1 : ℝ≥0∞)

/- English proof (translation)
Take `⟨_, _, _, _, -⟩` from `GlobalTheory.T.infinite_adeles_local_ring_totally_real F hF`. Establish `e : box F ι ρ = Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall 0 ρ`. Use extensionality with `x`. Conclude with `⟨fun h i _ w _ => mem_closedBall_zero_iff.2 (h i w), fun h i w => mem_closedBall_zero_iff.1 (h i (Set.mem_univ _) w (Set.mem_univ _))⟩`. Rewrite using `[e]`.

Conclude with `isCompact_univ_pi fun _ => isCompact_univ_pi fun w => isCompact_closedBall _ _`.
-/
theorem isCompact_box {F : Type} [Field F] [NumberField F] (hF : IsTotallyReal F) (ι : Type) (ρ : ℝ) :
    IsCompact (box F ι ρ) := by
  obtain ⟨_, _, _, _, -⟩ := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hF
  have e : box F ι ρ = Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall 0 ρ := by
    ext x
    exact ⟨fun h i _ w _ => mem_closedBall_zero_iff.2 (h i w),
      fun h i w => mem_closedBall_zero_iff.1 (h i (Set.mem_univ _) w (Set.mem_univ _))⟩
  rw [e]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun w => isCompact_closedBall _ _

/- English proof (translation)
Establish `hN0 : (N : F) ≠ 0` using `Nat.cast_ne_zero.2 hN.ne'`. Use `set Y := fun X : Fin 1 → Fin 1 → E => fun p : Fin 1 × Fin 1 × Fin 2 => (N : F) * b.repr (X p.1 p.2.1) p.2.2 with hY`. Establish `hYi : Function.Injective Y` using `fun X X' e => by`. Use function extensionality and compare the values at `a i`. Use `b.repr.injective (Finsupp.ext fun k => ?_)` and prove the remaining obligations.

Establish `h1` using `congrFun e (a, i, k)`. Conclude with `mul_left_cancel₀ hN0 h1`. Use `set g : ({X : Fin 1 → Fin 1 → E | X ≠ 0} : Set _) → ℝ≥0∞ := fun X => Psi φ A (fun a i => (y : AF F ⊗[F] E) * inclR (AF F) (X.1 a i)) with hg`. Use `set T : Set ({X : Fin 1 → Fin 1 → E | X ≠ 0} : Set _) := {X | g X ≠ 0} with hTdef`. Establish `hPsi : ∀ Z : Fin 1 → Fin 1 → AF F ⊗[F] E, Psi φ A Z ≤ Real.toNNReal B0` using `fun Z => by`.

Unfold `Psi`. Use `(Set.indicator_le_self' (fun _ _ => bot_le) _).trans ?_` and prove the remaining obligations. Rewrite using `[ENNReal.ofReal, ENNReal.coe_le_coe]`. Conclude with `Real.toNNReal_le_toNNReal ((le_abs_self _).trans (hB0 _))`. Establish `e1 : Th φ A y = ∑' X : T, g X.1`.

Rewrite using `[tsum_subtype T g]`. Use `tsum_congr fun X => ?_` and prove the remaining obligations. Distinguish the cases in `hX : X ∈ T`. Rewrite using `[Set.indicator_of_mem hX]`. Rewrite using `[Set.indicator_of_notMem hX]`.

Conclude with `not_not.1 hX`. Rewrite using `[e1, cnt, ← ENNReal.tsum_mul_left]`. Establish `hmap : ∀ X : T, (∀ v : HeightOneSpectrum (𝓞 F), ∀ i, algebraMap F (Fv F v) (Y X.1.1 i) ∈ v.adicCompletionIntegers F) ∧ (fun i => θ ε * algebraMap F (Ainf F) (Y X.1.1 i)) ∈ box F _ ρ` using `fun X => by`. Take `⟨h2, h3⟩` from `hbox X.1.1 X.2`. Conclude with `⟨fun v i => h2 i v, fun i w => h3 i w⟩`.

Establish `hinj : Function.Injective fun X : T => (⟨Y X.1.1, hmap X⟩ : {y : Fin 1 × Fin 1 × Fin 2 → F // (∀ v : HeightOneSpectrum (𝓞 F), ∀ i, algebraMap F (Fv F v) (y i) ∈ v.adicCompletionIntegers F) ∧ (fun i => θ ε * algebraMap F (Ainf F) (y i)) ∈ box F _ ρ})` using `fun X X' e => Subtype.ext (Subtype.ext (hYi (congrArg Subtype.val e)))`. Use `le_trans (ENNReal.tsum_le_tsum fun X => ?_) (ENNReal.tsum_comp_le_tsum_of_injective hinj fun _ => (Real.toNNReal B0 : ℝ≥0∞) * 1)` and prove the remaining obligations. Rewrite using `[mul_one]`. Conclude with `hPsi _`.
-/
theorem Th_le {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (b : Module.Basis (Fin 2) F E)
    (θ : ℝ →+* Ainf F) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)) (B0 : ℝ) (hB0 : ∀ x, ‖φ x‖ ≤ B0)
    (N : ℕ) (hN : 0 < N) (ρ ε : ℝ) (y : (AF F ⊗[F] E)ˣ)
    (hbox : ∀ X : Fin 1 → Fin 1 → E, Psi φ A (fun a i => (y : AF F ⊗[F] E) * inclR (AF F) (X a i)) ≠ 0 →
      (∀ (p : Fin 1 × Fin 1 × Fin 2) (v : HeightOneSpectrum (𝓞 F)),
        algebraMap F (Fv F v) ((N : F) * b.repr (X p.1 p.2.1) p.2.2) ∈ v.adicCompletionIntegers F) ∧
      ∀ (p : Fin 1 × Fin 1 × Fin 2) (w : InfinitePlace F),
        ‖(θ ε * algebraMap F (Ainf F) ((N : F) * b.repr (X p.1 p.2.1) p.2.2)) w‖ ≤ ρ) :
    Th φ A y ≤ Real.toNNReal B0 * cnt θ (Fin 1 × Fin 1 × Fin 2) (box F _ ρ) ε := by
  have hN0 : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  set Y := fun X : Fin 1 → Fin 1 → E => fun p : Fin 1 × Fin 1 × Fin 2 => (N : F) * b.repr (X p.1 p.2.1) p.2.2 with hY
  have hYi : Function.Injective Y := fun X X' e => by
    funext a i
    refine b.repr.injective (Finsupp.ext fun k => ?_)
    have h1 := congrFun e (a, i, k)
    exact mul_left_cancel₀ hN0 h1
  set g : ({X : Fin 1 → Fin 1 → E | X ≠ 0} : Set _) → ℝ≥0∞ :=
    fun X => Psi φ A (fun a i => (y : AF F ⊗[F] E) * inclR (AF F) (X.1 a i)) with hg
  set T : Set ({X : Fin 1 → Fin 1 → E | X ≠ 0} : Set _) := {X | g X ≠ 0} with hTdef
  have hPsi : ∀ Z : Fin 1 → Fin 1 → AF F ⊗[F] E, Psi φ A Z ≤ Real.toNNReal B0 := fun Z => by
    unfold Psi
    refine (Set.indicator_le_self' (fun _ _ => bot_le) _).trans ?_
    rw [ENNReal.ofReal, ENNReal.coe_le_coe]
    exact Real.toNNReal_le_toNNReal ((le_abs_self _).trans (hB0 _))
  have e1 : Th φ A y = ∑' X : T, g X.1 := by
    rw [tsum_subtype T g]
    refine tsum_congr fun X => ?_
    by_cases hX : X ∈ T
    · rw [Set.indicator_of_mem hX]
    · rw [Set.indicator_of_notMem hX]
      exact not_not.1 hX
  rw [e1, cnt, ← ENNReal.tsum_mul_left]
  have hmap : ∀ X : T, (∀ v : HeightOneSpectrum (𝓞 F), ∀ i,
      algebraMap F (Fv F v) (Y X.1.1 i) ∈ v.adicCompletionIntegers F) ∧
        (fun i => θ ε * algebraMap F (Ainf F) (Y X.1.1 i)) ∈ box F _ ρ := fun X => by
    obtain ⟨h2, h3⟩ := hbox X.1.1 X.2
    exact ⟨fun v i => h2 i v, fun i w => h3 i w⟩
  have hinj : Function.Injective fun X : T => (⟨Y X.1.1, hmap X⟩ : {y : Fin 1 × Fin 1 × Fin 2 → F // (∀ v : HeightOneSpectrum (𝓞 F), ∀ i,
      algebraMap F (Fv F v) (y i) ∈ v.adicCompletionIntegers F) ∧
        (fun i => θ ε * algebraMap F (Ainf F) (y i)) ∈ box F _ ρ}) := fun X X' e =>
    Subtype.ext (Subtype.ext (hYi (congrArg Subtype.val e)))
  refine le_trans (ENNReal.tsum_le_tsum fun X => ?_) (ENNReal.tsum_comp_le_tsum_of_injective hinj
    fun _ => (Real.toNNReal B0 : ℝ≥0∞) * 1)
  rw [mul_one]
  exact hPsi _

/- English proof (translation)
Introduce `hEq F E _ _ _ _ _ σ hcm J hJ d b li lam hli hlam θ hθ r hr S φ A hT K hK ε₁`. Take `⟨N, ρ, hN, hbox⟩` from `GlobalTheory.T.theta_test_function_ray_asymptotic F E σ hcm J hJ d b θ r hr S φ A hT K hK`. Establish `hd : d = 2`. Use `Module.finrank_eq_card_basis b` as an intermediate fact. Rewrite `this` using `[hcm.2.2.1]`.

Simplify using `using this.symm`. Substitute `hd` using the available equality. Take `⟨B, hB⟩` from `count hEq F hcm.1 θ hθ li lam hli hlam (Fin 1 × Fin 1 × Fin 2) (box F _ ρ) (isCompact_box hcm.1 _ ρ)`. Take `⟨B0, hB0⟩` from `hT.2.1.exists_bound_of_continuous hT.1`. Establish `e2 : Module.finrank ℚ F * Fintype.card (Fin 1 × Fin 1 × Fin 2) = 2 * Module.finrank ℚ F`.

Rewrite using `[show Fintype.card (Fin 1 × Fin 1 × Fin 2) = 2 from rfl, mul_comm]`. Rewrite `hB` using `[e2]`. Use `set m := 2 * Module.finrank ℚ F with hm`. Use `set c : ℝ → ℝ≥0∞ := cnt θ (Fin 1 × Fin 1 × Fin 2) (box F _ ρ) with hc`. Take `⟨ε₀, hε₀, hI⟩` from `(mem_nhdsGT_iff_exists_Ioo_subset).1 hB`.

Establish `hε₀' : (0 : ℝ) < ε₀` using `hε₀`. Use `set ε₂ := ε₀ / 2 with hε₂`. Establish `h2pos : 0 < ε₂` using `half_pos hε₀'`. Establish `h2 : ENNReal.ofReal (ε₂ ^ m) * c ε₂ ≤ B` using `hI ⟨h2pos, half_lt_self hε₀'⟩`. Use `set E2 : ℝ≥0 := Real.toNNReal (ε₂ ^ m) with hE2`.

Establish `hE2pos : E2 ≠ 0`. Simplify using `only [hE2, ne_eq, Real.toNNReal_eq_zero, not_le]`. Conclude with `pow_pos h2pos _`. Use `set D : ℝ≥0 := B + Real.toNNReal (ε₁ ^ m) * (E2⁻¹ * B) with hD`. Use `⟨Real.toNNReal B0 * D, fun k hk ε hε hε1 => ?_⟩` and prove the remaining obligations.

Establish `hTh` using `Th_le b θ φ A B0 hB0 N hN ρ ε (k * ofF (r ε)) fun X h => hbox k hk X ε hε h`. Establish `hcD : ENNReal.ofReal (ε ^ m) * c ε ≤ D`. Distinguish the cases in `hlt : ε < ε₀`. Establish `h1 : ENNReal.ofReal (ε ^ m) * c ε ≤ B` using `hI ⟨hε, hlt⟩`. Use `h1.trans ?_` and prove the remaining obligations.

Rewrite using `[ENNReal.coe_le_coe, hD]`. Conclude with `le_self_add`. Establish `hle : ε₂ ≤ ε` using `(half_le_self hε₀'.le).trans (not_lt.1 hlt)`. Establish `h3 : c ε ≤ c ε₂` using `cnt_anti hcm.1 θ hθ r hr _ ρ h2pos hle`. Establish `h4 : c ε₂ ≤ ((E2⁻¹ * B : ℝ≥0) : ℝ≥0∞)`.

Establish `e : c ε₂ = (E2 : ℝ≥0∞)⁻¹ * ((E2 : ℝ≥0∞) * c ε₂)`. Rewrite using `[← mul_assoc, ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.2 hE2pos) ENNReal.coe_ne_top, one_mul]`. Rewrite using `[e, ENNReal.coe_mul, ENNReal.coe_inv hE2pos]`. Conclude with `mul_le_mul' le_rfl h2`. Establish `h5 : ENNReal.ofReal (ε ^ m) ≤ (Real.toNNReal (ε₁ ^ m) : ℝ≥0∞)` using `ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hε.le hε1 m)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← ENNReal.coe_mul, ENNReal.coe_le_coe, hD]`. Conclude with `le_add_self`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem unit_bound : PositivityTheory.Rg.Mass.Equi → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Matrix (Fin 1) (Fin 1) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (li : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf li → (∀ v, IsStdV v (lam v)) → ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ r, IsRay θ r → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)), IsTest σ J b S φ A → ∀ K : Set (AF F ⊗[F] E)ˣ, IsCompact K → ∀ ε₁ : ℝ, ∃ C : ℝ≥0, ∀ k ∈ K, ∀ ε : ℝ, 0 < ε → ε ≤ ε₁ → ENNReal.ofReal (ε ^ (2 * Module.finrank ℚ F)) * Th φ A (k * ofF (r ε)) ≤ C := by
  intro hEq F E _ _ _ _ _ σ hcm J hJ d b li lam hli hlam θ hθ r hr S φ A hT K hK ε₁
  obtain ⟨N, ρ, hN, hbox⟩ := GlobalTheory.T.theta_test_function_ray_asymptotic F E σ hcm J hJ d b θ r hr S φ A hT K hK
  have hd : d = 2 := by
    have := Module.finrank_eq_card_basis b
    rw [hcm.2.2.1] at this
    simpa using this.symm
  subst hd
  obtain ⟨B, hB⟩ := count hEq F hcm.1 θ hθ li lam hli hlam (Fin 1 × Fin 1 × Fin 2) (box F _ ρ) (isCompact_box hcm.1 _ ρ)
  obtain ⟨B0, hB0⟩ := hT.2.1.exists_bound_of_continuous hT.1
  have e2 : Module.finrank ℚ F * Fintype.card (Fin 1 × Fin 1 × Fin 2) = 2 * Module.finrank ℚ F := by
    rw [show Fintype.card (Fin 1 × Fin 1 × Fin 2) = 2 from rfl, mul_comm]
  rw [e2] at hB
  set m := 2 * Module.finrank ℚ F with hm
  set c : ℝ → ℝ≥0∞ := cnt θ (Fin 1 × Fin 1 × Fin 2) (box F _ ρ) with hc
  obtain ⟨ε₀, hε₀, hI⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hB
  have hε₀' : (0 : ℝ) < ε₀ := hε₀
  set ε₂ := ε₀ / 2 with hε₂
  have h2pos : 0 < ε₂ := half_pos hε₀'
  have h2 : ENNReal.ofReal (ε₂ ^ m) * c ε₂ ≤ B := hI ⟨h2pos, half_lt_self hε₀'⟩
  set E2 : ℝ≥0 := Real.toNNReal (ε₂ ^ m) with hE2
  have hE2pos : E2 ≠ 0 := by
    simp only [hE2, ne_eq, Real.toNNReal_eq_zero, not_le]
    exact pow_pos h2pos _
  set D : ℝ≥0 := B + Real.toNNReal (ε₁ ^ m) * (E2⁻¹ * B) with hD
  refine ⟨Real.toNNReal B0 * D, fun k hk ε hε hε1 => ?_⟩
  have hTh := Th_le b θ φ A B0 hB0 N hN ρ ε (k * ofF (r ε)) fun X h => hbox k hk X ε hε h
  have hcD : ENNReal.ofReal (ε ^ m) * c ε ≤ D := by
    by_cases hlt : ε < ε₀
    · have h1 : ENNReal.ofReal (ε ^ m) * c ε ≤ B := hI ⟨hε, hlt⟩
      refine h1.trans ?_
      rw [ENNReal.coe_le_coe, hD]
      exact le_self_add
    · have hle : ε₂ ≤ ε := (half_le_self hε₀'.le).trans (not_lt.1 hlt)
      have h3 : c ε ≤ c ε₂ := cnt_anti hcm.1 θ hθ r hr _ ρ h2pos hle
      have h4 : c ε₂ ≤ ((E2⁻¹ * B : ℝ≥0) : ℝ≥0∞) := by
        have e : c ε₂ = (E2 : ℝ≥0∞)⁻¹ * ((E2 : ℝ≥0∞) * c ε₂) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.2 hE2pos) ENNReal.coe_ne_top, one_mul]
        rw [e, ENNReal.coe_mul, ENNReal.coe_inv hE2pos]
        exact mul_le_mul' le_rfl h2
      have h5 : ENNReal.ofReal (ε ^ m) ≤ (Real.toNNReal (ε₁ ^ m) : ℝ≥0∞) :=
        ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hε.le hε1 m)
      calc ENNReal.ofReal (ε ^ m) * c ε ≤ (Real.toNNReal (ε₁ ^ m) : ℝ≥0∞) * ((E2⁻¹ * B : ℝ≥0) : ℝ≥0∞) :=
            mul_le_mul' h5 (h3.trans h4)
        _ ≤ D := by
            rw [← ENNReal.coe_mul, ENNReal.coe_le_coe, hD]
            exact le_add_self
  calc ENNReal.ofReal (ε ^ m) * Th φ A (k * ofF (r ε))
      ≤ ENNReal.ofReal (ε ^ m) * ((Real.toNNReal B0 : ℝ≥0∞) * c ε) := mul_le_mul' le_rfl hTh
    _ = (Real.toNNReal B0 : ℝ≥0∞) * (ENNReal.ofReal (ε ^ m) * c ε) := by ring
    _ ≤ (Real.toNNReal B0 : ℝ≥0∞) * D := mul_le_mul' le_rfl hcD
    _ = ((Real.toNNReal B0 * D : ℝ≥0) : ℝ≥0∞) := by rw [ENNReal.coe_mul]

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.UnitBd

end
