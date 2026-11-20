import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.RightInvariantOfCovolume
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped GlobalTheory.MixModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnipMean

variable {D : D7}

/- English proof (translation)
Take `⟨i1, i2, i3, i4, i5, i6, i7⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V`. Take `⟨K, hK, h⟩` from `(GlobalTheory.Mem.UnipCocompact.radicals_cocompact D V r C ⟨hC.2.1, hC.2.2⟩).2`. Establish `hcl : IsClosed (NI V C : Set (GA D V))`. Establish `: DiscreteTopology (GQ V ⊓ NI V C : Subgroup (GA D V))` using `DiscreteTopology.of_subset (s := (GQ V : Set (GA D V))) i6 (fun x hx => hx.1)`. Establish `h1 : IsClosed ((GQ V ⊓ NI V C : Subgroup (GA D V)) : Set (GA D V))` using `Subgroup.isClosed_of_discrete`.

Establish `h2` using `h1.mul_right_of_isCompact (hK.image continuous_subtype_val)`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Take `⟨γ, hγ, k, hk, e⟩` from `h ⟨x, hx⟩`. Conclude with `⟨γ, ⟨hγ, γ.2⟩, k, ⟨k, hk, rfl⟩, (congrArg Subtype.val e).symm⟩`. Introduce and unpack `⟨γ, hγ, _, ⟨k, -, rfl⟩, rfl⟩`. Conclude with `mul_mem hγ.2 k.2`. Establish `hinj : Function.Injective fun γ : NIQ V C => (⟨γ.1.1, γ.2⟩ : GQ V)` using `fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x : GQ V => (x : GA D V)) h))`.

Conclude with `⟨hcl.locallyCompactSpace, TopologicalSpace.Subtype.secondCountableTopology _, Subtype.borelSpace _, inferInstance, hinj.countable, K, hK, h⟩`.
-/
theorem topology_NI (V : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (hC : IsIsoFrame V C) :
    LocallyCompactSpace (NI V C) ∧ SecondCountableTopology (NI V C) ∧ BorelSpace (NI V C) ∧
    IsTopologicalGroup (NI V C) ∧ Countable (NIQ V C) ∧
    ∃ K : Set (NI V C), IsCompact K ∧ ∀ n, ∃ γ ∈ NIQ V C, ∃ k ∈ K, n = γ * k := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨K, hK, h⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D V r C ⟨hC.2.1, hC.2.2⟩).2
  have hcl : IsClosed (NI V C : Set (GA D V)) := by
    have : DiscreteTopology (GQ V ⊓ NI V C : Subgroup (GA D V)) :=
      DiscreteTopology.of_subset (s := (GQ V : Set (GA D V))) i6 (fun x hx => hx.1)
    have h1 : IsClosed ((GQ V ⊓ NI V C : Subgroup (GA D V)) : Set (GA D V)) := Subgroup.isClosed_of_discrete
    have h2 := h1.mul_right_of_isCompact (hK.image continuous_subtype_val)
    convert h2 using 1
    ext x
    constructor
    · intro hx
      obtain ⟨γ, hγ, k, hk, e⟩ := h ⟨x, hx⟩
      exact ⟨γ, ⟨hγ, γ.2⟩, k, ⟨k, hk, rfl⟩, (congrArg Subtype.val e).symm⟩
    · rintro ⟨γ, hγ, _, ⟨k, -, rfl⟩, rfl⟩
      exact mul_mem hγ.2 k.2
  have hinj : Function.Injective fun γ : NIQ V C => (⟨γ.1.1, γ.2⟩ : GQ V) :=
    fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x : GQ V => (x : GA D V)) h))
  exact ⟨hcl.locallyCompactSpace, TopologicalSpace.Subtype.secondCountableTopology _, Subtype.borelSpace _,
    inferInstance, hinj.countable, K, hK, h⟩

/- English proof (translation)
Take `⟨i1, i2, i3, i4, i5, K, hK, hKc⟩` from `GlobalTheory.MixModel.lattice_Mx D s k`. Use `haveI : BorelSpace (Mx D s k) := ⟨rfl⟩`. Use `haveI := hμ.1`. Establish `h0 : κ 𝓝 ≠ 0` using `h𝓝.measure_ne_zero (NeZero.ne κ)`. Take `⟨M, hM⟩` from `hK.exists_bound_of_continuousOn hφc.continuousOn`.

Establish `hb : ∀ a, ‖φ a‖ ≤ M` using `fun a => by`. Take `⟨γ, hγ, ha⟩` from `hKc a`. Rewrite using `[← hφ γ hγ a]`. Conclude with `hM _ ha`. Establish `hinv : ∀ a, ∫ n in 𝓝, φ (f n + a) ∂κ = ∫ n in 𝓝, φ (f n) ∂κ`.

Introduce `a`. Take `⟨n0, rfl⟩` from `hfs a`. Establish `hmp : MeasurePreserving (· * n0) κ κ` using `⟨measurable_mul_const n0, GlobalTheory.AutQuotCheck.rightInvariant_of_covolume Γ κ h𝓝 h0 hfin n0⟩`. Establish `hmp' : MeasurePreserving (· * n0⁻¹) κ κ` using `⟨measurable_mul_const n0⁻¹, GlobalTheory.AutQuotCheck.rightInvariant_of_covolume Γ κ h𝓝 h0 hfin n0⁻¹⟩`. Establish `hF' : IsFundamentalDomain Γ ((· * n0⁻¹) ⁻¹' 𝓝) κ` using `h𝓝.preimage_of_equiv hmp'.quasiMeasurePreserving (e := id) Function.bijective_id (fun γ x => by simp [Subgroup.smul_def, mul_assoc])`.

Establish `e1 : (· * n0) ⁻¹' ((· * n0⁻¹) ⁻¹' 𝓝) = 𝓝`. Use extensionality with `x`. Simplify using the standard rewrite rules. Use `hmp.setIntegral_preimage_emb (measurableEmbedding_mulRight n0) (fun y => φ (f y)) ((· * n0⁻¹) ⁻¹' 𝓝)` as an intermediate fact. Rewrite `this` using `[e1]`.

Simplify using `only [hf] at this`. Rewrite using `[this]`. Conclude with `hF'.setIntegral_eq h𝓝 fun γ x => by`. Rewrite using `[Subgroup.smul_def, smul_eq_mul, hf, hφ _ (hfΓ _ γ.2)]`. Use `haveI : IsFiniteMeasure (κ.restrict 𝓝) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩`.

Use `haveI : IsFiniteMeasure (μ.restrict 𝓐) := ⟨by rw [Measure.restrict_apply_univ, hμ.2.2]; exact ENNReal.one_lt_top⟩`. Establish `hint : Integrable (Function.uncurry fun n a => φ (f n + a)) ((κ.restrict 𝓝).prod (μ.restrict 𝓐))` using `Integrable.of_bound (hφc.comp ((hfc.comp continuous_fst).add continuous_snd)).aestronglyMeasurable M (Filter.Eventually.of_forall fun p => hb _)`. Establish `hswap` using `integral_integral_swap hint`. Establish `l1 : ∀ n, ∫ a in 𝓐, φ (f n + a) ∂μ = ∫ a in 𝓐, φ a ∂μ` using `fun n => by`. Rewrite using `[← GlobalTheory.MixModel.covolOne_integral_add hμ φ hφ (f n)]`.

Simplify using `only [add_comm]`. Simplify using `only [l1, hinv, integral_const, smul_eq_mul] at hswap`. Rewrite `hswap` using `[Measure.real, Measure.real, Measure.restrict_apply_univ, Measure.restrict_apply_univ, hμ.2.2]`. Simplify `hswap.symm` using `[mul_comm]`.
-/
theorem mean_of_hom {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ]
    {s k : ℕ} (f : G → Mx D s k) (hf : ∀ x y, f (x * y) = f x + f y) (hfc : Continuous f)
    (hfs : Function.Surjective f) (hfΓ : ∀ γ ∈ Γ, f γ ∈ ratMx D s k)
    (κ : Measure G) [κ.IsHaarMeasure] (𝓝 : Set G) (h𝓝 : IsFundamentalDomain Γ 𝓝 κ) (hfin : κ 𝓝 ≠ ⊤)
    {μ : Measure (Mx D s k)} {𝓐 : Set (Mx D s k)} (hμ : IsCovolOne (ratMx D s k) μ 𝓐)
    (φ : Mx D s k → ℂ) (hφc : Continuous φ) (hφ : ∀ γ ∈ ratMx D s k, ∀ a, φ (γ + a) = φ a) :
    ∫ n in 𝓝, φ (f n) ∂κ = ((κ 𝓝).toReal : ℂ) * ∫ a in 𝓐, φ a ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.MixModel.lattice_Mx D s k
  haveI : BorelSpace (Mx D s k) := ⟨rfl⟩
  haveI := hμ.1
  have h0 : κ 𝓝 ≠ 0 := h𝓝.measure_ne_zero (NeZero.ne κ)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hφc.continuousOn
  have hb : ∀ a, ‖φ a‖ ≤ M := fun a => by
    obtain ⟨γ, hγ, ha⟩ := hKc a
    rw [← hφ γ hγ a]
    exact hM _ ha
  have hinv : ∀ a, ∫ n in 𝓝, φ (f n + a) ∂κ = ∫ n in 𝓝, φ (f n) ∂κ := by
    intro a
    obtain ⟨n0, rfl⟩ := hfs a
    have hmp : MeasurePreserving (· * n0) κ κ :=
      ⟨measurable_mul_const n0, GlobalTheory.AutQuotCheck.rightInvariant_of_covolume Γ κ h𝓝 h0 hfin n0⟩
    have hmp' : MeasurePreserving (· * n0⁻¹) κ κ :=
      ⟨measurable_mul_const n0⁻¹, GlobalTheory.AutQuotCheck.rightInvariant_of_covolume Γ κ h𝓝 h0 hfin n0⁻¹⟩
    have hF' : IsFundamentalDomain Γ ((· * n0⁻¹) ⁻¹' 𝓝) κ :=
      h𝓝.preimage_of_equiv hmp'.quasiMeasurePreserving (e := id) Function.bijective_id
        (fun γ x => by simp [Subgroup.smul_def, mul_assoc])
    have e1 : (· * n0) ⁻¹' ((· * n0⁻¹) ⁻¹' 𝓝) = 𝓝 := by
      ext x; simp
    have := hmp.setIntegral_preimage_emb (measurableEmbedding_mulRight n0) (fun y => φ (f y)) ((· * n0⁻¹) ⁻¹' 𝓝)
    rw [e1] at this
    simp only [hf] at this
    rw [this]
    exact hF'.setIntegral_eq h𝓝 fun γ x => by
      rw [Subgroup.smul_def, smul_eq_mul, hf, hφ _ (hfΓ _ γ.2)]
  haveI : IsFiniteMeasure (κ.restrict 𝓝) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓐) := ⟨by rw [Measure.restrict_apply_univ, hμ.2.2]; exact ENNReal.one_lt_top⟩
  have hint : Integrable (Function.uncurry fun n a => φ (f n + a)) ((κ.restrict 𝓝).prod (μ.restrict 𝓐)) :=
    Integrable.of_bound (hφc.comp ((hfc.comp continuous_fst).add continuous_snd)).aestronglyMeasurable M
      (Filter.Eventually.of_forall fun p => hb _)
  have hswap := integral_integral_swap hint
  have l1 : ∀ n, ∫ a in 𝓐, φ (f n + a) ∂μ = ∫ a in 𝓐, φ a ∂μ := fun n => by
    rw [← GlobalTheory.MixModel.covolOne_integral_add hμ φ hφ (f n)]
    simp only [add_comm]
  simp only [l1, hinv, integral_const, smul_eq_mul] at hswap
  rw [Measure.real, Measure.real, Measure.restrict_apply_univ, Measure.restrict_apply_univ, hμ.2.2] at hswap
  simpa [mul_comm] using hswap.symm

/- English proof (translation)
Use `noncomm_ring`.
-/
theorem mul_sub_one_eq {R : Type*} [Ring R] (a b : R) : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by
  noncomm_ring

def coord (V : HSp D) {s k : ℕ} (M : Matrix (Fin s) (Fin V.rank) D.host.E) (B : Matrix (Fin V.rank) (Fin k) D.host.E)
    (g : GA D V) : Mx D s k :=
  HMul.hMul (HMul.hMul (M.map (incA D) : Matrix (Fin s) (Fin V.rank) (AE D)) (mt V g - 1))
    (B.map (incA D) : Matrix (Fin V.rank) (Fin k) (AE D))

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Proceed by induction on `hg using Subgroup.closure_induction with`. Consider the case `mem x hx`. Take `⟨h1, -, h3⟩` from `hx`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Establish `hcol : ∀ j, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram).mulVec (fun i => B i j) = 0`.

Introduce `j`. Use function extensionality and compare the values at `i`. Use `congrFun (congrFun hB i) j` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, Matrix.mulVec, dotProduct, adj]`. Use `choose a ha using fun j => h3 (fun i => B i j) (hcol j)`.

Use `⟨Matrix.of fun i j => a j i, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i j`. Use `congrFun (ha j) i` as an intermediate fact. Simplify using `only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply] at this ⊢`. Conclude with `this`.

Consider the case `one`. Use `⟨by simp [GlobalTheory.MixModel.mt_one], 0, by simp [GlobalTheory.MixModel.mt_one]⟩` and prove the remaining obligations. Consider the case `mul x y _ _ hx hy`. Take `⟨hx1, Yx, hx2⟩` from `hx`. Take `⟨hy1, Yy, hy2⟩` from `hy`.

Establish `e : mt V (x * y) - 1 = (mt V x - 1) * (mt V y - 1) + (mt V x - 1) + (mt V y - 1)`. Rewrite using `[GlobalTheory.MixModel.mt_mul]`. Conclude with `mul_sub_one_eq _ _`. Use `⟨?_, Yx + Yy, ?_⟩` and prove the remaining obligations. Rewrite using `[e, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc, hy1, hx1, Matrix.mul_zero, add_zero, add_zero]`.

Rewrite using `[e, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc, hy2, hx2, ← Matrix.mul_assoc, hx1, Matrix.zero_mul, zero_add, Matrix.mul_add]`. Consider the case `inv x _ hx`. Take `⟨hx1, Y, hx2⟩` from `hx`. Establish `hinv : ∀ {q : ℕ} (Z : Matrix (Fin V.rank) (Fin q) (AE D)), mt V x⁻¹ ⬝ (mt V x ⬝ Z) = Z` using `fun Z => by`. Rewrite using `[← Matrix.mul_assoc, GlobalTheory.MixModel.mt_inv_mul, Matrix.one_mul]`.

Establish `hc : mt V x ⬝ (C.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D)) = C.map (incA D)`. Establish `h` using `hx1`. Rewrite `h` using `[Matrix.sub_mul]`. Rewrite `h` using `[Matrix.one_mul]`. Conclude with `sub_eq_zero.1 h`.

Establish `hb : mt V x ⬝ (B.map (incA D) : Matrix (Fin V.rank) (Fin k) (AE D)) = B.map (incA D) + (C.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D)) ⬝ Y`. Establish `h` using `hx2`. Rewrite `h` using `[Matrix.sub_mul]`. Rewrite `h` using `[Matrix.one_mul]`. Conclude with `sub_eq_iff_eq_add'.1 h`.

Establish `h2 : mt V x⁻¹ ⬝ (C.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D)) = C.map (incA D)` using `by conv_lhs => rw [← hc]`. Conclude with `hinv _`. Use `⟨by rw [Matrix.sub_mul, Matrix.one_mul, h2, sub_self], -Y, ?_⟩` and prove the remaining obligations. Establish `h3` using `hinv (B.map (incA D))`. Rewrite `h3` using `[hb, Matrix.mul_add, ← Matrix.mul_assoc, h2]`.

Rewrite using `[Matrix.sub_mul, Matrix.one_mul, Matrix.mul_neg]`. Rewrite `h3` using `[← eq_sub_iff_add_eq]`. Rewrite using `[h3]`. Normalize the expressions using the abelian group laws.
-/
theorem mem_NI_prop (V : HSp D) {r k : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin k) D.host.E) (hB : adj D C * V.gram * B = 0) {g : GA D V} (hg : g ∈ NI V C) :
    (mt V g - 1) ⬝ C.map (incA D) = 0 ∧
      ∃ Y : Matrix (Fin r) (Fin k) (AE D), (mt V g - 1) ⬝ B.map (incA D) = C.map (incA D) ⬝ Y := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨h1, -, h3⟩ := hx
    refine ⟨h1, ?_⟩
    have hcol : ∀ j, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram).mulVec (fun i => B i j) = 0 := by
      intro j
      funext i
      have := congrFun (congrFun hB i) j
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, adj] using this
    choose a ha using fun j => h3 (fun i => B i j) (hcol j)
    refine ⟨Matrix.of fun i j => a j i, ?_⟩
    funext i j
    have := congrFun (ha j) i
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply] at this ⊢
    exact this
  | one =>
    refine ⟨by simp [GlobalTheory.MixModel.mt_one], 0, by simp [GlobalTheory.MixModel.mt_one]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨hx1, Yx, hx2⟩ := hx
    obtain ⟨hy1, Yy, hy2⟩ := hy
    have e : mt V (x * y) - 1 = (mt V x - 1) * (mt V y - 1) + (mt V x - 1) + (mt V y - 1) := by
      rw [GlobalTheory.MixModel.mt_mul]; exact mul_sub_one_eq _ _
    refine ⟨?_, Yx + Yy, ?_⟩
    · rw [e, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc, hy1, hx1, Matrix.mul_zero, add_zero, add_zero]
    · rw [e, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc, hy2, hx2, ← Matrix.mul_assoc, hx1, Matrix.zero_mul,
        zero_add, Matrix.mul_add]
  | inv x _ hx =>
    obtain ⟨hx1, Y, hx2⟩ := hx
    have hinv : ∀ {q : ℕ} (Z : Matrix (Fin V.rank) (Fin q) (AE D)), mt V x⁻¹ ⬝ (mt V x ⬝ Z) = Z := fun Z => by
      rw [← Matrix.mul_assoc, GlobalTheory.MixModel.mt_inv_mul, Matrix.one_mul]
    have hc : mt V x ⬝ (C.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D)) = C.map (incA D) := by
      have h := hx1
      rw [Matrix.sub_mul] at h
      rw [Matrix.one_mul] at h
      exact sub_eq_zero.1 h
    have hb : mt V x ⬝ (B.map (incA D) : Matrix (Fin V.rank) (Fin k) (AE D)) = B.map (incA D) + (C.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D)) ⬝ Y := by
      have h := hx2
      rw [Matrix.sub_mul] at h
      rw [Matrix.one_mul] at h
      exact sub_eq_iff_eq_add'.1 h
    have h2 : mt V x⁻¹ ⬝ (C.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D)) = C.map (incA D) := by
      conv_lhs => rw [← hc]
      exact hinv _
    refine ⟨by rw [Matrix.sub_mul, Matrix.one_mul, h2, sub_self], -Y, ?_⟩
    have h3 := hinv (B.map (incA D))
    rw [hb, Matrix.mul_add, ← Matrix.mul_assoc, h2] at h3
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_neg]
    rw [← eq_sub_iff_add_eq] at h3
    rw [h3]
    abel

/- English proof (translation)
Take `⟨hx1, -⟩` from `mem_NI_prop V C B hB x.2`. Take `⟨-, Yy, hy2⟩` from `mem_NI_prop V C B hB y.2`. Establish `e : mt V ((x * y : NI V C) : GA D V) - 1 = (mt V x - 1) * (mt V y - 1) + (mt V x - 1) + (mt V y - 1)`. Rewrite using `[Subgroup.coe_mul, GlobalTheory.MixModel.mt_mul]`. Conclude with `mul_sub_one_eq _ _`.

Simplify using `only [coord]`. Rewrite using `[e, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc _ ((mt V x - 1) * _), Matrix.mul_assoc (mt V x - 1), hy2, ← Matrix.mul_assoc (mt V x - 1), hx1, Matrix.zero_mul, Matrix.mul_zero, zero_add]`.
-/
theorem coord_mul (V : HSp D) {r s k : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (M : Matrix (Fin s) (Fin V.rank) D.host.E) (B : Matrix (Fin V.rank) (Fin k) D.host.E)
    (hB : adj D C * V.gram * B = 0) (x y : NI V C) :
    coord V M B ((x * y : NI V C) : GA D V) = coord V M B x + coord V M B y := by
  obtain ⟨hx1, -⟩ := mem_NI_prop V C B hB x.2
  obtain ⟨-, Yy, hy2⟩ := mem_NI_prop V C B hB y.2
  have e : mt V ((x * y : NI V C) : GA D V) - 1 =
      (mt V x - 1) * (mt V y - 1) + (mt V x - 1) + (mt V y - 1) := by
    rw [Subgroup.coe_mul, GlobalTheory.MixModel.mt_mul]; exact mul_sub_one_eq _ _
  simp only [coord]
  rw [e, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc _ ((mt V x - 1) * _),
    Matrix.mul_assoc (mt V x - 1), hy2, ← Matrix.mul_assoc (mt V x - 1), hx1, Matrix.zero_mul, Matrix.mul_zero,
    zero_add]

/- English proof (translation)
Establish `h` using `(GlobalTheory.MixModel.mem_GQ_iff V (γ : GA D V)).1 hγ`. Establish `h1 : mt V γ - 1 ∈ GlobalTheory.MixModel.ratMx D V.rank V.rank` using `sub_mem h GlobalTheory.MixModel.ratMx_one`. Conclude with `GlobalTheory.MixModel.ratMx_mul (GlobalTheory.MixModel.ratMx_mul (GlobalTheory.MixModel.rat_mem M) h1) (GlobalTheory.MixModel.rat_mem B)`.
-/
theorem coord_rat (V : HSp D) {r s k : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (M : Matrix (Fin s) (Fin V.rank) D.host.E) (B : Matrix (Fin V.rank) (Fin k) D.host.E) (γ : NI V C)
    (hγ : γ ∈ NIQ V C) : coord V M B γ ∈ ratMx D s k := by
  have h := (GlobalTheory.MixModel.mem_GQ_iff V (γ : GA D V)).1 hγ
  have h1 : mt V γ - 1 ∈ GlobalTheory.MixModel.ratMx D V.rank V.rank := sub_mem h GlobalTheory.MixModel.ratMx_one
  exact GlobalTheory.MixModel.ratMx_mul (GlobalTheory.MixModel.ratMx_mul (GlobalTheory.MixModel.rat_mem M) h1) (GlobalTheory.MixModel.rat_mem B)

/- English proof (translation)
Take `⟨i1, -⟩` from `GlobalTheory.MixModel.lattice_Mx D V.rank V.rank`. Use `haveI : ContinuousSub (Mx D V.rank V.rank) := IsTopologicalAddGroup.to_continuousSub`. Conclude with `(continuous_const.matrix_mul ((GlobalTheory.MixModel.continuous_mt V).sub continuous_const)).matrix_mul continuous_const`.
-/
theorem continuous_coord (V : HSp D) {s k : ℕ} (M : Matrix (Fin s) (Fin V.rank) D.host.E)
    (B : Matrix (Fin V.rank) (Fin k) D.host.E) : Continuous (coord V M B) := by
  obtain ⟨i1, -⟩ := GlobalTheory.MixModel.lattice_Mx D V.rank V.rank
  haveI : ContinuousSub (Mx D V.rank V.rank) := IsTopologicalAddGroup.to_continuousSub
  exact (continuous_const.matrix_mul ((GlobalTheory.MixModel.continuous_mt V).sub continuous_const)).matrix_mul continuous_const

/- English proof (translation)
Establish `htop : LinearMap.range m.mulVecLin = ⊤`. Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Rewrite using `[Module.finrank_fin_fun]`. Conclude with `hm`. Establish `hs : ∀ i, ∃ v, m.mulVec v = Pi.single i 1` using `fun i => by`.

Establish `: (Pi.single i (1 : K) : Fin s → K) ∈ LinearMap.range m.mulVecLin` using `htop ▸ Submodule.mem_top`. Take `⟨v, hv⟩` from `this`. Conclude with `⟨v, hv⟩`. Use `choose v hv using hs`. Use `⟨Matrix.of fun j i => v i j, ?_⟩` and prove the remaining obligations.

Use extensionality with `i i'`. Use `congrFun (hv i') i` as an intermediate fact. Simplify using `only [Matrix.mulVec, dotProduct] at this`. Rewrite using `[Matrix.mul_apply, Matrix.one_apply]`. Simplify using `only [Matrix.of_apply, this, Pi.single_apply]`.
-/
theorem exists_right_inv {K : Type*} [Field K] {s r : ℕ} (m : Matrix (Fin s) (Fin r) K) (hm : m.rank = s) :
    ∃ m' : Matrix (Fin r) (Fin s) K, m * m' = 1 := by
  have htop : LinearMap.range m.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fin_fun]
    exact hm
  have hs : ∀ i, ∃ v, m.mulVec v = Pi.single i 1 := fun i => by
    have : (Pi.single i (1 : K) : Fin s → K) ∈ LinearMap.range m.mulVecLin := htop ▸ Submodule.mem_top
    obtain ⟨v, hv⟩ := this
    exact ⟨v, hv⟩
  choose v hv using hs
  refine ⟨Matrix.of fun j i => v i j, ?_⟩
  ext i i'
  have := congrFun (hv i') i
  simp only [Matrix.mulVec, dotProduct] at this
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.of_apply, this, Pi.single_apply]

/- English proof (translation)
Establish `hqq : q * q = 0`. Establish `: q * (u * u) = 0` using `by rw [← mul_assoc, hqu, zero_mul]`. Rewrite `this` using `[huu, mul_neg, neg_eq_zero]`. Then use the resulting hypothesis. Establish `e1 : (1 + us - h • qs) * g = g * (1 - u - h • q)`. Rewrite using `[sub_mul, add_mul, one_mul, hu, smul_mul_assoc, hq, mul_sub, mul_sub, mul_one, mul_smul_comm]`.

Normalize the expressions using the abelian group laws. Establish `e2 : (1 - u - h • q) * (1 + u - h • q) = 1`. Simplify using `only [sub_mul, add_mul, mul_sub, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, huu, huq, hqu, hqq, smul_zero, smul_smul]`. Take the linear combination `(norm := module) (-1 : S) • hh • q`. Rewrite using `[e1, mul_assoc, e2, mul_one]`.
-/
theorem unit_aux {S R : Type*} [CommRing S] [Ring R] [Algebra S R] (h : S) (hh : h + h = 1) (g u q us qs : R)
    (hu : us * g = -(g * u)) (hq : qs * g = g * q) (huu : u * u = -q) (huq : u * q = 0) (hqu : q * u = 0) :
    (1 + us - h • qs) * g * (1 + u - h • q) = g := by
  have hqq : q * q = 0 := by
    have : q * (u * u) = 0 := by rw [← mul_assoc, hqu, zero_mul]
    rwa [huu, mul_neg, neg_eq_zero] at this
  have e1 : (1 + us - h • qs) * g = g * (1 - u - h • q) := by
    rw [sub_mul, add_mul, one_mul, hu, smul_mul_assoc, hq, mul_sub, mul_sub, mul_one, mul_smul_comm]
    abel
  have e2 : (1 - u - h • q) * (1 + u - h • q) = 1 := by
    simp only [sub_mul, add_mul, mul_sub, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, huu, huq, hqu,
      hqq, smul_zero, smul_smul]
    linear_combination (norm := module) (-1 : S) • hh • q
  rw [e1, mul_assoc, e2, mul_one]

section Surj

open GlobalTheory.MixModel (rat gA giA half ofMat)

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Take `⟨m', hm'⟩` from `exists_right_inv m hm`. Establish `hr : ∀ {a b : ℕ} (P : Matrix (Fin V.rank) (Fin a) D.host.E) (Q : Matrix (Fin V.rank) (Fin b) D.host.E), rat (adj D P * V.gram * Q) = GlobalTheory.MixModel.adj (rat P) ⬝ (gA V ⬝ rat Q)`. Introduce `a b P Q`. Rewrite using `[GlobalTheory.MixModel.rat_mul, GlobalTheory.MixModel.rat_mul, Matrix.mul_assoc]`. Both sides reduce to the same expression.

Use `set c := rat C with hc`. Use `set b := rat B with hb`. Use `set c' := rat C' with hc'`. Use `set G := gA V with hG`. Use `set G' := gA V' with hG'`.

Establish `f1 : GlobalTheory.MixModel.adj c ⬝ (G ⬝ c) = 0`. Rewrite using `[← hr, show adj D C * V.gram * C = 0 from hs.frame.2.2, GlobalTheory.MixModel.rat_zero]`. Establish `f2 : GlobalTheory.MixModel.adj c ⬝ (G ⬝ b) = 0` using `by rw [← hr, hs.orth, GlobalTheory.MixModel.rat_zero]`. Establish `f3 : GlobalTheory.MixModel.adj b ⬝ (G ⬝ b) = G'` using `by rw [← hr, hs.isom]; rfl`. Establish `f6 : GlobalTheory.MixModel.adj c' ⬝ (G ⬝ b) = 0` using `by rw [← hr, h3, GlobalTheory.MixModel.rat_zero]`.

Establish `f4 : GlobalTheory.MixModel.adj b ⬝ (G ⬝ c) = 0`. Use `congrArg GlobalTheory.MixModel.adj f2` as an intermediate fact. Rewrite `this` using `[GlobalTheory.MixModel.adj_mul, GlobalTheory.MixModel.adj_mul, GlobalTheory.MixModel.adj_adj, GlobalTheory.MixModel.adj_gA, GlobalTheory.MixModel.adj_zero, Matrix.mul_assoc]`. Then use the resulting hypothesis. Establish `f5 : GlobalTheory.MixModel.adj c' ⬝ (G ⬝ c) = 1`. Use `congrArg GlobalTheory.MixModel.adj (show GlobalTheory.MixModel.adj c ⬝ (G ⬝ c') = 1 by` as an intermediate fact.

Rewrite using `[← hr, h1, GlobalTheory.MixModel.rat_one])`. Rewrite `this` using `[GlobalTheory.MixModel.adj_mul, GlobalTheory.MixModel.adj_mul, GlobalTheory.MixModel.adj_adj, GlobalTheory.MixModel.adj_gA, GlobalTheory.MixModel.adj_one, Matrix.mul_assoc]`. Then use the resulting hypothesis. Establish `e1 : ∀ {q : ℕ} (Y : Matrix (Fin r) (Fin q) (AE D)), GlobalTheory.MixModel.adj c ⬝ (G ⬝ (c ⬝ Y)) = 0` using `fun Y => by`. Rewrite using `[← Matrix.mul_assoc G, ← Matrix.mul_assoc, f1, Matrix.zero_mul]`. Establish `e2 : ∀ {q : ℕ} (Y : Matrix (Fin V'.rank) (Fin q) (AE D)), GlobalTheory.MixModel.adj c ⬝ (G ⬝ (b ⬝ Y)) = 0` using `fun Y => by`.

Rewrite using `[← Matrix.mul_assoc G, ← Matrix.mul_assoc, f2, Matrix.zero_mul]`. Establish `e3 : ∀ {q : ℕ} (Y : Matrix (Fin V'.rank) (Fin q) (AE D)), GlobalTheory.MixModel.adj b ⬝ (G ⬝ (b ⬝ Y)) = G' ⬝ Y` using `fun Y => by rw [← Matrix.mul_assoc G, ← Matrix.mul_assoc, f3]`. Establish `e4 : ∀ {q : ℕ} (Y : Matrix (Fin r) (Fin q) (AE D)), GlobalTheory.MixModel.adj b ⬝ (G ⬝ (c ⬝ Y)) = 0` using `fun Y => by`. Rewrite using `[← Matrix.mul_assoc G, ← Matrix.mul_assoc, f4, Matrix.zero_mul]`. Establish `e5 : ∀ {q : ℕ} (Y : Matrix (Fin r) (Fin q) (AE D)), GlobalTheory.MixModel.adj c' ⬝ (G ⬝ (c ⬝ Y)) = Y` using `fun Y => by`.

Rewrite using `[← Matrix.mul_assoc G, ← Matrix.mul_assoc, f5, Matrix.one_mul]`. Use `set Z : Matrix (Fin r) (Fin V'.rank) (AE D) := rat m' ⬝ X ⬝ giA V' with hZ`. Use `set u : Matrix (Fin V.rank) (Fin V.rank) (AE D) := c ⬝ (Z ⬝ (GlobalTheory.MixModel.adj b ⬝ G)) - b ⬝ (GlobalTheory.MixModel.adj Z ⬝ (GlobalTheory.MixModel.adj c ⬝ G)) with hu`. Use `set q : Matrix (Fin V.rank) (Fin V.rank) (AE D) := c ⬝ (Z ⬝ (G' ⬝ (GlobalTheory.MixModel.adj Z ⬝ (GlobalTheory.MixModel.adj c ⬝ G)))) with hq`. Establish `ku : GlobalTheory.MixModel.adj u * G = -(G * u)`.

Simplify using `only [hu, GlobalTheory.MixModel.adj_sub, GlobalTheory.MixModel.adj_mul, GlobalTheory.MixModel.adj_adj, hG, GlobalTheory.MixModel.adj_gA, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, neg_sub]`. Establish `kq : GlobalTheory.MixModel.adj q * G = G * q`. Simplify using `only [hq, GlobalTheory.MixModel.adj_mul, GlobalTheory.MixModel.adj_adj, hG, hG', GlobalTheory.MixModel.adj_gA, Matrix.mul_assoc]`. Establish `kuu : u * u = -q`. Simplify using `only [hu, hq, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, e1, e2, e3, e4, Matrix.mul_zero, sub_zero, zero_sub]`.

Establish `kuq : u * q = 0`. Simplify using `only [hu, hq, Matrix.sub_mul, Matrix.mul_assoc, e1, e4, Matrix.mul_zero, sub_zero]`. Establish `kqu : q * u = 0`. Simplify using `only [hu, hq, Matrix.mul_sub, Matrix.mul_assoc, e1, e2, Matrix.mul_zero, sub_zero]`. Use `set N : Matrix (Fin V.rank) (Fin V.rank) (AE D) := 1 + u - half D • q with hN`.

Establish `hadjN : GlobalTheory.MixModel.adj N = 1 + GlobalTheory.MixModel.adj u - half D • GlobalTheory.MixModel.adj q`. Rewrite using `[hN, GlobalTheory.MixModel.adj_sub, GlobalTheory.MixModel.adj_add, GlobalTheory.MixModel.adj_one, GlobalTheory.MixModel.adj_smul, GlobalTheory.MixModel.cA_half]`. Establish `hunit : GlobalTheory.MixModel.adj N * (gA V * N) = gA V`. Rewrite using `[hadjN, ← Matrix.mul_assoc]`. Conclude with `unit_aux (half D) GlobalTheory.MixModel.half_add_half G u q _ _ ku kq kuu kuq kqu`.

Use `set n : GA D V := ofMat V N hunit with hn`. Establish `hN1 : mt V n - 1 = u - half D • q`. Rewrite using `[hn, GlobalTheory.MixModel.mt_ofMat, hN]`. Normalize the expressions using the abelian group laws. Establish `kuc : u ⬝ c = 0`.

Simplify using `only [hu, Matrix.sub_mul, Matrix.mul_assoc, f1, f4, Matrix.mul_zero, sub_zero]`. Establish `kqc : q ⬝ c = 0`. Simplify using `only [hq, Matrix.mul_assoc, f1, Matrix.mul_zero]`. Establish `kcu : (GlobalTheory.MixModel.adj c ⬝ G) ⬝ u = 0`. Simplify using `only [hu, Matrix.mul_sub, Matrix.mul_assoc, e1, e2, sub_zero]`.

Establish `kcq : (GlobalTheory.MixModel.adj c ⬝ G) ⬝ q = 0`. Simplify using `only [hq, Matrix.mul_assoc, e1]`. Establish `kub : u ⬝ b = c ⬝ (Z ⬝ G')`. Simplify using `only [hu, Matrix.sub_mul, Matrix.mul_assoc, f2, f3, Matrix.mul_zero, sub_zero]`. Establish `kqb : q ⬝ b = 0`.

Simplify using `only [hq, Matrix.mul_assoc, f2, Matrix.mul_zero]`. Establish `he : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram).map (incA D) = GlobalTheory.MixModel.adj c ⬝ G` using `GlobalTheory.MixModel.rat_mul _ _`. Establish `hmem : n ∈ NI V C`. Use `Subgroup.subset_closure ⟨?_, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(mt V n - 1) ⬝ c = 0`.

Rewrite using `[hN1, Matrix.sub_mul, kuc, Matrix.smul_mul, kqc, smul_zero, sub_zero]`. Rewrite using `[he]`. Express the relevant statement in the definitionally equal form `(GlobalTheory.MixModel.adj c ⬝ G) ⬝ (mt V n - 1) = 0`. Rewrite using `[hN1, Matrix.mul_sub, kcu, Matrix.mul_smul, kcq, smul_zero, sub_zero]`. Introduce `x hx set xA : Fin V.rank → AE D := fun i => incA D (x i) with hxA`.

Establish `hz : GlobalTheory.MixModel.adj c *ᵥ (G *ᵥ xA) = 0`. Rewrite using `[Matrix.mulVec_mulVec, ← he]`. Use function extensionality and compare the values at `i`. Use `congrArg (incA D) (congrFun hx i)` as an intermediate fact. Rewrite `this` using `[RingHom.map_mulVec, Pi.zero_apply, map_zero]`.

Conclude with `this`. Use `⟨(Z ⬝ (GlobalTheory.MixModel.adj b ⬝ G)) *ᵥ xA, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(mt V n - 1) *ᵥ xA = _`. Rewrite using `[hN1, Matrix.sub_mulVec, Matrix.smul_mulVec]`. Establish `hu' : u *ᵥ xA = c *ᵥ ((Z ⬝ (GlobalTheory.MixModel.adj b ⬝ G)) *ᵥ xA)`.

Rewrite using `[hu, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec (M := b), ← Matrix.mulVec_mulVec (M := GlobalTheory.MixModel.adj Z), ← Matrix.mulVec_mulVec (M := GlobalTheory.MixModel.adj c), hz, Matrix.mulVec_zero, Matrix.mulVec_zero, sub_zero, Matrix.mulVec_mulVec]`. Establish `hq' : q *ᵥ xA = 0`. Rewrite using `[hq, ← Matrix.mulVec_mulVec (M := c), ← Matrix.mulVec_mulVec (M := Z), ← Matrix.mulVec_mulVec (M := G'), ← Matrix.mulVec_mulVec (M := GlobalTheory.MixModel.adj Z), ← Matrix.mulVec_mulVec (M := GlobalTheory.MixModel.adj c), hz, Matrix.mulVec_zero, Matrix.mulVec_zero, Matrix.mulVec …`. Rewrite using `[hu', hq', smul_zero, sub_zero]`. Both sides reduce to the same expression.

Use `⟨⟨n, hmem⟩, ?_⟩` and prove the remaining obligations. Establish `hM : (m * adj D C' * V.gram).map (incA D) = rat m ⬝ (GlobalTheory.MixModel.adj c' ⬝ G)`. Express the relevant statement in the definitionally equal form `rat (m * adj D C' * V.gram) = _`. Rewrite using `[GlobalTheory.MixModel.rat_mul, GlobalTheory.MixModel.rat_mul, Matrix.mul_assoc]`. Both sides reduce to the same expression.

Express the relevant statement in the definitionally equal form `(m * adj D C' * V.gram).map (incA D) ⬝ (mt V n - 1) ⬝ b = X`. Rewrite using `[hM, hN1, Matrix.mul_assoc, Matrix.sub_mul, kub, Matrix.smul_mul, kqb, smul_zero, sub_zero, Matrix.mul_assoc, Matrix.mul_assoc, e5, hZ, Matrix.mul_assoc, Matrix.mul_assoc, hG', GlobalTheory.MixModel.giA_mul_gA, Matrix.mul_one, ← Matrix.mul_assoc, ← GlobalTheory.MixModel.rat_mul, …`.
-/
theorem coord_surj (V V' : HSp D) {r s : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (hs : IsIsoSplit V V' C B) (h1 : adj D C * V.gram * C' = 1)
    (h3 : adj D C' * V.gram * B = 0) (m : Matrix (Fin s) (Fin r) D.host.E) (hm : m.rank = s)
    (X : Mx D s V'.rank) : ∃ n : NI V C, coord V (m * adj D C' * V.gram) B n = X := by
  obtain ⟨m', hm'⟩ := exists_right_inv m hm
  have hr : ∀ {a b : ℕ} (P : Matrix (Fin V.rank) (Fin a) D.host.E) (Q : Matrix (Fin V.rank) (Fin b) D.host.E),
      rat (adj D P * V.gram * Q) = GlobalTheory.MixModel.adj (rat P) ⬝ (gA V ⬝ rat Q) := by
    intro a b P Q
    rw [GlobalTheory.MixModel.rat_mul, GlobalTheory.MixModel.rat_mul, Matrix.mul_assoc]
    rfl
  set c := rat C with hc
  set b := rat B with hb
  set c' := rat C' with hc'
  set G := gA V with hG
  set G' := gA V' with hG'
  have f1 : GlobalTheory.MixModel.adj c ⬝ (G ⬝ c) = 0 := by
    rw [← hr, show adj D C * V.gram * C = 0 from hs.frame.2.2, GlobalTheory.MixModel.rat_zero]
  have f2 : GlobalTheory.MixModel.adj c ⬝ (G ⬝ b) = 0 := by rw [← hr, hs.orth, GlobalTheory.MixModel.rat_zero]
  have f3 : GlobalTheory.MixModel.adj b ⬝ (G ⬝ b) = G' := by rw [← hr, hs.isom]; rfl
  have f6 : GlobalTheory.MixModel.adj c' ⬝ (G ⬝ b) = 0 := by rw [← hr, h3, GlobalTheory.MixModel.rat_zero]
  have f4 : GlobalTheory.MixModel.adj b ⬝ (G ⬝ c) = 0 := by
    have := congrArg GlobalTheory.MixModel.adj f2
    rwa [GlobalTheory.MixModel.adj_mul, GlobalTheory.MixModel.adj_mul, GlobalTheory.MixModel.adj_adj, GlobalTheory.MixModel.adj_gA,
      GlobalTheory.MixModel.adj_zero, Matrix.mul_assoc] at this
  have f5 : GlobalTheory.MixModel.adj c' ⬝ (G ⬝ c) = 1 := by
    have := congrArg GlobalTheory.MixModel.adj (show GlobalTheory.MixModel.adj c ⬝ (G ⬝ c') = 1 by
      rw [← hr, h1, GlobalTheory.MixModel.rat_one])
    rwa [GlobalTheory.MixModel.adj_mul, GlobalTheory.MixModel.adj_mul, GlobalTheory.MixModel.adj_adj, GlobalTheory.MixModel.adj_gA,
      GlobalTheory.MixModel.adj_one, Matrix.mul_assoc] at this
  have e1 : ∀ {q : ℕ} (Y : Matrix (Fin r) (Fin q) (AE D)), GlobalTheory.MixModel.adj c ⬝ (G ⬝ (c ⬝ Y)) = 0 := fun Y => by
    rw [← Matrix.mul_assoc G, ← Matrix.mul_assoc, f1, Matrix.zero_mul]
  have e2 : ∀ {q : ℕ} (Y : Matrix (Fin V'.rank) (Fin q) (AE D)), GlobalTheory.MixModel.adj c ⬝ (G ⬝ (b ⬝ Y)) = 0 := fun Y => by
    rw [← Matrix.mul_assoc G, ← Matrix.mul_assoc, f2, Matrix.zero_mul]
  have e3 : ∀ {q : ℕ} (Y : Matrix (Fin V'.rank) (Fin q) (AE D)), GlobalTheory.MixModel.adj b ⬝ (G ⬝ (b ⬝ Y)) = G' ⬝ Y :=
    fun Y => by rw [← Matrix.mul_assoc G, ← Matrix.mul_assoc, f3]
  have e4 : ∀ {q : ℕ} (Y : Matrix (Fin r) (Fin q) (AE D)), GlobalTheory.MixModel.adj b ⬝ (G ⬝ (c ⬝ Y)) = 0 := fun Y => by
    rw [← Matrix.mul_assoc G, ← Matrix.mul_assoc, f4, Matrix.zero_mul]
  have e5 : ∀ {q : ℕ} (Y : Matrix (Fin r) (Fin q) (AE D)), GlobalTheory.MixModel.adj c' ⬝ (G ⬝ (c ⬝ Y)) = Y := fun Y => by
    rw [← Matrix.mul_assoc G, ← Matrix.mul_assoc, f5, Matrix.one_mul]
  set Z : Matrix (Fin r) (Fin V'.rank) (AE D) := rat m' ⬝ X ⬝ giA V' with hZ
  set u : Matrix (Fin V.rank) (Fin V.rank) (AE D) :=
    c ⬝ (Z ⬝ (GlobalTheory.MixModel.adj b ⬝ G)) - b ⬝ (GlobalTheory.MixModel.adj Z ⬝ (GlobalTheory.MixModel.adj c ⬝ G)) with hu
  set q : Matrix (Fin V.rank) (Fin V.rank) (AE D) :=
    c ⬝ (Z ⬝ (G' ⬝ (GlobalTheory.MixModel.adj Z ⬝ (GlobalTheory.MixModel.adj c ⬝ G)))) with hq
  have ku : GlobalTheory.MixModel.adj u * G = -(G * u) := by
    simp only [hu, GlobalTheory.MixModel.adj_sub, GlobalTheory.MixModel.adj_mul, GlobalTheory.MixModel.adj_adj, hG, GlobalTheory.MixModel.adj_gA,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, neg_sub]
  have kq : GlobalTheory.MixModel.adj q * G = G * q := by
    simp only [hq, GlobalTheory.MixModel.adj_mul, GlobalTheory.MixModel.adj_adj, hG, hG', GlobalTheory.MixModel.adj_gA, Matrix.mul_assoc]
  have kuu : u * u = -q := by
    simp only [hu, hq, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, e1, e2, e3, e4, Matrix.mul_zero, sub_zero,
      zero_sub]
  have kuq : u * q = 0 := by
    simp only [hu, hq, Matrix.sub_mul, Matrix.mul_assoc, e1, e4, Matrix.mul_zero, sub_zero]
  have kqu : q * u = 0 := by
    simp only [hu, hq, Matrix.mul_sub, Matrix.mul_assoc, e1, e2, Matrix.mul_zero, sub_zero]
  set N : Matrix (Fin V.rank) (Fin V.rank) (AE D) := 1 + u - half D • q with hN
  have hadjN : GlobalTheory.MixModel.adj N = 1 + GlobalTheory.MixModel.adj u - half D • GlobalTheory.MixModel.adj q := by
    rw [hN, GlobalTheory.MixModel.adj_sub, GlobalTheory.MixModel.adj_add, GlobalTheory.MixModel.adj_one, GlobalTheory.MixModel.adj_smul,
      GlobalTheory.MixModel.cA_half]
  have hunit : GlobalTheory.MixModel.adj N * (gA V * N) = gA V := by
    rw [hadjN, ← Matrix.mul_assoc]
    exact unit_aux (half D) GlobalTheory.MixModel.half_add_half G u q _ _ ku kq kuu kuq kqu
  set n : GA D V := ofMat V N hunit with hn
  have hN1 : mt V n - 1 = u - half D • q := by
    rw [hn, GlobalTheory.MixModel.mt_ofMat, hN]; abel
  have kuc : u ⬝ c = 0 := by
    simp only [hu, Matrix.sub_mul, Matrix.mul_assoc, f1, f4, Matrix.mul_zero, sub_zero]
  have kqc : q ⬝ c = 0 := by
    simp only [hq, Matrix.mul_assoc, f1, Matrix.mul_zero]
  have kcu : (GlobalTheory.MixModel.adj c ⬝ G) ⬝ u = 0 := by
    simp only [hu, Matrix.mul_sub, Matrix.mul_assoc, e1, e2, sub_zero]
  have kcq : (GlobalTheory.MixModel.adj c ⬝ G) ⬝ q = 0 := by
    simp only [hq, Matrix.mul_assoc, e1]
  have kub : u ⬝ b = c ⬝ (Z ⬝ G') := by
    simp only [hu, Matrix.sub_mul, Matrix.mul_assoc, f2, f3, Matrix.mul_zero, sub_zero]
  have kqb : q ⬝ b = 0 := by
    simp only [hq, Matrix.mul_assoc, f2, Matrix.mul_zero]
  have he : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram).map (incA D) =
      GlobalTheory.MixModel.adj c ⬝ G := GlobalTheory.MixModel.rat_mul _ _
  have hmem : n ∈ NI V C := by
    refine Subgroup.subset_closure ⟨?_, ?_, ?_⟩
    · change (mt V n - 1) ⬝ c = 0
      rw [hN1, Matrix.sub_mul, kuc, Matrix.smul_mul, kqc, smul_zero, sub_zero]
    · rw [he]
      change (GlobalTheory.MixModel.adj c ⬝ G) ⬝ (mt V n - 1) = 0
      rw [hN1, Matrix.mul_sub, kcu, Matrix.mul_smul, kcq, smul_zero, sub_zero]
    · intro x hx
      set xA : Fin V.rank → AE D := fun i => incA D (x i) with hxA
      have hz : GlobalTheory.MixModel.adj c *ᵥ (G *ᵥ xA) = 0 := by
        rw [Matrix.mulVec_mulVec, ← he]
        funext i
        have := congrArg (incA D) (congrFun hx i)
        rw [RingHom.map_mulVec, Pi.zero_apply, map_zero] at this
        exact this
      refine ⟨(Z ⬝ (GlobalTheory.MixModel.adj b ⬝ G)) *ᵥ xA, ?_⟩
      change (mt V n - 1) *ᵥ xA = _
      rw [hN1, Matrix.sub_mulVec, Matrix.smul_mulVec]
      have hu' : u *ᵥ xA = c *ᵥ ((Z ⬝ (GlobalTheory.MixModel.adj b ⬝ G)) *ᵥ xA) := by
        rw [hu, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec (M := b), ← Matrix.mulVec_mulVec (M := GlobalTheory.MixModel.adj Z),
          ← Matrix.mulVec_mulVec (M := GlobalTheory.MixModel.adj c), hz, Matrix.mulVec_zero, Matrix.mulVec_zero, sub_zero,
          Matrix.mulVec_mulVec]
      have hq' : q *ᵥ xA = 0 := by
        rw [hq, ← Matrix.mulVec_mulVec (M := c), ← Matrix.mulVec_mulVec (M := Z), ← Matrix.mulVec_mulVec (M := G'),
          ← Matrix.mulVec_mulVec (M := GlobalTheory.MixModel.adj Z), ← Matrix.mulVec_mulVec (M := GlobalTheory.MixModel.adj c), hz,
          Matrix.mulVec_zero, Matrix.mulVec_zero, Matrix.mulVec_zero, Matrix.mulVec_zero]
      rw [hu', hq', smul_zero, sub_zero]
      rfl
  refine ⟨⟨n, hmem⟩, ?_⟩
  have hM : (m * adj D C' * V.gram).map (incA D) = rat m ⬝ (GlobalTheory.MixModel.adj c' ⬝ G) := by
    change rat (m * adj D C' * V.gram) = _
    rw [GlobalTheory.MixModel.rat_mul, GlobalTheory.MixModel.rat_mul, Matrix.mul_assoc]
    rfl
  change (m * adj D C' * V.gram).map (incA D) ⬝ (mt V n - 1) ⬝ b = X
  rw [hM, hN1, Matrix.mul_assoc, Matrix.sub_mul, kub, Matrix.smul_mul, kqb, smul_zero, sub_zero, Matrix.mul_assoc,
    Matrix.mul_assoc, e5, hZ, Matrix.mul_assoc, Matrix.mul_assoc, hG', GlobalTheory.MixModel.giA_mul_gA, Matrix.mul_one,
    ← Matrix.mul_assoc, ← GlobalTheory.MixModel.rat_mul, hm', GlobalTheory.MixModel.rat_one, Matrix.one_mul]

end Surj

/- English proof (translation)
Introduce `D V V' r C C' B hs h1 _ h3 κ 𝓝 hκ h𝓝 s m hm`. Take `⟨i1, i2, i3, i4, i5, K, hK, hKc⟩` from `topology_NI V C hs.frame`. Take `⟨μ, 𝓐, hμ⟩` from `GlobalTheory.MixModel.exists_isCovolOne D s V'.rank`. Establish `hfin : κ 𝓝 ≠ ⊤`. Establish `hle : κ 𝓝 ≤ κ K`.

Rewrite using `[h𝓝.measure_eq_tsum K]`. Use `(measure_mono fun n hn => ?_).trans (measure_iUnion_le _)` and prove the remaining obligations. Take `⟨γ, hγ, k, hk, rfl⟩` from `hKc n`. Conclude with `Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ⟨k, hk, rfl⟩, hn⟩`. Conclude with `(hle.trans_lt hK.measure_lt_top).ne`.

Use `⟨μ, 𝓐, hμ, fun φ hφc hφ => ?_⟩` and prove the remaining obligations. Conclude with `mean_of_hom (NIQ V C) (fun n : NI V C => coord V (m * adj D C' * V.gram) B n) (coord_mul V C _ B hs.orth) ((continuous_coord V _ B).comp continuous_subtype_val) (fun X => coord_surj V V' C C' B hs h1 h3 m hm X) (fun γ hγ => coord_rat V C _ B γ hγ) κ 𝓝 h𝓝 hfin hμ φ hφc hφ`.
-/
theorem mean_eq_volume_mul : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (κ : Measure (NI V C)) (𝓝 : Set (NI V C)), κ.IsHaarMeasure → IsFundamentalDomain (NIQ V C) 𝓝 κ → ∀ (s : ℕ) (m : Matrix (Fin s) (Fin r) D.host.E), m.rank = s → ∃ (μ : Measure (Mx D s V'.rank)) (𝓐 : Set (Mx D s V'.rank)), IsCovolOne (ratMx D s V'.rank) μ 𝓐 ∧ ∀ φ : Mx D s V'.rank → ℂ, Continuous φ → (∀ γ ∈ ratMx D s V'.rank, ∀ a, φ (γ + a) = φ a) → ∫ n in 𝓝, φ (HMul.hMul (HMul.hMul ((m * adj D C' * V.gram).map (incA D) : Matrix (Fin s) (Fin V.rank) (AE D)) (mt V (n : GA D V) - 1)) (B.map (incA D) : Matrix (Fin V.rank) (Fin V'.rank) (AE D))) ∂κ = ((κ 𝓝).toReal : ℂ) * ∫ a in 𝓐, φ a ∂μ := by
  intro D V V' r C C' B hs h1 _ h3 κ 𝓝 hκ h𝓝 s m hm
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := topology_NI V C hs.frame
  obtain ⟨μ, 𝓐, hμ⟩ := GlobalTheory.MixModel.exists_isCovolOne D s V'.rank
  have hfin : κ 𝓝 ≠ ⊤ := by
    have hle : κ 𝓝 ≤ κ K := by
      rw [h𝓝.measure_eq_tsum K]
      refine (measure_mono fun n hn => ?_).trans (measure_iUnion_le _)
      obtain ⟨γ, hγ, k, hk, rfl⟩ := hKc n
      exact Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ⟨k, hk, rfl⟩, hn⟩
    exact (hle.trans_lt hK.measure_lt_top).ne
  refine ⟨μ, 𝓐, hμ, fun φ hφc hφ => ?_⟩
  exact mean_of_hom (NIQ V C) (fun n : NI V C => coord V (m * adj D C' * V.gram) B n)
    (coord_mul V C _ B hs.orth) ((continuous_coord V _ B).comp continuous_subtype_val)
    (fun X => coord_surj V V' C C' B hs h1 h3 m hm X) (fun γ hγ => coord_rat V C _ B γ hγ) κ 𝓝 h𝓝 hfin hμ φ hφc hφ

end GlobalTheory.UnipMean
