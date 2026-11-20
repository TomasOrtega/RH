import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianQuadraticUnitaryLocalComponents
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmExtensionLocalFieldProductRingExistsSmulEq

noncomputable section

namespace GlobalTheory.GaugeEx

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct NNReal ENNReal

/- English proof (translation)
Use `haveI : LocallyCompactSpace (MulAction.orbit G x) := hc.locallyCompactSpace`. Use `haveI : ContinuousSMul G (MulAction.orbit G x) := ⟨Continuous.subtype_mk (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)) _⟩`. Set `x₀ : MulAction.orbit G x` to `⟨x, MulAction.mem_orbit_self x⟩`. Establish `ho : IsOpenMap fun g : G => g • x₀` using `isOpenMap_smul_of_sigmaCompact x₀`. Establish `hK' : IsCompact (Subtype.val ⁻¹' K : Set (MulAction.orbit G x))` using `hc.isClosedEmbedding_subtypeVal.isCompact_preimage hK`.

Set `ex` to `CompactExhaustion.choice G`. Take `⟨n, hn⟩` from `hK'.elim_directed_cover (fun n : ℕ => (fun g : G => g • x₀) '' interior (ex n)) (fun n => ho _ isOpen_interior) (by`. Introduce and unpack `⟨y, g, rfl⟩ _`. Take `⟨n, hn⟩` from `ex.exists_mem g`. Conclude with `Set.mem_iUnion.2 ⟨n + 1, g, ex.subset_interior_succ n hn, rfl⟩)`.

Use the proof step `(Monotone.directed_le fun a b hab => Set.image_mono (interior_mono (ex.subset hab)))`. Use `⟨ex n, ex.isCompact n, fun y hy hg => ?_⟩` and prove the remaining obligations. Take `⟨g, hg1, hg2⟩` from `hn (a := ⟨y, hg⟩) hy`. Conclude with `⟨g, interior_subset hg1, congrArg Subtype.val hg2⟩`.
-/
theorem tsfin_compact_lift {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SigmaCompactSpace G] [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [MulAction G X] [ContinuousSMul G X] (x : X)
    (hc : IsClosed (MulAction.orbit G x)) {K : Set X} (hK : IsCompact K) :
    ∃ C : Set G, IsCompact C ∧ ∀ y ∈ K, (∃ g : G, g • x = y) → ∃ g ∈ C, g • x = y := by
  haveI : LocallyCompactSpace (MulAction.orbit G x) := hc.locallyCompactSpace
  haveI : ContinuousSMul G (MulAction.orbit G x) :=
    ⟨Continuous.subtype_mk (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)) _⟩
  let x₀ : MulAction.orbit G x := ⟨x, MulAction.mem_orbit_self x⟩
  have ho : IsOpenMap fun g : G => g • x₀ := isOpenMap_smul_of_sigmaCompact x₀
  have hK' : IsCompact (Subtype.val ⁻¹' K : Set (MulAction.orbit G x)) :=
    hc.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  let ex := CompactExhaustion.choice G
  obtain ⟨n, hn⟩ := hK'.elim_directed_cover (fun n : ℕ => (fun g : G => g • x₀) '' interior (ex n))
    (fun n => ho _ isOpen_interior)
    (by
      rintro ⟨y, g, rfl⟩ _
      obtain ⟨n, hn⟩ := ex.exists_mem g
      exact Set.mem_iUnion.2 ⟨n + 1, g, ex.subset_interior_succ n hn, rfl⟩)
    (Monotone.directed_le fun a b hab => Set.image_mono (interior_mono (ex.subset hab)))
  refine ⟨ex n, ex.isCompact n, fun y hy hg => ?_⟩
  obtain ⟨g, hg1, hg2⟩ := hn (a := ⟨y, hg⟩) hy
  exact ⟨g, interior_subset hg1, congrArg Subtype.val hg2⟩

/- English proof (translation)
Establish `key : ∀ (J : Matrix (Fin n) (Fin n) A) (x y : Fin n → A), Formalism.UG.hform σ J x y = (σ ∘ x) ⬝ᵥ J.mulVec y`. Introduce `J x y`. Simplify using `[Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]`. Establish `h2 : σ ∘ g.mulVec x = (g.map σ).mulVec (σ ∘ x)`. Use function extensionality and compare the values at `i`.

Conclude with `RingHom.map_mulVec σ g x i`. Rewrite using `[key, key, h2]`. Use `conv_rhs => rw [← hg]`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mulVec_mulVec (M := Formalism.UG.cT σ g), Matrix.dotProduct_mulVec (σ ∘ x), Formalism.UG.cT, Matrix.vecMul_transpose, Matrix.mulVec_mulVec]`.
-/
theorem tsfin_hform_mulVec {A : Type} [CommRing A] (σ : A →+* A) {n : ℕ} (J g : Matrix (Fin n) (Fin n) A)
    (hg : Formalism.UG.cT σ g * J * g = J) (x : Fin n → A) :
    Formalism.UG.hform σ J (g.mulVec x) (g.mulVec x) = Formalism.UG.hform σ J x x := by
  have key : ∀ (J : Matrix (Fin n) (Fin n) A) (x y : Fin n → A),
      Formalism.UG.hform σ J x y = (σ ∘ x) ⬝ᵥ J.mulVec y := by
    intro J x y
    simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have h2 : σ ∘ g.mulVec x = (g.map σ).mulVec (σ ∘ x) := by
    funext i
    exact RingHom.map_mulVec σ g x i
  rw [key, key, h2]
  conv_rhs => rw [← hg]
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec (M := Formalism.UG.cT σ g), Matrix.dotProduct_mulVec (σ ∘ x),
    Formalism.UG.cT, Matrix.vecMul_transpose, Matrix.mulVec_mulVec]

section

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

/- English proof (translation)
Establish `hg : Formalism.UG.cT (sigR R σ) (HA.mat R σ J g).val * JR R J * (HA.mat R σ J g).val = JR R J` using `Subtype.property (p := fun x => x ∈ HR R σ J) g`. Unfold `qR hR`. Rewrite using `[← tsfin_hform_mulVec _ _ _ hg (y 0)]`. Both sides reduce to the same expression.
-/
theorem tsfin_q_smul (g : HA R σ J) (y : Fin 1 → Fin M → R ⊗[F] E) :
    qR R σ J ((g • y) 0) = qR R σ J (y 0) := by
  have hg : Formalism.UG.cT (sigR R σ) (HA.mat R σ J g).val * JR R J * (HA.mat R σ J g).val = JR R J :=
    Subtype.property (p := fun x => x ∈ HR R σ J) g
  unfold qR hR
  rw [← tsfin_hform_mulVec _ _ _ hg (y 0)]
  rfl

/- English proof (translation)
Use `haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2`. Establish `h : hR R σ J (ratTup (F` using `F) R x 0) (ratTup (F := F) R x 0) = (1 : R) ⊗ₜ[F] algebraMap F E a := by`. Rewrite using `[← hx]`. Simplify using `[hR, hE, Formalism.UG.hform, ratTup, JR, inclR, sigR, TensorProduct.tmul_sum]`. Rewrite using `[qR, h, qloc_trace_tmul, Algebra.trace_algebraMap, h2, one_mul, ← map_mul]`.

Use `congr 1`. Simplify using the standard rewrite rules.
-/
theorem tsfin_q_rat [CharZero F] (h2 : Module.finrank F E = 2) (x : Fin 1 → Fin M → E) (a : F)
    (hx : hE σ J (x 0) (x 0) = algebraMap F E a) :
    qR R σ J (ratTup (F := F) R x 0) = algebraMap F R a := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  have h : hR R σ J (ratTup (F := F) R x 0) (ratTup (F := F) R x 0) =
      (1 : R) ⊗ₜ[F] algebraMap F E a := by
    rw [← hx]
    simp [hR, hE, Formalism.UG.hform, ratTup, JR, inclR, sigR, TensorProduct.tmul_sum]
  rw [qR, h, qloc_trace_tmul, Algebra.trace_algebraMap, h2, one_mul, ← map_mul]
  congr 1
  simp

/- English proof (translation)
Establish `h1 : Continuous (Algebra.trace R (R ⊗[F] E))` using `IsModuleTopology.continuous_of_linearMap _`. Establish `h2 : Continuous (sigR R σ)` using `IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.map (AlgHom.id R R) σ).toLinearMap`. Unfold `qR hR Formalism.UG.hform`. Use `fun_prop`.
-/
theorem tsfin_q_cont [FiniteDimensional F E] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous fun y : Fin 1 → Fin M → R ⊗[F] E => qR R σ J (y 0) := by
  have h1 : Continuous (Algebra.trace R (R ⊗[F] E)) := IsModuleTopology.continuous_of_linearMap _
  have h2 : Continuous (sigR R σ) :=
    IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.map (AlgHom.id R R) σ).toLinearMap
  unfold qR hR Formalism.UG.hform
  fun_prop

end

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hcm R _ _ _ _ _ _ _ _ _ hR M J x a B J' m m' N hS hO hm hm' _ hT`. Take `⟨hJ, ha, hx, -, hJ', hJ'nd⟩` from `hS`. Establish `hq` using `tsfin_q_rat R σ J hcm.2.2.1 x a hx`. Establish `hu : IsUnit (algebraMap F R a)` using `(IsUnit.mk0 a ha).map _`. Establish `hc : IsClosed (MulAction.orbit (HA R σ J) (ratTup (F` using `F) R x)) := by`.

Establish `: MulAction.orbit (HA R σ J) (ratTup (F` using `F) R x) = {y | qR R σ J (y 0) = algebraMap F R a} := by`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, rfl⟩`. Conclude with `(tsfin_q_smul R σ J g _).trans hq`.

Introduce `hy`. Conclude with `GlobalTheory.GaugeWittLoc.exists_smul_eq F E σ hcm R hR (M + 1) J hJ _ _ y hu hq hy`. Rewrite using `[this]`. Conclude with `isClosed_eq (tsfin_q_cont R σ J) continuous_const`. Use `⟨fun K hK => ?_⟩` and prove the remaining obligations.

Set `K₁ : Set (Fin 1 → Fin (M + 1) → R ⊗[F] E)` to `(fun X _ => X 0) '' K`. Establish `hK₁ : IsCompact K₁` using `hK.image (by fun_prop)`. Take `⟨C, hC, hCK⟩` from `tsfin_compact_lift _ hc hK₁`. Set `L : Matrix (Fin M) (Fin (M + 1)) E` to `J'⁻¹ * (Formalism.UG.cT (σ : E →+* E) B * J)`. Establish `hL : L * B = 1`.

Rewrite using `[Matrix.mul_assoc, ← hJ']`. Conclude with `Matrix.nonsing_inv_mul _ (Ne.isUnit hJ'nd.2)`. Establish `hL' : L.map (inclR (F` using `F) R) * B.map (inclR (F := F) R) = 1 := by`. Rewrite using `[← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]`. Set `K' : Set (Fin 1 → Fin M → R ⊗[F] E)` to `(fun p : HA R σ J × (Fin 2 → Fin (M + 1) → R ⊗[F] E) => fun _ => (L.map (inclR (F := F) R)).mulVec ((p.1⁻¹ • p.2) 1)) '' (C ×ˢ K)`.

Establish `hK' : IsCompact K'` using `(hC.prod hK).image (continuous_pi fun _ => continuous_const.matrix_mulVec ((continuous_apply 1).comp (continuous_fst.inv.smul continuous_snd)))`. Set `s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ J` to `fun y => if h : ∃ g ∈ C, g • ratTup (F := F) R x = y then h.choose else if h' : ∃ g : HA R σ J, g • ratTup (F := F) R x = y then h'.choose else 1`. Establish `hs : IsSec R σ J x s`. Introduce `y hy`. Distinguish the cases in `h : ∃ g ∈ C, g • ratTup (F := F) R x = y`.

Simplify using `only [s, dif_pos h]`. Conclude with `h.choose_spec.2`. Simplify using `only [s, dif_neg h, dif_pos hy]`. Conclude with `hy.choose_spec`. Establish `hsC : ∀ y ∈ K₁, (∃ g : HA R σ J, g • ratTup (F` using `F) R x = y) → s y ∈ C := by`.

Introduce `y hy hg`. Establish `h` using `hCK y hy hg`. Simplify using `only [s, dif_pos h]`. Conclude with `h.choose_spec.1`. Establish `h1` using `hT (K.indicator 1) (measurable_one.indicator hK.measurableSet) s hs`.

Rewrite `h1` using `[lintegral_indicator_one hK.measurableSet]`. Rewrite using `[h1]`. Establish `hae : ∀ᵐ y ∂m, ∃ g : HA R σ J, g • ratTup (F` using `F) R x = y := hO`. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_mono_ae (hae.mono fun y hy => ?_)` and prove the remaining obligations.

Distinguish the cases in `hyK : y ∈ K₁`. Rewrite using `[Set.indicator_of_mem hyK, ← lintegral_indicator_one hK'.measurableSet]`. Use `lintegral_mono fun y' => ?_` and prove the remaining obligations. Distinguish the cases in `hp : pairOf R σ J B y (s y) y' ∈ K`. Establish `: y' ∈ K'`.

Use `⟨(s y, pairOf R σ J B y (s y) y'), ⟨hsC y hyK hy, hp⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Establish `e : ((s y)⁻¹ • pairOf R σ J B y (s y) y') 1 = ((s y)⁻¹ • s y • fun _ : Fin 1 => (B.map (inclR (F` using `F) R)).mulVec (y' 0)) 0 := rfl`. Simplify using `only`. Rewrite using `[e, inv_smul_smul, Matrix.mulVec_mulVec, hL', Matrix.one_mulVec, Subsingleton.elim i 0]`.

Simplify using `[Set.indicator_of_mem hp, Set.indicator_of_mem this]`. Simplify using `[Set.indicator_of_notMem hp]`. Establish `: ∀ y', pairOf R σ J B y (s y) y' ∉ K` using `fun y' hp => hyK ⟨_, hp, funext fun i => by rw [Subsingleton.elim i 0]; rfl⟩`. Simplify using `[Set.indicator_of_notMem (this _)]`. Use `_ < ⊤ := by`.

Rewrite using `[lintegral_indicator_const hK₁.measurableSet]`. Conclude with `ENNReal.mul_lt_top hK'.measure_lt_top hK₁.measure_lt_top`.
-/
theorem twoStep_finite_on_compacts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (m : Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : Measure (Fin 1 → Fin M → R ⊗[F] E)) (N : Measure (Fin 2 → Fin (M + 1) → R ⊗[F] E)), StepData σ J x a B J' → OnOrbit R σ J x m → IsFiniteMeasureOnCompacts m → IsFiniteMeasureOnCompacts m' → IsInvTup R σ J' m' → TwoStep R σ J x B m m' N → IsFiniteMeasureOnCompacts N := by
  intro F E _ _ _ _ _ σ hcm R _ _ _ _ _ _ _ _ _ hR M J x a B J' m m' N hS hO hm hm' _ hT
  classical
  obtain ⟨hJ, ha, hx, -, hJ', hJ'nd⟩ := hS
  have hq := tsfin_q_rat R σ J hcm.2.2.1 x a hx
  have hu : IsUnit (algebraMap F R a) := (IsUnit.mk0 a ha).map _
  have hc : IsClosed (MulAction.orbit (HA R σ J) (ratTup (F := F) R x)) := by
    have : MulAction.orbit (HA R σ J) (ratTup (F := F) R x) =
        {y | qR R σ J (y 0) = algebraMap F R a} := by
      ext y
      constructor
      · rintro ⟨g, rfl⟩
        exact (tsfin_q_smul R σ J g _).trans hq
      · intro hy
        exact GlobalTheory.GaugeWittLoc.exists_smul_eq F E σ hcm R hR (M + 1) J hJ _ _ y hu hq hy
    rw [this]
    exact isClosed_eq (tsfin_q_cont R σ J) continuous_const
  refine ⟨fun K hK => ?_⟩
  let K₁ : Set (Fin 1 → Fin (M + 1) → R ⊗[F] E) := (fun X _ => X 0) '' K
  have hK₁ : IsCompact K₁ := hK.image (by fun_prop)
  obtain ⟨C, hC, hCK⟩ := tsfin_compact_lift _ hc hK₁
  let L : Matrix (Fin M) (Fin (M + 1)) E := J'⁻¹ * (Formalism.UG.cT (σ : E →+* E) B * J)
  have hL : L * B = 1 := by
    rw [Matrix.mul_assoc, ← hJ']
    exact Matrix.nonsing_inv_mul _ (Ne.isUnit hJ'nd.2)
  have hL' : L.map (inclR (F := F) R) * B.map (inclR (F := F) R) = 1 := by
    rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  let K' : Set (Fin 1 → Fin M → R ⊗[F] E) :=
    (fun p : HA R σ J × (Fin 2 → Fin (M + 1) → R ⊗[F] E) => fun _ =>
      (L.map (inclR (F := F) R)).mulVec ((p.1⁻¹ • p.2) 1)) '' (C ×ˢ K)
  have hK' : IsCompact K' := (hC.prod hK).image (continuous_pi fun _ =>
    continuous_const.matrix_mulVec ((continuous_apply 1).comp (continuous_fst.inv.smul continuous_snd)))
  let s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ J := fun y =>
    if h : ∃ g ∈ C, g • ratTup (F := F) R x = y then h.choose
    else if h' : ∃ g : HA R σ J, g • ratTup (F := F) R x = y then h'.choose else 1
  have hs : IsSec R σ J x s := by
    intro y hy
    by_cases h : ∃ g ∈ C, g • ratTup (F := F) R x = y
    · simp only [s, dif_pos h]
      exact h.choose_spec.2
    · simp only [s, dif_neg h, dif_pos hy]
      exact hy.choose_spec
  have hsC : ∀ y ∈ K₁, (∃ g : HA R σ J, g • ratTup (F := F) R x = y) → s y ∈ C := by
    intro y hy hg
    have h := hCK y hy hg
    simp only [s, dif_pos h]
    exact h.choose_spec.1
  have h1 := hT (K.indicator 1) (measurable_one.indicator hK.measurableSet) s hs
  rw [lintegral_indicator_one hK.measurableSet] at h1
  rw [h1]
  have hae : ∀ᵐ y ∂m, ∃ g : HA R σ J, g • ratTup (F := F) R x = y := hO
  calc _ ≤ ∫⁻ y, K₁.indicator (fun _ => m' K') y ∂m := by
        refine lintegral_mono_ae (hae.mono fun y hy => ?_)
        by_cases hyK : y ∈ K₁
        · rw [Set.indicator_of_mem hyK, ← lintegral_indicator_one hK'.measurableSet]
          refine lintegral_mono fun y' => ?_
          by_cases hp : pairOf R σ J B y (s y) y' ∈ K
          · have : y' ∈ K' := by
              refine ⟨(s y, pairOf R σ J B y (s y) y'), ⟨hsC y hyK hy, hp⟩, ?_⟩
              funext i
              have e : ((s y)⁻¹ • pairOf R σ J B y (s y) y') 1 =
                  ((s y)⁻¹ • s y • fun _ : Fin 1 => (B.map (inclR (F := F) R)).mulVec (y' 0)) 0 := rfl
              simp only
              rw [e, inv_smul_smul, Matrix.mulVec_mulVec, hL', Matrix.one_mulVec,
                Subsingleton.elim i 0]
            simp [Set.indicator_of_mem hp, Set.indicator_of_mem this]
          · simp [Set.indicator_of_notMem hp]
        · have : ∀ y', pairOf R σ J B y (s y) y' ∉ K := fun y' hp =>
            hyK ⟨_, hp, funext fun i => by rw [Subsingleton.elim i 0]; rfl⟩
          simp [Set.indicator_of_notMem (this _)]
    _ < ⊤ := by
        rw [lintegral_indicator_const hK₁.measurableSet]
        exact ENNReal.mul_lt_top hK'.measure_lt_top hK₁.measure_lt_top

end GlobalTheory.GaugeEx
