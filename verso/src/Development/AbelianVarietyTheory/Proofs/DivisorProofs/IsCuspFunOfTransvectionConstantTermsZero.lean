import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransvectionSubgroupCocompactHaarFundamentalDomaStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyCompactSecondCountableBorelCountable
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsCuspFunOnePlane

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TransvCusp

section Abstract

variable {N : Type} [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [MeasurableSpace N] [BorelSpace N]
  {Γ : Subgroup N} [Countable Γ] {μ : Measure N} [μ.IsMulLeftInvariant] {𝓕 : Set N}

/- English proof (translation)
The claim follows from `h.preimage_of_equiv (measurePreserving_mul_left μ z).quasiMeasurePreserving (e := id) Function.bijective_id fun γ n => by change z * ((γ : N) * n) = (γ : N) * (z * n) rw [← mul_assoc, hz, mul_assoc]`.
-/
theorem fd_preimage (h : IsFundamentalDomain Γ 𝓕 μ) {z : N} (hz : ∀ n, z * n = n * z) :
    IsFundamentalDomain Γ ((fun n => z * n) ⁻¹' 𝓕) μ :=
  h.preimage_of_equiv (measurePreserving_mul_left μ z).quasiMeasurePreserving (e := id) Function.bijective_id
    fun γ n => by
      change z * ((γ : N) * n) = (γ : N) * (z * n)
      rw [← mul_assoc, hz, mul_assoc]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `F (z * ((γ : N) * n)) = _`. Rewrite using `[← mul_assoc, hz, mul_assoc, hF]`.
-/
theorem inv_shift {B : Type} {z : N} (hz : ∀ n, z * n = n * z) {F : N → B} (hF : ∀ (γ : Γ) n, F ((γ : N) * n) = F n)
    (γ : Γ) (n : N) : F (z * (γ • n)) = F (z * n) := by
  change F (z * ((γ : N) * n)) = _
  rw [← mul_assoc, hz, mul_assoc, hF]

/- English proof (translation)
Rewrite using `[h.setIntegral_eq (fd_preimage h hz) (f := fun n => F (z * n)) (inv_shift hz hF)]`. Conclude with `(measurePreserving_mul_left μ z).setIntegral_preimage_emb (MeasurableEquiv.mulLeft z).measurableEmbedding F 𝓕`.
-/
theorem setIntegral_shift {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] (h : IsFundamentalDomain Γ 𝓕 μ)
    {z : N} (hz : ∀ n, z * n = n * z) {F : N → B} (hF : ∀ (γ : Γ) n, F ((γ : N) * n) = F n) :
    ∫ n in 𝓕, F (z * n) ∂μ = ∫ n in 𝓕, F n ∂μ := by
  rw [h.setIntegral_eq (fd_preimage h hz) (f := fun n => F (z * n)) (inv_shift hz hF)]
  exact (measurePreserving_mul_left μ z).setIntegral_preimage_emb (MeasurableEquiv.mulLeft z).measurableEmbedding F 𝓕

/- English proof (translation)
Rewrite using `[h.integrableOn_iff (fd_preimage h hz) (f := fun n => F (z * n)) (inv_shift hz hF)]`. Conclude with `((measurePreserving_mul_left μ z).integrableOn_comp_preimage (MeasurableEquiv.mulLeft z).measurableEmbedding).2 hi`.
-/
theorem integrableOn_shift {B : Type} [NormedAddCommGroup B] (h : IsFundamentalDomain Γ 𝓕 μ)
    {z : N} (hz : ∀ n, z * n = n * z) {F : N → B} (hF : ∀ (γ : Γ) n, F ((γ : N) * n) = F n)
    (hi : IntegrableOn F 𝓕 μ) : IntegrableOn (fun n => F (z * n)) 𝓕 μ := by
  rw [h.integrableOn_iff (fd_preimage h hz) (f := fun n => F (z * n)) (inv_shift hz hF)]
  exact ((measurePreserving_mul_left μ z).integrableOn_comp_preimage
    (MeasurableEquiv.mulLeft z).measurableEmbedding).2 hi

/- English proof (translation)
Distinguish the cases in `hI : IntegrableOn F 𝓕 μ`. Use `swap`. Conclude with `integral_undef hI`. Establish `hm : AEStronglyMeasurable (Function.uncurry fun (z : Z) (n : N) => F (i z * n)) (ν.prod (μ.restrict 𝓕))` using `(hc.comp ((hi.comp continuous_fst).mul continuous_snd)).aestronglyMeasurable`. Establish `hp : Integrable (Function.uncurry fun (z : Z) (n : N) => F (i z * n)) (ν.prod (μ.restrict 𝓕))`.

Use `(integrable_prod_iff hm).2 ⟨Filter.Eventually.of_forall fun z => integrableOn_shift h (hz z) hF hI, ?_⟩` and prove the remaining obligations. Establish `e : (fun z : Z => ∫ n in 𝓕, ‖F (i z * n)‖ ∂μ) = fun _ => ∫ n in 𝓕, ‖F n‖ ∂μ`. Use function extensionality and compare the values at `fun z => setIntegral_shift h (hz z) (F := fun n => ‖F n‖) fun γ n => by rw [hF]`. Conclude with `e ▸ integrable_const _`. Establish `key` using `integral_integral_swap hp`.

Simplify using `only [h0, integral_zero, setIntegral_shift h (hz _) hF, integral_const, smul_eq_zero] at key`. Conclude with `key.resolve_left (by simpa [measureReal_eq_zero_iff] using hν)`.
-/
theorem setIntegral_eq_zero [SecondCountableTopology N] [SFinite μ] {Z : Type} [TopologicalSpace Z] [MeasurableSpace Z]
    [OpensMeasurableSpace Z] (ν : Measure Z) [IsFiniteMeasure ν] (hν : ν ≠ 0) (i : Z → N) (hi : Continuous i)
    (hz : ∀ z n, i z * n = n * i z) (h : IsFundamentalDomain Γ 𝓕 μ) {F : N → ℂ} (hc : Continuous F)
    (hF : ∀ (γ : Γ) n, F ((γ : N) * n) = F n) (h0 : ∀ n, ∫ z, F (i z * n) ∂ν = 0) : ∫ n in 𝓕, F n ∂μ = 0 := by
  by_cases hI : IntegrableOn F 𝓕 μ
  swap
  · exact integral_undef hI
  have hm : AEStronglyMeasurable (Function.uncurry fun (z : Z) (n : N) => F (i z * n)) (ν.prod (μ.restrict 𝓕)) :=
    (hc.comp ((hi.comp continuous_fst).mul continuous_snd)).aestronglyMeasurable
  have hp : Integrable (Function.uncurry fun (z : Z) (n : N) => F (i z * n)) (ν.prod (μ.restrict 𝓕)) := by
    refine (integrable_prod_iff hm).2 ⟨Filter.Eventually.of_forall fun z => integrableOn_shift h (hz z) hF hI, ?_⟩
    have e : (fun z : Z => ∫ n in 𝓕, ‖F (i z * n)‖ ∂μ) = fun _ => ∫ n in 𝓕, ‖F n‖ ∂μ :=
      funext fun z => setIntegral_shift h (hz z) (F := fun n => ‖F n‖) fun γ n => by rw [hF]
    exact e ▸ integrable_const _
  have key := integral_integral_swap hp
  simp only [h0, integral_zero, setIntegral_shift h (hz _) hF, integral_const, smul_eq_zero] at key
  exact key.resolve_left (by simpa [measureReal_eq_zero_iff] using hν)

end Abstract

section Mat

variable {R : Type} [CommRing R] {n r : ℕ} {m m' : Matrix (Fin n) (Fin n) R} {a : R} {C : Matrix (Fin n) (Fin r) R}
  {E : Matrix (Fin r) (Fin r) R} {P : Matrix (Fin r) (Fin n) R}

/- English proof (translation)
Use `⟨?_, ?_, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[ha, Matrix.smul_mul, Matrix.mul_assoc, h0, Matrix.mul_zero, smul_zero]`. Rewrite using `[ha, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h0, Matrix.zero_mul, Matrix.zero_mul, smul_zero]`. Rewrite using `[ha, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero, smul_zero, Matrix.mulVec_zero]`.
-/
theorem mat_kill (ha : m = a • (C * E * P)) (h0 : P * C = 0) :
    m * C = 0 ∧ P * m = 0 ∧ ∀ x, P *ᵥ x = 0 → m *ᵥ x = C *ᵥ 0 := by
  refine ⟨?_, ?_, fun x hx => ?_⟩
  · rw [ha, Matrix.smul_mul, Matrix.mul_assoc, h0, Matrix.mul_zero, smul_zero]
  · rw [ha, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h0, Matrix.zero_mul, Matrix.zero_mul, smul_zero]
  · rw [ha, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero, smul_zero, Matrix.mulVec_zero]

/- English proof (translation)
Establish `e : Commute (m - 1) (m' - 1)`. Rewrite using `[Commute, SemiconjBy, ha, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, h2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul]`. Use `(e.add_left (Commute.one_left _)).add_right (Commute.one_right _)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel, sub_add_cancel]`. Conclude with `this`.
-/
theorem mat_comm (ha : m - 1 = a • (C * E * P)) (h1 : (m' - 1) * C = 0) (h2 : P * (m' - 1) = 0) :
    m * m' = m' * m := by
  have e : Commute (m - 1) (m' - 1) := by
    rw [Commute, SemiconjBy, ha, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, h2, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, h1, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul]
  have := (e.add_left (Commute.one_left _)).add_right (Commute.one_right _)
  rw [sub_add_cancel, sub_add_cancel] at this
  exact this

/- English proof (translation)
Proceed by induction on `hx using Subgroup.closure_induction with`. Consider the case `mem x hx`. Proceed by induction on `hy using Subgroup.closure_induction with`. Consider the case `mem y hy => exact h x hx y hy`. Consider the case `one => exact Commute.one_right _`.

Consider the case `mul _ _ _ _ k k' => exact k.mul_right k'`. Consider the case `inv _ _ k => exact k.inv_right`. Consider the case `one => exact Commute.one_left _`. Consider the case `mul _ _ _ _ k k' => exact k.mul_left k'`. Consider the case `inv _ _ k => exact k.inv_left`.
-/
theorem commute_closure {G : Type} [Group G] {s t : Set G} (h : ∀ x ∈ s, ∀ y ∈ t, Commute x y) {x y : G}
    (hx : x ∈ Subgroup.closure s) (hy : y ∈ Subgroup.closure t) : Commute x y := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    induction hy using Subgroup.closure_induction with
    | mem y hy => exact h x hx y hy
    | one => exact Commute.one_right _
    | mul _ _ _ _ k k' => exact k.mul_right k'
    | inv _ _ k => exact k.inv_right
  | one => exact Commute.one_left _
  | mul _ _ _ _ k k' => exact k.mul_left k'
  | inv _ _ k => exact k.inv_left

end Mat

section Algebra

variable {D : D7} (V : HSp D) {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single j]`. Rewrite using `[Matrix.mul_single_apply_same, mul_one]`. Both sides reduce to the same expression. Introduce `k _ hk`.

Rewrite using `[Matrix.mul_single_apply_of_ne _ _ _ _ _ hk, zero_mul]`. Conclude with `fun h => absurd (Finset.mem_univ j) h`.
-/
theorem vecMulVec_col (j : Fin r) :
    vecMulVec (fun i => C i j) ((fun i => (D.sp.cm.sig : D.host.E →+* D.host.E) (C i j)) ᵥ* V.gram) =
      C * Matrix.single j j (1 : D.host.E) * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram) := by
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [Matrix.mul_single_apply_same, mul_one]
    rfl
  · intro k _ hk
    rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hk, zero_mul]
  · exact fun h => absurd (Finset.mem_univ j) h

/- English proof (translation)
Use `⟨hC.2.1.ne_zero j, ?_⟩` and prove the remaining obligations. Use `congrFun (congrFun hC.2.2 j) j` as an intermediate fact. Rewrite `this` using `[Matrix.mul_assoc]`. Conclude with `this`.
-/
theorem isoVec_col (hC : IsIsoFrame V C) (j : Fin r) : IsoVec V fun i => C i j := by
  refine ⟨hC.2.1.ne_zero j, ?_⟩
  have := congrFun (congrFun hC.2.2 j) j
  rw [Matrix.mul_assoc] at this
  exact this

/- English proof (translation)
Use `Subgroup.closure_mono ?_` and prove the remaining obligations. Introduce and unpack `g ⟨a, ha⟩`. Establish `h0 : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram).map (incA D) * C.map (incA D) = 0`. Rewrite using `[← Matrix.map_mul, hC.2.2, Matrix.map_zero _ (map_zero _)]`. Rewrite `ha` using `[vecMulVec_col, Matrix.map_mul, Matrix.map_mul]`.

Take `⟨k1, k2, k3⟩` from `mat_kill ha h0`. Use `⟨k1, k2, fun x hx => ⟨0, k3 _ (funext fun i => ?_)⟩⟩` and prove the remaining obligations. Use `RingHom.map_mulVec (incA D) (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram) x i` as an intermediate fact. Rewrite `this` using `[hx, Pi.zero_apply, map_zero]`. Conclude with `this.symm`.
-/
theorem ZI_le (hC : IsIsoFrame V C) (j : Fin r) : ZI V (fun i => C i j) ≤ NI V C := by
  refine Subgroup.closure_mono ?_
  rintro g ⟨a, ha⟩
  have h0 : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram).map (incA D) * C.map (incA D) = 0 := by
    rw [← Matrix.map_mul, hC.2.2, Matrix.map_zero _ (map_zero _)]
  rw [vecMulVec_col, Matrix.map_mul, Matrix.map_mul] at ha
  obtain ⟨k1, k2, k3⟩ := mat_kill ha h0
  refine ⟨k1, k2, fun x hx => ⟨0, k3 _ (funext fun i => ?_)⟩⟩
  have := RingHom.map_mulVec (incA D) (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram) x i
  rw [hx, Pi.zero_apply, map_zero] at this
  exact this.symm

/- English proof (translation)
Use `commute_closure ?_ hz hn` and prove the remaining obligations. Introduce and unpack `z ⟨a, ha⟩ n ⟨h1, h2, -⟩`. Rewrite `ha` using `[vecMulVec_col, Matrix.map_mul, Matrix.map_mul]`. Conclude with `Subtype.ext (Units.ext (mat_comm ha h1 h2))`.
-/
theorem ZI_comm (j : Fin r) {z n : GA D V} (hz : z ∈ ZI V fun i => C i j) (hn : n ∈ NI V C) : Commute z n := by
  refine commute_closure ?_ hz hn
  rintro z ⟨a, ha⟩ n ⟨h1, h2, -⟩
  rw [vecMulVec_col, Matrix.map_mul, Matrix.map_mul] at ha
  exact Subtype.ext (Units.ext (mat_comm ha h1 h2))

end Algebra

/- English proof (translation)
Introduce `D θ V hθ φ hφ hZ r C hC μ 𝓕 hμ h𝓕 g`. Take `⟨h1, h2, h3, h4, h5, h6, h7⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V`. Set `j : Fin r` to `⟨0, hC.1⟩`. Establish `hξ` using `isoVec_col V hC j`. Take `⟨⟨ν, 𝓖, hν, h𝓖, -⟩, hm, -⟩` from `GlobalTheory.T.transvectionSubgroup_cocompact_haar_fundamentalDomain D θ V hθ _ hξ`.

Take `⟨m0, m1⟩` from `hm ν 𝓖 hν h𝓖`. Establish `: LocallyCompactSpace (NI V C)` using `(GlobalTheory.CuspDecay.Model.isClosed_NI V hC).locallyCompactSpace`. Set `i : NIQ V C → GQ V` to `fun x => ⟨x.1.1, x.2⟩`. Establish `hi : Function.Injective i` using `fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z : GQ V => z.1) h))`. Establish `: Countable (NIQ V C)` using `hi.countable`.

Establish `: SecondCountableTopology (NI V C)` using `TopologicalSpace.Subtype.secondCountableTopology _`. Establish `: IsFiniteMeasure (ν.restrict 𝓖)` using `isFiniteMeasure_restrict.2 m1`. Use `setIntegral_eq_zero (ν.restrict 𝓖) (fun h => m0 (Measure.restrict_eq_zero.1 h)) (Subgroup.inclusion (ZI_le V hC j)) (continuous_subtype_val.subtype_mk _) (fun z n => Subtype.ext (ZI_comm V j z.2 n.2)) h𝓕 (F := fun n => φ ((n : GA D V) * g)) (hφ.cont.comp (continuous_subtype_val.m …` and prove the remaining obligations. Rewrite using `[Subgroup.coe_mul, mul_assoc]`. Conclude with `hφ.left _ γ.2 _`.

Simplify `hZ _ hξ ν 𝓖 hν h𝓖 ((n : GA D V) * g)` using `only [Subgroup.coe_mul, mul_assoc, Subgroup.coe_inclusion]`.
-/
theorem isCuspFun_of_zCusp : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ φ : GA D V → ℂ, IsAutFun V φ →
    ZCusp V φ → IsCuspFun V φ := by
  intro D θ V hθ φ hφ hZ r C hC μ 𝓕 hμ h𝓕 g
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  let j : Fin r := ⟨0, hC.1⟩
  have hξ := isoVec_col V hC j
  obtain ⟨⟨ν, 𝓖, hν, h𝓖, -⟩, hm, -⟩ := GlobalTheory.T.transvectionSubgroup_cocompact_haar_fundamentalDomain D θ V hθ _ hξ
  obtain ⟨m0, m1⟩ := hm ν 𝓖 hν h𝓖
  have : LocallyCompactSpace (NI V C) := (GlobalTheory.CuspDecay.Model.isClosed_NI V hC).locallyCompactSpace
  let i : NIQ V C → GQ V := fun x => ⟨x.1.1, x.2⟩
  have hi : Function.Injective i := fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z : GQ V => z.1) h))
  have : Countable (NIQ V C) := hi.countable
  have : SecondCountableTopology (NI V C) := TopologicalSpace.Subtype.secondCountableTopology _
  have : IsFiniteMeasure (ν.restrict 𝓖) := isFiniteMeasure_restrict.2 m1
  refine setIntegral_eq_zero (ν.restrict 𝓖) (fun h => m0 (Measure.restrict_eq_zero.1 h))
    (Subgroup.inclusion (ZI_le V hC j)) (continuous_subtype_val.subtype_mk _)
    (fun z n => Subtype.ext (ZI_comm V j z.2 n.2)) h𝓕 (F := fun n => φ ((n : GA D V) * g))
    (hφ.cont.comp (continuous_subtype_val.mul continuous_const)) (fun γ n => ?_) fun n => ?_
  · rw [Subgroup.coe_mul, mul_assoc]
    exact hφ.left _ γ.2 _
  · simpa only [Subgroup.coe_mul, mul_assoc, Subgroup.coe_inclusion] using hZ _ hξ ν 𝓖 hν h𝓖 ((n : GA D V) * g)

end GlobalTheory.TransvCusp
