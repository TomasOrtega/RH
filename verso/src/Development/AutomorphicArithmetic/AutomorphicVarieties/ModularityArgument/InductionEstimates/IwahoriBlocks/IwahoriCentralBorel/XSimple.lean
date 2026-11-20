import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.ExistsInjectionIntoL2Cusp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.MemOfTranslates
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.OpenStab
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.PiHomExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.LevLaws

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks

section Abs

variable {G : Type} [Group G] [TopologicalSpace G]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/- English proof (translation)
Establish `hlc : IsLocallyConstant fun u : G => π u m`. Rewrite using `[IsLocallyConstant.iff_exists_open]`. Introduce `x`. Use `⟨(fun y => x⁻¹ * y) ⁻¹' (L' : Set G), hL'.preimage (by fun_prop), by simp, fun y hy => ?_⟩` and prove the remaining obligations. Establish `: y = x * (x⁻¹ * y)` using `by simp`.

Rewrite using `[this, UnitaryRep.map_mul_apply, hm _ hy]`. Use `haveI : CompactSpace (L : Set G) := isCompact_iff_compactSpace.1 hL`. Rewrite using `[Set.image_eq_range]`. Conclude with `(hlc.comp_continuous continuous_subtype_val).range_finite`.
-/
private lemma orbit_finite [IsTopologicalGroup G] (π : UnitaryRep G H) {L L' : Subgroup G} (hL : IsCompact (L : Set G))
    (hL' : IsOpen (L' : Set G)) {m : H} (hm : ∀ u ∈ L', π u m = m) : ((fun u => π u m) '' (L : Set G)).Finite := by
  have hlc : IsLocallyConstant fun u : G => π u m := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨(fun y => x⁻¹ * y) ⁻¹' (L' : Set G), hL'.preimage (by fun_prop), by simp, fun y hy => ?_⟩
    have : y = x * (x⁻¹ * y) := by simp
    rw [this, UnitaryRep.map_mul_apply, hm _ hy]
  haveI : CompactSpace (L : Set G) := isCompact_iff_compactSpace.1 hL
  rw [Set.image_eq_range]
  exact (hlc.comp_continuous continuous_subtype_val).range_finite

/- English proof (translation)
Use `haveI : FiniteDimensional ℂ ↥(M ⊓ E) := Submodule.finiteDimensional_of_le inf_le_right`. Establish `hcl : IsClosed ((M ⊓ E : Submodule ℂ H) : Set H)` using `Submodule.closed_of_finiteDimensional _`. It suffices to establish `h : v ∈ closure ((M ⊓ E : Submodule ℂ H) : Set H) by`. Rewrite `h` using `[hcl.closure_eq]`. Conclude with `h.1`.

Rewrite `hv`, the goal using `[Metric.mem_closure_iff]`. Introduce `ε hε`. Take `⟨m, hm, hd⟩` from `hv ε hε`. Use `set O := (hfin m hm).toFinset with hO`. Establish `hmem : ∀ x, x ∈ O ↔ ∃ u ∈ L, π u m = x`.

Introduce `x`. Simplify using `[hO]`. Establish `hne : O.Nonempty` using `⟨π 1 m, (hmem _).2 ⟨1, L.one_mem, rfl⟩⟩`. Establish `hcard : (0 : ℝ) < O.card` using `by exact_mod_cast hne.card_pos`. Establish `haM : O.centerMass (fun _ => (1 : ℝ)) id ∈ M`.

Rewrite using `[Finset.centerMass]`. Use `M.smul_of_tower_mem _ (M.sum_mem fun x hx => M.smul_of_tower_mem _ ?_)` and prove the remaining obligations. Take `⟨u, hu, rfl⟩` from `(hmem x).1 hx`. Conclude with `hst u hu m hm`. Use `⟨O.centerMass (fun _ => (1 : ℝ)) id, ⟨haM, hE _ haM fun u hu => ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[Finset.centerMass, ContinuousLinearMap.map_smul_of_tower, map_sum]`. Use `congr 1`. Simplify using `only [one_smul, id]`. Use `Finset.sum_nbij' (fun x => π u x) (fun x => π u⁻¹ x) ?_ ?_ ?_ ?_ (fun _ _ => rfl)` and prove the remaining obligations. Introduce `x hx`.

Take `⟨a, ha, rfl⟩` from `(hmem x).1 hx`. Conclude with `(hmem _).2 ⟨u * a, L.mul_mem hu ha, UnitaryRep.map_mul_apply _ _ _ _⟩`. Introduce `x hx`. Take `⟨a, ha, rfl⟩` from `(hmem x).1 hx`. Conclude with `(hmem _).2 ⟨u⁻¹ * a, L.mul_mem (L.inv_mem hu) ha, UnitaryRep.map_mul_apply _ _ _ _⟩`.

Introduce `x _`. Simplify using `[← UnitaryRep.map_mul_apply]`. Introduce `x _`. Simplify using `[← UnitaryRep.map_mul_apply]`. Rewrite using `[dist_comm, ← Metric.mem_ball]`.

Use `(convex_ball v ε).centerMass_mem (fun _ _ => zero_le_one) (by simpa using hcard) fun x hx => ?_` and prove the remaining obligations. Take `⟨a, ha, rfl⟩` from `(hmem x).1 hx`. Rewrite using `[Metric.mem_ball, id, dist_comm, dist_eq_norm, ← hfix a ha, ← map_sub, UnitaryRep.norm_map, ← dist_eq_norm]`. Conclude with `hd`.
-/
private lemma mem_of_closure (π : UnitaryRep G H) (L : Subgroup G) (M E : Submodule ℂ H) [FiniteDimensional ℂ E]
    (hst : ∀ u ∈ L, ∀ m ∈ M, π u m ∈ M) (hfin : ∀ m ∈ M, ((fun u => π u m) '' (L : Set G)).Finite)
    (hE : ∀ m ∈ M, (∀ u ∈ L, π u m = m) → m ∈ E) {v : H} (hv : v ∈ closure (M : Set H))
    (hfix : ∀ u ∈ L, π u v = v) : v ∈ M := by
  haveI : FiniteDimensional ℂ ↥(M ⊓ E) := Submodule.finiteDimensional_of_le inf_le_right
  have hcl : IsClosed ((M ⊓ E : Submodule ℂ H) : Set H) := Submodule.closed_of_finiteDimensional _
  suffices h : v ∈ closure ((M ⊓ E : Submodule ℂ H) : Set H) by
    rw [hcl.closure_eq] at h
    exact h.1
  rw [Metric.mem_closure_iff] at hv ⊢
  intro ε hε
  obtain ⟨m, hm, hd⟩ := hv ε hε
  set O := (hfin m hm).toFinset with hO
  have hmem : ∀ x, x ∈ O ↔ ∃ u ∈ L, π u m = x := by
    intro x
    simp [hO]
  have hne : O.Nonempty := ⟨π 1 m, (hmem _).2 ⟨1, L.one_mem, rfl⟩⟩
  have hcard : (0 : ℝ) < O.card := by exact_mod_cast hne.card_pos
  have haM : O.centerMass (fun _ => (1 : ℝ)) id ∈ M := by
    rw [Finset.centerMass]
    refine M.smul_of_tower_mem _ (M.sum_mem fun x hx => M.smul_of_tower_mem _ ?_)
    obtain ⟨u, hu, rfl⟩ := (hmem x).1 hx
    exact hst u hu m hm
  refine ⟨O.centerMass (fun _ => (1 : ℝ)) id, ⟨haM, hE _ haM fun u hu => ?_⟩, ?_⟩
  · rw [Finset.centerMass, ContinuousLinearMap.map_smul_of_tower, map_sum]
    congr 1
    simp only [one_smul, id]
    refine Finset.sum_nbij' (fun x => π u x) (fun x => π u⁻¹ x) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := (hmem x).1 hx
      exact (hmem _).2 ⟨u * a, L.mul_mem hu ha, UnitaryRep.map_mul_apply _ _ _ _⟩
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := (hmem x).1 hx
      exact (hmem _).2 ⟨u⁻¹ * a, L.mul_mem (L.inv_mem hu) ha, UnitaryRep.map_mul_apply _ _ _ _⟩
    · intro x _
      simp [← UnitaryRep.map_mul_apply]
    · intro x _
      simp [← UnitaryRep.map_mul_apply]
  · rw [dist_comm, ← Metric.mem_ball]
    refine (convex_ball v ε).centerMass_mem (fun _ _ => zero_le_one) (by simpa using hcard) fun x hx => ?_
    obtain ⟨a, ha, rfl⟩ := (hmem x).1 hx
    rw [Metric.mem_ball, id, dist_comm, dist_eq_norm, ← hfix a ha, ← map_sub, UnitaryRep.norm_map, ← dist_eq_norm]
    exact hd

end Abs

section Cl

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

/- English proof (translation)
Take `⟨-, -, -, harc, hcs, -⟩` from `levLaws (K := K) n ∅`. Use `haveI := hcs`. Use `haveI := hp.haar.prob`. Establish `hi : ∀ v, Integrable (fun k => p k • rightRegularRep (Gam K n) μ (arc1 k) v) κ` using `fun v => (hp.cont.smul (((rightRegularRep (Gam K n) μ).continuous_orbit v).comp harc)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)`. Establish `hb : ∀ v v', dist (pOp μ κ p v) (pOp μ κ p v') ≤ (∫ k, ‖p k‖ ∂κ) * dist v v'`.

Introduce `v v'`. Rewrite using `[dist_eq_norm, dist_eq_norm, pOp, pOp, ← integral_sub (hi v) (hi v'), ← integral_mul_const]`. Use `(norm_integral_le_integral_norm _).trans (le_of_eq ?_)` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `k`.

Rewrite using `[← smul_sub, ← map_sub, norm_smul, UnitaryRep.norm_map]`. Conclude with `(LipschitzWith.of_dist_le' hb).continuous`.
-/
private lemma continuous_pOp (μ : Measure (G1 K n)) [μ.IsHaarMeasure] {κ : Measure (archCompact K n)}
    {p : archCompact K n → ℂ} (hp : IdemA κ p) : Continuous (pOp μ κ p) := by
  obtain ⟨-, -, -, harc, hcs, -⟩ := levLaws (K := K) n ∅
  haveI := hcs
  haveI := hp.haar.prob
  have hi : ∀ v, Integrable (fun k => p k • rightRegularRep (Gam K n) μ (arc1 k) v) κ := fun v =>
    (hp.cont.smul (((rightRegularRep (Gam K n) μ).continuous_orbit v).comp harc)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hb : ∀ v v', dist (pOp μ κ p v) (pOp μ κ p v') ≤ (∫ k, ‖p k‖ ∂κ) * dist v v' := by
    intro v v'
    rw [dist_eq_norm, dist_eq_norm, pOp, pOp, ← integral_sub (hi v) (hi v'), ← integral_mul_const]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1
    funext k
    rw [← smul_sub, ← map_sub, norm_smul, UnitaryRep.norm_map]
  exact (LipschitzWith.of_dist_le' hb).continuous

/- English proof (translation)
Simplify using `[fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus]`.
-/
private lemma mem_fixF (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (U : Subgroup (FA K n)) (v : L2 μ) :
    v ∈ fixF μ U ↔ ∀ u ∈ U, rhoF μ u v = v := by
  simp [fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus]

/- English proof (translation)
Establish `hf : ∀ U : Subgroup (FA K n), IsClosed (fixF μ U : Set (L2 μ))`. Introduce `U`. Establish `h : (fixF μ U : Set (L2 μ)) = ⋂ u ∈ U, {v | rhoF μ u v = v}`. Use extensionality with `v`. Simplify using `[mem_fixF]`.

Rewrite using `[h]`. Conclude with `isClosed_biInter fun u _ => isClosed_eq (rhoF μ u).continuous continuous_id`. Establish `hs : IsClosed (sphOff μ S : Set (L2 μ))`. Rewrite using `[sphOff]`. Simplify using `only [Submodule.coe_iInf]`.

Conclude with `isClosed_iInter fun v => isClosed_iInter fun _ => hf _`. Conclude with `hτ.closed.inter ((isClosed_eq (continuous_pOp μ hp) continuous_id).inter hs)`.
-/
private lemma isClosed_inH (μ : Measure (G1 K n)) [μ.IsHaarMeasure] {τ : Submodule ℂ (L2 μ)} (hτ : CuspIrr μ τ)
    {κ : Measure (archCompact K n)} {p : archCompact K n → ℂ} (hp : IdemA κ p) (S : Finset (Pl K)) :
    IsClosed {v | InH μ τ κ p S v} := by
  have hf : ∀ U : Subgroup (FA K n), IsClosed (fixF μ U : Set (L2 μ)) := by
    intro U
    have h : (fixF μ U : Set (L2 μ)) = ⋂ u ∈ U, {v | rhoF μ u v = v} := by
      ext v
      simp [mem_fixF]
    rw [h]
    exact isClosed_biInter fun u _ => isClosed_eq (rhoF μ u).continuous continuous_id
  have hs : IsClosed (sphOff μ S : Set (L2 μ)) := by
    rw [sphOff]
    simp only [Submodule.coe_iInf]
    exact isClosed_iInter fun v => isClosed_iInter fun _ => hf _
  exact hτ.closed.inter ((isClosed_eq (continuous_pOp μ hp) continuous_id).inter hs)

end Cl

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks

/- English proof (translation)
Introduce `K _ _ _ μ _ τ κ p hτ hR r w ι hw hι`. Establish `hp : IdemA κ p` using `hR.1`. Take `⟨hX, hX'⟩` from `xMem μ τ κ p hp`. Establish `hstab` using `fun φ hφ => (hX' hτ w ι hw hι φ hφ).2`. Take `⟨J, hJi, hJ, hJr, hJU⟩` from `exists_injection_into_l2_cusp μ τ κ p hτ hp (im w)`.

Take `⟨-, hcw, hco, -, -, hlev⟩` from `(embEx 2 w hw).2 ι hι`. Establish `hcw1 : ∀ i, GM.cf (w i) (1 : FA K 2) = 1` using `fun i => by`. Use `hcw 1 i` as an intermediate fact. Rewrite `this` using `[map_one]`. Then use the resulting hypothesis. Establish `hcv1 : ∀ v, GM.cf v (1 : FA K 2) = 1` using `fun v => by`.

Distinguish the cases in `hv : v ∈ im w`. Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 hv`. Conclude with `hcw1 i`. Use `hco 1 v hv` as an intermediate fact. Rewrite `this` using `[map_one]`. Then use the resulting hypothesis.

Establish `hCO` using `(levLaws (K := K) 2 (im w)).1`. Establish `hrS : ∀ g (φ : G1 K 2 → ℂ) x, rS ι g φ x = φ (x * fin1 (ι g))` using `fun _ _ _ => rfl`. Establish `hdec : ∀ U, ∀ u ∈ levOn (im w) U, ∃ g, ι g ∈ levOn (im w) U ∧ ∀ φ ∈ Xs μ τ κ p (im w), ∀ x, φ (x * fin1 u) = rS ι g φ x`. Introduce `U u hu`. Take `⟨g, h', rfl, hg, h1, h2⟩` from `(hlev U u).1 hu`.

Use `⟨g, (hlev U _).2 ⟨g, 1, (mul_one _).symm, hg, hcw1, fun v => ?_⟩, fun φ hφ x => ?_⟩` and prove the remaining obligations. Rewrite using `[hcv1]`. Conclude with `one_mem _`. Take `⟨-, -, -, U', -, hU'⟩` from `(hX _ _).1 hφ`. Use `hU' h' ((hlev U' _).2 ⟨1, h', by simp, fun i => one_mem _, h1, h2⟩) (x * fin1 (ι g))` as an intermediate fact.

Rewrite using `[hrS, ← this]`. Simplify using `only [fin1, map_mul, mul_assoc]`. Set `π : UnitaryRep (FA K 2) (L2 μ)` to `(rightRegularRep (rationalGLOne K 2) μ).compHom (MultiplicityOne.finProj K 2) MultiplicityOne.continuous_finProj`. Establish `hπ : ∀ h, π h = rhoF μ h` using `fun _ => rfl`. Establish `hfixJ : ∀ (L : Subgroup (FA K 2)) (φ : Xs μ τ κ p (im w)), FixF L φ.1 → ∀ u ∈ L, rhoF μ u (J φ) = J φ` using `fun L φ hφ u hu => (hJr u φ φ fun x => (hφ u hu x).symm).symm`.

Establish `hS : SimpleIn (rS ι) (Xs μ τ κ p (im w))`. Use `⟨fun g φ hφ => hstab φ hφ g, fun Q hQ hQs => ?_⟩` and prove the remaining obligations. Set `M : Submodule ℂ (L2 μ)` to `(Q.comap (Xs μ τ κ p (im w)).subtype).map J`. Establish `hM : ∀ g, ∀ m ∈ M, rhoF μ (ι g) m ∈ M`. Introduce and unpack `g _ ⟨φ, hφ, rfl⟩`.

Conclude with `⟨⟨rS ι g φ.1, hstab _ φ.2 g⟩, hQs g _ hφ, hJr _ _ _ fun x => rfl⟩`. Establish `hT` using `xTop μ τ κ p hτ hR w ι hw hι M.topologicalClosure M.isClosed_topologicalClosure (fun v hv => closure_minimal (s := (M : Set (L2 μ))) (by rintro _ ⟨φ, -, rfl⟩; exact (hJ φ).2) (isClosed_inH μ hτ hp (im w)) hv) (fun g v hv => map_mem_closure (rhoF μ (ι g)).continuous hv (hM g))`. Break down `hT with hT | hT` into its components or cases. Use `left`. Rewrite using `[eq_bot_iff]`.

Introduce `φ hφ`. Establish `h0 : J ⟨φ, hQ hφ⟩ ∈ M.topologicalClosure` using `M.le_topologicalClosure ⟨⟨φ, hQ hφ⟩, hφ, rfl⟩`. Rewrite `h0` using `[hT, Submodule.mem_bot, ← map_zero J]`. Conclude with `congrArg Subtype.val (hJi h0)`. Use `right`.

Use `le_antisymm hQ fun φ hφ => ?_` and prove the remaining obligations. Take `⟨-, -, -, U, hU, hφU⟩` from `(hX _ _).1 hφ`. Take `⟨hsur, E, hE, hEU⟩` from `hJU U hU`. Use `haveI : FiniteDimensional ℂ ↥(E.comap (Xs μ τ κ p (im w)).subtype) := FiniteDimensional.of_injective (((Xs μ τ κ p (im w)).subtype.domRestrict (E.comap (Xs μ τ κ p (im w)).subtype)).codRestrict E fun a => a.2) fun a b h => Subtype.ext (Subtype.ext (congrArg (fun z : E => (z : G1 …`. Establish `key : J ⟨φ, hφ⟩ ∈ M`.

Use `mem_of_closure π (levOn (im w) U) M ((E.comap (Xs μ τ κ p (im w)).subtype).map J) ?_ ?_ ?_ (hT _ (hJ _).2) (hfixJ _ ⟨φ, hφ⟩ hφU)` and prove the remaining obligations. Introduce and unpack `u hu _ ⟨ψ, hψ, rfl⟩`. Take `⟨g, -, hg⟩` from `hdec U u hu`. Conclude with `⟨⟨rS ι g ψ.1, hstab _ ψ.2 g⟩, hQs g _ hψ, hJr _ _ _ fun x => (hg _ ψ.2 x).symm⟩`. Introduce and unpack `_ ⟨ψ, -, rfl⟩`.

Take `⟨-, -, -, U', hU', hψU⟩` from `(hX _ _).1 ψ.2`. Conclude with `orbit_finite π (hCO U hU).1.1 (hCO U' hU').1.2 (hfixJ _ ψ hψU)`. Introduce and unpack `_ ⟨ψ, -, rfl⟩ hf`. Take `⟨ψ', h1, h2⟩` from `hsur _ (hJ ψ).2 ((mem_fixF μ _ _).2 hf)`. Conclude with `⟨ψ', hEU _ ψ'.2 h2, h1⟩`.

Take `⟨ψ, hψ, h⟩` from `key`. Rewrite `hψ` using `[hJi h]`. Conclude with `hψ`. Use `⟨hS, fun T hT => ?_⟩` and prove the remaining obligations. Distinguish the cases in `h0 : ∀ φ : Xs μ τ κ p (im w), φ = 0`.

Conclude with `⟨0, fun v => by rw [h0 (T v), zero_smul]⟩`. Use `push Not at h0`. Take `⟨φ, hφ0⟩` from `h0`. Take `⟨-, -, -, U, hU, hφU⟩` from `(hX _ _).1 φ.2`. Take `⟨-, E, hE, hEU⟩` from `hJU U hU`.

Set `F : Submodule ℂ (Xs μ τ κ p (im w))` to `{ carrier := {ψ | FixF (levOn (im w) U) ψ.1} add_mem' := fun ha hb u hu g => by simp [ha u hu g, hb u hu g] zero_mem' := fun u hu g => rfl smul_mem' := fun c _ ha u hu g => by simp [ha u hu g] }`. Use `haveI : FiniteDimensional ℂ ↥(E.comap (Xs μ τ κ p (im w)).subtype) := FiniteDimensional.of_injective (((Xs μ τ κ p (im w)).subtype.domRestrict (E.comap (Xs μ τ κ p (im w)).subtype)).codRestrict E fun a => a.2) fun a b h => Subtype.ext (Subtype.ext (congrArg (fun z : E => (z : G1 …`. Use `haveI : FiniteDimensional ℂ F := Submodule.finiteDimensional_of_le (S₂ := E.comap (Xs μ τ κ p (im w)).subtype) fun ψ hψ => hEU _ ψ.2 hψ`. Use `haveI : Nontrivial F := ⟨⟨⟨φ, hφU⟩, 0, fun h => hφ0 (congrArg Subtype.val h)⟩⟩`. Establish `hTF : ∀ ψ ∈ F, T ψ ∈ F`.

Introduce `ψ hψ u hu x`. Take `⟨g, hg, hg'⟩` from `hdec U u hu`. Rewrite using `[hg' _ (T ψ).2, ← hT g ψ ψ (funext fun y => (hψ _ hg y).symm)]`. Take `⟨c, hc⟩` from `Module.End.exists_eigenvalue (T.restrict hTF)`. Take `⟨ψ, hψ⟩` from `hc.exists_hasEigenvector`.

Establish `hψ1 : T ψ.1 = c • ψ.1` using `congrArg Subtype.val hψ.apply_eq_smul`. Use `⟨c, ?_⟩` and prove the remaining obligations. Break down `hS.2 ((Module.End.eigenspace T c).map (Xs μ τ κ p (im w)).subtype) (Submodule.map_subtype_le _ _) (by` into its components or cases. Introduce and unpack `g _ ⟨a, ha, rfl⟩`. Use `⟨⟨rS ι g a.1, hstab _ a.2 g⟩, Module.End.mem_eigenspace_iff.2 (Subtype.ext ?_), rfl⟩` and prove the remaining obligations.

Rewrite using `[hT g a _ rfl, Module.End.mem_eigenspace_iff.1 ha]`. Use the proof step `simp) with h | h`. Establish `: (ψ.1 : G1 K 2 → ℂ) ∈ (Module.End.eigenspace T c).map (Xs μ τ κ p (im w)).subtype` using `⟨ψ.1, Module.End.mem_eigenspace_iff.2 hψ1, rfl⟩`. Rewrite `this` using `[h, Submodule.mem_bot]`. Conclude with `absurd (Subtype.ext (Subtype.ext this)) hψ.2`.

Introduce `v`. Establish `: (v : G1 K 2 → ℂ) ∈ (Module.End.eigenspace T c).map (Xs μ τ κ p (im w)).subtype`. Rewrite using `[h]`. Conclude with `v.2`. Take `⟨a, ha, hav⟩` from `this`.

Rewrite using `[← Subtype.ext hav]`. Conclude with `Module.End.mem_eigenspace_iff.1 ha`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.xSimple :
    ∀ {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (μ : Measure (G1 K 2)) [μ.IsHaarMeasure] (τ : Submodule ℂ (L2 μ)) (κ : Measure (archCompact K 2)) (p : archCompact K 2 → ℂ), CuspIrr μ τ → RankInf μ τ κ p → ∀ {r : ℕ} (w : Fin r → Pl K) (ι : GS 2 w →* FA K 2), Function.Injective w → IsEmb w ι →
      SimpleIn (rS ι) (Xs μ τ κ p (im w)) ∧ SchurIn (rS ι) (Xs μ τ κ p (im w)) := by
  intro K _ _ _ μ _ τ κ p hτ hR r w ι hw hι
  have hp : IdemA κ p := hR.1
  obtain ⟨hX, hX'⟩ := xMem μ τ κ p hp
  have hstab := fun φ hφ => (hX' hτ w ι hw hι φ hφ).2
  obtain ⟨J, hJi, hJ, hJr, hJU⟩ := exists_injection_into_l2_cusp μ τ κ p hτ hp (im w)
  obtain ⟨-, hcw, hco, -, -, hlev⟩ := (embEx 2 w hw).2 ι hι
  have hcw1 : ∀ i, GM.cf (w i) (1 : FA K 2) = 1 := fun i => by
    have := hcw 1 i
    rwa [map_one] at this
  have hcv1 : ∀ v, GM.cf v (1 : FA K 2) = 1 := fun v => by
    by_cases hv : v ∈ im w
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
      exact hcw1 i
    · have := hco 1 v hv
      rwa [map_one] at this
  have hCO := (levLaws (K := K) 2 (im w)).1
  have hrS : ∀ g (φ : G1 K 2 → ℂ) x, rS ι g φ x = φ (x * fin1 (ι g)) := fun _ _ _ => rfl

  have hdec : ∀ U, ∀ u ∈ levOn (im w) U, ∃ g, ι g ∈ levOn (im w) U ∧
      ∀ φ ∈ Xs μ τ κ p (im w), ∀ x, φ (x * fin1 u) = rS ι g φ x := by
    intro U u hu
    obtain ⟨g, h', rfl, hg, h1, h2⟩ := (hlev U u).1 hu
    refine ⟨g, (hlev U _).2 ⟨g, 1, (mul_one _).symm, hg, hcw1, fun v => ?_⟩, fun φ hφ x => ?_⟩
    · rw [hcv1]
      exact one_mem _
    · obtain ⟨-, -, -, U', -, hU'⟩ := (hX _ _).1 hφ
      have := hU' h' ((hlev U' _).2 ⟨1, h', by simp, fun i => one_mem _, h1, h2⟩) (x * fin1 (ι g))
      rw [hrS, ← this]
      simp only [fin1, map_mul, mul_assoc]
  let π : UnitaryRep (FA K 2) (L2 μ) :=
    (rightRegularRep (rationalGLOne K 2) μ).compHom (MultiplicityOne.finProj K 2) MultiplicityOne.continuous_finProj
  have hπ : ∀ h, π h = rhoF μ h := fun _ => rfl
  have hfixJ : ∀ (L : Subgroup (FA K 2)) (φ : Xs μ τ κ p (im w)), FixF L φ.1 → ∀ u ∈ L, rhoF μ u (J φ) = J φ :=
    fun L φ hφ u hu => (hJr u φ φ fun x => (hφ u hu x).symm).symm
  have hS : SimpleIn (rS ι) (Xs μ τ κ p (im w)) := by
    refine ⟨fun g φ hφ => hstab φ hφ g, fun Q hQ hQs => ?_⟩
    let M : Submodule ℂ (L2 μ) := (Q.comap (Xs μ τ κ p (im w)).subtype).map J
    have hM : ∀ g, ∀ m ∈ M, rhoF μ (ι g) m ∈ M := by
      rintro g _ ⟨φ, hφ, rfl⟩
      exact ⟨⟨rS ι g φ.1, hstab _ φ.2 g⟩, hQs g _ hφ, hJr _ _ _ fun x => rfl⟩
    have hT := xTop μ τ κ p hτ hR w ι hw hι M.topologicalClosure M.isClosed_topologicalClosure
      (fun v hv => closure_minimal (s := (M : Set (L2 μ))) (by rintro _ ⟨φ, -, rfl⟩; exact (hJ φ).2)
        (isClosed_inH μ hτ hp (im w)) hv)
      (fun g v hv => map_mem_closure (rhoF μ (ι g)).continuous hv (hM g))
    rcases hT with hT | hT
    · left
      rw [eq_bot_iff]
      intro φ hφ
      have h0 : J ⟨φ, hQ hφ⟩ ∈ M.topologicalClosure := M.le_topologicalClosure ⟨⟨φ, hQ hφ⟩, hφ, rfl⟩
      rw [hT, Submodule.mem_bot, ← map_zero J] at h0
      exact congrArg Subtype.val (hJi h0)
    · right
      refine le_antisymm hQ fun φ hφ => ?_
      obtain ⟨-, -, -, U, hU, hφU⟩ := (hX _ _).1 hφ
      obtain ⟨hsur, E, hE, hEU⟩ := hJU U hU
      haveI : FiniteDimensional ℂ ↥(E.comap (Xs μ τ κ p (im w)).subtype) :=
        FiniteDimensional.of_injective
          (((Xs μ τ κ p (im w)).subtype.domRestrict (E.comap (Xs μ τ κ p (im w)).subtype)).codRestrict E fun a => a.2)
          fun a b h => Subtype.ext (Subtype.ext (congrArg (fun z : E => (z : G1 K 2 → ℂ)) h))
      have key : J ⟨φ, hφ⟩ ∈ M := by
        refine mem_of_closure π (levOn (im w) U) M ((E.comap (Xs μ τ κ p (im w)).subtype).map J) ?_ ?_ ?_
          (hT _ (hJ _).2) (hfixJ _ ⟨φ, hφ⟩ hφU)
        · rintro u hu _ ⟨ψ, hψ, rfl⟩
          obtain ⟨g, -, hg⟩ := hdec U u hu
          exact ⟨⟨rS ι g ψ.1, hstab _ ψ.2 g⟩, hQs g _ hψ, hJr _ _ _ fun x => (hg _ ψ.2 x).symm⟩
        · rintro _ ⟨ψ, -, rfl⟩
          obtain ⟨-, -, -, U', hU', hψU⟩ := (hX _ _).1 ψ.2
          exact orbit_finite π (hCO U hU).1.1 (hCO U' hU').1.2 (hfixJ _ ψ hψU)
        · rintro _ ⟨ψ, -, rfl⟩ hf
          obtain ⟨ψ', h1, h2⟩ := hsur _ (hJ ψ).2 ((mem_fixF μ _ _).2 hf)
          exact ⟨ψ', hEU _ ψ'.2 h2, h1⟩
      obtain ⟨ψ, hψ, h⟩ := key
      rw [hJi h] at hψ
      exact hψ
  refine ⟨hS, fun T hT => ?_⟩
  by_cases h0 : ∀ φ : Xs μ τ κ p (im w), φ = 0
  · exact ⟨0, fun v => by rw [h0 (T v), zero_smul]⟩
  push Not at h0
  obtain ⟨φ, hφ0⟩ := h0
  obtain ⟨-, -, -, U, hU, hφU⟩ := (hX _ _).1 φ.2
  obtain ⟨-, E, hE, hEU⟩ := hJU U hU
  let F : Submodule ℂ (Xs μ τ κ p (im w)) :=
    { carrier := {ψ | FixF (levOn (im w) U) ψ.1}
      add_mem' := fun ha hb u hu g => by simp [ha u hu g, hb u hu g]
      zero_mem' := fun u hu g => rfl
      smul_mem' := fun c _ ha u hu g => by simp [ha u hu g] }
  haveI : FiniteDimensional ℂ ↥(E.comap (Xs μ τ κ p (im w)).subtype) :=
    FiniteDimensional.of_injective
          (((Xs μ τ κ p (im w)).subtype.domRestrict (E.comap (Xs μ τ κ p (im w)).subtype)).codRestrict E fun a => a.2)
          fun a b h => Subtype.ext (Subtype.ext (congrArg (fun z : E => (z : G1 K 2 → ℂ)) h))
  haveI : FiniteDimensional ℂ F :=
    Submodule.finiteDimensional_of_le (S₂ := E.comap (Xs μ τ κ p (im w)).subtype) fun ψ hψ => hEU _ ψ.2 hψ
  haveI : Nontrivial F := ⟨⟨⟨φ, hφU⟩, 0, fun h => hφ0 (congrArg Subtype.val h)⟩⟩
  have hTF : ∀ ψ ∈ F, T ψ ∈ F := by
    intro ψ hψ u hu x
    obtain ⟨g, hg, hg'⟩ := hdec U u hu
    rw [hg' _ (T ψ).2, ← hT g ψ ψ (funext fun y => (hψ _ hg y).symm)]
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (T.restrict hTF)
  obtain ⟨ψ, hψ⟩ := hc.exists_hasEigenvector
  have hψ1 : T ψ.1 = c • ψ.1 := congrArg Subtype.val hψ.apply_eq_smul
  refine ⟨c, ?_⟩
  rcases hS.2 ((Module.End.eigenspace T c).map (Xs μ τ κ p (im w)).subtype) (Submodule.map_subtype_le _ _) (by
    rintro g _ ⟨a, ha, rfl⟩
    refine ⟨⟨rS ι g a.1, hstab _ a.2 g⟩, Module.End.mem_eigenspace_iff.2 (Subtype.ext ?_), rfl⟩
    rw [hT g a _ rfl, Module.End.mem_eigenspace_iff.1 ha]
    simp) with h | h
  · have : (ψ.1 : G1 K 2 → ℂ) ∈ (Module.End.eigenspace T c).map (Xs μ τ κ p (im w)).subtype :=
      ⟨ψ.1, Module.End.mem_eigenspace_iff.2 hψ1, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact absurd (Subtype.ext (Subtype.ext this)) hψ.2
  · intro v
    have : (v : G1 K 2 → ℂ) ∈ (Module.End.eigenspace T c).map (Xs μ τ κ p (im w)).subtype := by
      rw [h]
      exact v.2
    obtain ⟨a, ha, hav⟩ := this
    rw [← Subtype.ext hav]
    exact Module.End.mem_eigenspace_iff.1 ha
