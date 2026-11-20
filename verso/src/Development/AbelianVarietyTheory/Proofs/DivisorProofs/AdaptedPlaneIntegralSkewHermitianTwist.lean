import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLeviLeviElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementAdapted
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSqFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviElementUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentMemIffUnipotentRadicalStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThKCtFin

noncomputable section
namespace GlobalTheory.CtLeviCont
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

instance topRingAE : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
instance borelUA (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : BorelSpace (UA σ J) := ⟨rfl⟩

/- English proof (translation)
Take `⟨K, hK, hs⟩` from `hc`. Use `haveI : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 h𝓕`. Use `continuous_iff_continuousAt.2 fun x => ?_` and prove the remaining obligations. Establish `hcont : Continuous fun p : G × N => φ (p.2.1 * p.1)` using `by fun_prop`. Take `⟨C, hC⟩` from `hK.exists_bound_of_continuousOn (f := fun k : N => φ (k.1 * x)) (by fun_prop)`.

Establish `hev : ∀ᶠ g in 𝓝 x, ∀ k ∈ K, ‖φ (k.1 * g)‖ < C + 1`. Use `hK.eventually_forall_of_forall_eventually fun k hk => ?_` and prove the remaining obligations. Establish `h1 : ‖φ (k.1 * x)‖ < C + 1` using `by linarith [hC k hk]`. Conclude with `(hcont.norm.continuousAt (x := (x, k))).eventually (gt_mem_nhds h1)`. Use `continuousAt_of_dominated (bound := fun _ => C + 1) (.of_forall fun g => ?_) ?_ (integrable_const _) (.of_forall fun u => by fun_prop)` and prove the remaining obligations.

Conclude with `(by fun_prop : Continuous fun u : N => φ (u.1 * g)).aestronglyMeasurable`. Use `hev.mono fun g hg => .of_forall fun u => ?_` and prove the remaining obligations. Take `⟨γ, hγ, hk⟩` from `hs u`. Establish `e : φ (u.1 * g) = φ ((γ * u).1 * g)`. Rewrite using `[Subgroup.coe_mul, mul_assoc, hφ _ (Subgroup.mem_subgroupOf.1 hγ)]`.

Rewrite using `[e]`. Conclude with `(hg _ hk).le`.
-/
theorem continuous_setIntegral_of_cocompact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [FirstCountableTopology G] [MeasurableSpace G] [OpensMeasurableSpace G] {Γ N : Subgroup G} (hc : GlobalTheory.Cusp.Cocompact Γ N)
    {φ : G → ℂ} (hφ : ∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g) (hφc : Continuous φ)
    (μ : Measure N) (𝓕 : Set N) (h𝓕 : μ 𝓕 ≠ ⊤) :
    Continuous fun g => ∫ u in 𝓕, φ (u.1 * g) ∂μ := by
  obtain ⟨K, hK, hs⟩ := hc
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 h𝓕
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hcont : Continuous fun p : G × N => φ (p.2.1 * p.1) := by fun_prop
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (f := fun k : N => φ (k.1 * x)) (by fun_prop)
  have hev : ∀ᶠ g in 𝓝 x, ∀ k ∈ K, ‖φ (k.1 * g)‖ < C + 1 := by
    refine hK.eventually_forall_of_forall_eventually fun k hk => ?_
    have h1 : ‖φ (k.1 * x)‖ < C + 1 := by linarith [hC k hk]
    exact (hcont.norm.continuousAt (x := (x, k))).eventually (gt_mem_nhds h1)
  refine continuousAt_of_dominated (bound := fun _ => C + 1) (.of_forall fun g => ?_) ?_ (integrable_const _)
    (.of_forall fun u => by fun_prop)
  · exact (by fun_prop : Continuous fun u : N => φ (u.1 * g)).aestronglyMeasurable
  · refine hev.mono fun g hg => .of_forall fun u => ?_
    obtain ⟨γ, hγ, hk⟩ := hs u
    have e : φ (u.1 * g) = φ ((γ * u).1 * g) := by
      rw [Subgroup.coe_mul, mul_assoc, hφ _ (Subgroup.mem_subgroupOf.1 hγ)]
    rw [e]
    exact (hg _ hk).le

end GlobalTheory.CtLeviCont

namespace GlobalTheory.CtLeviCont
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Use `⟨fun i j => ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : σ (W.J i j) = -W.J j i` using `hW.skew j i`. Simplify using `only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, hcs, hσ, h1]`. Expand and normalize the polynomial expressions, which then agree. Establish `hJ : W.J.det ≠ 0`.

Introduce `h0`. Take `⟨v, hv, hJv⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h0`. Set `w : InfinitePlace F` to `Classical.arbitrary _`. Set `τ : E →+* ℂ` to `(B.emb w).1`. Set `M : Matrix (Fin d) (Fin d) ℂ` to `Complex.I • W.J.map τ`.

Set `v' : Fin d → ℂ` to `fun i => τ (v i)`. Establish `hv' : v' ≠ 0` using `fun h => hv (funext fun i => τ.injective (by simpa [v'] using congrFun h i))`. Establish `hMv : M *ᵥ v' = 0`. Use extensionality with `i`. Use `congrArg τ (congrFun hJv i)` as an intermediate fact.

Simplify using `only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.zero_apply, map_zero] at this`. Simplify using `only [M, v', Matrix.smul_mulVec, Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Matrix.smul_apply, mul_assoc, ← Finset.mul_sum, this, mul_zero]`. Establish `hx : star v' ≠ 0` using `fun h => hv' (by simpa using congrArg star h)`. Use `(hW.cartan w).2.2 (star v') hx` as an intermediate fact. Rewrite `this` using `[star_star]`.

Express the relevant statement in the definitionally equal form `0 < (_ ⬝ᵥ M *ᵥ v').re at this`. Rewrite `this` using `[hMv, dotProduct_zero, Complex.zero_re]`. Conclude with `lt_irrefl _ this`. Establish `e : (W.J.map σ).det = (σ : E →+* E) W.J.det` using `by rw [RingHom.map_det]; rfl`. Rewrite using `[Matrix.det_smul, e]`.

Conclude with `mul_ne_zero (pow_ne_zero _ hc) ((map_ne_zero _).2 hJ)`.
-/
theorem isHermND_smul (σ : E →ₐ[F] E) (B : Base F E) {d r s : ℕ} (W : Spc F E d) (hW : W.IsSkew σ B r s)
    (hσ : ∀ x, σ (σ x) = x) (c : E) (hc : c ≠ 0) (hcs : σ c = -c) : IsHermND σ (c • W.J.map σ) := by
  refine ⟨fun i j => ?_, ?_⟩
  · have h1 : σ (W.J i j) = -W.J j i := hW.skew j i
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, hcs, hσ, h1]
    ring
  · have hJ : W.J.det ≠ 0 := by
      intro h0
      obtain ⟨v, hv, hJv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
      let w : InfinitePlace F := Classical.arbitrary _
      let τ : E →+* ℂ := (B.emb w).1
      let M : Matrix (Fin d) (Fin d) ℂ := Complex.I • W.J.map τ
      let v' : Fin d → ℂ := fun i => τ (v i)
      have hv' : v' ≠ 0 := fun h => hv (funext fun i => τ.injective (by simpa [v'] using congrFun h i))
      have hMv : M *ᵥ v' = 0 := by
        ext i
        have := congrArg τ (congrFun hJv i)
        simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.zero_apply, map_zero] at this
        simp only [M, v', Matrix.smul_mulVec, Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul,
          Pi.zero_apply, Matrix.smul_apply, mul_assoc, ← Finset.mul_sum, this, mul_zero]
      have hx : star v' ≠ 0 := fun h => hv' (by simpa using congrArg star h)
      have := (hW.cartan w).2.2 (star v') hx
      rw [star_star] at this
      change 0 < (_ ⬝ᵥ M *ᵥ v').re at this
      rw [hMv, dotProduct_zero, Complex.zero_re] at this
      exact lt_irrefl _ this
    have e : (W.J.map σ).det = (σ : E →+* E) W.J.det := by rw [RingHom.map_det]; rfl
    rw [Matrix.det_smul, e]
    exact mul_ne_zero (pow_ne_zero _ hc) ((map_ne_zero _).2 hJ)

end GlobalTheory.CtLeviCont

namespace GlobalTheory.CtLeviCont
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `linearIndependent_unique_iff.2 fun h => ?_` and prove the remaining obligations. Establish `h0 : H'.x = 0` using `funext fun i => congrFun h i`. Use `hH.xy` as an intermediate fact. Rewrite `this` using `[h0]`.

Simplify using `[form] at this`. Use extensionality with `i j`. Establish `h2 : c * σ (form σ W.J H'.x H'.x) = 0` using `by rw [hH.xx, map_zero, mul_zero]`. Rewrite using `[Matrix.zero_apply, ← h2]`. Simplify using `only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Matrix.zero_apply, Finset.mul_sum, Finset.sum_mul]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Simplify using `only [AlgHom.coe_toRingHom]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isIsoCols_plane (σ : E →ₐ[F] E) (B : Base F E) {d d₁ : ℕ} (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁)
    {i₀ i₁ : ℕ} (hH : H'.IsAdapted σ B W W₁ i₀ i₁) (hσ : ∀ x, σ (σ x) = x) (c : E) :
    IsIsoCols σ (c • W.J.map σ) (Matrix.of fun i (_ : Fin 1) => H'.x i) := by
  refine ⟨?_, ?_⟩
  · refine linearIndependent_unique_iff.2 fun h => ?_
    have h0 : H'.x = 0 := funext fun i => congrFun h i
    have := hH.xy
    rw [h0] at this
    simp [form] at this
  · ext i j
    have h2 : c * σ (form σ W.J H'.x H'.x) = 0 := by rw [hH.xx, map_zero, mul_zero]
    rw [Matrix.zero_apply, ← h2]
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Matrix.zero_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [AlgHom.coe_toRingHom]
    ring

end GlobalTheory.CtLeviCont

namespace GlobalTheory.CtLeviCont
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Use `set C : Matrix (Fin d) (Fin 1) E := Matrix.of fun i (_ : Fin 1) => H'.x i with hCdef`. Set `e` to `toGAd hσ W.J hc`. Establish `hes : Continuous e.symm`. Apply `Continuous.subtype_mk` to reduce the goal to its premises. Conclude with `continuous_subtype_val`.

Establish `hmem` using `GlobalTheory.T.unipotent_mem_iff_unipotent_radical F E σ B d r s W hW hσ c hc hcs d₁ W₁ H' i₀ i₁ hH`. Take `⟨K, hK, hs⟩` from `cocompact_unipRad hcm (isHermND_smul σ B W hW hσ c hc hcs) (isIsoCols_plane σ B W W₁ H' hH hσ c)`. Set `φ : unipRad σ (c • W.J.map σ) C → unip σ W H'` to `fun u => ⟨e.symm u.1, (hmem _).2 (by rw [e.apply_symm_apply]; exact u.2)⟩`. Establish `hφ : Continuous φ` using `(hes.comp continuous_subtype_val).subtype_mk _`. Use `⟨φ '' K, hK.image hφ, fun n => ?_⟩` and prove the remaining obligations.

Take `⟨γ, hγ, hk⟩` from `hs ⟨e n.1, (hmem n.1).1 n.2⟩`. Use `⟨φ γ, ?_, ⟨_, hk, ?_⟩⟩` and prove the remaining obligations. Take `⟨u, -, hu2⟩` from `Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 hγ))`. Conclude with `Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 ⟨u, hu2⟩)`. Apply `Subtype.ext show e.symm (γ.1 * e n.1) = e.symm γ.1 * n.1` to reduce the goal to its premises.

Rewrite using `[map_mul, e.symm_apply_apply]`.
-/
theorem cocompact_unip (σ : E →ₐ[F] E) (B : Base F E) (hcm : IsCMExt F E σ) {d r s : ℕ} (W : Spc F E d)
    (hW : W.IsSkew σ B r s) (hσ : ∀ x, σ (σ x) = x) (c : E) (hc : c ≠ 0) (hcs : σ c = -c) {d₁ : ℕ} (W₁ : Spc F E d₁)
    (H' : Plane E d d₁) {i₀ i₁ : ℕ} (hH : H'.IsAdapted σ B W W₁ i₀ i₁) :
    GlobalTheory.Cusp.Cocompact (ratU σ W.J) (unip σ W H') := by
  set C : Matrix (Fin d) (Fin 1) E := Matrix.of fun i (_ : Fin 1) => H'.x i with hCdef
  let e := toGAd hσ W.J hc
  have hes : Continuous e.symm := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  have hmem := GlobalTheory.T.unipotent_mem_iff_unipotent_radical F E σ B d r s W hW hσ c hc hcs d₁ W₁ H' i₀ i₁ hH
  obtain ⟨K, hK, hs⟩ := cocompact_unipRad hcm (isHermND_smul σ B W hW hσ c hc hcs)
    (isIsoCols_plane σ B W W₁ H' hH hσ c)
  let φ : unipRad σ (c • W.J.map σ) C → unip σ W H' := fun u =>
    ⟨e.symm u.1, (hmem _).2 (by rw [e.apply_symm_apply]; exact u.2)⟩
  have hφ : Continuous φ := (hes.comp continuous_subtype_val).subtype_mk _
  refine ⟨φ '' K, hK.image hφ, fun n => ?_⟩
  obtain ⟨γ, hγ, hk⟩ := hs ⟨e n.1, (hmem n.1).1 n.2⟩
  refine ⟨φ γ, ?_, ⟨_, hk, ?_⟩⟩
  · obtain ⟨u, -, hu2⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 hγ))
    exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 ⟨u, hu2⟩)
  · apply Subtype.ext
    show e.symm (γ.1 * e n.1) = e.symm γ.1 * n.1
    rw [map_mul, e.symm_apply_apply]

end GlobalTheory.CtLeviCont

namespace GlobalTheory.CtLeviCont
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
open GlobalTheory.LeviPlane

/- English proof (translation)
The claim follows from `IsModuleTopology.continuous_of_linearMap (cA (F := F) (E := E) σ).toLinearMap`.
-/
theorem continuous_cA (σ : E →ₐ[F] E) : Continuous (cA (F := F) (E := E) σ) :=
  IsModuleTopology.continuous_of_linearMap (cA (F := F) (E := E) σ).toLinearMap

/- English proof (translation)
Use `set c : AE F E →+* AE F E := (cA σ).toRingHom with hcdef`. Establish `hσ` using `sigma_invol hcm`. Establish `hc : ∀ x, c (c x) = x` using `fun x => cA_invol hσ x`. Establish `hJ : ∀ i j, c (incM F W.J j i) = -incM F W.J i j`. Introduce `i j`.

Simplify using `only [hcdef, incM, Matrix.map_apply, cAr_inclR, hW.skew, map_neg]`. Establish `hxx : fm c (incM F W.J) (incV F H'.x) (incV F H'.x) = 0` using `by rw [fm_inc, hH.xx, map_zero]`. Establish `hyy : fm c (incM F W.J) (incV F H'.y) (incV F H'.y) = 0` using `by rw [fm_inc, hH.yy, map_zero]`. Establish `hxy : fm c (incM F W.J) (incV F H'.x) (incV F H'.y) = 1` using `by rw [fm_inc, hH.xy, map_one]`. Establish `hι : ∀ j, fm c (incM F W.J) (fun i => incM F H'.ι i j) (incV F H'.x) = 0 ∧ fm c (incM F W.J) (fun i => incM F H'.ι i j) (incV F H'.y) = 0`.

Introduce `j`. Establish `hcol : (fun i => incM F H'.ι i j) = incV F (H'.ι *ᵥ Pi.single j 1)`. Use extensionality with `i`. Simplify using `[incV, incM, Matrix.mulVec_single_one]`. Rewrite using `[hcol, fm_inc, fm_inc, (hH.orth _).1, (hH.orth _).2, map_zero]`.

Conclude with `⟨rfl, rfl⟩`. Set `L : AE F E → AE F E → Matrix (Fin d) (Fin d) (AE F E)` to `fun s r => lev c (incM F W.J) (incV F H'.x) (incV F H'.y) s r`. Establish `hmul : ∀ s r s' r', L s r * L s' r' = L (s * s') (r * r')` using `fun s r s' r' => lev_mul hc hJ hxx hyy hxy s r s' r'`. Establish `h1 : L 1 1 = 1` using `lev_one hc hJ hxx hyy hxy`. Set `g : (AE F E)ˣ → GL (Fin d) (AE F E)` to `fun t => ⟨L (t : AE F E) (cA σ ((t⁻¹ : (AE F E)ˣ) : AE F E)), L ((t⁻¹ : (AE F E)ˣ) : AE F E) (cA σ (t : AE F E)), by rw [hmul, ← map_mul, Units.mul_inv, Units.inv_mul, map_one, h1], by rw [hmul, ← map_mul, Units.inv_mul, Units.mul_inv, map_one, h1]⟩`.

Establish `hg : ∀ t, g t ∈ GlobalTheory.WeilM.UG (cA σ) (incM F W.J)`. Introduce `t`. Use `show (L _ _)ᵀ * incM F W.J * (L _ _).map (cA σ) = incM F W.J`. Conclude with `lev_unitary hc hJ hxx hyy hxy (t : AE F E) (cA σ ((t⁻¹ : (AE F E)ˣ) : AE F E)) (by show (t : AE F E) * cA σ (cA σ _) = 1; rw [cA_invol hσ, Units.mul_inv])`. Set `m : (AE F E)ˣ → UA σ W.J` to `fun t => ⟨g t, hg t⟩`.

Establish `hm : ∀ t, IsLevi (W₁` using `W₁) H' t 1 (m t) := by`. Introduce `t`. Use `⟨lev_X hxx hxy _ _, lev_Y hc hJ hxx hyy hxy _ _, ?_⟩` and prove the remaining obligations. Establish `: mat (1 : UA σ W₁.J) = 1` using `rfl`. Rewrite using `[this, Matrix.mul_one]`.

Conclude with `lev_mul_ι _ hι _ _`. Establish `e : leviElt σ W W₁ H' = m` using `funext fun t => GlobalTheory.T.levi_element_unique F E σ B d r s W hW d₁ W₁ H' i₀ i₁ hH t _ _ (isLevi_leviElt ⟨_, hm t⟩) (hm t)`. Rewrite using `[e]`. Establish `hLc : Continuous fun p : AE F E × AE F E => L p.1 p.2`. Simplify using `only [L, lev]`.

Use `fun_prop`. Apply `Continuous.subtype_mk` to reduce the goal to its premises. Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `(hLc.comp (Units.continuous_val.prodMk ((continuous_cA σ).comp Units.continuous_coe_inv))).congr fun t => rfl`. Establish `e2 : ∀ t, (((g t)⁻¹ : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) = L ((t⁻¹ : (AE F E)ˣ) : AE F E) (cA σ (t : AE F E))` using `fun t => rfl`.

Conclude with `(hLc.comp (Units.continuous_coe_inv.prodMk ((continuous_cA σ).comp Units.continuous_val))).congr fun t => (e2 t).symm`.
-/
theorem continuous_leviElt (σ : E →ₐ[F] E) (B : Base F E) (hcm : IsCMExt F E σ) {d r s : ℕ} (W : Spc F E d)
    (hW : W.IsSkew σ B r s) {d₁ : ℕ} (W₁ : Spc F E d₁) (H' : Plane E d d₁) {i₀ i₁ : ℕ}
    (hH : H'.IsAdapted σ B W W₁ i₀ i₁) : Continuous (leviElt σ W W₁ H') := by
  set c : AE F E →+* AE F E := (cA σ).toRingHom with hcdef
  have hσ := sigma_invol hcm
  have hc : ∀ x, c (c x) = x := fun x => cA_invol hσ x
  have hJ : ∀ i j, c (incM F W.J j i) = -incM F W.J i j := by
    intro i j
    simp only [hcdef, incM, Matrix.map_apply, cAr_inclR, hW.skew, map_neg]
  have hxx : fm c (incM F W.J) (incV F H'.x) (incV F H'.x) = 0 := by rw [fm_inc, hH.xx, map_zero]
  have hyy : fm c (incM F W.J) (incV F H'.y) (incV F H'.y) = 0 := by rw [fm_inc, hH.yy, map_zero]
  have hxy : fm c (incM F W.J) (incV F H'.x) (incV F H'.y) = 1 := by rw [fm_inc, hH.xy, map_one]
  have hι : ∀ j, fm c (incM F W.J) (fun i => incM F H'.ι i j) (incV F H'.x) = 0 ∧
      fm c (incM F W.J) (fun i => incM F H'.ι i j) (incV F H'.y) = 0 := by
    intro j
    have hcol : (fun i => incM F H'.ι i j) = incV F (H'.ι *ᵥ Pi.single j 1) := by
      ext i; simp [incV, incM, Matrix.mulVec_single_one]
    rw [hcol, fm_inc, fm_inc, (hH.orth _).1, (hH.orth _).2, map_zero]; exact ⟨rfl, rfl⟩
  let L : AE F E → AE F E → Matrix (Fin d) (Fin d) (AE F E) :=
    fun s r => lev c (incM F W.J) (incV F H'.x) (incV F H'.y) s r
  have hmul : ∀ s r s' r', L s r * L s' r' = L (s * s') (r * r') := fun s r s' r' =>
    lev_mul hc hJ hxx hyy hxy s r s' r'
  have h1 : L 1 1 = 1 := lev_one hc hJ hxx hyy hxy
  let g : (AE F E)ˣ → GL (Fin d) (AE F E) := fun t =>
    ⟨L (t : AE F E) (cA σ ((t⁻¹ : (AE F E)ˣ) : AE F E)), L ((t⁻¹ : (AE F E)ˣ) : AE F E) (cA σ (t : AE F E)),
      by rw [hmul, ← map_mul, Units.mul_inv, Units.inv_mul, map_one, h1],
      by rw [hmul, ← map_mul, Units.inv_mul, Units.mul_inv, map_one, h1]⟩
  have hg : ∀ t, g t ∈ GlobalTheory.WeilM.UG (cA σ) (incM F W.J) := by
    intro t
    show (L _ _)ᵀ * incM F W.J * (L _ _).map (cA σ) = incM F W.J
    exact lev_unitary hc hJ hxx hyy hxy (t : AE F E) (cA σ ((t⁻¹ : (AE F E)ˣ) : AE F E))
      (by show (t : AE F E) * cA σ (cA σ _) = 1; rw [cA_invol hσ, Units.mul_inv])
  let m : (AE F E)ˣ → UA σ W.J := fun t => ⟨g t, hg t⟩
  have hm : ∀ t, IsLevi (W₁ := W₁) H' t 1 (m t) := by
    intro t
    refine ⟨lev_X hxx hxy _ _, lev_Y hc hJ hxx hyy hxy _ _, ?_⟩
    have : mat (1 : UA σ W₁.J) = 1 := rfl
    rw [this, Matrix.mul_one]
    exact lev_mul_ι _ hι _ _
  have e : leviElt σ W W₁ H' = m := funext fun t =>
    GlobalTheory.T.levi_element_unique F E σ B d r s W hW d₁ W₁ H' i₀ i₁ hH t _ _ (isLevi_leviElt ⟨_, hm t⟩) (hm t)
  rw [e]
  have hLc : Continuous fun p : AE F E × AE F E => L p.1 p.2 := by
    simp only [L, lev]
    fun_prop
  apply Continuous.subtype_mk
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (hLc.comp (Units.continuous_val.prodMk ((continuous_cA σ).comp Units.continuous_coe_inv))).congr fun t => rfl
  · have e2 : ∀ t, (((g t)⁻¹ : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) =
        L ((t⁻¹ : (AE F E)ˣ) : AE F E) (cA σ (t : AE F E)) := fun t => rfl
    exact (hLc.comp (Units.continuous_coe_inv.prodMk ((continuous_cA σ).comp Units.continuous_val))).congr fun t => (e2 t).symm

end GlobalTheory.CtLeviCont

namespace GlobalTheory.CtLeviCont
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Introduce `_ F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH hσ c hc hcs f hf μ 𝓕 _ _ h1 h`. Take `⟨K, -, hA⟩` from `hf`. Set `e` to `toGAd hσ G.W.J hc`. Establish `he : Continuous e`. Apply `Continuous.subtype_mk` to reduce the goal to its premises.

Conclude with `continuous_subtype_val`. Establish `hes : Continuous e.symm`. Apply `Continuous.subtype_mk` to reduce the goal to its premises. Conclude with `continuous_subtype_val`. Set `t : UA σ G.W.J ≃ₜ GAd σ (c • G.W.J.map σ)` to `⟨e.toEquiv, he, hes⟩`.

Use `haveI : SecondCountableTopology (GAd σ (c • G.W.J.map σ)) := (GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary F E σ (a + a') (c • G.W.J.map σ)).2.1`. Use `haveI hsc : SecondCountableTopology (UA σ G.W.J) := t.secondCountableTopology`. Use `haveI : FirstCountableTopology (UA σ G.W.J) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ hsc`. Establish `hfc : Continuous f`. Establish `: f = (fun x => f (e.symm x)) ∘ e` using `funext fun x => by simp`.

Rewrite using `[this]`. Conclude with `hA.mod.cont.comp he`. Establish `hfl : ∀ γ ∈ ratU σ G.W.J, ∀ g, f (γ * g) = f g`. Introduce `γ hγ g`. Take `⟨m, hm⟩` from `Subgroup.mem_subgroupOf.1 hγ`.

Establish `hP : e γ ∈ ratPts σ (c • G.W.J.map σ)`. Use `Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨m, ?_, hm⟩)` and prove the remaining obligations. Conclude with `unitary_of_map_inclR σ (a + a') _ m _ (by rw [hm]; rfl) (e γ).2`. Use `hA.mod.left (e γ) hP (e g)` as an intermediate fact. Rewrite `this` using `[← map_mul, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]`. Then use the resulting hypothesis.

Establish `hcc` using `cocompact_unip σ B hT.base.cm G.W hT.geo.hW hσ c hc hcs W₁ H' hH`. Establish `hI` using `continuous_setIntegral_of_cocompact hcc hfl hfc μ 𝓕 (by rw [h1]; exact ENNReal.one_ne_top)`. Establish `hL` using `continuous_leviElt σ B hT.base.cm G.W hT.geo.hW W₁ H' hH`. Conclude with `hI.comp (hL.mul continuous_const)`.
-/
theorem ctLevi_continuous : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ (hσ : ∀ x, σ (σ x) = x) (c : E) (hc : c ≠ 0), σ c = -c → ∀ f : UA σ G.W.J → ℂ, (∃ K, IsMaxCpt σ (c • G.W.J.map σ) K ∧ IsAut σ (c • G.W.J.map σ) K (fun x => f ((toGAd hσ G.W.J hc).symm x))) → ∀ (μ : Measure (unip σ G.W H')) (𝓕 : Set (unip σ G.W H')), μ.IsHaarMeasure → IsFundamentalDomain ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) 𝓕 μ → μ 𝓕 = 1 → ∀ h : UA σ G.W.J, Continuous (ctLevi σ G.W W₁ H' μ 𝓕 f h) := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH hσ c hc hcs f hf μ 𝓕 _ _ h1 h
  obtain ⟨K, -, hA⟩ := hf
  let e := toGAd hσ G.W.J hc
  have he : Continuous e := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  have hes : Continuous e.symm := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  let t : UA σ G.W.J ≃ₜ GAd σ (c • G.W.J.map σ) := ⟨e.toEquiv, he, hes⟩
  haveI : SecondCountableTopology (GAd σ (c • G.W.J.map σ)) :=
    (GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary F E σ (a + a') (c • G.W.J.map σ)).2.1
  haveI hsc : SecondCountableTopology (UA σ G.W.J) := t.secondCountableTopology
  haveI : FirstCountableTopology (UA σ G.W.J) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ hsc
  have hfc : Continuous f := by
    have : f = (fun x => f (e.symm x)) ∘ e := funext fun x => by simp
    rw [this]
    exact hA.mod.cont.comp he
  have hfl : ∀ γ ∈ ratU σ G.W.J, ∀ g, f (γ * g) = f g := by
    intro γ hγ g
    obtain ⟨m, hm⟩ := Subgroup.mem_subgroupOf.1 hγ
    have hP : e γ ∈ ratPts σ (c • G.W.J.map σ) := by
      refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨m, ?_, hm⟩)
      exact unitary_of_map_inclR σ (a + a') _ m _ (by rw [hm]; rfl) (e γ).2
    have := hA.mod.left (e γ) hP (e g)
    rwa [← map_mul, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply] at this
  have hcc := cocompact_unip σ B hT.base.cm G.W hT.geo.hW hσ c hc hcs W₁ H' hH
  have hI := continuous_setIntegral_of_cocompact hcc hfl hfc μ 𝓕 (by rw [h1]; exact ENNReal.one_ne_top)
  have hL := continuous_leviElt σ B hT.base.cm G.W hT.geo.hW W₁ H' hH
  exact hI.comp (hL.mul continuous_const)

end GlobalTheory.CtLeviCont
