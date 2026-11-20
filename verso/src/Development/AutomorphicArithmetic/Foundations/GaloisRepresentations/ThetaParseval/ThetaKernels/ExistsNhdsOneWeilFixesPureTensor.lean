import Development.AutomorphicArithmetic.AdelicQuotients.WeilRepresentationSmoothVectors
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaBasicK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkEstCoefBd
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkEstCoefEq

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
open UpperTheory.TP
section Left
open PositivityTheory.ThKEst PositivityTheory.ThKEst.levelStructure PositivityTheory.ThKEst.LatticeQuotientMeasure PositivityTheory.ThKF0.Grow PositivityTheory.ThKF0.Grow.Fi
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
/- English proof (translation)
Use `ring_AE F E` as an intermediate fact. Establish `: IsModuleTopology (AF F) (Ten F E n d)` using `inferInstanceAs (IsModuleTopology (AF F) (Fin n → Fin d → AE F E))`. Establish `he : Continuous M.co.e` using `IsModuleTopology.continuous_of_linearMap M.co.e.toLinearMap`. Establish `hV` using `schr_near hψ hg (hC.image he)`. Establish `hm : Continuous fun p : UA σ X.J × Ten F E n d => M.co.e ((mat p.1 - 1) * p.2)` using `he.comp ((((Units.continuous_val.comp continuous_subtype_val).comp continuous_fst).sub continuous_const).matrix_mul continuous_snd)`.

Establish `h1` using `hC.eventually_forall_of_forall_eventually (x₀ := (1 : UA σ X.J)) (P := fun u c => M.co.e ((mat u - 1) * c) ∈ _) fun c _ => hm.continuousAt.preimage_mem_nhds (by`. Rewrite using `[show mat (1 : UA σ X.J) = 1 from rfl, sub_self, Matrix.zero_mul, map_zero])` and apply the resulting hypothesis. Use `filter_upwards [h1] with u h1 hu z hz f`. Take `⟨c, hc, hz⟩` from `hz`. Rewrite `hz` using `[at_iff, smul_sub, sub_eq_zero]`.

Establish `hu' : e0 F • (mat u - 1) = mat u - 1` using `hu`. Establish `e : mat u * z = z + (mat u - 1) * c`. Establish `e1 : (mat u - 1) * c = (mat u - 1) * z`. Rewrite using `[← hu', Matrix.smul_mul, ← Matrix.mul_smul, ← hz, Matrix.mul_smul, Matrix.smul_mul]`. Rewrite using `[e1, Matrix.sub_mul, Matrix.one_mul, add_sub_cancel]`.

Rewrite using `[e, map_add]`. Conclude with `h1 c hc (by rw [← map_smul, ← Matrix.smul_mul, hu']) _ ⟨c, hc, rfl⟩ _ (by rw [← map_smul, ← map_smul, hz]) f`.
-/
private theorem schr_left_pk {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    {g : (Fin n × Fin d → Af F) → ℂ} (hg : g ∈ SB _) {C : Set (Ten F E n d)} (hC : IsCompact C) :
    ∀ᶠ u in 𝓝 (1 : UA σ X.J), levelStructure.IsFin u → ∀ z : Ten F E n d, (∃ c ∈ C, At (evI F) (z - c)) → ∀ f,
      schr ψ (M.co.e (mat u * z)) (pureA F f g) = schr ψ (M.co.e z) (pureA F f g) := by
  have := ring_AE F E
  have : IsModuleTopology (AF F) (Ten F E n d) := inferInstanceAs (IsModuleTopology (AF F) (Fin n → Fin d → AE F E))
  have he : Continuous M.co.e := IsModuleTopology.continuous_of_linearMap M.co.e.toLinearMap
  have hV := schr_near hψ hg (hC.image he)
  have hm : Continuous fun p : UA σ X.J × Ten F E n d => M.co.e ((mat p.1 - 1) * p.2) :=
    he.comp ((((Units.continuous_val.comp continuous_subtype_val).comp continuous_fst).sub continuous_const).matrix_mul
      continuous_snd)
  have h1 := hC.eventually_forall_of_forall_eventually (x₀ := (1 : UA σ X.J))
    (P := fun u c => M.co.e ((mat u - 1) * c) ∈ _) fun c _ => hm.continuousAt.preimage_mem_nhds (by
      rwa [show mat (1 : UA σ X.J) = 1 from rfl, sub_self, Matrix.zero_mul, map_zero])
  filter_upwards [h1] with u h1 hu z hz f
  obtain ⟨c, hc, hz⟩ := hz
  rw [at_iff, smul_sub, sub_eq_zero] at hz
  have hu' : e0 F • (mat u - 1) = mat u - 1 := hu
  have e : mat u * z = z + (mat u - 1) * c := by
    have e1 : (mat u - 1) * c = (mat u - 1) * z := by
      rw [← hu', Matrix.smul_mul, ← Matrix.mul_smul, ← hz, Matrix.mul_smul, Matrix.smul_mul]
    rw [e1, Matrix.sub_mul, Matrix.one_mul, add_sub_cancel]
  rw [e, map_add]
  exact h1 c hc (by rw [← map_smul, ← Matrix.smul_mul, hu']) _ ⟨c, hc, rfl⟩ _ (by rw [← map_smul, ← map_smul, hz]) f
end Left
/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp φ hφ`. Distinguish the cases in `h0 : ∀ f : SInf F (Fin n × Fin d), pureA F f φ = 0`. Conclude with `⟨Set.univ, univ_mem, fun u _ _ f => by rw [h0, map_zero]⟩`. Use `push Not at h0`. Take `⟨f₀, h0⟩` from `h0`.

Take `⟨y, hy⟩` from `Function.ne_iff.1 h0`. Establish `hy : pureA F f₀ φ y ≠ 0` using `hy`. Establish `hs` using `IsUWeilPair.isUSplitting hp.weil`. Establish `mem : ∀ f : SInf F (Fin n × Fin d), pureA F f φ ∈ schA F (Fin n × Fin d)` using `fun f => Submodule.subset_span ⟨f, φ, hφ, rfl⟩`. Take `⟨μ, hμ, -⟩` from `PositivityTheory.ThKEst.ParityOfCoefficients.exists_haar (F := F) (κ := Fin n × Fin d)`.

Take `⟨p, C, -, hCc, hb⟩` from `_root_.PositivityTheory.ThKEst.coefBd_of_k PositivityTheory.ThKEst.coefReal_of F E σ B n d X W M χX χW om r s r' s' hp μ hμ φ hφ φ hφ 0`. Establish `h1` using `schr_left_pk M hp.base.std hφ hCc`. Use `PositivityTheory.ThKEst.LatticeQuotientMeasure.ring_AE F E` as an intermediate fact. Establish `hi : Continuous fun u : UA σ X.J => u⁻¹` using `((continuous_inv (G := GL (Fin n) (AE F E))).comp continuous_subtype_val).subtype_mk fun u => (u⁻¹).2`. Establish `h2` using `(hi.tendsto' 1 1 inv_one).eventually h1`.

Establish `hc : Continuous fun u : UA σ X.J => ‖om (u, 1) (pureA F f₀ φ) y / pureA F f₀ φ y - 1‖` using `((((hs.cont _ (PositivityTheory.ThKEst.levelStructure.ev_adm y) _ (mem f₀)).comp (continuous_id.prodMk continuous_const)).div_const _).sub continuous_const).norm`. Establish `h3` using `PositivityTheory.ThKEst.levelStructure.pow_near _ ((isOpen_lt hc (continuous_const (y := (1 / 2 : ℝ)))).mem_nhds (by`. Express the relevant statement in the definitionally equal form `‖om 1 (pureA F f₀ φ) y / pureA F f₀ φ y - 1‖ < 1 / 2`. Rewrite using `[map_one, Module.End.one_apply, div_self hy]`. Use the proof step `norm_num))`.

Use `⟨_, h1.and (h2.and h3), fun u ⟨h1, h2, h3⟩ hu => ?_⟩` and prove the remaining obligations. Establish `hu` using `PositivityTheory.ThKEst.levelStructure.isFin_of hp.base.cm B.emb hu`. Establish `key : ∀ (f : SInf F (Fin n × Fin d)) x, om (u, 1) (pureA F f φ) x * (starRingEnd ℂ) (om (u, 1) (pureA F f₀ φ) y) = pureA F f φ x * (starRingEnd ℂ) (pureA F f₀ φ y)`. Introduce `f x`. Use `PositivityTheory.ThKEst.fourierInj_of F _ B.ψ hp.base.std μ hμ _ (hs.pres _ _ (mem f)) _ (hs.pres _ _ (mem f₀)) _ (mem f) _ (mem f₀) ?_ x y` and prove the remaining obligations.

Use function extensionality and compare the values at `w`. Take `⟨z, rfl⟩` from `M.co.e.surjective w`. Rewrite using `[_root_.PositivityTheory.ThKEst.coefEq_of_k F E σ B n d X W M χX χW om r s r' s' hp μ hμ _ (mem f) _ (mem f₀), PositivityTheory.ThKEst.ParityOfCoefficients.mat_one_inv, Matrix.transpose_one, Matrix.mul_one]`. Distinguish the cases in `a : ∃ c ∈ C, At (evI F) (z - c)`. Unfold `PositivityTheory.ThKEst.coef`.

Rewrite using `[h2 hu.inv z a]`. Distinguish the cases in `a' : ∃ c ∈ C, At (evI F) (mat u⁻¹ * z - c)`. Unfold `PositivityTheory.ThKEst.coef`. Rewrite using `[← h1 hu _ a', ← Matrix.mul_assoc, show mat u * mat u⁻¹ = 1 from Units.mul_inv u.1, Matrix.one_mul]`. Establish `b` using `hb f f₀ z`.

Establish `b'` using `hb f f₀ (mat u⁻¹ * z)`. Rewrite `b` using `[PositivityTheory.ThKEst.maj, if_neg a, mul_zero, norm_le_zero_iff]`. Rewrite `b'` using `[PositivityTheory.ThKEst.maj, if_neg a', mul_zero, norm_le_zero_iff]`. Rewrite using `[b, b']`. Establish `h4 : (starRingEnd ℂ) (om (u, 1) (pureA F f₀ φ) y) ≠ 0` using `fun h => by`.

Use `key f₀ y` as an intermediate fact. Rewrite `this` using `[h, mul_zero, eq_comm, mul_eq_zero, map_eq_zero, or_self]`. Conclude with `hy this`. Take `⟨c, hc⟩ : ∃ c : ℂ, ∀ f : SInf F (Fin n × Fin d), om (u, 1) (pureA F f φ) = c • pureA F f φ` from `⟨(starRingEnd ℂ) (pureA F f₀ φ y) / (starRingEnd ℂ) (om (u, 1) (pureA F f₀ φ) y), fun f => funext fun x => by`. Rewrite using `[Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff h4, key, mul_comm]⟩`.

Establish `h5 : ∀ k : ℕ, om (u ^ k, 1) (pureA F f₀ φ) = c ^ k • pureA F f₀ φ` using `fun k => by`. Proceed by induction on `k with`. Consider the case `zero => rw [pow_zero, pow_zero, one_smul]`. Conclude with `congrArg (· (pureA F f₀ φ)) (map_one om)`. Consider the case `succ k ih`.

Rewrite using `[pow_succ, show ((u ^ k * u, 1) : UA σ X.J × UA σ W.J) = (u ^ k, 1) * (u, 1) from by simp, map_mul, Module.End.mul_apply, hc, map_smul, ih, smul_smul, pow_succ']`. Establish `h6 : c = 1` using `PositivityTheory.ThKH.Locrep.eq_one_of_pow_near fun k => by`. Use `h3 hu k` as an intermediate fact. Rewrite `this` using `[Set.mem_ofPred_eq, h5, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hy, mul_one]`. Then use the resulting hypothesis. Introduce `f`.

Rewrite using `[hc, h6, one_smul]`.
-/
theorem UpperTheory.exists_nhds_one_weil_fixes_pure_tensor :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), ∀ r s r' s', _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s' → ∀ φ ∈ SB (Fin n × Fin d → Af F), ∃ U ∈ 𝓝 (1 : UA σ X.J), ∀ u ∈ U, (∀ w, (mat u).map (piInf (B.emb w)) = 1) → ∀ f : SInf F (Fin n × Fin d), om (u, 1) (pureA F f φ) = pureA F f φ := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp φ hφ
  by_cases h0 : ∀ f : SInf F (Fin n × Fin d), pureA F f φ = 0
  · exact ⟨Set.univ, univ_mem, fun u _ _ f => by rw [h0, map_zero]⟩
  push Not at h0
  obtain ⟨f₀, h0⟩ := h0
  obtain ⟨y, hy⟩ := Function.ne_iff.1 h0
  have hy : pureA F f₀ φ y ≠ 0 := hy
  have hs := IsUWeilPair.isUSplitting hp.weil
  have mem : ∀ f : SInf F (Fin n × Fin d), pureA F f φ ∈ schA F (Fin n × Fin d) := fun f =>
    Submodule.subset_span ⟨f, φ, hφ, rfl⟩
  obtain ⟨μ, hμ, -⟩ := PositivityTheory.ThKEst.ParityOfCoefficients.exists_haar (F := F) (κ := Fin n × Fin d)
  obtain ⟨p, C, -, hCc, hb⟩ := _root_.PositivityTheory.ThKEst.coefBd_of_k PositivityTheory.ThKEst.coefReal_of F E σ B n d X W M χX χW om r s r' s' hp μ hμ φ hφ φ hφ 0
  have h1 := schr_left_pk M hp.base.std hφ hCc
  have := PositivityTheory.ThKEst.LatticeQuotientMeasure.ring_AE F E
  have hi : Continuous fun u : UA σ X.J => u⁻¹ :=
    ((continuous_inv (G := GL (Fin n) (AE F E))).comp continuous_subtype_val).subtype_mk fun u => (u⁻¹).2
  have h2 := (hi.tendsto' 1 1 inv_one).eventually h1
  have hc : Continuous fun u : UA σ X.J => ‖om (u, 1) (pureA F f₀ φ) y / pureA F f₀ φ y - 1‖ :=
    ((((hs.cont _ (PositivityTheory.ThKEst.levelStructure.ev_adm y) _ (mem f₀)).comp (continuous_id.prodMk continuous_const)).div_const _).sub
      continuous_const).norm
  have h3 := PositivityTheory.ThKEst.levelStructure.pow_near _ ((isOpen_lt hc (continuous_const (y := (1 / 2 : ℝ)))).mem_nhds (by
    change ‖om 1 (pureA F f₀ φ) y / pureA F f₀ φ y - 1‖ < 1 / 2
    rw [map_one, Module.End.one_apply, div_self hy]
    norm_num))
  refine ⟨_, h1.and (h2.and h3), fun u ⟨h1, h2, h3⟩ hu => ?_⟩
  have hu := PositivityTheory.ThKEst.levelStructure.isFin_of hp.base.cm B.emb hu
  have key : ∀ (f : SInf F (Fin n × Fin d)) x, om (u, 1) (pureA F f φ) x * (starRingEnd ℂ) (om (u, 1) (pureA F f₀ φ) y) =
      pureA F f φ x * (starRingEnd ℂ) (pureA F f₀ φ y) := by
    intro f x
    refine PositivityTheory.ThKEst.fourierInj_of F _ B.ψ hp.base.std μ hμ _ (hs.pres _ _ (mem f)) _ (hs.pres _ _ (mem f₀)) _ (mem f) _ (mem f₀) ?_ x y
    funext w
    obtain ⟨z, rfl⟩ := M.co.e.surjective w
    rw [_root_.PositivityTheory.ThKEst.coefEq_of_k F E σ B n d X W M χX χW om r s r' s' hp μ hμ _ (mem f) _ (mem f₀), PositivityTheory.ThKEst.ParityOfCoefficients.mat_one_inv,
      Matrix.transpose_one, Matrix.mul_one]
    by_cases a : ∃ c ∈ C, At (evI F) (z - c)
    · unfold PositivityTheory.ThKEst.coef
      rw [h2 hu.inv z a]
    by_cases a' : ∃ c ∈ C, At (evI F) (mat u⁻¹ * z - c)
    · unfold PositivityTheory.ThKEst.coef
      rw [← h1 hu _ a', ← Matrix.mul_assoc, show mat u * mat u⁻¹ = 1 from Units.mul_inv u.1, Matrix.one_mul]
    have b := hb f f₀ z
    have b' := hb f f₀ (mat u⁻¹ * z)
    rw [PositivityTheory.ThKEst.maj, if_neg a, mul_zero, norm_le_zero_iff] at b
    rw [PositivityTheory.ThKEst.maj, if_neg a', mul_zero, norm_le_zero_iff] at b'
    rw [b, b']
  have h4 : (starRingEnd ℂ) (om (u, 1) (pureA F f₀ φ) y) ≠ 0 := fun h => by
    have := key f₀ y
    rw [h, mul_zero, eq_comm, mul_eq_zero, map_eq_zero, or_self] at this
    exact hy this
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ f : SInf F (Fin n × Fin d), om (u, 1) (pureA F f φ) = c • pureA F f φ :=
    ⟨(starRingEnd ℂ) (pureA F f₀ φ y) / (starRingEnd ℂ) (om (u, 1) (pureA F f₀ φ) y), fun f => funext fun x => by
      rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff h4, key, mul_comm]⟩
  have h5 : ∀ k : ℕ, om (u ^ k, 1) (pureA F f₀ φ) = c ^ k • pureA F f₀ φ := fun k => by
    induction k with
    | zero => rw [pow_zero, pow_zero, one_smul]; exact congrArg (· (pureA F f₀ φ)) (map_one om)
    | succ k ih =>
      rw [pow_succ, show ((u ^ k * u, 1) : UA σ X.J × UA σ W.J) = (u ^ k, 1) * (u, 1) from by simp, map_mul,
        Module.End.mul_apply, hc, map_smul, ih, smul_smul, pow_succ']
  have h6 : c = 1 := PositivityTheory.ThKH.Locrep.eq_one_of_pow_near fun k => by
    have := h3 hu k
    rwa [Set.mem_ofPred_eq, h5, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hy, mul_one] at this
  intro f
  rw [hc, h6, one_smul]
end
