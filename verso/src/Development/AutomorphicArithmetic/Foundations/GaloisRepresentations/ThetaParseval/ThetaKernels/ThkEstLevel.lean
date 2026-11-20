import Development.WeilBound.ThetaLifts.FrameEstimates.SchrAddPt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkEstStmt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LevelKAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaBasicK

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace PositivityTheory.ThKEst
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
namespace levelStructure
open LatticeQuotientMeasure PositivityTheory.ThKF0.Grow PositivityTheory.ThKF0.Grow.Fi
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
end levelStructure
open levelStructure in
/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp φ hφ`. Distinguish the cases in `h0 : ∀ f : SInf F (Fin n × Fin d), pureA F f φ = 0`. Conclude with `⟨Set.univ, univ_mem, fun u _ _ f => by rw [h0, map_zero]⟩`. Use `push Not at h0`. Take `⟨f₀, h0⟩` from `h0`.

Take `⟨y, hy⟩` from `Function.ne_iff.1 h0`. Establish `hy : pureA F f₀ φ y ≠ 0` using `hy`. Establish `hs` using `IsUWeilPair.isUSplitting hp.weil`. Establish `mem : ∀ f : SInf F (Fin n × Fin d), pureA F f φ ∈ schA F (Fin n × Fin d)` using `fun f => Submodule.subset_span ⟨f, φ, hφ, rfl⟩`. Take `⟨μ, hμ, -⟩` from `ParityOfCoefficients.exists_haar (F := F) (κ := Fin n × Fin d)`.

Take `⟨p, C, -, hCc, hb⟩` from `hB F E σ B n d X W M χX χW om r s r' s' hp μ hμ φ hφ φ hφ 0`. Establish `h1` using `coef_near M hp.base.std hφ hCc`. Use `LatticeQuotientMeasure.ring_AE F E` as an intermediate fact. Establish `hi : Continuous fun u : UA σ W.J => u⁻¹` using `((continuous_inv (G := GL (Fin d) (AE F E))).comp continuous_subtype_val).subtype_mk fun u => (u⁻¹).2`. Establish `h2` using `(hi.tendsto' 1 1 inv_one).eventually h1`.

Establish `hc : Continuous fun u : UA σ W.J => ‖om (1, u) (pureA F f₀ φ) y / pureA F f₀ φ y - 1‖` using `((((hs.cont _ (ev_adm y) _ (mem f₀)).comp (continuous_const.prodMk continuous_id)).div_const _).sub continuous_const).norm`. Establish `h3` using `pow_near _ ((isOpen_lt hc (continuous_const (y := (1 / 2 : ℝ)))).mem_nhds (by`. Express the relevant statement in the definitionally equal form `‖om 1 (pureA F f₀ φ) y / pureA F f₀ φ y - 1‖ < 1 / 2`. Rewrite using `[map_one, Module.End.one_apply, div_self hy]`. Use the proof step `norm_num))`.

Use `⟨_, h1.and (h2.and h3), fun u ⟨h1, h2, h3⟩ hu => ?_⟩` and prove the remaining obligations. Establish `hu` using `isFin_of hp.base.cm B.emb hu`. Establish `key : ∀ (f : SInf F (Fin n × Fin d)) x, om (1, u) (pureA F f φ) x * (starRingEnd ℂ) (om (1, u) (pureA F f₀ φ) y) = pureA F f φ x * (starRingEnd ℂ) (pureA F f₀ φ y)`. Introduce `f x`. Use `hF F _ B.ψ hp.base.std μ hμ _ (hs.pres _ _ (mem f)) _ (hs.pres _ _ (mem f₀)) _ (mem f) _ (mem f₀) ?_ x y` and prove the remaining obligations.

Use function extensionality and compare the values at `w`. Take `⟨z, rfl⟩` from `M.co.e.surjective w`. Rewrite using `[hC F E σ B n d X W M χX χW om r s r' s' hp μ hμ _ (mem f) _ (mem f₀), ParityOfCoefficients.mat_one_inv, Matrix.one_mul]`. Distinguish the cases in `a : ∃ c ∈ C, At (evI F) (z - c)`. Unfold `coef`.

Rewrite using `[h2 hu.inv z a]`. Distinguish the cases in `a' : ∃ c ∈ C, At (evI F) (z * (mat u⁻¹)ᵀ - c)`. Unfold `coef`. Rewrite using `[← h1 hu _ a', Matrix.mul_assoc, ← Matrix.transpose_mul, show mat u * mat u⁻¹ = 1 from Units.mul_inv u.1, Matrix.transpose_one, Matrix.mul_one]`. Establish `b` using `hb f f₀ z`.

Establish `b'` using `hb f f₀ (z * (mat u⁻¹)ᵀ)`. Rewrite `b` using `[maj, if_neg a, mul_zero, norm_le_zero_iff]`. Rewrite `b'` using `[maj, if_neg a', mul_zero, norm_le_zero_iff]`. Rewrite using `[b, b']`. Establish `h4 : (starRingEnd ℂ) (om (1, u) (pureA F f₀ φ) y) ≠ 0` using `fun h => by`.

Use `key f₀ y` as an intermediate fact. Rewrite `this` using `[h, mul_zero, eq_comm, mul_eq_zero, map_eq_zero, or_self]`. Conclude with `hy this`. Take `⟨c, hc⟩ : ∃ c : ℂ, ∀ f : SInf F (Fin n × Fin d), om (1, u) (pureA F f φ) = c • pureA F f φ` from `⟨(starRingEnd ℂ) (pureA F f₀ φ y) / (starRingEnd ℂ) (om (1, u) (pureA F f₀ φ) y), fun f => funext fun x => by`. Rewrite using `[Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff h4, key, mul_comm]⟩`.

Establish `h5 : ∀ k : ℕ, om (1, u ^ k) (pureA F f₀ φ) = c ^ k • pureA F f₀ φ` using `fun k => by`. Proceed by induction on `k with`. Consider the case `zero => rw [pow_zero, pow_zero, one_smul]`. Conclude with `congrArg (· (pureA F f₀ φ)) (map_one om)`. Consider the case `succ k ih`.

Rewrite using `[pow_succ, show ((1, u ^ k * u) : UA σ X.J × UA σ W.J) = (1, u ^ k) * (1, u) from by simp, map_mul, Module.End.mul_apply, hc, map_smul, ih, smul_smul, pow_succ']`. Establish `h6 : c = 1` using `PositivityTheory.ThKH.Locrep.eq_one_of_pow_near fun k => by`. Use `h3 hu k` as an intermediate fact. Rewrite `this` using `[Set.mem_ofPred_eq, h5, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hy, mul_one]`. Then use the resulting hypothesis. Introduce `f`.

Rewrite using `[hc, h6, one_smul]`.
-/
theorem level_of_k (hC : _root_.PositivityTheory.ThKEst.CoefEq_k) (hF : FourierInj) (hB : _root_.PositivityTheory.ThKEst.CoefBd_k) : _root_.PositivityTheory.ThKEst.Level_k := by
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
  obtain ⟨μ, hμ, -⟩ := ParityOfCoefficients.exists_haar (F := F) (κ := Fin n × Fin d)
  obtain ⟨p, C, -, hCc, hb⟩ := hB F E σ B n d X W M χX χW om r s r' s' hp μ hμ φ hφ φ hφ 0
  have h1 := coef_near M hp.base.std hφ hCc
  have := LatticeQuotientMeasure.ring_AE F E
  have hi : Continuous fun u : UA σ W.J => u⁻¹ :=
    ((continuous_inv (G := GL (Fin d) (AE F E))).comp continuous_subtype_val).subtype_mk fun u => (u⁻¹).2
  have h2 := (hi.tendsto' 1 1 inv_one).eventually h1
  have hc : Continuous fun u : UA σ W.J => ‖om (1, u) (pureA F f₀ φ) y / pureA F f₀ φ y - 1‖ :=
    ((((hs.cont _ (ev_adm y) _ (mem f₀)).comp (continuous_const.prodMk continuous_id)).div_const _).sub
      continuous_const).norm
  have h3 := pow_near _ ((isOpen_lt hc (continuous_const (y := (1 / 2 : ℝ)))).mem_nhds (by
    change ‖om 1 (pureA F f₀ φ) y / pureA F f₀ φ y - 1‖ < 1 / 2
    rw [map_one, Module.End.one_apply, div_self hy]
    norm_num))
  refine ⟨_, h1.and (h2.and h3), fun u ⟨h1, h2, h3⟩ hu => ?_⟩
  have hu := isFin_of hp.base.cm B.emb hu
  have key : ∀ (f : SInf F (Fin n × Fin d)) x, om (1, u) (pureA F f φ) x * (starRingEnd ℂ) (om (1, u) (pureA F f₀ φ) y) =
      pureA F f φ x * (starRingEnd ℂ) (pureA F f₀ φ y) := by
    intro f x
    refine hF F _ B.ψ hp.base.std μ hμ _ (hs.pres _ _ (mem f)) _ (hs.pres _ _ (mem f₀)) _ (mem f) _ (mem f₀) ?_ x y
    funext w
    obtain ⟨z, rfl⟩ := M.co.e.surjective w
    rw [hC F E σ B n d X W M χX χW om r s r' s' hp μ hμ _ (mem f) _ (mem f₀), ParityOfCoefficients.mat_one_inv, Matrix.one_mul]
    by_cases a : ∃ c ∈ C, At (evI F) (z - c)
    · unfold coef
      rw [h2 hu.inv z a]
    by_cases a' : ∃ c ∈ C, At (evI F) (z * (mat u⁻¹)ᵀ - c)
    · unfold coef
      rw [← h1 hu _ a', Matrix.mul_assoc, ← Matrix.transpose_mul, show mat u * mat u⁻¹ = 1 from Units.mul_inv u.1,
        Matrix.transpose_one, Matrix.mul_one]
    have b := hb f f₀ z
    have b' := hb f f₀ (z * (mat u⁻¹)ᵀ)
    rw [maj, if_neg a, mul_zero, norm_le_zero_iff] at b
    rw [maj, if_neg a', mul_zero, norm_le_zero_iff] at b'
    rw [b, b']
  have h4 : (starRingEnd ℂ) (om (1, u) (pureA F f₀ φ) y) ≠ 0 := fun h => by
    have := key f₀ y
    rw [h, mul_zero, eq_comm, mul_eq_zero, map_eq_zero, or_self] at this
    exact hy this
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ f : SInf F (Fin n × Fin d), om (1, u) (pureA F f φ) = c • pureA F f φ :=
    ⟨(starRingEnd ℂ) (pureA F f₀ φ y) / (starRingEnd ℂ) (om (1, u) (pureA F f₀ φ) y), fun f => funext fun x => by
      rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff h4, key, mul_comm]⟩
  have h5 : ∀ k : ℕ, om (1, u ^ k) (pureA F f₀ φ) = c ^ k • pureA F f₀ φ := fun k => by
    induction k with
    | zero => rw [pow_zero, pow_zero, one_smul]; exact congrArg (· (pureA F f₀ φ)) (map_one om)
    | succ k ih =>
      rw [pow_succ, show ((1, u ^ k * u) : UA σ X.J × UA σ W.J) = (1, u ^ k) * (1, u) from by simp, map_mul,
        Module.End.mul_apply, hc, map_smul, ih, smul_smul, pow_succ']
  have h6 : c = 1 := PositivityTheory.ThKH.Locrep.eq_one_of_pow_near fun k => by
    have := h3 hu k
    rwa [Set.mem_ofPred_eq, h5, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hy, mul_one] at this
  intro f
  rw [hc, h6, one_smul]
end PositivityTheory.ThKEst
end
end
