import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IntConst
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory

noncomputable section

/- English proof (translation)
Introduce `E _ _ _ X _ μ _ w hmeas hbdd hind`. Use `set n := Module.finrank ℤ E`. Set `b : Module.Basis (Fin n) ℤ E` to `Module.finBasis ℤ E`. Establish `hmem : ∀ s, MemLp (w s) 2 μ` using `fun s => by`. Take `⟨C, hC⟩` from `hbdd s`.

Conclude with `(memLp_top_of_bound (hmeas s) C hC).mono_exponent le_top`. Set `F : Fin n → Lp ℂ 2 μ` to `fun i => (hmem (b i)).toLp _`. Set `ψ : (Fin n → ℝ) →ₗ[ℝ] Lp ℂ 2 μ` to `{ toFun := fun c => ∑ i, c i • F i map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib] map_smul' := fun a c => by simp [Finset.smul_sum, smul_smul] }`. Establish `hψ : ∀ c : Fin n → ℝ, (ψ c : X → ℂ) =ᵐ[μ] fun z => ∑ i, (c i : ℂ) * w (b i) z`. Introduce `c`.

Use `show ((∑ i, c i • F i : Lp ℂ 2 μ) : X → ℂ) =ᵐ[μ] _`. Proceed by induction on `(Finset.univ : Finset (Fin n)) using Finset.induction_on with`. Consider the case `empty`. Simplify using `only [Finset.sum_empty]`. Use `filter_upwards [Lp.coeFn_zero ℂ 2 μ] with z h`.

Rewrite using `[h]`. Both sides reduce to the same expression. Consider the case `insert i s hi ih`. Simplify using `only [Finset.sum_insert hi]`. Use `filter_upwards [Lp.coeFn_add (c i • F i) (∑ j ∈ s, c j • F j), Lp.coeFn_smul (c i) (F i), (hmem (b i)).coeFn_toLp, ih] with z h1 h2 h3 h4`.

Rewrite using `[h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, Complex.real_smul]`. Establish `hinj : Function.Injective ψ`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `c hc`. Apply `hind n b b.linearIndependent c` to reduce the goal to its premises.

Use `filter_upwards [hψ c, hc ▸ Lp.coeFn_zero ℂ 2 μ] with z h1 h2`. Rewrite using `[← h1]`. Conclude with `h2`. Establish `hcoord : ∀ s : E, ψ (fun i => (b.equivFun s i : ℝ)) = (hmem s).toLp _`. Introduce `s`.

Use `ext1`. Use `filter_upwards [hψ (fun i => (b.equivFun s i : ℝ)), (hmem s).coeFn_toLp] with z h1 h2`. Establish `hs : w s = ∑ i, b.repr s i • w (b i)` using `by conv_lhs => rw [← b.sum_repr s]`. Rewrite using `[map_sum]`. Simplify using `only [map_zsmul]`.

Rewrite using `[h1, h2, hs, Finset.sum_apply]`. Simplify using `[zsmul_eq_mul]`. Set `W` to `LinearMap.range ψ`. Set `e₁ : (Fin n → ℝ) ≃ₗ[ℝ] W` to `LinearEquiv.ofInjective ψ hinj`. Establish `hW : Module.finrank ℝ W = n`.

Rewrite using `[← e₁.finrank_eq, Module.finrank_fin_fun]`. Set `o` to `(stdOrthonormalBasis ℝ W).reindex (finCongr hW)`. Set `T : (Fin n → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n)` to `e₁.trans o.repr.toLinearEquiv`. Establish `hT : ∀ c, ‖T c‖ = ‖ψ c‖`. Introduce `c`.

Simplify using `only [T, e₁, LinearEquiv.trans_apply, LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.norm_map]`. Rewrite using `[Submodule.coe_norm, LinearEquiv.ofInjective_apply]`. Set `cast : (Fin n → ℤ) →+ (Fin n → ℝ)` to `AddMonoidHom.compLeft (Int.castAddHom ℝ) (Fin n)`. Set `φ : E →+ EuclideanSpace ℝ (Fin n)` to `(T.toLinearMap.toAddMonoidHom.comp cast).comp b.equivFun.toLinearMap.toAddMonoidHom`. Establish `hφ : ∀ s, φ s = T (fun i => (b.equivFun s i : ℝ))` using `fun s => rfl`.

Set `v : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))` to `(Pi.basisFun ℝ (Fin n)).map T`. Establish `hφb : ∀ i, φ (b i) = v i`. Introduce `i`. Rewrite using `[hφ]`. Simplify using `only [v, Module.Basis.map_apply, Pi.basisFun_apply, Module.Basis.equivFun_self]`.

Use `congr 1`. Use function extensionality and compare the values at `j`. Apply the tactic sequence `by_cases h : i = j <;> simp [h, eq_comm]`. Establish `hL : imageLattice φ = Submodule.span ℤ (Set.range v)`. Apply `le_antisymm` to reduce the goal to its premises.

Introduce and unpack `_ ⟨s, rfl⟩`. Rewrite using `[← b.sum_repr s, map_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, hφb]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `⟨b i, hφb i⟩`. Establish `key : ∀ L : Submodule ℤ (EuclideanSpace ℝ (Fin n)), L = Submodule.span ℤ (Set.range v) → DiscreteTopology L ∧ ∀ [DiscreteTopology L], IsZLattice ℝ L`. Introduce and unpack `_ rfl`.

Conclude with `⟨inferInstance, by intro _; infer_instance⟩`. Use `⟨φ, ?_, (key _ hL).1, (key _ hL).2, ?_⟩` and prove the remaining obligations. Introduce `s t hst`. Rewrite `hst` using `[hφ, hφ]`. Apply `b.equivFun.injective` to reduce the goal to its premises.

Use function extensionality and compare the values at `i`. Conclude with `congrFun (T.injective hst) i` after adjusting the coercions. Introduce `s`. Rewrite using `[hφ, hT, hcoord, Lp.norm_toLp, MemLp.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top (hmem s), ENNReal.toReal_ofReal (by positivity), Real.sqrt_eq_rpow]`. Evaluate the numerical expressions.
-/
theorem L2GramLattice.proof : L2GramLattice.Statement := by
  intro E _ _ _ X _ μ _ w hmeas hbdd hind
  classical
  set n := Module.finrank ℤ E
  let b : Module.Basis (Fin n) ℤ E := Module.finBasis ℤ E
  have hmem : ∀ s, MemLp (w s) 2 μ := fun s => by
    obtain ⟨C, hC⟩ := hbdd s
    exact (memLp_top_of_bound (hmeas s) C hC).mono_exponent le_top
  let F : Fin n → Lp ℂ 2 μ := fun i => (hmem (b i)).toLp _
  let ψ : (Fin n → ℝ) →ₗ[ℝ] Lp ℂ 2 μ :=
    { toFun := fun c => ∑ i, c i • F i
      map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun a c => by simp [Finset.smul_sum, smul_smul] }

  have hψ : ∀ c : Fin n → ℝ, (ψ c : X → ℂ) =ᵐ[μ] fun z => ∑ i, (c i : ℂ) * w (b i) z := by
    intro c
    show ((∑ i, c i • F i : Lp ℂ 2 μ) : X → ℂ) =ᵐ[μ] _
    induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      filter_upwards [Lp.coeFn_zero ℂ 2 μ] with z h
      rw [h]
      rfl
    | insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      filter_upwards [Lp.coeFn_add (c i • F i) (∑ j ∈ s, c j • F j), Lp.coeFn_smul (c i) (F i),
        (hmem (b i)).coeFn_toLp, ih] with z h1 h2 h3 h4
      rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, Complex.real_smul]
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    apply hind n b b.linearIndependent c
    filter_upwards [hψ c, hc ▸ Lp.coeFn_zero ℂ 2 μ] with z h1 h2
    rw [← h1]
    exact h2

  have hcoord : ∀ s : E, ψ (fun i => (b.equivFun s i : ℝ)) = (hmem s).toLp _ := by
    intro s
    ext1
    filter_upwards [hψ (fun i => (b.equivFun s i : ℝ)), (hmem s).coeFn_toLp] with z h1 h2
    have hs : w s = ∑ i, b.repr s i • w (b i) := by
      conv_lhs => rw [← b.sum_repr s]
      rw [map_sum]
      simp only [map_zsmul]
    rw [h1, h2, hs, Finset.sum_apply]
    simp [zsmul_eq_mul]
  let W := LinearMap.range ψ
  let e₁ : (Fin n → ℝ) ≃ₗ[ℝ] W := LinearEquiv.ofInjective ψ hinj
  have hW : Module.finrank ℝ W = n := by
    rw [← e₁.finrank_eq, Module.finrank_fin_fun]
  let o := (stdOrthonormalBasis ℝ W).reindex (finCongr hW)
  let T : (Fin n → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) := e₁.trans o.repr.toLinearEquiv
  have hT : ∀ c, ‖T c‖ = ‖ψ c‖ := by
    intro c
    simp only [T, e₁, LinearEquiv.trans_apply, LinearIsometryEquiv.coe_toLinearEquiv,
      LinearIsometryEquiv.norm_map]
    rw [Submodule.coe_norm, LinearEquiv.ofInjective_apply]
  let cast : (Fin n → ℤ) →+ (Fin n → ℝ) := AddMonoidHom.compLeft (Int.castAddHom ℝ) (Fin n)
  let φ : E →+ EuclideanSpace ℝ (Fin n) :=
    (T.toLinearMap.toAddMonoidHom.comp cast).comp b.equivFun.toLinearMap.toAddMonoidHom
  have hφ : ∀ s, φ s = T (fun i => (b.equivFun s i : ℝ)) := fun s => rfl
  let v : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) := (Pi.basisFun ℝ (Fin n)).map T
  have hφb : ∀ i, φ (b i) = v i := by
    intro i
    rw [hφ]
    simp only [v, Module.Basis.map_apply, Pi.basisFun_apply, Module.Basis.equivFun_self]
    congr 1
    funext j
    by_cases h : i = j <;> simp [h, eq_comm]
  have hL : imageLattice φ = Submodule.span ℤ (Set.range v) := by
    apply le_antisymm
    · rintro _ ⟨s, rfl⟩
      rw [← b.sum_repr s, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [map_zsmul, hφb]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨b i, hφb i⟩
  have key : ∀ L : Submodule ℤ (EuclideanSpace ℝ (Fin n)), L = Submodule.span ℤ (Set.range v) →
      DiscreteTopology L ∧ ∀ [DiscreteTopology L], IsZLattice ℝ L := by
    rintro _ rfl
    exact ⟨inferInstance, by intro _; infer_instance⟩
  refine ⟨φ, ?_, (key _ hL).1, (key _ hL).2, ?_⟩
  · intro s t hst
    rw [hφ, hφ] at hst
    apply b.equivFun.injective
    funext i
    exact_mod_cast congrFun (T.injective hst) i
  · intro s
    rw [hφ, hT, hcoord, Lp.norm_toLp,
      MemLp.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top (hmem s),
      ENNReal.toReal_ofReal (by positivity), Real.sqrt_eq_rpow]
    norm_num

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
