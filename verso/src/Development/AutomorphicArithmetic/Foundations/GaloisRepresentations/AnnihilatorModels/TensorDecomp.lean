import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PairCalc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod
open scoped TensorProduct

/- English proof (translation)
Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, 0, by simp⟩`. Consider the case `tmul c z`. Choose the witnesses or unpack the hypotheses as in `⟨r, z', hz⟩ : ∃ (r : ℤ) (z' : ℤ_[p]), z = r • (1 : ℤ_[p]) + (p : ℤ) • z' := by`. Establish `h : z - (PadicInt.zmodRepr z : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p])}`.

Rewrite using `[← PadicInt.maximalIdeal_eq_span_p]`. Conclude with `PadicInt.sub_zmodRepr_mem z`. Take `⟨z', hz'⟩` from `Ideal.mem_span_singleton'.mp h`. Use `⟨(PadicInt.zmodRepr z : ℤ), z', ?_⟩` and prove the remaining obligations. Establish `: z = (PadicInt.zmodRepr z : ℤ_[p]) + z' * p` using `by rw [hz']; ring`.

Simplify using `only [zsmul_eq_mul, mul_one]`. Use `push_cast`. Rewrite using `[mul_comm (p : ℤ_[p])]`. Apply the tactic sequence `first | (rw [mul_one]; exact this) | simpa using this`. Use `⟨r • c, c ⊗ₜ[ℤ] z', ?_⟩` and prove the remaining obligations.

Rewrite using `[hz, TensorProduct.tmul_add, TensorProduct.tmul_smul (p : ℤ), TensorProduct.tmul_smul r, TensorProduct.smul_tmul']`. Consider the case `add a b ha hb`. Take `⟨c, a', rfl⟩` from `ha`. Take `⟨d, b', rfl⟩` from `hb`. Conclude with `⟨c + d, a' + b', by rw [TensorProduct.add_tmul, smul_add]; abel⟩`.
-/
private lemma UpperTheory.Gal.crystallineComparison.Mod.tensor_decomp (p : ℕ) [Fact p.Prime] (B : Type) [AddCommGroup B]
    (a : B ⊗[ℤ] ℤ_[p]) :
    ∃ (c : B) (a' : B ⊗[ℤ] ℤ_[p]), a = c ⊗ₜ[ℤ] (1 : ℤ_[p]) + (p : ℤ) • a' := by
  induction a using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul c z =>
    obtain ⟨r, z', hz⟩ : ∃ (r : ℤ) (z' : ℤ_[p]), z = r • (1 : ℤ_[p]) + (p : ℤ) • z' := by
      have h : z - (PadicInt.zmodRepr z : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p])} := by
        rw [← PadicInt.maximalIdeal_eq_span_p]
        exact PadicInt.sub_zmodRepr_mem z
      obtain ⟨z', hz'⟩ := Ideal.mem_span_singleton'.mp h
      refine ⟨(PadicInt.zmodRepr z : ℤ), z', ?_⟩
      have : z = (PadicInt.zmodRepr z : ℤ_[p]) + z' * p := by rw [hz']; ring
      simp only [zsmul_eq_mul, mul_one]
      push_cast
      rw [mul_comm (p : ℤ_[p])]
      first | (rw [mul_one]; exact this) | simpa using this
    refine ⟨r • c, c ⊗ₜ[ℤ] z', ?_⟩
    rw [hz, TensorProduct.tmul_add, TensorProduct.tmul_smul (p : ℤ), TensorProduct.tmul_smul r,
      TensorProduct.smul_tmul']
  | add a b ha hb =>
    obtain ⟨c, a', rfl⟩ := ha
    obtain ⟨d, b', rfl⟩ := hb
    exact ⟨c + d, a' + b', by rw [TensorProduct.add_tmul, smul_add]; abel⟩

/- English proof (translation)
Introduce `p _ D hm x`. Take `⟨e⟩` from `D.splitP`. Establish `hsub : Subsingleton (Fin D.m)` using `by rw [hm]; infer_instance`. Set `i0 : Fin D.m` to `⟨0, D.m_pos⟩`. Take `⟨c, a', ha⟩` from `tensor_decomp p (𝓞 D.F) (e (x ⊗ₜ[ℤ] (1 : ℤ_[p])) i0 i0)`.

Set `M' : Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p])` to `Matrix.of fun _ _ => a'`. Establish `hM : e (x ⊗ₜ[ℤ] (1 : ℤ_[p])) = algebraMap (𝓞 D.F) _ c + (p : ℤ) • M'`. Use extensionality with `i j`. Take `rfl` from `Subsingleton.elim i i0`. Take `rfl` from `Subsingleton.elim j i0`.

Rewrite using `[ha]`. Simplify using `[M', Matrix.algebraMap_matrix_apply, Algebra.TensorProduct.algebraMap_apply]`. Establish `hx : x ⊗ₜ[ℤ] (1 : ℤ_[p]) = (algebraMap (𝓞 D.F) D.O c) ⊗ₜ[ℤ] (1 : ℤ_[p]) + (p : ℤ) • e.symm M'`. Use `congrArg e.symm hM` as an intermediate fact. Rewrite `this` using `[e.symm_apply_apply, map_add, map_zsmul, AlgEquiv.commutes, Algebra.TensorProduct.algebraMap_apply]`.

Conclude with `this`. Set `P : Submodule ℤ D.O` to `LinearMap.range (LinearMap.lsmul ℤ D.O (p : ℤ))`. Establish `hP : ∀ q : D.O ⧸ P, p • q = 0`. Introduce `q`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective P q`.

Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Conclude with `⟨y, by simp⟩`. Use `letI : Module (ZMod p) (D.O ⧸ P) := AddCommGroup.zmodModule hP`. Set `Φ : D.O ⊗[ℤ] ℤ_[p] →ₗ[ℤ] D.O ⧸ P` to `TensorProduct.lift <| LinearMap.mk₂ ℤ (fun y z => PadicInt.toZMod z • (Submodule.Quotient.mk y : D.O ⧸ P)) (fun y y' z => by simp [smul_add]) (fun n y z => by rw [Submodule.Quotient.mk_smul]; exact smul_comm _ _ _) (fun y z z' => by simp [add_smul]) (fun n y z => by rw [map_zsmul …`. Establish `h1 : ∀ y : D.O, Φ (y ⊗ₜ[ℤ] (1 : ℤ_[p])) = Submodule.Quotient.mk y`.

Introduce `y`. Express the relevant statement in the definitionally equal form `PadicInt.toZMod (1 : ℤ_[p]) • (Submodule.Quotient.mk y : D.O ⧸ P) = _`. Rewrite using `[map_one, one_smul]`. Establish `h2` using `congrArg Φ hx`. Rewrite `h2` using `[map_add, map_zsmul, h1, h1]`.

Establish `h3 : (p : ℤ) • Φ (e.symm M') = 0`. Rewrite using `[natCast_zsmul]`. Conclude with `hP _`. Rewrite `h2` using `[h3, add_zero, Submodule.Quotient.eq]`. Take `⟨y, hy⟩` from `h2`.

Use `⟨c, y, ?_⟩` and prove the remaining obligations. Establish `hy' : (p : ℤ) • y = x - algebraMap (𝓞 D.F) D.O c` using `hy`. Rewrite using `[map_natCast, ← sub_eq_iff_eq_add', ← hy']`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.Gal.crystallineComparison.Mod.oMod_of :
    OMod := by
  intro p _ D hm x
  obtain ⟨e⟩ := D.splitP
  have hsub : Subsingleton (Fin D.m) := by rw [hm]; infer_instance
  let i0 : Fin D.m := ⟨0, D.m_pos⟩
  obtain ⟨c, a', ha⟩ := tensor_decomp p (𝓞 D.F) (e (x ⊗ₜ[ℤ] (1 : ℤ_[p])) i0 i0)
  let M' : Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p]) := Matrix.of fun _ _ => a'
  have hM : e (x ⊗ₜ[ℤ] (1 : ℤ_[p])) = algebraMap (𝓞 D.F) _ c + (p : ℤ) • M' := by
    ext i j
    obtain rfl := Subsingleton.elim i i0
    obtain rfl := Subsingleton.elim j i0
    rw [ha]
    simp [M', Matrix.algebraMap_matrix_apply, Algebra.TensorProduct.algebraMap_apply]
  have hx : x ⊗ₜ[ℤ] (1 : ℤ_[p]) =
      (algebraMap (𝓞 D.F) D.O c) ⊗ₜ[ℤ] (1 : ℤ_[p]) + (p : ℤ) • e.symm M' := by
    have := congrArg e.symm hM
    rw [e.symm_apply_apply, map_add, map_zsmul, AlgEquiv.commutes,
      Algebra.TensorProduct.algebraMap_apply] at this
    exact this
  let P : Submodule ℤ D.O := LinearMap.range (LinearMap.lsmul ℤ D.O (p : ℤ))
  have hP : ∀ q : D.O ⧸ P, p • q = 0 := by
    intro q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective P q
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨y, by simp⟩
  letI : Module (ZMod p) (D.O ⧸ P) := AddCommGroup.zmodModule hP
  let Φ : D.O ⊗[ℤ] ℤ_[p] →ₗ[ℤ] D.O ⧸ P := TensorProduct.lift <|
    LinearMap.mk₂ ℤ (fun y z => PadicInt.toZMod z • (Submodule.Quotient.mk y : D.O ⧸ P))
      (fun y y' z => by simp [smul_add])
      (fun n y z => by rw [Submodule.Quotient.mk_smul]; exact smul_comm _ _ _)
      (fun y z z' => by simp [add_smul])
      (fun n y z => by rw [map_zsmul, smul_assoc])
  have h1 : ∀ y : D.O, Φ (y ⊗ₜ[ℤ] (1 : ℤ_[p])) = Submodule.Quotient.mk y := by
    intro y
    change PadicInt.toZMod (1 : ℤ_[p]) • (Submodule.Quotient.mk y : D.O ⧸ P) = _
    rw [map_one, one_smul]
  have h2 := congrArg Φ hx
  rw [map_add, map_zsmul, h1, h1] at h2
  have h3 : (p : ℤ) • Φ (e.symm M') = 0 := by
    rw [natCast_zsmul]; exact hP _
  rw [h3, add_zero, Submodule.Quotient.eq] at h2
  obtain ⟨y, hy⟩ := h2
  refine ⟨c, y, ?_⟩
  have hy' : (p : ℤ) • y = x - algebraMap (𝓞 D.F) D.O c := hy
  rw [map_natCast, ← sub_eq_iff_eq_add', ← hy']
  simp
