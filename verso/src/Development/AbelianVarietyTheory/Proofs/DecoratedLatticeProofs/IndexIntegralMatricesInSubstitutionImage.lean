import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LawLoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexMatrixLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmEqSumLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm

noncomputable section

namespace GlobalTheory.LocOm.IntIndex

section Det

variable {K : Type} [Field K] {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

def mulRight (Y : Type) (G : Matrix Y' Y' K) : Matrix Y Y' K →ₗ[K] Matrix Y Y' K :=
  LinearMap.pi fun i : Y => (Matrix.toLin' Gᵀ).comp (LinearMap.proj i)

/- English proof (translation)
Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `(Gᵀ.mulVec (w i)) j = _`. Rewrite using `[Matrix.mulVec_transpose]`. Both sides reduce to the same expression.
-/
theorem mulRight_apply (G : Matrix Y' Y' K) (w : Matrix Y Y' K) : mulRight Y G w = w * G := by
  ext i j
  change (Gᵀ.mulVec (w i)) j = _
  rw [Matrix.mulVec_transpose]
  rfl

/- English proof (translation)
Use `LinearMap.det_pi (R := K) (ι := Y) fun _ => Matrix.toLin' Gᵀ` as an intermediate fact. Rewrite `this` using `[LinearMap.det_toLin', Matrix.det_transpose, Finset.prod_const, Finset.card_univ]`. Conclude with `this`.
-/
theorem det_mulRight (G : Matrix Y' Y' K) : LinearMap.det (mulRight Y G) = G.det ^ Fintype.card Y := by
  have := LinearMap.det_pi (R := K) (ι := Y) fun _ => Matrix.toLin' Gᵀ
  rw [LinearMap.det_toLin', Matrix.det_transpose, Finset.prod_const, Finset.card_univ] at this
  exact this

/- English proof (translation)
Set `τ` to `Matrix.transposeLinearEquiv Y' Y K K`. Use `⟨mulRight Y G ∘ₗ ((τ : _ →ₗ[K] _) ∘ₗ mulRight Y' Hᵀ ∘ₗ (τ.symm : _ →ₗ[K] _)), fun w => ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `mulRight Y G (mulRight Y' Hᵀ wᵀ)ᵀ = _`. Rewrite using `[mulRight_apply, mulRight_apply, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose]`. Rewrite using `[LinearMap.det_comp, LinearMap.det_conj, det_mulRight, det_mulRight, Matrix.det_transpose]`.
-/
theorem exists_mul_map (H : Matrix Y Y K) (G : Matrix Y' Y' K) :
    ∃ B : Matrix Y Y' K →ₗ[K] Matrix Y Y' K, (∀ w, B w = H * w * G) ∧
      LinearMap.det B = G.det ^ Fintype.card Y * H.det ^ Fintype.card Y' := by
  let τ := Matrix.transposeLinearEquiv Y' Y K K
  refine ⟨mulRight Y G ∘ₗ ((τ : _ →ₗ[K] _) ∘ₗ mulRight Y' Hᵀ ∘ₗ (τ.symm : _ →ₗ[K] _)), fun w => ?_, ?_⟩
  · change mulRight Y G (mulRight Y' Hᵀ wᵀ)ᵀ = _
    rw [mulRight_apply, mulRight_apply, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose]
  · rw [LinearMap.det_comp, LinearMap.det_conj, det_mulRight, det_mulRight, Matrix.det_transpose]

end Det

/- English proof (translation)
Introduce `k _ _ _ _ Y Y' _ _ _ _ gk hk hE`. Set `M : Submodule 𝒪[k] (Matrix Y Y' k)` to `{ carrier := {x | ∀ r q, x r q ∈ 𝒪[k]} add_mem' := fun ha hb r q => add_mem (ha r q) (hb r q) zero_mem' := fun _ _ => zero_mem _ smul_mem' := fun c x hx r q => by`. Rewrite using `[Matrix.smul_apply, Algebra.smul_def]`. Conclude with `mul_mem c.2 (hx r q) }`. Use `haveI : Submodule.IsLattice k M := by`.

Prove the components needed by the constructor for the conclusion. Set `φ : Matrix Y Y' 𝒪[k] →ₗ[𝒪[k]] Matrix Y Y' k` to `(Algebra.linearMap 𝒪[k] k).mapMatrix`. Use `Submodule.FG.of_le (Submodule.fg_range φ) fun m hm => ⟨Matrix.of fun i j => ⟨m i j, hm i j⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Both sides reduce to the same expression.

Rewrite using `[eq_top_iff]`. Introduce `w _`. Rewrite using `[Matrix.matrix_eq_sum_single w]`. Use `Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Establish `h1 : Matrix.single i j (1 : k) ∈ M` using `fun r q => by`.

Rewrite using `[Matrix.single_apply]`. Use `split_ifs`. Use `exacts [one_mem _, zero_mem _]`. Use `Submodule.smul_mem _ (w i j) (Submodule.subset_span (R := k) h1)` as an intermediate fact. Rewrite `this` using `[Matrix.smul_single, smul_eq_mul, mul_one]`. Then use the resulting hypothesis.

Take `⟨Bl, hBl, hd⟩` from `exists_mul_map (↑(hk⁻¹) : Matrix Y Y k) (↑gk : Matrix Y' Y' k)`. Establish `hbij : Function.Bijective Bl`. Use `Function.bijective_iff_has_inverse.2 ⟨fun w => (↑hk : Matrix Y Y k) * w * (↑(gk⁻¹) : Matrix Y' Y' k), fun w => ?_, fun w => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(↑hk : Matrix Y Y k) * Bl w * (↑(gk⁻¹) : Matrix Y' Y' k) = w`. Rewrite using `[hBl]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = w := by rw [hk.mul_inv, gk.mul_inv, Matrix.one_mul, Matrix.mul_one]`. Express the relevant statement in the definitionally equal form `Bl ((↑hk : Matrix Y Y k) * w * (↑(gk⁻¹) : Matrix Y' Y' k)) = w`. Rewrite using `[hBl]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = w := by rw [hk.inv_mul, gk.inv_mul, Matrix.one_mul, Matrix.mul_one]`. Establish `hM : ∀ m ∈ M, Bl m ∈ M` using `fun m hm => show ∀ r q, (Bl m) r q ∈ 𝒪[k] by rw [hBl]; exact hE m hm`. Take `⟨p, hp⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[k]`.

Take `⟨m, u, e1, e2⟩` from `GlobalTheory.SplitLinear.relIndex_comap_lattice M Bl hbij hM hp`. Establish `hq : Nat.card (𝒪[k] ⧸ Ideal.span {p}) = resCard k`. Rewrite using `[resCard, ← hp.maximalIdeal_eq]`. Both sides reduce to the same expression. Establish `hq0 : 0 < resCard k` using `Nat.card_pos`.

Use `set A := M.toAddSubgroup with hA`. Use `set Bs := AddSubgroup.comap Bl.toAddMonoidHom A with hBs`. Establish `hne : A.relIndex Bs ≠ 0` using `by rw [e2, hq]; exact pow_ne_zero _ hq0.ne'`. Use `haveI : (A.addSubgroupOf Bs).FiniteIndex := ⟨hne⟩`. Use `haveI : Finite (Bs ⧸ A.addSubgroupOf Bs) := AddSubgroup.finite_quotient_of_finiteIndex`.

Take `⟨R, hRc, hRB, hRu⟩` from `GlobalTheory.SplitLinear.exists_reps A Bs`. Establish `hmemB : ∀ w, w ∈ Bs ↔ ∀ r q, ((↑(hk⁻¹) : Matrix Y Y k) * w * (↑gk : Matrix Y' Y' k)) r q ∈ 𝒪[k]`. Introduce `w`. Express the relevant statement in the definitionally equal form `(∀ r q, (Bl w) r q ∈ 𝒪[k]) ↔ _`. Rewrite using `[hBl]`.

Use `⟨R, ?_, fun v hv => (hmemB v).1 (hRB v hv), fun w hw => hRu w ((hmemB w).2 hw)⟩` and prove the remaining obligations. Establish `hpow : ∀ (x : kˣ) (n : ℕ), nabs k (x ^ n) = nabs k x ^ n`. Introduce `x n`. Simplify using `[nabs, map_pow]`. Establish `hinv : ∀ x : kˣ, nabs k x⁻¹ = (nabs k x)⁻¹`.

Introduce `x`. Simplify using `[nabs, map_inv]`. Establish `hp0 : (p : k) ≠ 0` using `fun h => hp.ne_zero (by exact_mod_cast h)`. Set `X : kˣ` to `Matrix.GeneralLinearGroup.det gk ^ Fintype.card Y * Matrix.GeneralLinearGroup.det hk⁻¹ ^ Fintype.card Y'`. Set `U : kˣ` to `Units.map (algebraMap 𝒪[k] k : 𝒪[k] →* k) u`.

Set `P : kˣ` to `Units.mk0 (p : k) hp0`. Establish `hXU : X * U = P ^ m`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, ← hd]`. Conclude with `e1`.

Establish `hU : nabs k U = 1`. Apply `nabs_eq_one_of_valuation_eq_one` to reduce the goal to its premises. Conclude with `(Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.mp u.isUnit`. Establish `hP : nabs k P = (resCard k : ℝ)⁻¹` using `nabs_uniformiser hp rfl`. Establish `key` using `congrArg (nabs k) hXU`.

Rewrite `key` using `[GlobalTheory.SplitWeil.nabs_mul, GlobalTheory.SplitWeil.nabs_mul, hpow, hpow, hpow, hU, hP, map_inv, hinv, mul_one]`. Rewrite using `[hRc, e2, hq, Real.rpow_natCast, Real.rpow_neg (GlobalTheory.SplitWeil.nabs_pos k _).le, Real.rpow_natCast]`. Use `push_cast`. Establish `hq' : ((resCard k : ℝ)) ^ m = (((resCard k : ℝ))⁻¹ ^ m)⁻¹` using `by rw [inv_pow, inv_inv]`. Rewrite using `[hq', ← key, inv_pow (nabs k _), mul_inv, inv_inv, mul_comm]`.
-/
theorem index_integral_image : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (gk : GL Y' k) (hk : GL Y k), Enl gk hk → ∃ R₀ : Finset (Matrix Y Y' k), (R₀.card : ℝ) = nabs k (Matrix.GeneralLinearGroup.det hk) ^ (Fintype.card Y' : ℝ) * nabs k (Matrix.GeneralLinearGroup.det gk) ^ (-(Fintype.card Y : ℝ)) ∧ (∀ v ∈ R₀, ∀ r q, ((↑(hk⁻¹) : Matrix Y Y k) * v * (↑gk : Matrix Y' Y' k)) r q ∈ 𝒪[k]) ∧ ∀ w : Matrix Y Y' k, (∀ r q, ((↑(hk⁻¹) : Matrix Y Y k) * w * (↑gk : Matrix Y' Y' k)) r q ∈ 𝒪[k]) → ∃! v, v ∈ R₀ ∧ ∀ r q, (w - v) r q ∈ 𝒪[k] := by
  intro k _ _ _ _ Y Y' _ _ _ _ gk hk hE
  let M : Submodule 𝒪[k] (Matrix Y Y' k) :=
    { carrier := {x | ∀ r q, x r q ∈ 𝒪[k]}
      add_mem' := fun ha hb r q => add_mem (ha r q) (hb r q)
      zero_mem' := fun _ _ => zero_mem _
      smul_mem' := fun c x hx r q => by
        rw [Matrix.smul_apply, Algebra.smul_def]
        exact mul_mem c.2 (hx r q) }
  haveI : Submodule.IsLattice k M := by
    constructor
    · let φ : Matrix Y Y' 𝒪[k] →ₗ[𝒪[k]] Matrix Y Y' k := (Algebra.linearMap 𝒪[k] k).mapMatrix
      refine Submodule.FG.of_le (Submodule.fg_range φ) fun m hm => ⟨Matrix.of fun i j => ⟨m i j, hm i j⟩, ?_⟩
      ext i j
      rfl
    · rw [eq_top_iff]
      intro w _
      rw [Matrix.matrix_eq_sum_single w]
      refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
      have h1 : Matrix.single i j (1 : k) ∈ M := fun r q => by
        rw [Matrix.single_apply]
        split_ifs
        exacts [one_mem _, zero_mem _]
      have := Submodule.smul_mem _ (w i j) (Submodule.subset_span (R := k) h1)
      rwa [Matrix.smul_single, smul_eq_mul, mul_one] at this
  obtain ⟨Bl, hBl, hd⟩ := exists_mul_map (↑(hk⁻¹) : Matrix Y Y k) (↑gk : Matrix Y' Y' k)
  have hbij : Function.Bijective Bl := by
    refine Function.bijective_iff_has_inverse.2
      ⟨fun w => (↑hk : Matrix Y Y k) * w * (↑(gk⁻¹) : Matrix Y' Y' k), fun w => ?_, fun w => ?_⟩
    · change (↑hk : Matrix Y Y k) * Bl w * (↑(gk⁻¹) : Matrix Y' Y' k) = w
      rw [hBl]
      calc (↑hk : Matrix Y Y k) * ((↑(hk⁻¹) : Matrix Y Y k) * w * (↑gk : Matrix Y' Y' k)) * (↑(gk⁻¹) : Matrix Y' Y' k)
          = ((↑hk : Matrix Y Y k) * (↑(hk⁻¹) : Matrix Y Y k)) * w * ((↑gk : Matrix Y' Y' k) * (↑(gk⁻¹) : Matrix Y' Y' k)) := by
            simp only [Matrix.mul_assoc]
        _ = w := by rw [hk.mul_inv, gk.mul_inv, Matrix.one_mul, Matrix.mul_one]
    · change Bl ((↑hk : Matrix Y Y k) * w * (↑(gk⁻¹) : Matrix Y' Y' k)) = w
      rw [hBl]
      calc (↑(hk⁻¹) : Matrix Y Y k) * ((↑hk : Matrix Y Y k) * w * (↑(gk⁻¹) : Matrix Y' Y' k)) * (↑gk : Matrix Y' Y' k)
          = ((↑(hk⁻¹) : Matrix Y Y k) * (↑hk : Matrix Y Y k)) * w * ((↑(gk⁻¹) : Matrix Y' Y' k) * (↑gk : Matrix Y' Y' k)) := by
            simp only [Matrix.mul_assoc]
        _ = w := by rw [hk.inv_mul, gk.inv_mul, Matrix.one_mul, Matrix.mul_one]
  have hM : ∀ m ∈ M, Bl m ∈ M := fun m hm =>
    show ∀ r q, (Bl m) r q ∈ 𝒪[k] by rw [hBl]; exact hE m hm
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  obtain ⟨m, u, e1, e2⟩ := GlobalTheory.SplitLinear.relIndex_comap_lattice M Bl hbij hM hp
  have hq : Nat.card (𝒪[k] ⧸ Ideal.span {p}) = resCard k := by
    rw [resCard, ← hp.maximalIdeal_eq]
    rfl
  have hq0 : 0 < resCard k := Nat.card_pos
  set A := M.toAddSubgroup with hA
  set Bs := AddSubgroup.comap Bl.toAddMonoidHom A with hBs
  have hne : A.relIndex Bs ≠ 0 := by rw [e2, hq]; exact pow_ne_zero _ hq0.ne'
  haveI : (A.addSubgroupOf Bs).FiniteIndex := ⟨hne⟩
  haveI : Finite (Bs ⧸ A.addSubgroupOf Bs) := AddSubgroup.finite_quotient_of_finiteIndex
  obtain ⟨R, hRc, hRB, hRu⟩ := GlobalTheory.SplitLinear.exists_reps A Bs
  have hmemB : ∀ w, w ∈ Bs ↔ ∀ r q, ((↑(hk⁻¹) : Matrix Y Y k) * w * (↑gk : Matrix Y' Y' k)) r q ∈ 𝒪[k] := by
    intro w
    change (∀ r q, (Bl w) r q ∈ 𝒪[k]) ↔ _
    rw [hBl]
  refine ⟨R, ?_, fun v hv => (hmemB v).1 (hRB v hv), fun w hw => hRu w ((hmemB w).2 hw)⟩

  have hpow : ∀ (x : kˣ) (n : ℕ), nabs k (x ^ n) = nabs k x ^ n := by
    intro x n; simp [nabs, map_pow]
  have hinv : ∀ x : kˣ, nabs k x⁻¹ = (nabs k x)⁻¹ := by
    intro x; simp [nabs, map_inv]
  have hp0 : (p : k) ≠ 0 := fun h => hp.ne_zero (by exact_mod_cast h)
  let X : kˣ := Matrix.GeneralLinearGroup.det gk ^ Fintype.card Y * Matrix.GeneralLinearGroup.det hk⁻¹ ^ Fintype.card Y'
  let U : kˣ := Units.map (algebraMap 𝒪[k] k : 𝒪[k] →* k) u
  let P : kˣ := Units.mk0 (p : k) hp0
  have hXU : X * U = P ^ m := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, ← hd]
    exact e1
  have hU : nabs k U = 1 := by
    apply nabs_eq_one_of_valuation_eq_one
    exact (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.mp u.isUnit
  have hP : nabs k P = (resCard k : ℝ)⁻¹ := nabs_uniformiser hp rfl
  have key := congrArg (nabs k) hXU
  rw [GlobalTheory.SplitWeil.nabs_mul, GlobalTheory.SplitWeil.nabs_mul, hpow, hpow, hpow, hU, hP, map_inv, hinv, mul_one] at key
  rw [hRc, e2, hq, Real.rpow_natCast, Real.rpow_neg (GlobalTheory.SplitWeil.nabs_pos k _).le, Real.rpow_natCast]
  push_cast
  have hq' : ((resCard k : ℝ)) ^ m = (((resCard k : ℝ))⁻¹ ^ m)⁻¹ := by rw [inv_pow, inv_inv]
  rw [hq', ← key, inv_pow (nabs k _), mul_inv, inv_inv, mul_comm]

end GlobalTheory.LocOm.IntIndex

end
