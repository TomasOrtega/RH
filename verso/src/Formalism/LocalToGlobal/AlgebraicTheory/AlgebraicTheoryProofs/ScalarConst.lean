import Formalism.LocalToGlobal.AlgebraicTheory.StatementD
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.SelfDualCovolume

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.AlgTh

open Formalism.L2.Th1.H

namespace SC

variable {n : Type} [Fintype n]

/- English proof (translation)
Simplify using `[cLat, imgLat, AddSubgroup.mem_map]`.
-/
theorem mem_cLat {c : ℂ} {Λ : AddSubgroup (n → ℂ)} {y : n → ℂ} :
    y ∈ cLat c Λ ↔ ∃ x ∈ Λ, c • x = y := by
  simp [cLat, imgLat, AddSubgroup.mem_map]

/- English proof (translation)
Take `⟨b, hb⟩` from `exists_basis_of_lattice Λ hL.1 hL.2`. Set `f : (n → ℂ) ≃ₗ[ℝ] (n → ℂ)` to `(LinearEquiv.smulOfNeZero ℂ (n → ℂ) c hc).restrictScalars ℝ`. Establish `hmap : cLat c Λ = Λ.map (f : (n → ℂ) →ₗ[ℝ] (n → ℂ)).toAddMonoidHom`. Use extensionality with `y`. Rewrite using `[mem_cLat, AddSubgroup.mem_map]`.

Both sides reduce to the same expression. Establish `hle : Λ.map (f : (n → ℂ) →ₗ[ℝ] (n → ℂ)).toAddMonoidHom ≤ Λ`. Rewrite using `[← hmap]`. Introduce `y hy`. Take `⟨x, hx, rfl⟩` from `mem_cLat.1 hy`.

Conclude with `hcΛ x hx`. Establish `key` using `relIndex_map_real Λ Λ le_rfl b b hb hb f hle`. Establish `hdet : LinearMap.det (f : (n → ℂ) →ₗ[ℝ] (n → ℂ)) = Complex.normSq c ^ Fintype.card n`. Establish `e : (f : (n → ℂ) →ₗ[ℝ] (n → ℂ)) = ((c • LinearMap.id : (n → ℂ) →ₗ[ℂ] (n → ℂ))).restrictScalars ℝ`. Use extensionality with `x`.

Both sides reduce to the same expression. Rewrite using `[e, LinearMap.det_restrictScalars, LinearMap.det_smul, LinearMap.det_id, mul_one, Module.finrank_fintype_fun_eq_card, map_pow, Algebra.norm_complex_apply]`. Unfold `relIdx`. Rewrite using `[hmap, key, AddSubgroup.relIndex_self, Nat.cast_one, one_mul, hdet, abs_of_nonneg (pow_nonneg (Complex.normSq_nonneg c) _)]`.
-/
theorem relIdx_cLat (Λ : AddSubgroup (n → ℂ)) (hL : IsLat Λ) (c : ℂ) (hc : c ≠ 0)
    (hcΛ : ∀ x ∈ Λ, c • x ∈ Λ) :
    (relIdx (cLat c Λ) Λ : ℝ) = Complex.normSq c ^ Fintype.card n := by
  obtain ⟨b, hb⟩ := exists_basis_of_lattice Λ hL.1 hL.2
  let f : (n → ℂ) ≃ₗ[ℝ] (n → ℂ) := (LinearEquiv.smulOfNeZero ℂ (n → ℂ) c hc).restrictScalars ℝ
  have hmap : cLat c Λ = Λ.map (f : (n → ℂ) →ₗ[ℝ] (n → ℂ)).toAddMonoidHom := by
    ext y
    rw [mem_cLat, AddSubgroup.mem_map]
    rfl
  have hle : Λ.map (f : (n → ℂ) →ₗ[ℝ] (n → ℂ)).toAddMonoidHom ≤ Λ := by
    rw [← hmap]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_cLat.1 hy
    exact hcΛ x hx
  have key := relIndex_map_real Λ Λ le_rfl b b hb hb f hle
  have hdet : LinearMap.det (f : (n → ℂ) →ₗ[ℝ] (n → ℂ)) = Complex.normSq c ^ Fintype.card n := by
    have e : (f : (n → ℂ) →ₗ[ℝ] (n → ℂ))
        = ((c • LinearMap.id : (n → ℂ) →ₗ[ℂ] (n → ℂ))).restrictScalars ℝ := by
      ext x
      rfl
    rw [e, LinearMap.det_restrictScalars, LinearMap.det_smul, LinearMap.det_id, mul_one,
      Module.finrank_fintype_fun_eq_card, map_pow, Algebra.norm_complex_apply]
  unfold relIdx
  rw [hmap, key, AddSubgroup.relIndex_self, Nat.cast_one, one_mul, hdet,
    abs_of_nonneg (pow_nonneg (Complex.normSq_nonneg c) _)]

/- English proof (translation)
Introduce `h0`. Apply `hA` to reduce the goal to its premises. Unfold `relIdx at *`. Conclude with `AddSubgroup.relIndex_eq_zero_of_le_left h h0`.
-/
theorem relIdx_ne_of_le {V : Type*} [AddCommGroup V] {A B L : AddSubgroup V} (h : A ≤ B)
    (hA : relIdx A L ≠ 0) : relIdx B L ≠ 0 := by
  intro h0
  apply hA
  unfold relIdx at *
  exact AddSubgroup.relIndex_eq_zero_of_le_left h h0

end SC

open SC in
/- English proof (translation)
Introduce `dK n _ _ h Λ hH hP hL hSD hSC hLine p hp π hππ hne hπΛ hπbΛ huw' Sa hSa θ hθ hθ0`. Take `⟨u, w, huΛ, hwΛ, huw⟩` from `huw'`. Use `set α := alphaQ (Real.sqrt dK / 2) (matH h) with hα`. Establish `hp0 : (p : ℂ) ≠ 0` using `by exact_mod_cast hp.ne_zero`. Establish `hπ0 : π ≠ 0` using `fun h0 => hp0 (by rw [← hππ, h0, zero_mul])`.

Establish `hπb0 : conj π ≠ 0` using `fun h0 => hp0 (by rw [← hππ, h0, mul_zero])`. Establish `hnsq : Complex.normSq π = p`. Use `Complex.mul_conj π` as an intermediate fact. Conclude with `this.symm.trans hππ` after adjusting the coercions. Establish `hnsqb : Complex.normSq (conj π) = p` using `by rw [Complex.normSq_conj, hnsq]`.

Use `set d := conj π / π with hd`. Establish `hd0 : d ≠ 0` using `div_ne_zero hπb0 hπ0`. Establish `hdπ : d * π = conj π` using `div_mul_cancel₀ _ hπ0`. Establish `hdd : d * conj d = 1`. Rewrite using `[hd, map_div₀, Complex.conj_conj, div_mul_div_comm, mul_comm (conj π) π, div_self (mul_ne_zero hπ0 hπb0)]`.

Establish `he0 : (1 - π / conj π) ≠ 0`. Introduce `h0`. Apply `hne` to reduce the goal to its premises. Establish `h1 : π / conj π = 1` using `by linear_combination -h0`. Conclude with `((div_eq_one_iff_eq hπb0).1 h1).symm`.

Set `δ : (n → ℂ) ≃ₗ[ℂ] (n → ℂ)` to `LinearEquiv.smulOfNeZero ℂ (n → ℂ) d hd0`. Set `Ae : (n → ℂ) ≃ₗ[ℂ] (n → ℂ)` to `LinearEquiv.smulOfNeZero ℂ (n → ℂ) (1 - π / conj π) he0`. Establish `hδ : ∀ x, δ x = d • x` using `fun x => rfl`. Establish `hδs : ∀ x, δ.symm x = d⁻¹ • x` using `fun x => by`. Apply `δ.injective` to reduce the goal to its premises.

Rewrite using `[LinearEquiv.apply_symm_apply, hδ, smul_smul, mul_inv_cancel₀ hd0, one_smul]`. Establish `hδlin : (δ : (n → ℂ) →ₗ[ℂ] (n → ℂ)) = d • LinearMap.id` using `LinearMap.ext fun x => by`. Simplify using `[hδ]`. Establish `hδΛ : imgLat (δ : (n → ℂ) →ₗ[ℂ] (n → ℂ)) Λ = cLat d Λ` using `by rw [cLat, hδlin]`. Establish `hisomxy : ∀ x y, matH h (δ x) (δ y) = matH h x y`.

Introduce `x y`. Simplify using `only [hδ, map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul]`. Rewrite using `[← mul_assoc, mul_comm (conj d) d, hdd, one_mul]`. Establish `hisom : IsIsom (matH h) (matH h) (δ : (n → ℂ) →ₗ[ℂ] (n → ℂ))` using `fun x y => hisomxy x y`. Establish `hαinv : ∀ x, α (δ x) = α x` using `fun x => alphaQRules.1 (n → ℂ) (n → ℂ) (matH h) (matH h) _ hisom (Real.sqrt dK / 2) x`.

Establish `hsemi' : IsSemiChar (matH h) (imgLat (δ : (n → ℂ) →ₗ[ℂ] (n → ℂ)) Λ) α`. Prove the components needed by the constructor for the conclusion. Introduce `y hy`. Take `⟨x, hx, rfl⟩` from `AddSubgroup.mem_map.1 hy`. Establish `e1 : (δ : (n → ℂ) →ₗ[ℂ] (n → ℂ)).toAddMonoidHom x = δ x` using `rfl`.

Rewrite using `[e1, hαinv]`. Conclude with `hSC.1 x hx`. Introduce `y hy y' hy'`. Take `⟨x, hx, rfl⟩` from `AddSubgroup.mem_map.1 hy`. Take `⟨x', hx', rfl⟩` from `AddSubgroup.mem_map.1 hy'`.

Establish `e1 : (δ : (n → ℂ) →ₗ[ℂ] (n → ℂ)).toAddMonoidHom x = δ x` using `rfl`. Establish `e2 : (δ : (n → ℂ) →ₗ[ℂ] (n → ℂ)).toAddMonoidHom x' = δ x'` using `rfl`. Establish `e3 : altE (matH h) (δ x) (δ x') = altE (matH h) x x'`. Simplify using `only [altE, hisomxy]`. Rewrite using `[e1, e2, ← map_add, hαinv, hαinv, hαinv, e3]`.

Conclude with `hSC.2 x hx x' hx'`. Establish `hπle : cLat π Λ ≤ Λ` using `fun y hy => by`. Take `⟨x, hx, rfl⟩` from `mem_cLat.1 hy`. Conclude with `hπΛ x hx`. Establish `hπble : cLat (conj π) Λ ≤ Λ` using `fun y hy => by`.

Take `⟨x, hx, rfl⟩` from `mem_cLat.1 hy`. Conclude with `hπbΛ x hx`. Establish `hcb : cLat (conj π) Λ = imgLat (δ : (n → ℂ) →ₗ[ℂ] (n → ℂ)) (cLat π Λ)`. Use extensionality with `y`. Rewrite using `[mem_cLat, imgLat, AddSubgroup.mem_map]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨π • x, mem_cLat.2 ⟨x, hx, rfl⟩, by show δ (π • x) = _`. Rewrite using `[hδ, smul_smul, hdπ]⟩`. Introduce and unpack `⟨z, hz, rfl⟩`.

Take `⟨x, hx, rfl⟩` from `mem_cLat.1 hz`. Conclude with `⟨x, hx, by show _ = δ (π • x)`. Rewrite using `[hδ, smul_smul, hdπ]⟩`. Establish `hπbleδ : cLat (conj π) Λ ≤ imgLat (δ : (n → ℂ) →ₗ[ℂ] (n → ℂ)) Λ`. Rewrite using `[hcb]`.

Conclude with `AddSubgroup.map_mono hπle`. Establish `hinter : ∀ y ∈ imgLat (δ : (n → ℂ) →ₗ[ℂ] (n → ℂ)) Λ, y ∈ Λ → y ∈ cLat (conj π) Λ`. Introduce `y hy hyΛ`. Rewrite `hy` using `[hδΛ]`. Take `⟨x, hx, rfl⟩` from `mem_cLat.1 hy`.

Use `mem_cLat.2 ⟨u • x + w • (d • x), Λ.add_mem (huΛ x hx) (hwΛ _ hyΛ), ?_⟩` and prove the remaining obligations. Simplify using `only [smul_smul, ← add_smul]`. Use `congr 1`. Take the linear combination `d * huw - u * hdπ`. Establish `hidxπ : relIdx (cLat π Λ) Λ = p ^ Fintype.card n`.

Establish `h1` using `relIdx_cLat Λ hL π hπ0 hπΛ`. Rewrite `h1` using `[hnsq]`. Conclude with `h1` after adjusting the coercions. Establish `hidxπb : relIdx (cLat (conj π) Λ) Λ = p ^ Fintype.card n`. Establish `h1` using `relIdx_cLat Λ hL (conj π) hπb0 hπbΛ`.

Rewrite `h1` using `[hnsqb]`. Conclude with `h1` after adjusting the coercions. Establish `hmapidx : relIdx (cLat (conj π) Λ) (imgLat (δ : (n → ℂ) →ₗ[ℂ] (n → ℂ)) Λ) = p ^ Fintype.card n`. Rewrite using `[hcb, ← hidxπ]`. Unfold `relIdx imgLat`.

Conclude with `AddSubgroup.relIndex_map_map_of_injective _ _ (fun a b hab => δ.injective hab)`. Establish `hpn0 : p ^ Fintype.card n ≠ 0` using `pow_ne_zero _ hp.ne_zero`. Establish `hidx1 : relIdx (imgLat (δ : (n → ℂ) →ₗ[ℂ] (n → ℂ)) Λ) Λ ≠ 0` using `relIdx_ne_of_le hπbleδ (by rw [hidxπb]; exact hpn0)`. Establish `hidx2 : relIdx Λ (imgLat (δ : (n → ℂ) →ₗ[ℂ] (n → ℂ)) Λ) ≠ 0` using `relIdx_ne_of_le hπble (by rw [hmapidx]; exact hpn0)`. Establish `hcay : ∀ x, Ae x = x - δ.symm x`.

Introduce `x`. Rewrite using `[hδs, hd, inv_div]`. Use `show (1 - π / conj π) • x = _`. Rewrite using `[sub_smul, one_smul]`. Establish `hU : UnitaryData (matH h) Λ α δ Ae` using `{ herm := hH, pos := hP, selfDual := hSD, semi := hSC, isom := hisom, semi' := hsemi', inv := fun x _ => hαinv x, idx₁ := hidx1, idx₂ := hidx2, cay := hcay }`.

Establish `hReps : IsReps Λ (imgLat (δ : (n → ℂ) →ₗ[ℂ] (n → ℂ)) Λ) Sa`. Use `⟨fun x hx => by rw [hδΛ]; exact hSa.1 x hx, fun x hx y hy hxy => hSa.2.1 x hx y hy ?_, fun y hy => ?_⟩` and prove the remaining obligations. Use `hinter _ ?_ hxy` and prove the remaining obligations. Rewrite using `[hδΛ]`. Conclude with `(cLat d Λ).sub_mem (hSa.1 x hx) (hSa.1 y hy)`.

Rewrite `hy` using `[hδΛ]`. Take `⟨x, hx, hyx⟩` from `hSa.2.2 y hy`. Conclude with `⟨x, hx, hπble hyx⟩`. Establish `hcard : Sa.card = p ^ Fintype.card n`. Establish `h2 : relIdx (cLat (conj π) Λ) (cLat d Λ) = p ^ Fintype.card n`.

Rewrite using `[← hδΛ, hmapidx]`. Rewrite using `[(repsExist (n → ℂ) _ _ (by rw [h2]; exact hpn0)).2 Sa hSa, h2]`. Establish `hrel : relIdx Λ (imgLat (δ : (n → ℂ) →ₗ[ℂ] (n → ℂ)) Λ) = p ^ Fintype.card n`. Rewrite using `[← (repsExist (n → ℂ) _ _ hidx2).2 Sa hReps, hcard]`. Take `⟨c, hc⟩` from `UC.exists_const hL hU hLine`.

Establish `hcθ` using `hc θ hθ`. Establish `hc8` using `unitaryEighth (n → ℂ) (matH h) Λ α δ Ae hL hU hLine θ hθ hθ0 c hcθ`. Use `⟨hcard, c, ?_, fun z => ?_⟩` and prove the remaining obligations. Rewrite using `[hc8, hδlin, LinearMap.det_smul, LinearMap.det_id, mul_one, Module.finrank_fintype_fun_eq_card]`. Expand and normalize the polynomial expressions, which then agree.

Establish `e1 : θ ((π / conj π) • z) = pullInv δ θ z` using `by show _ = θ (δ.symm z)`. Rewrite using `[hδs, hd, inv_div]`. Rewrite using `[e1, hcθ, Pi.smul_apply, smul_eq_mul, interReps (n → ℂ) (matH h) hH Λ _ α hsemi' θ hθ.2 Sa hReps z, hrel, sumU, Nat.cast_pow, mul_assoc]`.
-/
theorem scalar_constant_value : ScalarConst := by
  intro dK n _ _ h Λ hH hP hL hSD hSC hLine p hp π hππ hne hπΛ hπbΛ huw' Sa hSa θ hθ hθ0
  obtain ⟨u, w, huΛ, hwΛ, huw⟩ := huw'
  set α := alphaQ (Real.sqrt dK / 2) (matH h) with hα
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hπ0 : π ≠ 0 := fun h0 => hp0 (by rw [← hππ, h0, zero_mul])
  have hπb0 : conj π ≠ 0 := fun h0 => hp0 (by rw [← hππ, h0, mul_zero])
  have hnsq : Complex.normSq π = p := by
    have := Complex.mul_conj π
    exact_mod_cast this.symm.trans hππ
  have hnsqb : Complex.normSq (conj π) = p := by rw [Complex.normSq_conj, hnsq]
  set d := conj π / π with hd
  have hd0 : d ≠ 0 := div_ne_zero hπb0 hπ0
  have hdπ : d * π = conj π := div_mul_cancel₀ _ hπ0
  have hdd : d * conj d = 1 := by
    rw [hd, map_div₀, Complex.conj_conj, div_mul_div_comm, mul_comm (conj π) π,
      div_self (mul_ne_zero hπ0 hπb0)]
  have he0 : (1 - π / conj π) ≠ 0 := by
    intro h0
    apply hne
    have h1 : π / conj π = 1 := by linear_combination -h0
    exact ((div_eq_one_iff_eq hπb0).1 h1).symm
  let δ : (n → ℂ) ≃ₗ[ℂ] (n → ℂ) := LinearEquiv.smulOfNeZero ℂ (n → ℂ) d hd0
  let Ae : (n → ℂ) ≃ₗ[ℂ] (n → ℂ) := LinearEquiv.smulOfNeZero ℂ (n → ℂ) (1 - π / conj π) he0
  have hδ : ∀ x, δ x = d • x := fun x => rfl
  have hδs : ∀ x, δ.symm x = d⁻¹ • x := fun x => by
    apply δ.injective
    rw [LinearEquiv.apply_symm_apply, hδ, smul_smul, mul_inv_cancel₀ hd0, one_smul]
  have hδlin : (δ : (n → ℂ) →ₗ[ℂ] (n → ℂ)) = d • LinearMap.id := LinearMap.ext fun x => by
    simp [hδ]
  have hδΛ : imgLat (δ : (n → ℂ) →ₗ[ℂ] (n → ℂ)) Λ = cLat d Λ := by rw [cLat, hδlin]
  have hisomxy : ∀ x y, matH h (δ x) (δ y) = matH h x y := by
    intro x y
    simp only [hδ, map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul]
    rw [← mul_assoc, mul_comm (conj d) d, hdd, one_mul]
  have hisom : IsIsom (matH h) (matH h) (δ : (n → ℂ) →ₗ[ℂ] (n → ℂ)) := fun x y => hisomxy x y
  have hαinv : ∀ x, α (δ x) = α x := fun x =>
    alphaQRules.1 (n → ℂ) (n → ℂ) (matH h) (matH h) _ hisom (Real.sqrt dK / 2) x
  have hsemi' : IsSemiChar (matH h) (imgLat (δ : (n → ℂ) →ₗ[ℂ] (n → ℂ)) Λ) α := by
    constructor
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.1 hy
      have e1 : (δ : (n → ℂ) →ₗ[ℂ] (n → ℂ)).toAddMonoidHom x = δ x := rfl
      rw [e1, hαinv]
      exact hSC.1 x hx
    · intro y hy y' hy'
      obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.1 hy
      obtain ⟨x', hx', rfl⟩ := AddSubgroup.mem_map.1 hy'
      have e1 : (δ : (n → ℂ) →ₗ[ℂ] (n → ℂ)).toAddMonoidHom x = δ x := rfl
      have e2 : (δ : (n → ℂ) →ₗ[ℂ] (n → ℂ)).toAddMonoidHom x' = δ x' := rfl
      have e3 : altE (matH h) (δ x) (δ x') = altE (matH h) x x' := by
        simp only [altE, hisomxy]
      rw [e1, e2, ← map_add, hαinv, hαinv, hαinv, e3]
      exact hSC.2 x hx x' hx'

  have hπle : cLat π Λ ≤ Λ := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := mem_cLat.1 hy
    exact hπΛ x hx
  have hπble : cLat (conj π) Λ ≤ Λ := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := mem_cLat.1 hy
    exact hπbΛ x hx
  have hcb : cLat (conj π) Λ = imgLat (δ : (n → ℂ) →ₗ[ℂ] (n → ℂ)) (cLat π Λ) := by
    ext y
    rw [mem_cLat, imgLat, AddSubgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨π • x, mem_cLat.2 ⟨x, hx, rfl⟩, by
        show δ (π • x) = _
        rw [hδ, smul_smul, hdπ]⟩
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨x, hx, rfl⟩ := mem_cLat.1 hz
      exact ⟨x, hx, by
        show _ = δ (π • x)
        rw [hδ, smul_smul, hdπ]⟩
  have hπbleδ : cLat (conj π) Λ ≤ imgLat (δ : (n → ℂ) →ₗ[ℂ] (n → ℂ)) Λ := by
    rw [hcb]
    exact AddSubgroup.map_mono hπle
  have hinter : ∀ y ∈ imgLat (δ : (n → ℂ) →ₗ[ℂ] (n → ℂ)) Λ, y ∈ Λ → y ∈ cLat (conj π) Λ := by
    intro y hy hyΛ
    rw [hδΛ] at hy
    obtain ⟨x, hx, rfl⟩ := mem_cLat.1 hy
    refine mem_cLat.2 ⟨u • x + w • (d • x), Λ.add_mem (huΛ x hx) (hwΛ _ hyΛ), ?_⟩
    simp only [smul_smul, ← add_smul]
    congr 1
    linear_combination d * huw - u * hdπ

  have hidxπ : relIdx (cLat π Λ) Λ = p ^ Fintype.card n := by
    have h1 := relIdx_cLat Λ hL π hπ0 hπΛ
    rw [hnsq] at h1
    exact_mod_cast h1
  have hidxπb : relIdx (cLat (conj π) Λ) Λ = p ^ Fintype.card n := by
    have h1 := relIdx_cLat Λ hL (conj π) hπb0 hπbΛ
    rw [hnsqb] at h1
    exact_mod_cast h1
  have hmapidx : relIdx (cLat (conj π) Λ) (imgLat (δ : (n → ℂ) →ₗ[ℂ] (n → ℂ)) Λ)
      = p ^ Fintype.card n := by
    rw [hcb, ← hidxπ]
    unfold relIdx imgLat
    exact AddSubgroup.relIndex_map_map_of_injective _ _ (fun a b hab => δ.injective hab)
  have hpn0 : p ^ Fintype.card n ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hidx1 : relIdx (imgLat (δ : (n → ℂ) →ₗ[ℂ] (n → ℂ)) Λ) Λ ≠ 0 :=
    relIdx_ne_of_le hπbleδ (by rw [hidxπb]; exact hpn0)
  have hidx2 : relIdx Λ (imgLat (δ : (n → ℂ) →ₗ[ℂ] (n → ℂ)) Λ) ≠ 0 :=
    relIdx_ne_of_le hπble (by rw [hmapidx]; exact hpn0)
  have hcay : ∀ x, Ae x = x - δ.symm x := by
    intro x
    rw [hδs, hd, inv_div]
    show (1 - π / conj π) • x = _
    rw [sub_smul, one_smul]
  have hU : UnitaryData (matH h) Λ α δ Ae :=
    { herm := hH, pos := hP, selfDual := hSD, semi := hSC, isom := hisom, semi' := hsemi',
      inv := fun x _ => hαinv x, idx₁ := hidx1, idx₂ := hidx2, cay := hcay }
  have hReps : IsReps Λ (imgLat (δ : (n → ℂ) →ₗ[ℂ] (n → ℂ)) Λ) Sa := by
    refine ⟨fun x hx => by rw [hδΛ]; exact hSa.1 x hx, fun x hx y hy hxy => hSa.2.1 x hx y hy ?_,
      fun y hy => ?_⟩
    · refine hinter _ ?_ hxy
      rw [hδΛ]
      exact (cLat d Λ).sub_mem (hSa.1 x hx) (hSa.1 y hy)
    · rw [hδΛ] at hy
      obtain ⟨x, hx, hyx⟩ := hSa.2.2 y hy
      exact ⟨x, hx, hπble hyx⟩
  have hcard : Sa.card = p ^ Fintype.card n := by
    have h2 : relIdx (cLat (conj π) Λ) (cLat d Λ) = p ^ Fintype.card n := by
      rw [← hδΛ, hmapidx]
    rw [(repsExist (n → ℂ) _ _ (by rw [h2]; exact hpn0)).2 Sa hSa, h2]
  have hrel : relIdx Λ (imgLat (δ : (n → ℂ) →ₗ[ℂ] (n → ℂ)) Λ) = p ^ Fintype.card n := by
    rw [← (repsExist (n → ℂ) _ _ hidx2).2 Sa hReps, hcard]
  obtain ⟨c, hc⟩ := UC.exists_const hL hU hLine
  have hcθ := hc θ hθ
  have hc8 := unitaryEighth (n → ℂ) (matH h) Λ α δ Ae hL hU hLine θ hθ hθ0 c hcθ
  refine ⟨hcard, c, ?_, fun z => ?_⟩
  · rw [hc8, hδlin, LinearMap.det_smul, LinearMap.det_id, mul_one, Module.finrank_fintype_fun_eq_card]
    ring
  · have e1 : θ ((π / conj π) • z) = pullInv δ θ z := by
      show _ = θ (δ.symm z)
      rw [hδs, hd, inv_div]
    rw [e1, hcθ, Pi.smul_apply, smul_eq_mul,
      interReps (n → ℂ) (matH h) hH Λ _ α hsemi' θ hθ.2 Sa hReps z, hrel, sumU, Nat.cast_pow, mul_assoc]

end Formalism.L2.AlgTh
