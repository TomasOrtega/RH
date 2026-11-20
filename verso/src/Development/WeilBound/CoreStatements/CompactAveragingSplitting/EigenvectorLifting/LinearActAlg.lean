import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.LagrangianStabilizerCharacterTrivial

noncomputable section

open Matrix GlobalTheory.WeilM

namespace PositivityTheory.ThK.LinAct

set_option linter.unusedSectionVars false

variable {k : Type} [Field k] [Invertible (2 : k)] {K : Type} [CommRing K] [Algebra k K] {c : K →ₐ[k] K}
  {α β ν κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν] [Fintype κ]

omit [Invertible (2 : k)] [DecidableEq α] [DecidableEq β] in
/- English proof (translation)
Unfold `hTens`. Use `conv_lhs => rw [Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `conv_lhs => rw [Finset.sum_comm]`. Use `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations.

Simplify using `only [transpose_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hTens_transpose (JA : Matrix α α K) (JB : Matrix β β K) (x y : Matrix β α K) :
    hTens c JB JA x y = hTens c JA JB xᵀ yᵀ := by
  unfold hTens
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  simp only [transpose_apply]
  ring

def lagY {ξ : K} {JA : Matrix α α K} {JB : Matrix β β K} (d : Darboux (symp (R := k) c ξ JB JA) κ) (Cy : Matrix β ν K) :
    Submodule k ((κ → k) × (κ → k)) :=
  LinearMap.range (d.e.toLinearMap ∘ₗ
    ({ toFun := fun z => Cy * z, map_add' := Matrix.mul_add _, map_smul' := fun r z => Matrix.mul_smul _ r z } :
      Matrix ν α K →ₗ[k] Matrix β α K))

omit [DecidableEq α] [DecidableEq β] [DecidableEq ν] in
/- English proof (translation)
Simplify using `[lagY, LinearMap.mem_range]`.
-/
theorem mem_lagY {ξ : K} {JA : Matrix α α K} {JB : Matrix β β K} {d : Darboux (symp (R := k) c ξ JB JA) κ} {Cy : Matrix β ν K}
    {w : (κ → k) × (κ → k)} : w ∈ lagY d Cy ↔ ∃ z : Matrix ν α K, d.e (Cy * z) = w := by
  simp [lagY, LinearMap.mem_range]

omit [DecidableEq α] [DecidableEq β] [DecidableEq ν] in
/- English proof (translation)
Introduce `w hw w' hw'`. Take `⟨z, rfl⟩` from `mem_lagY.1 hw`. Take `⟨z', rfl⟩` from `mem_lagY.1 hw'`. Establish `h0` using `d.form (Cy * z) (Cy * z')`. Establish `hs : symp (R` using `k) c ξ JB JA (Cy * z) (Cy * z') = 0 := by`.

Unfold `symp`. Rewrite using `[hTens_transpose, transpose_mul, transpose_mul, GlobalTheory.CompanionTheory.SplitUnique.hTens_eq_zero c JA h zᵀ z'ᵀ, mul_zero, map_zero]`. Rewrite `h0` using `[hs]`. Conclude with `sub_eq_zero.1 h0.symm`.
-/
theorem lagY_iso {ξ : K} {JA : Matrix α α K} {JB : Matrix β β K} (d : Darboux (symp (R := k) c ξ JB JA) κ) {Cy : Matrix β ν K}
    (h : Cyᵀ * JB * Cy.map c = 0) : ∀ w ∈ lagY d Cy, ∀ w' ∈ lagY d Cy, w.1 ⬝ᵥ w'.2 = w'.1 ⬝ᵥ w.2 := by
  intro w hw w' hw'
  obtain ⟨z, rfl⟩ := mem_lagY.1 hw
  obtain ⟨z', rfl⟩ := mem_lagY.1 hw'
  have h0 := d.form (Cy * z) (Cy * z')
  have hs : symp (R := k) c ξ JB JA (Cy * z) (Cy * z') = 0 := by
    unfold symp
    rw [hTens_transpose, transpose_mul, transpose_mul,
      GlobalTheory.CompanionTheory.SplitUnique.hTens_eq_zero c JA h zᵀ z'ᵀ, mul_zero, map_zero]
  rw [hs] at h0
  exact sub_eq_zero.1 h0.symm

omit [Invertible (2 : k)] in
/- English proof (translation)
Take `⟨-, Cx, M, -, h1, h2⟩` from `h`. Set `f : (β → K) ≃ₗ[K] (ν ⊕ ν → K)` to `LinearEquiv.ofLinearMap (Matrix.toLin' M) (Matrix.toLin' (fromCols Cy Cx)) (by rw [← Matrix.toLin'_mul, h2, Matrix.toLin'_one]) (by rw [← Matrix.toLin'_mul, h1, Matrix.toLin'_one])`. Rewrite using `[card_eq_of_linearEquiv K f, Fintype.card_sum, two_mul]`.
-/
theorem card_lagr [Nontrivial K] {JB : Matrix β β K} {Cy : Matrix β ν K} (h : IsLagr c JB Cy) :
    Fintype.card β = 2 * Fintype.card ν := by
  obtain ⟨-, Cx, M, -, h1, h2⟩ := h
  let f : (β → K) ≃ₗ[K] (ν ⊕ ν → K) :=
    LinearEquiv.ofLinearMap (Matrix.toLin' M) (Matrix.toLin' (fromCols Cy Cx))
      (by rw [← Matrix.toLin'_mul, h2, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, h1, Matrix.toLin'_one])
  rw [card_eq_of_linearEquiv K f, Fintype.card_sum, two_mul]

omit [Invertible (2 : k)] [Fintype α] [DecidableEq α] in

/- English proof (translation)
Establish `hrows : fromRows z z' = 0`. Combine the equalities or inequalities in the displayed calculation. Establish `e1` using `congrArg Matrix.toRows₁ hrows`. Establish `e2` using `congrArg Matrix.toRows₂ hrows`. Simplify using `only [toRows₁_fromRows, toRows₂_fromRows] at e1 e2`.

Apply the tactic sequence `refine ⟨e1.trans ?_, e2.trans ?_⟩ <;> rfl`.
-/
theorem indep {Cy Cx : Matrix β ν K} {M : Matrix (ν ⊕ ν) β K} (h2 : M * fromCols Cy Cx = 1) {z z' : Matrix ν α K}
    (h : Cy * z + Cx * z' = 0) : z = 0 ∧ z' = 0 := by
  have hrows : fromRows z z' = 0 := by
    calc fromRows z z' = (M * fromCols Cy Cx) * fromRows z z' := by rw [h2, Matrix.one_mul]
      _ = M * (Cy * z + Cx * z') := by rw [Matrix.mul_assoc, fromCols_mul_fromRows]
      _ = 0 := by rw [h, Matrix.mul_zero]
  have e1 := congrArg Matrix.toRows₁ hrows
  have e2 := congrArg Matrix.toRows₂ hrows
  simp only [toRows₁_fromRows, toRows₂_fromRows] at e1 e2
  refine ⟨e1.trans ?_, e2.trans ?_⟩ <;> rfl

omit [DecidableEq α] in
/- English proof (translation)
Take `⟨b, -, -⟩` from `hq.basis`. Establish `: Module.Free k K` using `Module.Free.of_basis b`. Establish `: Module.Finite k K` using `Module.Finite.of_basis b`. Establish `hK : Module.finrank k K = 2` using `by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]`. Establish `hcard` using `card_lagr h`.

Take `⟨-, Cx, M, -, -, hM⟩` from `h`. Establish `hd` using `d.e.finrank_eq`. Rewrite `hd` using `[Module.finrank_matrix, Module.finrank_prod, Module.finrank_fintype_fun_eq_card, hK, hcard]`. Unfold `lagY`. Rewrite using `[LinearMap.finrank_range_of_inj, Module.finrank_matrix, hK]`.

Combine the linear equalities and inequalities to obtain the conclusion. Introduce `z z' hz`. Establish `hz' : Cy * z = Cy * z'` using `d.e.injective hz`. Establish `h3 : Cy * (z - z') + Cx * (0 : Matrix ν α K) = 0`. Rewrite using `[Matrix.mul_sub, hz', sub_self, Matrix.mul_zero, add_zero]`.

Conclude with `sub_eq_zero.1 (indep hM h3).1`.
-/
theorem lagY_dim [Nontrivial K] {ξ₀ : K} (hq : IsQuad c ξ₀) {ξ : K} {JA : Matrix α α K} {JB : Matrix β β K}
    (d : Darboux (symp (R := k) c ξ JB JA) κ) {Cy : Matrix β ν K} (h : IsLagr c JB Cy) :
    Module.finrank k (lagY d Cy) = Fintype.card κ := by
  obtain ⟨b, -, -⟩ := hq.basis
  have : Module.Free k K := Module.Free.of_basis b
  have : Module.Finite k K := Module.Finite.of_basis b
  have hK : Module.finrank k K = 2 := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hcard := card_lagr h
  obtain ⟨-, Cx, M, -, -, hM⟩ := h
  have hd := d.e.finrank_eq
  rw [Module.finrank_matrix, Module.finrank_prod, Module.finrank_fintype_fun_eq_card, hK, hcard] at hd
  unfold lagY
  rw [LinearMap.finrank_range_of_inj, Module.finrank_matrix, hK]
  · linarith
  · intro z z' hz
    have hz' : Cy * z = Cy * z' := d.e.injective hz
    have h3 : Cy * (z - z') + Cx * (0 : Matrix ν α K) = 0 := by
      rw [Matrix.mul_sub, hz', sub_self, Matrix.mul_zero, add_zero]
    exact sub_eq_zero.1 (indep hM h3).1

omit [Invertible (2 : k)] in

/- English proof (translation)
Take `⟨b, -, -⟩` from `hq.basis`. Establish `: Module.Free k K` using `Module.Free.of_basis b`. Establish `: Module.Finite k K` using `Module.Finite.of_basis b`. Use `⟨Module.finrank k (Matrix ν α K), (Module.finBasis k (Matrix ν α K)).equivFun.symm, fun t => ?_⟩` and prove the remaining obligations. Use `set e := (Module.finBasis k (Matrix ν α K)).equivFun.symm`.

Set `TK : GL α K → Matrix ν α K →ₗ[K] Matrix ν α K` to `fun s => { toFun := fun x => x * (s : Matrix α α K)ᵀ map_add' := fun x y => Matrix.add_mul x y _ map_smul' := fun a x => Matrix.smul_mul a x _ }`. Set `F : GL α K → (Fin (Module.finrank k (Matrix ν α K)) → k) →ₗ[k] (Fin (Module.finrank k (Matrix ν α K)) → k)` to `fun s => (e.symm : Matrix ν α K →ₗ[k] _) ∘ₗ (TK s).restrictScalars k ∘ₗ (e.symm.symm : _ →ₗ[k] Matrix ν α K)`. Establish `hF : ∀ s x, F s x = e.symm (e x * (s : Matrix α α K)ᵀ)` using `fun s x => rfl`. Establish `hinv : ∀ s s' : GL α K, s' * s = 1 → F s' ∘ₗ F s = LinearMap.id`. Introduce `s s' hss`.

Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, hF, hF, LinearEquiv.apply_symm_apply, Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, hss, Units.val_one, Matrix.transpose_one, Matrix.mul_one, LinearEquiv.symm_apply_apply, LinearMap.id_apply]`. Set `g : GL (Fin (Module.finrank k (Matrix ν α K))) k` to `⟨LinearMap.toMatrix' (F t), LinearMap.toMatrix' (F t⁻¹), by rw [← LinearMap.toMatrix'_comp, hinv _ _ (mul_inv_cancel t), LinearMap.toMatrix'_id], by rw [← LinearMap.toMatrix'_comp, hinv _ _ (inv_mul_cancel t), LinearMap.toMatrix'_id]⟩`. Use `⟨g, fun x => ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `e (LinearMap.toMatrix' (F t) *ᵥ x) = _`.

Rewrite using `[LinearMap.toMatrix'_mulVec, hF, LinearEquiv.apply_symm_apply]`. Establish `hpi : (Matrix.ofLinearEquiv K).symm.toLinearMap ∘ₗ TK t ∘ₗ (Matrix.ofLinearEquiv K).symm.symm.toLinearMap = LinearMap.pi (fun i : ν => (Matrix.toLin' (t : Matrix α α K)).comp (LinearMap.proj i))`. Use `LinearMap.ext fun x => funext fun i => funext fun j => ?_` and prove the remaining obligations. Simplify using `[TK, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]`. Establish `hdetK : LinearMap.det (TK t) = Matrix.det (t : Matrix α α K) ^ Fintype.card ν`.

Rewrite using `[← LinearMap.det_conj (TK t) (Matrix.ofLinearEquiv K).symm, hpi, LinearMap.det_pi, Finset.prod_const, Finset.card_univ, LinearMap.det_toLin']`. Use `ext`. Express the relevant statement in the definitionally equal form `Matrix.det (LinearMap.toMatrix' (F t)) = _`. Rewrite using `[LinearMap.det_toMatrix', LinearMap.det_conj, LinearMap.det_restrictScalars, hdetK, map_pow]`. Simplify using the standard rewrite rules.
-/
theorem exists_coord {ξ₀ : K} (hq : IsQuad c ξ₀) (ν α : Type) [Fintype ν] [Fintype α] [DecidableEq α] :
    ∃ (r : ℕ) (e : (Fin r → k) ≃ₗ[k] Matrix ν α K), ∀ t : GL α K, ∃ g : GL (Fin r) k,
      (∀ x, e (g.val *ᵥ x) = e x * t.valᵀ) ∧ GeneralLinearGroup.det g =
        Units.map (Algebra.norm k : K →* k) (GeneralLinearGroup.det t) ^ Fintype.card ν := by
  obtain ⟨b, -, -⟩ := hq.basis
  have : Module.Free k K := Module.Free.of_basis b
  have : Module.Finite k K := Module.Finite.of_basis b
  refine ⟨Module.finrank k (Matrix ν α K), (Module.finBasis k (Matrix ν α K)).equivFun.symm, fun t => ?_⟩
  set e := (Module.finBasis k (Matrix ν α K)).equivFun.symm
  let TK : GL α K → Matrix ν α K →ₗ[K] Matrix ν α K := fun s =>
    { toFun := fun x => x * (s : Matrix α α K)ᵀ
      map_add' := fun x y => Matrix.add_mul x y _
      map_smul' := fun a x => Matrix.smul_mul a x _ }
  let F : GL α K → (Fin (Module.finrank k (Matrix ν α K)) → k) →ₗ[k]
      (Fin (Module.finrank k (Matrix ν α K)) → k) := fun s =>
    (e.symm : Matrix ν α K →ₗ[k] _) ∘ₗ (TK s).restrictScalars k ∘ₗ (e.symm.symm : _ →ₗ[k] Matrix ν α K)
  have hF : ∀ s x, F s x = e.symm (e x * (s : Matrix α α K)ᵀ) := fun s x => rfl
  have hinv : ∀ s s' : GL α K, s' * s = 1 → F s' ∘ₗ F s = LinearMap.id := by
    intro s s' hss
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, hF, hF, LinearEquiv.apply_symm_apply, Matrix.mul_assoc,
      ← Matrix.transpose_mul, ← Units.val_mul, hss, Units.val_one, Matrix.transpose_one, Matrix.mul_one,
      LinearEquiv.symm_apply_apply, LinearMap.id_apply]
  let g : GL (Fin (Module.finrank k (Matrix ν α K))) k :=
    ⟨LinearMap.toMatrix' (F t), LinearMap.toMatrix' (F t⁻¹),
      by rw [← LinearMap.toMatrix'_comp, hinv _ _ (mul_inv_cancel t), LinearMap.toMatrix'_id],
      by rw [← LinearMap.toMatrix'_comp, hinv _ _ (inv_mul_cancel t), LinearMap.toMatrix'_id]⟩
  refine ⟨g, fun x => ?_, ?_⟩
  · change e (LinearMap.toMatrix' (F t) *ᵥ x) = _
    rw [LinearMap.toMatrix'_mulVec, hF, LinearEquiv.apply_symm_apply]
  · have hpi : (Matrix.ofLinearEquiv K).symm.toLinearMap ∘ₗ TK t ∘ₗ
        (Matrix.ofLinearEquiv K).symm.symm.toLinearMap =
        LinearMap.pi (fun i : ν => (Matrix.toLin' (t : Matrix α α K)).comp (LinearMap.proj i)) := by
      refine LinearMap.ext fun x => funext fun i => funext fun j => ?_
      simp [TK, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
    have hdetK : LinearMap.det (TK t) = Matrix.det (t : Matrix α α K) ^ Fintype.card ν := by
      rw [← LinearMap.det_conj (TK t) (Matrix.ofLinearEquiv K).symm, hpi, LinearMap.det_pi,
        Finset.prod_const, Finset.card_univ, LinearMap.det_toLin']
    ext
    change Matrix.det (LinearMap.toMatrix' (F t)) = _
    rw [LinearMap.det_toMatrix', LinearMap.det_conj, LinearMap.det_restrictScalars, hdetK, map_pow]
    simp

omit [DecidableEq α] [DecidableEq β] in

/- English proof (translation)
Use function extensionality and compare the values at `x`. Establish `hd : ∀ u v : κ ⊕ κ' → k, u ⬝ᵥ v = (u ∘ Sum.inl) ⬝ᵥ (v ∘ Sum.inl) + (u ∘ Sum.inr) ⬝ᵥ (v ∘ Sum.inr)` using `fun u v => by`. Simplify using `[dotProduct, Fintype.sum_sum_type]`. Establish `e1 : (x + w.1) ∘ Sum.inl = x ∘ Sum.inl + w.1 ∘ Sum.inl` using `rfl`. Establish `e2 : (x + w.1) ∘ Sum.inr = x ∘ Sum.inr + w.1 ∘ Sum.inr` using `rfl`.

Simplify using `only [schr, boxFun]`. Rewrite using `[e1, e2, hd x w.2, hd w.1 w.2]`. Establish `e3 : (x ∘ Sum.inl) ⬝ᵥ (w.2 ∘ Sum.inl) + (x ∘ Sum.inr) ⬝ᵥ (w.2 ∘ Sum.inr) + ⅟(2 : k) * ((w.1 ∘ Sum.inl) ⬝ᵥ (w.2 ∘ Sum.inl) + (w.1 ∘ Sum.inr) ⬝ᵥ (w.2 ∘ Sum.inr)) = ((x ∘ Sum.inl) ⬝ᵥ (w.2 ∘ Sum.inl) + ⅟(2 : k) * ((w.1 ∘ Sum.inl) ⬝ᵥ (w.2 ∘ Sum.inl))) + ((x ∘ Sum.inr) ⬝ᵥ (w.2 ∘ Sum.in …` using `by ring`. Rewrite using `[e3, AddChar.map_add_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem schr_box (ψ : AddChar k ℂ) {κ' : Type} [Fintype κ'] (w : (κ ⊕ κ' → k) × (κ ⊕ κ' → k)) (φ₁ : (κ → k) → ℂ)
    (φ₂ : (κ' → k) → ℂ) : schr ψ w (boxFun φ₁ φ₂) =
      boxFun (schr ψ (w.1 ∘ Sum.inl, w.2 ∘ Sum.inl) φ₁) (schr ψ (w.1 ∘ Sum.inr, w.2 ∘ Sum.inr) φ₂) := by
  funext x
  have hd : ∀ u v : κ ⊕ κ' → k,
      u ⬝ᵥ v = (u ∘ Sum.inl) ⬝ᵥ (v ∘ Sum.inl) + (u ∘ Sum.inr) ⬝ᵥ (v ∘ Sum.inr) := fun u v => by
    simp [dotProduct, Fintype.sum_sum_type]
  have e1 : (x + w.1) ∘ Sum.inl = x ∘ Sum.inl + w.1 ∘ Sum.inl := rfl
  have e2 : (x + w.1) ∘ Sum.inr = x ∘ Sum.inr + w.1 ∘ Sum.inr := rfl
  simp only [schr, boxFun]
  rw [e1, e2, hd x w.2, hd w.1 w.2]
  have e3 : (x ∘ Sum.inl) ⬝ᵥ (w.2 ∘ Sum.inl) + (x ∘ Sum.inr) ⬝ᵥ (w.2 ∘ Sum.inr) +
      ⅟(2 : k) * ((w.1 ∘ Sum.inl) ⬝ᵥ (w.2 ∘ Sum.inl) + (w.1 ∘ Sum.inr) ⬝ᵥ (w.2 ∘ Sum.inr)) =
      ((x ∘ Sum.inl) ⬝ᵥ (w.2 ∘ Sum.inl) + ⅟(2 : k) * ((w.1 ∘ Sum.inl) ⬝ᵥ (w.2 ∘ Sum.inl))) +
      ((x ∘ Sum.inr) ⬝ᵥ (w.2 ∘ Sum.inr) + ⅟(2 : k) * ((w.1 ∘ Sum.inr) ⬝ᵥ (w.2 ∘ Sum.inr))) := by ring
  rw [e3, AddChar.map_add_eq_mul]
  ring

end PositivityTheory.ThK.LinAct
