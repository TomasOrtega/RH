import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensFF

noncomputable section

namespace PI.VolStabS

namespace FiniteFieldSplitting

open Matrix

variable {k : Type} [Field k] [Finite k]

def cols {M a : ℕ} (P : Matrix (Fin M) (Fin a) k) : Fin a → Fin M → k := fun j i ↦ P i j

/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h v hv`. Use function extensionality and compare the values at `j`. Use `h v ?_ j` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Use `congrFun hv i` as an intermediate fact. Simplify using `only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, cols, Pi.zero_apply]`. Rewrite using `[← this]`.

Conclude with `Finset.sum_congr rfl (fun j _ => mul_comm _ _)`. Introduce `h g hg i`. Establish `hPg : P *ᵥ g = 0`. Use function extensionality and compare the values at `r`. Use `congrFun hg r` as an intermediate fact.

Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, cols, Pi.zero_apply] at this`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.zero_apply]`. Rewrite using `[← this]`. Conclude with `Finset.sum_congr rfl (fun j _ => mul_comm _ _)`. Conclude with `congrFun (h g hPg) i`.
-/
theorem linInd_cols_iff {M a : ℕ} (P : Matrix (Fin M) (Fin a) k) :
    LinearIndependent k (cols P) ↔ ∀ v : Fin a → k, P *ᵥ v = 0 → v = 0 := by
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro h v hv
    funext j
    refine h v ?_ j
    funext i
    have := congrFun hv i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, cols, Pi.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  · intro h g hg i
    have hPg : P *ᵥ g = 0 := by
      funext r
      have := congrFun hg r
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, cols, Pi.zero_apply] at this
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [← this]
      exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
    exact congrFun (h g hPg) i

/- English proof (translation)
Establish `hker : LinearMap.ker (Matrix.toLin' P) = ⊥`. Rewrite using `[LinearMap.ker_eq_bot']`. Introduce `v hv`. Rewrite `hv` using `[Matrix.toLin'_apply]`. Conclude with `(linInd_cols_iff P).1 hP v hv`.

Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective (Matrix.toLin' P) hker`. Use `⟨LinearMap.toMatrix' g, ?_⟩` and prove the remaining obligations. Establish `h1` using `congrArg LinearMap.toMatrix' hg`. Rewrite `h1` using `[LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id]`. Then use the resulting hypothesis.
-/
theorem exists_left_inv {M a : ℕ} (P : Matrix (Fin M) (Fin a) k)
    (hP : LinearIndependent k (cols P)) : ∃ L : Matrix (Fin a) (Fin M) k, L * P = 1 := by
  have hker : LinearMap.ker (Matrix.toLin' P) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    rw [Matrix.toLin'_apply] at hv
    exact (linInd_cols_iff P).1 hP v hv
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' P) hker
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have h1 := congrArg LinearMap.toMatrix' hg
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at h1

/- English proof (translation)
Rewrite using `[linInd_cols_iff]`. Introduce `v hv`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem linInd_of_left_inv {M a : ℕ} (W : Matrix (Fin a) (Fin M) k) (P : Matrix (Fin M) (Fin a) k)
    (h : W * P = 1) : LinearIndependent k (cols P) := by
  rw [linInd_cols_iff]
  intro v hv
  calc v = (W * P) *ᵥ v := by rw [h, Matrix.one_mulVec]
    _ = W *ᵥ (P *ᵥ v) := by rw [Matrix.mulVec_mulVec]
    _ = 0 := by rw [hv, Matrix.mulVec_zero]

/- English proof (translation)
Take `⟨L, hL⟩` from `exists_left_inv P hP`. Set `f : Matrix (Fin a) (Fin M) k →ₗ[k] Matrix (Fin a) (Fin a) k` to `{ toFun := fun D => D * P map_add' := fun D E => Matrix.add_mul D E P map_smul' := fun c D => Matrix.smul_mul c D P }`. Establish `hf : ∀ D, f D = D * P` using `fun D => rfl`. Establish `hsurj : LinearMap.range f = ⊤`. Rewrite using `[LinearMap.range_eq_top]`.

Introduce `E`. Conclude with `⟨E * L, by rw [hf, Matrix.mul_assoc, hL, Matrix.mul_one]⟩`. Establish `hrk` using `LinearMap.finrank_range_add_finrank_ker f`. Rewrite `hrk` using `[hsurj, finrank_top]`. Simplify using `only [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one] at hrk`.

Establish `hker : Module.finrank k (LinearMap.ker f) = a * M - a * a` using `by omega`. Establish `e : {W : Matrix (Fin a) (Fin M) k // W * P = 1} ≃ LinearMap.ker f` using `{ toFun := fun W => ⟨W.1 - L, by rw [LinearMap.mem_ker, hf, Matrix.sub_mul, W.2, hL, sub_self]⟩ invFun := fun D => ⟨D.1 + L, by`. Establish `hD` using `D.2`. Rewrite `hD` using `[LinearMap.mem_ker, hf]`. Rewrite using `[Matrix.add_mul, hD, hL, zero_add]⟩`.

Use `left_inv := fun W => by ext1; simp`. Use `right_inv := fun D => by ext1; simp }`. Rewrite using `[Nat.card_congr e, Module.natCard_eq_pow_finrank (K := k), hker, Nat.mul_sub_left_distrib]`.
-/
theorem card_left_inv {M a : ℕ} (P : Matrix (Fin M) (Fin a) k)
    (hP : LinearIndependent k (cols P)) :
    Nat.card {W : Matrix (Fin a) (Fin M) k // W * P = 1} = Nat.card k ^ (a * (M - a)) := by
  classical
  obtain ⟨L, hL⟩ := exists_left_inv P hP
  let f : Matrix (Fin a) (Fin M) k →ₗ[k] Matrix (Fin a) (Fin a) k :=
    { toFun := fun D => D * P
      map_add' := fun D E => Matrix.add_mul D E P
      map_smul' := fun c D => Matrix.smul_mul c D P }
  have hf : ∀ D, f D = D * P := fun D => rfl
  have hsurj : LinearMap.range f = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro E
    exact ⟨E * L, by rw [hf, Matrix.mul_assoc, hL, Matrix.mul_one]⟩
  have hrk := LinearMap.finrank_range_add_finrank_ker f
  rw [hsurj, finrank_top] at hrk
  simp only [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one] at hrk
  have hker : Module.finrank k (LinearMap.ker f) = a * M - a * a := by omega
  have e : {W : Matrix (Fin a) (Fin M) k // W * P = 1} ≃ LinearMap.ker f :=
    { toFun := fun W => ⟨W.1 - L, by rw [LinearMap.mem_ker, hf, Matrix.sub_mul, W.2, hL, sub_self]⟩
      invFun := fun D => ⟨D.1 + L, by
        have hD := D.2
        rw [LinearMap.mem_ker, hf] at hD
        rw [Matrix.add_mul, hD, hL, zero_add]⟩
      left_inv := fun W => by ext1; simp
      right_inv := fun D => by ext1; simp }
  rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := k), hker, Nat.mul_sub_left_distrib]

/- English proof (translation)
Establish `: Fintype k` using `Fintype.ofFinite k`. Set `e : {WP : Matrix (Fin a) (Fin M) k × Matrix (Fin M) (Fin a) k // WP.1 * WP.2 = 1} ≃ Σ P : {P : Matrix (Fin M) (Fin a) k // LinearIndependent k (cols P)}, {W : Matrix (Fin a) (Fin M) k // W * P.1 = 1}` to `{ toFun := fun x ↦ ⟨⟨x.1.2, linInd_of_left_inv x.1.1 x.1.2 x.2⟩, ⟨x.1.1, x.2⟩⟩ invFun := fun y ↦ ⟨(y.2.1, y.1.1), y.2.2⟩ left_inv := fun x ↦ rfl right_inv := fun y ↦ rfl }`. Rewrite using `[Nat.card_congr e, Nat.card_sigma]`. Repeatedly rewrite using `[fun P : {P : Matrix (Fin M) (Fin a) k // LinearIndependent k (cols P)} ↦ card_left_inv P.1 P.2]`. Rewrite using `[Finset.sum_const, Finset.card_univ, smul_eq_mul]`.

Use `congr 1`. Set `e2 : {P : Matrix (Fin M) (Fin a) k // LinearIndependent k (cols P)} ≃ {s : Fin a → Fin M → k // LinearIndependent k s}` to `{ toFun := fun P ↦ ⟨cols P.1, P.2⟩ invFun := fun s ↦ ⟨fun i j ↦ s.1 j i, s.2⟩ left_inv := fun P ↦ rfl right_inv := fun s ↦ rfl }`. Rewrite using `[← Nat.card_eq_fintype_card, Nat.card_congr e2, card_linearIndependent (by rw [Module.finrank_fin_fun]; exact ha), Module.finrank_fin_fun, Nat.card_eq_fintype_card]`.
-/
theorem card_pairs {M a : ℕ} (ha : a ≤ M) :
    Nat.card {WP : Matrix (Fin a) (Fin M) k × Matrix (Fin M) (Fin a) k // WP.1 * WP.2 = 1} =
      (∏ i : Fin a, (Nat.card k ^ M - Nat.card k ^ (i : ℕ))) * Nat.card k ^ (a * (M - a)) := by
  classical
  have : Fintype k := Fintype.ofFinite k
  let e : {WP : Matrix (Fin a) (Fin M) k × Matrix (Fin M) (Fin a) k // WP.1 * WP.2 = 1} ≃
      Σ P : {P : Matrix (Fin M) (Fin a) k // LinearIndependent k (cols P)},
        {W : Matrix (Fin a) (Fin M) k // W * P.1 = 1} :=
    { toFun := fun x ↦ ⟨⟨x.1.2, linInd_of_left_inv x.1.1 x.1.2 x.2⟩, ⟨x.1.1, x.2⟩⟩
      invFun := fun y ↦ ⟨(y.2.1, y.1.1), y.2.2⟩
      left_inv := fun x ↦ rfl
      right_inv := fun y ↦ rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  simp_rw [fun P : {P : Matrix (Fin M) (Fin a) k // LinearIndependent k (cols P)} ↦
    card_left_inv P.1 P.2]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  congr 1
  let e2 : {P : Matrix (Fin M) (Fin a) k // LinearIndependent k (cols P)} ≃
      {s : Fin a → Fin M → k // LinearIndependent k s} :=
    { toFun := fun P ↦ ⟨cols P.1, P.2⟩
      invFun := fun s ↦ ⟨fun i j ↦ s.1 j i, s.2⟩
      left_inv := fun P ↦ rfl
      right_inv := fun s ↦ rfl }
  rw [← Nat.card_eq_fintype_card, Nat.card_congr e2, card_linearIndependent
    (by rw [Module.finrank_fin_fun]; exact ha), Module.finrank_fin_fun, Nat.card_eq_fintype_card]

end FiniteFieldSplitting

namespace FiniteFieldSplitting

open Matrix

variable {k : Type} [Field k] [Finite k] {M a : ℕ}

abbrev swapR (k : Type) [Field k] : k × k →+* k × k := (RingEquiv.prodComm (R := k) (S := k)).toRingHom

def U1 (X : Fin a → Fin M → k × k) : Matrix (Fin a) (Fin M) k := fun r i ↦ (X r i).1

def V1 (X : Fin a → Fin M → k × k) : Matrix (Fin a) (Fin M) k := fun r i ↦ (X r i).2

/- English proof (translation)
Unfold `ffH`. Simplify using `[Prod.fst_sum, swapR]`.
-/
theorem ffH_fst (J : Matrix (Fin M) (Fin M) (k × k)) (x y : Fin M → k × k) :
    (ffH (swapR k) J x y).1 = ∑ i, ∑ j, (x i).2 * (J i j).1 * (y j).1 := by
  unfold ffH
  simp [Prod.fst_sum, swapR]

/- English proof (translation)
Unfold `ffH`. Simplify using `[Prod.snd_sum, swapR]`.
-/
theorem ffH_snd (J : Matrix (Fin M) (Fin M) (k × k)) (x y : Fin M → k × k) :
    (ffH (swapR k) J x y).2 = ∑ i, ∑ j, (x i).1 * (J i j).2 * (y j).2 := by
  unfold ffH
  simp [Prod.snd_sum, swapR]

/- English proof (translation)
Use `first`. Consider the case `rfl`. Consider the case `simp [ffGram]`. Consider the case `(unfold ffGram; simp)`.
-/
private theorem ffGram_apply (J : Matrix (Fin M) (Fin M) (k × k))
    (X : Fin a → Fin M → k × k) (r s : Fin a) :
    ffGram (swapR k) J X r s = ffH (swapR k) J (X r) (X s) := by
  first
  | rfl
  | simp [ffGram]
  | (unfold ffGram; simp)

/- English proof (translation)
Rewrite using `[ffGram_apply, ffH_fst]`. Simplify using `only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, V1, U1, Finset.sum_mul]`. Conclude with `Finset.sum_comm`.
-/
private theorem fst_ffGram_eq_V1_mul_map_fst (J : Matrix (Fin M) (Fin M) (k × k)) (X : Fin a → Fin M → k × k)
    (r s : Fin a) :
    (V1 X * J.map Prod.fst * (U1 X)ᵀ) r s = (ffGram (swapR k) J X r s).1 := by
  rw [ffGram_apply, ffH_fst]
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, V1, U1, Finset.sum_mul]
  exact Finset.sum_comm

/- English proof (translation)
Rewrite using `[ffGram_apply, ffGram_apply, ffH_fst, ffH_snd]`. Use `conv_lhs => rw [Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))` and prove the remaining obligations. Establish `h` using `congrArg Prod.fst (hJ x y)`. Rewrite `h` using `[Prod.fst_swap]`.

Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem snd_ffGram_eq_fst_ffGram_swap (J : Matrix (Fin M) (Fin M) (k × k)) (hJ : ∀ i j, (J j i).swap = J i j)
    (X : Fin a → Fin M → k × k) (r s : Fin a) :
    (ffGram (swapR k) J X r s).2 = (ffGram (swapR k) J X s r).1 := by
  rw [ffGram_apply, ffGram_apply, ffH_fst, ffH_snd]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  have h := congrArg Prod.fst (hJ x y)
  rw [Prod.fst_swap] at h
  rw [h]
  ring

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Use `Matrix.ext fun r s => ?_` and prove the remaining obligations. Rewrite using `[fst_ffGram_eq_V1_mul_map_fst]`. Both sides reduce to the same expression.

Introduce `h`. Establish `hf : ∀ r s, (ffGram (swapR k) J X r s).1 = (T r s).1` using `fun r s => by`. Rewrite using `[← fst_ffGram_eq_V1_mul_map_fst]`. Conclude with `congrFun (congrFun h r) s`. Use `Matrix.ext fun r s => Prod.ext (hf r s) ?_` and prove the remaining obligations.

Rewrite using `[snd_ffGram_eq_fst_ffGram_swap J hJ X, hf s r]`. Establish `h2` using `congrArg Prod.snd (hT r s)`. Rewrite `h2` using `[Prod.snd_swap]`. Conclude with `h2`.
-/
theorem gram_iff (J : Matrix (Fin M) (Fin M) (k × k)) (hJ : ∀ i j, (J j i).swap = J i j)
    (T : Matrix (Fin a) (Fin a) (k × k)) (hT : ∀ i j, (T j i).swap = T i j)
    (X : Fin a → Fin M → k × k) :
    ffGram (swapR k) J X = T ↔
      V1 X * J.map Prod.fst * (U1 X)ᵀ = T.map Prod.fst := by
  constructor
  · rintro rfl
    refine Matrix.ext fun r s => ?_
    rw [fst_ffGram_eq_V1_mul_map_fst]
    rfl
  · intro h
    have hf : ∀ r s, (ffGram (swapR k) J X r s).1 = (T r s).1 := fun r s => by
      rw [← fst_ffGram_eq_V1_mul_map_fst]
      exact congrFun (congrFun h r) s
    refine Matrix.ext fun r s => Prod.ext (hf r s) ?_
    rw [snd_ffGram_eq_fst_ffGram_swap J hJ X, hf s r]
    have h2 := congrArg Prod.snd (hT r s)
    rw [Prod.snd_swap] at h2
    exact h2

/- English proof (translation)
Establish `hJ1 : IsUnit (J.map Prod.fst).det`. Establish `h1` using `(Prod.isUnit_iff.mp hJd).1`. Rewrite `h1` using `[show J.det.1 = (J.map Prod.fst).det from RingHom.map_det (RingHom.fst k k) J]`. Then use the resulting hypothesis. Establish `hT1 : IsUnit (T.map Prod.fst).det`. Establish `h1` using `(Prod.isUnit_iff.mp hTd).1`.

Rewrite `h1` using `[show T.det.1 = (T.map Prod.fst).det from RingHom.map_det (RingHom.fst k k) T]`. Then use the resulting hypothesis. Establish `e : {X : Fin a → Fin M → k × k // ffGram (swapR k) J X = T} ≃ {WP : Matrix (Fin a) (Fin M) k × Matrix (Fin M) (Fin a) k // WP.1 * WP.2 = 1}` using `{ toFun := fun X => ⟨((T.map Prod.fst)⁻¹ * V1 X.1, J.map Prod.fst * (U1 X.1)ᵀ), by`. Establish `h` using `(gram_iff J hJ T hT X.1).1 X.2`. Use `show (T.map Prod.fst)⁻¹ * V1 X.1 * (J.map Prod.fst * (U1 X.1)ᵀ) = 1`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc (V1 X.1), h, Matrix.nonsing_inv_mul _ hT1]⟩`.

Use `invFun := fun WP => ⟨fun r i => ((((J.map Prod.fst)⁻¹ * WP.1.2)ᵀ) r i, (T.map Prod.fst * WP.1.1) r i), by`. Rewrite using `[gram_iff J hJ T hT]`. Establish `hU : U1 (fun r i => ((((J.map Prod.fst)⁻¹ * WP.1.2)ᵀ) r i, (T.map Prod.fst * WP.1.1) r i)) = ((J.map Prod.fst)⁻¹ * WP.1.2)ᵀ` using `rfl`. Establish `hV : V1 (fun r i => ((((J.map Prod.fst)⁻¹ * WP.1.2)ᵀ) r i, (T.map Prod.fst * WP.1.1) r i)) = T.map Prod.fst * WP.1.1` using `rfl`. Rewrite using `[hU, hV, Matrix.transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc (J.map Prod.fst), Matrix.mul_nonsing_inv _ hJ1, Matrix.one_mul, Matrix.mul_assoc, WP.2, Matrix.mul_one]⟩`.

Use `left_inv := fun X => by`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `r i`. Apply `Prod.ext` to reduce the goal to its premises. Use `show (((J.map Prod.fst)⁻¹ * (J.map Prod.fst * (U1 X.1)ᵀ))ᵀ) r i = (X.1 r i).1`.

Rewrite using `[← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJ1, Matrix.one_mul, Matrix.transpose_transpose]`. Both sides reduce to the same expression. Use `show (T.map Prod.fst * ((T.map Prod.fst)⁻¹ * V1 X.1)) r i = (X.1 r i).2`. Rewrite using `[← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hT1, Matrix.one_mul]`. Both sides reduce to the same expression.

Use `right_inv := fun WP => by`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Prod.ext` to reduce the goal to its premises. Use `show (T.map Prod.fst)⁻¹ * (T.map Prod.fst * WP.1.1) = WP.1.1`. Rewrite using `[← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hT1, Matrix.one_mul]`.

Use `show J.map Prod.fst * (((J.map Prod.fst)⁻¹ * WP.1.2)ᵀ)ᵀ = WP.1.2`. Rewrite using `[Matrix.transpose_transpose, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hJ1, Matrix.one_mul] }`. Rewrite using `[Nat.card_congr e, card_pairs ha]`.
-/
theorem fFSplit_nat (M a : ℕ) (ha : a ≤ M)
    (J : Matrix (Fin M) (Fin M) (k × k)) (hJ : ∀ i j, (J j i).swap = J i j) (hJd : IsUnit J.det)
    (T : Matrix (Fin a) (Fin a) (k × k)) (hT : ∀ i j, (T j i).swap = T i j) (hTd : IsUnit T.det) :
    Nat.card {X : Fin a → Fin M → k × k // ffGram (swapR k) J X = T} =
      (∏ i : Fin a, (Nat.card k ^ M - Nat.card k ^ (i : ℕ))) * Nat.card k ^ (a * (M - a)) := by
  classical
  have hJ1 : IsUnit (J.map Prod.fst).det := by
    have h1 := (Prod.isUnit_iff.mp hJd).1
    rwa [show J.det.1 = (J.map Prod.fst).det from RingHom.map_det (RingHom.fst k k) J] at h1
  have hT1 : IsUnit (T.map Prod.fst).det := by
    have h1 := (Prod.isUnit_iff.mp hTd).1
    rwa [show T.det.1 = (T.map Prod.fst).det from RingHom.map_det (RingHom.fst k k) T] at h1
  have e : {X : Fin a → Fin M → k × k // ffGram (swapR k) J X = T} ≃
      {WP : Matrix (Fin a) (Fin M) k × Matrix (Fin M) (Fin a) k // WP.1 * WP.2 = 1} :=
    { toFun := fun X => ⟨((T.map Prod.fst)⁻¹ * V1 X.1, J.map Prod.fst * (U1 X.1)ᵀ), by
        have h := (gram_iff J hJ T hT X.1).1 X.2
        show (T.map Prod.fst)⁻¹ * V1 X.1 * (J.map Prod.fst * (U1 X.1)ᵀ) = 1
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (V1 X.1), h, Matrix.nonsing_inv_mul _ hT1]⟩
      invFun := fun WP => ⟨fun r i => ((((J.map Prod.fst)⁻¹ * WP.1.2)ᵀ) r i,
          (T.map Prod.fst * WP.1.1) r i), by
        rw [gram_iff J hJ T hT]
        have hU : U1 (fun r i => ((((J.map Prod.fst)⁻¹ * WP.1.2)ᵀ) r i,
            (T.map Prod.fst * WP.1.1) r i)) = ((J.map Prod.fst)⁻¹ * WP.1.2)ᵀ := rfl
        have hV : V1 (fun r i => ((((J.map Prod.fst)⁻¹ * WP.1.2)ᵀ) r i,
            (T.map Prod.fst * WP.1.1) r i)) = T.map Prod.fst * WP.1.1 := rfl
        rw [hU, hV, Matrix.transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc (J.map Prod.fst),
          Matrix.mul_nonsing_inv _ hJ1, Matrix.one_mul, Matrix.mul_assoc, WP.2, Matrix.mul_one]⟩
      left_inv := fun X => by
        apply Subtype.ext
        funext r i
        apply Prod.ext
        · show (((J.map Prod.fst)⁻¹ * (J.map Prod.fst * (U1 X.1)ᵀ))ᵀ) r i = (X.1 r i).1
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJ1, Matrix.one_mul,
            Matrix.transpose_transpose]
          rfl
        · show (T.map Prod.fst * ((T.map Prod.fst)⁻¹ * V1 X.1)) r i = (X.1 r i).2
          rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hT1, Matrix.one_mul]
          rfl
      right_inv := fun WP => by
        apply Subtype.ext
        apply Prod.ext
        · show (T.map Prod.fst)⁻¹ * (T.map Prod.fst * WP.1.1) = WP.1.1
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hT1, Matrix.one_mul]
        · show J.map Prod.fst * (((J.map Prod.fst)⁻¹ * WP.1.2)ᵀ)ᵀ = WP.1.2
          rw [Matrix.transpose_transpose, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hJ1,
            Matrix.one_mul] }
  rw [Nat.card_congr e, card_pairs ha]

end FiniteFieldSplitting

/- English proof (translation)
Unfold `FFSplit`. Introduce `k _ _ M a ha J hJ hJd T hT hTd`. Establish `h` using `FiniteFieldSplitting.fFSplit_nat M a ha J hJ hJd T hT hTd`. Simplify using `only [FiniteFieldSplitting.swapR] at h`. Rewrite using `[h, Nat.cast_mul, Nat.cast_prod, Nat.cast_pow]`.

Use `congr 1`. Use `Finset.prod_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Establish `h1 : 1 ≤ Nat.card k` using `Nat.card_pos`. Establish `hi : (i : ℕ) ≤ M` using `by have := i.isLt; omega`. Rewrite using `[Nat.cast_sub (Nat.pow_le_pow_right h1 hi), Nat.cast_pow, Nat.cast_pow]`.
-/
theorem fFSplit_holds : FFSplit := by
  unfold FFSplit
  intro k _ _ M a ha J hJ hJd T hT hTd
  have h := FiniteFieldSplitting.fFSplit_nat M a ha J hJ hJd T hT hTd
  simp only [FiniteFieldSplitting.swapR] at h
  rw [h, Nat.cast_mul, Nat.cast_prod, Nat.cast_pow]
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have h1 : 1 ≤ Nat.card k := Nat.card_pos
  have hi : (i : ℕ) ≤ M := by have := i.isLt; omega
  rw [Nat.cast_sub (Nat.pow_le_pow_right h1 hi), Nat.cast_pow, Nat.cast_pow]

end PI.VolStabS
