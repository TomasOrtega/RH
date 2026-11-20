import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.PnormInvStatement

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix
open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities.
-/
theorem det_of_blockDiag {m α : Type} [Fintype m] [DecidableEq m] [LinearOrder α] (M : Matrix m m ℂ)
    (bk : m → α) (hM : M.BlockTriangular bk) (dg : m → ℂ)
    (hd : ∀ i j, bk i = bk j → M i j = if i = j then dg i else 0) : M.det = ∏ i, dg i := by
  classical
  rw [hM.det]
  have hb : ∀ k, M.toSquareBlock bk k = Matrix.diagonal (fun i : {i // bk i = k} => dg i) := by
    intro k
    ext i j
    simp only [Matrix.toSquareBlock_def, Matrix.of_apply]
    rw [hd i j (i.2.trans j.2.symm), Matrix.diagonal_apply]
    simp [Subtype.ext_iff]
  simp only [hb, Matrix.det_diagonal]
  rw [← Finset.prod_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image bk) (g := bk)
    (fun x _ => Finset.mem_image_of_mem bk (Finset.mem_univ x)) dg]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← Finset.prod_subtype (Finset.univ.filter fun i => bk i = k) (p := fun i => bk i = k)
    (fun i => by simp)]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Substitute using the available equality. Both sides reduce to the same expression.
-/
theorem ent_eq_iff (e e' : Ent X) :
    e = e' ↔ e.1 = e'.1 ∧ e.2.1.1 = e'.2.1.1 ∧ e.2.1.2 = e'.2.1.2 := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl, rfl⟩
  · obtain ⟨τ, ⟨⟨a, c⟩, h⟩⟩ := e
    obtain ⟨τ', ⟨⟨a', c'⟩, h'⟩⟩ := e'
    rintro ⟨h1, h2, h3⟩
    simp only at h1 h2 h3
    subst h1 h2 h3
    rfl

def embF (v : Ent X → ℂ) (τ : X.Ψ) (x c : Fin r) : ℂ := if h : c < x then v ⟨τ, ⟨(x, c), h⟩⟩ else 0

/- English proof (translation)
Replace the relevant objects with their definitions. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem embF_single (e' : Ent X) (τ : X.Ψ) (x c : Fin r) :
    embF X (Pi.single e' 1) τ x c = if τ = e'.1 ∧ x = e'.2.1.1 ∧ c = e'.2.1.2 then 1 else 0 := by
  unfold embF
  by_cases h1 : c < x
  · rw [dif_pos h1, Pi.single_apply]
    by_cases h2 : τ = e'.1 ∧ x = e'.2.1.1 ∧ c = e'.2.1.2
    · rw [if_pos h2, if_pos ((ent_eq_iff X _ _).2 h2)]
    · rw [if_neg h2, if_neg (fun h => h2 ((ent_eq_iff X _ _).1 h))]
  · rw [dif_neg h1, if_neg]
    rintro ⟨rfl, rfl, rfl⟩
    exact h1 e'.2.2

def lmulL (N : Frame X.Ψ r) : (Ent X → ℂ) →ₗ[ℂ] (Ent X → ℂ) where
  toFun v e := ∑ x, N e.1 e.2.1.1 x * embF X v e.1 x e.2.1.2
  map_add' v w := by
    funext e
    simp only [Pi.add_apply, embF]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> ring
  map_smul' a v := by
    funext e
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, embF, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> ring

def rmulL (b : Frame X.Ψ r) : (Ent X → ℂ) →ₗ[ℂ] (Ent X → ℂ) where
  toFun v e := ∑ y, embF X v e.1 e.2.1.1 y * b e.1 y e.2.1.2
  map_add' v w := by
    funext e
    simp only [Pi.add_apply, embF]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> ring
  map_smul' a v := by
    funext e
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, embF, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. A detailed English derivation is pending.
-/
theorem lmulL_entry (N : Frame X.Ψ r) (e e' : Ent X) :
    LinearMap.toMatrix (Pi.basisFun ℂ (Ent X)) (Pi.basisFun ℂ (Ent X)) (lmulL X N) e e' =
      if e.1 = e'.1 ∧ e.2.1.2 = e'.2.1.2 then N e.1 e.2.1.1 e'.2.1.1 else 0 := by
  classical
  rw [LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr]
  show ∑ x, N e.1 e.2.1.1 x * embF X (Pi.single e' 1) e.1 x e.2.1.2 = _
  simp only [embF_single, mul_ite, mul_one, mul_zero]
  split_ifs with h
  · rw [Finset.sum_eq_single e'.2.1.1]
    · rw [if_pos ⟨h.1, rfl, h.2⟩]
    · intro x _ hx
      rw [if_neg]
      exact fun h' => hx h'.2.1
    · simp
  · refine Finset.sum_eq_zero fun x _ => ?_
    rw [if_neg]
    exact fun h' => h ⟨h'.1, h'.2.2⟩

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. A detailed English derivation is pending.
-/
theorem rmulL_entry (b : Frame X.Ψ r) (e e' : Ent X) :
    LinearMap.toMatrix (Pi.basisFun ℂ (Ent X)) (Pi.basisFun ℂ (Ent X)) (rmulL X b) e e' =
      if e.1 = e'.1 ∧ e.2.1.1 = e'.2.1.1 then b e.1 e'.2.1.2 e.2.1.2 else 0 := by
  classical
  rw [LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr]
  show ∑ y, embF X (Pi.single e' 1) e.1 e.2.1.1 y * b e.1 y e.2.1.2 = _
  simp only [embF_single, ite_mul, one_mul, zero_mul]
  split_ifs with h
  · rw [Finset.sum_eq_single e'.2.1.2]
    · rw [if_pos ⟨h.1, h.2, rfl⟩]
    · intro y _ hy
      rw [if_neg]
      exact fun h' => hy h'.2.2
    · simp
  · refine Finset.sum_eq_zero fun y _ => ?_
    rw [if_neg]
    exact fun h' => h ⟨h'.1, h'.2.1⟩

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem det_lmulL_unit (N : Frame X.Ψ r) (hlow : ∀ τ a x, a < x → N τ a x = 0) (hdiag : ∀ τ a, N τ a a = 1) :
    LinearMap.det (lmulL X N) = 1 := by
  classical
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℂ (Ent X))]
  rw [det_of_blockDiag _ (fun e : Ent X => OrderDual.toDual e.2.1.1) (fun e e' hlt => by
      rw [lmulL_entry]
      split_ifs with h
      · exact hlow _ _ _ (by simpa using hlt)
      · rfl) (fun _ => 1) (fun e e' hk => by
      rw [lmulL_entry]
      have hk' : e.2.1.1 = e'.2.1.1 := by simpa using hk
      by_cases h : e = e'
      · subst h; simp [hdiag]
      · rw [if_neg h, if_neg]
        intro h2
        exact h ((ent_eq_iff X e e').2 ⟨h2.1, hk', h2.2⟩))]
  simp

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem det_lmulL_upper (b : Frame X.Ψ r) (hup : ∀ τ a x, x < a → b τ a x = 0) :
    LinearMap.det (lmulL X b) = ∏ e : Ent X, b e.1 e.2.1.1 e.2.1.1 := by
  classical
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℂ (Ent X))]
  exact det_of_blockDiag _ (fun e : Ent X => e.2.1.1) (fun e e' hlt => by
      rw [lmulL_entry]
      split_ifs with h
      · exact hup _ _ _ hlt
      · rfl) _ (fun e e' hk => by
      rw [lmulL_entry]
      by_cases h : e = e'
      · subst h; simp
      · rw [if_neg h, if_neg]
        intro h2
        exact h ((ent_eq_iff X e e').2 ⟨h2.1, hk, h2.2⟩))

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem det_rmulL_upper (b : Frame X.Ψ r) (hup : ∀ τ a x, x < a → b τ a x = 0) :
    LinearMap.det (rmulL X b) = ∏ e : Ent X, b e.1 e.2.1.2 e.2.1.2 := by
  classical
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℂ (Ent X))]
  exact det_of_blockDiag _ (fun e : Ent X => OrderDual.toDual e.2.1.2) (fun e e' hlt => by
      rw [rmulL_entry]
      split_ifs with h
      · exact hup _ _ _ (by simpa using hlt)
      · rfl) _ (fun e e' hk => by
      rw [rmulL_entry]
      have hk' : e.2.1.2 = e'.2.1.2 := by simpa using hk
      by_cases h : e = e'
      · subst h; simp
      · rw [if_neg h, if_neg]
        intro h2
        exact h ((ent_eq_iff X e e').2 ⟨h2.1, h2.2, hk'⟩))

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify by unfolding definitions. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem prod_low_row (g : Fin r → ℂ) :
    ∏ p : {p : Fin r × Fin r // p.2 < p.1}, g p.1.1 = ∏ a, g a ^ (a : ℕ) := by
  rw [← Finset.prod_subtype (Finset.univ.filter fun p : Fin r × Fin r => p.2 < p.1) (fun p => by simp)
    (fun p : Fin r × Fin r => g p.1), Finset.prod_filter, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_filter]
  dsimp only
  rw [Finset.prod_const]
  congr 1
  rw [← Fin.card_Iio a]
  congr 1
  ext c
  simp

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify by unfolding definitions. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem prod_low_col (g : Fin r → ℂ) :
    ∏ p : {p : Fin r × Fin r // p.2 < p.1}, g p.1.2 = ∏ c, g c ^ (r - 1 - (c : ℕ)) := by
  rw [← Finset.prod_subtype (Finset.univ.filter fun p : Fin r × Fin r => p.2 < p.1) (fun p => by simp)
    (fun p : Fin r × Fin r => g p.2), Finset.prod_filter, Fintype.prod_prod_type, Finset.prod_comm]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [← Finset.prod_filter]
  dsimp only
  rw [Finset.prod_const]
  congr 1
  rw [← Fin.card_Ioi c]
  congr 1
  ext a
  simp

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. A detailed English derivation is pending.
-/
theorem bchar_kap (b : Frame X.Ψ r) (hd : ∀ τ a, b τ a a ≠ 0) :
    bchar (kapW X) b = (∏ e : Ent X, b e.1 e.2.1.1 e.2.1.1) / ∏ e : Ent X, b e.1 e.2.1.2 e.2.1.2 := by
  rw [Fintype.prod_prod_type, Fintype.prod_prod_type, ← Finset.prod_div_distrib]
  unfold bchar
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [prod_low_row (fun a => b τ a a), prod_low_col (fun c => b τ c c), ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  have ha : (a : ℕ) ≤ r - 1 := by omega
  rw [kapW, show (2 * ((a : ℕ) : ℤ) - ((r : ℤ) - 1)) = ((a : ℕ) : ℤ) - ((r - 1 - (a : ℕ) : ℕ) : ℤ) by
    push_cast [Nat.sub_sub, Nat.cast_sub (by omega : 1 + (a : ℕ) ≤ r)]; ring,
    zpow_sub₀ (hd τ a), zpow_natCast, zpow_natCast]

end ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf
