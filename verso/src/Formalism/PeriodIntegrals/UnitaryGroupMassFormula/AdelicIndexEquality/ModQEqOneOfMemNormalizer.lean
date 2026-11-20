import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.Commensurated

noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

section Delta

variable {G : Type} [Group G]

def idxRatio (A B : Subgroup G) : ℚ := (B.relIndex A : ℚ) / (A.relIndex B : ℚ)

/- English proof (translation)
Establish `h1 : D.relIndex (A ⊓ B) * (A ⊓ B).relIndex A = D.relIndex A` using `Subgroup.relIndex_mul_relIndex (hHK := le_inf hDA hDB) (hKL := inf_le_left)`. Establish `h2 : D.relIndex (A ⊓ B) * (A ⊓ B).relIndex B = D.relIndex B` using `Subgroup.relIndex_mul_relIndex (hHK := le_inf hDA hDB) (hKL := inf_le_right)`. Rewrite `h1` using `[Subgroup.inf_relIndex_left]`. Rewrite `h2` using `[Subgroup.inf_relIndex_right]`. Establish `hc0 : D.relIndex (A ⊓ B) ≠ 0`.

Introduce `h0`. Apply `hA` to reduce the goal to its premises. Rewrite using `[← h1, h0, zero_mul]`. Establish `hc : (D.relIndex (A ⊓ B) : ℚ) ≠ 0` using `Nat.cast_ne_zero.mpr hc0`. Unfold `idxRatio`.

Rewrite using `[← h1, ← h2, Nat.cast_mul, Nat.cast_mul, mul_div_mul_left _ _ hc]`.
-/
theorem idxRatio_eq_of_le (A B D : Subgroup G) (hDA : D ≤ A) (hDB : D ≤ B)
    (hA : D.relIndex A ≠ 0) :
    idxRatio A B = (D.relIndex A : ℚ) / (D.relIndex B : ℚ) := by
  have h1 : D.relIndex (A ⊓ B) * (A ⊓ B).relIndex A = D.relIndex A :=
    Subgroup.relIndex_mul_relIndex (hHK := le_inf hDA hDB) (hKL := inf_le_left)
  have h2 : D.relIndex (A ⊓ B) * (A ⊓ B).relIndex B = D.relIndex B :=
    Subgroup.relIndex_mul_relIndex (hHK := le_inf hDA hDB) (hKL := inf_le_right)
  rw [Subgroup.inf_relIndex_left] at h1
  rw [Subgroup.inf_relIndex_right] at h2
  have hc0 : D.relIndex (A ⊓ B) ≠ 0 := by
    intro h0
    apply hA
    rw [← h1, h0, zero_mul]
  have hc : (D.relIndex (A ⊓ B) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hc0
  unfold idxRatio
  rw [← h1, ← h2, Nat.cast_mul, Nat.cast_mul, mul_div_mul_left _ _ hc]

/- English proof (translation)
Conclude with `Subgroup.relIndex_inf_ne_zero (Subgroup.relIndex_inf_ne_zero hA hB) hC`.
-/
theorem relIndex_inf_three_ne_zero {A B C L : Subgroup G} (hA : A.relIndex L ≠ 0)
    (hB : B.relIndex L ≠ 0) (hC : C.relIndex L ≠ 0) : (A ⊓ B ⊓ C).relIndex L ≠ 0 := by
  exact Subgroup.relIndex_inf_ne_zero (Subgroup.relIndex_inf_ne_zero hA hB) hC

/- English proof (translation)
Rewrite using `[Subgroup.relIndex_self]`. Conclude with `one_ne_zero`.
-/
theorem relIndex_self_ne_zero (A : Subgroup G) : A.relIndex A ≠ 0 := by
  rw [Subgroup.relIndex_self]
  exact one_ne_zero

/- English proof (translation)
Establish `hDA` using `relIndex_inf_three_ne_zero (relIndex_self_ne_zero A) hAB hAC`. Establish `hDB` using `relIndex_inf_three_ne_zero hBA (relIndex_self_ne_zero B) hBC`. Rewrite using `[idxRatio_eq_of_le A B (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left) (le_trans inf_le_left inf_le_right) hDA, idxRatio_eq_of_le B C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_right) inf_le_right hDB, idxRatio_eq_of_le A C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left) inf_le_right …`.
-/
theorem idxRatio_mul (A B C : Subgroup G)
    (hAB : B.relIndex A ≠ 0) (hAC : C.relIndex A ≠ 0) (hBA : A.relIndex B ≠ 0)
    (hBC : C.relIndex B ≠ 0) :
    idxRatio A B * idxRatio B C = idxRatio A C := by
  have hDA := relIndex_inf_three_ne_zero (relIndex_self_ne_zero A) hAB hAC
  have hDB := relIndex_inf_three_ne_zero hBA (relIndex_self_ne_zero B) hBC
  rw [idxRatio_eq_of_le A B (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left)
      (le_trans inf_le_left inf_le_right) hDA,
    idxRatio_eq_of_le B C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_right) inf_le_right hDB,
    idxRatio_eq_of_le A C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left) inf_le_right hDA,
    div_mul_div_comm, mul_comm ((A ⊓ B ⊓ C).relIndex A : ℚ),
    mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr hDB)]

/- English proof (translation)
Rewrite using `[← Subgroup.relIndex_comap, Subgroup.comap_map_eq_self_of_injective hf]`.
-/
private theorem relIndex_map_of_injective (X Y : Subgroup G) (f : G →* G) (hf : Function.Injective f) :
    (X.map f).relIndex (Y.map f) = X.relIndex Y := by
  rw [← Subgroup.relIndex_comap, Subgroup.comap_map_eq_self_of_injective hf]

/- English proof (translation)
Unfold `idxRatio`. Rewrite using `[relIndex_map_of_injective _ _ f hf, relIndex_map_of_injective _ _ f hf]`.
-/
theorem idxRatio_map (A B : Subgroup G) (f : G →* G) (hf : Function.Injective f) :
    idxRatio (A.map f) (B.map f) = idxRatio A B := by
  unfold idxRatio
  rw [relIndex_map_of_injective _ _ f hf, relIndex_map_of_injective _ _ f hf]

/- English proof (translation)
Rewrite using `[Subgroup.map_map]`. Use `congr 1`. Use extensionality with `y`. Simplify using `[MulAut.conj_apply, mul_assoc]`.
-/
theorem map_conj_mul' (K : Subgroup G) (a b : G) :
    (K.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      K.map (MulAut.conj (a * b)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply, mul_assoc]

/- English proof (translation)
Use extensionality with `x`. Simplify using `[Subgroup.mem_map]`.
-/
theorem map_conj_one' (K : Subgroup G) : K.map (MulAut.conj (1 : G)).toMonoidHom = K := by
  ext x
  simp [Subgroup.mem_map]

/- English proof (translation)
Establish `h1 : K.map (MulAut.conj x).toMonoidHom = (K.map (MulAut.conj (y⁻¹ * x)).toMonoidHom).map (MulAut.conj y).toMonoidHom`. Rewrite using `[map_conj_mul', mul_inv_cancel_left]`. Rewrite using `[h1, relIndex_map_of_injective _ _ _ (by intro a b h; simpa using h)]`. Conclude with `hK (y⁻¹ * x)`.
-/
theorem relIndex_conj_conj_ne_zero (K : Subgroup G) (hK : Commensurated K) (x y : G) :
    (K.map (MulAut.conj x).toMonoidHom).relIndex (K.map (MulAut.conj y).toMonoidHom) ≠ 0 := by
  have h1 : K.map (MulAut.conj x).toMonoidHom =
      (K.map (MulAut.conj (y⁻¹ * x)).toMonoidHom).map (MulAut.conj y).toMonoidHom := by
    rw [map_conj_mul', mul_inv_cancel_left]
  rw [h1, relIndex_map_of_injective _ _ _ (by intro a b h; simpa using h)]
  exact hK (y⁻¹ * x)

/- English proof (translation)
Establish `h` using `relIndex_conj_conj_ne_zero K hK 1 a`. Rewrite `h` using `[map_conj_one']`. Then use the resulting hypothesis.
-/
theorem relIndex_conj_right_ne_zero (K : Subgroup G) (hK : Commensurated K) (a : G) :
    K.relIndex (K.map (MulAut.conj a).toMonoidHom) ≠ 0 := by
  have h := relIndex_conj_conj_ne_zero K hK 1 a
  rwa [map_conj_one'] at h

/- English proof (translation)
Unfold `dIdx`. Rewrite using `[← relIndex_map_of_injective _ _ (MulAut.conj x).toMonoidHom (by intro a b h; simpa using h), map_conj_mul', mul_inv_cancel, map_conj_one']`.
-/
theorem dIdx_inv_eq (K : Subgroup G) (x : G) :
    dIdx K x⁻¹ = K.relIndex (K.map (MulAut.conj x).toMonoidHom) := by
  unfold dIdx
  rw [← relIndex_map_of_injective _ _ (MulAut.conj x).toMonoidHom (by intro a b h; simpa using h),
    map_conj_mul', mul_inv_cancel, map_conj_one']

/- English proof (translation)
Unfold `modQ idxRatio`. Rewrite using `[dIdx_inv_eq]`. Both sides reduce to the same expression.
-/
theorem modQ_eq_idxRatio (K : Subgroup G) (x : G) :
    modQ K x = idxRatio K (K.map (MulAut.conj x).toMonoidHom) := by
  unfold modQ idxRatio
  rw [dIdx_inv_eq]
  rfl

/- English proof (translation)
Unfold `dIdx`. Rewrite using `[map_conj_one', Subgroup.relIndex_self]`.
-/
theorem dIdx_one (K : Subgroup G) : dIdx K 1 = 1 := by
  unfold dIdx
  rw [map_conj_one', Subgroup.relIndex_self]

/- English proof (translation)
Unfold `modQ`. Simplify using `[dIdx_one]`.
-/
theorem modQ_one (K : Subgroup G) : modQ K 1 = 1 := by
  unfold modQ
  simp [dIdx_one]

/- English proof (translation)
Unfold `modQ`. Rewrite using `[inv_inv, inv_div]`.
-/
theorem modQ_inv (K : Subgroup G) (x : G) : modQ K x⁻¹ = (modQ K x)⁻¹ := by
  unfold modQ
  rw [inv_inv, inv_div]

/- English proof (translation)
Unfold `modQ`. Conclude with `div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (hK x))) (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (hK x⁻¹)))`.
-/
theorem modQ_pos (K : Subgroup G) (hK : Commensurated K) (x : G) : 0 < modQ K x := by
  unfold modQ
  exact div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (hK x))) (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (hK x⁻¹)))

/- English proof (translation)
Rewrite using `[modQ_eq_idxRatio, modQ_eq_idxRatio, modQ_eq_idxRatio, ← idxRatio_map K (K.map (MulAut.conj y).toMonoidHom) (MulAut.conj x).toMonoidHom (by intro a b h; simpa using h), map_conj_mul']`. Conclude with `(idxRatio_mul K (K.map (MulAut.conj x).toMonoidHom) (K.map (MulAut.conj (x * y)).toMonoidHom) (hK x) (hK (x * y)) (relIndex_conj_right_ne_zero K hK x) (relIndex_conj_conj_ne_zero K hK (x * y) x)).symm`.
-/
theorem modQ_mul (K : Subgroup G) (hK : Commensurated K) (x y : G) :
    modQ K (x * y) = modQ K x * modQ K y := by
  rw [modQ_eq_idxRatio, modQ_eq_idxRatio, modQ_eq_idxRatio,
    ← idxRatio_map K (K.map (MulAut.conj y).toMonoidHom) (MulAut.conj x).toMonoidHom
      (by intro a b h; simpa using h), map_conj_mul']
  exact (idxRatio_mul K (K.map (MulAut.conj x).toMonoidHom) (K.map (MulAut.conj (x * y)).toMonoidHom)
    (hK x) (hK (x * y)) (relIndex_conj_right_ne_zero K hK x)
    (relIndex_conj_conj_ne_zero K hK (x * y) x)).symm

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => rw [pow_zero, pow_zero, modQ_one]`. Consider the case `succ m ih => rw [pow_succ, modQ_mul K hK, ih, pow_succ]`.
-/
theorem modQ_pow (K : Subgroup G) (hK : Commensurated K) (x : G) (m : ℕ) :
    modQ K (x ^ m) = (modQ K x) ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, modQ_one]
  | succ m ih => rw [pow_succ, modQ_mul K hK, ih, pow_succ]

/- English proof (translation)
Rewrite using `[modQ_mul K hK, modQ_mul K hK, modQ_inv]`. Establish `hy` using `(modQ_pos K hK y).ne'`. Rewrite using `[mul_comm (modQ K y) (modQ K x), mul_assoc, mul_inv_cancel₀ hy, mul_one]`.
-/
theorem modQ_conj (K : Subgroup G) (hK : Commensurated K) (x y : G) :
    modQ K (y * x * y⁻¹) = modQ K x := by
  rw [modQ_mul K hK, modQ_mul K hK, modQ_inv]
  have hy := (modQ_pos K hK y).ne'
  rw [mul_comm (modQ K y) (modQ K x), mul_assoc, mul_inv_cancel₀ hy, mul_one]

/- English proof (translation)
Rewrite using `[modQ_eq_idxRatio, h]`. Unfold `idxRatio`. Simplify using `[Subgroup.relIndex_self]`.
-/
theorem modQ_eq_one_of_map_eq (K : Subgroup G) (x : G)
    (h : K.map (MulAut.conj x).toMonoidHom = K) : modQ K x = 1 := by
  rw [modQ_eq_idxRatio, h]
  unfold idxRatio
  simp [Subgroup.relIndex_self]

/- English proof (translation)
Establish `hx' : ∀ h, h ∈ K ↔ x * h * x⁻¹ ∈ K`. Introduce `h`. Establish `h2` using `Subgroup.mem_normalizer_iff.mp hx h`. Simplify using `using h2`. Use extensionality with `y`.

Simplify using `only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, hk, rfl⟩`. Conclude with `(hx' k).mp hk`. Introduce `hy`.

Use `⟨x⁻¹ * y * x, (hx' _).mpr ?_, by group⟩` and prove the remaining obligations. Use `hy using 1` and compare the differences between its conclusion and the goal. Use `group`.
-/
theorem map_conj_of_mem_normalizer (K : Subgroup G) {x : G} (hx : x ∈ Subgroup.normalizer (K : Set G)) :
    K.map (MulAut.conj x).toMonoidHom = K := by
  have hx' : ∀ h, h ∈ K ↔ x * h * x⁻¹ ∈ K := by
    intro h
    have h2 := Subgroup.mem_normalizer_iff.mp hx h
    simpa using h2
  ext y
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact (hx' k).mp hk
  · intro hy
    refine ⟨x⁻¹ * y * x, (hx' _).mpr ?_, by group⟩
    convert hy using 1
    group

/- English proof (translation)
Conclude with `modQ_eq_one_of_map_eq K x (map_conj_of_mem_normalizer K hx)`.
-/
theorem modQ_eq_one_of_mem_normalizer (K : Subgroup G) {x : G} (hx : x ∈ Subgroup.normalizer (K : Set G)) :
    modQ K x = 1 := by
  exact modQ_eq_one_of_map_eq K x (map_conj_of_mem_normalizer K hx)

/- English proof (translation)
Apply `modQ_eq_one_of_mem_normalizer` to reduce the goal to its premises. Rewrite using `[Subgroup.mem_normalizer_iff]`. Introduce `h`. Apply the tactic sequence `try simp only [SetLike.mem_coe]`. Prove the components needed by the constructor for the conclusion.

Introduce `hh`. Conclude with `K.mul_mem (K.mul_mem hk hh) (K.inv_mem hk)`. Introduce `hh`. Establish `h2` using `K.mul_mem (K.mul_mem (K.inv_mem hk) hh) hk`. Simplify `h2` using `[mul_assoc]`.
-/
theorem modQ_eq_one_of_mem (K : Subgroup G) {k : G} (hk : k ∈ K) : modQ K k = 1 := by
  apply modQ_eq_one_of_mem_normalizer
  rw [Subgroup.mem_normalizer_iff]
  intro h
  try simp only [SetLike.mem_coe]
  constructor
  · intro hh
    exact K.mul_mem (K.mul_mem hk hh) (K.inv_mem hk)
  · intro hh
    have h2 := K.mul_mem (K.mul_mem (K.inv_mem hk) hh) hk
    simpa [mul_assoc] using h2

/- English proof (translation)
Rewrite `h` using `[modQ_pow K hK]`. Conclude with `(pow_eq_one_iff_of_nonneg (modQ_pos K hK x).le hm).mp h`.
-/
theorem modQ_eq_one_of_pow (K : Subgroup G) (hK : Commensurated K) (x : G) {m : ℕ} (hm : m ≠ 0)
    (h : modQ K (x ^ m) = 1) : modQ K x = 1 := by
  rw [modQ_pow K hK] at h
  exact (pow_eq_one_iff_of_nonneg (modQ_pos K hK x).le hm).mp h

/- English proof (translation)
Conclude with `modQ_eq_one_of_pow K hK x hm (modQ_eq_one_of_mem_normalizer K h)`.
-/
theorem modQ_eq_one_of_pow_normalizer (K : Subgroup G) (hK : Commensurated K) (x : G) {m : ℕ}
    (hm : m ≠ 0) (h : x ^ m ∈ Subgroup.normalizer (K : Set G)) : modQ K x = 1 := by
  exact modQ_eq_one_of_pow K hK x hm (modQ_eq_one_of_mem_normalizer K h)

/- English proof (translation)
Introduce `x hx`. Proceed by induction on `hx using Subgroup.closure_induction with`. Consider the case `mem s hs => exact hS s hs`. Consider the case `one => exact modQ_one K`. Consider the case `mul a b _ _ ha hb => rw [modQ_mul K hK, ha, hb, one_mul]`.

Consider the case `inv a _ ha => rw [modQ_inv, ha, inv_one]`.
-/
theorem modQ_eq_one_closure (K : Subgroup G) (hK : Commensurated K) (S : Set G)
    (hS : ∀ s ∈ S, modQ K s = 1) : ∀ x ∈ Subgroup.closure S, modQ K x = 1 := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem s hs => exact hS s hs
  | one => exact modQ_one K
  | mul a b _ _ ha hb => rw [modQ_mul K hK, ha, hb, one_mul]
  | inv a _ ha => rw [modQ_inv, ha, inv_one]

/- English proof (translation)
Unfold `modQ at h`. Establish `h2 : ((dIdx K x⁻¹ : ℕ) : ℚ) ≠ 0` using `Nat.cast_ne_zero.mpr (hK x⁻¹)`. Rewrite `h` using `[div_eq_one_iff_eq h2]`. Conclude with `h` after adjusting the coercions.
-/
theorem dIdx_eq_of_modQ (K : Subgroup G) (hK : Commensurated K) (x : G) (h : modQ K x = 1) :
    dIdx K x = dIdx K x⁻¹ := by
  unfold modQ at h
  have h2 : ((dIdx K x⁻¹ : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (hK x⁻¹)
  rw [div_eq_one_iff_eq h2] at h
  exact_mod_cast h

end Delta

/- English proof (translation)
Unfold `PI.AdIndexEq.IndexEq`. Introduce `I x`. Conclude with `dIdx_eq_of_modQ (PI.AdIndexEq.Ksub I) (hK I) x (h I x)`.
-/
theorem indexEq_of_modQ_eq_one (hK : KComm)
    (h : ∀ (I : Formalism.MainNotions.S.AutInst) (x : I.Gf), modQ (PI.AdIndexEq.Ksub I) x = 1) :
    PI.AdIndexEq.IndexEq := by
  unfold PI.AdIndexEq.IndexEq
  intro I x
  exact dIdx_eq_of_modQ (PI.AdIndexEq.Ksub I) (hK I) x (h I x)

end PI.UnitaryGroupMassFormula.AdIndexEq
