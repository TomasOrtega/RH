import Development.DiscreteGroups.GlobalIrreducibility.LConvBigA

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker

namespace DiscreteGroups.sglob.LConv

variable {k : Type} [Field k] {m : ℕ}

def cornerHom : GL (Fin m) k →* GL (Fin (m + 1)) k :=
  (emb₂ k (stdSum (rfl : m + 1 = m + 1))).comp (MonoidHom.inl _ _)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cornerHom_apply (g : GL (Fin m) k) : cornerHom g = corner g := rfl

def IsP (p : GL (Fin (m + 1)) k) : Prop :=
  ∀ j, (p : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j

/- English proof (translation)
Rewrite using `[Units.val_mul, Matrix.mul_apply]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem mul_apply_last_of_isMirabolic {a b : GL (Fin (m + 1)) k} (ha : IsP a) (j : Fin (m + 1)) :
    ((a * b : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j =
      (b : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j := by
  rw [Units.val_mul, Matrix.mul_apply]
  calc ∑ c, (a : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) c * (b : Matrix (Fin (m + 1)) (Fin (m + 1)) k) c j
      = ∑ c, (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) c * (b : Matrix (Fin (m + 1)) (Fin (m + 1)) k) c j :=
        Finset.sum_congr rfl fun c _ => by rw [ha c]
    _ = _ := by rw [← Matrix.mul_apply, Matrix.one_mul]

/- English proof (translation)
Introduce `j` and use `(mul_apply_last_of_isMirabolic ha j).trans (hb j)`.
-/
theorem isMirabolic_mul {a b : GL (Fin (m + 1)) k} (ha : IsP a) (hb : IsP b) : IsP (a * b) := fun j =>
  (mul_apply_last_of_isMirabolic ha j).trans (hb j)

/- English proof (translation)
The claim follows from `corner_last g`.
-/
theorem isMirabolic_corner (g : GL (Fin m) k) : IsP (corner g) := corner_last g

/- English proof (translation)
Establish `hne : ∀ j : Fin m, Fin.last m ≠ j.castSucc` using `fun j => (Fin.castSucc_lt_last j).ne'`. Use `set A : Matrix (Fin m) (Fin m) k := (p : Matrix (Fin (m + 1)) (Fin (m + 1)) k).submatrix Fin.castSucc Fin.castSucc`. Establish `he : ((-1 : k) ^ (m + m)) = 1` using `by rw [← two_mul, pow_mul]; simp`. Establish `hdet : (p : Matrix (Fin (m + 1)) (Fin (m + 1)) k).det = A.det`. Establish `hp' : ∀ j, (p : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j` using `hp`.

Rewrite using `[Matrix.det_succ_row _ (Fin.last m), Fin.sum_univ_castSucc]`. Simplify using `[hp', Matrix.one_apply, hne, Fin.succAbove_last, A, he]`. Establish `hA : A.det ≠ 0`. Rewrite using `[← hdet]`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).1 p.isUnit).ne_zero`.

Use `set h : GL (Fin m) k := Matrix.GeneralLinearGroup.mkOfDetNeZero A hA`. Establish `hh : (h : Matrix (Fin m) (Fin m) k) = A` using `rfl`. Use `⟨p * corner h⁻¹, ?_, h, ?_⟩` and prove the remaining obligations. Use `swap`. Rewrite using `[mul_assoc, ← cornerHom_apply, ← cornerHom_apply, ← map_mul, inv_mul_cancel, map_one, mul_one]`.

Establish `hL : ∀ j, ((p * corner h⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j` using `fun j => (mul_apply_last_of_isMirabolic hp j).trans (corner_last _ j)`. Establish `hB : ∀ i j : Fin m, ((p * corner h⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) i.castSucc j.castSucc = (1 : Matrix (Fin m) (Fin m) k) i j`. Introduce `i j`. Rewrite using `[Units.val_mul, Matrix.mul_apply, Fin.sum_univ_castSucc, corner_last, Matrix.one_apply_ne (hne j)]`. Simplify using `only [corner_cs_cs, mul_zero, add_zero]`.

Rewrite using `[← h.mul_inv, Matrix.mul_apply, hh]`. Both sides reduce to the same expression. Use `(mem_unipB k).2 ⟨fun i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last => rw [hL, Matrix.one_apply_ne hij.ne']`.

Consider the case `cast i`. Proceed by induction on `j using Fin.lastCases with`. Consider the case `last => exact absurd hij (not_lt.2 (Fin.castSucc_lt_last i).le)`. Consider the case `cast j`. Rewrite using `[hB, Matrix.one_apply_ne]`.

Introduce `e`. Substitute `e` using the available equality. Conclude with `lt_irrefl _ hij`. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last => rw [hL, Matrix.one_apply_eq]`.

Consider the case `cast i => rw [hB, Matrix.one_apply_eq]`.
-/
theorem exists_eq_mul_corner {p : GL (Fin (m + 1)) k} (hp : IsP p) :
    ∃ u ∈ unipB k (Fin (m + 1)), ∃ h : GL (Fin m) k, p = u * corner h := by
  have hne : ∀ j : Fin m, Fin.last m ≠ j.castSucc := fun j => (Fin.castSucc_lt_last j).ne'
  set A : Matrix (Fin m) (Fin m) k := (p : Matrix (Fin (m + 1)) (Fin (m + 1)) k).submatrix Fin.castSucc Fin.castSucc
  have he : ((-1 : k) ^ (m + m)) = 1 := by rw [← two_mul, pow_mul]; simp
  have hdet : (p : Matrix (Fin (m + 1)) (Fin (m + 1)) k).det = A.det := by
    have hp' : ∀ j, (p : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j =
        (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j := hp
    rw [Matrix.det_succ_row _ (Fin.last m), Fin.sum_univ_castSucc]
    simp [hp', Matrix.one_apply, hne, Fin.succAbove_last, A, he]
  have hA : A.det ≠ 0 := by
    rw [← hdet]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 p.isUnit).ne_zero
  set h : GL (Fin m) k := Matrix.GeneralLinearGroup.mkOfDetNeZero A hA
  have hh : (h : Matrix (Fin m) (Fin m) k) = A := rfl
  refine ⟨p * corner h⁻¹, ?_, h, ?_⟩
  swap
  · rw [mul_assoc, ← cornerHom_apply, ← cornerHom_apply, ← map_mul, inv_mul_cancel, map_one, mul_one]
  have hL : ∀ j, ((p * corner h⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j := fun j =>
    (mul_apply_last_of_isMirabolic hp j).trans (corner_last _ j)
  have hB : ∀ i j : Fin m, ((p * corner h⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)
      i.castSucc j.castSucc = (1 : Matrix (Fin m) (Fin m) k) i j := by
    intro i j
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_castSucc, corner_last, Matrix.one_apply_ne (hne j)]
    simp only [corner_cs_cs, mul_zero, add_zero]
    rw [← h.mul_inv, Matrix.mul_apply, hh]
    rfl
  refine (mem_unipB k).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · induction i using Fin.lastCases with
    | last => rw [hL, Matrix.one_apply_ne hij.ne']
    | cast i =>
      induction j using Fin.lastCases with
      | last => exact absurd hij (not_lt.2 (Fin.castSucc_lt_last i).le)
      | cast j =>
        rw [hB, Matrix.one_apply_ne]
        intro e; subst e; exact lt_irrefl _ hij
  · induction i using Fin.lastCases with
    | last => rw [hL, Matrix.one_apply_eq]
    | cast i => rw [hB, Matrix.one_apply_eq]

section Agree

variable {ψ : AddChar k Circle} {V₁ V₂ : Type} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
  {π₁ : Representation ℂ (GL (Fin (m + 1)) k) V₁} {π₂ : Representation ℂ (GL (Fin (m + 1)) k) V₂}
  {l₁ : Module.Dual ℂ V₁} {l₂ : Module.Dual ℂ V₂}

/- English proof (translation)
Take `⟨u, hu, h, rfl⟩` from `exists_eq_mul_corner hp`. Rewrite using `[map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hl₁ u hu, hl₂ u hu, hX h]`.
-/
theorem agree_of_isP (hl₁ : IsFunctional ψ π₁ l₁) (hl₂ : IsFunctional ψ π₂ l₂) {v₁ : V₁} {v₂ : V₂}
    (hX : ∀ g : GL (Fin m) k, l₁ (π₁ (corner g) v₁) = l₂ (π₂ (corner g) v₂)) {p : GL (Fin (m + 1)) k}
    (hp : IsP p) : l₁ (π₁ p v₁) = l₂ (π₂ p v₂) := by
  obtain ⟨u, hu, h, rfl⟩ := exists_eq_mul_corner hp
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hl₁ u hu, hl₂ u hu, hX h]

/- English proof (translation)
Rewrite using `[← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]`. Conclude with `agree_of_isP hl₁ hl₂ hX (isMirabolic_mul (isMirabolic_corner g) hp)`.
-/
theorem agree_translate (hl₁ : IsFunctional ψ π₁ l₁) (hl₂ : IsFunctional ψ π₂ l₂) {v₁ : V₁} {v₂ : V₂}
    (hX : ∀ g : GL (Fin m) k, l₁ (π₁ (corner g) v₁) = l₂ (π₂ (corner g) v₂)) {p : GL (Fin (m + 1)) k}
    (hp : IsP p) (g : GL (Fin m) k) : l₁ (π₁ (corner g) (π₁ p v₁)) = l₂ (π₂ (corner g) (π₂ p v₂)) := by
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  exact agree_of_isP hl₁ hl₂ hX (isMirabolic_mul (isMirabolic_corner g) hp)

end Agree

end DiscreteGroups.sglob.LConv

end
