import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup

noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical TensorProduct

namespace GlobalTheory.FrameBasic

/- English proof (translation)
Set `e` to `Submodule.prodEquivOfIsCompl T T' h`. Establish `: Module.Finite R T` using `Module.Finite.of_surjective (T.projectionOnto T' h) (Submodule.projectionOnto_surjective h)`. Establish `: Module.Finite R T'` using `Module.Finite.of_surjective (T'.projectionOnto T h.symm) (Submodule.projectionOnto_surjective h.symm)`. Establish `: Module.Projective R T'` using `Module.Projective.of_split T'.subtype (T'.projectionOnto T h.symm) (by ext; simp)`. Use `Module.nonempty_basis_of_flat_of_finrank_eq R T' _ fun P => ?_` and prove the remaining obligations.

Set `` to `P.isMaximal`. Set `` to `Ideal.Quotient.field P.asIdeal`. Establish `: Nontrivial R` using `(Ideal.Quotient.mk P.asIdeal).domain_nontrivial`. Establish `e' : ((R ⧸ P.1) ⊗[R] M) ≃ₗ[R ⧸ P.1] ((R ⧸ P.1) ⊗[R] T) × ((R ⧸ P.1) ⊗[R] T')` using `(e.symm.baseChange R (R ⧸ P.1) _ _).trans (TensorProduct.prodRight R (R ⧸ P.1) _ _ _)`. Use `e'.finrank_eq` as an intermediate fact.

Rewrite `this` using `[Module.finrank_prod, Module.finrank_baseChange, Module.finrank_baseChange]`. Use linear arithmetic over natural numbers and integers.
-/
theorem basis_of_isCompl {R M : Type*} [CommRing R] [Finite (MaximalSpectrum R)] [AddCommGroup M]
    [Module R M] [Module.Free R M] [Module.Finite R M] {T T' : Submodule R M} [Module.Free R T]
    (h : IsCompl T T') :
    Nonempty (Module.Basis (Fin (Module.finrank R M - Module.finrank R T)) R T') := by
  let e := Submodule.prodEquivOfIsCompl T T' h
  have : Module.Finite R T := Module.Finite.of_surjective (T.projectionOnto T' h)
    (Submodule.projectionOnto_surjective h)
  have : Module.Finite R T' := Module.Finite.of_surjective (T'.projectionOnto T h.symm)
    (Submodule.projectionOnto_surjective h.symm)
  have : Module.Projective R T' :=
    Module.Projective.of_split T'.subtype (T'.projectionOnto T h.symm) (by ext; simp)
  refine Module.nonempty_basis_of_flat_of_finrank_eq R T' _ fun P => ?_
  let := P.isMaximal
  let := Ideal.Quotient.field P.asIdeal
  have : Nontrivial R := (Ideal.Quotient.mk P.asIdeal).domain_nontrivial
  have e' : ((R ⧸ P.1) ⊗[R] M) ≃ₗ[R ⧸ P.1] ((R ⧸ P.1) ⊗[R] T) × ((R ⧸ P.1) ⊗[R] T') :=
    (e.symm.baseChange R (R ⧸ P.1) _ _).trans (TensorProduct.prodRight R (R ⧸ P.1) _ _ _)
  have := e'.finrank_eq
  rw [Module.finrank_prod, Module.finrank_baseChange, Module.finrank_baseChange] at this
  omega

section Mono
variable {E : Type} [CommRing E]

def sig (bs : List (Eˣ × ℕ+)) : ℕ → ℕ :=
  bs.foldr (fun p g a => if a < p.2 then p.2 - 1 - a else p.2 + g (a - p.2)) id

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sig_cons (t : Eˣ) (s : ℕ+) (bs : List (Eˣ × ℕ+)) (a : ℕ) :
    sig ((t, s) :: bs) a = if a < s then s - 1 - a else s + sig bs (a - s) := rfl

/- English proof (translation)
The claim follows from `| [], a => rfl | (t, s) :: bs, a => by by_cases h : a < s · have h2 : (s : ℕ) - 1 - a < s := by omega simp only [sig_cons, h, h2, if_true]; omega · have h2 : ¬ ((s : ℕ) + sig bs (a - s) < s) := by omega simp only [sig_cons, h, h2, if_false, Nat.add_sub_cancel_left, sig_sig bs]; o …`.
-/
theorem sig_sig : ∀ (bs : List (Eˣ × ℕ+)) (a : ℕ), sig bs (sig bs a) = a
  | [], a => rfl
  | (t, s) :: bs, a => by
    by_cases h : a < s
    · have h2 : (s : ℕ) - 1 - a < s := by omega
      simp only [sig_cons, h, h2, if_true]; omega
    · have h2 : ¬ ((s : ℕ) + sig bs (a - s) < s) := by omega
      simp only [sig_cons, h, h2, if_false, Nat.add_sub_cancel_left, sig_sig bs]; omega

/- English proof (translation)
The claim follows from `| [], a, b, _ => rfl | (t, s) :: bs, a, b, hb => by simp only [sig_cons] at hb simp only [ptEntryL] split_ifs with h1 h2 h3 · rw [if_pos h1.1] at hb; omega · rfl · rw [if_neg (by omega)] at hb exact entry_zero bs _ _ (by omega) · rfl`.
-/
theorem entry_zero : ∀ (bs : List (Eˣ × ℕ+)) (a b : ℕ), b ≠ sig bs a → ptEntryL bs a b = 0
  | [], a, b, _ => rfl
  | (t, s) :: bs, a, b, hb => by
    simp only [sig_cons] at hb
    simp only [ptEntryL]
    split_ifs with h1 h2 h3
    · rw [if_pos h1.1] at hb; omega
    · rfl
    · rw [if_neg (by omega)] at hb
      exact entry_zero bs _ _ (by omega)
    · rfl

/- English proof (translation)
The claim follows from `| [], a, h => by simp at h | (t, s) :: bs, a, h => by simp only [List.map_cons, List.sum_cons] at h ⊢ by_cases h1 : a < s · simp only [sig_cons, ptEntryL, h1, if_true] refine ⟨by omega, ?_⟩ rw [if_pos ⟨trivial, by omega⟩, if_pos (by omega)] exact t.isUnit · obtain ⟨h2, h3⟩ := ent …`.
-/
theorem entry_unit : ∀ (bs : List (Eˣ × ℕ+)) (a : ℕ), a < (bs.map (fun b => (b.2 : ℕ))).sum →
    sig bs a < (bs.map (fun b => (b.2 : ℕ))).sum ∧ IsUnit (ptEntryL bs a (sig bs a))
  | [], a, h => by simp at h
  | (t, s) :: bs, a, h => by
    simp only [List.map_cons, List.sum_cons] at h ⊢
    by_cases h1 : a < s
    · simp only [sig_cons, ptEntryL, h1, if_true]
      refine ⟨by omega, ?_⟩
      rw [if_pos ⟨trivial, by omega⟩, if_pos (by omega)]
      exact t.isUnit
    · obtain ⟨h2, h3⟩ := entry_unit bs (a - s) (by omega)
      simp only [sig_cons, ptEntryL, h1, if_false, false_and]
      refine ⟨by omega, ?_⟩
      rw [if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]
      exact h3

/- English proof (translation)
Rewrite using `[← Matrix.det_diagonal, ← Matrix.det_mul]`. Use `congr 1`. Use extensionality with `a b`. Rewrite using `[Matrix.diagonal_mul]`. Distinguish the cases in `h : b = σ a`.

Rewrite using `[Matrix.submatrix_apply, id, ← h, Matrix.one_apply_eq, mul_one]`. Simplify using `[h0 a b h, Ne.symm h]`.
-/
theorem det_mono {n : ℕ} (A : Matrix (Fin n) (Fin n) E) (σ : Fin n → Fin n)
    (h0 : ∀ a b, b ≠ σ a → A a b = 0) :
    A.det = (∏ a, A a (σ a)) * ((1 : Matrix (Fin n) (Fin n) E).submatrix σ id).det := by
  rw [← Matrix.det_diagonal, ← Matrix.det_mul]
  congr 1
  ext a b
  rw [Matrix.diagonal_mul]
  by_cases h : b = σ a
  · rw [Matrix.submatrix_apply, id, ← h, Matrix.one_apply_eq, mul_one]
  · simp [h0 a b h, Ne.symm h]

/- English proof (translation)
Establish `hb` using `Finite.injective_iff_bijective.1 h`. Use `Matrix.det_permute (Equiv.ofBijective σ hb) (1 : Matrix (Fin n) (Fin n) E)` as an intermediate fact. Rewrite `this` using `[Equiv.coe_ofBijective]`. Rewrite using `[this, Matrix.det_one, mul_one]`. Conclude with `(Units.isUnit _).map (Int.castRingHom E)`.
-/
theorem det_perm_unit {n : ℕ} (σ : Fin n → Fin n) (h : Function.Injective σ) :
    IsUnit ((1 : Matrix (Fin n) (Fin n) E).submatrix σ id).det := by
  have hb := Finite.injective_iff_bijective.1 h
  have := Matrix.det_permute (Equiv.ofBijective σ hb) (1 : Matrix (Fin n) (Fin n) E)
  rw [Equiv.coe_ofBijective] at this
  rw [this, Matrix.det_one, mul_one]
  exact (Units.isUnit _).map (Int.castRingHom E)

/- English proof (translation)
Rewrite `hd`, the goal using `[det_mono A σ h0]`. Use `IsUnit.mul ?_ (det_perm_unit σ ?_)` and prove the remaining obligations. Rewrite using `[IsUnit.prod_univ_iff]`. Introduce `a`. Use `hu a fun h => hd ?_` and prove the remaining obligations.

Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ a) h, zero_mul]`. Introduce `a b hab`. Assume the negation of the conclusion as `hne`. Apply `hd` to reduce the goal to its premises. Rewrite using `[Matrix.det_zero_of_row_eq hne (by funext c; rw [Matrix.submatrix_apply, Matrix.submatrix_apply, hab]), mul_zero]`.
-/
theorem det_mono_unit {n : ℕ} (A : Matrix (Fin n) (Fin n) E) (σ : Fin n → Fin n)
    (h0 : ∀ a b, b ≠ σ a → A a b = 0) (hu : ∀ a, A a (σ a) ≠ 0 → IsUnit (A a (σ a)))
    (hd : A.det ≠ 0) : IsUnit A.det := by
  rw [det_mono A σ h0] at hd ⊢
  refine IsUnit.mul ?_ (det_perm_unit σ ?_)
  · rw [IsUnit.prod_univ_iff]
    intro a
    refine hu a fun h => hd ?_
    rw [Finset.prod_eq_zero (Finset.mem_univ a) h, zero_mul]
  · intro a b hab
    by_contra hne
    apply hd
    rw [Matrix.det_zero_of_row_eq hne (by funext c; rw [Matrix.submatrix_apply, Matrix.submatrix_apply, hab]), mul_zero]

/- English proof (translation)
Use `det_mono_unit _ (fun a => if h : sig w.blocks a < m then ⟨_, h⟩ else a) ?_ ?_` and prove the remaining obligations. Introduce `a b hb`. Simplify using `only [Matrix.submatrix_apply, Matrix.of_apply, Pt.mat, Fin.val_castLE]`. Rewrite using `[entry_zero, zero_mul]`. Introduce `h`.

Apply `hb` to reduce the goal to its premises. Rewrite using `[dif_pos (h ▸ b.2)]`. Conclude with `Fin.ext h`. Introduce `a`. Simplify using `only [Matrix.submatrix_apply, Matrix.of_apply, Pt.mat, Fin.val_castLE]`.

Use `split_ifs with h`. Introduce `_`. Conclude with `(entry_unit w.blocks a (by rw [w.size]; omega)).2.mul (hε _)`. Introduce `h2 exfalso`. Apply `h2` to reduce the goal to its premises.

Rewrite using `[entry_zero, zero_mul]`. Introduce `h3`. Conclude with `h (h3 ▸ a.2)`.
-/
theorem lead_unit {n : ℕ} (w : Pt E n) (ε : Fin n → E) (hε : ∀ b, IsUnit (ε b))
    {m : ℕ} (hm : m ≤ n) :
    ((Matrix.of fun a b => w.mat a b * ε b).submatrix (Fin.castLE hm) (Fin.castLE hm)).det ≠ 0 →
    IsUnit ((Matrix.of fun a b => w.mat a b * ε b).submatrix (Fin.castLE hm) (Fin.castLE hm)).det := by
  refine det_mono_unit _ (fun a => if h : sig w.blocks a < m then ⟨_, h⟩ else a) ?_ ?_
  · intro a b hb
    simp only [Matrix.submatrix_apply, Matrix.of_apply, Pt.mat, Fin.val_castLE]
    rw [entry_zero, zero_mul]
    intro h
    apply hb
    rw [dif_pos (h ▸ b.2)]
    exact Fin.ext h
  · intro a
    simp only [Matrix.submatrix_apply, Matrix.of_apply, Pt.mat, Fin.val_castLE]
    split_ifs with h
    · intro _
      exact (entry_unit w.blocks a (by rw [w.size]; omega)).2.mul (hε _)
    · intro h2
      exfalso; apply h2
      rw [entry_zero, zero_mul]
      intro h3
      exact h (h3 ▸ a.2)

/- English proof (translation)
Establish `hs : ∀ a : Fin n, sig w.blocks a < n` using `fun a => by`. Use `(entry_unit w.blocks a (by rw [w.size]; omega)).1` as an intermediate fact. Rewrite `this` using `[w.size]`. Then use the resulting hypothesis. Rewrite using `[det_mono _ (fun a => ⟨_, hs a⟩)]`. Use `IsUnit.mul ?_ (det_perm_unit _ ?_)` and prove the remaining obligations.

Rewrite using `[IsUnit.prod_univ_iff]`. Introduce `a`. Conclude with `(entry_unit w.blocks a (by rw [w.size]; omega)).2.mul (hε _)`. Introduce `a b hab`. Establish `h1 : sig w.blocks a = sig w.blocks b` using `congrArg Fin.val hab`.

Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[← sig_sig w.blocks a, h1, sig_sig]`. Introduce `a b hb`. Simplify using `only [Matrix.of_apply, Pt.mat]`. Rewrite using `[entry_zero, zero_mul]`.

Introduce `h`. Conclude with `hb (Fin.ext h)`.
-/
theorem full_unit {n : ℕ} (w : Pt E n) (ε : Fin n → E) (hε : ∀ b, IsUnit (ε b)) :
    IsUnit (Matrix.of fun a b => w.mat a b * ε b).det := by
  have hs : ∀ a : Fin n, sig w.blocks a < n := fun a => by
    have := (entry_unit w.blocks a (by rw [w.size]; omega)).1
    rwa [w.size] at this
  rw [det_mono _ (fun a => ⟨_, hs a⟩)]
  · refine IsUnit.mul ?_ (det_perm_unit _ ?_)
    · rw [IsUnit.prod_univ_iff]
      intro a
      exact (entry_unit w.blocks a (by rw [w.size]; omega)).2.mul (hε _)
    · intro a b hab
      have h1 : sig w.blocks a = sig w.blocks b := congrArg Fin.val hab
      apply Fin.ext
      rw [← sig_sig w.blocks a, h1, sig_sig]
  · intro a b hb
    simp only [Matrix.of_apply, Pt.mat]
    rw [entry_zero, zero_mul]
    intro h
    exact hb (Fin.ext h)

/- English proof (translation)
Establish `h1` using `congrArg (fun v => Z.adjugate.mulVec v (Fin.last r)) h`. Simplify using `only [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_single] at h1`. Rewrite using `[h1]`. Simplify using `[Matrix.adjugate_fin_succ_eq_det_submatrix, ← two_mul]`.
-/
theorem cramer_last {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (β : Fin (r + 1) → E) (c : E)
    (h : Z.mulVec β = Pi.single (Fin.last r) c) :
    Z.det * β (Fin.last r) = (Z.submatrix Fin.castSucc Fin.castSucc).det * c := by
  have h1 := congrArg (fun v => Z.adjugate.mulVec v (Fin.last r)) h
  simp only [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
    Pi.smul_apply, smul_eq_mul, Matrix.mulVec_single] at h1
  rw [h1]
  simp [Matrix.adjugate_fin_succ_eq_det_submatrix, ← two_mul]

/- English proof (translation)
Establish `e1` using `cramer_last _ _ _ h1`. Establish `e2` using `cramer_last _ _ _ h2`. Establish `ha : α (Fin.last r) = 0`. Apply `hG.mul_right_eq_zero.1` to reduce the goal to its premises. Take the linear combination `Z.det * e2 + T' * (Z'.submatrix Fin.castSucc Fin.castSucc).det * e1`.

Establish `hb : β = 0`. Rewrite `h1` using `[ha, mul_zero, Pi.single_zero]`. Conclude with `(Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 hZ)) (by simpa using h1)`. Use `⟨?_, hb⟩` and prove the remaining obligations. Rewrite `h2` using `[hb, Pi.zero_apply, mul_zero, Pi.single_zero]`.

Conclude with `(Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 hZ')) (by simpa using h2)`.
-/
theorem solve_zero {r : ℕ} (Z Z' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E)
    (hZ : IsUnit Z.det) (hZ' : IsUnit Z'.det)
    (hG : IsUnit (Z.det * Z'.det - T * T' * ((Z.submatrix Fin.castSucc Fin.castSucc).det *
      (Z'.submatrix Fin.castSucc Fin.castSucc).det)))
    (α β : Fin (r + 1) → E) (h1 : Z.mulVec β = Pi.single (Fin.last r) (T * α (Fin.last r)))
    (h2 : Z'.mulVec α = Pi.single (Fin.last r) (T' * β (Fin.last r))) : α = 0 ∧ β = 0 := by
  have e1 := cramer_last _ _ _ h1
  have e2 := cramer_last _ _ _ h2
  have ha : α (Fin.last r) = 0 := by
    apply hG.mul_right_eq_zero.1
    linear_combination Z.det * e2 + T' * (Z'.submatrix Fin.castSucc Fin.castSucc).det * e1
  have hb : β = 0 := by
    rw [ha, mul_zero, Pi.single_zero] at h1
    exact (Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 hZ)) (by simpa using h1)
  refine ⟨?_, hb⟩
  rw [hb, Pi.zero_apply, mul_zero, Pi.single_zero] at h2
  exact (Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 hZ')) (by simpa using h2)

end Mono

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

def hfL (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (y : Fin n → E) :
    (Fin n → E) →ₗ[E] E where
  toFun x := hf L H x y
  map_add' a b := by simp [hf, add_mul, Finset.sum_add_distrib]
  map_smul' c a := by simp [hf, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Establish `h1 : ∀ i j, L.cj (H j i) = H i j` using `fun i j => congrFun (congrFun h i) j`. Simplify using `only [hf, map_sum, map_mul, L.cj_cj, h1]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring` and prove the remaining obligations.
-/
theorem hf_conj (L : LocE F E) {n : ℕ} {H : Matrix (Fin n) (Fin n) E} (h : IsHerm L H)
    (x y : Fin n → E) : hf L H x y = L.cj (hf L H y x) := by
  have h1 : ∀ i j, L.cj (H j i) = H i j := fun i j => congrFun (congrFun h i) j
  simp only [hf, map_sum, map_mul, L.cj_cj, h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Use `⟨fun hx j => hx _ (Submodule.subset_span ⟨j, rfl⟩), fun hx y hy => ?_⟩` and prove the remaining obligations. Establish `: Submodule.span E (Set.range g) ≤ LinearMap.ker (hfL L H x)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Express the relevant statement in the definitionally equal form `hf L H (g j) x = 0`.

Rewrite using `[hf_conj L h, hx j, map_zero]`. Establish `h2 : hf L H y x = 0` using `this hy`. Rewrite using `[hf_conj L h, h2, map_zero]`.
-/
theorem mem_perp_span (L : LocE F E) {n : ℕ} {H : Matrix (Fin n) (Fin n) E} (h : IsHerm L H)
    {ι : Type} (g : ι → Fin n → E) (x : Fin n → E) :
    x ∈ perp L H (Submodule.span E (Set.range g)) ↔ ∀ j, hf L H x (g j) = 0 := by
  refine ⟨fun hx j => hx _ (Submodule.subset_span ⟨j, rfl⟩), fun hx y hy => ?_⟩
  have : Submodule.span E (Set.range g) ≤ LinearMap.ker (hfL L H x) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    change hf L H (g j) x = 0
    rw [hf_conj L h, hx j, map_zero]
  have h2 : hf L H y x = 0 := this hy
  rw [hf_conj L h, h2, map_zero]

/- English proof (translation)
Establish `key : ∀ (α : ι → E) (y : Fin n → E), hf L H (∑ i, α i • g i) y = ∑ i, α i * hf L H (g i) y` using `fun α y => by`. Express the relevant statement in the definitionally equal form `hfL L H y _ = _`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [map_smul]; rfl`. Set `φ : (ι → E) →ₗ[E] (ι → E)` to `LinearMap.pi fun j => (hfL L H (g j)).comp (Fintype.linearCombination E g)`.

Establish `hφ : ∀ α j, φ α j = hf L H (∑ i, α i • g i) (g j)` using `fun α j => by`. Simplify using `only [φ, LinearMap.pi_apply, LinearMap.comp_apply, Fintype.linearCombination_apply]`. Both sides reduce to the same expression. Establish `hinj : Function.Injective φ`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `α hα`. Use `hg α fun j => ?_` and prove the remaining obligations. Rewrite using `[← key, ← hφ, hα]`. Both sides reduce to the same expression. Establish `hsurj` using `(IsArtinian.bijective_of_injective_endomorphism φ hinj).2`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `α hα`. Establish `: α = 0` using `hg α fun j => by rw [← key, hα]; simp [hf]`. Simplify using `[this]`.

Rewrite using `[Submodule.disjoint_def]`. Introduce `x hx hx'`. Rewrite `hx'` using `[mem_perp_span L h]`. Take `⟨α, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun E).1 hx`. Establish `: α = 0` using `hg α fun j => by rw [← key, hx']`.

Simplify using `[this]`. Rewrite using `[codisjoint_iff, eq_top_iff]`. Introduce `v _`. Take `⟨α, hα⟩` from `hsurj fun j => hf L H v (g j)`. Use `Submodule.mem_sup.2 ⟨∑ i, α i • g i, (Submodule.mem_span_range_iff_exists_fun E).2 ⟨α, rfl⟩, v - ∑ i, α i • g i, ?_, by simp⟩` and prove the remaining obligations.

Rewrite using `[mem_perp_span L h]`. Introduce `j`. Express the relevant statement in the definitionally equal form `hfL L H (g j) _ = 0`. Rewrite using `[map_sub]`. Use `congrFun hα j` as an intermediate fact.

Rewrite `this` using `[hφ]`. Conclude with `sub_eq_zero.2 this.symm`.
-/
theorem split_of_gram (L : LocE F E) [IsArtinianRing E] {n : ℕ} {H : Matrix (Fin n) (Fin n) E}
    (h : IsHerm L H) {ι : Type} [Fintype ι] (g : ι → Fin n → E)
    (hg : ∀ α : ι → E, (∀ j, ∑ i, α i * hf L H (g i) (g j) = 0) → α = 0) :
    LinearIndependent E g ∧
      IsCompl (Submodule.span E (Set.range g)) (perp L H (Submodule.span E (Set.range g))) := by
  have key : ∀ (α : ι → E) (y : Fin n → E),
      hf L H (∑ i, α i • g i) y = ∑ i, α i * hf L H (g i) y := fun α y => by
    change hfL L H y _ = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul]; rfl
  let φ : (ι → E) →ₗ[E] (ι → E) :=
    LinearMap.pi fun j => (hfL L H (g j)).comp (Fintype.linearCombination E g)
  have hφ : ∀ α j, φ α j = hf L H (∑ i, α i • g i) (g j) := fun α j => by
    simp only [φ, LinearMap.pi_apply, LinearMap.comp_apply, Fintype.linearCombination_apply]; rfl
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro α hα
    refine hg α fun j => ?_
    rw [← key, ← hφ, hα]; rfl
  have hsurj := (IsArtinian.bijective_of_injective_endomorphism φ hinj).2
  refine ⟨?_, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro α hα
    have : α = 0 := hg α fun j => by rw [← key, hα]; simp [hf]
    simp [this]
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    rw [mem_perp_span L h] at hx'
    obtain ⟨α, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hx
    have : α = 0 := hg α fun j => by rw [← key, hx']
    simp [this]
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    obtain ⟨α, hα⟩ := hsurj fun j => hf L H v (g j)
    refine Submodule.mem_sup.2 ⟨∑ i, α i • g i,
      (Submodule.mem_span_range_iff_exists_fun E).2 ⟨α, rfl⟩, v - ∑ i, α i • g i, ?_, by simp⟩
    rw [mem_perp_span L h]
    intro j
    change hfL L H (g j) _ = 0
    rw [map_sub]
    have := congrFun hα j
    rw [hφ] at this
    exact sub_eq_zero.2 this.symm

/- English proof (translation)
Use `L.free` as an intermediate fact. Establish `: Module.Finite F E` using `Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)`. Establish `: Nontrivial E` using `Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; norm_num)`. Establish `: IsArtinianRing E` using `IsArtinianRing.of_finite F E`. Establish `hZ : S.Zh = Matrix.of fun a b => S.w.mat a b * (-1) ^ (r - (b : ℕ))`.

Use extensionality with `a b`. Conclude with `S.relevant a b`. Establish `hε : ∀ b : Fin (r + 1), IsUnit ((-1 : E) ^ (r - (b : ℕ)))` using `fun b => (isUnit_one.neg).pow _`. Establish `hD1 : S.D (Fin.last (r + 1)) = S.Zh.det` using `rfl`. Establish `hD0 : S.D (Fin.last r).castSucc = (S.Zh.submatrix Fin.castSucc Fin.castSucc).det` using `rfl`.

Establish `hU : IsUnit S.Zh.det` using `by rw [hZ]; exact full_unit _ _ hε`. Establish `hc : ∃ c : F, c ≠ 0 ∧ S.G = algebraMap F E c`. Establish `hfix : L.cj S.G = S.G`. Simplify using `only [Frames.G, map_sub, map_mul, L.cj_cj, AlgEquiv.commutes]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨c, hc⟩` from `(L.cj_fix _).1 hfix`. Use `⟨c, ?_, hc.symm⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `S.G_ne (show S.G = 0 by rw [← hc, map_zero])`. Establish `hGu : IsUnit S.G`.

Take `⟨c, h0, hc⟩` from `hc`. Rewrite using `[hc]`. Conclude with `(IsUnit.mk0 c h0).map _`. Establish `hME : S.ME = Submodule.span E (Set.range (Sum.elim S.f S.f'))`. Establish `hs : {i : Fin (r + 1) | (i : ℕ) < r + 1} = Set.univ`.

Use extensionality with `i`. Simplify using `using i.2`. Simplify using `only [Frames.ME, Frames.spanTo, hs, Set.image_univ, Set.Sum.elim_range, Submodule.span_union]`. Establish `hdet : ∀ {m : ℕ} (A : Matrix (Fin m) (Fin m) E), (A.map L.cj).transpose.det = L.cj A.det`. Introduce `m A`.

Rewrite using `[Matrix.det_transpose]`. Conclude with `(AlgEquiv.map_det L.cj A).symm`. Take `⟨hli, hco⟩` from `split_of_gram L S.herm.1 (Sum.elim S.f S.f') (by`. Introduce `γ hγ`. Use `solve_zero S.Zh (S.Zh.map L.cj).transpose (algebraMap F E S.T) (algebraMap F E S.T') hU (by rw [hdet]; exact hU.map _) (by` as an intermediate fact.

Establish `e : ((S.Zh.map L.cj).transpose.submatrix Fin.castSucc Fin.castSucc) = ((S.Zh.submatrix Fin.castSucc Fin.castSucc).map L.cj).transpose` using `rfl`. Rewrite using `[e, hdet, hdet, ← map_mul, ← hD0, ← hD1]`. Conclude with `hGu)`. Use the proof step `(fun a => γ (Sum.inl a)) (fun b => γ (Sum.inr b))`. Use the proof step `(by`.

Use function extensionality and compare the values at `a`. Establish `h1` using `hγ (Sum.inl a)`. Simplify using `only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, S.gram] at h1`. Establish `h2 : S.Zh.mulVec (fun b => γ (Sum.inr b)) a = ∑ b, γ (Sum.inr b) * hf L S.Hm (S.f' b) (S.f a)`. Unfold `Matrix.mulVec dotProduct`.

Conclude with `Finset.sum_congr rfl fun b _ => mul_comm _ _`. Rewrite using `[h2, Pi.single_apply]`. Use `split_ifs with ha`. Simplify using `[ha] at h1 ⊢`. Take the linear combination `h1`.

Simplify `h1)` using `[ha]`. Use the proof step `(by`. Use function extensionality and compare the values at `b`. Establish `h1` using `hγ (Sum.inr b)`. Simplify using `only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, S.gram'] at h1`.

Establish `h2 : (S.Zh.map L.cj).transpose.mulVec (fun a => γ (Sum.inl a)) b = ∑ a, γ (Sum.inl a) * hf L S.Hm (S.f a) (S.f' b)`. Unfold `Matrix.mulVec dotProduct`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[hf_conj L S.herm.1]`. Conclude with `mul_comm _ _`.

Rewrite using `[h2, Pi.single_apply]`. Use `split_ifs with ha`. Simplify using `[ha] at h1 ⊢`. Take the linear combination `h1`. Simplify `h1)` using `[ha]`.

Use function extensionality and compare the values at `i`. Break down `i with a | b` into its components or cases. Conclude with `congrFun this.1 a`. Conclude with `congrFun this.2 b)`. Establish `hW : S.W0 = perp L S.Hm (Submodule.span E (Set.range (Sum.elim S.f S.f')))`.

Rewrite using `[← hME]`. Both sides reduce to the same expression. Use `⟨hli, by rw [hW, hME]; exact hco, hc, hU, fun l => ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Unfold `Frames.D lead`. Rewrite using `[hZ]`.

Conclude with `lead_unit _ _ hε _`. Unfold `Frames.th split_ifs`. Conclude with `fun h => S.ϖ_irr.ne_zero (Subtype.ext h)`. Conclude with `one_ne_zero`. Unfold `Frames.th split_ifs`.

Conclude with `S.ϖ.2`. Conclude with `one_mem _`. Establish `: Module.Free E (Submodule.span E (Set.range (Sum.elim S.f S.f')))` using `Module.Free.of_basis (Module.Basis.span hli)`. Take `⟨b⟩` from `basis_of_isCompl hco`. Establish `hn : Module.finrank E (Fin (k + 2 * r + 1) → E) - Module.finrank E (Submodule.span E (Set.range (Sum.elim S.f S.f'))) = k - 1`.

Rewrite using `[Module.finrank_eq_card_basis (Module.Basis.span hli), Module.finrank_fin_fun]`. Simplify using `only [Fintype.card_sum, Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers. Set `b'` to `b.reindex (finCongr hn)`. Use `⟨fun i => (b' i : S.V), b'.linearIndependent.map' (Submodule.subtype _) (Submodule.ker_subtype _), ?_⟩` and prove the remaining obligations.

Rewrite using `[hW]`. Establish `h3` using `congrArg (Submodule.map (Submodule.subtype _)) b'.span_eq`. Rewrite `h3` using `[Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]`. Conclude with `h3.symm`.
-/
theorem frames_basic [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) (r k : ℕ)
    (S : Frames L r k) :
    LinearIndependent E (Sum.elim S.f S.f') ∧ IsCompl S.ME S.W0 ∧
    (∃ c : F, c ≠ 0 ∧ S.G = algebraMap F E c) ∧ IsUnit (S.D (Fin.last (r + 1))) ∧
    (∀ l, S.D l ≠ 0 → IsUnit (S.D l)) ∧ S.th ≠ 0 ∧ S.th ∈ 𝒪[F] ∧
    ∃ b : Fin (k - 1) → S.V, LinearIndependent E b ∧ S.W0 = Submodule.span E (Set.range b) := by
  have := L.free
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; norm_num)
  have : IsArtinianRing E := IsArtinianRing.of_finite F E
  have hZ : S.Zh = Matrix.of fun a b => S.w.mat a b * (-1) ^ (r - (b : ℕ)) := by
    ext a b; exact S.relevant a b
  have hε : ∀ b : Fin (r + 1), IsUnit ((-1 : E) ^ (r - (b : ℕ))) := fun b =>
    (isUnit_one.neg).pow _
  have hD1 : S.D (Fin.last (r + 1)) = S.Zh.det := rfl
  have hD0 : S.D (Fin.last r).castSucc = (S.Zh.submatrix Fin.castSucc Fin.castSucc).det := rfl
  have hU : IsUnit S.Zh.det := by rw [hZ]; exact full_unit _ _ hε
  have hc : ∃ c : F, c ≠ 0 ∧ S.G = algebraMap F E c := by
    have hfix : L.cj S.G = S.G := by
      simp only [Frames.G, map_sub, map_mul, L.cj_cj, AlgEquiv.commutes]; ring
    obtain ⟨c, hc⟩ := (L.cj_fix _).1 hfix
    refine ⟨c, ?_, hc.symm⟩
    rintro rfl
    exact S.G_ne (show S.G = 0 by rw [← hc, map_zero])
  have hGu : IsUnit S.G := by
    obtain ⟨c, h0, hc⟩ := hc
    rw [hc]; exact (IsUnit.mk0 c h0).map _
  have hME : S.ME = Submodule.span E (Set.range (Sum.elim S.f S.f')) := by
    have hs : {i : Fin (r + 1) | (i : ℕ) < r + 1} = Set.univ := by
      ext i; simpa using i.2
    simp only [Frames.ME, Frames.spanTo, hs, Set.image_univ, Set.Sum.elim_range, Submodule.span_union]
  have hdet : ∀ {m : ℕ} (A : Matrix (Fin m) (Fin m) E), (A.map L.cj).transpose.det = L.cj A.det := by
    intro m A
    rw [Matrix.det_transpose]
    exact (AlgEquiv.map_det L.cj A).symm
  obtain ⟨hli, hco⟩ := split_of_gram L S.herm.1 (Sum.elim S.f S.f') (by
    intro γ hγ
    have := solve_zero S.Zh (S.Zh.map L.cj).transpose (algebraMap F E S.T) (algebraMap F E S.T') hU
      (by rw [hdet]; exact hU.map _)
      (by
        have e : ((S.Zh.map L.cj).transpose.submatrix Fin.castSucc Fin.castSucc) =
          ((S.Zh.submatrix Fin.castSucc Fin.castSucc).map L.cj).transpose := rfl
        rw [e, hdet, hdet, ← map_mul, ← hD0, ← hD1]; exact hGu)
      (fun a => γ (Sum.inl a)) (fun b => γ (Sum.inr b))
      (by
        funext a
        have h1 := hγ (Sum.inl a)
        simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, S.gram] at h1
        have h2 : S.Zh.mulVec (fun b => γ (Sum.inr b)) a =
            ∑ b, γ (Sum.inr b) * hf L S.Hm (S.f' b) (S.f a) := by
          unfold Matrix.mulVec dotProduct
          exact Finset.sum_congr rfl fun b _ => mul_comm _ _
        rw [h2, Pi.single_apply]
        split_ifs with ha
        · simp [ha] at h1 ⊢
          linear_combination h1
        · simpa [ha] using h1)
      (by
        funext b
        have h1 := hγ (Sum.inr b)
        simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, S.gram'] at h1
        have h2 : (S.Zh.map L.cj).transpose.mulVec (fun a => γ (Sum.inl a)) b =
            ∑ a, γ (Sum.inl a) * hf L S.Hm (S.f a) (S.f' b) := by
          unfold Matrix.mulVec dotProduct
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [hf_conj L S.herm.1]; exact mul_comm _ _
        rw [h2, Pi.single_apply]
        split_ifs with ha
        · simp [ha] at h1 ⊢
          linear_combination h1
        · simpa [ha] using h1)
    funext i
    rcases i with a | b
    · exact congrFun this.1 a
    · exact congrFun this.2 b)
  have hW : S.W0 = perp L S.Hm (Submodule.span E (Set.range (Sum.elim S.f S.f'))) := by
    rw [← hME]; rfl
  refine ⟨hli, by rw [hW, hME]; exact hco, hc, hU, fun l => ?_, ?_, ?_, ?_⟩
  · unfold Frames.D lead
    rw [hZ]
    exact lead_unit _ _ hε _
  · unfold Frames.th
    split_ifs
    · exact fun h => S.ϖ_irr.ne_zero (Subtype.ext h)
    · exact one_ne_zero
  · unfold Frames.th
    split_ifs
    · exact S.ϖ.2
    · exact one_mem _
  · have : Module.Free E (Submodule.span E (Set.range (Sum.elim S.f S.f'))) :=
      Module.Free.of_basis (Module.Basis.span hli)
    obtain ⟨b⟩ := basis_of_isCompl hco
    have hn : Module.finrank E (Fin (k + 2 * r + 1) → E) -
        Module.finrank E (Submodule.span E (Set.range (Sum.elim S.f S.f'))) = k - 1 := by
      rw [Module.finrank_eq_card_basis (Module.Basis.span hli), Module.finrank_fin_fun]
      simp only [Fintype.card_sum, Fintype.card_fin]; omega
    let b' := b.reindex (finCongr hn)
    refine ⟨fun i => (b' i : S.V), b'.linearIndependent.map' (Submodule.subtype _)
      (Submodule.ker_subtype _), ?_⟩
    rw [hW]
    have h3 := congrArg (Submodule.map (Submodule.subtype _)) b'.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h3
    exact h3.symm

/- English proof (translation)
Introduce `L r k S` and use `frames_basic L r k S`.
-/
theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), LinearIndependent E (Sum.elim S.f S.f') ∧ IsCompl S.ME S.W0 ∧ (∃ c : F, c ≠ 0 ∧ S.G = algebraMap F E c) ∧ IsUnit (S.D (Fin.last (r + 1))) ∧ (∀ l, S.D l ≠ 0 → IsUnit (S.D l)) ∧ S.th ≠ 0 ∧ S.th ∈ 𝒪[F] ∧ ∃ b : Fin (k - 1) → S.V, LinearIndependent E b ∧ S.W0 = Submodule.span E (Set.range b) :=
  fun L r k S => frames_basic L r k S

end GlobalTheory.FrameBasic
