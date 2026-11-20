import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasBoundedSumsOne
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound Matrix

namespace GlobalTheory.SatakeFlip

section Ring

variable {R : Type} [CommRing R] {n : ℕ}

/- English proof (translation)
Rewrite using `[transpose_mul]`. Conclude with `submatrix_mul_equiv Aᵀ Bᵀ Fin.rev Fin.revPerm Fin.rev`.
-/
theorem revT_mul (A B : Matrix (Fin n) (Fin n) R) :
    Aᵀ.submatrix Fin.rev Fin.rev * Bᵀ.submatrix Fin.rev Fin.rev = (B * A)ᵀ.submatrix Fin.rev Fin.rev := by
  rw [transpose_mul]
  exact submatrix_mul_equiv Aᵀ Bᵀ Fin.rev Fin.revPerm Fin.rev

/- English proof (translation)
Rewrite using `[transpose_one]`. Conclude with `submatrix_one_equiv Fin.revPerm`.
-/
theorem revT_one : (1 : Matrix (Fin n) (Fin n) R)ᵀ.submatrix Fin.rev Fin.rev = 1 := by
  rw [transpose_one]
  exact submatrix_one_equiv Fin.revPerm

def invRevT : GL (Fin n) R →* GL (Fin n) R where
  toFun g := ⟨(g⁻¹).valᵀ.submatrix Fin.rev Fin.rev, g.valᵀ.submatrix Fin.rev Fin.rev,
    by rw [revT_mul, Units.mul_inv, revT_one], by rw [revT_mul, Units.inv_mul, revT_one]⟩
  map_one' := Units.ext (by simp only [inv_one, Units.val_one]; exact revT_one)
  map_mul' g h := Units.ext (by simp only [_root_.mul_inv_rev, Units.val_mul]; rw [revT_mul])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem invRevT_apply (g : GL (Fin n) R) (i j : Fin n) :
    (invRevT g).val i j = (g⁻¹).val j.rev i.rev := rfl

/- English proof (translation)
Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Rewrite using `[invRevT_apply, ← map_inv, invRevT_apply, inv_inv, Fin.rev_rev, Fin.rev_rev]`.
-/
theorem invRevT_invRevT (g : GL (Fin n) R) : invRevT (invRevT g) = g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [invRevT_apply, ← map_inv, invRevT_apply, inv_inv, Fin.rev_rev, Fin.rev_rev]

/- English proof (translation)
The claim follows from `(mem_borel R).2 fun _ _ h => (mem_borel R).1 (inv_mem hb) _ _ (Fin.rev_lt_rev.2 h)`.
-/
theorem invRevT_mem_borel {b : GL (Fin n) R} (hb : b ∈ GlobalTheory.SmGL.borel R (Fin n)) :
    invRevT b ∈ GlobalTheory.SmGL.borel R (Fin n) :=
  (mem_borel R).2 fun _ _ h => (mem_borel R).1 (inv_mem hb) _ _ (Fin.rev_lt_rev.2 h)

/- English proof (translation)
Establish `h` using `congrFun (congrFun (Units.inv_mul b) i) i`. Rewrite `h` using `[mul_apply, one_apply_eq, Finset.sum_eq_single i]`. Conclude with `h`. Introduce `j _ hj`. Break down `lt_or_gt_of_ne hj with h' | h'` into its components or cases.

Rewrite using `[(mem_borel R).1 (inv_mem hb) _ _ h', zero_mul]`. Rewrite using `[(mem_borel R).1 hb _ _ h', mul_zero]`. Simplify using the standard rewrite rules.
-/
theorem inv_diag_mul {b : GL (Fin n) R} (hb : b ∈ GlobalTheory.SmGL.borel R (Fin n)) (i : Fin n) :
    (b⁻¹).val i i * b.val i i = 1 := by
  have h := congrFun (congrFun (Units.inv_mul b) i) i
  rw [mul_apply, one_apply_eq, Finset.sum_eq_single i] at h
  · exact h
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h' | h'
    · rw [(mem_borel R).1 (inv_mem hb) _ _ h', zero_mul]
    · rw [(mem_borel R).1 hb _ _ h', mul_zero]
  · simp

end Ring

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

/- English proof (translation)
Take `⟨h1, h2⟩` from `(GlobalTheory.SplitFlip.mem_KO_iff g).1 hg`. Use `(GlobalTheory.SplitFlip.mem_KO_iff _).2 ⟨fun i j => h2 _ _, fun i j => ?_⟩` and prove the remaining obligations. Rewrite using `[← map_inv, invRevT_apply, inv_inv]`. Conclude with `h1 _ _`.
-/
theorem invRevT_mem_KO {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) : invRevT g ∈ KO k (Fin n) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SplitFlip.mem_KO_iff g).1 hg
  refine (GlobalTheory.SplitFlip.mem_KO_iff _).2 ⟨fun i j => h2 _ _, fun i j => ?_⟩
  rw [← map_inv, invRevT_apply, inv_inv]
  exact h1 _ _

/- English proof (translation)
Establish `h` using `ord_mul k x⁻¹ x`. Rewrite `h` using `[inv_mul_cancel, ord_eq_zero (by simp)]`. Use linear arithmetic over natural numbers and integers.
-/
theorem ord_inv_eq_neg (x : kˣ) : ord k x⁻¹ = -ord k x := by
  have h := ord_mul k x⁻¹ x
  rw [inv_mul_cancel, ord_eq_zero (by simp)] at h
  omega

def cosetMap : GL (Fin n) k ⧸ KO k (Fin n) → GL (Fin n) k ⧸ KO k (Fin n) :=
  Quotient.map' invRevT fun a b h => by
    rw [QuotientGroup.leftRel_apply] at h ⊢
    rw [← map_inv, ← map_mul]
    exact invRevT_mem_KO h

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cosetMap_mk (g : GL (Fin n) k) :
    cosetMap (g : GL (Fin n) k ⧸ KO k (Fin n)) = (invRevT g : GL (Fin n) k) := rfl

/- English proof (translation)
Proceed by induction on `c using QuotientGroup.induction_on with`. Consider the case `H g => rw [cosetMap_mk, cosetMap_mk, invRevT_invRevT]`.
-/
theorem cosetMap_cosetMap (c : GL (Fin n) k ⧸ KO k (Fin n)) : cosetMap (cosetMap c) = c := by
  induction c using QuotientGroup.induction_on with
  | H g => rw [cosetMap_mk, cosetMap_mk, invRevT_invRevT]

/- English proof (translation)
Proceed by induction on `c using QuotientGroup.induction_on with`. Consider the case `H g`. Rewrite using `[MulAction.Quotient.smul_mk, cosetMap_mk, cosetMap_mk, MulAction.Quotient.smul_mk, smul_eq_mul, smul_eq_mul, map_mul]`.
-/
theorem cosetMap_smul (x : GL (Fin n) k) (c : GL (Fin n) k ⧸ KO k (Fin n)) :
    cosetMap (x • c) = invRevT x • cosetMap c := by
  induction c using QuotientGroup.induction_on with
  | H g =>
    rw [MulAction.Quotient.smul_mk, cosetMap_mk, cosetMap_mk, MulAction.Quotient.smul_mk, smul_eq_mul,
      smul_eq_mul, map_mul]

/- English proof (translation)
Use `⟨fun g => φ (invRevT g), ⟨fun g x hx => ?_, fun b hb t ht => ?_⟩, fun S hK => ?_⟩` and prove the remaining obligations. Use `show φ (invRevT (g * x)) = φ (invRevT g)`. Rewrite using `[map_mul, h.1 _ _ (invRevT_mem_KO hx)]`. Use `show φ (invRevT b) = _`. Rewrite using `[h.2 _ (invRevT_mem_borel hb) (fun i => (t i.rev)⁻¹) fun i => ?_]`.

Use `Fintype.prod_equiv Fin.revPerm _ _ fun i => ?_` and prove the remaining obligations. Simplify using `only [Fin.revPerm_apply, Fin.rev_rev, ord_inv_eq_neg, _root_.zpow_neg, _root_.inv_zpow]`. Rewrite using `[invRevT_apply, Units.val_inv_eq_inv_val, ← ht]`. Conclude with `eq_inv_of_mul_eq_one_left (inv_diag_mul hb _)`. Establish `hinj : Function.Injective (cosetMap (k` using `k) (n := n)) := Function.LeftInverse.injective cosetMap_cosetMap`.

Establish `h1` using `hS (S.image cosetMap) fun x hx c hc => by`. Take `⟨d, hd, rfl⟩` from `Finset.mem_image.1 hc`. Use `Finset.mem_image.2 ⟨invRevT x • d, hK _ (invRevT_mem_KO hx) _ hd, ?_⟩` and prove the remaining obligations. Rewrite using `[cosetMap_smul, invRevT_invRevT]`. Rewrite `h1` using `[Finset.card_image_of_injective _ hinj, Finset.sum_image fun _ _ _ _ e => hinj e]`.

Use `le_of_eq_of_le (congrArg _ (Finset.sum_congr rfl fun c _ => ?_)) h1` and prove the remaining obligations. Take `⟨x, hx⟩` from `QuotientGroup.mk_out_eq_mul (KO k (Fin n)) (invRevT c.out)`. Rewrite `hx` using `[← cosetMap_mk, QuotientGroup.out_eq']`. Use `show φ (invRevT c.out) = _`. Rewrite using `[hx, h.1 _ _ x.2]`.
-/
theorem exists_isBorelSph_rev_inv (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (γ : Fin n → ℂ) (φ : GL (Fin n) k → ℂ)
    (h : IsBorelSph k γ φ) (hS : HasBoundedSums k φ) :
    ∃ ψ : GL (Fin n) k → ℂ, IsBorelSph k (fun i => (γ (Fin.rev i))⁻¹) ψ ∧ HasBoundedSums k ψ := by
  classical
  refine ⟨fun g => φ (invRevT g), ⟨fun g x hx => ?_, fun b hb t ht => ?_⟩, fun S hK => ?_⟩
  · show φ (invRevT (g * x)) = φ (invRevT g)
    rw [map_mul, h.1 _ _ (invRevT_mem_KO hx)]
  · show φ (invRevT b) = _
    rw [h.2 _ (invRevT_mem_borel hb) (fun i => (t i.rev)⁻¹) fun i => ?_]
    · refine Fintype.prod_equiv Fin.revPerm _ _ fun i => ?_
      simp only [Fin.revPerm_apply, Fin.rev_rev, ord_inv_eq_neg, _root_.zpow_neg, _root_.inv_zpow]
    · rw [invRevT_apply, Units.val_inv_eq_inv_val, ← ht]
      exact eq_inv_of_mul_eq_one_left (inv_diag_mul hb _)
  · have hinj : Function.Injective (cosetMap (k := k) (n := n)) :=
      Function.LeftInverse.injective cosetMap_cosetMap
    have h1 := hS (S.image cosetMap) fun x hx c hc => by
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hc
      refine Finset.mem_image.2 ⟨invRevT x • d, hK _ (invRevT_mem_KO hx) _ hd, ?_⟩
      rw [cosetMap_smul, invRevT_invRevT]
    rw [Finset.card_image_of_injective _ hinj, Finset.sum_image fun _ _ _ _ e => hinj e] at h1
    refine le_of_eq_of_le (congrArg _ (Finset.sum_congr rfl fun c _ => ?_)) h1
    obtain ⟨x, hx⟩ := QuotientGroup.mk_out_eq_mul (KO k (Fin n)) (invRevT c.out)
    rw [← cosetMap_mk, QuotientGroup.out_eq'] at hx
    show φ (invRevT c.out) = _
    rw [hx, h.1 _ _ x.2]

end GlobalTheory.SatakeFlip
