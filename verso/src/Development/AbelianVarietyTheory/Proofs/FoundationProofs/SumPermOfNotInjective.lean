import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.CapelliMain
open Polynomial MeasureTheory

namespace GlobalTheory.CapelliWeyl

/- English proof (translation)
Use `symm`. Establish `e : ∑ p : Equiv.Perm (Fin n), F p = ∑ s ∈ Finset.univ.map (⟨fun p : Equiv.Perm (Fin n) => (p : Fin n → Fin n), DFunLike.coe_injective⟩ : Equiv.Perm (Fin n) ↪ (Fin n → Fin n)), F s`. Rewrite using `[Finset.sum_map]`. Both sides reduce to the same expression. Rewrite using `[e]`.

Use `Finset.sum_subset (Finset.subset_univ _) fun s _ hs => hF s fun hinj => hs ?_` and prove the remaining obligations. Rewrite using `[Finset.mem_map]`. Conclude with `⟨Equiv.ofBijective s (Finite.injective_iff_bijective.mp hinj), Finset.mem_univ _, rfl⟩`.
-/
theorem sum_perm_of_not_injective {M : Type} [AddCommMonoid M] {n : ℕ}
    (F : (Fin n → Fin n) → M) (hF : ∀ s, ¬ Function.Injective s → F s = 0) :
    ∑ s, F s = ∑ p : Equiv.Perm (Fin n), F p := by
  symm
  have e : ∑ p : Equiv.Perm (Fin n), F p = ∑ s ∈ Finset.univ.map
      (⟨fun p : Equiv.Perm (Fin n) => (p : Fin n → Fin n), DFunLike.coe_injective⟩ :
        Equiv.Perm (Fin n) ↪ (Fin n → Fin n)), F s := by
    rw [Finset.sum_map]; rfl
  rw [e]
  refine Finset.sum_subset (Finset.subset_univ _) fun s _ hs => hF s fun hinj => hs ?_
  rw [Finset.mem_map]
  exact ⟨Equiv.ofBijective s (Finite.injective_iff_bijective.mp hinj), Finset.mem_univ _, rfl⟩

/- English proof (translation)
Rewrite using `[Matrix.det_apply, map_sum]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[Units.smul_def, map_zsmul, ← List.prod_ofFn, map_list_prod, List.map_ofFn]`. Both sides reduce to the same expression.
-/
theorem map_det_eq {C W : Type} [CommRing C] [Ring W] {n : ℕ} (f : C →+* W)
    (M : Matrix (Fin n) (Fin n) C) :
    f M.det = ∑ p : Equiv.Perm (Fin n), ((Equiv.Perm.sign p : ℤˣ) : ℤ) •
      (List.ofFn fun j : Fin n => f (M (p j) j)).prod := by
  rw [Matrix.det_apply, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Units.smul_def, map_zsmul, ← List.prod_ofFn, map_list_prod, List.map_ofFn]
  rfl

/- English proof (translation)
Establish `hdet : ∀ s : Fin n → Fin n, ∑ p : Equiv.Perm (Fin n), ((Equiv.Perm.sign p : ℤˣ) : ℤ) • (List.ofFn fun j : Fin n => f (M (s j) (p j))).prod = f (M.submatrix s id).det`. Introduce `s`. Rewrite using `[← Matrix.det_transpose, map_det_eq]`. Both sides reduce to the same expression. Rewrite using `[← map_det_eq]`.

Simplify using `only [Finset.smul_sum]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [← smul_mul_assoc, ← Finset.sum_mul, hdet]`. Rewrite using `[sum_perm_of_not_injective (fun s => f (M.submatrix s id).det * (List.ofFn fun j : Fin n => d (s j) j).prod)]`. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.det_permute, map_mul, map_intCast, mul_assoc, ← zsmul_eq_mul, mul_smul_comm]`. Introduce `s hs`. Simplify using `only [Function.Injective, not_forall] at hs`. Take `⟨i, j, hij, hne⟩` from `hs`.

Rewrite using `[Matrix.det_zero_of_row_eq hne (by funext k; simp [hij]), map_zero, zero_mul]`.
-/
theorem normal_sum_of_map {C W : Type} [CommRing C] [Ring W] {n : ℕ} (f : C →+* W)
    (M : Matrix (Fin n) (Fin n) C) (d : Fin n → Fin n → W) :
    ∑ p : Equiv.Perm (Fin n), ((Equiv.Perm.sign p : ℤˣ) : ℤ) •
      ∑ s : Fin n → Fin n, (List.ofFn fun j : Fin n => f (M (s j) (p j))).prod *
        (List.ofFn fun j : Fin n => d (s j) j).prod =
    (∑ p : Equiv.Perm (Fin n), ((Equiv.Perm.sign p : ℤˣ) : ℤ) •
      (List.ofFn fun j : Fin n => f (M (p j) j)).prod) *
    (∑ p : Equiv.Perm (Fin n), ((Equiv.Perm.sign p : ℤˣ) : ℤ) •
      (List.ofFn fun j : Fin n => d (p j) j).prod) := by
  have hdet : ∀ s : Fin n → Fin n, ∑ p : Equiv.Perm (Fin n), ((Equiv.Perm.sign p : ℤˣ) : ℤ) •
      (List.ofFn fun j : Fin n => f (M (s j) (p j))).prod = f (M.submatrix s id).det := by
    intro s
    rw [← Matrix.det_transpose, map_det_eq]
    rfl
  rw [← map_det_eq]
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]
  simp only [← smul_mul_assoc, ← Finset.sum_mul, hdet]
  rw [sum_perm_of_not_injective
    (fun s => f (M.submatrix s id).det * (List.ofFn fun j : Fin n => d (s j) j).prod)]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Matrix.det_permute, map_mul, map_intCast, mul_assoc, ← zsmul_eq_mul, mul_smul_comm]
  · intro s hs
    simp only [Function.Injective, not_forall] at hs
    obtain ⟨i, j, hij, hne⟩ := hs
    rw [Matrix.det_zero_of_row_eq hne (by funext k; simp [hij]), map_zero, zero_mul]

/- English proof (translation)
Set `S : Set W` to `Set.range fun p : Fin n × Fin n => x p.1 p.2`. Establish `hS : ∀ u ∈ S, ∀ v ∈ S, u * v = v * u`. Introduce and unpack `_ ⟨p, rfl⟩ _ ⟨q, rfl⟩`. Conclude with `(hx _ _ _ _).eq`. Use `letI : CommRing (Subring.closure S) := Subring.closureCommRingOfComm hS`.

Use `⟨(Subring.closure S).subtype.comp (MvPolynomial.eval₂Hom (Int.castRingHom _) (fun p => (⟨x p.1 p.2, Subring.subset_closure ⟨p, rfl⟩⟩ : Subring.closure S))), ?_⟩` and prove the remaining obligations. Introduce `a b`. Rewrite using `[RingHom.comp_apply, MvPolynomial.eval₂Hom_X']`. Both sides reduce to the same expression.
-/
theorem exists_comm_lift {W : Type} [Ring W] {n : ℕ} (x : Fin n → Fin n → W)
    (hx : ∀ a b c e, Commute (x a b) (x c e)) :
    ∃ f : MvPolynomial (Fin n × Fin n) ℤ →+* W, ∀ a b, f (MvPolynomial.X (a, b)) = x a b := by
  let S : Set W := Set.range fun p : Fin n × Fin n => x p.1 p.2
  have hS : ∀ u ∈ S, ∀ v ∈ S, u * v = v * u := by
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    exact (hx _ _ _ _).eq
  letI : CommRing (Subring.closure S) := Subring.closureCommRingOfComm hS
  refine ⟨(Subring.closure S).subtype.comp
    (MvPolynomial.eval₂Hom (Int.castRingHom _)
      (fun p => (⟨x p.1 p.2, Subring.subset_closure ⟨p, rfl⟩⟩ : Subring.closure S))), ?_⟩
  intro a b
  rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
  rfl

/- English proof (translation)
Introduce `W _ n x d hx _ hdx`. Establish `hA` using `PI.HookSteps.Cap.capelli_absolute_value W (Fin n) (Fin n) (fun a t => x t a) (fun b t => d t b) (fun a s b t => (hx _ _ _ _).eq) (fun a s b t => by`. Establish `h` using `hdx t b s a`. Rewrite `h` using `[sub_eq_iff_eq_add']`. Rewrite using `[h]`.

Use `congr 1`. Apply the tactic sequence `refine if_congr ⟨?_, ?_⟩ rfl rfl <;> rintro ⟨h1, h2⟩ <;> exact ⟨h2.symm, h1.symm⟩)`. Use `n id id`. Simplify using `only [smul_sub, Finset.sum_sub_distrib, sub_eq_zero] at hA`. Take `⟨f, hf⟩` from `exists_comm_lift x hx`.

Establish `hB` using `normal_sum_of_map f (Matrix.of fun a b => MvPolynomial.X (a, b)) d`. Simplify using `only [Matrix.of_apply, hf] at hB`. Rewrite using `[← hB]`. Use `Eq.trans ?_ (hA.trans rfl)` and prove the remaining obligations. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations.

Unfold `PI.HookSteps.Cap.Lw PI.HookSteps.Cap.Eop`. Use `congr 3`. Use function extensionality and compare the values at `j`. Establish `hj : 1 + j.val ≤ n` using `by have := j.isLt; omega`. Rewrite using `[Nat.sub_sub, Nat.cast_sub hj, Nat.cast_add, Nat.cast_one, ← sub_sub]`.

Both sides reduce to the same expression.
-/
theorem capelli_identity : ∀ {W : Type} [Ring W] {n : ℕ} (x d : Fin n → Fin n → W), (∀ a b c e, Commute (x a b) (x c e)) → (∀ a b c e, Commute (d a b) (d c e)) → (∀ a b c e, d a b * x c e - x c e * d a b = if a = c ∧ b = e then 1 else 0) → ∑ p : Equiv.Perm (Fin n), ((Equiv.Perm.sign p : ℤˣ) : ℤ) • (List.ofFn fun j : Fin n => (∑ k, x k (p j) * d k j) + if p j = j then ((n - 1 - j.val : ℕ) : W) else 0).prod = (∑ p : Equiv.Perm (Fin n), ((Equiv.Perm.sign p : ℤˣ) : ℤ) • (List.ofFn fun j : Fin n => x (p j) j).prod) * (∑ p : Equiv.Perm (Fin n), ((Equiv.Perm.sign p : ℤˣ) : ℤ) • (List.ofFn fun j : Fin n => d (p j) j).prod) := by
  intro W _ n x d hx _ hdx
  have hA := PI.HookSteps.Cap.capelli_absolute_value W (Fin n) (Fin n) (fun a t => x t a)
    (fun b t => d t b) (fun a s b t => (hx _ _ _ _).eq)
    (fun a s b t => by
      have h := hdx t b s a
      rw [sub_eq_iff_eq_add'] at h
      rw [h]
      congr 1
      refine if_congr ⟨?_, ?_⟩ rfl rfl <;> rintro ⟨h1, h2⟩ <;> exact ⟨h2.symm, h1.symm⟩)
    n id id
  simp only [smul_sub, Finset.sum_sub_distrib, sub_eq_zero] at hA
  obtain ⟨f, hf⟩ := exists_comm_lift x hx
  have hB := normal_sum_of_map f (Matrix.of fun a b => MvPolynomial.X (a, b)) d
  simp only [Matrix.of_apply, hf] at hB
  rw [← hB]
  refine Eq.trans ?_ (hA.trans rfl)
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold PI.HookSteps.Cap.Lw PI.HookSteps.Cap.Eop
  congr 3
  funext j
  have hj : 1 + j.val ≤ n := by have := j.isLt; omega
  rw [Nat.sub_sub, Nat.cast_sub hj, Nat.cast_add, Nat.cast_one, ← sub_sub]
  rfl

end GlobalTheory.CapelliWeyl
