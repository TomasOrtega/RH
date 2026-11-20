import ReciprocityTheory.GroupCohomology.CupCorA

namespace ReciprocityTheory.Coh.CCA

open ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

section Leibniz

variable {R : Type u} [CommRing R] {X V W Z : Type u} [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W] [AddCommGroup Z] [Module R Z]

def hcup (β : V →ₗ[R] W →ₗ[R] Z) (p q : ℕ) (F : (Fin (p + 1) → X) → V) (F' : (Fin (q + 1) → X) → W)
    (x : Fin (p + q + 1) → X) : Z :=
  β (F fun i => x ⟨i, by omega⟩) (F' fun j => x ⟨p + j, by omega⟩)

/- English proof (translation)
Distinguish the cases in `h : (k : ℕ) < i`. Rewrite using `[if_pos h, Fin.succAbove_of_castSucc_lt _ _ (Fin.lt_def.mpr h), Fin.coe_castSucc]`. Rewrite using `[if_neg h, Fin.succAbove_of_le_castSucc _ _ (Fin.le_def.mpr (Nat.le_of_not_lt h)), Fin.val_succ]`.
-/
theorem val_succAbove {n : ℕ} (i : Fin (n + 1)) (k : Fin n) :
    (i.succAbove k : ℕ) = if (k : ℕ) < i then (k : ℕ) else k + 1 := by
  by_cases h : (k : ℕ) < i
  · rw [if_pos h, Fin.succAbove_of_castSucc_lt _ _ (Fin.lt_def.mpr h), Fin.coe_castSucc]
  · rw [if_neg h, Fin.succAbove_of_le_castSucc _ _ (Fin.le_def.mpr (Nat.le_of_not_lt h)),
      Fin.val_succ]

/- English proof (translation)
The claim follows from `congrArg x (Fin.ext h)`.
-/
theorem x_congr {n : ℕ} (x : Fin n → X) (a b : Fin n) (h : (a : ℕ) = b) : x a = x b := congrArg x (Fin.ext h)

/- English proof (translation)
Use function extensionality and compare the values at `x`. Establish `hF'` using `congrFun hF (fun k : Fin (p + 2) => x ⟨k, by omega⟩)`. Simplify using `only [hd, Pi.zero_apply] at hF'`. Rewrite `hF'` using `[Fin.sum_univ_castSucc]`. Establish `e0 : F (fun j => x ⟨((Fin.last (p + 1)).succAbove j : ℕ), by omega⟩) = F (fun i => x ⟨i, by omega⟩)`.

Use `congr 1`. Use function extensionality and compare the values at `k`. Use `congr 1`. Use `ext`. Simplify using `[val_succAbove]`.

Rewrite `hF'` using `[e0]`. Establish `hsum : ∑ a : Fin (p + 1), (-1 : ℤ) ^ (a : ℕ) • F (fun j => x ⟨((Fin.castSucc a).succAbove j : ℕ), by omega⟩) = (-1 : ℤ) ^ p • F (fun i => x ⟨i, by omega⟩)`. Establish `h2` using `eq_neg_of_add_eq_zero_left hF'`. Simplify using `only [Fin.val_castSucc, Fin.val_last] at h2`. Rewrite using `[h2, pow_succ, mul_neg_one, neg_smul, neg_neg]`.

Establish `h : p + 1 + (q + 1) = p + q + 2` using `by omega`. Establish `key : (∑ a : Fin (p + 1), (-1 : ℤ) ^ (a : ℕ) • β (F fun j => x ⟨(a.castSucc.succAbove j : ℕ), by omega⟩) (F' fun j => x ⟨p + 1 + j, by omega⟩)) + ∑ b : Fin (q + 1), (-1 : ℤ) ^ (p + 1 + b : ℕ) • β (F fun i => x ⟨i, by omega⟩) (F' fun j => x ⟨p + (b.succ.succAbove j : ℕ), by omega⟩ …`. Establish `s1 : (∑ a : Fin (p + 1), (-1 : ℤ) ^ (a : ℕ) • β (F fun j => x ⟨(a.castSucc.succAbove j : ℕ), by omega⟩) (F' fun j => x ⟨p + 1 + j, by omega⟩)) = β (∑ a : Fin (p + 1), (-1 : ℤ) ^ (a : ℕ) • F fun j => x ⟨(a.castSucc.succAbove j : ℕ), by omega⟩) (F' fun j => x ⟨p + 1 + j, by omega⟩)`. Simplify using `[map_sum, LinearMap.sum_apply]`. Establish `e1 : (F' fun j => x ⟨p + ((0 : Fin (q + 2)).succAbove j : ℕ), by omega⟩) = F' fun j => x ⟨p + 1 + j, by omega⟩`.

Use `congr 1`. Use function extensionality and compare the values at `k`. Use `congr 1`. Use `ext`. Simplify using `[val_succAbove]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[s1, hsum, e1]`. Simplify using `only [Fin.val_zero, pow_zero, one_smul, map_add, map_sum, map_zsmul, smul_add, Finset.smul_sum, smul_smul, Fin.val_succ, LinearMap.smul_apply]`. Use `congr 1`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Rewrite using `[← pow_add]`. Use `congr 2`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Pi.smul_apply]`. Unfold `hd hcup`.

Use `beta_reduce`. Use `conv_lhs => rw [← (finCongr h).sum_comp, Fin.sum_univ_add]`. Use `conv_rhs => rw [Fin.sum_univ_succ]`. Use `key using 4` and compare the differences between its conclusion and the goal. Apply the tactic sequence `all_goals first`.

Consider the case `(simp; done)`. Consider the case `(congr 2 <;> (try funext k) <;> (try congr 1) <;> (try funext k) <;> (first | apply x_congr | apply Fin.ext) <;>`. Apply the tactic sequence `simp only [val_succAbove, finCongr_apply, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd, Fin.val_castSucc, Fin.val_succ] <;> (try split_ifs) <;>`. Apply the tactic sequence `(try simp only [finCongr_apply, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd, Fin.val_castSucc, Fin.val_succ] at *) <;> omega)`.
-/
theorem hd_hcup (β : V →ₗ[R] W →ₗ[R] Z) (p q : ℕ) (F : (Fin (p + 1) → X) → V)
    (F' : (Fin (q + 1) → X) → W) (hF : hd p F = 0) :
    hd (p + q) (hcup β p q F F') = (-1 : ℤ) ^ p • hcup β p (q + 1) F (hd q F') := by
  funext x
  have hF' := congrFun hF (fun k : Fin (p + 2) => x ⟨k, by omega⟩)
  simp only [hd, Pi.zero_apply] at hF'
  rw [Fin.sum_univ_castSucc] at hF'
  have e0 : F (fun j => x ⟨((Fin.last (p + 1)).succAbove j : ℕ), by omega⟩) =
      F (fun i => x ⟨i, by omega⟩) := by
    congr 1; funext k; congr 1; ext; simp [val_succAbove]
  rw [e0] at hF'
  have hsum : ∑ a : Fin (p + 1), (-1 : ℤ) ^ (a : ℕ) •
      F (fun j => x ⟨((Fin.castSucc a).succAbove j : ℕ), by omega⟩) =
      (-1 : ℤ) ^ p • F (fun i => x ⟨i, by omega⟩) := by
    have h2 := eq_neg_of_add_eq_zero_left hF'
    simp only [Fin.val_castSucc, Fin.val_last] at h2
    rw [h2, pow_succ, mul_neg_one, neg_smul, neg_neg]
  have h : p + 1 + (q + 1) = p + q + 2 := by omega
  have key : (∑ a : Fin (p + 1), (-1 : ℤ) ^ (a : ℕ) •
      β (F fun j => x ⟨(a.castSucc.succAbove j : ℕ), by omega⟩) (F' fun j => x ⟨p + 1 + j, by omega⟩)) +
      ∑ b : Fin (q + 1), (-1 : ℤ) ^ (p + 1 + b : ℕ) • β (F fun i => x ⟨i, by omega⟩)
        (F' fun j => x ⟨p + (b.succ.succAbove j : ℕ), by omega⟩) =
      (-1 : ℤ) ^ p • β (F fun i => x ⟨i, by omega⟩)
        ((-1 : ℤ) ^ ((0 : Fin (q + 2)) : ℕ) • F' (fun j => x ⟨p + ((0 : Fin (q + 2)).succAbove j : ℕ), by omega⟩) +
          ∑ b : Fin (q + 1), (-1 : ℤ) ^ (b.succ : ℕ) • F' (fun j => x ⟨p + (b.succ.succAbove j : ℕ), by omega⟩)) := by
    have s1 : (∑ a : Fin (p + 1), (-1 : ℤ) ^ (a : ℕ) •
        β (F fun j => x ⟨(a.castSucc.succAbove j : ℕ), by omega⟩) (F' fun j => x ⟨p + 1 + j, by omega⟩)) =
        β (∑ a : Fin (p + 1), (-1 : ℤ) ^ (a : ℕ) • F fun j => x ⟨(a.castSucc.succAbove j : ℕ), by omega⟩)
          (F' fun j => x ⟨p + 1 + j, by omega⟩) := by
      simp [map_sum, LinearMap.sum_apply]
    have e1 : (F' fun j => x ⟨p + ((0 : Fin (q + 2)).succAbove j : ℕ), by omega⟩) =
        F' fun j => x ⟨p + 1 + j, by omega⟩ := by
      congr 1; funext k; congr 1; ext; simp [val_succAbove]; omega
    rw [s1, hsum, e1]
    simp only [Fin.val_zero, pow_zero, one_smul, map_add, map_sum, map_zsmul, smul_add, Finset.smul_sum,
      smul_smul, Fin.val_succ, LinearMap.smul_apply]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← pow_add]; congr 2; omega
  rw [Pi.smul_apply]
  unfold hd hcup
  beta_reduce
  conv_lhs => rw [← (finCongr h).sum_comp, Fin.sum_univ_add]
  conv_rhs => rw [Fin.sum_univ_succ]
  convert key using 4
  all_goals first
    | (simp; done)
    | (congr 2 <;> (try funext k) <;> (try congr 1) <;> (try funext k) <;> (first | apply x_congr | apply Fin.ext) <;>
        simp only [val_succAbove, finCongr_apply, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd,
          Fin.val_castSucc, Fin.val_succ] <;> (try split_ifs) <;>
        (try simp only [finCongr_apply, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd,
          Fin.val_castSucc, Fin.val_succ] at *) <;> omega)

end Leibniz

section PartialProd

/- English proof (translation)
Simplify using `only [Fin.partialProd]`. Rewrite using `[List.ofFn_add, List.take_append_of_le_length (by rw [List.length_ofFn]; exact Nat.lt_succ_iff.mp k.isLt)]`. Both sides reduce to the same expression.
-/
theorem pp_trunc {K : Type*} [Monoid K] {p q : ℕ} (g : Fin (p + q) → K) (k : Fin (p + 1)) :
    Fin.partialProd (fun i : Fin p => g (Fin.castAdd q i)) k = Fin.partialProd g ⟨k, by omega⟩ := by
  simp only [Fin.partialProd]
  rw [List.ofFn_add, List.take_append_of_le_length (by rw [List.length_ofFn]; exact Nat.lt_succ_iff.mp k.isLt)]
  rfl

/- English proof (translation)
Simplify using `only [Fin.partialProd]`. Rewrite using `[List.ofFn_add, List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]`. Both sides reduce to the same expression.
-/
theorem prod_castAdd {K : Type*} [Monoid K] {p q : ℕ} (g : Fin (p + q) → K) :
    (List.ofFn fun i : Fin p => g (Fin.castAdd q i)).prod = Fin.partialProd g ⟨p, by omega⟩ := by
  simp only [Fin.partialProd]
  rw [List.ofFn_add, List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]
  rfl

/- English proof (translation)
Rewrite using `[show (⟨p + j + 1, by omega⟩ : Fin (p + q + 1)) = Fin.succ (⟨p + j, by omega⟩ : Fin (p + q)) from Fin.ext rfl, Fin.partialProd_succ]`. Conclude with `inv_mul_cancel_left _ _`.
-/
theorem pp_tail {K : Type*} [Group K] {p q : ℕ} (g : Fin (p + q) → K) (j : Fin q) :
    (Fin.partialProd g ⟨p + j, by omega⟩)⁻¹ * Fin.partialProd g ⟨p + j + 1, by omega⟩ =
      g (Fin.natAdd p j) := by
  rw [show (⟨p + j + 1, by omega⟩ : Fin (p + q + 1)) = Fin.succ (⟨p + j, by omega⟩ : Fin (p + q)) from
    Fin.ext rfl, Fin.partialProd_succ]
  exact inv_mul_cancel_left _ _

/- English proof (translation)
Proceed by induction on `k using Fin.induction with`. Consider the case `zero => rw [Fin.partialProd_zero, h0]`. Consider the case `succ i ih => rw [Fin.partialProd_succ, ih, mul_inv_cancel_left]`.
-/
theorem pp_of_one {K : Type*} [Group K] {n : ℕ} (t : Fin (n + 1) → K) (h0 : t 0 = 1) (k : Fin (n + 1)) :
    Fin.partialProd (fun i : Fin n => (t i.castSucc)⁻¹ * t i.succ) k = t k := by
  induction k using Fin.induction with
  | zero => rw [Fin.partialProd_zero, h0]
  | succ i ih => rw [Fin.partialProd_succ, ih, mul_inv_cancel_left]

end PartialProd

section Homz

variable {R : Type u} [CommRing R]

def homz {K V : Type u} [Group K] [AddCommGroup V] [Module R V] (ρ : Representation R K V) (n : ℕ)
    (f : (Fin n → K) → V) (x : Fin (n + 1) → K) : V :=
  ρ (x 0) (f fun i => (x i.castSucc)⁻¹ * x i.succ)

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {M N P : TRep R G}
  (U : Subgroup G) [U.FiniteIndex]

/- English proof (translation)
Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem resSub_rho_one (M : TRep R G) (v : M.V) : (M.resSub U).rho 1 v = v := by
  simp
  rfl

/- English proof (translation)
Use `haveI : Finite (Quotient (QuotientGroup.rightRel U)) := Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel U).symm`. Use `haveI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel U))`. Establish `hr1 : ∀ c : Quotient (QuotientGroup.rightRel U), retr U c.out = 1`. Introduce `c`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show c.out * (⟦c.out⟧ : Quotient (QuotientGroup.rightRel U)).out⁻¹ = 1`. Rewrite using `[Quotient.out_eq, mul_inv_cancel]`. Establish `h0 : Fin.partialProd g ⟨0, by omega⟩ = 1` using `Fin.partialProd_zero g`. Unfold `cupFun corFun normF`. Simplify using `only [finsum_eq_sum_of_fintype]`.

Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Simplify using `only [hcup, homz, Fin.coe_castSucc, Fin.val_succ, Fin.val_zero, add_zero, hb]`. Establish `hprod : (List.ofFn fun i : Fin p => (retr U (c.out * Fin.partialProd g (Fin.castAdd q i).castSucc))⁻¹ * retr U (c.out * Fin.partialProd g (Fin.castAdd q i).succ)).prod = retr U (c.out * Fin.partialProd g ⟨p, by omega⟩)`. Establish `h1` using `pp_of_one (fun k : Fin (p + 1) => retr U (c.out * Fin.partialProd g ⟨k, by omega⟩)) (by show retr U (c.out * Fin.partialProd g ⟨0, by omega⟩) = 1; rw [h0, mul_one, hr1]) (Fin.last p)`. Use `Eq.trans ?_ h1` and prove the remaining obligations.

Simplify using `only [Fin.partialProd, Fin.val_last]`. Rewrite using `[List.take_of_length_le (by simp)]`. Both sides reduce to the same expression. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv]`. Rewrite using `[hprod, h0, mul_one, hr1]`.

Use `erw [resSub_rho_one]`. Both sides reduce to the same expression.
-/
theorem cor_cup_eq (b : Pairing M N P) (bU : Pairing (M.resSub U) (N.resSub U) (P.resSub U))
    (hb : bU.β = b.β) (p q : ℕ) (f : (Fin p → U) → M.V) (f' : (Fin q → G) → N.V) (g : Fin (p + q) → G) :
    corFun P U (p + q) (cupFun bU p q f (fun h => f' fun i => (h i : G))) g =
      normF P U (p + q) (hcup b.β p q (fun x => homz (M.resSub U).rho p f (fun i => retr U (x i)))
        (fun x => homz N.rho q f' (fun i => (retr U (x i) : G)))) (Fin.partialProd g) := by
  haveI : Finite (Quotient (QuotientGroup.rightRel U)) :=
    Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel U).symm
  haveI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel U))
  have hr1 : ∀ c : Quotient (QuotientGroup.rightRel U), retr U c.out = 1 := by
    intro c
    apply Subtype.ext
    show c.out * (⟦c.out⟧ : Quotient (QuotientGroup.rightRel U)).out⁻¹ = 1
    rw [Quotient.out_eq, mul_inv_cancel]
  have h0 : Fin.partialProd g ⟨0, by omega⟩ = 1 := Fin.partialProd_zero g
  unfold cupFun corFun normF
  simp only [finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [hcup, homz, Fin.coe_castSucc, Fin.val_succ, Fin.val_zero, add_zero, hb]
  have hprod : (List.ofFn fun i : Fin p =>
      (retr U (c.out * Fin.partialProd g (Fin.castAdd q i).castSucc))⁻¹ *
        retr U (c.out * Fin.partialProd g (Fin.castAdd q i).succ)).prod =
      retr U (c.out * Fin.partialProd g ⟨p, by omega⟩) := by
    have h1 := pp_of_one (fun k : Fin (p + 1) => retr U (c.out * Fin.partialProd g ⟨k, by omega⟩))
      (by show retr U (c.out * Fin.partialProd g ⟨0, by omega⟩) = 1; rw [h0, mul_one, hr1])
      (Fin.last p)
    refine Eq.trans ?_ h1
    simp only [Fin.partialProd, Fin.val_last]
    rw [List.take_of_length_le (by simp)]
    rfl
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hprod, h0, mul_one, hr1]
  erw [resSub_rho_one]
  rfl

/- English proof (translation)
Use `haveI : Finite (Quotient (QuotientGroup.rightRel U)) := Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel U).symm`. Use `haveI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel U))`. Establish `hr1 : ∀ c : Quotient (QuotientGroup.rightRel U), retr U c.out = 1`. Introduce `c`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show c.out * (⟦c.out⟧ : Quotient (QuotientGroup.rightRel U)).out⁻¹ = 1`. Rewrite using `[Quotient.out_eq, mul_inv_cancel]`. Establish `htail : ∀ j : Fin q, (Fin.partialProd g ⟨p + ↑j, by omega⟩)⁻¹ * Fin.partialProd g ⟨p + (↑j + 1), by omega⟩ = g (Fin.natAdd p j)` using `fun j => pp_tail g j`. Establish `h0 : Fin.partialProd g ⟨0, by omega⟩ = 1` using `Fin.partialProd_zero g`. Unfold `cupFun corFun normF`.

Simplify using `only [finsum_eq_sum_of_fintype, map_sum, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Simplify using `only [hcup, homz, Fin.coe_castSucc, Fin.val_succ, Fin.val_zero, add_zero]`. Simplify using `only [pp_trunc, Fin.coe_castSucc, Fin.val_succ]`. Rewrite using `[h0, mul_one, hr1]`.

Use `erw [resSub_rho_one]`. Rewrite using `[prod_castAdd]`. Simplify using `only [mul_inv_rev, mul_assoc, inv_mul_cancel_left, htail]`. Rewrite using `[← b.equiv]`. Use `congr 1`.

Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel_left]`.
-/
theorem cup_cor_eq (b : Pairing M N P) (p q : ℕ) (f : (Fin p → U) → M.V) (f' : (Fin q → G) → N.V)
    (g : Fin (p + q) → G) :
    cupFun b p q (corFun M U p f) f' g =
      normF P U (p + q) (hcup b.β p q (fun x => homz (M.resSub U).rho p f (fun i => retr U (x i)))
        (homz N.rho q f')) (Fin.partialProd g) := by
  haveI : Finite (Quotient (QuotientGroup.rightRel U)) :=
    Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel U).symm
  haveI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel U))
  have hr1 : ∀ c : Quotient (QuotientGroup.rightRel U), retr U c.out = 1 := by
    intro c
    apply Subtype.ext
    show c.out * (⟦c.out⟧ : Quotient (QuotientGroup.rightRel U)).out⁻¹ = 1
    rw [Quotient.out_eq, mul_inv_cancel]
  have htail : ∀ j : Fin q, (Fin.partialProd g ⟨p + ↑j, by omega⟩)⁻¹ *
      Fin.partialProd g ⟨p + (↑j + 1), by omega⟩ = g (Fin.natAdd p j) := fun j => pp_tail g j
  have h0 : Fin.partialProd g ⟨0, by omega⟩ = 1 := Fin.partialProd_zero g
  unfold cupFun corFun normF
  simp only [finsum_eq_sum_of_fintype, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [hcup, homz, Fin.coe_castSucc, Fin.val_succ, Fin.val_zero, add_zero]
  simp only [pp_trunc, Fin.coe_castSucc, Fin.val_succ]
  rw [h0, mul_one, hr1]
  erw [resSub_rho_one]
  rw [prod_castAdd]
  simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left, htail]
  rw [← b.equiv]
  congr 1
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_left]

end Homz

section SlopeTestRemainingChoices

variable {R : Type u} [CommRing R]

/- English proof (translation)
Simplify using `only [hcoch] at hF hF' ⊢`. Use `⟨?_, fun g x => ?_⟩` and prove the remaining obligations. Establish `h1 : Continuous (fun x : Fin (p + q + 1) → X => F fun i : Fin (p + 1) => x ⟨i, by omega⟩)` using `hF.1.comp (continuous_pi fun i => continuous_apply _)`. Establish `h2 : Continuous (fun x : Fin (p + q + 1) → X => F' fun j : Fin (q + 1) => x ⟨p + j, by omega⟩)` using `hF'.1.comp (continuous_pi fun j => continuous_apply _)`. Conclude with `b.cont.comp (h1.prodMk h2)`.

Simplify using `only [hcup]`. Rewrite using `[hF.2 g (fun i => x ⟨i, by omega⟩), hF'.2 g (fun j => x ⟨p + j, by omega⟩), b.equiv]`.
-/
theorem hcup_mem {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] {X : Type u}
    [TopologicalSpace X] [MulAction K X] {M N P : TRep R K} (b : Pairing M N P) (p q : ℕ)
    (F : (Fin (p + 1) → X) → M.V) (F' : (Fin (q + 1) → X) → N.V) (hF : F ∈ hcoch M X p)
    (hF' : F' ∈ hcoch N X q) : hcup b.β p q F F' ∈ hcoch P X (p + q) := by
  simp only [hcoch] at hF hF' ⊢
  refine ⟨?_, fun g x => ?_⟩
  · have h1 : Continuous (fun x : Fin (p + q + 1) → X => F fun i : Fin (p + 1) => x ⟨i, by omega⟩) :=
      hF.1.comp (continuous_pi fun i => continuous_apply _)
    have h2 : Continuous
        (fun x : Fin (p + q + 1) → X => F' fun j : Fin (q + 1) => x ⟨p + j, by omega⟩) :=
      hF'.1.comp (continuous_pi fun j => continuous_apply _)
    exact b.cont.comp (h1.prodMk h2)
  · simp only [hcup]
    rw [hF.2 g (fun i => x ⟨i, by omega⟩), hF'.2 g (fun j => x ⟨p + j, by omega⟩), b.equiv]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [hcup, Pi.sub_apply, map_sub]`.
-/
theorem hcup_sub_right {X V W Z : Type u} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    [AddCommGroup Z] [Module R Z] (β : V →ₗ[R] W →ₗ[R] Z) (p q : ℕ) (F : (Fin (p + 1) → X) → V)
    (F₁ F₂ : (Fin (q + 1) → X) → W) :
    hcup β p q F (F₁ - F₂) = hcup β p q F F₁ - hcup β p q F F₂ := by
  funext x
  simp only [hcup, Pi.sub_apply, map_sub]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Unfold `hd`. Simplify using `only [Pi.smul_apply, Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => smul_comm _ _ _`.
-/
theorem hd_zsmul {V X : Type u} [AddCommGroup V] (n : ℕ) (c : ℤ) (F : (Fin (n + 1) → X) → V) :
    hd n (c • F) = c • hd n F := by
  funext x
  unfold hd
  simp only [Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G)

/- English proof (translation)
Simplify using `only [hcoch] at hF ⊢`. Unfold `retr rep`. Establish `hcont : Continuous (fun y : G => (⟦y⟧ : Quotient (QuotientGroup.rightRel U)).out)`. Use `IsLocallyConstant.continuous ?_` and prove the remaining obligations. Rewrite using `[IsLocallyConstant.iff_exists_open]`.

Introduce `x`. Use `⟨(fun y => y * x⁻¹) ⁻¹' (U : Set G), hU.preimage (continuous_mul_right _), by simp, fun y hy => ?_⟩` and prove the remaining obligations. Use `congr 1`. Conclude with `(Quotient.sound (QuotientGroup.rightRel_apply.mpr hy)).symm`. Use `⟨?_, fun g x => ?_⟩` and prove the remaining obligations.

Use `hF.1.comp (continuous_pi fun i => ?_)` and prove the remaining obligations. Conclude with `((continuous_apply i).mul ((hcont.comp (continuous_apply i)).inv)).subtype_mk _`. Establish `hq : ∀ i, (⟦(g : G) * x i⟧ : Quotient (QuotientGroup.rightRel U)) = ⟦x i⟧` using `fun i => Quotient.sound (QuotientGroup.rightRel_apply.mpr (by simp)) dsimp only`. Rewrite using `[← hF.2]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[hq i, Subgroup.smul_def, smul_eq_mul, mul_assoc]`.
-/
theorem retr_pull_mem (hU : IsOpen (U : Set G)) {M : TRep R G} (n : ℕ) (F : (Fin (n + 1) → U) → M.V)
    (hF : F ∈ hcoch (M.resSub U) U n) :
    (fun x : Fin (n + 1) → G => F fun i => retr U (x i)) ∈ hcoch (M.resSub U) G n := by
  simp only [hcoch] at hF ⊢
  unfold retr rep
  have hcont : Continuous (fun y : G => (⟦y⟧ : Quotient (QuotientGroup.rightRel U)).out) := by
    refine IsLocallyConstant.continuous ?_
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨(fun y => y * x⁻¹) ⁻¹' (U : Set G), hU.preimage (continuous_mul_right _), by simp,
      fun y hy => ?_⟩
    congr 1
    exact (Quotient.sound (QuotientGroup.rightRel_apply.mpr hy)).symm
  refine ⟨?_, fun g x => ?_⟩
  · refine hF.1.comp (continuous_pi fun i => ?_)
    exact ((continuous_apply i).mul ((hcont.comp (continuous_apply i)).inv)).subtype_mk _
  · have hq : ∀ i, (⟦(g : G) * x i⟧ : Quotient (QuotientGroup.rightRel U)) = ⟦x i⟧ := fun i =>
      Quotient.sound (QuotientGroup.rightRel_apply.mpr (by simp))
    dsimp only
    rw [← hF.2]
    congr 1
    funext i
    apply Subtype.ext
    simp [hq i, Subgroup.smul_def, smul_eq_mul, mul_assoc]

/- English proof (translation)
Simplify using `only [hcoch] at hF ⊢`. Conclude with `⟨hF.1, fun g x => hF.2 g x⟩`.
-/
theorem res_mem {N : TRep R G} (n : ℕ) (F : (Fin (n + 1) → G) → N.V) (hF : F ∈ hcoch N G n) :
    F ∈ hcoch (N.resSub U) G n := by
  simp only [hcoch] at hF ⊢
  exact ⟨hF.1, fun g x => hF.2 g x⟩

/- English proof (translation)
Use function extensionality and compare the values at `x`. Rewrite using `[h1, hf]`. Establish `ht : (fun i : Fin n => (x i.castSucc)⁻¹ * x i.succ) = fun i : Fin n => ((x 0)⁻¹ * x i.castSucc)⁻¹ * ((x 0)⁻¹ * x i.succ)`. Use function extensionality and compare the values at `i`. Simplify using `only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]`.

Establish `hp : Fin.partialProd (fun i : Fin n => (x i.castSucc)⁻¹ * x i.succ) = fun k => (x 0)⁻¹ * x k`. Use function extensionality and compare the values at `k`. Rewrite using `[ht]`. Conclude with `pp_of_one (fun k => (x 0)⁻¹ * x k) (inv_mul_cancel _) k`. Rewrite using `[hp]`.

Simplify using `only [hcoch] at hF`. Establish `h2` using `hF.2 (x 0) (fun k => (x 0)⁻¹ * x k)`. Simplify using `only [smul_eq_mul, mul_inv_cancel_left] at h2`. Conclude with `h2.symm`.
-/
theorem homog_eq {P : TRep R G} (e : ∀ n, P.coch.X n ≃ₗ[R] hcoch P G n)
    (h1 : ∀ n f x, (e n f).1 x = P.rho (x 0) (f.1 fun i => (x i.castSucc)⁻¹ * x i.succ)) (n : ℕ)
    (f : P.coch.X n) (F : (Fin (n + 1) → G) → P.V) (hF : F ∈ hcoch P G n)
    (hf : ∀ g, f.1 g = F (Fin.partialProd g)) : (e n f).1 = F := by
  funext x
  rw [h1, hf]
  have ht : (fun i : Fin n => (x i.castSucc)⁻¹ * x i.succ) =
      fun i : Fin n => ((x 0)⁻¹ * x i.castSucc)⁻¹ * ((x 0)⁻¹ * x i.succ) := by
    funext i
    simp only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
  have hp : Fin.partialProd (fun i : Fin n => (x i.castSucc)⁻¹ * x i.succ) =
      fun k => (x 0)⁻¹ * x k := by
    funext k
    rw [ht]
    exact pp_of_one (fun k => (x 0)⁻¹ * x k) (inv_mul_cancel _) k
  rw [hp]
  simp only [hcoch] at hF
  have h2 := hF.2 (x 0) (fun k => (x 0)⁻¹ * x k)
  simp only [smul_eq_mul, mul_inv_cancel_left] at h2
  exact h2.symm

variable [U.FiniteIndex]

/- English proof (translation)
Use `haveI : Finite (Quotient (QuotientGroup.rightRel U)) := Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel U).symm`. Use `haveI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel U))`. Use function extensionality and compare the values at `x`. Simplify using `only [normF, Pi.sub_apply, map_sub, finsum_eq_sum_of_fintype, Finset.sum_sub_distrib]`.
-/
theorem normF_sub {M : TRep R G} (n : ℕ) (F F' : (Fin (n + 1) → G) → M.V) :
    normF M U n (F - F') = normF M U n F - normF M U n F' := by
  haveI : Finite (Quotient (QuotientGroup.rightRel U)) :=
    Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel U).symm
  haveI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel U))
  funext x
  simp only [normF, Pi.sub_apply, map_sub, finsum_eq_sum_of_fintype, Finset.sum_sub_distrib]

/- English proof (translation)
Use `haveI : Finite (Quotient (QuotientGroup.rightRel U)) := Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel U).symm`. Use `haveI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel U))`. Use function extensionality and compare the values at `x`. Simplify using `only [normF, Pi.smul_apply, map_zsmul, finsum_eq_sum_of_fintype, Finset.smul_sum]`.
-/
theorem normF_zsmul {M : TRep R G} (n : ℕ) (c : ℤ) (F : (Fin (n + 1) → G) → M.V) :
    normF M U n (c • F) = c • normF M U n F := by
  haveI : Finite (Quotient (QuotientGroup.rightRel U)) :=
    Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel U).symm
  haveI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel U))
  funext x
  simp only [normF, Pi.smul_apply, map_zsmul, finsum_eq_sum_of_fintype, Finset.smul_sum]

end SlopeTestRemainingChoices

end

end ReciprocityTheory.Coh.CCA
