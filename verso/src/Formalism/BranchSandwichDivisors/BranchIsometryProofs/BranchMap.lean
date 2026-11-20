import Mathlib
import Formalism.GradedWeylDivisibility.FinalC
import Formalism.BranchSandwichDivisors.StatementW
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.MemBranchRangeOfDefectEq

open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace Formalism.BranchingDeterminantCap

def bmF {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (E : Fin n → Fin n → Module.End R M) (u : ℤ) (k a i : Fin n) : Module.End R M :=
  (if a = i then ((u + ((k : ℕ) : ℤ) : ℤ) : Module.End R M) else 0) - E a i

def bmM {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (E : Fin n → Fin n → Module.End R M) (u : ℤ) (α β : Fin n → Fin n) : Module.End R M :=
  (List.ofFn fun k => bmF E u k (α k) (β k)).prod

def bmPi {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (E : Fin n → Fin n → Module.End R M) (u : ℤ) (β : Fin n → Fin n) : Module.End R M :=
  ∑ α : Equiv.Perm (Fin n), ((Equiv.Perm.sign α : ℤˣ) : ℤ) • bmM E u α β

def capDet {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (E : Fin n → Fin n → Module.End R M) (u : ℤ) : Module.End R M :=
  bmPi E u id

abbrev BP (R : Type*) [CommRing R] (n : ℕ) := MvPolynomial (Fin (n + 1) × Fin n) R

def bmE (R : Type*) [CommRing R] (n : ℕ) (s t : Fin n) : Derivation R (BP R n) (BP R n) :=
  mkDerivation R fun v => if v.2 = t ∧ v.1 ≠ Fin.last n then X (v.1, s) else 0

def bmZ (R : Type*) [CommRing R] (n : ℕ) (s t : Fin n) : Derivation R (BP R n) (BP R n) :=
  mkDerivation R fun v => if v.2 = t ∧ v.1 = Fin.last n then X (v.1, s) else 0

def bmEL (R : Type*) [CommRing R] (n : ℕ) (s t : Fin n) : Module.End R (BP R n) :=
  (bmE R n s t).toLinearMap

def bmZL (R : Type*) [CommRing R] (n : ℕ) (s t : Fin n) : Module.End R (BP R n) :=
  (bmZ R n s t).toLinearMap

def bmCap (R : Type*) [CommRing R] (n : ℕ) (u : ℤ) : Module.End R (BP R n) :=
  capDet (bmEL R n) u

def zW (n : ℕ) : Fin (n + 1) × Fin n → (Fin n → ℤ) :=
  fun v => if v.1 = Fin.last n then Pi.single v.2 1 else 0

def lastW (n : ℕ) : Fin (n + 1) × Fin n → ℕ := fun v => if v.1 = Fin.last n then 1 else 0

def omg {n : ℕ} (β : Fin n → ℤ) : ℤ := ∑ s : Fin n, ((((s : ℕ) : ℤ)) + 1) * β s

def zcomp (R : Type*) [CommRing R] (n : ℕ) (β : Fin n → ℤ) : Module.End R (BP R n) :=
  weightedHomogeneousComponent (zW n) β

def emb (R : Type*) [CommRing R] (n : ℕ) : MvPolynomial (Fin n × Fin n) R →ₐ[R] BP R n :=
  rename fun v => (v.1.castSucc, v.2)

def zmon (R : Type*) [CommRing R] (n : ℕ) (b : Fin n → ℕ) : BP R n :=
  ∏ s : Fin n, X (Fin.last n, s) ^ b s

def bmChi {n : ℕ} (lam : Fin n → ℕ) (β : Fin n → ℤ) (u : ℤ) : ℤ :=
  ∏ j : Fin n, (u + ((j : ℕ) : ℤ) - ((lam j : ℤ) - β j))

def bmAdm {n : ℕ} (lam : Fin n → ℕ) (d : ℕ) (β : Fin n → ℤ) : Prop :=
  (∀ s, 0 ≤ β s) ∧ ∑ s, β s = (d : ℤ) ∧ Interlace (lamZ lam) (fun i => (lam i : ℤ) - β i)

def IsLow {R : Type*} [CommRing R] {n : ℕ} (D : ℤ) (L : BP R n) : Prop :=
  ∀ m ∈ L.support, omg (Finsupp.weight (zW n) m) < D

def bmLift (R : Type*) [CommRing R] (n : ℕ) (lam b : Fin n → ℕ) (f : MvPolynomial (Fin n × Fin n) R)
    (G : BP R n) : Prop :=
  G ∈ dualWeyl R (n + 1) n lam ∧ IsWeightedHomogeneous (lastW n) G (∑ s, b s) ∧
    IsLow (omg fun s => (b s : ℤ)) (G - zmon R n b * emb R n f)

def bmList {n : ℕ} (lam sg : Fin n → ℕ) : List ℤ :=
  (Finset.univ : Finset (Fin n)).toList.flatMap fun i =>
    ((rset (lamZ lam) (fun i => (sg i : ℤ)) i).erase (sg i : ℤ)).toList.map fun v => v - ((i : ℕ) : ℤ)

def bmZop (R : Type*) [CommRing R] (n : ℕ) (lam sg : Fin n → ℕ) : Module.End R (BP R n) :=
  ((bmList lam sg).map (bmCap R n)).prod

def bmIL {n : ℕ} (lam sg : Fin n → ℕ) : Prop := ∀ i : Fin n, sg i ≤ lam i ∧ nuNext lam i ≤ sg i

def bmRho {n : ℕ} (lam sg : Fin n → ℕ) : Fin (n + 1) → ℕ :=
  fun a => if h : a.val < n then sg ⟨a.val, h⟩ else ∑ s, (lam s - sg s)

/- English proof (translation)
Introduce `d hd`. Apply `hF` to reduce the goal to its premises. Introduce `h0`. Apply `hd` to reduce the goal to its premises. Rewrite using `[coeff_smul, h0, smul_zero]`.
-/
theorem isWeightedHomogeneous_smul {R σ B : Type*} [CommRing R] [AddCommMonoid B] {w : σ → B} {β : B}
    {F : MvPolynomial σ R} (hF : IsWeightedHomogeneous w F β) (c : R) :
    IsWeightedHomogeneous w (c • F) β := by
  intro d hd
  apply hF
  intro h0
  apply hd
  rw [coeff_smul, h0, smul_zero]

/- English proof (translation)
Use extensionality with `d`. Rewrite using `[coeff_weightedHomogeneousComponent]`. Use `split_ifs with hd`. Both sides reduce to the same expression. Assume the negation of the conclusion as `hc`.

Conclude with `hd (h (Ne.symm hc))`.
-/
private theorem bm_whcSame_lemma {R σ B : Type*} [CommRing R] [AddCommMonoid B] {w : σ → B} {m : B}
    {φ : MvPolynomial σ R} (h : IsWeightedHomogeneous w φ m) : weightedHomogeneousComponent w m φ = φ := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent]
  split_ifs with hd
  · rfl
  · by_contra hc
    exact hd (h (Ne.symm hc))

/- English proof (translation)
Use extensionality with `d`. Rewrite using `[coeff_weightedHomogeneousComponent, coeff_zero]`. Use `split_ifs with hd`. Assume the negation of the conclusion as `hc`. Conclude with `hk (hd.symm.trans (h hc))`.

Both sides reduce to the same expression.
-/
private theorem bm_whcNe_lemma_2 {R σ B : Type*} [CommRing R] [AddCommMonoid B] {w : σ → B} {m : B}
    {φ : MvPolynomial σ R} (h : IsWeightedHomogeneous w φ m) {k : B} (hk : k ≠ m) :
    weightedHomogeneousComponent w k φ = 0 := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_zero]
  split_ifs with hd
  · by_contra hc
    exact hk (hd.symm.trans (h hc))
  · rfl

/- English proof (translation)
Introduce `d hd`. Rewrite `hd` using `[coeff_weightedHomogeneousComponent]`. Use `split_ifs at hd with h`. Conclude with `h`. Conclude with `absurd rfl hd`.
-/
private theorem bm_whcWH_lemma_3 {R σ B : Type*} [CommRing R] [AddCommMonoid B] (w : σ → B) (m : B)
    (φ : MvPolynomial σ R) : IsWeightedHomogeneous w (weightedHomogeneousComponent w m φ) m := by
  classical
  intro d hd
  rw [coeff_weightedHomogeneousComponent] at hd
  split_ifs at hd with h
  · exact h
  · exact absurd rfl hd

/- English proof (translation)
Proceed by induction on `F using MvPolynomial.induction_on' with`. Consider the case `monomial u a`. Establish `hm : monomial u a = a • monomial u (1 : R)`. Rewrite using `[smul_monomial, smul_eq_mul, mul_one]`. Establish `hDa : IsWeightedHomogeneous w (D (monomial u a)) (Finsupp.weight w u + δ)`.

Rewrite using `[hm, map_smul]`. Conclude with `isWeightedHomogeneous_smul (hD u) a`. Establish `hma : IsWeightedHomogeneous w (monomial u a) (Finsupp.weight w u)` using `isWeightedHomogeneous_monomial w u a rfl`. Distinguish the cases in `h : Finsupp.weight w u = β`. Substitute `h` using the available equality.

Rewrite using `[bm_whcSame_lemma hDa, bm_whcSame_lemma hma]`. Rewrite using `[bm_whcNe_lemma_2 hDa (fun h' => h (add_right_cancel h').symm), bm_whcNe_lemma_2 hma (Ne.symm h), map_zero]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`.
-/
theorem bm_whc_shift {R σ B : Type*} [CommRing R] [AddCommMonoid B] [IsRightCancelAdd B] (w : σ → B) (δ : B)
    (D : MvPolynomial σ R →ₗ[R] MvPolynomial σ R)
    (hD : ∀ m, IsWeightedHomogeneous w (D (monomial m 1)) (Finsupp.weight w m + δ)) (β : B)
    (F : MvPolynomial σ R) :
    weightedHomogeneousComponent w (β + δ) (D F) = D (weightedHomogeneousComponent w β F) := by
  induction F using MvPolynomial.induction_on' with
  | monomial u a =>
    have hm : monomial u a = a • monomial u (1 : R) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    have hDa : IsWeightedHomogeneous w (D (monomial u a)) (Finsupp.weight w u + δ) := by
      rw [hm, map_smul]
      exact isWeightedHomogeneous_smul (hD u) a
    have hma : IsWeightedHomogeneous w (monomial u a) (Finsupp.weight w u) :=
      isWeightedHomogeneous_monomial w u a rfl
    by_cases h : Finsupp.weight w u = β
    · subst h
      rw [bm_whcSame_lemma hDa, bm_whcSame_lemma hma]
    · rw [bm_whcNe_lemma_2 hDa (fun h' => h (add_right_cancel h').symm), bm_whcNe_lemma_2 hma (Ne.symm h),
        map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]

/- English proof (translation)
Establish `h1 : x F = weightedHomogeneousComponent w β (x F)` using `by conv_lhs => rw [← bm_whcSame_lemma hF]`. Conclude with `(LinearMap.congr_fun hx.eq F).symm`. Rewrite using `[h1]`. Conclude with `bm_whcWH_lemma_3 w β (x F)`.
-/
theorem bm_isWH_of_comm {R σ B : Type*} [CommRing R] [AddCommMonoid B] (w : σ → B) (β : B)
    (x : Module.End R (MvPolynomial σ R))
    (hx : Commute (weightedHomogeneousComponent w β : Module.End R (MvPolynomial σ R)) x)
    (F : MvPolynomial σ R) (hF : IsWeightedHomogeneous w F β) : IsWeightedHomogeneous w (x F) β := by
  have h1 : x F = weightedHomogeneousComponent w β (x F) := by
    conv_lhs => rw [← bm_whcSame_lemma hF]
    exact (LinearMap.congr_fun hx.eq F).symm
  rw [h1]
  exact bm_whcWH_lemma_3 w β (x F)

/- English proof (translation)
Rewrite using `[mkDerivation_monomial, one_smul, Finsupp.sum]`. Use `IsWeightedHomogeneous.sum _ _ _ fun i hi => ?_` and prove the remaining obligations. Establish `hm : 1 ≤ m i` using `Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)`. Establish `hsplit : m = (m - Finsupp.single i 1) + Finsupp.single i 1` using `(tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hm)).symm`. Establish `hw1 : Finsupp.weight w (Finsupp.single i 1) = w i`.

Simplify using `[Finsupp.weight_apply]`. Establish `e : Finsupp.weight w m + δ = Finsupp.weight w (m - Finsupp.single i 1) + (w i + δ)` using `by conv_lhs => rw [hsplit]`. Rewrite using `[map_add, hw1, add_assoc]`. Rewrite using `[e, smul_eq_mul]`. Conclude with `(isWeightedHomogeneous_monomial _ _ _ rfl).mul (hf i)`.
-/
theorem bm_deriv_monomial_WH {R σ B : Type*} [CommRing R] [AddCommMonoid B] (w : σ → B) (δ : B)
    (f : σ → MvPolynomial σ R) (hf : ∀ v, IsWeightedHomogeneous w (f v) (w v + δ)) (m : σ →₀ ℕ) :
    IsWeightedHomogeneous w (mkDerivation R f (monomial m 1)) (Finsupp.weight w m + δ) := by
  rw [mkDerivation_monomial, one_smul, Finsupp.sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun i hi => ?_
  have hm : 1 ≤ m i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
  have hsplit : m = (m - Finsupp.single i 1) + Finsupp.single i 1 :=
    (tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hm)).symm
  have hw1 : Finsupp.weight w (Finsupp.single i 1) = w i := by
    simp [Finsupp.weight_apply]
  have e : Finsupp.weight w m + δ = Finsupp.weight w (m - Finsupp.single i 1) + (w i + δ) := by
    conv_lhs => rw [hsplit]
    rw [map_add, hw1, add_assoc]
  rw [e, smul_eq_mul]
  exact (isWeightedHomogeneous_monomial _ _ _ rfl).mul (hf i)

/- English proof (translation)
Rewrite using `[aeval_monomial, map_one, one_mul, Finsupp.prod, Finsupp.weight_apply, Finsupp.sum]`. Conclude with `IsWeightedHomogeneous.prod _ _ _ fun i _ => (hh i).pow (m i)`.
-/
theorem bm_aeval_monomial_WH {R σ B : Type*} [CommRing R] [AddCommMonoid B] (w : σ → B)
    (h : σ → MvPolynomial σ R) (hh : ∀ v, IsWeightedHomogeneous w (h v) (w v)) (m : σ →₀ ℕ) :
    IsWeightedHomogeneous w (aeval h (monomial m (1 : R))) (Finsupp.weight w m) := by
  rw [aeval_monomial, map_one, one_mul, Finsupp.prod, Finsupp.weight_apply, Finsupp.sum]
  exact IsWeightedHomogeneous.prod _ _ _ fun i _ => (hh i).pow (m i)

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype m (fun i c => c • zW n i) (fun _ => zero_smul _ _), Finset.sum_apply, Fintype.sum_prod_type, Fin.sum_univ_castSucc]`. Simplify using `[zW, Pi.single_apply, Fin.castSucc_ne_last]`.
-/
theorem bm_weight_zW {n : ℕ} (m : Fin (n + 1) × Fin n →₀ ℕ) (s : Fin n) :
    Finsupp.weight (zW n) m s = (m (Fin.last n, s) : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype m (fun i c => c • zW n i) (fun _ => zero_smul _ _), Finset.sum_apply,
    Fintype.sum_prod_type, Fin.sum_univ_castSucc]
  simp [zW, Pi.single_apply, Fin.castSucc_ne_last]

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype m (fun i c => c • rowW r n i) (fun _ => zero_smul _ _), Finset.sum_apply, Fintype.sum_prod_type, Finset.sum_comm]`. Simplify using `[rowW, rowDeg, Pi.single_apply]`.
-/
theorem bm_weight_rowW {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) (a : Fin r) :
    Finsupp.weight (rowW r n) m a = rowDeg m a := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype m (fun i c => c • rowW r n i) (fun _ => zero_smul _ _), Finset.sum_apply,
    Fintype.sum_prod_type, Finset.sum_comm]
  simp [rowW, rowDeg, Pi.single_apply]

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype m (fun i c => c • lastW n i) (fun _ => zero_smul _ _), Fintype.sum_prod_type, Fin.sum_univ_castSucc]`. Simplify using `[lastW, rowDeg, Fin.castSucc_ne_last]`.
-/
theorem bm_weight_lastW {n : ℕ} (m : Fin (n + 1) × Fin n →₀ ℕ) :
    Finsupp.weight (lastW n) m = rowDeg m (Fin.last n) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype m (fun i c => c • lastW n i) (fun _ => zero_smul _ _),
    Fintype.sum_prod_type, Fin.sum_univ_castSucc]
  simp [lastW, rowDeg, Fin.castSucc_ne_last]

/- English proof (translation)
Use `LinearMap.ext fun F => ?_` and prove the remaining obligations. Use `show weightedHomogeneousComponent w β (D F) = D (weightedHomogeneousComponent w β F)`. Proceed by induction on `F using MvPolynomial.induction_on' with`. Consider the case `monomial u a`. Establish `hm : monomial u a = a • monomial u (1 : R)`.

Rewrite using `[smul_monomial, smul_eq_mul, mul_one]`. Establish `hDa : IsWeightedHomogeneous w (D (monomial u a)) (Finsupp.weight w u)`. Rewrite using `[hm, map_smul]`. Conclude with `isWeightedHomogeneous_smul (hD u) a`. Establish `hma : IsWeightedHomogeneous w (monomial u a) (Finsupp.weight w u)` using `isWeightedHomogeneous_monomial w u a rfl`.

Distinguish the cases in `h : Finsupp.weight w u = β`. Substitute `h` using the available equality. Rewrite using `[bm_whcSame_lemma hDa, bm_whcSame_lemma hma]`. Rewrite using `[bm_whcNe_lemma_2 hDa (Ne.symm h), bm_whcNe_lemma_2 hma (Ne.symm h), map_zero]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`.
-/
theorem commute_weightedComponent_of_monomial {R σ B : Type*} [CommRing R] [AddCommMonoid B] [IsRightCancelAdd B] (w : σ → B)
    (D : Module.End R (MvPolynomial σ R))
    (hD : ∀ m, IsWeightedHomogeneous w (D (monomial m 1)) (Finsupp.weight w m)) (β : B) :
    Commute (weightedHomogeneousComponent w β : Module.End R (MvPolynomial σ R)) D := by
  refine LinearMap.ext fun F => ?_
  show weightedHomogeneousComponent w β (D F) = D (weightedHomogeneousComponent w β F)
  induction F using MvPolynomial.induction_on' with
  | monomial u a =>
    have hm : monomial u a = a • monomial u (1 : R) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    have hDa : IsWeightedHomogeneous w (D (monomial u a)) (Finsupp.weight w u) := by
      rw [hm, map_smul]
      exact isWeightedHomogeneous_smul (hD u) a
    have hma : IsWeightedHomogeneous w (monomial u a) (Finsupp.weight w u) :=
      isWeightedHomogeneous_monomial w u a rfl
    by_cases h : Finsupp.weight w u = β
    · subst h
      rw [bm_whcSame_lemma hDa, bm_whcSame_lemma hma]
    · rw [bm_whcNe_lemma_2 hDa (Ne.symm h), bm_whcNe_lemma_2 hma (Ne.symm h), map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]

/- English proof (translation)
Establish `hf : ∀ v : Fin (n + 1) × Fin n, IsWeightedHomogeneous w ((fun v : Fin (n + 1) × Fin n => if v.2 = t ∧ v.1 ≠ Fin.last n then (X (v.1, s) : BP R n) else 0) v) (w v + 0)`. Introduce `v`. Simplify using `only`. Use `split_ifs with hv`. Establish `e : w v + 0 = w (v.1, s)`.

Rewrite using `[add_zero, hw v.1 s t hv.2, ← hv.1]`. Rewrite using `[e]`. Apply `isWeightedHomogeneous_X` to reduce the goal to its premises. Apply `isWeightedHomogeneous_zero` to reduce the goal to its premises. Establish `key` using `bm_deriv_monomial_WH (R := R) w 0 _ hf m`.

Rewrite `key` using `[add_zero]`. Conclude with `key`.
-/
theorem elemDeriv_monomial_weighted (R : Type*) [CommRing R] (n : ℕ) {B : Type*} [AddCommMonoid B]
    (w : Fin (n + 1) × Fin n → B) (hw : ∀ (a : Fin (n + 1)) (s t : Fin n), a ≠ Fin.last n → w (a, s) = w (a, t))
    (s t : Fin n) (m : Fin (n + 1) × Fin n →₀ ℕ) :
    IsWeightedHomogeneous w (bmEL R n s t (monomial m 1)) (Finsupp.weight w m) := by
  have hf : ∀ v : Fin (n + 1) × Fin n, IsWeightedHomogeneous w
      ((fun v : Fin (n + 1) × Fin n => if v.2 = t ∧ v.1 ≠ Fin.last n then (X (v.1, s) : BP R n) else 0) v)
      (w v + 0) := by
    intro v
    dsimp only
    split_ifs with hv
    · have e : w v + 0 = w (v.1, s) := by
        rw [add_zero, hw v.1 s t hv.2, ← hv.1]
      rw [e]
      apply isWeightedHomogeneous_X
    · apply isWeightedHomogeneous_zero
  have key := bm_deriv_monomial_WH (R := R) w 0 _ hf m
  rw [add_zero] at key
  exact key

/- English proof (translation)
Conclude with `commute_weightedComponent_of_monomial (zW n) (bmEL R n s t) (elemDeriv_monomial_weighted R n (zW n) (fun a s t ha => by simp [zW, ha]) s t) β`.
-/
theorem bm_zcomp_comm_bmEL (R : Type*) [CommRing R] (n : ℕ) (β : Fin n → ℤ) (s t : Fin n) :
    Commute (zcomp R n β) (bmEL R n s t) := by
  exact commute_weightedComponent_of_monomial (zW n) (bmEL R n s t)
    (elemDeriv_monomial_weighted R n (zW n) (fun a s t ha => by simp [zW, ha]) s t) β

/- English proof (translation)
Establish `hf : ∀ v : Fin (n + 1) × Fin n, IsWeightedHomogeneous (zW n) ((fun v : Fin (n + 1) × Fin n => if v.2 = j ∧ v.1 = Fin.last n then (X (v.1, l) : BP R n) else 0) v) (zW n v + (Pi.single l 1 - Pi.single j 1))`. Introduce `v`. Simplify using `only`. Use `split_ifs with hv`. Establish `e : zW n v + (Pi.single l 1 - Pi.single j 1) = zW n (v.1, l)`.

Take `⟨a, b⟩` from `v`. Simplify using `only at hv`. Take `⟨rfl, rfl⟩` from `hv`. Simplify using `[zW]`. Rewrite using `[e]`.

Apply `isWeightedHomogeneous_X` to reduce the goal to its premises. Apply `isWeightedHomogeneous_zero` to reduce the goal to its premises. Conclude with `bm_whc_shift (zW n) _ (bmZ R n l j).toLinearMap (fun m => bm_deriv_monomial_WH (zW n) _ _ hf m) β F`.
-/
theorem bm_zcomp_bmZ (R : Type*) [CommRing R] (n : ℕ) (β : Fin n → ℤ) (l j : Fin n) (F : BP R n) :
    zcomp R n (β + (Pi.single l 1 - Pi.single j 1)) (bmZ R n l j F) = bmZ R n l j (zcomp R n β F) := by
  have hf : ∀ v : Fin (n + 1) × Fin n, IsWeightedHomogeneous (zW n)
      ((fun v : Fin (n + 1) × Fin n => if v.2 = j ∧ v.1 = Fin.last n then (X (v.1, l) : BP R n) else 0) v)
      (zW n v + (Pi.single l 1 - Pi.single j 1)) := by
    intro v
    dsimp only
    split_ifs with hv
    · have e : zW n v + (Pi.single l 1 - Pi.single j 1) = zW n (v.1, l) := by
        obtain ⟨a, b⟩ := v
        simp only at hv
        obtain ⟨rfl, rfl⟩ := hv
        simp [zW]
      rw [e]
      apply isWeightedHomogeneous_X
    · apply isWeightedHomogeneous_zero
  exact bm_whc_shift (zW n) _ (bmZ R n l j).toLinearMap (fun m => bm_deriv_monomial_WH (zW n) _ _ hf m) β F

/- English proof (translation)
Conclude with `commute_weightedComponent_of_monomial (lastW n) (bmEL R n s t) (elemDeriv_monomial_weighted R n (lastW n) (fun a s t _ => rfl) s t) d`.
-/
theorem bm_lastcomp_comm_bmEL (R : Type*) [CommRing R] (n : ℕ) (d : ℕ) (s t : Fin n) :
    Commute (weightedHomogeneousComponent (lastW n) d : Module.End R (BP R n)) (bmEL R n s t) := by
  exact commute_weightedComponent_of_monomial (lastW n) (bmEL R n s t) (elemDeriv_monomial_weighted R n (lastW n) (fun a s t _ => rfl) s t) d

/- English proof (translation)
Conclude with `commute_weightedComponent_of_monomial (rowW (n + 1) n) (bmEL R n s t) (elemDeriv_monomial_weighted R n (rowW (n + 1) n) (fun a s t _ => rfl) s t) ρ`.
-/
theorem bm_rowcomp_comm_bmEL (R : Type*) [CommRing R] (n : ℕ) (ρ : Fin (n + 1) → ℕ) (s t : Fin n) :
    Commute (weightedHomogeneousComponent (rowW (n + 1) n) ρ : Module.End R (BP R n)) (bmEL R n s t) := by
  exact commute_weightedComponent_of_monomial (rowW (n + 1) n) (bmEL R n s t)
    (elemDeriv_monomial_weighted R n (rowW (n + 1) n) (fun a s t _ => rfl) s t) ρ

/- English proof (translation)
Unfold `bmE`. Conclude with `mkDerivation_X R _ v`.
-/
theorem elemDeriv_X (R : Type*) [CommRing R] (n : ℕ) (s t : Fin n) (v : Fin (n + 1) × Fin n) :
    bmE R n s t (X v) = if v.2 = t ∧ v.1 ≠ Fin.last n then X (v.1, s) else 0 := by
  unfold bmE
  exact mkDerivation_X R _ v

/- English proof (translation)
Unfold `bmZ`. Conclude with `mkDerivation_X R _ v`.
-/
theorem lastRowDeriv_X (R : Type*) [CommRing R] (n : ℕ) (s t : Fin n) (v : Fin (n + 1) × Fin n) :
    bmZ R n s t (X v) = if v.2 = t ∧ v.1 = Fin.last n then X (v.1, s) else 0 := by
  unfold bmZ
  exact mkDerivation_X R _ v

/- English proof (translation)
Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem ite_derivation_apply {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (c : Prop) [Decidable c]
    (D : Derivation R A A) (x : A) : (if c then D else 0) x = if c then D x else 0 := by
  split_ifs <;> simp

/- English proof (translation)
Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem derivation_apply_ite {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (c : Prop) [Decidable c]
    (D : Derivation R A A) (x : A) : D (if c then x else 0) = if c then D x else 0 := by
  split_ifs <;> simp

/- English proof (translation)
Use `MvPolynomial.derivation_ext fun v => ?_` and prove the remaining obligations. Rewrite using `[Derivation.commutator_apply, Derivation.sub_apply, ite_derivation_apply, ite_derivation_apply]`. Simplify using `only [elemDeriv_X, derivation_apply_ite, map_zero]`. Apply the tactic sequence `by_cases h1 : v.2 = l <;> by_cases h2 : v.2 = j <;> by_cases h3 : j = k <;> by_cases h4 : i = l <;>`. Apply the tactic sequence `by_cases h5 : v.1 = Fin.last n <;> simp_all`.

Apply the tactic sequence `all_goals (try (intros; simp_all))`.
-/
theorem elemDeriv_lie_bracket (R : Type*) [CommRing R] (n : ℕ) (i j k l : Fin n) :
    ⁅bmE R n i j, bmE R n k l⁆ =
      (if j = k then bmE R n i l else 0) - (if i = l then bmE R n k j else 0) := by
  refine MvPolynomial.derivation_ext fun v => ?_
  rw [Derivation.commutator_apply, Derivation.sub_apply, ite_derivation_apply, ite_derivation_apply]
  simp only [elemDeriv_X, derivation_apply_ite, map_zero]
  by_cases h1 : v.2 = l <;> by_cases h2 : v.2 = j <;> by_cases h3 : j = k <;> by_cases h4 : i = l <;>
    by_cases h5 : v.1 = Fin.last n <;> simp_all
  all_goals (try (intros; simp_all))

/- English proof (translation)
Use `MvPolynomial.derivation_ext fun v => ?_` and prove the remaining obligations. Rewrite using `[Derivation.commutator_apply]`. Simplify using `only [elemDeriv_X, lastRowDeriv_X, derivation_apply_ite, map_zero, Derivation.zero_apply]`. Apply the tactic sequence `by_cases h1 : v.1 = Fin.last n <;> simp [h1]`.
-/
theorem lastRowDeriv_elemDeriv_commute (R : Type*) [CommRing R] (n : ℕ) (l j s t : Fin n) :
    ⁅bmZ R n l j, bmE R n s t⁆ = 0 := by
  refine MvPolynomial.derivation_ext fun v => ?_
  rw [Derivation.commutator_apply]
  simp only [elemDeriv_X, lastRowDeriv_X, derivation_apply_ite, map_zero, Derivation.zero_apply]
  by_cases h1 : v.1 = Fin.last n <;> simp [h1]

/- English proof (translation)
Use `LinearMap.ext fun F => ?_` and prove the remaining obligations. Establish `h` using `congrArg (fun D : Derivation R (BP R n) (BP R n) => D F) (elemDeriv_lie_bracket R n i j k l)`. Simplify using `only [Derivation.commutator_apply] at h`. Use `show bmE R n i j (bmE R n k l F) - bmE R n k l (bmE R n i j F) = _`. Rewrite using `[h]`.

Apply the tactic sequence `split_ifs <;> simp [bmEL]`.
-/
theorem bmEL_rel (R : Type*) [CommRing R] (n : ℕ) (i j k l : Fin n) :
    bmEL R n i j * bmEL R n k l - bmEL R n k l * bmEL R n i j =
      (if j = k then bmEL R n i l else 0) - (if i = l then bmEL R n k j else 0) := by
  refine LinearMap.ext fun F => ?_
  have h := congrArg (fun D : Derivation R (BP R n) (BP R n) => D F) (elemDeriv_lie_bracket R n i j k l)
  simp only [Derivation.commutator_apply] at h
  show bmE R n i j (bmE R n k l F) - bmE R n k l (bmE R n i j F) = _
  rw [h]
  split_ifs <;> simp [bmEL]

/- English proof (translation)
Use `MvPolynomial.derivation_ext fun v => ?_` and prove the remaining obligations. Rewrite using `[Derivation.add_apply]`. Simplify using `only [ndE, bmE, bmZ, mkDerivation_X]`. Apply the tactic sequence `by_cases h1 : v.2 = j <;> by_cases h2 : v.1 = Fin.last n <;> simp [h1, h2]`.
-/
theorem bm_ndE_eq (R : Type*) [CommRing R] (n : ℕ) (l j : Fin n) :
    ndE R (n + 1) n l j = bmE R n l j + bmZ R n l j := by
  refine MvPolynomial.derivation_ext fun v => ?_
  rw [Derivation.add_apply]
  simp only [ndE, bmE, bmZ, mkDerivation_X]
  by_cases h1 : v.2 = j <;> by_cases h2 : v.1 = Fin.last n <;> simp [h1, h2]

/- English proof (translation)
Use `MvPolynomial.derivation_ext fun v => ?_` and prove the remaining obligations. Rewrite using `[Derivation.add_apply]`. Simplify using `only [ndF, bmE, bmZ, mkDerivation_X]`. Apply the tactic sequence `by_cases h1 : v.2 = l <;> by_cases h2 : v.1 = Fin.last n <;> simp [h1, h2]`.
-/
theorem bm_ndF_eq (R : Type*) [CommRing R] (n : ℕ) (l j : Fin n) :
    ndF R (n + 1) n l j = bmE R n j l + bmZ R n j l := by
  refine MvPolynomial.derivation_ext fun v => ?_
  rw [Derivation.add_apply]
  simp only [ndF, bmE, bmZ, mkDerivation_X]
  by_cases h1 : v.2 = l <;> by_cases h2 : v.1 = Fin.last n <;> simp [h1, h2]

/- English proof (translation)
Use `MvPolynomial.derivation_ext fun v => ?_` and prove the remaining obligations. Simplify using `only [ndE, ndEul, mkDerivation_X, colW]`. Distinguish the cases in `h : v.2 = s`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[h, Pi.single_apply, Ne.symm h]`.
-/
theorem bm_ndE_self (R : Type*) [CommRing R] (r n : ℕ) (s : Fin n) : ndE R r n s s = ndEul R r n s := by
  refine MvPolynomial.derivation_ext fun v => ?_
  simp only [ndE, ndEul, mkDerivation_X, colW]
  by_cases h : v.2 = s
  · subst h
    simp
  · simp [h, Pi.single_apply, Ne.symm h]

/- English proof (translation)
Rewrite using `[← bm_ndE_self R (n + 1) n s, bm_ndE_eq]`.
-/
theorem bm_ndEul_eq (R : Type*) [CommRing R] (n : ℕ) (s : Fin n) :
    ndEul R (n + 1) n s = bmE R n s s + bmZ R n s s := by
  rw [← bm_ndE_self R (n + 1) n s, bm_ndE_eq]

/- English proof (translation)
Use `LinearMap.ext fun F => ?_` and prove the remaining obligations. Establish `h` using `congrArg (fun D : Derivation R (BP R n) (BP R n) => D F) (lastRowDeriv_elemDeriv_commute R n l j s t)`. Simplify using `only [Derivation.commutator_apply, Derivation.zero_apply] at h`. Conclude with `sub_eq_zero.mp h`.
-/
theorem bmZL_comm_bmEL (R : Type*) [CommRing R] (n : ℕ) (l j s t : Fin n) :
    Commute (bmZL R n l j) (bmEL R n s t) := by
  refine LinearMap.ext fun F => ?_
  have h := congrArg (fun D : Derivation R (BP R n) (BP R n) => D F) (lastRowDeriv_elemDeriv_commute R n l j s t)
  simp only [Derivation.commutator_apply, Derivation.zero_apply] at h
  exact sub_eq_zero.mp h

/- English proof (translation)
Simplify using `[extM, ha]`.
-/
theorem extendMatrix_last_right_zero (R : Type*) [CommRing R] {n : ℕ} (g : Matrix (Fin n) (Fin n) R)
    (a : Fin (n + 1)) (ha : a ≠ Fin.last n) : extM R g a (Fin.last n) = 0 := by
  simp [extM, ha]

/- English proof (translation)
Simplify using `[extM, Ne.symm hb]`.
-/
theorem extendMatrix_last_left_zero (R : Type*) [CommRing R] {n : ℕ} (g : Matrix (Fin n) (Fin n) R)
    (b : Fin (n + 1)) (hb : b ≠ Fin.last n) : extM R g (Fin.last n) b = 0 := by
  simp [extM, Ne.symm hb]

/- English proof (translation)
Rewrite using `[rowAct, aeval_X]`.
-/
theorem rowAction_X_sum (R : Type*) [CommRing R] {r n : ℕ} (g : Matrix (Fin r) (Fin r) R) (v : Fin r × Fin n) :
    rowAct R g (X v) = ∑ b : Fin r, C (g v.1 b) * X (b, v.2) := by
  rw [rowAct, aeval_X]

/- English proof (translation)
Rewrite using `[elemDeriv_X, rowAction_X_sum, map_sum]`. Take `⟨a, c⟩` from `v`. Distinguish the cases in `hc : c = t`. Substitute `hc` using the available equality. Distinguish the cases in `ha : a = Fin.last n`.

Substitute `ha` using the available equality. Simplify using `only [ne_eq, not_true_eq_false, and_false, if_false, map_zero]`. Use `(Finset.sum_eq_zero fun b _ => ?_).symm` and prove the remaining obligations. Distinguish the cases in `hb : b = Fin.last n`. Substitute `hb` using the available equality.

Rewrite using `[Derivation.leibniz, elemDeriv_X]`. Simplify using `[MvPolynomial.derivation_C]`. Rewrite using `[extendMatrix_last_left_zero R g b hb]`. Simplify using the standard rewrite rules. Simplify using `only [ha, ne_eq, not_false_eq_true, and_self, if_true, rowAction_X_sum]`.

Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[Derivation.leibniz, elemDeriv_X, MvPolynomial.derivation_C, smul_zero, add_zero, smul_eq_mul]`. Distinguish the cases in `hb : b = Fin.last n`. Substitute `hb` using the available equality. Rewrite using `[extendMatrix_last_right_zero R g a ha]`.

Simplify using the standard rewrite rules. Simplify using `[hb]`. Simplify using `only [hc, false_and, if_false, map_zero]`. Use `(Finset.sum_eq_zero fun b _ => ?_).symm` and prove the remaining obligations. Rewrite using `[Derivation.leibniz, elemDeriv_X, MvPolynomial.derivation_C]`.

Simplify using `[hc]`.
-/
theorem rowAction_ext_elemDeriv_X (R : Type*) [CommRing R] (n : ℕ) (g : Matrix (Fin n) (Fin n) R) (s t : Fin n)
    (v : Fin (n + 1) × Fin n) :
    rowAct R (extM R g) (bmE R n s t (X v)) = bmE R n s t (rowAct R (extM R g) (X v)) := by
  rw [elemDeriv_X, rowAction_X_sum, map_sum]
  obtain ⟨a, c⟩ := v
  by_cases hc : c = t
  · subst hc
    by_cases ha : a = Fin.last n
    · subst ha
      simp only [ne_eq, not_true_eq_false, and_false, if_false, map_zero]
      refine (Finset.sum_eq_zero fun b _ => ?_).symm
      by_cases hb : b = Fin.last n
      · subst hb
        rw [Derivation.leibniz, elemDeriv_X]
        simp [MvPolynomial.derivation_C]
      · rw [extendMatrix_last_left_zero R g b hb]
        simp
    · simp only [ha, ne_eq, not_false_eq_true, and_self, if_true, rowAction_X_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Derivation.leibniz, elemDeriv_X, MvPolynomial.derivation_C, smul_zero, add_zero, smul_eq_mul]
      by_cases hb : b = Fin.last n
      · subst hb
        rw [extendMatrix_last_right_zero R g a ha]
        simp
      · simp [hb]
  · simp only [hc, false_and, if_false, map_zero]
    refine (Finset.sum_eq_zero fun b _ => ?_).symm
    rw [Derivation.leibniz, elemDeriv_X, MvPolynomial.derivation_C]
    simp [hc]

/- English proof (translation)
Use `LinearMap.ext fun F => ?_` and prove the remaining obligations. Use `show rowAct R (extM R g) (bmE R n s t F) = bmE R n s t (rowAct R (extM R g) F)`. Proceed by induction on `F using MvPolynomial.induction_on`. Use `next a => simp [rowAct, MvPolynomial.derivation_C]`. Use `next p q hp hq => simp only [map_add, hp, hq]`.

Use `next p v hp => simp only [Derivation.leibniz, map_mul, map_add, smul_eq_mul, hp, rowAction_ext_elemDeriv_X]`.
-/
theorem bm_rowAct_comm_bmEL (R : Type*) [CommRing R] (n : ℕ) (g : Matrix (Fin n) (Fin n) R) (s t : Fin n) :
    Commute ((rowAct R (extM R g)).toLinearMap : Module.End R (BP R n)) (bmEL R n s t) := by
  refine LinearMap.ext fun F => ?_
  show rowAct R (extM R g) (bmE R n s t F) = bmE R n s t (rowAct R (extM R g) F)
  induction F using MvPolynomial.induction_on
  next a => simp [rowAct, MvPolynomial.derivation_C]
  next p q hp hq => simp only [map_add, hp, hq]
  next p v hp => simp only [Derivation.leibniz, map_mul, map_add, smul_eq_mul, hp, rowAction_ext_elemDeriv_X]

/- English proof (translation)
Establish `: bmZ R n s t = (X (Fin.last n, s) : BP R n) • (pderiv (Fin.last n, t) : Derivation R (BP R n) (BP R n))`. Use `MvPolynomial.derivation_ext fun v => ?_` and prove the remaining obligations. Rewrite using `[lastRowDeriv_X, Derivation.smul_apply, pderiv_X, smul_eq_mul]`. Take `⟨a, b⟩` from `v`. Apply the tactic sequence `by_cases h1 : b = t <;> by_cases h2 : a = Fin.last n <;> simp [h1, h2, Pi.single_apply]`.

Rewrite using `[this, Derivation.smul_apply, smul_eq_mul]`.
-/
theorem lastRowDeriv_eq_X_mul_pderiv (R : Type*) [CommRing R] (n : ℕ) (s t : Fin n) (F : BP R n) :
    bmZ R n s t F = X (Fin.last n, s) * pderiv (Fin.last n, t) F := by
  have : bmZ R n s t = (X (Fin.last n, s) : BP R n) • (pderiv (Fin.last n, t) : Derivation R (BP R n) (BP R n)) := by
    refine MvPolynomial.derivation_ext fun v => ?_
    rw [lastRowDeriv_X, Derivation.smul_apply, pderiv_X, smul_eq_mul]
    obtain ⟨a, b⟩ := v
    by_cases h1 : b = t <;> by_cases h2 : a = Fin.last n <;> simp [h1, h2, Pi.single_apply]
  rw [this, Derivation.smul_apply, smul_eq_mul]

/- English proof (translation)
Rewrite using `[lastRowDeriv_eq_X_mul_pderiv, coeff_X_mul']`. Use `split_ifs with h`. Rewrite using `[coeff_pderiv]`. Establish `hle : Finsupp.single (Fin.last n, s) 1 ≤ m`. Rewrite using `[Finsupp.single_le_iff]`.

Conclude with `Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 h)`. Rewrite using `[tsub_add_cancel_of_le hle]`. Establish `h1 : (m - Finsupp.single (Fin.last n, s) 1 : Fin (n + 1) × Fin n →₀ ℕ) (Fin.last n, s) + 1 = m (Fin.last n, s)`. Use `Finsupp.single_le_iff.1 hle` as an intermediate fact. Simplify using `only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[mul_comm]`. Use `congr 1`. Establish `h2` using `congrArg (Nat.cast : ℕ → R) h1`. Move the coercions through the operations in `at h2`.

Conclude with `h2`. Rewrite using `[Finsupp.notMem_support_iff.1 h]`. Simplify using the standard rewrite rules.
-/
theorem lastRowDiagDeriv_coeff (R : Type*) [CommRing R] (n : ℕ) (s : Fin n) (F : BP R n)
    (m : Fin (n + 1) × Fin n →₀ ℕ) :
    coeff m (bmZ R n s s F) = (m (Fin.last n, s) : R) * coeff m F := by
  classical
  rw [lastRowDeriv_eq_X_mul_pderiv, coeff_X_mul']
  split_ifs with h
  · rw [coeff_pderiv]
    have hle : Finsupp.single (Fin.last n, s) 1 ≤ m := by
      rw [Finsupp.single_le_iff]; exact Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 h)
    rw [tsub_add_cancel_of_le hle]
    have h1 : (m - Finsupp.single (Fin.last n, s) 1 : Fin (n + 1) × Fin n →₀ ℕ) (Fin.last n, s) + 1 =
        m (Fin.last n, s) := by
      have := Finsupp.single_le_iff.1 hle
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]
      omega
    rw [mul_comm]
    congr 1
    have h2 := congrArg (Nat.cast : ℕ → R) h1
    push_cast at h2
    exact h2
  · rw [Finsupp.notMem_support_iff.1 h]; simp

/- English proof (translation)
Use extensionality with `m`. Rewrite using `[lastRowDiagDeriv_coeff, coeff_smul, smul_eq_mul]`. Distinguish the cases in `hc : coeff m F = 0`. Rewrite using `[hc, mul_zero, mul_zero]`. Establish `h1` using `hF hc`.

Establish `h2` using `bm_weight_zW m s`. Rewrite `h2` using `[h1]`. Rewrite using `[h2, Int.cast_natCast]`.
-/
theorem bmZ_euler (R : Type*) [CommRing R] (n : ℕ) (β : Fin n → ℤ) (s : Fin n) (F : BP R n)
    (hF : IsWeightedHomogeneous (zW n) F β) : bmZ R n s s F = ((β s : ℤ) : R) • F := by
  ext m
  rw [lastRowDiagDeriv_coeff, coeff_smul, smul_eq_mul]
  by_cases hc : coeff m F = 0
  · rw [hc, mul_zero, mul_zero]
  · have h1 := hF hc
    have h2 := bm_weight_zW m s
    rw [h1] at h2
    rw [h2, Int.cast_natCast]

/- English proof (translation)
Establish `h` using `bm_zcomp_bmZ R n β l j F`. Simplify using `only [zcomp] at h`. Rewrite `h` using `[bm_whcSame_lemma hF]`. Rewrite using `[← h]`. Conclude with `bm_whcWH_lemma_3 _ _ _`.
-/
theorem lastRowDeriv_weighted_homogeneous (R : Type*) [CommRing R] (n : ℕ) (l j : Fin n) (β : Fin n → ℤ) (F : BP R n)
    (hF : IsWeightedHomogeneous (zW n) F β) :
    IsWeightedHomogeneous (zW n) (bmZ R n l j F) (β + (Pi.single l 1 - Pi.single j 1)) := by
  have h := bm_zcomp_bmZ R n β l j F
  simp only [zcomp] at h
  rw [bm_whcSame_lemma hF] at h
  rw [← h]
  exact bm_whcWH_lemma_3 _ _ _

/- English proof (translation)
Establish `h1 : pderiv (Fin.last n, l) F = 0`. Rewrite `h0` using `[lastRowDeriv_eq_X_mul_pderiv]`. Conclude with `(mul_eq_zero.mp h0).resolve_left (X_ne_zero _)`. Establish `h2` using `bmZ_euler R n β l F hF`. Rewrite `h2` using `[lastRowDeriv_eq_X_mul_pderiv, h1, mul_zero]`.

Establish `hne : ((β l : ℤ) : R) ≠ 0`. Conclude with `(show β l ≠ 0 by omega)` after adjusting the coercions. Conclude with `(smul_eq_zero.mp h2.symm).resolve_left hne`.
-/
theorem lastRowDeriv_injective_weighted (R : Type*) [CommRing R] [IsDomain R] [CharZero R] (n : ℕ) (j l : Fin n)
    (β : Fin n → ℤ) (F : BP R n) (hF : IsWeightedHomogeneous (zW n) F β) (hk : 1 ≤ β l)
    (h0 : bmZ R n j l F = 0) : F = 0 := by
  have h1 : pderiv (Fin.last n, l) F = 0 := by
    rw [lastRowDeriv_eq_X_mul_pderiv] at h0
    exact (mul_eq_zero.mp h0).resolve_left (X_ne_zero _)
  have h2 := bmZ_euler R n β l F hF
  rw [lastRowDeriv_eq_X_mul_pderiv, h1, mul_zero] at h2
  have hne : ((β l : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show β l ≠ 0 by omega)
  exact (smul_eq_zero.mp h2.symm).resolve_left hne

/- English proof (translation)
Proceed by induction on `k generalizing β F with`. Consider the case `zero => simpa using h0`. Consider the case `succ k ih`. Rewrite `h0` using `[Function.iterate_succ_apply]`. Establish `hW` using `lastRowDeriv_weighted_homogeneous R n j l β F hF`.

Establish `h1 : bmZ R n j l F = 0`. Use `ih _ _ hW ?_ h0` and prove the remaining obligations. Establish `e : (β + (Pi.single j 1 - Pi.single l 1) : Fin n → ℤ) l = β l - 1`. Rewrite using `[Pi.add_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hjl)]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Use linear arithmetic over natural numbers and integers. Conclude with `lastRowDeriv_injective_weighted R n j l β F hF (by omega) h1`.
-/
theorem bmZ_iter_inj (R : Type*) [CommRing R] [IsDomain R] [CharZero R] (n : ℕ) (j l : Fin n) (hjl : j ≠ l)
    (k : ℕ) (β : Fin n → ℤ) (F : BP R n) (hF : IsWeightedHomogeneous (zW n) F β) (hk : (k : ℤ) ≤ β l)
    (h0 : (bmZ R n j l)^[k] F = 0) : F = 0 := by
  induction k generalizing β F with
  | zero => simpa using h0
  | succ k ih =>
    rw [Function.iterate_succ_apply] at h0
    have hW := lastRowDeriv_weighted_homogeneous R n j l β F hF
    have h1 : bmZ R n j l F = 0 := by
      refine ih _ _ hW ?_ h0
      have e : (β + (Pi.single j 1 - Pi.single l 1) : Fin n → ℤ) l = β l - 1 := by
        rw [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hjl)]
        ring
      rw [e]
      omega
    exact lastRowDeriv_injective_weighted R n j l β F hF (by omega) h1

/- English proof (translation)
Unfold `zmon`. Use `Finset.prod_induction _ (fun p => bmE R n s t p = 0) (fun a b ha hb => ?_) (by simp) (fun x _ => ?_)` and prove the remaining obligations. Use `beta_reduce at ha hb ⊢`. Rewrite using `[Derivation.leibniz, ha, hb, smul_zero, smul_zero, add_zero]`. Use `beta_reduce`.

Rewrite using `[Derivation.leibniz_pow, elemDeriv_X]`. Simplify using the standard rewrite rules.
-/
theorem elemDeriv_lastMonomial_zero (R : Type*) [CommRing R] (n : ℕ) (s t : Fin n) (b : Fin n → ℕ) :
    bmE R n s t (zmon R n b) = 0 := by
  unfold zmon
  refine Finset.prod_induction _ (fun p => bmE R n s t p = 0) (fun a b ha hb => ?_) (by simp) (fun x _ => ?_)
  · beta_reduce at ha hb ⊢
    rw [Derivation.leibniz, ha, hb, smul_zero, smul_zero, add_zero]
  · beta_reduce
    rw [Derivation.leibniz_pow, elemDeriv_X]
    simp

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on`. Use `next a => simp [emb, MvPolynomial.derivation_C]`. Use `next p q hp hq => simp only [map_add, hp, hq]`. Use `next p v hp =>`. Establish `hX : bmE R n s t (emb R n (X v)) = emb R n (ndE R n n s t (X v))`.

Simplify using `only [emb, rename_X, elemDeriv_X, ndE, mkDerivation_X]`. Apply the tactic sequence `by_cases h : v.2 = t <;> simp [h, Fin.castSucc_ne_last]`. Simplify using `only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, hp, hX]`.
-/
theorem elemDeriv_embed_comm (R : Type*) [CommRing R] (n : ℕ) (s t : Fin n) (f : MvPolynomial (Fin n × Fin n) R) :
    bmE R n s t (emb R n f) = emb R n (ndE R n n s t f) := by
  induction f using MvPolynomial.induction_on
  next a => simp [emb, MvPolynomial.derivation_C]
  next p q hp hq => simp only [map_add, hp, hq]
  next p v hp =>
    have hX : bmE R n s t (emb R n (X v)) = emb R n (ndE R n n s t (X v)) := by
      simp only [emb, rename_X, elemDeriv_X, ndE, mkDerivation_X]
      by_cases h : v.2 = t <;> simp [h, Fin.castSucc_ne_last]
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, hp, hX]

/- English proof (translation)
Rewrite using `[Derivation.leibniz, elemDeriv_lastMonomial_zero, smul_zero, add_zero, elemDeriv_embed_comm, smul_eq_mul]`.
-/
theorem bmE_lead (R : Type*) [CommRing R] (n : ℕ) (s t : Fin n) (b : Fin n → ℕ)
    (f : MvPolynomial (Fin n × Fin n) R) :
    bmE R n s t (zmon R n b * emb R n f) = zmon R n b * emb R n (ndE R n n s t f) := by
  rw [Derivation.leibniz, elemDeriv_lastMonomial_zero, smul_zero, add_zero, elemDeriv_embed_comm, smul_eq_mul]

section bmAList

variable {A : Type*} [Ring A]

/- English proof (translation)
Simplify using `[List.ofFn_succ, Function.update_of_ne, Fin.succ_ne_zero]`.
-/
theorem bmA_prod_update_zero {n : ℕ} (g : Fin (n + 1) → A) (w : A) :
    (List.ofFn (Function.update g 0 w)).prod = w * (List.ofFn fun i : Fin n => g i.succ).prod := by
  simp [List.ofFn_succ, Function.update_of_ne, Fin.succ_ne_zero]

/- English proof (translation)
Rewrite using `[List.ofFn_succ, List.prod_cons, Function.update_of_ne (Fin.succ_ne_zero k).symm]`. Use `congr 1`. Use `congr 1`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Distinguish the cases in `h : i = k`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Function.update_of_ne h, Function.update_of_ne (fun h' => h (Fin.succ_injective _ h'))]`.
-/
theorem bmA_prod_update_succ {n : ℕ} (g : Fin (n + 1) → A) (k : Fin n) (w : A) :
    (List.ofFn (Function.update g k.succ w)).prod =
      g 0 * (List.ofFn (Function.update (fun i : Fin n => g i.succ) k w)).prod := by
  rw [List.ofFn_succ, List.prod_cons, Function.update_of_ne (Fin.succ_ne_zero k).symm]
  congr 1
  congr 1
  congr 1
  funext i
  by_cases h : i = k
  · subst h
    simp
  · rw [Function.update_of_ne h, Function.update_of_ne (fun h' => h (Fin.succ_injective _ h'))]

/- English proof (translation)
The claim follows from `| 0, g => by simp | n + 1, g => by have ih := bmA_comm_prod x (fun i : Fin n => g i.succ) rw [Fin.sum_univ_succ, bmA_prod_update_zero] simp only [bmA_prod_update_succ] rw [← Finset.mul_sum, ← ih, List.ofFn_succ, List.prod_cons] noncomm_ring`.
-/
theorem bmA_comm_prod (x : A) : ∀ {n : ℕ} (g : Fin n → A),
    x * (List.ofFn g).prod - (List.ofFn g).prod * x =
      ∑ k, (List.ofFn (Function.update g k (x * g k - g k * x))).prod
  | 0, g => by simp
  | n + 1, g => by
    have ih := bmA_comm_prod x (fun i : Fin n => g i.succ)
    rw [Fin.sum_univ_succ, bmA_prod_update_zero]
    simp only [bmA_prod_update_succ]
    rw [← Finset.mul_sum, ← ih, List.ofFn_succ, List.prod_cons]
    noncomm_ring

/- English proof (translation)
The claim follows from `| 0, _, p, _, _ => p.elim0 | n + 1, g, p, p', h => by obtain ⟨q', rfl⟩ : ∃ q' : Fin n, p' = q'.succ := by refine ⟨⟨p'.val - 1, by omega⟩, ?_⟩ ext; simp; omega induction p using Fin.cases with | zero => have hq : q'.val = 0 := by simpa using h obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨ …`.
-/
theorem bmA_adj : ∀ {n : ℕ} (g : Fin n → A) (p p' : Fin n), p'.val = p.val + 1 →
    ∃ L Rr : A, ∀ a b : A,
      (List.ofFn (Function.update (Function.update g p a) p' b)).prod = L * (a * b) * Rr
  | 0, _, p, _, _ => p.elim0
  | n + 1, g, p, p', h => by
    obtain ⟨q', rfl⟩ : ∃ q' : Fin n, p' = q'.succ := by
      refine ⟨⟨p'.val - 1, by omega⟩, ?_⟩
      ext; simp; omega
    induction p using Fin.cases with
    | zero =>
      have hq : q'.val = 0 := by simpa using h
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := q'.isLt; omega⟩
      have hq0 : q' = 0 := by ext; simpa using hq
      subst hq0
      refine ⟨1, (List.ofFn fun i : Fin m => g i.succ.succ).prod, fun a b => ?_⟩
      rw [bmA_prod_update_succ, Function.update_self, bmA_prod_update_zero]
      have : (fun i : Fin m => Function.update g 0 a i.succ.succ) = fun i : Fin m => g i.succ.succ := by
        funext i
        rw [Function.update_of_ne (Fin.succ_ne_zero _)]
      rw [this]
      noncomm_ring
    | succ q =>
      have hq : q'.val = q.val + 1 := by simpa using h
      obtain ⟨L, Rr, hL⟩ := bmA_adj (fun i : Fin n => g i.succ) q q' hq
      refine ⟨g 0 * L, Rr, fun a b => ?_⟩
      rw [bmA_prod_update_succ, Function.update_of_ne (Fin.succ_ne_zero q).symm]
      have : (fun i : Fin n => Function.update g q.succ a i.succ) =
          Function.update (fun i : Fin n => g i.succ) q a := by
        funext i
        by_cases hi : i = q
        · subst hi; simp
        · rw [Function.update_of_ne hi, Function.update_of_ne (fun h' => hi (Fin.succ_injective _ h'))]
      rw [this, hL]
      noncomm_ring

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact k.elim0`. Consider the case `succ n ih`. Consider the cases of `k using Fin.cases with`. Consider the case `zero => rw [bmA_prod_update_zero, bmA_prod_update_zero, bmA_prod_update_zero, sub_mul]`.

Consider the case `succ k => rw [bmA_prod_update_succ, bmA_prod_update_succ, bmA_prod_update_succ, ih, mul_sub]`.
-/
theorem bmA_prod_update_sub {n : ℕ} (g : Fin n → A) (k : Fin n) (a b : A) :
    (List.ofFn (Function.update g k (a - b))).prod =
      (List.ofFn (Function.update g k a)).prod - (List.ofFn (Function.update g k b)).prod := by
  induction n with
  | zero => exact k.elim0
  | succ n ih =>
    cases k using Fin.cases with
    | zero => rw [bmA_prod_update_zero, bmA_prod_update_zero, bmA_prod_update_zero, sub_mul]
    | succ k => rw [bmA_prod_update_succ, bmA_prod_update_succ, bmA_prod_update_succ, ih, mul_sub]

/- English proof (translation)
Use `bmA_prod_update_sub g k 0 0` as an intermediate fact. Rewrite `this` using `[sub_self, sub_self]`. Conclude with `this`.
-/
theorem bmA_prod_update_zero' {n : ℕ} (g : Fin n → A) (k : Fin n) :
    (List.ofFn (Function.update g k 0)).prod = 0 := by
  have := bmA_prod_update_sub g k 0 0
  rw [sub_self, sub_self] at this
  exact this

/- English proof (translation)
Apply the tactic sequence `split_ifs <;> (try simp only [mul_sub, sub_mul, mul_add, add_mul, mul_one, one_mul, mul_zero, zero_mul, sub_zero, zero_sub, neg_mul, mul_neg]) <;> (try simp only [← hX, ← hY]) <;> abel`.
-/
theorem bmA_two (c X Y : A) (hX : c * X = X * c) (hY : c * Y = Y * c) (P Q : Prop) [Decidable P] [Decidable Q] :
    ((if P then c else 0) - X) * ((if Q then c + 1 else 0) - Y) -
        ((if Q then c else 0) - Y) * ((if P then c + 1 else 0) - X) =
      (if P then Y else 0) - (if Q then X else 0) + (X * Y - Y * X) := by
  split_ifs <;>
    (try simp only [mul_sub, sub_mul, mul_add, add_mul, mul_one, one_mul, mul_zero, zero_mul, sub_zero,
      zero_sub, neg_mul, mul_neg]) <;>
    (try simp only [← hX, ← hY]) <;> abel

end bmAList

section bmACap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}

/- English proof (translation)
Conclude with `(Int.cast_commute z X).eq`.
-/
theorem bmA_cast_comm (z : ℤ) (X : Module.End R M) :
    ((z : ℤ) : Module.End R M) * X = X * ((z : ℤ) : Module.End R M) := by
  exact (Int.cast_commute z X).eq

/- English proof (translation)
Establish `hc : ((u + ((p' : ℕ) : ℤ) : ℤ) : Module.End R M) = ((u + ((p : ℕ) : ℤ) : ℤ) : Module.End R M) + 1`. Rewrite using `[hp]`. Use `push_cast`. Normalize the expressions using the abelian group laws. Unfold `bmF`.

Rewrite using `[hc, bmA_two _ _ _ (bmA_cast_comm _ _) (bmA_cast_comm _ _), bmA_two _ _ _ (bmA_cast_comm _ _) (bmA_cast_comm _ _), hE a i b j, hE b i a j]`. Simplify using `only [eq_comm (a := i) (b := b), eq_comm (a := i) (b := a)]`. Normalize the expressions using the abelian group laws.
-/
theorem bmA_four_mid (E : Fin n → Fin n → Module.End R M) (u : ℤ)
    (hE : ∀ i j k l, E i j * E k l - E k l * E i j = (if j = k then E i l else 0) - (if i = l then E k j else 0))
    (p p' : Fin n) (hp : p'.val = p.val + 1) (a b i j : Fin n) :
    bmF E u p a i * bmF E u p' b j - bmF E u p b j * bmF E u p' a i =
      bmF E u p b i * bmF E u p' a j - bmF E u p a j * bmF E u p' b i := by
  have hc : ((u + ((p' : ℕ) : ℤ) : ℤ) : Module.End R M) = ((u + ((p : ℕ) : ℤ) : ℤ) : Module.End R M) + 1 := by
    rw [hp]; push_cast; abel
  unfold bmF
  rw [hc, bmA_two _ _ _ (bmA_cast_comm _ _) (bmA_cast_comm _ _), bmA_two _ _ _ (bmA_cast_comm _ _) (bmA_cast_comm _ _),
    hE a i b j, hE b i a j]
  simp only [eq_comm (a := i) (b := b), eq_comm (a := i) (b := a)]
  abel

/- English proof (translation)
Establish `hne : p ≠ p'` using `by intro h; rw [h] at hp; omega`. Take `⟨L, Rr, hL⟩` from `bmA_adj (fun k => bmF E u k (α k) (β k)) p p' hp`. Establish `key : ∀ (α' β' : Fin n → Fin n), (∀ k, k ≠ p → k ≠ p' → α' k = α k ∧ β' k = β k) → bmM E u α' β' = L * (bmF E u p (α' p) (β' p) * bmF E u p' (α' p') (β' p')) * Rr`. Introduce `α' β' h`. Rewrite using `[← hL]`.

Unfold `bmM`. Use `congr 2`. Use function extensionality and compare the values at `k`. Distinguish the cases in `h1 : k = p'`. Substitute `h1` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[Function.update_of_ne h1]`. Distinguish the cases in `h2 : k = p`. Substitute `h2` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[Function.update_of_ne h2, (h k h2 h1).1, (h k h2 h1).2]`. Rewrite using `[key α β (fun k _ _ => ⟨rfl, rfl⟩), key (α ∘ Equiv.swap p p') (β ∘ Equiv.swap p p') (fun k h1 h2 => by`. Simplify using `[Equiv.swap_apply_of_ne_of_ne h1 h2]),`. Use `key (α ∘ Equiv.swap p p') β (fun k h1 h2 => by simp [Equiv.swap_apply_of_ne_of_ne h1 h2]),`. Use `key α (β ∘ Equiv.swap p p') (fun k h1 h2 => by simp [Equiv.swap_apply_of_ne_of_ne h1 h2])]`.

Simplify using `only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]`. Rewrite using `[← mul_sub_right_distrib, ← mul_sub_left_distrib, ← mul_sub_right_distrib, ← mul_sub_left_distrib, bmA_four_mid E u hE p p' hp]`.
-/
theorem bmA_four (E : Fin n → Fin n → Module.End R M) (u : ℤ)
    (hE : ∀ i j k l, E i j * E k l - E k l * E i j = (if j = k then E i l else 0) - (if i = l then E k j else 0))
    (p p' : Fin n) (hp : p'.val = p.val + 1) (α β : Fin n → Fin n) :
    bmM E u α β - bmM E u (α ∘ Equiv.swap p p') (β ∘ Equiv.swap p p') =
      bmM E u (α ∘ Equiv.swap p p') β - bmM E u α (β ∘ Equiv.swap p p') := by
  have hne : p ≠ p' := by intro h; rw [h] at hp; omega
  obtain ⟨L, Rr, hL⟩ := bmA_adj (fun k => bmF E u k (α k) (β k)) p p' hp
  have key : ∀ (α' β' : Fin n → Fin n), (∀ k, k ≠ p → k ≠ p' → α' k = α k ∧ β' k = β k) →
      bmM E u α' β' = L * (bmF E u p (α' p) (β' p) * bmF E u p' (α' p') (β' p')) * Rr := by
    intro α' β' h
    rw [← hL]
    unfold bmM
    congr 2
    funext k
    by_cases h1 : k = p'
    · subst h1; simp
    · rw [Function.update_of_ne h1]
      by_cases h2 : k = p
      · subst h2; simp
      · rw [Function.update_of_ne h2, (h k h2 h1).1, (h k h2 h1).2]
  rw [key α β (fun k _ _ => ⟨rfl, rfl⟩),
    key (α ∘ Equiv.swap p p') (β ∘ Equiv.swap p p') (fun k h1 h2 => by
      simp [Equiv.swap_apply_of_ne_of_ne h1 h2]),
    key (α ∘ Equiv.swap p p') β (fun k h1 h2 => by simp [Equiv.swap_apply_of_ne_of_ne h1 h2]),
    key α (β ∘ Equiv.swap p p') (fun k h1 h2 => by simp [Equiv.swap_apply_of_ne_of_ne h1 h2])]
  simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  rw [← mul_sub_right_distrib, ← mul_sub_left_distrib, ← mul_sub_right_distrib, ← mul_sub_left_distrib,
    bmA_four_mid E u hE p p' hp]

end bmACap

section bmACap2

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}

/- English proof (translation)
Establish `hne : p ≠ p'` using `by intro h; rw [h] at hp; omega`. Use `set s := Equiv.swap p p' with hs`. Establish `hsign : ∀ α : Equiv.Perm (Fin n), ((Equiv.Perm.sign (α * s) : ℤˣ) : ℤ) = - ((Equiv.Perm.sign α : ℤˣ) : ℤ)`. Introduce `α`. Rewrite using `[Equiv.Perm.sign_mul, hs, Equiv.Perm.sign_swap hne]`.

Simplify using the standard rewrite rules. Establish `h1 : bmPi E u (β ∘ s) = - ∑ α : Equiv.Perm (Fin n), ((Equiv.Perm.sign α : ℤˣ) : ℤ) • bmM E u (α ∘ s) (β ∘ s)`. Unfold `bmPi`. Rewrite using `[← Equiv.sum_comp (Equiv.mulRight s), ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun α _ => ?_` and prove the remaining obligations.

Rewrite using `[Equiv.coe_mulRight, hsign, neg_smul, Equiv.Perm.coe_mul]`. Use `set S : Module.End R M := ∑ α : Equiv.Perm (Fin n), ((Equiv.Perm.sign α : ℤˣ) : ℤ) • (bmM E u α β - bmM E u (α ∘ s) (β ∘ s)) with hS`. Establish `h3 : S = - S` using `by conv_lhs => rw [hS, ← Equiv.sum_comp (Equiv.mulRight s)]`. Rewrite using `[hS, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun α _ => ?_` and prove the remaining obligations.

Rewrite using `[Equiv.coe_mulRight, hsign, neg_smul, Equiv.Perm.coe_mul]`. Use `congr 2`. Establish `hss : ((α : Fin n → Fin n) ∘ s) ∘ s = α`. Use function extensionality and compare the values at `k`. Simplify using `[hs]`.

Rewrite using `[hss, hs, bmA_four E u hE p p' hp α β]`. Establish `h4 : S = 0` using `h2 S (by nth_rewrite 1 [h3]; simp)`. Establish `h5 : S = bmPi E u β + bmPi E u (β ∘ s)`. Rewrite using `[h1, hS]`. Unfold `bmPi`.

Simplify using `only [smul_sub, Finset.sum_sub_distrib]`. Normalize the expressions using the abelian group laws. Rewrite `h5` using `[h4]`. Conclude with `(neg_eq_of_add_eq_zero_right h5.symm).symm`.
-/
theorem bmA_Pi_adj (E : Fin n → Fin n → Module.End R M) (u : ℤ)
    (hE : ∀ i j k l, E i j * E k l - E k l * E i j = (if j = k then E i l else 0) - (if i = l then E k j else 0))
    (h2 : ∀ x : Module.End R M, x + x = 0 → x = 0)
    (p p' : Fin n) (hp : p'.val = p.val + 1) (β : Fin n → Fin n) :
    bmPi E u (β ∘ Equiv.swap p p') = - bmPi E u β := by
  have hne : p ≠ p' := by intro h; rw [h] at hp; omega
  set s := Equiv.swap p p' with hs
  have hsign : ∀ α : Equiv.Perm (Fin n), ((Equiv.Perm.sign (α * s) : ℤˣ) : ℤ) = - ((Equiv.Perm.sign α : ℤˣ) : ℤ) := by
    intro α
    rw [Equiv.Perm.sign_mul, hs, Equiv.Perm.sign_swap hne]; simp

  have h1 : bmPi E u (β ∘ s) = - ∑ α : Equiv.Perm (Fin n), ((Equiv.Perm.sign α : ℤˣ) : ℤ) • bmM E u (α ∘ s) (β ∘ s) := by
    unfold bmPi
    rw [← Equiv.sum_comp (Equiv.mulRight s), ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Equiv.coe_mulRight, hsign, neg_smul, Equiv.Perm.coe_mul]
  set S : Module.End R M := ∑ α : Equiv.Perm (Fin n), ((Equiv.Perm.sign α : ℤˣ) : ℤ) •
      (bmM E u α β - bmM E u (α ∘ s) (β ∘ s)) with hS
  have h3 : S = - S := by
    conv_lhs => rw [hS, ← Equiv.sum_comp (Equiv.mulRight s)]
    rw [hS, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Equiv.coe_mulRight, hsign, neg_smul, Equiv.Perm.coe_mul]
    congr 2
    have hss : ((α : Fin n → Fin n) ∘ s) ∘ s = α := by
      funext k; simp [hs]
    rw [hss, hs, bmA_four E u hE p p' hp α β]
  have h4 : S = 0 := h2 S (by nth_rewrite 1 [h3]; simp)
  have h5 : S = bmPi E u β + bmPi E u (β ∘ s) := by
    rw [h1, hS]
    unfold bmPi
    simp only [smul_sub, Finset.sum_sub_distrib]
    abel
  rw [h4] at h5
  exact (neg_eq_of_add_eq_zero_right h5.symm).symm

/- English proof (translation)
Consider the cases of `n with`. Consider the case `zero`. Introduce `β`. Establish `: τ = 1` using `Subsingleton.elim _ _`. Substitute `this` using the available equality.

Simplify using the standard rewrite rules. Consider the case `succ m`. Establish `hmem : τ ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ)`. Rewrite using `[Equiv.Perm.mclosure_swap_castSucc_succ]`. Conclude with `Submonoid.mem_top _`.

Proceed by induction on `hmem using Submonoid.closure_induction with`. Consider the case `mem x hx`. Take `⟨i, rfl⟩` from `hx`. Introduce `β`. Rewrite using `[bmA_Pi_adj E u hE h2 i.castSucc i.succ (by simp) β, Equiv.Perm.sign_swap (by intro h; have := congrArg Fin.val h; simp at this)]`.

Simplify using the standard rewrite rules. Consider the case `one => intro β`. Simplify using the standard rewrite rules. Consider the case `mul x y _ _ hx hy`. Introduce `β`.

Rewrite using `[Equiv.Perm.coe_mul, ← Function.comp_assoc, hy, hx, Equiv.Perm.sign_mul, smul_smul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem bmA_Pi_perm (E : Fin n → Fin n → Module.End R M) (u : ℤ)
    (hE : ∀ i j k l, E i j * E k l - E k l * E i j = (if j = k then E i l else 0) - (if i = l then E k j else 0))
    (h2 : ∀ x : Module.End R M, x + x = 0 → x = 0) (τ : Equiv.Perm (Fin n)) :
    ∀ β : Fin n → Fin n, bmPi E u (β ∘ τ) = ((Equiv.Perm.sign τ : ℤˣ) : ℤ) • bmPi E u β := by
  cases n with
  | zero =>
    intro β
    have : τ = 1 := Subsingleton.elim _ _
    subst this
    simp
  | succ m =>
    have hmem : τ ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]; exact Submonoid.mem_top _
    induction hmem using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro β
      rw [bmA_Pi_adj E u hE h2 i.castSucc i.succ (by simp) β,
        Equiv.Perm.sign_swap (by intro h; have := congrArg Fin.val h; simp at this)]
      simp
    | one => intro β; simp
    | mul x y _ _ hx hy =>
      intro β
      rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, hy, hx, Equiv.Perm.sign_mul, smul_smul]
      congr 1
      push_cast
      ring

/- English proof (translation)
Establish `h` using `bmA_Pi_perm E u hE h2 (Equiv.swap k l) β`. Establish `e : β ∘ Equiv.swap k l = β`. Use function extensionality and compare the values at `x`. Simplify using `only [Function.comp_apply]`. Distinguish the cases in `hx : x = k`.

Substitute `hx` using the available equality. Rewrite using `[Equiv.swap_apply_left, hβ]`. Distinguish the cases in `hx' : x = l`. Substitute `hx'` using the available equality. Rewrite using `[Equiv.swap_apply_right, hβ]`.

Rewrite using `[Equiv.swap_apply_of_ne_of_ne hx hx']`. Rewrite `h` using `[e, Equiv.Perm.sign_swap hkl]`. Simplify using `only [Units.val_neg, Units.val_one, neg_smul, one_smul] at h`. Apply `h2` to reduce the goal to its premises. Use `nth_rewrite 1 [h]`.

Conclude with `neg_add_cancel _`.
-/
theorem bmA_Pi_zero (E : Fin n → Fin n → Module.End R M) (u : ℤ)
    (hE : ∀ i j k l, E i j * E k l - E k l * E i j = (if j = k then E i l else 0) - (if i = l then E k j else 0))
    (h2 : ∀ x : Module.End R M, x + x = 0 → x = 0) (β : Fin n → Fin n) (k l : Fin n) (hkl : k ≠ l)
    (hβ : β k = β l) : bmPi E u β = 0 := by
  have h := bmA_Pi_perm E u hE h2 (Equiv.swap k l) β
  have e : β ∘ Equiv.swap k l = β := by
    funext x
    simp only [Function.comp_apply]
    by_cases hx : x = k
    · subst hx
      rw [Equiv.swap_apply_left, hβ]
    · by_cases hx' : x = l
      · subst hx'
        rw [Equiv.swap_apply_right, hβ]
      · rw [Equiv.swap_apply_of_ne_of_ne hx hx']
  rw [e, Equiv.Perm.sign_swap hkl] at h
  simp only [Units.val_neg, Units.val_one, neg_smul, one_smul] at h
  apply h2
  nth_rewrite 1 [h]
  exact neg_add_cancel _

/- English proof (translation)
Use `set S : Module.End R M := ∑ α : Equiv.Perm (Fin n), ((Equiv.Perm.sign α : ℤˣ) : ℤ) • bmM E u (c ∘ α) β with hS`. Establish `hcs : c ∘ Equiv.swap k l = c`. Use function extensionality and compare the values at `x`. Distinguish the cases in `h1 : x = k`. Substitute `h1` using the available equality.

Simplify using `[hc]`. Distinguish the cases in `h3 : x = l`. Substitute `h3` using the available equality. Simplify using `[hc]`. Simplify using `[Equiv.swap_apply_of_ne_of_ne h1 h3]`.

Establish `h3 : S = - S` using `by conv_lhs => rw [hS, ← Equiv.sum_comp (Equiv.mulLeft (Equiv.swap k l))]`. Rewrite using `[hS, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun α _ => ?_` and prove the remaining obligations. Rewrite using `[Equiv.coe_mulLeft, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hkl, Equiv.Perm.coe_mul, ← Function.comp_assoc, hcs]`. Simplify using the standard rewrite rules.

Conclude with `h2 S (by nth_rewrite 1 [h3]; simp)`.
-/
theorem bmA_row_zero (E : Fin n → Fin n → Module.End R M) (u : ℤ)
    (h2 : ∀ x : Module.End R M, x + x = 0 → x = 0) (c β : Fin n → Fin n) (k l : Fin n) (hkl : k ≠ l)
    (hc : c k = c l) :
    ∑ α : Equiv.Perm (Fin n), ((Equiv.Perm.sign α : ℤˣ) : ℤ) • bmM E u (c ∘ α) β = 0 := by
  set S : Module.End R M := ∑ α : Equiv.Perm (Fin n), ((Equiv.Perm.sign α : ℤˣ) : ℤ) • bmM E u (c ∘ α) β with hS
  have hcs : c ∘ Equiv.swap k l = c := by
    funext x
    by_cases h1 : x = k
    · subst h1; simp [hc]
    · by_cases h3 : x = l
      · subst h3; simp [hc]
      · simp [Equiv.swap_apply_of_ne_of_ne h1 h3]
  have h3 : S = - S := by
    conv_lhs => rw [hS, ← Equiv.sum_comp (Equiv.mulLeft (Equiv.swap k l))]
    rw [hS, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Equiv.coe_mulLeft, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hkl, Equiv.Perm.coe_mul,
      ← Function.comp_assoc, hcs]
    simp
  exact h2 S (by nth_rewrite 1 [h3]; simp)

end bmACap2

section bmACap3

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}

/- English proof (translation)
Unfold `capDet bmPi bmM`. Use `Commute.sum_right _ _ _ fun α _ => ?_` and prove the remaining obligations. Rewrite using `[zsmul_eq_mul]`. Use `((Int.cast_commute _ x).symm).mul_right ?_` and prove the remaining obligations. Use `Commute.list_prod_right _ _ fun y hy => ?_` and prove the remaining obligations.

Take `⟨k, rfl⟩` from `List.mem_ofFn.mp hy`. Unfold `bmF`. Use `split_ifs`. Conclude with `((Int.cast_commute _ x).symm).sub_right (hx _ _)`. Conclude with `(Commute.zero_right x).sub_right (hx _ _)`.
-/
theorem capDet_commute_of {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (E : Fin n → Fin n → Module.End R M) (u : ℤ) (x : Module.End R M) (hx : ∀ i j, Commute x (E i j)) :
    Commute x (capDet E u) := by
  unfold capDet bmPi bmM
  refine Commute.sum_right _ _ _ fun α _ => ?_
  rw [zsmul_eq_mul]
  refine ((Int.cast_commute _ x).symm).mul_right ?_
  refine Commute.list_prod_right _ _ fun y hy => ?_
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hy
  unfold bmF
  split_ifs
  · exact ((Int.cast_commute _ x).symm).sub_right (hx _ _)
  · exact (Commute.zero_right x).sub_right (hx _ _)

/- English proof (translation)
Establish `h` using `hE k l a j`. Unfold `bmF`. Use `set c : Module.End R M := ((u + ((q : ℕ) : ℤ) : ℤ) : Module.End R M) with hc`. Establish `hcc : c * E k l = E k l * c` using `bmA_cast_comm _ _`. Establish `h1 : E k l * ((if a = j then c else 0) - E a j) - ((if a = j then c else 0) - E a j) * E k l = - (E k l * E a j - E a j * E k l)`.

Distinguish the cases in `haj : a = j`. Simplify using `only [haj, if_true]`. Establish `: E k l * (c - E j j) - (c - E j j) * E k l = - (E k l * E j j - E j j * E k l) - (c * E k l - E k l * c)` using `by noncomm_ring`. Rewrite using `[this, hcc]`. Use `noncomm_ring`.

Simplify using `only [haj, if_false]`. Use `noncomm_ring`. Rewrite using `[h1, h]`. Apply the tactic sequence `by_cases hla : l = a <;> by_cases hkj : k = j`. Substitute `hla` using the available equality.

Substitute `hkj` using the available equality. Simplify using the standard rewrite rules. Substitute `hla` using the available equality. Simplify using `[hkj]`. Substitute `hkj` using the available equality.

Simplify using `[hla, Ne.symm hla]`. Simplify using `[hla, hkj]`.
-/
theorem bmA_comm_entry (E : Fin n → Fin n → Module.End R M) (u : ℤ)
    (hE : ∀ i j k l, E i j * E k l - E k l * E i j = (if j = k then E i l else 0) - (if i = l then E k j else 0))
    (k l q a j : Fin n) :
    E k l * bmF E u q a j - bmF E u q a j * E k l =
      (if l = a then bmF E u q k j else 0) - (if k = j then bmF E u q a l else 0) := by
  have h := hE k l a j
  unfold bmF
  set c : Module.End R M := ((u + ((q : ℕ) : ℤ) : ℤ) : Module.End R M) with hc
  have hcc : c * E k l = E k l * c := bmA_cast_comm _ _
  have h1 : E k l * ((if a = j then c else 0) - E a j) - ((if a = j then c else 0) - E a j) * E k l =
      - (E k l * E a j - E a j * E k l) := by
    by_cases haj : a = j
    · simp only [haj, if_true]
      have : E k l * (c - E j j) - (c - E j j) * E k l =
          - (E k l * E j j - E j j * E k l) - (c * E k l - E k l * c) := by noncomm_ring
      rw [this, hcc]; noncomm_ring
    · simp only [haj, if_false]; noncomm_ring
  rw [h1, h]
  by_cases hla : l = a <;> by_cases hkj : k = j
  · subst hla; subst hkj; simp
  · subst hla; simp [hkj]
  · subst hkj; simp [hla, Ne.symm hla]
  · simp [hla, hkj]

/- English proof (translation)
Establish `hM : ∀ α : Equiv.Perm (Fin n), E k l * bmM E u α id - bmM E u α id * E k l = bmM E u (Function.update id l k ∘ α) id - bmM E u α (Function.update id k l)`. Introduce `α`. Unfold `bmM`. Rewrite using `[bmA_comm_prod]`. Apply the tactic sequence `simp only [bmA_comm_entry E u hE, bmA_prod_update_sub, Finset.sum_sub_distrib, id_eq]`.

Use `congr 1`. Rewrite using `[Finset.sum_eq_single (α.symm l)]`. Rewrite using `[if_pos (by simp)]`. Use `congr 2`. Use function extensionality and compare the values at `q`.

Distinguish the cases in `hq : q = α.symm l`. Substitute `hq` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Function.update_of_ne hq]`. Establish `: α q ≠ l` using `fun h => hq (by rw [← h]; simp)`.

Simplify using `[Function.update_of_ne this]`. Introduce `q _ hq`. Establish `: l ≠ α q` using `fun h => hq (by rw [h]; simp)`. Rewrite using `[if_neg this, bmA_prod_update_zero']`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`. Rewrite using `[Finset.sum_eq_single k]`. Rewrite using `[if_pos rfl]`. Use `congr 2`. Use function extensionality and compare the values at `q`.

Distinguish the cases in `hq : q = k`. Substitute `hq` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Function.update_of_ne hq, Function.update_of_ne hq]`. Both sides reduce to the same expression.

Introduce `q _ hq`. Rewrite using `[if_neg (Ne.symm hq), bmA_prod_update_zero']`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Establish `hsum : E k l * capDet E u - capDet E u * E k l = (∑ α : Equiv.Perm (Fin n), ((Equiv.Perm.sign α : ℤˣ) : ℤ) • bmM E u (Function.update id l k ∘ α) id) - bmPi E u (Function.update id k l)`.

Unfold `capDet bmPi`. Rewrite using `[Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun α _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul_comm, smul_mul_assoc, ← smul_sub, hM, smul_sub]`. Establish `hzero : E k l * capDet E u - capDet E u * E k l = 0`.

Rewrite using `[hsum]`. Distinguish the cases in `hkl : k = l`. Substitute `hkl` using the available equality. Establish `hid : Function.update (id : Fin n → Fin n) k k = id` using `Function.update_eq_self k id`. Rewrite using `[hid]`.

Unfold `bmPi`. Simplify using `only [Function.id_comp, sub_self]`. Rewrite using `[bmA_row_zero E u h2 (Function.update id l k) id k l hkl (by simp [Function.update_of_ne hkl]), bmA_Pi_zero E u hE h2 (Function.update id k l) k l hkl (by simp [Function.update_of_ne (Ne.symm hkl)]), sub_zero]`. Conclude with `sub_eq_zero.1 hzero`.
-/
theorem capDet_central {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (E : Fin n → Fin n → Module.End R M) (u : ℤ)
    (hE : ∀ i j k l, E i j * E k l - E k l * E i j = (if j = k then E i l else 0) - (if i = l then E k j else 0))
    (h2 : ∀ x : Module.End R M, x + x = 0 → x = 0) (k l : Fin n) : Commute (E k l) (capDet E u) := by

  have hM : ∀ α : Equiv.Perm (Fin n), E k l * bmM E u α id - bmM E u α id * E k l =
      bmM E u (Function.update id l k ∘ α) id - bmM E u α (Function.update id k l) := by
    intro α
    unfold bmM
    rw [bmA_comm_prod]
    simp only [bmA_comm_entry E u hE, bmA_prod_update_sub, Finset.sum_sub_distrib, id_eq]
    congr 1
    · rw [Finset.sum_eq_single (α.symm l)]
      · rw [if_pos (by simp)]
        congr 2
        funext q
        by_cases hq : q = α.symm l
        · subst hq; simp
        · rw [Function.update_of_ne hq]
          have : α q ≠ l := fun h => hq (by rw [← h]; simp)
          simp [Function.update_of_ne this]
      · intro q _ hq
        have : l ≠ α q := fun h => hq (by rw [h]; simp)
        rw [if_neg this, bmA_prod_update_zero']
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [Finset.sum_eq_single k]
      · rw [if_pos rfl]
        congr 2
        funext q
        by_cases hq : q = k
        · subst hq; simp
        · rw [Function.update_of_ne hq, Function.update_of_ne hq]; rfl
      · intro q _ hq
        rw [if_neg (Ne.symm hq), bmA_prod_update_zero']
      · intro h; exact absurd (Finset.mem_univ _) h
  have hsum : E k l * capDet E u - capDet E u * E k l =
      (∑ α : Equiv.Perm (Fin n), ((Equiv.Perm.sign α : ℤˣ) : ℤ) • bmM E u (Function.update id l k ∘ α) id) -
        bmPi E u (Function.update id k l) := by
    unfold capDet bmPi
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, hM, smul_sub]
  have hzero : E k l * capDet E u - capDet E u * E k l = 0 := by
    rw [hsum]
    by_cases hkl : k = l
    · subst hkl
      have hid : Function.update (id : Fin n → Fin n) k k = id := Function.update_eq_self k id
      rw [hid]
      unfold bmPi
      simp only [Function.id_comp, sub_self]
    · rw [bmA_row_zero E u h2 (Function.update id l k) id k l hkl (by simp [Function.update_of_ne hkl]),
        bmA_Pi_zero E u hE h2 (Function.update id k l) k l hkl (by simp [Function.update_of_ne (Ne.symm hkl)]),
        sub_zero]
  exact sub_eq_zero.1 hzero

/- English proof (translation)
The claim follows from `| 0, g, c, F, _, _ => by refine ⟨fun _ => by simp, fun h => absurd (fun k : Fin 0 => k.elim0) h⟩ | m + 1, g, c, F, h1, h2 => by obtain ⟨ih1, ih2⟩ := bmA_tri v (fun i : Fin m => g i.succ) (fun i => c i.succ) (fun i => F i.succ) (fun k hk => h1 _ hk) (fun k hk hj => h2 _ hk (fun j …`.
-/
theorem bmA_tri (v : M) : ∀ {m : ℕ} (g : Fin m → Module.End R M) (c : Fin m → R) (F : Fin m → Prop),
    (∀ k, F k → g k v = c k • v) → (∀ k, ¬ F k → (∀ j, k < j → F j) → g k v = 0) →
    ((∀ k, F k) → (List.ofFn g).prod v = (∏ k, c k) • v) ∧ ((¬ ∀ k, F k) → (List.ofFn g).prod v = 0)
  | 0, g, c, F, _, _ => by
    refine ⟨fun _ => by simp, fun h => absurd (fun k : Fin 0 => k.elim0) h⟩
  | m + 1, g, c, F, h1, h2 => by
    obtain ⟨ih1, ih2⟩ := bmA_tri v (fun i : Fin m => g i.succ) (fun i => c i.succ) (fun i => F i.succ)
      (fun k hk => h1 _ hk)
      (fun k hk hj => h2 _ hk (fun j hkj => by
        obtain ⟨j', rfl⟩ : ∃ j' : Fin m, j = j'.succ :=
          ⟨j.pred (by intro h; rw [h] at hkj; exact absurd hkj (Fin.not_lt_zero _)), by simp⟩
        exact hj j' (Fin.succ_lt_succ_iff.1 hkj)))
    rw [List.ofFn_succ, List.prod_cons, Module.End.mul_apply]
    constructor
    · intro hF
      rw [ih1 (fun k => hF _), map_smul, h1 0 (hF 0), Fin.prod_univ_succ, smul_smul, mul_comm]
    · intro hF
      by_cases hs : ∀ k : Fin m, F k.succ
      · have h0 : ¬ F 0 := fun h0 => hF (fun k => by
          induction k using Fin.cases with
          | zero => exact h0
          | succ i => exact hs i)
        rw [ih1 hs, map_smul, h2 0 h0 (fun j hj => by
          obtain ⟨j', rfl⟩ : ∃ j' : Fin m, j = j'.succ :=
            ⟨j.pred (by intro h; rw [h] at hj; exact absurd hj (lt_irrefl _)), by simp⟩
          exact hs j'), smul_zero]
      · rw [ih2 hs, map_zero]

/- English proof (translation)
Establish `hα : ∀ α : Equiv.Perm (Fin n), ((∀ k, α k = k) → bmM E u α id v = (∏ k : Fin n, ((u + ((k : ℕ) : ℤ) - μ k : ℤ) : R)) • v) ∧ ((¬ ∀ k, α k = k) → bmM E u α id v = 0)`. Introduce `α`. Unfold `bmM`. Use `bmA_tri v _ _ (fun k => α k = k) ?_ ?_` and prove the remaining obligations. Introduce `k hk`.

Simplify using `only [bmF, id_eq, hk, if_true, LinearMap.sub_apply, hw]`. Rewrite using `[Module.End.intCast_apply, ← Int.cast_smul_eq_zsmul R, ← sub_smul]`. Use `push_cast`. Both sides reduce to the same expression. Introduce `k hk hj`.

Establish `hlt : α k < k`. Break down `lt_trichotomy (α k) k with h | h | h` into its components or cases. Conclude with `h`. Conclude with `absurd h hk`. Conclude with `absurd (α.injective (hj _ h)) hk`.

Simplify using `only [bmF, id_eq, hk, if_false, LinearMap.sub_apply, hr _ _ hlt, LinearMap.zero_apply, sub_zero]`. Unfold `capDet bmPi`. Rewrite using `[LinearMap.sum_apply, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]`. Rewrite using `[LinearMap.smul_apply, (hα 1).1 (fun k => rfl)]`. Simplify using the standard rewrite rules.

Introduce `α _ hne`. Establish `: ¬ ∀ k, α k = k` using `fun h => hne (Equiv.ext h)`. Rewrite using `[LinearMap.smul_apply, (hα α).2 this, smul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem capDet_eigen {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (E : Fin n → Fin n → Module.End R M) (u : ℤ) (v : M) (μ : Fin n → ℤ)
    (hr : ∀ l j, l < j → E l j v = 0) (hw : ∀ s, E s s v = ((μ s : ℤ) : R) • v) :
    capDet E u v = ((∏ j : Fin n, (u + ((j : ℕ) : ℤ) - μ j) : ℤ) : R) • v := by
  have hα : ∀ α : Equiv.Perm (Fin n),
      ((∀ k, α k = k) → bmM E u α id v = (∏ k : Fin n, ((u + ((k : ℕ) : ℤ) - μ k : ℤ) : R)) • v) ∧
      ((¬ ∀ k, α k = k) → bmM E u α id v = 0) := by
    intro α
    unfold bmM
    refine bmA_tri v _ _ (fun k => α k = k) ?_ ?_
    · intro k hk
      simp only [bmF, id_eq, hk, if_true, LinearMap.sub_apply, hw]
      rw [Module.End.intCast_apply, ← Int.cast_smul_eq_zsmul R, ← sub_smul]
      push_cast
      rfl
    · intro k hk hj
      have hlt : α k < k := by
        rcases lt_trichotomy (α k) k with h | h | h
        · exact h
        · exact absurd h hk
        · exact absurd (α.injective (hj _ h)) hk
      simp only [bmF, id_eq, hk, if_false, LinearMap.sub_apply, hr _ _ hlt, LinearMap.zero_apply, sub_zero]
  unfold capDet bmPi
  rw [LinearMap.sum_apply, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
  · rw [LinearMap.smul_apply, (hα 1).1 (fun k => rfl)]
    simp
  · intro α _ hne
    have : ¬ ∀ k, α k = k := fun h => hne (Equiv.ext h)
    rw [LinearMap.smul_apply, (hα α).2 this, smul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

end bmACap3

/- English proof (translation)
Distinguish the cases in `h : v.2 = j`. Simplify using `[colAddGen, ndE, mkDerivation_X, h, hlj, Derivation.leibniz, pderiv_X, Pi.single_apply]`. Simplify using `[colAddGen, ndE, mkDerivation_X, h, pderiv_X, Pi.single_apply]`.
-/
theorem bmC_pderiv_colAddGen_X {R : Type*} [CommRing R] {r n : ℕ} {l j : Fin n} (hlj : l ≠ j)
    (v : Fin r × Fin n) :
    pderiv none (colAddGen R l j (X v)) = colAddGen R l j (ndE R r n l j (X v)) := by
  by_cases h : v.2 = j
  · simp [colAddGen, ndE, mkDerivation_X, h, hlj, Derivation.leibniz, pderiv_X, Pi.single_apply]
  · simp [colAddGen, ndE, mkDerivation_X, h, pderiv_X, Pi.single_apply]

/- English proof (translation)
Proceed by induction on `g using MvPolynomial.induction_on`. Use `next a => simp [colAddGen, MvPolynomial.derivation_C]`. Use `next p q hp hq => simp only [map_add, hp, hq]`. Use `next p v hp => simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, hp, bmC_pderiv_colAddGen_X hlj]`.
-/
theorem bmC_pderiv_colAddGen {R : Type*} [CommRing R] {r n : ℕ} {l j : Fin n} (hlj : l ≠ j)
    (g : MvPolynomial (Fin r × Fin n) R) :
    pderiv none (colAddGen R l j g) = colAddGen R l j (ndE R r n l j g) := by
  induction g using MvPolynomial.induction_on
  next a => simp [colAddGen, MvPolynomial.derivation_C]
  next p q hp hq => simp only [map_add, hp, hq]
  next p v hp => simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, hp, bmC_pderiv_colAddGen_X hlj]

/- English proof (translation)
Establish `: (ndEv R r n).comp (rename some) = AlgHom.id R _`. Use `MvPolynomial.algHom_ext fun v => ?_` and prove the remaining obligations. Simplify using `[ndEv]`. Conclude with `AlgHom.congr_fun this q`.
-/
theorem bmC_ndEv_rename {R : Type*} [CommRing R] {r n : ℕ} (q : MvPolynomial (Fin r × Fin n) R) :
    ndEv R r n (rename some q) = q := by
  have : (ndEv R r n).comp (rename some) = AlgHom.id R _ := by
    refine MvPolynomial.algHom_ext fun v => ?_
    simp [ndEv]
  exact AlgHom.congr_fun this q

/- English proof (translation)
Establish `hsupp : ∀ m ∈ H.support, m none = 0`. Introduce `m hm`. Assume the negation of the conclusion as `hne`. Establish `hle : Finsupp.single none 1 ≤ m`. Rewrite using `[Finsupp.single_le_iff]`.

Conclude with `Nat.one_le_iff_ne_zero.2 hne`. Establish `hm' : m = (m - Finsupp.single none 1) + Finsupp.single none 1` using `(tsub_add_cancel_of_le hle).symm`. Establish `h1` using `congrArg (coeff (m - Finsupp.single none 1)) h`. Rewrite `h1` using `[coeff_pderiv, ← hm', coeff_zero]`. Break down `mul_eq_zero.1 h1 with h2 | h2` into its components or cases.

Conclude with `(mem_support_iff.1 hm) h2`. Conclude with `absurd h2 (Nat.cast_add_one_ne_zero _)`. Establish `hv : (↑H.vars : Set (Option (Fin r × Fin n))) ⊆ Set.range some`. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_coe, mem_vars_iff_mem_support]`.

Take `⟨m, hm, him⟩` from `hi`. Consider the cases of `i with`. Consider the case `none => exact absurd (hsupp m hm) (Finsupp.mem_support_iff.1 him)`. Consider the case `some v => exact ⟨v, rfl⟩`. Take `⟨q, hq⟩` from `exists_rename_eq_of_vars_subset_range H some (Option.some_injective _) hv`.

Rewrite using `[← hq, bmC_ndEv_rename]`.
-/
theorem bmC_eq_rename_of_pderiv {R : Type*} [CommRing R] [IsDomain R] [CharZero R] {r n : ℕ}
    (H : MvPolynomial (Option (Fin r × Fin n)) R) (h : pderiv none H = 0) :
    H = rename some (ndEv R r n H) := by
  have hsupp : ∀ m ∈ H.support, m none = 0 := by
    intro m hm
    by_contra hne
    have hle : Finsupp.single none 1 ≤ m := by
      rw [Finsupp.single_le_iff]; exact Nat.one_le_iff_ne_zero.2 hne
    have hm' : m = (m - Finsupp.single none 1) + Finsupp.single none 1 := (tsub_add_cancel_of_le hle).symm
    have h1 := congrArg (coeff (m - Finsupp.single none 1)) h
    rw [coeff_pderiv, ← hm', coeff_zero] at h1
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact (mem_support_iff.1 hm) h2
    · exact absurd h2 (Nat.cast_add_one_ne_zero _)
  have hv : (↑H.vars : Set (Option (Fin r × Fin n))) ⊆ Set.range some := by
    intro i hi
    rw [Finset.mem_coe, mem_vars_iff_mem_support] at hi
    obtain ⟨m, hm, him⟩ := hi
    cases i with
    | none => exact absurd (hsupp m hm) (Finsupp.mem_support_iff.1 him)
    | some v => exact ⟨v, rfl⟩
  obtain ⟨q, hq⟩ := exists_rename_eq_of_vars_subset_range H some (Option.some_injective _) hv
  rw [← hq, bmC_ndEv_rename]

/- English proof (translation)
Rewrite using `[mem_dualWeyl_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hhom, hinv⟩`. Conclude with `⟨fun s => ndEul_homog hhom s, fun l j hlj => ndE_eq_zero (hinv l j hlj)⟩`. Introduce and unpack `⟨heul, hE⟩`.

Use `⟨?_, fun l j hlj => ?_⟩` and prove the remaining obligations. Introduce `m hm`. Use function extensionality and compare the values at `s`. Establish `h1` using `congrArg (coeff m) (heul s)`. Rewrite `h1` using `[ndEul_coeff, coeff_smul, smul_eq_mul]`.

Establish `h2` using `mul_right_cancel₀ hm h1`. Rewrite using `[← nd_weight_apply]`. Conclude with `h2` after adjusting the coercions. Establish `h1 : pderiv none (colAddGen R l j G) = 0`. Rewrite using `[bmC_pderiv_colAddGen (ne_of_lt hlj), hE l j hlj, map_zero]`.

Establish `h2` using `bmC_eq_rename_of_pderiv _ h1`. Rewrite `h2` using `[ndEv_colAddGen]`. Conclude with `h2`.
-/
theorem bm_mem_dualWeyl_iff {R : Type} [CommRing R] [IsDomain R] [CharZero R] {r n : ℕ} {ν : Fin n → ℕ}
    {G : MvPolynomial (Fin r × Fin n) R} :
    G ∈ dualWeyl R r n ν ↔
      (∀ s, ndEul R r n s G = (ν s : R) • G) ∧ ∀ l j : Fin n, l < j → ndE R r n l j G = 0 := by
  rw [mem_dualWeyl_iff]
  constructor
  · rintro ⟨hhom, hinv⟩
    exact ⟨fun s => ndEul_homog hhom s, fun l j hlj => ndE_eq_zero (hinv l j hlj)⟩
  · rintro ⟨heul, hE⟩
    refine ⟨?_, fun l j hlj => ?_⟩
    · intro m hm
      funext s
      have h1 := congrArg (coeff m) (heul s)
      rw [ndEul_coeff, coeff_smul, smul_eq_mul] at h1
      have h2 := mul_right_cancel₀ hm h1
      rw [← nd_weight_apply]
      exact_mod_cast h2
    · have h1 : pderiv none (colAddGen R l j G) = 0 := by
        rw [bmC_pderiv_colAddGen (ne_of_lt hlj), hE l j hlj, map_zero]
      have h2 := bmC_eq_rename_of_pderiv _ h1
      rw [ndEv_colAddGen] at h2
      exact h2

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro j _ a ha`. Conclude with `absurd ha (Nat.not_lt_zero _)`. Consider the case `succ k ih`.

Introduce `j hj a ha`. Establish `hk : k < n` using `by have := j.isLt; omega`. Establish `h1` using `hm ⟨k, hk⟩ j (by simpa using hj) ⟨k, by omega⟩`. Establish `h0 : (∑ b : Fin r with b < (⟨k, by omega⟩ : Fin r), m (b, (⟨k, hk⟩ : Fin n))) = 0`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `b hb`. Rewrite `hb` using `[Finset.mem_filter]`. Conclude with `ih ⟨k, hk⟩ rfl b (by simpa [Fin.lt_def] using hb.2)`. Rewrite `h1` using `[h0, add_zero, Nat.le_zero, Finset.sum_eq_zero_iff]`. Conclude with `h1 a (by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, by rw [Fin.le_def]; simp; omega⟩)`.
-/
theorem bmC_tri {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) (hm : Interlaced m) (hr : n ≤ r) :
    ∀ (k : ℕ) (j : Fin n), j.val = k → ∀ a : Fin r, a.val < k → m (a, j) = 0 := by
  intro k
  induction k with
  | zero => intro j _ a ha; exact absurd ha (Nat.not_lt_zero _)
  | succ k ih =>
    intro j hj a ha
    have hk : k < n := by have := j.isLt; omega
    have h1 := hm ⟨k, hk⟩ j (by simpa using hj) ⟨k, by omega⟩
    have h0 : (∑ b : Fin r with b < (⟨k, by omega⟩ : Fin r), m (b, (⟨k, hk⟩ : Fin n))) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      rw [Finset.mem_filter] at hb
      exact ih ⟨k, hk⟩ rfl b (by simpa [Fin.lt_def] using hb.2)
    rw [h0, add_zero, Nat.le_zero, Finset.sum_eq_zero_iff] at h1
    exact h1 a (by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, by rw [Fin.le_def]; simp; omega⟩)

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `set m := (colLex (n + 1) n).degree H with hmdef`. Establish `hm : m ∈ H.support` using `MonomialOrder.degree_mem_support hne`. Establish `hint : Interlaced m` using `leadInterlaced R (n + 1) n lam H hH hne`. Establish `htri` using `bmC_tri m hint (Nat.le_succ n)`.

Establish `hcol` using `colSums R (n + 1) n lam H hH m hm`. Establish `hr` using `hrow m hm`. Establish `hl` using `hlow m hm`. Unfold `omg at hl`. Simplify using `only [bm_weight_zW] at hl`.

Establish `hcol' : ∀ s : Fin n, (lam s : ℤ) = (∑ a : Fin n, (m (a.castSucc, s) : ℤ)) + (m (Fin.last n, s) : ℤ)`. Introduce `s`. Rewrite using `[← hcol s, Fin.sum_univ_castSucc]`. Use `push_cast`. Both sides reduce to the same expression.

Establish `hrow' : ∀ a : Fin n, (sg a : ℤ) = ∑ s : Fin n, (m (a.castSucc, s) : ℤ)`. Introduce `a`. Rewrite using `[← hr a]`. Unfold `rowDeg`. Use `push_cast`.

Both sides reduce to the same expression. Establish `hkey : (∑ s : Fin n, ((((s : ℕ) : ℤ)) + 1) * ∑ a : Fin n, (m (a.castSucc, s) : ℤ)) ≤ ∑ a : Fin n, ((((a : ℕ) : ℤ)) + 1) * ∑ s : Fin n, (m (a.castSucc, s) : ℤ)`. Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Apply `Finset.sum_le_sum` to reduce the goal to its premises.

Introduce `a _`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `s _`. Distinguish the cases in `has : a.val < s.val`. Establish `: m (a.castSucc, s) = 0` using `htri s.val s rfl a.castSucc (by simpa using has)`.

Rewrite using `[this]`. Simplify using the standard rewrite rules. Apply `mul_le_mul_of_nonneg_right _ (by positivity)` to reduce the goal to its premises. Establish `: (s : ℕ) ≤ (a : ℕ)` using `by omega`. Establish `: ((s : ℕ) : ℤ) ≤ ((a : ℕ) : ℤ)` using `by exact_mod_cast this`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `e1 : (∑ s : Fin n, ((((s : ℕ) : ℤ)) + 1) * ((lam s : ℤ) - (sg s : ℤ))) = (∑ s : Fin n, ((((s : ℕ) : ℤ)) + 1) * ∑ a : Fin n, (m (a.castSucc, s) : ℤ)) + (∑ s : Fin n, ((((s : ℕ) : ℤ)) + 1) * (m (Fin.last n, s) : ℤ)) - ∑ a : Fin n, ((((a : ℕ) : ℤ)) + 1) * ∑ s : Fin n, (m (a.castSucc …`. Rewrite using `[← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `s _`.

Rewrite using `[hcol' s, hrow' s]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hl` using `[e1]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem bm_claimT {R : Type} [CommRing R] [IsDomain R] {n : ℕ} (lam sg : Fin n → ℕ) (H : BP R n)
    (hH : H ∈ dualWeyl R (n + 1) n lam)
    (hrow : ∀ m ∈ H.support, ∀ a : Fin n, rowDeg m a.castSucc = sg a)
    (hlow : IsLow (omg fun s => (lam s : ℤ) - (sg s : ℤ)) H) : H = 0 := by
  by_contra hne
  set m := (colLex (n + 1) n).degree H with hmdef
  have hm : m ∈ H.support := MonomialOrder.degree_mem_support hne
  have hint : Interlaced m := leadInterlaced R (n + 1) n lam H hH hne
  have htri := bmC_tri m hint (Nat.le_succ n)
  have hcol := colSums R (n + 1) n lam H hH m hm
  have hr := hrow m hm
  have hl := hlow m hm
  unfold omg at hl
  simp only [bm_weight_zW] at hl

  have hcol' : ∀ s : Fin n, (lam s : ℤ) = (∑ a : Fin n, (m (a.castSucc, s) : ℤ)) + (m (Fin.last n, s) : ℤ) := by
    intro s
    rw [← hcol s, Fin.sum_univ_castSucc]
    push_cast
    rfl
  have hrow' : ∀ a : Fin n, (sg a : ℤ) = ∑ s : Fin n, (m (a.castSucc, s) : ℤ) := by
    intro a
    rw [← hr a]
    unfold rowDeg
    push_cast
    rfl
  have hkey : (∑ s : Fin n, ((((s : ℕ) : ℤ)) + 1) * ∑ a : Fin n, (m (a.castSucc, s) : ℤ)) ≤
      ∑ a : Fin n, ((((a : ℕ) : ℤ)) + 1) * ∑ s : Fin n, (m (a.castSucc, s) : ℤ) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro a _
    apply Finset.sum_le_sum
    intro s _
    by_cases has : a.val < s.val
    · have : m (a.castSucc, s) = 0 := htri s.val s rfl a.castSucc (by simpa using has)
      rw [this]; simp
    · apply mul_le_mul_of_nonneg_right _ (by positivity)
      have : (s : ℕ) ≤ (a : ℕ) := by omega
      have : ((s : ℕ) : ℤ) ≤ ((a : ℕ) : ℤ) := by exact_mod_cast this
      linarith
  have e1 : (∑ s : Fin n, ((((s : ℕ) : ℤ)) + 1) * ((lam s : ℤ) - (sg s : ℤ))) =
      (∑ s : Fin n, ((((s : ℕ) : ℤ)) + 1) * ∑ a : Fin n, (m (a.castSucc, s) : ℤ)) +
      (∑ s : Fin n, ((((s : ℕ) : ℤ)) + 1) * (m (Fin.last n, s) : ℤ)) -
      ∑ a : Fin n, ((((a : ℕ) : ℤ)) + 1) * ∑ s : Fin n, (m (a.castSucc, s) : ℤ) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s _
    rw [hcol' s, hrow' s]
    ring
  rw [e1] at hl
  linarith

/- English proof (translation)
Proceed by induction on `ℓ with`. Consider the case `nil => simp`. Consider the case `cons a t ih`. Simplify using `only [List.map_cons, List.prod_cons]`. Use `show C a ((List.map C t).prod v) = _`.

Rewrite using `[ih, map_smul, h, smul_smul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem bm_list_eigen {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (C : ℤ → Module.End R M)
    (χ : ℤ → ℤ) (v : M) (h : ∀ u, C u v = ((χ u : ℤ) : R) • v) (ℓ : List ℤ) :
    (ℓ.map C).prod v = (((ℓ.map χ).prod : ℤ) : R) • v := by
  induction ℓ with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.prod_cons]
    show C a ((List.map C t).prod v) = _
    rw [ih, map_smul, h, smul_smul]
    congr 1
    push_cast
    ring

/- English proof (translation)
Conclude with `LinearMap.congr_fun h.eq x`.
-/
theorem bmE_comm_apply {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {a b : Module.End R M}
    (h : Commute a b) (x : M) : a (b x) = b (a x) := by
  exact LinearMap.congr_fun h.eq x

/- English proof (translation)
Use extensionality with `d`. Use `congrArg (coeff d) (h (Finsupp.weight w d))` as an intermediate fact. Rewrite `this` using `[coeff_weightedHomogeneousComponent, if_pos rfl, coeff_zero]`. Rewrite using `[this, coeff_zero]`.
-/
theorem bmE_eq_zero_of_comp {R σ B : Type*} [CommRing R] [AddCommMonoid B] (w : σ → B)
    (G : MvPolynomial σ R) (h : ∀ β, weightedHomogeneousComponent w β G = 0) : G = 0 := by
  classical
  ext d
  have := congrArg (coeff d) (h (Finsupp.weight w d))
  rw [coeff_weightedHomogeneousComponent, if_pos rfl, coeff_zero] at this
  rw [this, coeff_zero]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨d, hd⟩` from `MvPolynomial.ne_zero_iff.mp h`. Rewrite `hd` using `[coeff_weightedHomogeneousComponent]`. Use `split_ifs at hd with hw`.

Conclude with `Finset.mem_image.mpr ⟨d, mem_support_iff.mpr hd, hw⟩`. Conclude with `absurd rfl hd`. Introduce `h`. Take `⟨d, hd, hw⟩` from `Finset.mem_image.mp h`. Introduce `h0`.

Use `congrArg (coeff d) h0` as an intermediate fact. Rewrite `this` using `[coeff_weightedHomogeneousComponent, if_pos hw, coeff_zero]`. Conclude with `mem_support_iff.mp hd this`.
-/
theorem bmE_comp_ne_iff {R σ B : Type*} [CommRing R] [AddCommMonoid B] [DecidableEq B] (w : σ → B)
    (G : MvPolynomial σ R) (β : B) :
    weightedHomogeneousComponent w β G ≠ 0 ↔ β ∈ G.support.image (Finsupp.weight w) := by
  classical
  constructor
  · intro h
    obtain ⟨d, hd⟩ := MvPolynomial.ne_zero_iff.mp h
    rw [coeff_weightedHomogeneousComponent] at hd
    split_ifs at hd with hw
    · exact Finset.mem_image.mpr ⟨d, mem_support_iff.mpr hd, hw⟩
    · exact absurd rfl hd
  · intro h
    obtain ⟨d, hd, hw⟩ := Finset.mem_image.mp h
    intro h0
    have := congrArg (coeff d) h0
    rw [coeff_weightedHomogeneousComponent, if_pos hw, coeff_zero] at this
    exact mem_support_iff.mp hd this

/- English proof (translation)
Establish `hempty : ∀ β0 : B, ∃ (Q : Module.End R (MvPolynomial σ R)) (q : ℤ), q ≠ 0 ∧ (∀ u, Commute Q (C u)) ∧ (∀ β, Commute (weightedHomogeneousComponent w β : Module.End R (MvPolynomial σ R)) Q) ∧ (∀ G ∈ W, Q G ∈ W) ∧ (∀ F, (∀ u, C u F = ((χ β0 u : ℤ) : R) • F) → Q F = ((q : ℤ) : R) • F) …`. Introduce `β0`. Use `⟨1, 1, one_ne_zero, fun u => Commute.one_left _, fun β => Commute.one_right _, fun G hG => by simpa using hG, fun F _ => by simp, fun G _ hS => ?_⟩` and prove the remaining obligations. Rewrite using `[bmE_eq_zero_of_comp w G (fun β => by_contra fun hne => absurd (hS β hne) (Finset.notMem_empty β))]`. Simplify using the standard rewrite rules.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `S β0 hS _ _`. Establish `hS0 : S = ∅` using `Finset.card_eq_zero.1 (Nat.le_zero.1 hS)`.

Substitute `hS0` using the available equality. Conclude with `hempty β0`. Consider the case `succ k ih`. Introduce `S β0 hS hA0 h0S`. Break down `S.eq_empty_or_nonempty with rfl | hne` into its components or cases.

Conclude with `hempty β0`. Take `⟨β1, hβ1, hmax⟩` from `Finset.exists_max_image S ω hne`. Establish `hcard : (S.erase β1).card ≤ k`. Rewrite using `[Finset.card_erase_of_mem hβ1]`. Use linear arithmetic over natural numbers and integers.

Establish `h0S' : β0 ∉ S.erase β1` using `fun h => h0S (Finset.mem_of_mem_erase h)`. Take `⟨Q', q', hq', hQC, hQc, hQW, hQe, hQk⟩` from `ih (S.erase β1) β0 hcard hA0 h0S'`. Distinguish the cases in `hA1 : admitted β1`. Establish `hne01 : β0 ≠ β1` using `fun h => h0S (h ▸ hβ1)`. Take `⟨u, hu⟩` from `hSep β0 β1 hA0 hA1 hne01`.

Use `set T : Module.End R (MvPolynomial σ R) := C u - ((χ β1 u : ℤ) : R) • 1 with hT`. Establish `hTa : ∀ G, T G = C u G - ((χ β1 u : ℤ) : R) • G` using `fun G => by simp [hT]`. Use `⟨Q' * T, q' * (χ β0 u - χ β1 u), mul_ne_zero hq' (sub_ne_zero.2 hu), ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `v`. Conclude with `(hQC v).mul_left ((hCC u v).sub_left ((Commute.one_left _).smul_left _))`.

Introduce `β`. Conclude with `(hQc β).mul_right ((hCc u β).sub_right ((Commute.one_right _).smul_right _))`. Introduce `G hG`. Rewrite using `[Module.End.mul_apply, hTa]`. Conclude with `hQW _ (W.sub_mem (hCW u G hG) (W.smul_mem _ hG))`.

Introduce `F hF`. Rewrite using `[Module.End.mul_apply, hTa, hF u, ← sub_smul, map_smul, hQe F hF, smul_smul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Introduce `G hG hS`. Rewrite using `[Module.End.mul_apply]`. Apply `hQk (T G) (by rw [hTa]; exact W.sub_mem (hCW u G hG) (W.smul_mem _ hG))` to reduce the goal to its premises. Introduce `β hβ`. Establish `hcomp : weightedHomogeneousComponent w β (T G) = T (weightedHomogeneousComponent w β G)`.

Rewrite using `[hTa, hTa, map_sub, map_smul, bmE_comm_apply (hCc u β)]`. Rewrite `hβ` using `[hcomp]`. Establish `hβG : weightedHomogeneousComponent w β G ≠ 0` using `fun h0 => hβ (by rw [h0, map_zero])`. Use `Finset.mem_erase.2 ⟨?_, hS β hβG⟩` and prove the remaining obligations. Introduce and unpack `rfl`.

Apply `hβ` to reduce the goal to its premises. Rewrite using `[hTa, (hEig G hG β hβG (fun β' hβ' => hmax β' (hS β' hβ'))).2 u, sub_self]`. Use `⟨Q', q', hq', hQC, hQc, hQW, hQe, fun G hG hS => hQk G hG fun β hβ => Finset.mem_erase.2 ⟨?_, hS β hβ⟩⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `hA1 (hEig G hG β hβ (fun β' hβ' => hmax β' (hS β' hβ'))).1`.
-/
theorem bmE_sep_op {R σ B : Type*} [CommRing R] [AddCommMonoid B] (w : σ → B) (ω : B → ℤ)
    (C : ℤ → Module.End R (MvPolynomial σ R)) (W : Submodule R (MvPolynomial σ R)) (χ : B → ℤ → ℤ)
    (admitted : B → Prop) (hCC : ∀ u v, Commute (C u) (C v))
    (hCc : ∀ u β, Commute (weightedHomogeneousComponent w β : Module.End R (MvPolynomial σ R)) (C u))
    (hCW : ∀ u, ∀ G ∈ W, C u G ∈ W)
    (hEig : ∀ G ∈ W, ∀ β, weightedHomogeneousComponent w β G ≠ 0 →
      (∀ β', weightedHomogeneousComponent w β' G ≠ 0 → ω β' ≤ ω β) →
      admitted β ∧ ∀ u, C u (weightedHomogeneousComponent w β G) =
        ((χ β u : ℤ) : R) • weightedHomogeneousComponent w β G)
    (hSep : ∀ β β', admitted β → admitted β' → β ≠ β' → ∃ u, χ β u ≠ χ β' u) :
    ∀ (k : ℕ) (S : Finset B) (β0 : B), S.card ≤ k → admitted β0 → β0 ∉ S →
      ∃ (Q : Module.End R (MvPolynomial σ R)) (q : ℤ), q ≠ 0 ∧ (∀ u, Commute Q (C u)) ∧
        (∀ β, Commute (weightedHomogeneousComponent w β : Module.End R (MvPolynomial σ R)) Q) ∧
        (∀ G ∈ W, Q G ∈ W) ∧
        (∀ F, (∀ u, C u F = ((χ β0 u : ℤ) : R) • F) → Q F = ((q : ℤ) : R) • F) ∧
        (∀ G ∈ W, (∀ β, weightedHomogeneousComponent w β G ≠ 0 → β ∈ S) → Q G = 0) := by
  classical
  have hempty : ∀ β0 : B,
      ∃ (Q : Module.End R (MvPolynomial σ R)) (q : ℤ), q ≠ 0 ∧ (∀ u, Commute Q (C u)) ∧
        (∀ β, Commute (weightedHomogeneousComponent w β : Module.End R (MvPolynomial σ R)) Q) ∧
        (∀ G ∈ W, Q G ∈ W) ∧
        (∀ F, (∀ u, C u F = ((χ β0 u : ℤ) : R) • F) → Q F = ((q : ℤ) : R) • F) ∧
        (∀ G ∈ W, (∀ β, weightedHomogeneousComponent w β G ≠ 0 → β ∈ (∅ : Finset B)) → Q G = 0) := by
    intro β0
    refine ⟨1, 1, one_ne_zero, fun u => Commute.one_left _, fun β => Commute.one_right _,
      fun G hG => by simpa using hG, fun F _ => by simp, fun G _ hS => ?_⟩
    rw [bmE_eq_zero_of_comp w G (fun β => by_contra fun hne => absurd (hS β hne) (Finset.notMem_empty β))]
    simp
  intro k
  induction k with
  | zero =>
    intro S β0 hS _ _
    have hS0 : S = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hS)
    subst hS0
    exact hempty β0
  | succ k ih =>
    intro S β0 hS hA0 h0S
    rcases S.eq_empty_or_nonempty with rfl | hne
    · exact hempty β0
    obtain ⟨β1, hβ1, hmax⟩ := Finset.exists_max_image S ω hne
    have hcard : (S.erase β1).card ≤ k := by
      rw [Finset.card_erase_of_mem hβ1]; omega
    have h0S' : β0 ∉ S.erase β1 := fun h => h0S (Finset.mem_of_mem_erase h)
    obtain ⟨Q', q', hq', hQC, hQc, hQW, hQe, hQk⟩ := ih (S.erase β1) β0 hcard hA0 h0S'
    by_cases hA1 : admitted β1
    · have hne01 : β0 ≠ β1 := fun h => h0S (h ▸ hβ1)
      obtain ⟨u, hu⟩ := hSep β0 β1 hA0 hA1 hne01
      set T : Module.End R (MvPolynomial σ R) := C u - ((χ β1 u : ℤ) : R) • 1 with hT
      have hTa : ∀ G, T G = C u G - ((χ β1 u : ℤ) : R) • G := fun G => by simp [hT]
      refine ⟨Q' * T, q' * (χ β0 u - χ β1 u), mul_ne_zero hq' (sub_ne_zero.2 hu), ?_, ?_, ?_, ?_, ?_⟩
      · intro v
        exact (hQC v).mul_left ((hCC u v).sub_left ((Commute.one_left _).smul_left _))
      · intro β
        exact (hQc β).mul_right ((hCc u β).sub_right ((Commute.one_right _).smul_right _))
      · intro G hG
        rw [Module.End.mul_apply, hTa]
        exact hQW _ (W.sub_mem (hCW u G hG) (W.smul_mem _ hG))
      · intro F hF
        rw [Module.End.mul_apply, hTa, hF u, ← sub_smul, map_smul, hQe F hF, smul_smul]
        congr 1
        push_cast
        ring
      · intro G hG hS
        rw [Module.End.mul_apply]
        apply hQk (T G) (by rw [hTa]; exact W.sub_mem (hCW u G hG) (W.smul_mem _ hG))
        intro β hβ
        have hcomp : weightedHomogeneousComponent w β (T G) =
            T (weightedHomogeneousComponent w β G) := by
          rw [hTa, hTa, map_sub, map_smul, bmE_comm_apply (hCc u β)]
        rw [hcomp] at hβ
        have hβG : weightedHomogeneousComponent w β G ≠ 0 := fun h0 => hβ (by rw [h0, map_zero])
        refine Finset.mem_erase.2 ⟨?_, hS β hβG⟩
        rintro rfl
        apply hβ
        rw [hTa, (hEig G hG β hβG (fun β' hβ' => hmax β' (hS β' hβ'))).2 u, sub_self]
    · refine ⟨Q', q', hq', hQC, hQc, hQW, hQe, fun G hG hS => hQk G hG fun β hβ =>
        Finset.mem_erase.2 ⟨?_, hS β hβ⟩⟩
      rintro rfl
      exact hA1 (hEig G hG β hβ (fun β' hβ' => hmax β' (hS β' hβ'))).1

/- English proof (translation)
Establish `main : ∀ (k : ℕ) (G : MvPolynomial σ R), G ∈ W → (G.support.image (Finsupp.weight w)).card ≤ k → weightedHomogeneousComponent w b G = 0 → (ℓ.map C).prod G = 0`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `G _ hc _`.

Establish `h1` using `Finset.card_eq_zero.1 (Nat.le_zero.1 hc)`. Rewrite `h1` using `[Finset.image_eq_empty]`. Rewrite using `[support_eq_empty.1 h1, map_zero]`. Consider the case `succ k ih`. Introduce `G hG hc hb`.

Break down `(G.support.image (Finsupp.weight w)).eq_empty_or_nonempty with h0 | hne` into its components or cases. Rewrite `h0` using `[Finset.image_eq_empty]`. Rewrite using `[support_eq_empty.1 h0, map_zero]`. Take `⟨β0, hβ0, hmax⟩` from `Finset.exists_max_image _ ω hne`. Establish `hF0 : weightedHomogeneousComponent w β0 G ≠ 0` using `(bmE_comp_ne_iff w G β0).2 hβ0`.

Take `⟨hA0, hE0⟩` from `hEig G hG β0 hF0 (fun β' hβ' => hmax β' ((bmE_comp_ne_iff w G β').1 hβ'))`. Establish `hne0 : β0 ≠ b` using `fun h => hF0 (h ▸ hb)`. Take `⟨Q, q, hq, hQC, hQc, hQW, hQe, hQk⟩` from `bmE_sep_op w ω C W χ admitted hCC hCc hCW hEig hSep _ ((G.support.image (Finsupp.weight w)).erase β0) β0 le_rfl hA0 (Finset.notMem_erase _ _)`. Establish `hQG : ∀ u, C u (Q G) = ((χ β0 u : ℤ) : R) • Q G`. Introduce `u`.

Establish `h1 : Q (C u G - ((χ β0 u : ℤ) : R) • G) = 0`. Apply `hQk _ (W.sub_mem (hCW u G hG) (W.smul_mem _ hG))` to reduce the goal to its premises. Introduce `β hβ`. Rewrite `hβ` using `[map_sub, map_smul, bmE_comm_apply (hCc u β)]`. Use `Finset.mem_erase.2 ⟨?_, (bmE_comp_ne_iff w G β).1 (fun h0 => hβ (by rw [h0]; simp))⟩` and prove the remaining obligations.

Introduce and unpack `rfl`. Conclude with `hβ (by rw [hE0 u, sub_self])`. Rewrite `h1` using `[map_sub, map_smul, sub_eq_zero]`. Rewrite using `[← bmE_comm_apply (hQC u) G, h1]`. Establish `hZ1 : (ℓ.map C).prod (Q G) = 0`.

Rewrite using `[bm_list_eigen C (χ β0) (Q G) hQG ℓ]`. Take `⟨u, hu, hχ⟩` from `hℓ β0 hA0 hne0`. Establish `h0 : (ℓ.map (χ β0)).prod = 0` using `List.prod_eq_zero (List.mem_map.2 ⟨u, hu, hχ⟩)`. Rewrite using `[h0]`. Simplify using the standard rewrite rules.

Establish `hcomp : ∀ β, weightedHomogeneousComponent w β (((q : ℤ) : R) • G - Q G) = ((q : ℤ) : R) • weightedHomogeneousComponent w β G - Q (weightedHomogeneousComponent w β G)`. Introduce `β`. Rewrite using `[map_sub, map_smul, bmE_comm_apply (hQc β)]`. Establish `hsub : ((((q : ℤ) : R) • G - Q G).support.image (Finsupp.weight w)) ⊆ (G.support.image (Finsupp.weight w)).erase β0`. Introduce `β hβ`.

Establish `hβ'` using `(bmE_comp_ne_iff w _ β).2 hβ`. Rewrite `hβ'` using `[hcomp]`. Use `Finset.mem_erase.2 ⟨?_, (bmE_comp_ne_iff w G β).1 (fun h0 => hβ' (by rw [h0]; simp))⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `hβ' (by rw [hQe _ hE0, sub_self])`.

Establish `hcard : ((((q : ℤ) : R) • G - Q G).support.image (Finsupp.weight w)).card ≤ k`. Establish `h1` using `Finset.card_le_card hsub`. Rewrite `h1` using `[Finset.card_erase_of_mem hβ0]`. Use linear arithmetic over natural numbers and integers. Establish `h2` using `ih (((q : ℤ) : R) • G - Q G) (W.sub_mem (W.smul_mem _ hG) (hQW G hG)) hcard (by rw [hcomp, hb]; simp)`.

Rewrite `h2` using `[map_sub, map_smul, hZ1, sub_zero]`. Conclude with `(smul_eq_zero.1 h2).resolve_left (Int.cast_ne_zero.2 hq)`. Conclude with `main _ G hG le_rfl hb`.
-/
theorem bm_kill {R σ B : Type*} [CommRing R] [IsDomain R] [CharZero R] [AddCommMonoid B] (w : σ → B) (ω : B → ℤ)
    (C : ℤ → Module.End R (MvPolynomial σ R)) (W : Submodule R (MvPolynomial σ R)) (χ : B → ℤ → ℤ)
    (admitted : B → Prop) (hCC : ∀ u v, Commute (C u) (C v))
    (hCc : ∀ u β, Commute (weightedHomogeneousComponent w β : Module.End R (MvPolynomial σ R)) (C u))
    (hCW : ∀ u, ∀ G ∈ W, C u G ∈ W)
    (hEig : ∀ G ∈ W, ∀ β, weightedHomogeneousComponent w β G ≠ 0 →
      (∀ β', weightedHomogeneousComponent w β' G ≠ 0 → ω β' ≤ ω β) →
      admitted β ∧ ∀ u, C u (weightedHomogeneousComponent w β G) =
        ((χ β u : ℤ) : R) • weightedHomogeneousComponent w β G)
    (hSep : ∀ β β', admitted β → admitted β' → β ≠ β' → ∃ u, χ β u ≠ χ β' u)
    (ℓ : List ℤ) (b : B) (hℓ : ∀ β, admitted β → β ≠ b → ∃ u ∈ ℓ, χ β u = 0)
    (G : MvPolynomial σ R) (hG : G ∈ W) (hb : weightedHomogeneousComponent w b G = 0) :
    (ℓ.map C).prod G = 0 := by
  classical
  have main : ∀ (k : ℕ) (G : MvPolynomial σ R), G ∈ W →
      (G.support.image (Finsupp.weight w)).card ≤ k →
      weightedHomogeneousComponent w b G = 0 → (ℓ.map C).prod G = 0 := by
    intro k
    induction k with
    | zero =>
      intro G _ hc _
      have h1 := Finset.card_eq_zero.1 (Nat.le_zero.1 hc)
      rw [Finset.image_eq_empty] at h1
      rw [support_eq_empty.1 h1, map_zero]
    | succ k ih =>
      intro G hG hc hb
      rcases (G.support.image (Finsupp.weight w)).eq_empty_or_nonempty with h0 | hne
      · rw [Finset.image_eq_empty] at h0
        rw [support_eq_empty.1 h0, map_zero]
      obtain ⟨β0, hβ0, hmax⟩ := Finset.exists_max_image _ ω hne
      have hF0 : weightedHomogeneousComponent w β0 G ≠ 0 := (bmE_comp_ne_iff w G β0).2 hβ0
      obtain ⟨hA0, hE0⟩ := hEig G hG β0 hF0
        (fun β' hβ' => hmax β' ((bmE_comp_ne_iff w G β').1 hβ'))
      have hne0 : β0 ≠ b := fun h => hF0 (h ▸ hb)
      obtain ⟨Q, q, hq, hQC, hQc, hQW, hQe, hQk⟩ :=
        bmE_sep_op w ω C W χ admitted hCC hCc hCW hEig hSep _
          ((G.support.image (Finsupp.weight w)).erase β0) β0 le_rfl hA0 (Finset.notMem_erase _ _)
      have hQG : ∀ u, C u (Q G) = ((χ β0 u : ℤ) : R) • Q G := by
        intro u
        have h1 : Q (C u G - ((χ β0 u : ℤ) : R) • G) = 0 := by
          apply hQk _ (W.sub_mem (hCW u G hG) (W.smul_mem _ hG))
          intro β hβ
          rw [map_sub, map_smul, bmE_comm_apply (hCc u β)] at hβ
          refine Finset.mem_erase.2 ⟨?_, (bmE_comp_ne_iff w G β).1 (fun h0 => hβ (by rw [h0]; simp))⟩
          rintro rfl
          exact hβ (by rw [hE0 u, sub_self])
        rw [map_sub, map_smul, sub_eq_zero] at h1
        rw [← bmE_comm_apply (hQC u) G, h1]
      have hZ1 : (ℓ.map C).prod (Q G) = 0 := by
        rw [bm_list_eigen C (χ β0) (Q G) hQG ℓ]
        obtain ⟨u, hu, hχ⟩ := hℓ β0 hA0 hne0
        have h0 : (ℓ.map (χ β0)).prod = 0 := List.prod_eq_zero (List.mem_map.2 ⟨u, hu, hχ⟩)
        rw [h0]
        simp
      have hcomp : ∀ β, weightedHomogeneousComponent w β (((q : ℤ) : R) • G - Q G) =
          ((q : ℤ) : R) • weightedHomogeneousComponent w β G -
            Q (weightedHomogeneousComponent w β G) := by
        intro β
        rw [map_sub, map_smul, bmE_comm_apply (hQc β)]
      have hsub : ((((q : ℤ) : R) • G - Q G).support.image (Finsupp.weight w)) ⊆
          (G.support.image (Finsupp.weight w)).erase β0 := by
        intro β hβ
        have hβ' := (bmE_comp_ne_iff w _ β).2 hβ
        rw [hcomp] at hβ'
        refine Finset.mem_erase.2 ⟨?_, (bmE_comp_ne_iff w G β).1 (fun h0 => hβ' (by rw [h0]; simp))⟩
        rintro rfl
        exact hβ' (by rw [hQe _ hE0, sub_self])
      have hcard : ((((q : ℤ) : R) • G - Q G).support.image (Finsupp.weight w)).card ≤ k := by
        have h1 := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hβ0] at h1
        omega
      have h2 := ih (((q : ℤ) : R) • G - Q G) (W.sub_mem (W.smul_mem _ hG) (hQW G hG)) hcard
        (by rw [hcomp, hb]; simp)
      rw [map_sub, map_smul, hZ1, sub_zero] at h2
      exact (smul_eq_zero.1 h2).resolve_left (Int.cast_ne_zero.2 hq)
  exact main _ G hG le_rfl hb

/- English proof (translation)
Simplify using `[lamZ]`.
-/
theorem bmH_lamZ_castSucc {n : ℕ} (lam : Fin n → ℕ) (i : Fin n) :
    lamZ lam i.castSucc = (lam i : ℤ) := by
  simp [lamZ]

/- English proof (translation)
Apply the tactic sequence `by_cases h : i.val + 1 < n <;> simp [lamZ, nuNext, h]`.
-/
theorem bmH_lamZ_succ {n : ℕ} (lam : Fin n → ℕ) (i : Fin n) :
    lamZ lam i.succ = (nuNext lam i : ℤ) := by
  by_cases h : i.val + 1 < n <;> simp [lamZ, nuNext, h]

/- English proof (translation)
Introduce `i`. Establish `h1 : (sg i : ℤ) ≤ lam i`. Use `(hI i).1` as an intermediate fact. Rewrite `this` using `[bmH_lamZ_castSucc]`. Then use the resulting hypothesis. Establish `h2 : (nuNext lam i : ℤ) ≤ sg i`.

Use `(hI i).2` as an intermediate fact. Rewrite `this` using `[bmH_lamZ_succ]`. Then use the resulting hypothesis. Conclude with `⟨by exact_mod_cast h1, by exact_mod_cast h2⟩`.
-/
theorem bm_IL_of {n : ℕ} (lam sg : Fin n → ℕ) (hI : Interlace (lamZ lam) (fun i => (sg i : ℤ))) : bmIL lam sg := by
  intro i
  have h1 : (sg i : ℤ) ≤ lam i := by
    have := (hI i).1
    rwa [bmH_lamZ_castSucc] at this
  have h2 : (nuNext lam i : ℤ) ≤ sg i := by
    have := (hI i).2
    rwa [bmH_lamZ_succ] at this
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/- English proof (translation)
Conclude with `Fin.antitone_iff_succ_le.mpr fun i => le_trans (h i).2 (h i).1`.
-/
theorem bmH_anti {n : ℕ} (L : Fin (n + 1) → ℤ) (μ : Fin n → ℤ) (h : Interlace L μ) : Antitone L := by
  exact Fin.antitone_iff_succ_le.mpr fun i => le_trans (h i).2 (h i).1

/- English proof (translation)
Establish `hA` using `bmH_anti L μ hμ`. Break down `lt_or_gt_of_ne hij with h | h` into its components or cases. Establish `hl : i.succ ≤ j.castSucc`. Rewrite using `[Fin.le_iff_val_le_val, Fin.val_succ, Fin.coe_castSucc]`. Conclude with `Fin.lt_iff_val_lt_val.mp h`.

Establish `e1` using `hA hl`. Establish `e2` using `(hν i).2`. Establish `e3` using `(hμ j).1`. Establish `hv : (i : ℕ) < (j : ℕ)` using `Fin.lt_iff_val_lt_val.mp h`. Use linear arithmetic over natural numbers and integers.

Establish `hl : j.succ ≤ i.castSucc`. Rewrite using `[Fin.le_iff_val_le_val, Fin.val_succ, Fin.coe_castSucc]`. Conclude with `Fin.lt_iff_val_lt_val.mp h`. Establish `e1` using `hA hl`. Establish `e2` using `(hμ j).2`.

Establish `e3` using `(hν i).1`. Establish `hv : (j : ℕ) < (i : ℕ)` using `Fin.lt_iff_val_lt_val.mp h`. Use linear arithmetic over natural numbers and integers.
-/
theorem bmH_disj {n : ℕ} (L : Fin (n + 1) → ℤ) (μ ν : Fin n → ℤ) (hμ : Interlace L μ) (hν : Interlace L ν)
    (i j : Fin n) (hij : i ≠ j) : (ν i - ((i : ℕ) : ℤ)) - (μ j - ((j : ℕ) : ℤ)) ≠ 0 := by
  have hA := bmH_anti L μ hμ
  rcases lt_or_gt_of_ne hij with h | h
  · have hl : i.succ ≤ j.castSucc := by
      rw [Fin.le_iff_val_le_val, Fin.val_succ, Fin.coe_castSucc]
      exact Fin.lt_iff_val_lt_val.mp h
    have e1 := hA hl
    have e2 := (hν i).2
    have e3 := (hμ j).1
    have hv : (i : ℕ) < (j : ℕ) := Fin.lt_iff_val_lt_val.mp h
    omega
  · have hl : j.succ ≤ i.castSucc := by
      rw [Fin.le_iff_val_le_val, Fin.val_succ, Fin.coe_castSucc]
      exact Fin.lt_iff_val_lt_val.mp h
    have e1 := hA hl
    have e2 := (hμ j).2
    have e3 := (hν i).1
    have hv : (j : ℕ) < (i : ℕ) := Fin.lt_iff_val_lt_val.mp h
    omega

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, β i ≠ β' i := by`. Assume the negation of the conclusion as `hc`. Conclude with `hne (funext fun i => by by_contra h''; exact hc ⟨i, h''⟩)`. Use `⟨((lam i : ℤ) - β' i) - ((i : ℕ) : ℤ), ?_⟩` and prove the remaining obligations. Establish `h0 : bmChi lam β' (((lam i : ℤ) - β' i) - ((i : ℕ) : ℤ)) = 0`.

Unfold `bmChi`. Apply `Finset.prod_eq_zero (Finset.mem_univ i)` to reduce the goal to its premises. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h0]`. Unfold `bmChi`.

Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `j _`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Introduce `hc`.

Apply `hi` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Use `bmH_disj (lamZ lam) (fun i => (lam i : ℤ) - β i) (fun i => (lam i : ℤ) - β' i) h.2.2 h'.2.2 i j hij` as an intermediate fact. Introduce `hc`. Apply `this` to reduce the goal to its premises.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem bm_sep {n : ℕ} (lam : Fin n → ℕ) (d : ℕ) (β β' : Fin n → ℤ) (h : bmAdm lam d β) (h' : bmAdm lam d β')
    (hne : β ≠ β') : ∃ u, bmChi lam β u ≠ bmChi lam β' u := by
  obtain ⟨i, hi⟩ : ∃ i, β i ≠ β' i := by
    by_contra hc
    exact hne (funext fun i => by by_contra h''; exact hc ⟨i, h''⟩)
  refine ⟨((lam i : ℤ) - β' i) - ((i : ℕ) : ℤ), ?_⟩
  have h0 : bmChi lam β' (((lam i : ℤ) - β' i) - ((i : ℕ) : ℤ)) = 0 := by
    unfold bmChi
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    ring
  rw [h0]
  unfold bmChi
  rw [Finset.prod_ne_zero_iff]
  intro j _
  by_cases hij : i = j
  · subst hij
    intro hc
    apply hi
    linarith
  · have := bmH_disj (lamZ lam) (fun i => (lam i : ℤ) - β i) (fun i => (lam i : ℤ) - β' i) h.2.2 h'.2.2 i j hij
    intro hc
    apply this
    linarith

/- English proof (translation)
Establish `hIL` using `bm_IL_of lam sg hI`. Establish `hcast : ∀ s, ((lam s - sg s : ℕ) : ℤ) = (lam s : ℤ) - (sg s : ℤ)` using `fun s => Nat.cast_sub (hIL s).1`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, β i ≠ ((lam i - sg i : ℕ) : ℤ) := by`. Assume the negation of the conclusion as `hc`. Conclude with `hne (funext fun i => by by_contra h''; exact hc ⟨i, h''⟩)`.

Use `⟨((lam i : ℤ) - β i) - ((i : ℕ) : ℤ), ?_, ?_⟩` and prove the remaining obligations. Unfold `bmList`. Rewrite using `[List.mem_flatMap]`. Use `⟨i, Finset.mem_toList.2 (Finset.mem_univ i), ?_⟩` and prove the remaining obligations. Rewrite using `[List.mem_map]`.

Use `⟨(lam i : ℤ) - β i, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[Finset.mem_toList, Finset.mem_erase]`. Prove the components needed by the constructor for the conclusion. Introduce `hc`. Apply `hi` to reduce the goal to its premises.

Rewrite using `[hcast]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `memBranchRangeOfDefectEq n (lamZ lam) (fun i => (sg i : ℤ)) (fun i => (lam i : ℤ) - β i) hI h.2.2 ?_ i` and prove the remaining obligations. Unfold `d0`. Rewrite using `[Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, h.2.1]`.

Use `push_cast`. Simplify using `only [hcast]`. Rewrite using `[Finset.sum_sub_distrib]`. Expand and normalize the polynomial expressions, which then agree. Unfold `bmChi`.

Apply `Finset.prod_eq_zero (Finset.mem_univ i)` to reduce the goal to its premises. Expand and normalize the polynomial expressions, which then agree.
-/
theorem bm_list_kills {n : ℕ} (lam sg : Fin n → ℕ) (hI : Interlace (lamZ lam) (fun i => (sg i : ℤ)))
    (β : Fin n → ℤ) (h : bmAdm lam (∑ s, (lam s - sg s)) β) (hne : β ≠ fun s => ((lam s - sg s : ℕ) : ℤ)) :
    ∃ u ∈ bmList lam sg, bmChi lam β u = 0 := by
  have hIL := bm_IL_of lam sg hI
  have hcast : ∀ s, ((lam s - sg s : ℕ) : ℤ) = (lam s : ℤ) - (sg s : ℤ) := fun s =>
    Nat.cast_sub (hIL s).1
  obtain ⟨i, hi⟩ : ∃ i, β i ≠ ((lam i - sg i : ℕ) : ℤ) := by
    by_contra hc
    exact hne (funext fun i => by by_contra h''; exact hc ⟨i, h''⟩)
  refine ⟨((lam i : ℤ) - β i) - ((i : ℕ) : ℤ), ?_, ?_⟩
  · unfold bmList
    rw [List.mem_flatMap]
    refine ⟨i, Finset.mem_toList.2 (Finset.mem_univ i), ?_⟩
    rw [List.mem_map]
    refine ⟨(lam i : ℤ) - β i, ?_, rfl⟩
    rw [Finset.mem_toList, Finset.mem_erase]
    constructor
    · intro hc
      apply hi
      rw [hcast]
      linarith
    · refine memBranchRangeOfDefectEq n (lamZ lam) (fun i => (sg i : ℤ)) (fun i => (lam i : ℤ) - β i) hI h.2.2 ?_ i
      unfold d0
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, h.2.1]
      push_cast
      simp only [hcast]
      rw [Finset.sum_sub_distrib]
      ring
  · unfold bmChi
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    ring

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons a t ih => simp [List.flatMap_cons, List.prod_append, ih]`.
-/
theorem bmH_flatMap_prod {α : Type*} (l : List α) (f : α → List ℤ) (g : ℤ → ℤ) :
    ((l.flatMap f).map g).prod = (l.map fun i => ((f i).map g).prod).prod := by
  induction l with
  | nil => simp
  | cons a t ih => simp [List.flatMap_cons, List.prod_append, ih]

/- English proof (translation)
Establish `hIL` using `bm_IL_of lam sg hI`. Establish `hcast : ∀ s, ((lam s - sg s : ℕ) : ℤ) = (lam s : ℤ) - (sg s : ℤ)` using `fun s => Nat.cast_sub (hIL s).1`. Unfold `bmList cCap capEig`. Rewrite using `[bmH_flatMap_prod, Finset.prod_map_toList]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[List.map_map, Finset.prod_map_toList]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp, bmChi]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hcast]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem bm_list_prod {n : ℕ} (lam sg : Fin n → ℕ) (hI : Interlace (lamZ lam) (fun i => (sg i : ℤ))) :
    ((bmList lam sg).map (bmChi lam fun s => ((lam s - sg s : ℕ) : ℤ))).prod =
      cCap (lamZ lam) (fun i => (sg i : ℤ)) := by
  have hIL := bm_IL_of lam sg hI
  have hcast : ∀ s, ((lam s - sg s : ℕ) : ℤ) = (lam s : ℤ) - (sg s : ℤ) := fun s =>
    Nat.cast_sub (hIL s).1
  unfold bmList cCap capEig
  rw [bmH_flatMap_prod, Finset.prod_map_toList]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [List.map_map, Finset.prod_map_toList]
  refine Finset.prod_congr rfl fun v _ => ?_
  simp only [Function.comp, bmChi]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [hcast]
  ring

/- English proof (translation)
Simplify using `only [omg, Pi.add_apply, mul_add, Finset.sum_add_distrib]`.
-/
theorem bmD_omg_add {n : ℕ} (β γ : Fin n → ℤ) : omg (β + γ) = omg β + omg γ := by
  simp only [omg, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [omg, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]`.
-/
theorem bmD_omg_sub {n : ℕ} (β γ : Fin n → ℤ) : omg (β - γ) = omg β - omg γ := by
  simp only [omg, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/- English proof (translation)
Simplify using `[omg, Pi.single_apply]`.
-/
theorem bmD_omg_single {n : ℕ} (s : Fin n) :
    omg (Pi.single s 1 : Fin n → ℤ) = ((s : ℕ) : ℤ) + 1 := by
  simp [omg, Pi.single_apply]

/- English proof (translation)
Conclude with `bm_whcWH_lemma_3 (zW n) β Y`.
-/
theorem bmD_zcomp_isWH {R : Type*} [CommRing R] {n : ℕ} (β : Fin n → ℤ) (Y : BP R n) :
    IsWeightedHomogeneous (zW n) (zcomp R n β Y) β := by
  exact bm_whcWH_lemma_3 (zW n) β Y

/- English proof (translation)
Conclude with `bmE_comm_apply (bm_zcomp_comm_bmEL R n β s t) Y`.
-/
theorem bmD_zcomp_bmE {R : Type*} [CommRing R] {n : ℕ} (β : Fin n → ℤ) (s t : Fin n) (Y : BP R n) :
    zcomp R n β (bmE R n s t Y) = bmE R n s t (zcomp R n β Y) := by
  exact bmE_comm_apply (bm_zcomp_comm_bmEL R n β s t) Y

/- English proof (translation)
Use `bm_zcomp_bmZ R n (β - (Pi.single l 1 - Pi.single j 1)) l j Y` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis.
-/
theorem bmD_zcomp_bmZ {R : Type*} [CommRing R] {n : ℕ} (β : Fin n → ℤ) (l j : Fin n) (Y : BP R n) :
    zcomp R n β (bmZ R n l j Y) =
      bmZ R n l j (zcomp R n (β - (Pi.single l 1 - Pi.single j 1)) Y) := by
  have := bm_zcomp_bmZ R n (β - (Pi.single l 1 - Pi.single j 1)) l j Y
  rwa [sub_add_cancel] at this

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Conclude with `absurd (hmax β' hne) (not_le.mpr h)`.
-/
theorem bmD_zero_of_gt {R : Type*} [CommRing R] {n : ℕ} (G : BP R n) (β : Fin n → ℤ)
    (hmax : ∀ β', zcomp R n β' G ≠ 0 → omg β' ≤ omg β) (β' : Fin n → ℤ) (h : omg β < omg β') :
    zcomp R n β' G = 0 := by
  by_contra hne
  exact absurd (hmax β' hne) (not_le.mpr h)

/- English proof (translation)
Establish `hG'` using `(bm_mem_dualWeyl_iff.mp hG).2 l j hlj`. Rewrite `hG'` using `[bm_ndE_eq, Derivation.add_apply]`. Establish `h1` using `congrArg (zcomp R n β) hG'`. Rewrite `h1` using `[map_add, bmD_zcomp_bmE, bmD_zcomp_bmZ, map_zero]`. Establish `h0 : zcomp R n (β - (Pi.single l 1 - Pi.single j 1)) G = 0`.

Apply `bmD_zero_of_gt G β hmax` to reduce the goal to its premises. Rewrite using `[bmD_omg_sub, bmD_omg_sub, bmD_omg_single, bmD_omg_single]`. Establish `: (l : ℕ) < (j : ℕ)` using `hlj`. Use linear arithmetic over natural numbers and integers. Rewrite `h1` using `[h0, map_zero, add_zero]`.

Conclude with `h1`.
-/
theorem bmD_raise {R : Type} [CommRing R] [IsDomain R] [CharZero R] {n : ℕ} (lam : Fin n → ℕ)
    (G : BP R n) (hG : G ∈ dualWeyl R (n + 1) n lam) (β : Fin n → ℤ)
    (hmax : ∀ β', zcomp R n β' G ≠ 0 → omg β' ≤ omg β) (l j : Fin n) (hlj : l < j) :
    bmE R n l j (zcomp R n β G) = 0 := by
  have hG' := (bm_mem_dualWeyl_iff.mp hG).2 l j hlj
  rw [bm_ndE_eq, Derivation.add_apply] at hG'
  have h1 := congrArg (zcomp R n β) hG'
  rw [map_add, bmD_zcomp_bmE, bmD_zcomp_bmZ, map_zero] at h1
  have h0 : zcomp R n (β - (Pi.single l 1 - Pi.single j 1)) G = 0 := by
    apply bmD_zero_of_gt G β hmax
    rw [bmD_omg_sub, bmD_omg_sub, bmD_omg_single, bmD_omg_single]
    have : (l : ℕ) < (j : ℕ) := hlj
    omega
  rw [h0, map_zero, add_zero] at h1
  exact h1

/- English proof (translation)
Establish `hG'` using `(bm_mem_dualWeyl_iff.mp hG).1 s`. Rewrite `hG'` using `[bm_ndEul_eq, Derivation.add_apply]`. Establish `h1` using `congrArg (zcomp R n β) hG'`. Rewrite `h1` using `[map_add, bmD_zcomp_bmE, map_smul]`. Establish `h2 : zcomp R n β (bmZ R n s s G) = ((β s : ℤ) : R) • zcomp R n β G`.

Rewrite using `[bmD_zcomp_bmZ, sub_self, sub_zero]`. Conclude with `bmZ_euler R n β s _ (bmD_zcomp_isWH β G)`. Rewrite `h1` using `[h2]`. Rewrite using `[eq_sub_of_add_eq h1]`. Use `push_cast`.

Rewrite using `[sub_smul]`.
-/
theorem bmD_weight {R : Type} [CommRing R] [IsDomain R] [CharZero R] {n : ℕ} (lam : Fin n → ℕ)
    (G : BP R n) (hG : G ∈ dualWeyl R (n + 1) n lam) (β : Fin n → ℤ) (s : Fin n) :
    bmE R n s s (zcomp R n β G) = (((lam s : ℤ) - β s : ℤ) : R) • zcomp R n β G := by
  have hG' := (bm_mem_dualWeyl_iff.mp hG).1 s
  rw [bm_ndEul_eq, Derivation.add_apply] at hG'
  have h1 := congrArg (zcomp R n β) hG'
  rw [map_add, bmD_zcomp_bmE, map_smul] at h1
  have h2 : zcomp R n β (bmZ R n s s G) = ((β s : ℤ) : R) • zcomp R n β G := by
    rw [bmD_zcomp_bmZ, sub_self, sub_zero]
    exact bmZ_euler R n β s _ (bmD_zcomp_isWH β G)
  rw [h2] at h1
  rw [eq_sub_of_add_eq h1]
  push_cast
  rw [sub_smul]

/- English proof (translation)
Establish `hne : l ≠ j` using `ne_of_lt hlj`. Establish `hl` using `(bm_mem_dualWeyl_iff.1 hG).1 l`. Establish `hj` using `(bm_mem_dualWeyl_iff.1 hG).1 j`. Establish `hE` using `(bm_mem_dualWeyl_iff.1 hG).2 l j hlj`. Establish `hN : (ndF R r n l j)^[lam l + 1] G = 0`.

Apply `ndEul_neg_eq_zero l` to reduce the goal to its premises. Rewrite using `[nd_iter_Eul_l hne hl, Nat.cast_succ, show (lam l : R) - ((lam l : R) + 1) = -1 by ring, neg_one_smul]`. Establish `hstep : ∀ k : ℕ, (lam l : ℤ) - (lam j : ℤ) < (k : ℤ) → (ndF R r n l j)^[k + 1] G = 0 → (ndF R r n l j)^[k] G = 0`. Introduce `k hk hk1`. Establish `h1` using `nd_iter_E hne hl hj hE k`.

Rewrite `h1` using `[hk1, map_zero]`. Establish `hc : (((k : R) + 1) * ((lam l : R) - (lam j : R) - k)) ≠ 0`. Use `mul_ne_zero (Nat.cast_add_one_ne_zero k) ?_` and prove the remaining obligations. Establish `: (lam l : R) - (lam j : R) - k = (((lam l : ℤ) - lam j - k : ℤ) : R)` using `by push_cast; ring`. Rewrite using `[this, Int.cast_ne_zero]`.

Use linear arithmetic over natural numbers and integers. Conclude with `(smul_eq_zero.1 h1.symm).resolve_left hc`. Establish `hdown : ∀ e k : ℕ, (lam l : ℤ) - (lam j : ℤ) < (k : ℤ) → (ndF R r n l j)^[k + e] G = 0 → (ndF R r n l j)^[k] G = 0`. Introduce `e`. Proceed by induction on `e with`.

Consider the case `zero => intro k _ hk0`. Simplify using `using hk0`. Consider the case `succ e ih`. Introduce `k hk hk0`. Use `hstep k hk (ih (k + 1) (by push_cast; omega) ?_)` and prove the remaining obligations.

Rewrite using `[show k + 1 + e = k + (e + 1) by omega]`. Conclude with `hk0`. Use `hdown (lam l + 1) k hk ?_` and prove the remaining obligations. Rewrite using `[Function.iterate_add_apply, hN]`. Conclude with `Function.iterate_fixed (map_zero _) k`.
-/
theorem bmD_nil {R : Type} [CommRing R] [IsDomain R] [CharZero R] {r n : ℕ} (lam : Fin n → ℕ)
    (G : MvPolynomial (Fin r × Fin n) R) (hG : G ∈ dualWeyl R r n lam) (l j : Fin n) (hlj : l < j)
    (k : ℕ) (hk : (lam l : ℤ) - (lam j : ℤ) < (k : ℤ)) : (ndF R r n l j)^[k] G = 0 := by
  have hne : l ≠ j := ne_of_lt hlj
  have hl := (bm_mem_dualWeyl_iff.1 hG).1 l
  have hj := (bm_mem_dualWeyl_iff.1 hG).1 j
  have hE := (bm_mem_dualWeyl_iff.1 hG).2 l j hlj
  have hN : (ndF R r n l j)^[lam l + 1] G = 0 := by
    apply ndEul_neg_eq_zero l
    rw [nd_iter_Eul_l hne hl, Nat.cast_succ, show (lam l : R) - ((lam l : R) + 1) = -1 by ring,
      neg_one_smul]
  have hstep : ∀ k : ℕ, (lam l : ℤ) - (lam j : ℤ) < (k : ℤ) → (ndF R r n l j)^[k + 1] G = 0 →
      (ndF R r n l j)^[k] G = 0 := by
    intro k hk hk1
    have h1 := nd_iter_E hne hl hj hE k
    rw [hk1, map_zero] at h1
    have hc : (((k : R) + 1) * ((lam l : R) - (lam j : R) - k)) ≠ 0 := by
      refine mul_ne_zero (Nat.cast_add_one_ne_zero k) ?_
      have : (lam l : R) - (lam j : R) - k = (((lam l : ℤ) - lam j - k : ℤ) : R) := by
        push_cast; ring
      rw [this, Int.cast_ne_zero]
      omega
    exact (smul_eq_zero.1 h1.symm).resolve_left hc
  have hdown : ∀ e k : ℕ, (lam l : ℤ) - (lam j : ℤ) < (k : ℤ) → (ndF R r n l j)^[k + e] G = 0 →
      (ndF R r n l j)^[k] G = 0 := by
    intro e
    induction e with
    | zero => intro k _ hk0; simpa using hk0
    | succ e ih =>
      intro k hk hk0
      refine hstep k hk (ih (k + 1) (by push_cast; omega) ?_)
      rw [show k + 1 + e = k + (e + 1) by omega]
      exact hk0
  refine hdown (lam l + 1) k hk ?_
  rw [Function.iterate_add_apply, hN]
  exact Function.iterate_fixed (map_zero _) k

/- English proof (translation)
Establish `hδ : omg (Pi.single j 1 - Pi.single l 1 : Fin n → ℤ) = 1`. Rewrite using `[bmD_omg_sub, bmD_omg_single, bmD_omg_single, hj]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Proceed by induction on `k with`.

Consider the case `zero`. Use `⟨fun β' h => ?_, by simp, by simp⟩` and prove the remaining obligations. Rewrite using `[Function.iterate_zero, id]`. Conclude with `bmD_zero_of_gt G β hmax β' (by simpa using h)`. Consider the case `succ k ih`.

Take `⟨ih1, ih2, ih3⟩` from `ih`. Establish `hexp : ∀ β', zcomp R n β' ((ndF R (n + 1) n l j)^[k + 1] G) = bmE R n j l (zcomp R n β' ((ndF R (n + 1) n l j)^[k] G)) + bmZ R n j l (zcomp R n (β' - (Pi.single j 1 - Pi.single l 1)) ((ndF R (n + 1) n l j)^[k] G))`. Introduce `β'`. Rewrite using `[Function.iterate_succ_apply', bm_ndF_eq, Derivation.add_apply, map_add, bmD_zcomp_bmE, bmD_zcomp_bmZ]`. Establish `h2 : omg (β + (k + 1) • (Pi.single j 1 - Pi.single l 1)) = omg β + ((k + 1 : ℕ) : ℤ)`.

Rewrite using `[succ_nsmul, ← add_assoc, bmD_omg_add, ih2, hδ]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `⟨fun β' h => ?_, h2, ?_⟩` and prove the remaining obligations. Rewrite using `[hexp, ih1 β' (by push_cast at h; linarith), ih1 _ (by`.

Rewrite using `[bmD_omg_sub, hδ]`. Move the coercions through the operations in `at h`. Use the proof step `linarith), map_zero, map_zero, add_zero]`. Rewrite using `[hexp, ih1 _ (by rw [h2]; push_cast; linarith), map_zero, zero_add, Function.iterate_succ_apply', ← ih3]`. Use `congr 2`.

Rewrite using `[succ_nsmul, ← add_assoc, add_sub_cancel_right]`.
-/
theorem bmD_top {R : Type} [CommRing R] {n : ℕ} (G : BP R n) (β : Fin n → ℤ)
    (hmax : ∀ β', zcomp R n β' G ≠ 0 → omg β' ≤ omg β) (l j : Fin n) (hj : j.val = l.val + 1) (k : ℕ) :
    (∀ β', omg β + (k : ℤ) < omg β' → zcomp R n β' ((ndF R (n + 1) n l j)^[k] G) = 0) ∧
      omg (β + k • (Pi.single j 1 - Pi.single l 1)) = omg β + (k : ℤ) ∧
      zcomp R n (β + k • (Pi.single j 1 - Pi.single l 1)) ((ndF R (n + 1) n l j)^[k] G) =
        (bmZ R n j l)^[k] (zcomp R n β G) := by
  have hδ : omg (Pi.single j 1 - Pi.single l 1 : Fin n → ℤ) = 1 := by
    rw [bmD_omg_sub, bmD_omg_single, bmD_omg_single, hj]
    push_cast; ring
  induction k with
  | zero =>
    refine ⟨fun β' h => ?_, by simp, by simp⟩
    rw [Function.iterate_zero, id]
    exact bmD_zero_of_gt G β hmax β' (by simpa using h)
  | succ k ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    have hexp : ∀ β', zcomp R n β' ((ndF R (n + 1) n l j)^[k + 1] G) =
        bmE R n j l (zcomp R n β' ((ndF R (n + 1) n l j)^[k] G)) +
          bmZ R n j l (zcomp R n (β' - (Pi.single j 1 - Pi.single l 1))
            ((ndF R (n + 1) n l j)^[k] G)) := by
      intro β'
      rw [Function.iterate_succ_apply', bm_ndF_eq, Derivation.add_apply, map_add, bmD_zcomp_bmE,
        bmD_zcomp_bmZ]
    have h2 : omg (β + (k + 1) • (Pi.single j 1 - Pi.single l 1)) = omg β + ((k + 1 : ℕ) : ℤ) := by
      rw [succ_nsmul, ← add_assoc, bmD_omg_add, ih2, hδ]
      push_cast; ring
    refine ⟨fun β' h => ?_, h2, ?_⟩
    · rw [hexp, ih1 β' (by push_cast at h; linarith), ih1 _ (by
        rw [bmD_omg_sub, hδ]; push_cast at h; linarith), map_zero, map_zero, add_zero]
    · rw [hexp, ih1 _ (by rw [h2]; push_cast; linarith), map_zero, zero_add,
        Function.iterate_succ_apply', ← ih3]
      congr 2
      rw [succ_nsmul, ← add_assoc, add_sub_cancel_right]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Choose the witnesses or unpack the hypotheses as in `⟨m, hm⟩ : ∃ m, coeff m (zcomp R n β G) ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `hβ (MvPolynomial.ext _ _ fun m => ?_)` and prove the remaining obligations. Rewrite using `[coeff_zero]`.

Assume the negation of the conclusion as `hm0`. Conclude with `hcon ⟨m, hm0⟩`. Establish `hm' : Finsupp.weight (zW n) m = β ∧ coeff m G ≠ 0`. Unfold `zcomp at hm`. Rewrite `hm` using `[coeff_weightedHomogeneousComponent]`.

Distinguish the cases in `hw : Finsupp.weight (zW n) m = β`. Rewrite `hm` using `[if_pos hw]`. Conclude with `⟨hw, hm⟩`. Rewrite `hm` using `[if_neg hw]`. Conclude with `absurd rfl hm`.

Take `⟨hmw, hmG⟩` from `hm'`. Establish `hβs : ∀ s, β s = (m (Fin.last n, s) : ℤ)` using `fun s => by rw [← hmw, bm_weight_zW]`. Establish `hpos : ∀ s, 0 ≤ β s` using `fun s => by rw [hβs]; exact Int.natCast_nonneg _`. Establish `hcol : ∀ t : Fin n, ∑ a : Fin (n + 1), m (a, t) = lam t` using `colSums R (n + 1) n lam G hG m (mem_support_iff.2 hmG)`. Use `⟨hpos, ?_, fun i => ⟨?_, ?_⟩⟩` and prove the remaining obligations.

Establish `h1 : Finsupp.weight (lastW n) m = d` using `hd hmG`. Rewrite `h1` using `[bm_weight_lastW]`. Rewrite using `[← h1]`. Unfold `rowDeg`. Use `push_cast`.

Conclude with `Finset.sum_congr rfl fun s _ => hβs s`. Establish `: lamZ lam i.castSucc = (lam i : ℤ)`. Unfold `lamZ`. Rewrite using `[dif_pos (by simp : (i.castSucc : Fin (n + 1)).val < n)]`. Both sides reduce to the same expression.

Rewrite using `[this]`. Use `hpos i` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Distinguish the cases in `hi : i.val + 1 < n`. Establish `hz : lamZ lam i.succ = (lam ⟨i.val + 1, hi⟩ : ℤ)`.

Unfold `lamZ`. Rewrite using `[dif_pos (by simpa using hi : (i.succ : Fin (n + 1)).val < n)]`. Both sides reduce to the same expression. Rewrite using `[hz]`. Assume the negation of the conclusion as `hcon`.

Establish `hcon` using `not_le.mp hcon`. Use `set j : Fin n := ⟨i.val + 1, hi⟩ with hjdef`. Establish `hij : i < j`. Rewrite using `[Fin.lt_def]`. Simplify using `[hjdef]`.

Take `⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = β i` from `⟨(β i).toNat, Int.toNat_of_nonneg (hpos i)⟩`. Establish `hnil` using `bmD_nil lam G hG i j hij k (by rw [hk]; linarith)`. Establish `htop` using `(bmD_top G β hmax i j rfl k).2.2`. Rewrite `htop` using `[hnil, map_zero]`. Conclude with `hβ (bmZ_iter_inj R n j i (ne_of_gt hij) k β _ (bmD_zcomp_isWH β G) (le_of_eq hk) htop.symm)`.

Establish `hz : lamZ lam i.succ = 0`. Unfold `lamZ`. Rewrite using `[dif_neg (by simpa using hi : ¬ (i.succ : Fin (n + 1)).val < n)]`. Rewrite using `[hz]`. Use `show (0 : ℤ) ≤ (lam i : ℤ) - β i`.

Rewrite using `[hβs, ← hcol i]`. Establish `: m (Fin.last n, i) ≤ ∑ a : Fin (n + 1), m (a, i)` using `Finset.single_le_sum (f := fun a : Fin (n + 1) => m (a, i)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (Fin.last n))`. Establish `h2 : ((m (Fin.last n, i) : ℕ) : ℤ) ≤ ((∑ a : Fin (n + 1), m (a, i) : ℕ) : ℤ)`. Conclude with `this` after adjusting the coercions. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `u`. Unfold `bmCap bmChi`. Conclude with `capDet_eigen (bmEL R n) u (zcomp R n β G) (fun s => (lam s : ℤ) - β s) (fun l j hlj => bmD_raise lam G hG β hmax l j hlj) (fun s => bmD_weight lam G hG β s)`.
-/
theorem bm_eig {R : Type} [CommRing R] [IsDomain R] [CharZero R] {n : ℕ} (lam : Fin n → ℕ) (d : ℕ) (G : BP R n)
    (hG : G ∈ dualWeyl R (n + 1) n lam) (hd : IsWeightedHomogeneous (lastW n) G d) (β : Fin n → ℤ)
    (hβ : zcomp R n β G ≠ 0) (hmax : ∀ β', zcomp R n β' G ≠ 0 → omg β' ≤ omg β) :
    bmAdm lam d β ∧ ∀ u, bmCap R n u (zcomp R n β G) = ((bmChi lam β u : ℤ) : R) • zcomp R n β G := by
  classical
  constructor
  ·
    obtain ⟨m, hm⟩ : ∃ m, coeff m (zcomp R n β G) ≠ 0 := by
      by_contra hcon
      refine hβ (MvPolynomial.ext _ _ fun m => ?_)
      rw [coeff_zero]
      by_contra hm0
      exact hcon ⟨m, hm0⟩
    have hm' : Finsupp.weight (zW n) m = β ∧ coeff m G ≠ 0 := by
      unfold zcomp at hm
      rw [coeff_weightedHomogeneousComponent] at hm
      by_cases hw : Finsupp.weight (zW n) m = β
      · rw [if_pos hw] at hm
        exact ⟨hw, hm⟩
      · rw [if_neg hw] at hm
        exact absurd rfl hm
    obtain ⟨hmw, hmG⟩ := hm'
    have hβs : ∀ s, β s = (m (Fin.last n, s) : ℤ) := fun s => by rw [← hmw, bm_weight_zW]
    have hpos : ∀ s, 0 ≤ β s := fun s => by rw [hβs]; exact Int.natCast_nonneg _
    have hcol : ∀ t : Fin n, ∑ a : Fin (n + 1), m (a, t) = lam t :=
      colSums R (n + 1) n lam G hG m (mem_support_iff.2 hmG)
    refine ⟨hpos, ?_, fun i => ⟨?_, ?_⟩⟩
    · have h1 : Finsupp.weight (lastW n) m = d := hd hmG
      rw [bm_weight_lastW] at h1
      rw [← h1]
      unfold rowDeg
      push_cast
      exact Finset.sum_congr rfl fun s _ => hβs s
    · have : lamZ lam i.castSucc = (lam i : ℤ) := by
        unfold lamZ
        rw [dif_pos (by simp : (i.castSucc : Fin (n + 1)).val < n)]
        rfl
      rw [this]
      have := hpos i
      linarith
    · by_cases hi : i.val + 1 < n
      · have hz : lamZ lam i.succ = (lam ⟨i.val + 1, hi⟩ : ℤ) := by
          unfold lamZ
          rw [dif_pos (by simpa using hi : (i.succ : Fin (n + 1)).val < n)]
          rfl
        rw [hz]
        by_contra hcon
        have hcon := not_le.mp hcon
        set j : Fin n := ⟨i.val + 1, hi⟩ with hjdef
        have hij : i < j := by
          rw [Fin.lt_def]; simp [hjdef]
        obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = β i := ⟨(β i).toNat, Int.toNat_of_nonneg (hpos i)⟩
        have hnil := bmD_nil lam G hG i j hij k (by rw [hk]; linarith)
        have htop := (bmD_top G β hmax i j rfl k).2.2
        rw [hnil, map_zero] at htop
        exact hβ (bmZ_iter_inj R n j i (ne_of_gt hij) k β _ (bmD_zcomp_isWH β G) (le_of_eq hk)
          htop.symm)
      · have hz : lamZ lam i.succ = 0 := by
          unfold lamZ
          rw [dif_neg (by simpa using hi : ¬ (i.succ : Fin (n + 1)).val < n)]
        rw [hz]
        show (0 : ℤ) ≤ (lam i : ℤ) - β i
        rw [hβs, ← hcol i]
        have : m (Fin.last n, i) ≤ ∑ a : Fin (n + 1), m (a, i) :=
          Finset.single_le_sum (f := fun a : Fin (n + 1) => m (a, i)) (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ (Fin.last n))
        have h2 : ((m (Fin.last n, i) : ℕ) : ℤ) ≤ ((∑ a : Fin (n + 1), m (a, i) : ℕ) : ℤ) := by
          exact_mod_cast this
        linarith
  · intro u
    unfold bmCap bmChi
    exact capDet_eigen (bmEL R n) u (zcomp R n β G) (fun s => (lam s : ℤ) - β s)
      (fun l j hlj => bmD_raise lam G hG β hmax l j hlj) (fun s => bmD_weight lam G hG β s)

/- English proof (translation)
Simplify using `only [omg, Pi.add_apply, mul_add, Finset.sum_add_distrib]`.
-/
theorem bmF_omg_add {n : ℕ} (β β' : Fin n → ℤ) : omg (β + β') = omg β + omg β' := by
  simp only [omg, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h β hβ`. Use extensionality with `m`. Rewrite using `[zcomp, coeff_weightedHomogeneousComponent, coeff_zero]`. Use `split_ifs with hm`.

Assume the negation of the conclusion as `hc`. Use `h m (mem_support_iff.mpr hc)` as an intermediate fact. Rewrite `this` using `[hm]`. Use linear arithmetic over natural numbers and integers. Both sides reduce to the same expression.

Introduce `h m hm`. Assume the negation of the conclusion as `hc`. Establish `h0` using `h _ (not_lt.mp hc)`. Use `congrArg (coeff m) h0` as an intermediate fact. Rewrite `this` using `[zcomp, coeff_weightedHomogeneousComponent, if_pos rfl, coeff_zero]`.

Conclude with `mem_support_iff.mp hm this`.
-/
theorem bm_isLow_iff {R : Type*} [CommRing R] {n : ℕ} (D : ℤ) (L : BP R n) :
    IsLow D L ↔ ∀ β, D ≤ omg β → zcomp R n β L = 0 := by
  classical
  constructor
  · intro h β hβ
    ext m
    rw [zcomp, coeff_weightedHomogeneousComponent, coeff_zero]
    split_ifs with hm
    · by_contra hc
      have := h m (mem_support_iff.mpr hc)
      rw [hm] at this
      omega
    · rfl
  · intro h m hm
    by_contra hc
    have h0 := h _ (not_lt.mp hc)
    have := congrArg (coeff m) h0
    rw [zcomp, coeff_weightedHomogeneousComponent, if_pos rfl, coeff_zero] at this
    exact mem_support_iff.mp hm this

/- English proof (translation)
Introduce `m hm`. Simplify using `at hm`.
-/
theorem bmF_low_zero {R : Type*} [CommRing R] {n : ℕ} (D : ℤ) : IsLow D (0 : BP R n) := by
  intro m hm
  simp at hm

/- English proof (translation)
Introduce `m hm`. Break down `Finset.mem_union.mp (support_add hm) with h1 | h1` into its components or cases. Conclude with `h m h1`. Conclude with `h' m h1`.
-/
theorem bmF_low_add {R : Type*} [CommRing R] {n : ℕ} {D : ℤ} {L L' : BP R n} (h : IsLow D L)
    (h' : IsLow D L') : IsLow D (L + L') := by
  intro m hm
  rcases Finset.mem_union.mp (support_add hm) with h1 | h1
  · exact h m h1
  · exact h' m h1

/- English proof (translation)
Introduce `m hm`. Conclude with `h m (support_smul hm)`.
-/
theorem bmF_low_smul {R : Type*} [CommRing R] {n : ℕ} {D : ℤ} {L : BP R n} (c : R) (h : IsLow D L) :
    IsLow D (c • L) := by
  intro m hm
  exact h m (support_smul hm)

/- English proof (translation)
Conclude with `Finset.sum_induction L (fun x => IsLow D x) (fun _ _ ha hb => bmF_low_add ha hb) (bmF_low_zero D) h`.
-/
theorem bmF_low_sum {R : Type*} [CommRing R] {n : ℕ} {D : ℤ} {ι : Type*} (s : Finset ι) (L : ι → BP R n)
    (h : ∀ i ∈ s, IsLow D (L i)) : IsLow D (∑ i ∈ s, L i) := by
  exact Finset.sum_induction L (fun x => IsLow D x) (fun _ _ ha hb => bmF_low_add ha hb)
    (bmF_low_zero D) h

/- English proof (translation)
Introduce `m hm`. Rewrite using `[hF (mem_support_iff.mp hm)]`. Conclude with `hβ`.
-/
theorem bmF_low_of_WH {R : Type*} [CommRing R] {n : ℕ} {D : ℤ} {F : BP R n} {β : Fin n → ℤ}
    (hF : IsWeightedHomogeneous (zW n) F β) (hβ : omg β < D) : IsLow D F := by
  intro m hm
  rw [hF (mem_support_iff.mp hm)]
  exact hβ

def bmF_Fil {R : Type*} [CommRing R] {n : ℕ} (D : ℤ) (F : BP R n) : Prop :=
  ∀ m ∈ F.support, omg (Finsupp.weight (zW n) m) ≤ D

/- English proof (translation)
Introduce `m hm`. Conclude with `le_of_eq (congrArg omg (hF (mem_support_iff.mp hm)))`.
-/
theorem bmF_fil_of_WH {R : Type*} [CommRing R] {n : ℕ} {F : BP R n} {β : Fin n → ℤ}
    (hF : IsWeightedHomogeneous (zW n) F β) : bmF_Fil (omg β) F := by
  intro m hm
  exact le_of_eq (congrArg omg (hF (mem_support_iff.mp hm)))

/- English proof (translation)
Introduce `m hm`. Break down `Finset.mem_union.mp (support_add hm) with h1 | h1` into its components or cases. Conclude with `hF m h1`. Conclude with `le_of_lt (hL m h1)`.
-/
theorem bmF_fil_add_low {R : Type*} [CommRing R] {n : ℕ} {D : ℤ} {F L : BP R n} (hF : bmF_Fil D F)
    (hL : IsLow D L) : bmF_Fil D (F + L) := by
  intro m hm
  rcases Finset.mem_union.mp (support_add hm) with h1 | h1
  · exact hF m h1
  · exact le_of_lt (hL m h1)

/- English proof (translation)
Introduce `m hm`. Take `⟨a, ha, b, hb, rfl⟩` from `Finset.mem_add.mp (support_mul F L hm)`. Rewrite using `[map_add, bmD_omg_add]`. Conclude with `add_lt_add_of_le_of_lt (hF a ha) (hL b hb)`.
-/
theorem bmF_fil_mul_low {R : Type*} [CommRing R] {n : ℕ} {D D' : ℤ} {F L : BP R n} (hF : bmF_Fil D F)
    (hL : IsLow D' L) : IsLow (D + D') (F * L) := by
  intro m hm
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (support_mul F L hm)
  rw [map_add, bmD_omg_add]
  exact add_lt_add_of_le_of_lt (hF a ha) (hL b hb)

/- English proof (translation)
Establish `hX : ∀ s, IsWeightedHomogeneous (zW n) (X (Fin.last n, s) : BP R n) (zW n (Fin.last n, s))` using `fun s => by apply isWeightedHomogeneous_X`. Establish `e : (fun s => (b s : ℤ)) = ∑ s, b s • zW n (Fin.last n, s)`. Use function extensionality and compare the values at `t`. Simplify using `[zW, Finset.sum_apply, Pi.single_apply]`. Rewrite using `[e]`.

Conclude with `IsWeightedHomogeneous.prod Finset.univ _ _ (fun s _ => (hX s).pow (b s))`.
-/
theorem bmF_zmon_WH (R : Type*) [CommRing R] (n : ℕ) (b : Fin n → ℕ) :
    IsWeightedHomogeneous (zW n) (zmon R n b) (fun s => (b s : ℤ)) := by
  have hX : ∀ s, IsWeightedHomogeneous (zW n) (X (Fin.last n, s) : BP R n) (zW n (Fin.last n, s)) :=
    fun s => by apply isWeightedHomogeneous_X
  have e : (fun s => (b s : ℤ)) = ∑ s, b s • zW n (Fin.last n, s) := by
    funext t
    simp [zW, Finset.sum_apply, Pi.single_apply]
  rw [e]
  exact IsWeightedHomogeneous.prod Finset.univ _ _ (fun s _ => (hX s).pow (b s))

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on`. Use `next a =>`. Rewrite using `[emb, rename_C]`. Apply `isWeightedHomogeneous_C` to reduce the goal to its premises. Use `next p q hp hq =>`.

Rewrite using `[map_add]`. Conclude with `hp.add hq`. Use `next p v hp =>`. Rewrite using `[map_mul]`. Establish `hx : IsWeightedHomogeneous w (emb R n (X v)) 0`.

Rewrite using `[emb, rename_X, ← hw v.1 v.2]`. Apply `isWeightedHomogeneous_X` to reduce the goal to its premises. Simplify using `using hp.mul hx`.
-/
theorem bmF_emb_WH {R : Type*} [CommRing R] {n : ℕ} {B : Type*} [AddCommMonoid B]
    (w : Fin (n + 1) × Fin n → B) (hw : ∀ (a : Fin n) (s : Fin n), w (a.castSucc, s) = 0)
    (f : MvPolynomial (Fin n × Fin n) R) : IsWeightedHomogeneous w (emb R n f) 0 := by
  induction f using MvPolynomial.induction_on
  next a =>
    rw [emb, rename_C]
    apply isWeightedHomogeneous_C
  next p q hp hq =>
    rw [map_add]
    exact hp.add hq
  next p v hp =>
    rw [map_mul]
    have hx : IsWeightedHomogeneous w (emb R n (X v)) 0 := by
      rw [emb, rename_X, ← hw v.1 v.2]
      apply isWeightedHomogeneous_X
    simpa using hp.mul hx

/- English proof (translation)
Conclude with `if_neg (Fin.castSucc_ne_last a)`.
-/
theorem bmF_zW_castSucc {n : ℕ} (a s : Fin n) : zW n (a.castSucc, s) = 0 := by
  exact if_neg (Fin.castSucc_ne_last a)

/- English proof (translation)
Conclude with `if_neg (Fin.castSucc_ne_last a)`.
-/
theorem bmF_lastW_castSucc {n : ℕ} (a s : Fin n) : lastW n (a.castSucc, s) = 0 := by
  exact if_neg (Fin.castSucc_ne_last a)

/- English proof (translation)
Simplify using `using (bmF_zmon_WH R n b).mul (bmF_emb_WH (zW n) (fun a s => bmF_zW_castSucc a s) f)`.
-/
theorem bmF_lead_WH (R : Type*) [CommRing R] (n : ℕ) (b : Fin n → ℕ) (f : MvPolynomial (Fin n × Fin n) R) :
    IsWeightedHomogeneous (zW n) (zmon R n b * emb R n f) (fun s => (b s : ℤ)) := by
  simpa using (bmF_zmon_WH R n b).mul (bmF_emb_WH (zW n) (fun a s => bmF_zW_castSucc a s) f)

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Take `⟨h1', h2', h3'⟩` from `h'`. Use `⟨Submodule.add_mem _ h1 h1', h2.add h2', ?_⟩` and prove the remaining obligations. Establish `e : G + G' - zmon R n b * emb R n (f + f') = (G - zmon R n b * emb R n f) + (G' - zmon R n b * emb R n f')`. Rewrite using `[map_add]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `bmF_low_add h3 h3'`.
-/
theorem bmLift_add {R : Type*} [CommRing R] {n : ℕ} {lam b : Fin n → ℕ} {f f' : MvPolynomial (Fin n × Fin n) R}
    {G G' : BP R n} (h : bmLift R n lam b f G) (h' : bmLift R n lam b f' G') :
    bmLift R n lam b (f + f') (G + G') := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  refine ⟨Submodule.add_mem _ h1 h1', h2.add h2', ?_⟩
  have e : G + G' - zmon R n b * emb R n (f + f') =
      (G - zmon R n b * emb R n f) + (G' - zmon R n b * emb R n f') := by
    rw [map_add]
    ring
  rw [e]
  exact bmF_low_add h3 h3'

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Use `⟨Submodule.smul_mem _ c h1, isWeightedHomogeneous_smul h2 c, ?_⟩` and prove the remaining obligations. Establish `e : c • G - zmon R n b * emb R n (c • f) = c • (G - zmon R n b * emb R n f)`. Rewrite using `[map_smul, smul_sub, mul_smul_comm]`. Rewrite using `[e]`.

Conclude with `bmF_low_smul c h3`.
-/
theorem bmLift_smul {R : Type*} [CommRing R] {n : ℕ} {lam b : Fin n → ℕ} {f : MvPolynomial (Fin n × Fin n) R}
    {G : BP R n} (c : R) (h : bmLift R n lam b f G) : bmLift R n lam b (c • f) (c • G) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨Submodule.smul_mem _ c h1, isWeightedHomogeneous_smul h2 c, ?_⟩
  have e : c • G - zmon R n b * emb R n (c • f) = c • (G - zmon R n b * emb R n f) := by
    rw [map_smul, smul_sub, mul_smul_comm]
  rw [e]
  exact bmF_low_smul c h3

/- English proof (translation)
Simplify using `only [zmon, Pi.add_apply, pow_add, Finset.prod_mul_distrib]`.
-/
theorem bmF_zmon_add (R : Type*) [CommRing R] (n : ℕ) (b b' : Fin n → ℕ) :
    zmon R n (b + b') = zmon R n b * zmon R n b' := by
  simp only [zmon, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

/- English proof (translation)
Use `⟨dualWeyl_mul h.1 h'.1, ?_, ?_⟩` and prove the remaining obligations. Use `h.2.1.mul h'.2.1` as an intermediate fact. Rewrite `this` using `[← Finset.sum_add_distrib]`. Then use the resulting hypothesis. Establish `e1 : G * G' - zmon R n (b + b') * emb R n (f * f') = (zmon R n b * emb R n f) * (G' - zmon R n b' * emb R n f') + G' * (G - zmon R n b * emb R n f)`. Rewrite using `[bmF_zmon_add, map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e2 : omg (fun s => (((b + b') s : ℕ) : ℤ)) = omg (fun s => (b s : ℤ)) + omg (fun s => (b' s : ℤ))`. Establish `e3 : (fun s => (((b + b') s : ℕ) : ℤ)) = (fun s => (b s : ℤ)) + fun s => (b' s : ℤ)`. Use function extensionality and compare the values at `s`. Simplify using the standard rewrite rules.

Rewrite using `[e3, bmF_omg_add]`. Rewrite using `[e1, e2]`. Use `bmF_low_add (bmF_fil_mul_low (bmF_fil_of_WH (bmF_lead_WH R n b f)) h'.2.2) ?_` and prove the remaining obligations. Rewrite using `[add_comm (omg _)]`. Use `bmF_fil_mul_low ?_ h.2.2` and prove the remaining obligations.

Establish `: G' = zmon R n b' * emb R n f' + (G' - zmon R n b' * emb R n f')` using `by ring`. Rewrite using `[this]`. Conclude with `bmF_fil_add_low (bmF_fil_of_WH (bmF_lead_WH R n b' f')) h'.2.2`.
-/
theorem bmLift_mul {R : Type*} [CommRing R] {n : ℕ} {lam b lam' b' : Fin n → ℕ}
    {f f' : MvPolynomial (Fin n × Fin n) R} {G G' : BP R n} (h : bmLift R n lam b f G)
    (h' : bmLift R n lam' b' f' G') : bmLift R n (lam + lam') (b + b') (f * f') (G * G') := by
  refine ⟨dualWeyl_mul h.1 h'.1, ?_, ?_⟩
  · have := h.2.1.mul h'.2.1
    rwa [← Finset.sum_add_distrib] at this
  · have e1 : G * G' - zmon R n (b + b') * emb R n (f * f') =
        (zmon R n b * emb R n f) * (G' - zmon R n b' * emb R n f') +
          G' * (G - zmon R n b * emb R n f) := by
      rw [bmF_zmon_add, map_mul]; ring
    have e2 : omg (fun s => (((b + b') s : ℕ) : ℤ)) = omg (fun s => (b s : ℤ)) + omg (fun s => (b' s : ℤ)) := by
      have e3 : (fun s => (((b + b') s : ℕ) : ℤ)) = (fun s => (b s : ℤ)) + fun s => (b' s : ℤ) := by
        funext s
        simp
      rw [e3, bmF_omg_add]
    rw [e1, e2]
    refine bmF_low_add (bmF_fil_mul_low (bmF_fil_of_WH (bmF_lead_WH R n b f)) h'.2.2) ?_
    rw [add_comm (omg _)]
    refine bmF_fil_mul_low ?_ h.2.2
    have : G' = zmon R n b' * emb R n f' + (G' - zmon R n b' * emb R n f') := by ring
    rw [this]
    exact bmF_fil_add_low (bmF_fil_of_WH (bmF_lead_WH R n b' f')) h'.2.2

/- English proof (translation)
Use `⟨Submodule.mem_inf.mpr ⟨?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Apply `isWeightedHomogeneous_one` to reduce the goal to its premises. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker]`. Introduce `l j _`. Simplify using the standard rewrite rules.

Simplify using `only [Pi.zero_apply, Finset.sum_const_zero]`. Apply `isWeightedHomogeneous_one` to reduce the goal to its premises. Establish `e : (1 : BP R n) - zmon R n 0 * emb R n 1 = 0`. Simplify using `[zmon]`. Rewrite using `[e]`.

Conclude with `bmF_low_zero _`.
-/
theorem bmLift_one (R : Type*) [CommRing R] (n : ℕ) : bmLift R n 0 0 1 1 := by
  refine ⟨Submodule.mem_inf.mpr ⟨?_, ?_⟩, ?_, ?_⟩
  · apply isWeightedHomogeneous_one
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    intro l j _
    simp
  · simp only [Pi.zero_apply, Finset.sum_const_zero]
    apply isWeightedHomogeneous_one
  · have e : (1 : BP R n) - zmon R n 0 * emb R n 1 = 0 := by
      simp [zmon]
    rw [e]
    exact bmF_low_zero _

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using bmLift_one R n`. Consider the case `succ k ih`. Use `bmLift_mul ih h` as an intermediate fact. Rewrite using `[succ_nsmul, succ_nsmul, pow_succ, pow_succ]`.

Conclude with `this`.
-/
theorem bmLift_pow {R : Type*} [CommRing R] {n : ℕ} {lam b : Fin n → ℕ}
    {f : MvPolynomial (Fin n × Fin n) R} {G : BP R n} (h : bmLift R n lam b f G) (k : ℕ) :
    bmLift R n (k • lam) (k • b) (f ^ k) (G ^ k) := by
  induction k with
  | zero => simpa using bmLift_one R n
  | succ k ih =>
    have := bmLift_mul ih h
    rw [succ_nsmul, succ_nsmul, pow_succ, pow_succ]
    exact this

/- English proof (translation)
Rewrite using `[emb, rename_X]`.
-/
theorem bmF_emb_X (R : Type*) [CommRing R] (n : ℕ) (v : Fin n × Fin n) :
    emb R n (X v) = X (v.1.castSucc, v.2) := by
  rw [emb, rename_X]

/- English proof (translation)
Rewrite using `[AlgHom.map_det]`. Use `congr 1`. Use extensionality with `p q`. Simplify using `[bmF_emb_X]`.
-/
theorem bmF_emb_minor (R : Type*) [CommRing R] (n : ℕ) {s : ℕ} (I : Fin s → Fin n) (c : Fin s → Fin n) :
    emb R n (Matrix.of fun p q : Fin s => (X (I p, c q) : MvPolynomial (Fin n × Fin n) R)).det =
      (Matrix.of fun p q : Fin s => (X ((I p).castSucc, c q) : BP R n)).det := by
  rw [AlgHom.map_det]
  congr 1
  ext p q
  simp [bmF_emb_X]

/- English proof (translation)
Establish `he : initMinor R (fun p => (I p).castSucc) hs = emb R n (initMinor R I hs)`. Unfold `initMinor`. Rewrite using `[bmF_emb_minor]`. Use `⟨initMinor_mem _ hs, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[he]`.

Simplify using `using bmF_emb_WH (lastW n) bmF_lastW_castSucc (initMinor R I hs)`. Establish `: initMinor R (fun p => (I p).castSucc) hs - zmon R n 0 * emb R n (initMinor R I hs) = 0`. Rewrite using `[he]`. Simplify using `[zmon]`. Rewrite using `[this]`.

Conclude with `bmF_low_zero _`.
-/
theorem bmLift_minor0 (R : Type*) [CommRing R] (n : ℕ) {s : ℕ} (I : Fin s → Fin n) (hs : s ≤ n) :
    bmLift R n (initW n s) 0 (initMinor R I hs) (initMinor R (fun p => (I p).castSucc) hs) := by
  have he : initMinor R (fun p => (I p).castSucc) hs = emb R n (initMinor R I hs) := by
    unfold initMinor
    rw [bmF_emb_minor]
  refine ⟨initMinor_mem _ hs, ?_, ?_⟩
  · rw [he]
    simpa using bmF_emb_WH (lastW n) bmF_lastW_castSucc (initMinor R I hs)
  · have : initMinor R (fun p => (I p).castSucc) hs - zmon R n 0 * emb R n (initMinor R I hs) = 0 := by
      rw [he]; simp [zmon]
    rw [this]
    exact bmF_low_zero _

/- English proof (translation)
Unfold `zmon`. Rewrite using `[Finset.prod_eq_single t (fun b _ hb => by simp [Pi.single_apply, hb]) (fun h => absurd (Finset.mem_univ t) h)]`. Simplify using the standard rewrite rules.
-/
theorem bmF_zmon_single (R : Type*) [CommRing R] (n : ℕ) (t : Fin n) :
    zmon R n (Pi.single t 1) = X (Fin.last n, t) := by
  unfold zmon
  rw [Finset.prod_eq_single t (fun b _ hb => by simp [Pi.single_apply, hb])
    (fun h => absurd (Finset.mem_univ t) h)]
  simp

/- English proof (translation)
Simplify using `[omg, Pi.single_apply]`.
-/
theorem bmF_omg_single {n : ℕ} (t : Fin n) : omg (Pi.single t 1 : Fin n → ℤ) = ((t : ℕ) : ℤ) + 1 := by
  simp [omg, Pi.single_apply]

/- English proof (translation)
Rewrite using `[show (-1 : MvPolynomial σ R) ^ k = C ((-1 : R) ^ k) by rw [map_pow, map_neg, map_one]]`. Conclude with `isWeightedHomogeneous_C w _`.
-/
theorem bmF_neg_one_pow_WH {R σ B : Type*} [CommRing R] [AddCommMonoid B] (w : σ → B) (k : ℕ) :
    IsWeightedHomogeneous w ((-1 : MvPolynomial σ R) ^ k) 0 := by
  rw [show (-1 : MvPolynomial σ R) ^ k = C ((-1 : R) ^ k) by rw [map_pow, map_neg, map_one]]
  exact isWeightedHomogeneous_C w _

/- English proof (translation)
Unfold `initMinor`. Rewrite using `[Matrix.det_succ_row _ (Fin.last s)]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[bmF_emb_minor]`. Use `congr 1`.

Use `congr 1`. Simplify using the standard rewrite rules. Use `congr 1`. Use extensionality with `p q`. Simplify using `[Matrix.submatrix_apply, Fin.succAbove_last]`.
-/
theorem bmF_laplace (R : Type*) [CommRing R] (n : ℕ) {s : ℕ} (I : Fin s → Fin n) (hs : s + 1 ≤ n) :
    initMinor R (fun p : Fin (s + 1) => if h : p.val < s then (I ⟨p.val, h⟩).castSucc else Fin.last n) hs =
      ∑ j : Fin (s + 1), (-1 : BP R n) ^ (s + (j : ℕ)) * X (Fin.last n, Fin.castLE hs j) *
        emb R n (Matrix.of fun p q : Fin s =>
          (X (I p, Fin.castLE hs (j.succAbove q)) : MvPolynomial (Fin n × Fin n) R)).det := by
  unfold initMinor
  rw [Matrix.det_succ_row _ (Fin.last s)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [bmF_emb_minor]
  congr 1
  · congr 1
    simp
  · congr 1
    ext p q
    simp [Matrix.submatrix_apply, Fin.succAbove_last]

/- English proof (translation)
Use `⟨initMinor_mem _ hs, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[bmF_laplace]`. Establish `hsum : (∑ t : Fin n, (Pi.single (⟨s, hs⟩ : Fin n) 1 : Fin n → ℕ) t) = 1`. Rewrite using `[Finset.sum_eq_single (⟨s, hs⟩ : Fin n)]`. Simplify using the standard rewrite rules.

Introduce `t _ ht`. Simplify using `[ht]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Rewrite using `[hsum]`.

Use `IsWeightedHomogeneous.sum _ _ _ fun j _ => ?_` and prove the remaining obligations. Establish `h1` using `((bmF_neg_one_pow_WH (R := R) (lastW n) (s + (j : ℕ))).mul (isWeightedHomogeneous_X R (lastW n) (Fin.last n, Fin.castLE hs j))).mul (bmF_emb_WH (lastW n) bmF_lastW_castSucc (Matrix.of fun p q : Fin s => (X (I p, Fin.castLE hs (j.succAbove q)) : MvPolynomial (Fin n × Fin n) R)).de …`. Simplify `h1` using `[lastW]`. Rewrite using `[bmF_laplace, Fin.sum_univ_castSucc, bmF_zmon_single]`. Establish `hlast : (-1 : BP R n) ^ (s + ((Fin.last s : Fin (s + 1)) : ℕ)) * X (Fin.last n, Fin.castLE hs (Fin.last s)) * emb R n (Matrix.of fun p q : Fin s => (X (I p, Fin.castLE hs ((Fin.last s).succAbove q)) : MvPolynomial (Fin n × Fin n) R)).det = X (Fin.last n, (⟨s, hs⟩ : Fin n)) * emb …`.

Establish `h1 : (-1 : BP R n) ^ (s + ((Fin.last s : Fin (s + 1)) : ℕ)) = 1`. Rewrite using `[Fin.val_last, ← two_mul, pow_mul]`. Simplify using the standard rewrite rules. Establish `h2 : ∀ q : Fin s, Fin.castLE hs ((Fin.last s).succAbove q) = Fin.castLE (Nat.le_of_succ_le hs) q`. Introduce `q`.

Rewrite using `[Fin.succAbove_last]`. Both sides reduce to the same expression. Rewrite using `[h1, one_mul]`. Simplify using `only [h2]`. Both sides reduce to the same expression.

Rewrite using `[hlast, add_sub_cancel_right]`. Use `bmF_low_sum _ _ fun j _ => ?_` and prove the remaining obligations. Establish `h1` using `((bmF_neg_one_pow_WH (R := R) (zW n) (s + ((j.castSucc : Fin (s + 1)) : ℕ))).mul (isWeightedHomogeneous_X R (zW n) (Fin.last n, Fin.castLE hs j.castSucc))).mul (bmF_emb_WH (zW n) bmF_zW_castSucc (Matrix.of fun p q : Fin s => (X (I p, Fin.castLE hs (j.castSucc.succAbove q)) : MvPo …`. Use `bmF_low_of_WH h1 ?_` and prove the remaining obligations. Establish `h2 : (0 : Fin n → ℤ) + zW n (Fin.last n, Fin.castLE hs j.castSucc) + 0 = Pi.single (Fin.castLE hs j.castSucc) 1`.

Simplify using `[zW]`. Establish `h3 : (fun t => (((Pi.single (⟨s, hs⟩ : Fin n) 1 : Fin n → ℕ) t : ℕ) : ℤ)) = (Pi.single (⟨s, hs⟩ : Fin n) 1 : Fin n → ℤ)`. Use function extensionality and compare the values at `t`. Distinguish the cases in `ht : t = ⟨s, hs⟩`. Substitute `ht` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[ht]`. Rewrite using `[h2, h3, bmF_omg_single, bmF_omg_single]`. Simplify using the standard rewrite rules.
-/
theorem bmLift_minor1 (R : Type*) [CommRing R] (n : ℕ) {s : ℕ} (I : Fin s → Fin n) (hs : s + 1 ≤ n) :
    bmLift R n (initW n (s + 1)) (Pi.single ⟨s, hs⟩ 1) (initMinor R I (Nat.le_of_succ_le hs))
      (initMinor R (fun p : Fin (s + 1) => if h : p.val < s then (I ⟨p.val, h⟩).castSucc else Fin.last n) hs) := by
  classical
  refine ⟨initMinor_mem _ hs, ?_, ?_⟩
  · rw [bmF_laplace]
    have hsum : (∑ t : Fin n, (Pi.single (⟨s, hs⟩ : Fin n) 1 : Fin n → ℕ) t) = 1 := by
      rw [Finset.sum_eq_single (⟨s, hs⟩ : Fin n)]
      · simp
      · intro t _ ht
        simp [ht]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hsum]
    refine IsWeightedHomogeneous.sum _ _ _ fun j _ => ?_
    have h1 := ((bmF_neg_one_pow_WH (R := R) (lastW n) (s + (j : ℕ))).mul
      (isWeightedHomogeneous_X R (lastW n) (Fin.last n, Fin.castLE hs j))).mul
      (bmF_emb_WH (lastW n) bmF_lastW_castSucc (Matrix.of fun p q : Fin s =>
          (X (I p, Fin.castLE hs (j.succAbove q)) : MvPolynomial (Fin n × Fin n) R)).det)
    simpa [lastW] using h1
  · rw [bmF_laplace, Fin.sum_univ_castSucc, bmF_zmon_single]
    have hlast : (-1 : BP R n) ^ (s + ((Fin.last s : Fin (s + 1)) : ℕ)) *
        X (Fin.last n, Fin.castLE hs (Fin.last s)) *
        emb R n (Matrix.of fun p q : Fin s =>
          (X (I p, Fin.castLE hs ((Fin.last s).succAbove q)) : MvPolynomial (Fin n × Fin n) R)).det =
        X (Fin.last n, (⟨s, hs⟩ : Fin n)) * emb R n (initMinor R I (Nat.le_of_succ_le hs)) := by
      have h1 : (-1 : BP R n) ^ (s + ((Fin.last s : Fin (s + 1)) : ℕ)) = 1 := by
        rw [Fin.val_last, ← two_mul, pow_mul]; simp
      have h2 : ∀ q : Fin s, Fin.castLE hs ((Fin.last s).succAbove q) = Fin.castLE (Nat.le_of_succ_le hs) q := by
        intro q
        rw [Fin.succAbove_last]
        rfl
      rw [h1, one_mul]
      simp only [h2]
      rfl
    rw [hlast, add_sub_cancel_right]
    refine bmF_low_sum _ _ fun j _ => ?_
    have h1 := ((bmF_neg_one_pow_WH (R := R) (zW n) (s + ((j.castSucc : Fin (s + 1)) : ℕ))).mul
      (isWeightedHomogeneous_X R (zW n) (Fin.last n, Fin.castLE hs j.castSucc))).mul
      (bmF_emb_WH (zW n) bmF_zW_castSucc (Matrix.of fun p q : Fin s =>
          (X (I p, Fin.castLE hs (j.castSucc.succAbove q)) : MvPolynomial (Fin n × Fin n) R)).det)
    refine bmF_low_of_WH h1 ?_
    have h2 : (0 : Fin n → ℤ) + zW n (Fin.last n, Fin.castLE hs j.castSucc) + 0 =
        Pi.single (Fin.castLE hs j.castSucc) 1 := by
      simp [zW]
    have h3 : (fun t => (((Pi.single (⟨s, hs⟩ : Fin n) 1 : Fin n → ℕ) t : ℕ) : ℤ)) =
        (Pi.single (⟨s, hs⟩ : Fin n) 1 : Fin n → ℤ) := by
      funext t
      by_cases ht : t = ⟨s, hs⟩
      · subst ht; simp
      · simp [ht]
    rw [h2, h3, bmF_omg_single, bmF_omg_single]
    simp

/- English proof (translation)
Simplify using `[extM]`.
-/
theorem bmF_extM_castSucc (R : Type*) [CommRing R] {n : ℕ} (g : Matrix (Fin n) (Fin n) R) (a b : Fin n) :
    extM R g a.castSucc b.castSucc = g a b := by
  simp [extM]

/- English proof (translation)
Simplify using `[extM, Fin.castSucc_ne_last]`.
-/
theorem bmF_extM_castSucc_last (R : Type*) [CommRing R] {n : ℕ} (g : Matrix (Fin n) (Fin n) R) (a : Fin n) :
    extM R g a.castSucc (Fin.last n) = 0 := by
  simp [extM, Fin.castSucc_ne_last]

/- English proof (translation)
Simplify using `[extM, (Fin.castSucc_ne_last b).symm]`.
-/
theorem bmF_extM_last_castSucc (R : Type*) [CommRing R] {n : ℕ} (g : Matrix (Fin n) (Fin n) R) (b : Fin n) :
    extM R g (Fin.last n) b.castSucc = 0 := by
  simp [extM, (Fin.castSucc_ne_last b).symm]

/- English proof (translation)
Simplify using `[extM]`.
-/
theorem bmF_extM_last_last (R : Type*) [CommRing R] {n : ℕ} (g : Matrix (Fin n) (Fin n) R) :
    extM R g (Fin.last n) (Fin.last n) = 1 := by
  simp [extM]

/- English proof (translation)
Rewrite using `[rowAction_X_sum, Fin.sum_univ_castSucc]`. Simplify using `[bmF_extM_castSucc, bmF_extM_castSucc_last]`.
-/
theorem bmF_rowAct_X_castSucc (R : Type*) [CommRing R] {n : ℕ} (g : Matrix (Fin n) (Fin n) R) (a s : Fin n) :
    rowAct R (extM R g) (X (a.castSucc, s) : BP R n) = ∑ b : Fin n, C (g a b) * X (b.castSucc, s) := by
  rw [rowAction_X_sum, Fin.sum_univ_castSucc]
  simp [bmF_extM_castSucc, bmF_extM_castSucc_last]

/- English proof (translation)
Rewrite using `[rowAction_X_sum, Fin.sum_univ_castSucc]`. Simplify using `[bmF_extM_last_castSucc, bmF_extM_last_last]`.
-/
theorem bmF_rowAct_X_last (R : Type*) [CommRing R] {n : ℕ} (g : Matrix (Fin n) (Fin n) R) (s : Fin n) :
    rowAct R (extM R g) (X (Fin.last n, s) : BP R n) = X (Fin.last n, s) := by
  rw [rowAction_X_sum, Fin.sum_univ_castSucc]
  simp [bmF_extM_last_castSucc, bmF_extM_last_last]

/- English proof (translation)
Simplify using `only [zmon, map_prod, map_pow, bmF_rowAct_X_last]`.
-/
theorem bmF_rowAct_zmon (R : Type*) [CommRing R] {n : ℕ} (g : Matrix (Fin n) (Fin n) R) (b : Fin n → ℕ) :
    rowAct R (extM R g) (zmon R n b) = zmon R n b := by
  simp only [zmon, map_prod, map_pow, bmF_rowAct_X_last]

/- English proof (translation)
Establish `: (rowAct R (extM R g)).comp (emb R n) = (emb R n).comp (rowAct R g)`. Use `MvPolynomial.algHom_ext fun v => ?_` and prove the remaining obligations. Rewrite using `[AlgHom.comp_apply, AlgHom.comp_apply, bmF_emb_X, bmF_rowAct_X_castSucc, rowAction_X_sum]`. Simplify using `[emb, rename_C]`. Conclude with `AlgHom.congr_fun this f`.
-/
theorem bmF_rowAct_emb (R : Type*) [CommRing R] {n : ℕ} (g : Matrix (Fin n) (Fin n) R)
    (f : MvPolynomial (Fin n × Fin n) R) :
    rowAct R (extM R g) (emb R n f) = emb R n (rowAct R g f) := by
  have : (rowAct R (extM R g)).comp (emb R n) = (emb R n).comp (rowAct R g) := by
    refine MvPolynomial.algHom_ext fun v => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, bmF_emb_X, bmF_rowAct_X_castSucc, rowAction_X_sum]
    simp [emb, rename_C]
  exact AlgHom.congr_fun this f

/- English proof (translation)
Use `IsWeightedHomogeneous.sum _ _ _ fun b _ => ?_` and prove the remaining obligations. Distinguish the cases in `hb : extM R g v.1 b = 0`. Rewrite using `[hb, map_zero, zero_mul]`. Apply `isWeightedHomogeneous_zero` to reduce the goal to its premises. Establish `e : w (b, v.2) = w v`.

Take `⟨a, s⟩` from `v`. Distinguish the cases in `ha : a = Fin.last n`. Substitute `ha` using the available equality. Distinguish the cases in `hbl : b = Fin.last n`. Rewrite using `[hbl]`.

Conclude with `absurd (extendMatrix_last_left_zero R g b hbl) hb`. Distinguish the cases in `hbl : b = Fin.last n`. Conclude with `absurd (hbl ▸ extendMatrix_last_right_zero R g a ha) hb`. Take `⟨a', rfl⟩` from `Fin.exists_castSucc_eq.mpr ha`. Take `⟨b', rfl⟩` from `Fin.exists_castSucc_eq.mpr hbl`.

Conclude with `hw b' a' s`. Rewrite using `[← e]`. Establish `hC : IsWeightedHomogeneous w (C (extM R g v.1 b) : BP R n) 0`. Apply `isWeightedHomogeneous_C` to reduce the goal to its premises. Establish `hX : IsWeightedHomogeneous w (X (b, v.2) : BP R n) (w (b, v.2))`.

Apply `isWeightedHomogeneous_X` to reduce the goal to its premises. Simplify using `using hC.mul hX`.
-/
theorem bmF_rowAct_var_WH (R : Type*) [CommRing R] {n : ℕ} {B : Type*} [AddCommMonoid B]
    (w : Fin (n + 1) × Fin n → B) (hw : ∀ a b s : Fin n, w (a.castSucc, s) = w (b.castSucc, s))
    (g : Matrix (Fin n) (Fin n) R) (v : Fin (n + 1) × Fin n) :
    IsWeightedHomogeneous w (∑ b : Fin (n + 1), C (extM R g v.1 b) * (X (b, v.2) : BP R n)) (w v) := by
  refine IsWeightedHomogeneous.sum _ _ _ fun b _ => ?_
  by_cases hb : extM R g v.1 b = 0
  · rw [hb, map_zero, zero_mul]
    apply isWeightedHomogeneous_zero
  · have e : w (b, v.2) = w v := by
      obtain ⟨a, s⟩ := v
      by_cases ha : a = Fin.last n
      · subst ha
        by_cases hbl : b = Fin.last n
        · rw [hbl]
        · exact absurd (extendMatrix_last_left_zero R g b hbl) hb
      · by_cases hbl : b = Fin.last n
        · exact absurd (hbl ▸ extendMatrix_last_right_zero R g a ha) hb
        · obtain ⟨a', rfl⟩ := Fin.exists_castSucc_eq.mpr ha
          obtain ⟨b', rfl⟩ := Fin.exists_castSucc_eq.mpr hbl
          exact hw b' a' s
    rw [← e]
    have hC : IsWeightedHomogeneous w (C (extM R g v.1 b) : BP R n) 0 := by
      apply isWeightedHomogeneous_C
    have hX : IsWeightedHomogeneous w (X (b, v.2) : BP R n) (w (b, v.2)) := by
      apply isWeightedHomogeneous_X
    simpa using hC.mul hX

/- English proof (translation)
Establish `hm : (monomial m c : BP R n) = c • monomial m 1`. Rewrite using `[smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[hm, map_smul]`. Conclude with `isWeightedHomogeneous_smul (bm_aeval_monomial_WH w _ (fun v => bmF_rowAct_var_WH R w hw g v) m) c`.
-/
theorem bmF_rowAct_monomial_WH (R : Type*) [CommRing R] {n : ℕ} {B : Type*} [AddCommMonoid B]
    (w : Fin (n + 1) × Fin n → B) (hw : ∀ a b s : Fin n, w (a.castSucc, s) = w (b.castSucc, s))
    (g : Matrix (Fin n) (Fin n) R) (m : Fin (n + 1) × Fin n →₀ ℕ) (c : R) :
    IsWeightedHomogeneous w (rowAct R (extM R g) (monomial m c : BP R n)) (Finsupp.weight w m) := by
  have hm : (monomial m c : BP R n) = c • monomial m 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hm, map_smul]
  exact isWeightedHomogeneous_smul (bm_aeval_monomial_WH w _ (fun v => bmF_rowAct_var_WH R w hw g v) m) c

/- English proof (translation)
Rewrite using `[F.as_sum, map_sum]`. Use `IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_` and prove the remaining obligations. Use `bmF_rowAct_monomial_WH R w hw g d (coeff d F)` as an intermediate fact. Rewrite `this` using `[hF (mem_support_iff.mp hd)]`. Then use the resulting hypothesis.
-/
theorem bmF_rowAct_WH (R : Type*) [CommRing R] {n : ℕ} {B : Type*} [AddCommMonoid B]
    (w : Fin (n + 1) × Fin n → B) (hw : ∀ a b s : Fin n, w (a.castSucc, s) = w (b.castSucc, s))
    (g : Matrix (Fin n) (Fin n) R) (F : BP R n) (β : B) (hF : IsWeightedHomogeneous w F β) :
    IsWeightedHomogeneous w (rowAct R (extM R g) F) β := by
  rw [F.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  have := bmF_rowAct_monomial_WH R w hw g d (coeff d F)
  rwa [hF (mem_support_iff.mp hd)] at this

/- English proof (translation)
Introduce `m' hm'`. Rewrite `hm'` using `[L.as_sum, map_sum]`. Take `⟨d, hd, hmd⟩` from `Finset.mem_biUnion.mp (MvPolynomial.support_sum hm')`. Establish `hW` using `bmF_rowAct_monomial_WH R (zW n) (fun a b s => by rw [bmF_zW_castSucc, bmF_zW_castSucc]) g d (coeff d L)`. Rewrite using `[hW (mem_support_iff.mp hmd)]`.

Conclude with `hL d hd`.
-/
theorem bmF_rowAct_low (R : Type*) [CommRing R] {n : ℕ} (g : Matrix (Fin n) (Fin n) R) (D : ℤ) (L : BP R n)
    (hL : IsLow D L) : IsLow D (rowAct R (extM R g) L) := by
  classical
  intro m' hm'
  rw [L.as_sum, map_sum] at hm'
  obtain ⟨d, hd, hmd⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm')
  have hW := bmF_rowAct_monomial_WH R (zW n)
    (fun a b s => by rw [bmF_zW_castSucc, bmF_zW_castSucc]) g d (coeff d L)
  rw [hW (mem_support_iff.mp hmd)]
  exact hL d hd

/- English proof (translation)
Use `⟨dualWeylRowStable R (n + 1) n lam (extM R g) G h.1, ?_, ?_⟩` and prove the remaining obligations. Conclude with `bmF_rowAct_WH R (lastW n) (fun a b s => by rw [bmF_lastW_castSucc, bmF_lastW_castSucc]) g G _ h.2.1`. Establish `h1` using `bmF_rowAct_low R g _ _ h.2.2`. Rewrite `h1` using `[map_sub, map_mul, bmF_rowAct_zmon, bmF_rowAct_emb]`. Then use the resulting hypothesis.
-/
theorem bmLift_rowAct {R : Type} [CommRing R] {n : ℕ} {lam b : Fin n → ℕ} {f : MvPolynomial (Fin n × Fin n) R}
    {G : BP R n} (g : Matrix (Fin n) (Fin n) R) (h : bmLift R n lam b f G) :
    bmLift R n lam b (rowAct R g f) (rowAct R (extM R g) G) := by
  refine ⟨dualWeylRowStable R (n + 1) n lam (extM R g) G h.1, ?_, ?_⟩
  · exact bmF_rowAct_WH R (lastW n) (fun a b s => by rw [bmF_lastW_castSucc, bmF_lastW_castSucc]) g G _ h.2.1
  · have h1 := bmF_rowAct_low R g _ _ h.2.2
    rwa [map_sub, map_mul, bmF_rowAct_zmon, bmF_rowAct_emb] at h1

/- English proof (translation)
Substitute `h1 h2 h3 h4` using the available equality. Conclude with `h`.
-/
theorem bmG_cast {R : Type*} [CommRing R] {n : ℕ} {lam b lam' b' : Fin n → ℕ}
    {f f' : MvPolynomial (Fin n × Fin n) R} {G G' : BP R n} (h : bmLift R n lam b f G)
    (h1 : lam = lam') (h2 : b = b') (h3 : f = f') (h4 : G = G') : bmLift R n lam' b' f' G' := by
  subst h1 h2 h3 h4
  exact h

/- English proof (translation)
Use `⟨Submodule.zero_mem _, ?_, ?_⟩` and prove the remaining obligations. Apply `isWeightedHomogeneous_zero` to reduce the goal to its premises. Rewrite using `[map_zero, mul_zero, sub_zero]`. Conclude with `bmF_low_zero _`.
-/
theorem bmG_zero (R : Type*) [CommRing R] (n : ℕ) (lam b : Fin n → ℕ) : bmLift R n lam b 0 0 := by
  refine ⟨Submodule.zero_mem _, ?_, ?_⟩
  · apply isWeightedHomogeneous_zero
  · rw [map_zero, mul_zero, sub_zero]
    exact bmF_low_zero _

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using bmLift_one R n`. Consider the case `@insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, Finset.prod_insert ha, Finset.prod_insert ha]`. Conclude with `bmLift_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem bmG_prod {R : Type*} [CommRing R] {n : ℕ} {ι : Type*} (s : Finset ι) (lam b : ι → Fin n → ℕ)
    (f : ι → MvPolynomial (Fin n × Fin n) R) (G : ι → BP R n)
    (h : ∀ i ∈ s, bmLift R n (lam i) (b i) (f i) (G i)) :
    bmLift R n (∑ i ∈ s, lam i) (∑ i ∈ s, b i) (∏ i ∈ s, f i) (∏ i ∈ s, G i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using bmLift_one R n
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.prod_insert ha, Finset.prod_insert ha]
    exact bmLift_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Simplify using `only [shapeDeg, Finset.card_filter, Fin.sum_univ_succ]`.
-/
theorem bmG_shapeDeg_succ {n K : ℕ} (sz : Fin (K + 1) → ℕ) (t : Fin n) :
    shapeDeg sz t = (if t.val < sz 0 then 1 else 0) + shapeDeg (fun k : Fin K => sz k.succ) t := by
  simp only [shapeDeg, Finset.card_filter, Fin.sum_univ_succ]

/- English proof (translation)
Use function extensionality and compare the values at `t`. Simplify using `[shapeDeg]`.
-/
theorem bmG_shapeDeg_zero {n : ℕ} (sz : Fin 0 → ℕ) : (shapeDeg sz : Fin n → ℕ) = 0 := by
  funext t
  simp [shapeDeg]

/- English proof (translation)
Introduce `t t' h`. Apply `Finset.card_le_card` to reduce the goal to its premises. Introduce `k hk`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢`. Conclude with `lt_of_le_of_lt (Fin.le_iff_val_le_val.mp h) hk`.
-/
theorem bmG_shapeDeg_anti {n K : ℕ} (sz : Fin K → ℕ) : Antitone (shapeDeg sz : Fin n → ℕ) := by
  intro t t' h
  apply Finset.card_le_card
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  exact lt_of_le_of_lt (Fin.le_iff_val_le_val.mp h) hk

/- English proof (translation)
Simplify using `only [bideterminant, Fin.prod_univ_succ]`.
-/
theorem bmG_bidet_succ (R : Type*) [CommRing R] {r n K : ℕ} (sz : Fin (K + 1) → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) :
    bideterminant R sz hsz I = initMinor R (I 0) (hsz 0) *
      bideterminant R (fun k : Fin K => sz k.succ) (fun k => hsz k.succ) (fun k => I k.succ) := by
  simp only [bideterminant, Fin.prod_univ_succ]

/- English proof (translation)
Establish `hc : i.val + 1 < n`. Use `j.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Unfold `nuNext`. Rewrite using `[dif_pos hc]`.

Use `congr 1`. Conclude with `Fin.ext h.symm`.
-/
theorem bmG_nuNext_of_succ {n : ℕ} (ν : Fin n → ℕ) (i j : Fin n) (h : j.val = i.val + 1) :
    nuNext ν i = ν j := by
  have hc : i.val + 1 < n := by
    have := j.isLt
    omega
  unfold nuNext
  rw [dif_pos hc]
  congr 1
  exact Fin.ext h.symm

/- English proof (translation)
Unfold `nuNext`. Rewrite using `[dif_neg h]`.
-/
theorem bmG_nuNext_last {n : ℕ} (ν : Fin n → ℕ) (i : Fin n) (h : ¬ i.val + 1 < n) : nuNext ν i = 0 := by
  unfold nuNext
  rw [dif_neg h]

/- English proof (translation)
Simplify using `[initMinor]`.
-/
theorem bmG_minor_empty (R : Type*) [CommRing R] {r n : ℕ} (I : Fin 0 → Fin r) (hs : 0 ≤ n) :
    initMinor R I hs = 1 := by
  simp [initMinor]

/- English proof (translation)
Break down `Nat.eq_zero_or_pos n with hn | hn` into its components or cases. Substitute `hn` using the available equality. Conclude with `⟨1, bmG_cast (bmLift_one R 0) (Subsingleton.elim _ _) (Subsingleton.elim _ _) rfl rfl⟩`. Establish `hs : 0 + 1 ≤ n` using `hn`. Establish `h1` using `bmLift_pow (bmLift_minor1 R n (Fin.elim0 : Fin 0 → Fin n) hs) (lam ⟨0, hn⟩)`.

Establish `hz : ∀ t : Fin n, t.val ≠ 0 → lam t = 0`. Introduce `t ht`. Establish `hlt : t.val - 1 < n` using `by have := t.isLt; omega`. Rewrite using `[← bmG_nuNext_of_succ lam ⟨t.val - 1, hlt⟩ t (by simp; omega)]`. Conclude with `h _`.

Use `⟨_, bmG_cast h1 ?_ ?_ ?_ rfl⟩` and prove the remaining obligations. Use function extensionality and compare the values at `t`. Simplify using `only [Pi.smul_apply, initW, smul_eq_mul]`. Distinguish the cases in `ht : t.val = 0`. Establish `: t = ⟨0, hn⟩` using `Fin.ext ht`.

Rewrite using `[this]`. Simplify using the standard rewrite rules. Rewrite using `[if_neg (by omega), hz t ht, mul_zero]`. Use function extensionality and compare the values at `t`. Simplify using `only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]`.

Distinguish the cases in `ht : t.val = 0`. Establish `: t = ⟨0, hn⟩` using `Fin.ext ht`. Rewrite using `[this]`. Simplify using the standard rewrite rules. Rewrite using `[if_neg (fun hh => ht (by rw [hh])), hz t ht, mul_zero]`.

Rewrite using `[bmG_minor_empty, one_pow]`.
-/
theorem bmG_base (R : Type*) [CommRing R] (n : ℕ) (lam : Fin n → ℕ) (h : ∀ i : Fin n, nuNext lam i = 0) :
    ∃ G, bmLift R n lam lam 1 G := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨1, bmG_cast (bmLift_one R 0) (Subsingleton.elim _ _) (Subsingleton.elim _ _) rfl rfl⟩
  · have hs : 0 + 1 ≤ n := hn
    have h1 := bmLift_pow (bmLift_minor1 R n (Fin.elim0 : Fin 0 → Fin n) hs) (lam ⟨0, hn⟩)
    have hz : ∀ t : Fin n, t.val ≠ 0 → lam t = 0 := by
      intro t ht
      have hlt : t.val - 1 < n := by have := t.isLt; omega
      rw [← bmG_nuNext_of_succ lam ⟨t.val - 1, hlt⟩ t (by simp; omega)]
      exact h _
    refine ⟨_, bmG_cast h1 ?_ ?_ ?_ rfl⟩
    · funext t
      simp only [Pi.smul_apply, initW, smul_eq_mul]
      by_cases ht : t.val = 0
      · have : t = ⟨0, hn⟩ := Fin.ext ht
        rw [this]; simp
      · rw [if_neg (by omega), hz t ht, mul_zero]
    · funext t
      simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      by_cases ht : t.val = 0
      · have : t = ⟨0, hn⟩ := Fin.ext ht
        rw [this]; simp
      · rw [if_neg (fun hh => ht (by rw [hh])), hz t ht, mul_zero]
    · rw [bmG_minor_empty, one_pow]

/- English proof (translation)
Introduce `K`. Proceed by induction on `K with`. Consider the case `zero`. Introduce `sz hsz I lam hIL`. Establish `h0 : (shapeDeg sz : Fin n → ℕ) = 0` using `bmG_shapeDeg_zero sz`.

Take `⟨G, hG⟩` from `bmG_base R n lam (fun i => by`. Use `(hIL i).2` as an intermediate fact. Rewrite `this` using `[h0]`. Simplify using `using this)`. Use `⟨G, bmG_cast hG rfl ?_ ?_ rfl⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `s`. Rewrite using `[h0]`. Simplify using the standard rewrite rules. Unfold `bideterminant`. Simplify using the standard rewrite rules.

Consider the case `succ K ih`. Introduce `sz hsz I lam hIL`. Establish `hsg : ∀ t : Fin n, shapeDeg sz t = (if t.val < sz 0 then 1 else 0) + shapeDeg (fun k : Fin K => sz k.succ) t` using `bmG_shapeDeg_succ sz`. Establish `hanti : Antitone (shapeDeg (fun k : Fin K => sz k.succ) : Fin n → ℕ)` using `bmG_shapeDeg_anti _`. Distinguish the cases in `hA : ∀ i : Fin n, i.val + 1 = sz 0 → nuNext lam i < shapeDeg sz i`.

Establish `hIL' : bmIL (fun t => lam t - (if t.val < sz 0 then 1 else 0)) (shapeDeg (fun k : Fin K => sz k.succ))`. Introduce `t`. Prove the components needed by the constructor for the conclusion. Establish `h1` using `(hIL t).1`. Rewrite `h1` using `[hsg t]`.

Use `show _ ≤ lam t - (if t.val < sz 0 then 1 else 0)`. Apply the tactic sequence `split_ifs at h1 ⊢ <;> omega`. Distinguish the cases in `ht : t.val + 1 < n`. Establish `h2` using `(hIL t).2`. Rewrite using `[bmG_nuNext_of_succ _ t ⟨t.val + 1, ht⟩ rfl]`.

Establish `h3` using `hA t`. Rewrite `h2`, `h3` using `[bmG_nuNext_of_succ lam t ⟨t.val + 1, ht⟩ rfl]`. Rewrite `h2`, `h3` using `[hsg t]`. Use `show lam ⟨t.val + 1, ht⟩ - (if t.val + 1 < sz 0 then 1 else 0) ≤ _`. Distinguish the cases in `h4 : t.val + 1 = sz 0`.

Establish `h5` using `h3 h4`. Rewrite using `[if_neg (by omega)]`. Rewrite `h5` using `[if_pos (by omega)]`. Use linear arithmetic over natural numbers and integers. Apply the tactic sequence `split_ifs at h2 ⊢ <;> omega`.

Rewrite using `[bmG_nuNext_last _ t ht]`. Conclude with `Nat.zero_le _`. Take `⟨G', hG'⟩` from `ih _ (fun k => hsz k.succ) (fun k => I k.succ) _ hIL'`. Use `⟨_, bmG_cast (bmLift_mul (bmLift_minor0 R n (I 0) (hsz 0)) hG') ?_ ?_ (bmG_bidet_succ R sz hsz I).symm rfl⟩` and prove the remaining obligations. Use function extensionality and compare the values at `t`.

Establish `h1` using `(hIL t).1`. Rewrite `h1` using `[hsg t]`. Simplify using `only [Pi.add_apply, initW]`. Apply the tactic sequence `split_ifs at h1 ⊢ <;> omega`. Use function extensionality and compare the values at `t`.

Establish `h1` using `(hIL t).1`. Rewrite `h1` using `[hsg t]`. Simplify using `only [Pi.add_apply, Pi.zero_apply]`. Rewrite using `[hsg t]`. Apply the tactic sequence `split_ifs at h1 ⊢ <;> omega`.

Use `push Not at hA`. Take `⟨i, hij, hle⟩` from `hA`. Establish `hi1 : 1 ≤ shapeDeg sz i` using `by rw [hsg i, if_pos (by omega)]; omega`. Establish `hin : i.val + 1 < n`. Assume the negation of the conclusion as `hcon`.

Rewrite `hle` using `[bmG_nuNext_last lam i hcon]`. Use linear arithmetic over natural numbers and integers. Establish `hs : sz 0 + 1 ≤ n` using `by omega`. Establish `hlj : shapeDeg (fun k : Fin K => sz k.succ) (⟨sz 0, hs⟩ : Fin n) + 1 ≤ lam ⟨sz 0, hs⟩`. Rewrite `hle` using `[bmG_nuNext_of_succ lam i ⟨sz 0, hs⟩ hij.symm, hsg i, if_pos (by omega)]`.

Establish `h5 : shapeDeg (fun k : Fin K => sz k.succ) (⟨sz 0, hs⟩ : Fin n) ≤ shapeDeg (fun k : Fin K => sz k.succ) i` using `hanti (Fin.le_def.mpr (by simp; omega))`. Use linear arithmetic over natural numbers and integers. Establish `hIL' : bmIL (fun t => lam t - (if t.val < sz 0 + 1 then 1 else 0)) (shapeDeg (fun k : Fin K => sz k.succ))`. Introduce `t`. Prove the components needed by the constructor for the conclusion.

Establish `h1` using `(hIL t).1`. Rewrite `h1` using `[hsg t]`. Use `show _ ≤ lam t - (if t.val < sz 0 + 1 then 1 else 0)`. Distinguish the cases in `h4 : t.val = sz 0`. Establish `h6 : t = ⟨sz 0, hs⟩` using `Fin.ext h4`.

Rewrite using `[h6]`. Rewrite using `[if_pos (by simp)]`. Use linear arithmetic over natural numbers and integers. Apply the tactic sequence `split_ifs at h1 ⊢ <;> omega`. Distinguish the cases in `ht : t.val + 1 < n`.

Establish `h2` using `(hIL t).2`. Rewrite using `[bmG_nuNext_of_succ _ t ⟨t.val + 1, ht⟩ rfl]`. Rewrite `h2` using `[bmG_nuNext_of_succ lam t ⟨t.val + 1, ht⟩ rfl]`. Rewrite `h2` using `[hsg t]`. Use `show lam ⟨t.val + 1, ht⟩ - (if t.val + 1 < sz 0 + 1 then 1 else 0) ≤ _`.

Apply the tactic sequence `split_ifs at h2 ⊢ <;> omega`. Rewrite using `[bmG_nuNext_last _ t ht]`. Conclude with `Nat.zero_le _`. Take `⟨G', hG'⟩` from `ih _ (fun k => hsz k.succ) (fun k => I k.succ) _ hIL'`. Use `⟨_, bmG_cast (bmLift_mul (bmLift_minor1 R n (I 0) hs) hG') ?_ ?_ (bmG_bidet_succ R sz hsz I).symm rfl⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `t`. Establish `h1` using `(hIL t).1`. Rewrite `h1` using `[hsg t]`. Simplify using `only [Pi.add_apply, initW]`. Distinguish the cases in `h4 : t.val = sz 0`.

Establish `h6 : t = ⟨sz 0, hs⟩` using `Fin.ext h4`. Rewrite using `[h6]`. Rewrite using `[if_pos (by simp)]`. Use linear arithmetic over natural numbers and integers. Apply the tactic sequence `split_ifs at h1 ⊢ <;> omega`.

Use function extensionality and compare the values at `t`. Establish `h1` using `(hIL t).1`. Rewrite `h1` using `[hsg t]`. Simplify using `only [Pi.add_apply, Pi.single_apply]`. Rewrite using `[hsg t]`.

Distinguish the cases in `h4 : t.val = sz 0`. Establish `h6 : t = ⟨sz 0, hs⟩` using `Fin.ext h4`. Rewrite using `[h6]`. Rewrite using `[if_pos rfl, if_pos (by simp), if_neg (by simp)]`. Use linear arithmetic over natural numbers and integers.

Apply the tactic sequence `rw [if_neg (fun hh => h4 (by rw [hh]))] split_ifs at h1 ⊢ <;> omega`.
-/
theorem bmG_bidet {R : Type*} [CommRing R] {n : ℕ} : ∀ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin n) (lam : Fin n → ℕ), bmIL lam (shapeDeg sz) →
    ∃ G, bmLift R n lam (fun s => lam s - shapeDeg sz s) (bideterminant R sz hsz I) G := by
  intro K
  induction K with
  | zero =>
    intro sz hsz I lam hIL
    have h0 : (shapeDeg sz : Fin n → ℕ) = 0 := bmG_shapeDeg_zero sz
    obtain ⟨G, hG⟩ := bmG_base R n lam (fun i => by
      have := (hIL i).2
      rw [h0] at this
      simpa using this)
    refine ⟨G, bmG_cast hG rfl ?_ ?_ rfl⟩
    · funext s; rw [h0]; simp
    · unfold bideterminant; simp
  | succ K ih =>
    intro sz hsz I lam hIL
    have hsg : ∀ t : Fin n, shapeDeg sz t =
        (if t.val < sz 0 then 1 else 0) + shapeDeg (fun k : Fin K => sz k.succ) t :=
      bmG_shapeDeg_succ sz
    have hanti : Antitone (shapeDeg (fun k : Fin K => sz k.succ) : Fin n → ℕ) := bmG_shapeDeg_anti _
    by_cases hA : ∀ i : Fin n, i.val + 1 = sz 0 → nuNext lam i < shapeDeg sz i
    ·
      have hIL' : bmIL (fun t => lam t - (if t.val < sz 0 then 1 else 0))
          (shapeDeg (fun k : Fin K => sz k.succ)) := by
        intro t
        constructor
        · have h1 := (hIL t).1
          rw [hsg t] at h1
          show _ ≤ lam t - (if t.val < sz 0 then 1 else 0)
          split_ifs at h1 ⊢ <;> omega
        · by_cases ht : t.val + 1 < n
          · have h2 := (hIL t).2
            rw [bmG_nuNext_of_succ _ t ⟨t.val + 1, ht⟩ rfl]
            have h3 := hA t
            rw [bmG_nuNext_of_succ lam t ⟨t.val + 1, ht⟩ rfl] at h2 h3
            rw [hsg t] at h2 h3
            show lam ⟨t.val + 1, ht⟩ - (if t.val + 1 < sz 0 then 1 else 0) ≤ _
            by_cases h4 : t.val + 1 = sz 0
            · have h5 := h3 h4
              rw [if_neg (by omega)]
              rw [if_pos (by omega)] at h5
              omega
            · split_ifs at h2 ⊢ <;> omega
          · rw [bmG_nuNext_last _ t ht]; exact Nat.zero_le _
      obtain ⟨G', hG'⟩ := ih _ (fun k => hsz k.succ) (fun k => I k.succ) _ hIL'
      refine ⟨_, bmG_cast (bmLift_mul (bmLift_minor0 R n (I 0) (hsz 0)) hG') ?_ ?_
        (bmG_bidet_succ R sz hsz I).symm rfl⟩
      · funext t
        have h1 := (hIL t).1
        rw [hsg t] at h1
        simp only [Pi.add_apply, initW]
        split_ifs at h1 ⊢ <;> omega
      · funext t
        have h1 := (hIL t).1
        rw [hsg t] at h1
        simp only [Pi.add_apply, Pi.zero_apply]
        rw [hsg t]
        split_ifs at h1 ⊢ <;> omega
    ·
      push Not at hA
      obtain ⟨i, hij, hle⟩ := hA
      have hi1 : 1 ≤ shapeDeg sz i := by rw [hsg i, if_pos (by omega)]; omega
      have hin : i.val + 1 < n := by
        by_contra hcon
        rw [bmG_nuNext_last lam i hcon] at hle
        omega
      have hs : sz 0 + 1 ≤ n := by omega
      have hlj : shapeDeg (fun k : Fin K => sz k.succ) (⟨sz 0, hs⟩ : Fin n) + 1 ≤ lam ⟨sz 0, hs⟩ := by
        rw [bmG_nuNext_of_succ lam i ⟨sz 0, hs⟩ hij.symm, hsg i, if_pos (by omega)] at hle
        have h5 : shapeDeg (fun k : Fin K => sz k.succ) (⟨sz 0, hs⟩ : Fin n) ≤
            shapeDeg (fun k : Fin K => sz k.succ) i := hanti (Fin.le_def.mpr (by simp; omega))
        omega
      have hIL' : bmIL (fun t => lam t - (if t.val < sz 0 + 1 then 1 else 0))
          (shapeDeg (fun k : Fin K => sz k.succ)) := by
        intro t
        constructor
        · have h1 := (hIL t).1
          rw [hsg t] at h1
          show _ ≤ lam t - (if t.val < sz 0 + 1 then 1 else 0)
          by_cases h4 : t.val = sz 0
          · have h6 : t = ⟨sz 0, hs⟩ := Fin.ext h4
            rw [h6]
            rw [if_pos (by simp)]
            omega
          · split_ifs at h1 ⊢ <;> omega
        · by_cases ht : t.val + 1 < n
          · have h2 := (hIL t).2
            rw [bmG_nuNext_of_succ _ t ⟨t.val + 1, ht⟩ rfl]
            rw [bmG_nuNext_of_succ lam t ⟨t.val + 1, ht⟩ rfl] at h2
            rw [hsg t] at h2
            show lam ⟨t.val + 1, ht⟩ - (if t.val + 1 < sz 0 + 1 then 1 else 0) ≤ _
            split_ifs at h2 ⊢ <;> omega
          · rw [bmG_nuNext_last _ t ht]; exact Nat.zero_le _
      obtain ⟨G', hG'⟩ := ih _ (fun k => hsz k.succ) (fun k => I k.succ) _ hIL'
      refine ⟨_, bmG_cast (bmLift_mul (bmLift_minor1 R n (I 0) hs) hG') ?_ ?_
        (bmG_bidet_succ R sz hsz I).symm rfl⟩
      · funext t
        have h1 := (hIL t).1
        rw [hsg t] at h1
        simp only [Pi.add_apply, initW]
        by_cases h4 : t.val = sz 0
        · have h6 : t = ⟨sz 0, hs⟩ := Fin.ext h4
          rw [h6]
          rw [if_pos (by simp)]
          omega
        · split_ifs at h1 ⊢ <;> omega
      · funext t
        have h1 := (hIL t).1
        rw [hsg t] at h1
        simp only [Pi.add_apply, Pi.single_apply]
        rw [hsg t]
        by_cases h4 : t.val = sz 0
        · have h6 : t = ⟨sz 0, hs⟩ := Fin.ext h4
          rw [h6]
          rw [if_pos rfl, if_pos (by simp), if_neg (by simp)]
          omega
        · rw [if_neg (fun hh => h4 (by rw [hh]))]
          split_ifs at h1 ⊢ <;> omega

/- English proof (translation)
Rewrite `hf` using `[standardMonomialSpanDomain R n n sg]`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨K, sz, hsz, I, hsh, rfl⟩` from `hx`. Substitute `hsh` using the available equality.

Conclude with `bmG_bidet K sz hsz I lam hIL`. Consider the case `zero => exact ⟨0, bmG_zero R n _ _⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨G, hG⟩` from `hx`. Take `⟨G', hG'⟩` from `hy`.

Conclude with `⟨_, bmLift_add hG hG'⟩`. Consider the case `smul c x _ hx`. Take `⟨G, hG⟩` from `hx`. Conclude with `⟨_, bmLift_smul c hG⟩`.
-/
theorem bmLift_exists {R : Type} [CommRing R] [IsDomain R] {n : ℕ} (lam sg : Fin n → ℕ) (hIL : bmIL lam sg)
    (f : MvPolynomial (Fin n × Fin n) R) (hf : f ∈ dualWeyl R n n sg) :
    ∃ G, bmLift R n lam (fun s => lam s - sg s) f G := by
  rw [standardMonomialSpanDomain R n n sg] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, sz, hsz, I, hsh, rfl⟩ := hx
    subst hsh
    exact bmG_bidet K sz hsz I lam hIL
  | zero => exact ⟨0, bmG_zero R n _ _⟩
  | add x y _ _ hx hy =>
    obtain ⟨G, hG⟩ := hx
    obtain ⟨G', hG'⟩ := hy
    exact ⟨_, bmLift_add hG hG'⟩
  | smul c x _ hx =>
    obtain ⟨G, hG⟩ := hx
    exact ⟨_, bmLift_smul c hG⟩

/- English proof (translation)
Introduce `i j hij`. Take `⟨i, hi⟩` from `i`. Take `⟨j, hj⟩` from `j`. Simplify using `only [Fin.mk_le_mk] at hij`. Proceed by induction on `j, hij using Nat.le_induction with`.

Consider the case `base => exact le_rfl`. Consider the case `succ k hik ih`. Establish `h1` using `h ⟨k, by omega⟩`. Rewrite `h1` using `[bmG_nuNext_of_succ ν ⟨k, by omega⟩ ⟨k + 1, hj⟩ rfl]`. Conclude with `le_trans h1 (ih (by omega))`.
-/
theorem bmG_antitone {n : ℕ} (ν : Fin n → ℕ) (h : ∀ i, nuNext ν i ≤ ν i) : Antitone ν := by
  intro i j hij
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  simp only [Fin.mk_le_mk] at hij
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ k hik ih =>
    have h1 := h ⟨k, by omega⟩
    rw [bmG_nuNext_of_succ ν ⟨k, by omega⟩ ⟨k + 1, hj⟩ rfl] at h1
    exact le_trans h1 (ih (by omega))

/- English proof (translation)
Consider the cases of `n with`. Consider the case `zero => simp`. Consider the case `succ m`. Rewrite using `[Fin.prod_univ_succ, Fin.prod_univ_castSucc (f := fun i : Fin (m + 1) => D (i.val + 1) ^ nuNext b i)]`. Establish `h1 : nuNext b (Fin.last m) = 0` using `bmG_nuNext_last b _ (by simp)`.

Rewrite using `[h1, pow_zero, mul_one]`. Simplify using `only [Fin.val_zero, hD, one_pow, one_mul]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[bmG_nuNext_of_succ b i.castSucc i.succ (by simp)]`. Simplify using the standard rewrite rules.
-/
theorem bmG_shift {M : Type*} [CommMonoid M] (n : ℕ) (D : ℕ → M) (hD : D 0 = 1) (b : Fin n → ℕ) :
    ∏ i : Fin n, D i.val ^ b i = ∏ i : Fin n, D (i.val + 1) ^ nuNext b i := by
  cases n with
  | zero => simp
  | succ m =>
    rw [Fin.prod_univ_succ, Fin.prod_univ_castSucc (f := fun i : Fin (m + 1) => D (i.val + 1) ^ nuNext b i)]
    have h1 : nuNext b (Fin.last m) = 0 := bmG_nuNext_last b _ (by simp)
    rw [h1, pow_zero, mul_one]
    simp only [Fin.val_zero, hD, one_pow, one_mul]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [bmG_nuNext_of_succ b i.castSucc i.succ (by simp)]
    simp

/- English proof (translation)
Use function extensionality and compare the values at `p`. Both sides reduce to the same expression.
-/
theorem bmG_rowsA {n : ℕ} (i : Fin n) :
    (rowsA i : Fin (i.val + 1) → Fin (n + 1)) =
      fun p => (Fin.castLE (by omega : i.val + 1 ≤ n) p).castSucc := by
  funext p
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `p`. Simplify using `only [rowsB]`. Distinguish the cases in `h : p.val < i.val`. Rewrite using `[if_pos h, dif_pos h]`. Both sides reduce to the same expression.

Rewrite using `[if_neg h, dif_neg h]`.
-/
theorem bmG_rowsB {n : ℕ} (i : Fin n) :
    (rowsB i : Fin (i.val + 1) → Fin (n + 1)) =
      fun p => if h : p.val < i.val then (Fin.castLE (by omega : i.val ≤ n) ⟨p.val, h⟩).castSucc
        else Fin.last n := by
  funext p
  simp only [rowsB]
  by_cases h : p.val < i.val
  · rw [if_pos h, dif_pos h]
    rfl
  · rw [if_neg h, dif_neg h]

def bmG_D (R : Type*) [CommRing R] (n : ℕ) (s : ℕ) : MvPolynomial (Fin n × Fin n) R :=
  if h : s ≤ n then lpMinor R s h h else 1

/- English proof (translation)
Simplify using `[bmG_D, lpMinor]`.
-/
theorem bmG_D_zero (R : Type*) [CommRing R] (n : ℕ) : bmG_D R n 0 = 1 := by
  simp [bmG_D, lpMinor]

/- English proof (translation)
Rewrite using `[bmG_D, dif_pos h]`. Both sides reduce to the same expression.
-/
theorem bmG_D_eq (R : Type*) [CommRing R] (n : ℕ) (s : ℕ) (h : s ≤ n) :
    bmG_D R n s = initMinor R (Fin.castLE h) h := by
  rw [bmG_D, dif_pos h]
  rfl

/- English proof (translation)
Rewrite using `[Finset.prod_mul_distrib, bmG_shift n (bmG_D R n) (bmG_D_zero R n) (fun i => lam i - sg i), ← Finset.prod_mul_distrib]`. Unfold `hw`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← pow_add]`. Establish `h1 : bmG_D R n (i.val + 1) = lpMinor R (i.val + 1) (by omega) (by omega)`.

Unfold `bmG_D`. Rewrite using `[dif_pos (by omega)]`. Rewrite using `[h1]`. Use `congr 1`. Distinguish the cases in `hi : i.val + 1 < n`.

Rewrite using `[bmG_nuNext_of_succ lam i ⟨i.val + 1, hi⟩ rfl, bmG_nuNext_of_succ sg i ⟨i.val + 1, hi⟩ rfl, bmG_nuNext_of_succ (fun i => lam i - sg i) i ⟨i.val + 1, hi⟩ rfl]`. Establish `h2` using `(hIL i).2`. Rewrite `h2` using `[bmG_nuNext_of_succ lam i ⟨i.val + 1, hi⟩ rfl]`. Establish `h3` using `(hIL ⟨i.val + 1, hi⟩).1`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[bmG_nuNext_last lam i hi, bmG_nuNext_last sg i hi, bmG_nuNext_last _ i hi]`. Both sides reduce to the same expression.
-/
theorem bmG_hw (R : Type*) [CommRing R] {n : ℕ} (lam sg : Fin n → ℕ) (hIL : bmIL lam sg) :
    ∏ i : Fin n, (bmG_D R n (i.val + 1) ^ (sg i - nuNext lam i) * bmG_D R n i.val ^ (lam i - sg i)) =
      hw R le_rfl sg := by
  rw [Finset.prod_mul_distrib, bmG_shift n (bmG_D R n) (bmG_D_zero R n) (fun i => lam i - sg i),
    ← Finset.prod_mul_distrib]
  unfold hw
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← pow_add]
  have h1 : bmG_D R n (i.val + 1) = lpMinor R (i.val + 1) (by omega) (by omega) := by
    unfold bmG_D
    rw [dif_pos (by omega)]
  rw [h1]
  congr 1
  by_cases hi : i.val + 1 < n
  · rw [bmG_nuNext_of_succ lam i ⟨i.val + 1, hi⟩ rfl, bmG_nuNext_of_succ sg i ⟨i.val + 1, hi⟩ rfl,
      bmG_nuNext_of_succ (fun i => lam i - sg i) i ⟨i.val + 1, hi⟩ rfl]
    have h2 := (hIL i).2
    rw [bmG_nuNext_of_succ lam i ⟨i.val + 1, hi⟩ rfl] at h2
    have h3 := (hIL ⟨i.val + 1, hi⟩).1
    omega
  · rw [bmG_nuNext_last lam i hi, bmG_nuNext_last sg i hi, bmG_nuNext_last _ i hi]
    rfl

/- English proof (translation)
Establish `hanti : Antitone lam` using `bmG_antitone lam fun i => (hIL i).2.trans (hIL i).1`. Establish `hi : ∀ i ∈ (Finset.univ : Finset (Fin n)), bmLift R n ((sg i - nuNext lam i) • initW n (i.val + 1) + (lam i - sg i) • initW n (i.val + 1)) ((sg i - nuNext lam i) • (0 : Fin n → ℕ) + (lam i - sg i) • Pi.single i 1) (bmG_D R n (i.val + 1) ^ (sg i - nuNext lam i) * bmG_D R n i.val ^ …`. Introduce `i _`. Establish `hs1 : i.val + 1 ≤ n` using `by omega`. Establish `hs0 : i.val ≤ n` using `by omega`.

Use `bmLift_mul (bmLift_pow ?_ _) (bmLift_pow ?_ _)` and prove the remaining obligations. Rewrite using `[bmG_D_eq R n _ hs1, bmG_rowsA]`. Conclude with `bmLift_minor0 R n (Fin.castLE hs1) hs1`. Rewrite using `[bmG_D_eq R n _ hs0, bmG_rowsB]`. Conclude with `bmLift_minor1 R n (Fin.castLE hs0) hs1`.

Use `bmG_cast (bmG_prod Finset.univ _ _ _ _ hi) ?_ ?_ (bmG_hw R lam sg hIL) rfl` and prove the remaining obligations. Use `Eq.trans ?_ (hw_weight_eq lam hanti)` and prove the remaining obligations. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← add_smul]`. Use `congr 1`.

Establish `h1` using `hIL i`. Use linear arithmetic over natural numbers and integers. Use function extensionality and compare the values at `t`. Simplify using `only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, mul_zero, zero_add, Pi.single_apply, mul_ite, mul_one]`. Rewrite using `[Finset.sum_ite_eq]`.

Simplify using the standard rewrite rules.
-/
theorem bmLift_xi {R : Type} [CommRing R] {n : ℕ} (lam sg : Fin n → ℕ) (hIL : bmIL lam sg) :
    bmLift R n lam (fun s => lam s - sg s) (hw R le_rfl sg) (xiB R lam sg) := by
  have hanti : Antitone lam := bmG_antitone lam fun i => (hIL i).2.trans (hIL i).1
  have hi : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      bmLift R n ((sg i - nuNext lam i) • initW n (i.val + 1) + (lam i - sg i) • initW n (i.val + 1))
        ((sg i - nuNext lam i) • (0 : Fin n → ℕ) + (lam i - sg i) • Pi.single i 1)
        (bmG_D R n (i.val + 1) ^ (sg i - nuNext lam i) * bmG_D R n i.val ^ (lam i - sg i))
        (initMinor R (rowsA i) (by omega : i.val + 1 ≤ n) ^ (sg i - nuNext lam i) *
          initMinor R (rowsB i) (by omega : i.val + 1 ≤ n) ^ (lam i - sg i)) := by
    intro i _
    have hs1 : i.val + 1 ≤ n := by omega
    have hs0 : i.val ≤ n := by omega
    refine bmLift_mul (bmLift_pow ?_ _) (bmLift_pow ?_ _)
    · rw [bmG_D_eq R n _ hs1, bmG_rowsA]
      exact bmLift_minor0 R n (Fin.castLE hs1) hs1
    · rw [bmG_D_eq R n _ hs0, bmG_rowsB]
      exact bmLift_minor1 R n (Fin.castLE hs0) hs1
  refine bmG_cast (bmG_prod Finset.univ _ _ _ _ hi) ?_ ?_ (bmG_hw R lam sg hIL) rfl
  · refine Eq.trans ?_ (hw_weight_eq lam hanti)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← add_smul]
    congr 1
    have h1 := hIL i
    omega
  · funext t
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, mul_zero, zero_add,
      Pi.single_apply, mul_ite, mul_one]
    rw [Finset.sum_ite_eq]
    simp

/- English proof (translation)
Unfold `initMinor`. Rewrite using `[Matrix.det_apply]`. Use `IsWeightedHomogeneous.sum _ _ _ fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[← mem_weightedHomogeneousSubmodule]`. Use `zsmul_mem ?_ _` and prove the remaining obligations.

Rewrite using `[mem_weightedHomogeneousSubmodule, ← Equiv.sum_comp σ (fun p => (Pi.single (I p) 1 : Fin r → ℕ))]`. Use `IsWeightedHomogeneous.prod _ _ _ fun q _ => ?_` and prove the remaining obligations. Conclude with `isWeightedHomogeneous_X R (rowW r n) _`.
-/
theorem bmG_initMinor_rowHom (R : Type*) [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n) :
    IsWeightedHomogeneous (rowW r n) (initMinor R (n := n) I hs) (∑ p : Fin s, Pi.single (I p) 1) := by
  unfold initMinor
  rw [Matrix.det_apply]
  refine IsWeightedHomogeneous.sum _ _ _ fun σ _ => ?_
  rw [← mem_weightedHomogeneousSubmodule]
  refine zsmul_mem ?_ _
  rw [mem_weightedHomogeneousSubmodule,
    ← Equiv.sum_comp σ (fun p => (Pi.single (I p) 1 : Fin r → ℕ))]
  refine IsWeightedHomogeneous.prod _ _ _ fun q _ => ?_
  exact isWeightedHomogeneous_X R (rowW r n) _

/- English proof (translation)
The claim follows from `sum_single_castLE (by omega : i.val + 1 ≤ n + 1)`.
-/
theorem bmG_sumA {n : ℕ} (i : Fin n) :
    (∑ p : Fin (i.val + 1), (Pi.single (rowsA i p) 1 : Fin (n + 1) → ℕ)) = initW (n + 1) (i.val + 1) :=
  sum_single_castLE (by omega : i.val + 1 ≤ n + 1)

/- English proof (translation)
Rewrite using `[Fin.sum_univ_castSucc, ← sum_single_castLE (by omega : i.val ≤ n + 1)]`. Use `congr 1`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Use `congr 1`. Unfold `rowsB`.

Rewrite using `[if_pos (by simp)]`. Conclude with `Fin.ext rfl`. Use `congr 1`. Unfold `rowsB`. Rewrite using `[if_neg (by simp)]`.
-/
theorem bmG_sumB {n : ℕ} (i : Fin n) :
    (∑ p : Fin (i.val + 1), (Pi.single (rowsB i p) 1 : Fin (n + 1) → ℕ)) =
      initW (n + 1) i.val + Pi.single (Fin.last n) 1 := by
  rw [Fin.sum_univ_castSucc, ← sum_single_castLE (by omega : i.val ≤ n + 1)]
  congr 1
  · refine Finset.sum_congr rfl fun p _ => ?_
    congr 1
    unfold rowsB
    rw [if_pos (by simp)]
    exact Fin.ext rfl
  · congr 1
    unfold rowsB
    rw [if_neg (by simp)]

/- English proof (translation)
Establish `hanti : Antitone lam` using `bmG_antitone lam fun i => (hIL i).2.trans (hIL i).1`. Establish `h1 : IsWeightedHomogeneous (rowW (n + 1) n) (xiB R lam sg) (∑ i : Fin n, ((sg i - nuNext lam i) • initW (n + 1) (i.val + 1) + (lam i - sg i) • (initW (n + 1) i.val + Pi.single (Fin.last n) 1)))`. Unfold `xiB`. Use `IsWeightedHomogeneous.prod _ _ _ fun i _ => ?_` and prove the remaining obligations. Use `IsWeightedHomogeneous.mul (IsWeightedHomogeneous.pow ?_ _) (IsWeightedHomogeneous.pow ?_ _)` and prove the remaining obligations.

Rewrite using `[← bmG_sumA]`. Conclude with `bmG_initMinor_rowHom R _ _`. Rewrite using `[← bmG_sumB]`. Conclude with `bmG_initMinor_rowHom R _ _`. Use `h1 using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `a`. Simplify using `only [bmRho, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, initW, Pi.single_apply]`. Distinguish the cases in `ha : a.val < n`. Rewrite using `[dif_pos ha]`. Establish `hne : a ≠ Fin.last n` using `fun h => by rw [h] at ha; simp at ha`.

Establish `h2` using `congrFun (hw_weight_eq lam hanti) ⟨a.val, ha⟩`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, initW] at h2`. Establish `h3 : (∑ i : Fin n, ((sg i - nuNext lam i) * (if a.val < i.val + 1 then 1 else 0) + (lam i - sg i) * ((if a.val < i.val then 1 else 0) + if a = Fin.last n then 1 else 0))) + (lam ⟨a.val, ha⟩ - sg ⟨a.val, ha⟩) = lam ⟨a.val, ha⟩`. Establish `h4 : lam ⟨a.val, ha⟩ - sg ⟨a.val, ha⟩ = ∑ i : Fin n, if i = ⟨a.val, ha⟩ then (lam i - sg i) else 0`. Rewrite using `[Finset.sum_ite_eq']`.

Simplify using the standard rewrite rules. Rewrite using `[h4, ← Finset.sum_add_distrib]`. Use `Eq.trans ?_ h2` and prove the remaining obligations. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[if_neg hne]`.

Establish `h5` using `hIL i`. Distinguish the cases in `h6 : i.val = a.val`. Establish `h7 : i = ⟨a.val, ha⟩` using `Fin.ext h6`. Rewrite using `[if_pos h7, if_pos (by omega), if_neg (by omega)]`. Use linear arithmetic over natural numbers and integers.

Establish `h7 : i ≠ ⟨a.val, ha⟩` using `fun h => h6 (by rw [h])`. Rewrite using `[if_neg h7]`. Distinguish the cases in `h8 : a.val < i.val`. Rewrite using `[if_pos (by omega), if_pos h8]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[if_neg (by omega), if_neg h8]`. Use linear arithmetic over natural numbers and integers. Establish `h9` using `(hIL ⟨a.val, ha⟩).1`. Use linear arithmetic over natural numbers and integers. Rewrite using `[dif_neg ha]`.

Establish `hl : a = Fin.last n` using `Fin.ext (by have := a.isLt; simp; omega)`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[if_pos hl, if_neg (by have := i.isLt; omega), if_neg (by have := i.isLt; omega)]`. Use linear arithmetic over natural numbers and integers.
-/
theorem bm_xi_row {R : Type} [CommRing R] {n : ℕ} (lam sg : Fin n → ℕ) (hIL : bmIL lam sg) :
    IsWeightedHomogeneous (rowW (n + 1) n) (xiB R lam sg) (bmRho lam sg) := by
  have hanti : Antitone lam := bmG_antitone lam fun i => (hIL i).2.trans (hIL i).1
  have h1 : IsWeightedHomogeneous (rowW (n + 1) n) (xiB R lam sg)
      (∑ i : Fin n, ((sg i - nuNext lam i) • initW (n + 1) (i.val + 1) +
        (lam i - sg i) • (initW (n + 1) i.val + Pi.single (Fin.last n) 1))) := by
    unfold xiB
    refine IsWeightedHomogeneous.prod _ _ _ fun i _ => ?_
    refine IsWeightedHomogeneous.mul (IsWeightedHomogeneous.pow ?_ _) (IsWeightedHomogeneous.pow ?_ _)
    · rw [← bmG_sumA]; exact bmG_initMinor_rowHom R _ _
    · rw [← bmG_sumB]; exact bmG_initMinor_rowHom R _ _
  convert h1 using 1
  funext a
  simp only [bmRho, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, initW, Pi.single_apply]
  by_cases ha : a.val < n
  · rw [dif_pos ha]
    have hne : a ≠ Fin.last n := fun h => by rw [h] at ha; simp at ha
    have h2 := congrFun (hw_weight_eq lam hanti) ⟨a.val, ha⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, initW] at h2
    have h3 : (∑ i : Fin n, ((sg i - nuNext lam i) * (if a.val < i.val + 1 then 1 else 0) +
        (lam i - sg i) * ((if a.val < i.val then 1 else 0) + if a = Fin.last n then 1 else 0))) +
        (lam ⟨a.val, ha⟩ - sg ⟨a.val, ha⟩) = lam ⟨a.val, ha⟩ := by
      have h4 : lam ⟨a.val, ha⟩ - sg ⟨a.val, ha⟩ =
          ∑ i : Fin n, if i = ⟨a.val, ha⟩ then (lam i - sg i) else 0 := by
        rw [Finset.sum_ite_eq']; simp
      rw [h4, ← Finset.sum_add_distrib]
      refine Eq.trans ?_ h2
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [if_neg hne]
      have h5 := hIL i
      by_cases h6 : i.val = a.val
      · have h7 : i = ⟨a.val, ha⟩ := Fin.ext h6
        rw [if_pos h7, if_pos (by omega), if_neg (by omega)]
        omega
      · have h7 : i ≠ ⟨a.val, ha⟩ := fun h => h6 (by rw [h])
        rw [if_neg h7]
        by_cases h8 : a.val < i.val
        · rw [if_pos (by omega), if_pos h8]
          omega
        · rw [if_neg (by omega), if_neg h8]
          omega
    have h9 := (hIL ⟨a.val, ha⟩).1
    omega
  · rw [dif_neg ha]
    have hl : a = Fin.last n := Fin.ext (by have := a.isLt; simp; omega)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [if_pos hl, if_neg (by have := i.isLt; omega), if_neg (by have := i.isLt; omega)]
    omega

/- English proof (translation)
Use `LinearMap.ext fun F => ?_` and prove the remaining obligations. Establish `h1` using `LinearMap.congr_fun h F`. Rewrite `h1` using `[LinearMap.add_apply, LinearMap.zero_apply]`. Rewrite using `[LinearMap.zero_apply]`. Conclude with `add_self_eq_zero.mp h1`.
-/
theorem bmK_two_tf (R : Type*) [CommRing R] [IsDomain R] [CharZero R] (n : ℕ) (x : Module.End R (BP R n))
    (h : x + x = 0) : x = 0 := by
  refine LinearMap.ext fun F => ?_
  have h1 := LinearMap.congr_fun h F
  rw [LinearMap.add_apply, LinearMap.zero_apply] at h1
  rw [LinearMap.zero_apply]
  exact add_self_eq_zero.mp h1

/- English proof (translation)
Conclude with `capDet_central (bmEL R n) u (bmEL_rel R n) (bmK_two_tf R n) k l`.
-/
theorem bmK_central (R : Type*) [CommRing R] [IsDomain R] [CharZero R] (n : ℕ) (k l : Fin n) (u : ℤ) :
    Commute (bmEL R n k l) (bmCap R n u) := by
  exact capDet_central (bmEL R n) u (bmEL_rel R n) (bmK_two_tf R n) k l

/- English proof (translation)
Conclude with `(capDet_commute_of (bmEL R n) u (bmCap R n v) (fun i j => (bmK_central R n i j v).symm)).symm`.
-/
theorem bmK_comm (R : Type*) [CommRing R] [IsDomain R] [CharZero R] (n : ℕ) (u v : ℤ) :
    Commute (bmCap R n u) (bmCap R n v) := by
  exact (capDet_commute_of (bmEL R n) u (bmCap R n v) (fun i j => (bmK_central R n i j v).symm)).symm

/- English proof (translation)
Conclude with `bmE_comm_apply (bmK_central R n k l u) G`.
-/
theorem bmK_bmE (R : Type*) [CommRing R] [IsDomain R] [CharZero R] (n : ℕ) (k l : Fin n) (u : ℤ) (G : BP R n) :
    bmE R n k l (bmCap R n u G) = bmCap R n u (bmE R n k l G) := by
  exact bmE_comm_apply (bmK_central R n k l u) G

/- English proof (translation)
Conclude with `bmE_comm_apply (capDet_commute_of (bmEL R n) u (bmZL R n k l) (fun i j => bmZL_comm_bmEL R n k l i j)) G`.
-/
theorem bmK_bmZ (R : Type*) [CommRing R] (n : ℕ) (k l : Fin n) (u : ℤ) (G : BP R n) :
    bmZ R n k l (bmCap R n u G) = bmCap R n u (bmZ R n k l G) := by
  exact bmE_comm_apply (capDet_commute_of (bmEL R n) u (bmZL R n k l) (fun i j => bmZL_comm_bmEL R n k l i j)) G

/- English proof (translation)
Rewrite `hG`, the goal using `[bm_mem_dualWeyl_iff]`. Take `⟨h1, h2⟩` from `hG`. Use `⟨fun s => ?_, fun l j hlj => ?_⟩` and prove the remaining obligations. Establish `e : ndEul R (n + 1) n s (bmCap R n u G) = bmCap R n u (ndEul R (n + 1) n s G)`. Rewrite using `[bm_ndEul_eq, Derivation.add_apply, Derivation.add_apply, bmK_bmE, bmK_bmZ, map_add]`.

Rewrite using `[e, h1 s, map_smul]`. Establish `e : ndE R (n + 1) n l j (bmCap R n u G) = bmCap R n u (ndE R (n + 1) n l j G)`. Rewrite using `[bm_ndE_eq, Derivation.add_apply, Derivation.add_apply, bmK_bmE, bmK_bmZ, map_add]`. Rewrite using `[e, h2 l j hlj, map_zero]`.
-/
theorem bmK_mem {R : Type} [CommRing R] [IsDomain R] [CharZero R] {n : ℕ} (lam : Fin n → ℕ) (u : ℤ) (G : BP R n)
    (hG : G ∈ dualWeyl R (n + 1) n lam) : bmCap R n u G ∈ dualWeyl R (n + 1) n lam := by
  rw [bm_mem_dualWeyl_iff] at hG ⊢
  obtain ⟨h1, h2⟩ := hG
  refine ⟨fun s => ?_, fun l j hlj => ?_⟩
  · have e : ndEul R (n + 1) n s (bmCap R n u G) = bmCap R n u (ndEul R (n + 1) n s G) := by
      rw [bm_ndEul_eq, Derivation.add_apply, Derivation.add_apply, bmK_bmE, bmK_bmZ, map_add]
    rw [e, h1 s, map_smul]
  · have e : ndE R (n + 1) n l j (bmCap R n u G) = bmCap R n u (ndE R (n + 1) n l j G) := by
      rw [bm_ndE_eq, Derivation.add_apply, Derivation.add_apply, bmK_bmE, bmK_bmZ, map_add]
    rw [e, h2 l j hlj, map_zero]

/- English proof (translation)
Proceed by induction on `ℓ with`. Consider the case `nil => simp`. Consider the case `cons a t ih`. Rewrite using `[List.map_cons, List.prod_cons]`. Conclude with `(hx a).mul_right ih`.
-/
theorem bmK_list_comm {A : Type*} [Ring A] (C : ℤ → A) (x : A) (hx : ∀ u, Commute x (C u)) (ℓ : List ℤ) :
    Commute x (ℓ.map C).prod := by
  induction ℓ with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.prod_cons]
    exact (hx a).mul_right ih

/- English proof (translation)
Proceed by induction on `ℓ with`. Consider the case `nil => intro G hG`. Simplify using `using hG`. Consider the case `cons a t ih`. Introduce `G hG`.

Rewrite using `[List.map_cons, List.prod_cons]`. Conclude with `hC a _ (ih G hG)`.
-/
theorem bmK_list_mem {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (C : ℤ → Module.End R M)
    (W : Submodule R M) (hC : ∀ u, ∀ G ∈ W, C u G ∈ W) (ℓ : List ℤ) : ∀ G ∈ W, (ℓ.map C).prod G ∈ W := by
  induction ℓ with
  | nil => intro G hG; simpa using hG
  | cons a t ih =>
    intro G hG
    rw [List.map_cons, List.prod_cons]
    exact hC a _ (ih G hG)

/- English proof (translation)
Introduce `i j hij`. Take `⟨i, hi⟩` from `i`. Take `⟨j, hj⟩` from `j`. Simplify using `only [Fin.mk_le_mk] at hij`. Proceed by induction on `j, hij using Nat.le_induction with`.

Consider the case `base => exact le_rfl`. Consider the case `succ k hik ih`. Establish `h1` using `(hIL ⟨k, by omega⟩).2`. Establish `h2` using `(hIL ⟨k + 1, hj⟩).1`. Rewrite `h1` using `[bmG_nuNext_of_succ lam ⟨k, by omega⟩ ⟨k + 1, hj⟩ rfl]`.

Conclude with `le_trans (le_trans h2 h1) (ih (by omega))`.
-/
theorem bmK_antitone {n : ℕ} (lam sg : Fin n → ℕ) (hIL : bmIL lam sg) : Antitone sg := by
  intro i j hij
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  simp only [Fin.mk_le_mk] at hij
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ k hik ih =>
    have h1 := (hIL ⟨k, by omega⟩).2
    have h2 := (hIL ⟨k + 1, hj⟩).1
    rw [bmG_nuNext_of_succ lam ⟨k, by omega⟩ ⟨k + 1, hj⟩ rfl] at h1
    exact le_trans (le_trans h2 h1) (ih (by omega))

def bmW (R : Type*) [CommRing R] (n : ℕ) (lam : Fin n → ℕ) (d : ℕ) : Submodule R (BP R n) :=
  dualWeyl R (n + 1) n lam ⊓ weightedHomogeneousSubmodule R (lastW n) d

/- English proof (translation)
Conclude with `Iff.rfl`.
-/
theorem bmK_mem_alt {R : Type*} [CommRing R] {n : ℕ} {lam : Fin n → ℕ} {d : ℕ} {G : BP R n} :
    G ∈ bmW R n lam d ↔ G ∈ dualWeyl R (n + 1) n lam ∧ IsWeightedHomogeneous (lastW n) G d := by
  exact Iff.rfl

/- English proof (translation)
Conclude with `bmK_list_comm (bmCap R n) x (fun u => capDet_commute_of (bmEL R n) u x hx) (bmList lam sg)`.
-/
theorem bmK_Zc (R : Type*) [CommRing R] (n : ℕ) (lam sg : Fin n → ℕ) (x : Module.End R (BP R n))
    (hx : ∀ i j, Commute x (bmEL R n i j)) : Commute x (bmZop R n lam sg) := by
  exact bmK_list_comm (bmCap R n) x (fun u => capDet_commute_of (bmEL R n) u x hx) (bmList lam sg)

/- English proof (translation)
Conclude with `bmE_comm_apply (bmK_Zc R n lam sg (zcomp R n β) (fun i j => bm_zcomp_comm_bmEL R n β i j)) G`.
-/
theorem bmK_Zz (R : Type*) [CommRing R] (n : ℕ) (lam sg : Fin n → ℕ) (β : Fin n → ℤ) (G : BP R n) :
    zcomp R n β (bmZop R n lam sg G) = bmZop R n lam sg (zcomp R n β G) := by
  exact bmE_comm_apply (bmK_Zc R n lam sg (zcomp R n β) (fun i j => bm_zcomp_comm_bmEL R n β i j)) G

/- English proof (translation)
Rewrite `hG`, the goal using `[bmK_mem_alt]`. Use `⟨bmK_mem lam u G hG.1, ?_⟩` and prove the remaining obligations. Conclude with `bm_isWH_of_comm (lastW n) d (bmCap R n u) (capDet_commute_of (bmEL R n) u _ (fun i j => bm_lastcomp_comm_bmEL R n d i j)) G hG.2`.
-/
theorem bmK_capW {R : Type} [CommRing R] [IsDomain R] [CharZero R] {n : ℕ} (lam : Fin n → ℕ) (d : ℕ) (u : ℤ)
    (G : BP R n) (hG : G ∈ bmW R n lam d) : bmCap R n u G ∈ bmW R n lam d := by
  rw [bmK_mem_alt] at hG ⊢
  refine ⟨bmK_mem lam u G hG.1, ?_⟩
  exact bm_isWH_of_comm (lastW n) d (bmCap R n u)
    (capDet_commute_of (bmEL R n) u _ (fun i j => bm_lastcomp_comm_bmEL R n d i j)) G hG.2

/- English proof (translation)
Conclude with `bmK_list_mem (bmCap R n) (bmW R n lam d) (fun u G hG => bmK_capW lam d u G hG) (bmList lam sg) G hG`.
-/
theorem bmK_ZW {R : Type} [CommRing R] [IsDomain R] [CharZero R] {n : ℕ} (lam sg : Fin n → ℕ) (d : ℕ)
    (G : BP R n) (hG : G ∈ bmW R n lam d) : bmZop R n lam sg G ∈ bmW R n lam d := by
  exact bmK_list_mem (bmCap R n) (bmW R n lam d) (fun u G hG => bmK_capW lam d u G hG) (bmList lam sg) G hG

/- English proof (translation)
The claim follows from `bm_kill (zW n) omg (bmCap R n) (bmW R n lam (∑ s, (lam s - sg s))) (bmChi lam) (bmAdm lam (∑ s, (lam s - sg s))) (bmK_comm R n) (fun u β => capDet_commute_of (bmEL R n) u _ (bm_zcomp_comm_bmEL R n β)) (bmK_capW lam _) (fun G hG β h1 h2 => bm_eig lam _ G (bmK_mem_alt.1 hG).1 (bmK_ …`.
-/
theorem bmK_kill {R : Type} [CommRing R] [IsDomain R] [CharZero R] {n : ℕ} (lam sg : Fin n → ℕ)
    (hI : Interlace (lamZ lam) (fun i => (sg i : ℤ))) (G : BP R n)
    (hG : G ∈ bmW R n lam (∑ s, (lam s - sg s)))
    (h0 : zcomp R n (fun s => ((lam s - sg s : ℕ) : ℤ)) G = 0) : bmZop R n lam sg G = 0 :=
  bm_kill (zW n) omg (bmCap R n) (bmW R n lam (∑ s, (lam s - sg s))) (bmChi lam)
    (bmAdm lam (∑ s, (lam s - sg s))) (bmK_comm R n)
    (fun u β => capDet_commute_of (bmEL R n) u _ (bm_zcomp_comm_bmEL R n β)) (bmK_capW lam _)
    (fun G hG β h1 h2 => bm_eig lam _ G (bmK_mem_alt.1 hG).1 (bmK_mem_alt.1 hG).2 β h1 h2)
    (bm_sep lam _) (bmList lam sg) _ (bm_list_kills lam sg hI) G hG h0

/- English proof (translation)
Conclude with `bmK_mem_alt.mpr ⟨h.1, h.2.1⟩`.
-/
theorem bmK_liftW {R : Type*} [CommRing R] {n : ℕ} {lam b : Fin n → ℕ} {f : MvPolynomial (Fin n × Fin n) R}
    {G : BP R n} (h : bmLift R n lam b f G) : G ∈ bmW R n lam (∑ s, b s) := by
  exact bmK_mem_alt.mpr ⟨h.1, h.2.1⟩

/- English proof (translation)
Establish `h0 : bmLift R n lam (fun s => lam s - sg s) 0 (G - G')`. Use `bmLift_add h (bmLift_smul (-1 : R) h')` as an intermediate fact. Simplify `this` using `[sub_eq_add_neg]`. Establish `hz : zcomp R n (fun s => ((lam s - sg s : ℕ) : ℤ)) (G - G') = 0`. Establish `hlow` using `h0.2.2`.

Rewrite `hlow` using `[map_zero, mul_zero, sub_zero]`. Conclude with `(bm_isLow_iff _ _).mp hlow _ le_rfl`. Establish `hk` using `bmK_kill lam sg hI (G - G') (bmK_liftW h0) hz`. Rewrite `hk` using `[map_sub]`. Conclude with `sub_eq_zero.mp hk`.
-/
theorem bmK_key {R : Type} [CommRing R] [IsDomain R] [CharZero R] {n : ℕ} (lam sg : Fin n → ℕ)
    (hI : Interlace (lamZ lam) (fun i => (sg i : ℤ))) (f : MvPolynomial (Fin n × Fin n) R) (G G' : BP R n)
    (h : bmLift R n lam (fun s => lam s - sg s) f G) (h' : bmLift R n lam (fun s => lam s - sg s) f G') :
    bmZop R n lam sg G = bmZop R n lam sg G' := by
  have h0 : bmLift R n lam (fun s => lam s - sg s) 0 (G - G') := by
    have := bmLift_add h (bmLift_smul (-1 : R) h')
    simpa [sub_eq_add_neg] using this
  have hz : zcomp R n (fun s => ((lam s - sg s : ℕ) : ℤ)) (G - G') = 0 := by
    have hlow := h0.2.2
    rw [map_zero, mul_zero, sub_zero] at hlow
    exact (bm_isLow_iff _ _).mp hlow _ le_rfl
  have hk := bmK_kill lam sg hI (G - G') (bmK_liftW h0) hz
  rw [map_sub] at hk
  exact sub_eq_zero.mp hk

/- English proof (translation)
Establish `hwm : hw R le_rfl sg ∈ dualWeyl R n n sg` using `hwMem R n n le_rfl sg (bmK_antitone lam sg hIL)`. Establish `hwm'` using `bm_mem_dualWeyl_iff.1 hwm`. Establish `h1` using `capDet_eigen (bmEL R n) u (zmon R n (fun s => lam s - sg s) * emb R n (hw R le_rfl sg)) (fun s => (sg s : ℤ)) (fun l j hlj => by show bmE R n l j _ = 0`. Rewrite using `[bmE_lead, hwm'.2 l j hlj, map_zero, mul_zero])`. Use the proof step `(fun s => by show bmE R n s s _ = _`.

Rewrite using `[bmE_lead, bm_ndE_self, hwm'.1 s, map_smul, mul_smul_comm]`. Use the proof step `simp)`. Establish `h2 : bmChi lam (fun s => ((lam s - sg s : ℕ) : ℤ)) u = ∏ j : Fin n, (u + ((j : ℕ) : ℤ) - (sg j : ℤ))`. Unfold `bmChi`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations.

Use `beta_reduce`. Rewrite using `[Nat.cast_sub (hIL j).1]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2]`. Conclude with `h1`.
-/
theorem bmK_lead_eigen {R : Type} [CommRing R] [IsDomain R] [CharZero R] {n : ℕ} (lam sg : Fin n → ℕ)
    (hIL : bmIL lam sg) (u : ℤ) :
    bmCap R n u (zmon R n (fun s => lam s - sg s) * emb R n (hw R le_rfl sg)) =
      ((bmChi lam (fun s => ((lam s - sg s : ℕ) : ℤ)) u : ℤ) : R) •
        (zmon R n (fun s => lam s - sg s) * emb R n (hw R le_rfl sg)) := by
  have hwm : hw R le_rfl sg ∈ dualWeyl R n n sg := hwMem R n n le_rfl sg (bmK_antitone lam sg hIL)
  have hwm' := bm_mem_dualWeyl_iff.1 hwm
  have h1 := capDet_eigen (bmEL R n) u (zmon R n (fun s => lam s - sg s) * emb R n (hw R le_rfl sg))
    (fun s => (sg s : ℤ))
    (fun l j hlj => by
      show bmE R n l j _ = 0
      rw [bmE_lead, hwm'.2 l j hlj, map_zero, mul_zero])
    (fun s => by
      show bmE R n s s _ = _
      rw [bmE_lead, bm_ndE_self, hwm'.1 s, map_smul, mul_smul_comm]
      simp)
  have h2 : bmChi lam (fun s => ((lam s - sg s : ℕ) : ℤ)) u = ∏ j : Fin n, (u + ((j : ℕ) : ℤ) - (sg j : ℤ)) := by
    unfold bmChi
    refine Finset.prod_congr rfl fun j _ => ?_
    beta_reduce
    rw [Nat.cast_sub (hIL j).1]
    ring
  rw [h2]
  exact h1

/- English proof (translation)
Establish `hIL` using `bm_IL_of lam sg hI`. Establish `hxi` using `bmLift_xi (R := R) lam sg hIL`. Establish `hZA : bmZop R n lam sg (zmon R n (fun s => lam s - sg s) * emb R n (hw R le_rfl sg)) = ((cCap (lamZ lam) (fun i => (sg i : ℤ)) : ℤ) : R) • (zmon R n (fun s => lam s - sg s) * emb R n (hw R le_rfl sg))`. Rewrite using `[bmZop, bm_list_eigen (bmCap R n) (bmChi lam (fun s => ((lam s - sg s : ℕ) : ℤ))) _ (bmK_lead_eigen lam sg hIL), bm_list_prod lam sg hI]`. Use `sub_eq_zero.1 (bm_claimT lam sg _ ?_ ?_ ?_)` and prove the remaining obligations.

Conclude with `Submodule.sub_mem _ (bmK_mem_alt.1 (bmK_ZW lam sg _ _ (bmK_liftW hxi))).1 (Submodule.smul_mem _ _ hxi.1)`. Establish `hr` using `bm_xi_row (R := R) lam sg hIL`. Establish `hr2 : IsWeightedHomogeneous (rowW (n + 1) n) (bmZop R n lam sg (xiB R lam sg)) (bmRho lam sg)` using `bm_isWH_of_comm _ _ _ (bmK_Zc R n lam sg _ (bm_rowcomp_comm_bmEL R n _)) _ hr`. Establish `hr3 : IsWeightedHomogeneous (rowW (n + 1) n) (bmZop R n lam sg (xiB R lam sg) - ((cCap (lamZ lam) (fun i => (sg i : ℤ)) : ℤ) : R) • xiB R lam sg) (bmRho lam sg)` using `(weightedHomogeneousSubmodule R (rowW (n + 1) n) (bmRho lam sg)).sub_mem hr2 ((weightedHomogeneousSubmodule R (rowW (n + 1) n) (bmRho lam sg)).smul_mem _ hr)`. Introduce `m hm a`.

Establish `h4` using `hr3 (mem_support_iff.1 hm)`. Rewrite using `[← bm_weight_rowW, h4]`. Simplify using `[bmRho]`. Establish `e : bmZop R n lam sg (xiB R lam sg) - ((cCap (lamZ lam) (fun i => (sg i : ℤ)) : ℤ) : R) • xiB R lam sg = bmZop R n lam sg (xiB R lam sg - zmon R n (fun s => lam s - sg s) * emb R n (hw R le_rfl sg)) - ((cCap (lamZ lam) (fun i => (sg i : ℤ)) : ℤ) : R) • (xiB R lam sg - zmon R n (f …`. Rewrite using `[map_sub, hZA, smul_sub]`.

Normalize the expressions using the abelian group laws. Establish `eD : (omg fun s => (lam s : ℤ) - (sg s : ℤ)) = omg fun s => ((lam s - sg s : ℕ) : ℤ)`. Use `congr 1`. Use function extensionality and compare the values at `s`. Rewrite using `[Nat.cast_sub (hIL s).1]`.

Rewrite using `[e, eD, bm_isLow_iff]`. Introduce `β hβ`. Establish `h5` using `(bm_isLow_iff _ _).1 hxi.2.2 β hβ`. Rewrite using `[map_sub, map_smul, bmK_Zz, h5, map_zero, smul_zero, sub_zero]`.
-/
theorem bmK_xi {R : Type} [CommRing R] [IsDomain R] [CharZero R] {n : ℕ} (lam sg : Fin n → ℕ)
    (hI : Interlace (lamZ lam) (fun i => (sg i : ℤ))) :
    bmZop R n lam sg (xiB R lam sg) = ((cCap (lamZ lam) (fun i => (sg i : ℤ)) : ℤ) : R) • xiB R lam sg := by
  have hIL := bm_IL_of lam sg hI
  have hxi := bmLift_xi (R := R) lam sg hIL
  have hZA : bmZop R n lam sg (zmon R n (fun s => lam s - sg s) * emb R n (hw R le_rfl sg)) =
      ((cCap (lamZ lam) (fun i => (sg i : ℤ)) : ℤ) : R) •
        (zmon R n (fun s => lam s - sg s) * emb R n (hw R le_rfl sg)) := by
    rw [bmZop, bm_list_eigen (bmCap R n) (bmChi lam (fun s => ((lam s - sg s : ℕ) : ℤ))) _
      (bmK_lead_eigen lam sg hIL), bm_list_prod lam sg hI]
  refine sub_eq_zero.1 (bm_claimT lam sg _ ?_ ?_ ?_)
  · exact Submodule.sub_mem _ (bmK_mem_alt.1 (bmK_ZW lam sg _ _ (bmK_liftW hxi))).1 (Submodule.smul_mem _ _ hxi.1)
  · have hr := bm_xi_row (R := R) lam sg hIL
    have hr2 : IsWeightedHomogeneous (rowW (n + 1) n) (bmZop R n lam sg (xiB R lam sg)) (bmRho lam sg) :=
      bm_isWH_of_comm _ _ _ (bmK_Zc R n lam sg _ (bm_rowcomp_comm_bmEL R n _)) _ hr
    have hr3 : IsWeightedHomogeneous (rowW (n + 1) n)
        (bmZop R n lam sg (xiB R lam sg) - ((cCap (lamZ lam) (fun i => (sg i : ℤ)) : ℤ) : R) • xiB R lam sg)
        (bmRho lam sg) :=
      (weightedHomogeneousSubmodule R (rowW (n + 1) n) (bmRho lam sg)).sub_mem hr2
        ((weightedHomogeneousSubmodule R (rowW (n + 1) n) (bmRho lam sg)).smul_mem _ hr)
    intro m hm a
    have h4 := hr3 (mem_support_iff.1 hm)
    rw [← bm_weight_rowW, h4]
    simp [bmRho]
  · have e : bmZop R n lam sg (xiB R lam sg) - ((cCap (lamZ lam) (fun i => (sg i : ℤ)) : ℤ) : R) • xiB R lam sg =
        bmZop R n lam sg (xiB R lam sg - zmon R n (fun s => lam s - sg s) * emb R n (hw R le_rfl sg)) -
          ((cCap (lamZ lam) (fun i => (sg i : ℤ)) : ℤ) : R) •
            (xiB R lam sg - zmon R n (fun s => lam s - sg s) * emb R n (hw R le_rfl sg)) := by
      rw [map_sub, hZA, smul_sub]; abel
    have eD : (omg fun s => (lam s : ℤ) - (sg s : ℤ)) = omg fun s => ((lam s - sg s : ℕ) : ℤ) := by
      congr 1
      funext s
      rw [Nat.cast_sub (hIL s).1]
    rw [e, eD, bm_isLow_iff]
    intro β hβ
    have h5 := (bm_isLow_iff _ _).1 hxi.2.2 β hβ
    rw [map_sub, map_smul, bmK_Zz, h5, map_zero, smul_zero, sub_zero]

/- English proof (translation)
Use `choose g hg using hex`. Use `⟨{ toFun := fun f => Z (g f), map_add' := ?_, map_smul' := ?_ }, ?_⟩` and prove the remaining obligations. Introduce `f f' show Z (g (f + f')) = Z (g f) + Z (g f')`. Rewrite using `[hkey (f + f') (g (f + f')) (g f + g f') (hg _) (hadd _ _ _ _ (hg f) (hg f')), map_add]`. Introduce `c f show Z (g (c • f)) = (RingHom.id R) c • Z (g f)`.

Rewrite using `[hkey (c • f) (g (c • f)) (c • g f) (hg _) (hsmul c f _ (hg f)), map_smul, RingHom.id_apply]`. Introduce `f G hG`. Conclude with `hkey f (g f) G (hg f) hG`.
-/
theorem bmK_lin {R M N P : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (rel : M → N → Prop) (Z : N →ₗ[R] P) (hex : ∀ f, ∃ G, rel f G)
    (hadd : ∀ f f' G G', rel f G → rel f' G' → rel (f + f') (G + G'))
    (hsmul : ∀ (c : R) f G, rel f G → rel (c • f) (c • G))
    (hkey : ∀ f G G', rel f G → rel f G' → Z G = Z G') :
    ∃ io : M →ₗ[R] P, ∀ f G, rel f G → io f = Z G := by
  choose g hg using hex
  refine ⟨{ toFun := fun f => Z (g f), map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro f f'
    show Z (g (f + f')) = Z (g f) + Z (g f')
    rw [hkey (f + f') (g (f + f')) (g f + g f') (hg _) (hadd _ _ _ _ (hg f) (hg f')), map_add]
  · intro c f
    show Z (g (c • f)) = (RingHom.id R) c • Z (g f)
    rw [hkey (c • f) (g (c • f)) (c • g f) (hg _) (hsmul c f _ (hg f)), map_smul, RingHom.id_apply]
  · intro f G hG
    exact hkey f (g f) G (hg f) hG

def bmRel (R : Type) [CommRing R] (n : ℕ) (lam sg : Fin n → ℕ) (f : ↥(dualWeyl R n n sg)) (G : BP R n) : Prop :=
  bmLift R n lam (fun s => lam s - sg s) (f : MvPolynomial (Fin n × Fin n) R) G

/- English proof (translation)
Conclude with `bmLift_exists lam sg hIL (f : MvPolynomial (Fin n × Fin n) R) f.2`.
-/
theorem bmK_rel_ex {R : Type} [CommRing R] [IsDomain R] {n : ℕ} (lam sg : Fin n → ℕ)
    (hIL : bmIL lam sg) (f : ↥(dualWeyl R n n sg)) : ∃ G, bmRel R n lam sg f G := by
  exact bmLift_exists lam sg hIL (f : MvPolynomial (Fin n × Fin n) R) f.2

/- English proof (translation)
Conclude with `bmLift_add h h'`.
-/
theorem bmK_rel_add {R : Type} [CommRing R] {n : ℕ} (lam sg : Fin n → ℕ) (f f' : ↥(dualWeyl R n n sg))
    (G G' : BP R n) (h : bmRel R n lam sg f G) (h' : bmRel R n lam sg f' G') :
    bmRel R n lam sg (f + f') (G + G') := by
  exact bmLift_add h h'

/- English proof (translation)
Conclude with `bmLift_smul c h`.
-/
theorem bmK_rel_smul {R : Type} [CommRing R] {n : ℕ} (lam sg : Fin n → ℕ) (c : R) (f : ↥(dualWeyl R n n sg))
    (G : BP R n) (h : bmRel R n lam sg f G) : bmRel R n lam sg (c • f) (c • G) := by
  exact bmLift_smul c h

/- English proof (translation)
Conclude with `bmK_lin (bmRel R n lam sg) (bmZop R n lam sg) (bmK_rel_ex lam sg (bm_IL_of lam sg hI)) (fun f f' G G' h h' => bmK_rel_add lam sg f f' G G' h h') (fun c f G h => bmK_rel_smul lam sg c f G h) (fun f G G' h h' => bmK_key lam sg hI (f : MvPolynomial (Fin n × Fin n) R) G G' h h')`.
-/
theorem bmK_io {R : Type} [CommRing R] [IsDomain R] [CharZero R] {n : ℕ} (lam sg : Fin n → ℕ)
    (hI : Interlace (lamZ lam) (fun i => (sg i : ℤ))) :
    ∃ io : ↥(dualWeyl R n n sg) →ₗ[R] BP R n, ∀ (f : ↥(dualWeyl R n n sg)) (G : BP R n),
      bmRel R n lam sg f G → io f = bmZop R n lam sg G := by
  exact bmK_lin (bmRel R n lam sg) (bmZop R n lam sg) (bmK_rel_ex lam sg (bm_IL_of lam sg hI))
    (fun f f' G G' h h' => bmK_rel_add lam sg f f' G G' h h')
    (fun c f G h => bmK_rel_smul lam sg c f G h)
    (fun f G G' h h' => bmK_key lam sg hI (f : MvPolynomial (Fin n × Fin n) R) G G' h h')

/- English proof (translation)
Introduce `R _ _ _ n lam sg hI`. Take `⟨io, hio⟩` from `bmK_io (R := R) lam sg hI`. Establish `hIL` using `bm_IL_of lam sg hI`. Use `⟨io, fun f => ?_, fun g f f' hf => ?_, fun h hh => ?_, fun f m hm => ?_⟩` and prove the remaining obligations. Take `⟨G, hG⟩` from `bmK_rel_ex lam sg hIL f`.

Rewrite using `[hio f G hG]`. Conclude with `(bmK_mem_alt.mp (bmK_ZW lam sg _ G (bmK_liftW hG))).1`. Take `⟨G, hG⟩` from `bmK_rel_ex lam sg hIL f`. Establish `hG' : bmRel R n lam sg f' (rowAct R (extM R g) G)`. Unfold `bmRel`.

Rewrite using `[hf]`. Conclude with `bmLift_rowAct g hG`. Rewrite using `[hio f' _ hG', hio f G hG]`. Conclude with `(bmE_comm_apply (bmK_Zc R n lam sg _ (fun i j => bm_rowAct_comm_bmEL R n g i j)) G).symm`. Establish `hx : bmRel R n lam sg h (xiB R lam sg)`.

Unfold `bmRel`. Rewrite using `[hh]`. Conclude with `bmLift_xi lam sg hIL`. Rewrite using `[hio h _ hx]`. Conclude with `bmK_xi lam sg hI`.

Take `⟨G, hG⟩` from `bmK_rel_ex lam sg hIL f`. Rewrite `hm` using `[hio f G hG]`. Establish `hW` using `bmK_mem_alt.mp (bmK_ZW lam sg _ G (bmK_liftW hG))`. Use `hW.2 (mem_support_iff.mp hm)` as an intermediate fact. Rewrite `this` using `[bm_weight_lastW]`.

Conclude with `this`.
-/
theorem branch_map_formula : BranchMap := by
  intro R _ _ _ n lam sg hI
  obtain ⟨io, hio⟩ := bmK_io (R := R) lam sg hI
  have hIL := bm_IL_of lam sg hI
  refine ⟨io, fun f => ?_, fun g f f' hf => ?_, fun h hh => ?_, fun f m hm => ?_⟩
  · obtain ⟨G, hG⟩ := bmK_rel_ex lam sg hIL f
    rw [hio f G hG]
    exact (bmK_mem_alt.mp (bmK_ZW lam sg _ G (bmK_liftW hG))).1
  · obtain ⟨G, hG⟩ := bmK_rel_ex lam sg hIL f
    have hG' : bmRel R n lam sg f' (rowAct R (extM R g) G) := by
      unfold bmRel
      rw [hf]
      exact bmLift_rowAct g hG
    rw [hio f' _ hG', hio f G hG]
    exact (bmE_comm_apply (bmK_Zc R n lam sg _ (fun i j => bm_rowAct_comm_bmEL R n g i j)) G).symm
  · have hx : bmRel R n lam sg h (xiB R lam sg) := by
      unfold bmRel
      rw [hh]
      exact bmLift_xi lam sg hIL
    rw [hio h _ hx]
    exact bmK_xi lam sg hI
  · obtain ⟨G, hG⟩ := bmK_rel_ex lam sg hIL f
    rw [hio f G hG] at hm
    have hW := bmK_mem_alt.mp (bmK_ZW lam sg _ G (bmK_liftW hG))
    have := hW.2 (mem_support_iff.mp hm)
    rw [bm_weight_lastW] at this
    exact this

end Formalism.BranchingDeterminantCap
